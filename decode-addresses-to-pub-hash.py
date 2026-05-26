#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import base58
import sys

# ----------------------------------------------------------------------
# Настройки
INPUT_FILE = "addresses.txt"      # файл с адресами (по одному на строку)
OUTPUT_P2PK = "p2pk_keys.txt"     # найденные публичные ключи (P2PK)
OUTPUT_P2PKH_HASH = "p2pkh_hashes.txt"  # хеши публичных ключей для P2PKH
OUTPUT_OTHER = "other.txt"        # остальные адреса

# ----------------------------------------------------------------------
def decode_base58check(addr):
    """Декодирует Base58Check, возвращает (version_byte, payload) или (None, None) при ошибке."""
    try:
        decoded = base58.b58decode_check(addr)
        if len(decoded) < 1:
            return None, None
        version = decoded[0]
        payload = decoded[1:]
        return version, payload
    except Exception:
        return None, None

def is_p2pkh(addr):
    """Проверяет, является ли адрес P2PKH (начинается с 1, после декодирования версия 0x00 и payload 20 байт)."""
    if not addr.startswith('1'):
        return False
    version, payload = decode_base58check(addr)
    if version == 0x00 and payload and len(payload) == 20:
        return True
    return False

def is_p2pk(addr):
    """
    Определяет потенциальный P2PK-адрес.
    В классическом биткоине P2PK не кодировался в стандартные адреса вида '1...'.
    Однако некоторые ранние реализации использовали версию 0x41 (65 байт ключа)
    или 0x21 (33 байта сжатого ключа) без хеширования.
    Здесь мы проверяем: после декодирования длина payload равна 33 или 65 (сжатый/несжатый ключ)
    и первый байт payload начинается с 0x02,0x03,0x04.
    """
    version, payload = decode_base58check(addr)
    if version is None:
        return False
    # Возможные версии для P2PK: 0x41 (65 байт), 0x21 (33 байта) – редко, иногда 0x00 но это P2PKH
    if version not in (0x41, 0x21):
        return False
    if len(payload) in (33, 65):
        # Дополнительная проверка: первый байт ключа должен быть 0x02, 0x03 (сжатый) или 0x04 (несжатый)
        first_byte = payload[0]
        if first_byte in (0x02, 0x03, 0x04):
            return True
    return False

def extract_pubkey_from_p2pk(addr):
    """Из P2PK-адреса возвращает публичный ключ в hex."""
    version, payload = decode_base58check(addr)
    if version is None:
        return None
    # payload уже является публичным ключом (33 или 65 байт)
    return payload.hex()

def get_pubkey_hash(addr):
    """Для P2PKH возвращает хеш публичного ключа (20 байт) в hex."""
    _, payload = decode_base58check(addr)
    if payload and len(payload) == 20:
        return payload.hex()
    return None

# ----------------------------------------------------------------------
# Опционально: получение публичного ключа по P2PKH через внешнее API
# (требуется интернет и возможно ключ API)
import requests
import json

def fetch_pubkey_from_blockchain(addr):
    """
    Пытается получить публичный ключ для P2PKH через blockchair.com API.
    Возвращает hex публичного ключа или None.
    """
    try:
        # Используем открытое API blockchair (без ключа, но с ограничениями)
        url = f"https://api.blockchair.com/bitcoin/dashboards/address/{addr}"
        resp = requests.get(url, timeout=10)
        if resp.status_code == 200:
            data = resp.json()
            # Ищем в транзакциях, где этот адрес был входом
            tx_ids = data['data'][addr].get('transactions', [])
            # Для простоты берём первую транзакцию, где адрес вход
            for txid in tx_ids:
                tx_url = f"https://api.blockchair.com/bitcoin/raw/transaction/{txid}"
                tx_resp = requests.get(tx_url, timeout=10)
                if tx_resp.status_code == 200:
                    tx_data = tx_resp.json()
                    # Анализ входов
                    for inp in tx_data['data'][txid]['inputs']:
                        # В raw данные вход содержит script_sig, из которого можно извлечь pubkey
                        # Это сложно; проще использовать другой сервис, например blockchain.com
                        pass
            # Упрощённо: вернём None, так как полный разбор сложен.
            # Вместо этого можно использовать специализированный сервис.
        return None
    except Exception:
        return None

# ----------------------------------------------------------------------
def main():
    try:
        with open(INPUT_FILE, 'r', encoding='utf-8') as f:
            addresses = [line.strip() for line in f if line.strip()]
    except FileNotFoundError:
        print(f"Файл {INPUT_FILE} не найден. Создайте его с адресами.")
        sys.exit(1)

    # Открываем выходные файлы
    with open(OUTPUT_P2PK, 'w', encoding='utf-8') as f_p2pk, \
         open(OUTPUT_P2PKH_HASH, 'w', encoding='utf-8') as f_p2pkh_hash, \
         open(OUTPUT_OTHER, 'w', encoding='utf-8') as f_other:

        for addr in addresses:
            # 1) Пытаемся определить P2PK
            if is_p2pk(addr):
                pubkey_hex = extract_pubkey_from_p2pk(addr)
                if pubkey_hex:
                    f_p2pk.write(f"{addr} -> {pubkey_hex}\n")
                    print(f"[P2PK] {addr} -> ключ сохранён в {OUTPUT_P2PK}")
                else:
                    f_other.write(f"{addr} (ошибка декодирования P2PK)\n")
            # 2) P2PKH
            elif is_p2pkh(addr):
                pkh = get_pubkey_hash(addr)
                if pkh:
                    f_p2pkh_hash.write(f"{addr} -> {pkh}\n")
                    print(f"[P2PKH] {addr} -> хеш сохранён в {OUTPUT_P2PKH_HASH} (сам публичный ключ не вычислен)")
                    # ---- Раскомментируйте для попытки получить реальный публичный ключ через API ----
                    # pubkey = fetch_pubkey_from_blockchain(addr)
                    # if pubkey:
                    #     f_p2pk.write(f"{addr} (из API) -> {pubkey}\n")
                else:
                    f_other.write(f"{addr} (некорректный P2PKH)\n")
            # 3) Другие типы (P2SH, Bech32, или неизвестные)
            else:
                # Дополнительное определение для Bech32 (начинается с bc1)
                if addr.startswith('bc1'):
                    f_other.write(f"{addr} (Bech32) -> публичный ключ не хранится в адресе\n")
                elif addr.startswith('3'):
                    f_other.write(f"{addr} (P2SH) -> публичный ключ не хранится в адресе\n")
                else:
                    f_other.write(f"{addr} (неизвестный формат)\n")
                print(f"[OTHER] {addr} -> записан в {OUTPUT_OTHER}")

if __name__ == "__main__":
    main()