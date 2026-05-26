#![allow(unused_must_use, unused_assignments)]

use clap::Parser;
use secp256k1::{Secp256k1, PublicKey, SecretKey};
use ripemd::Ripemd160;
use sha2::{Sha256, Digest};
use base58::ToBase58;
use bech32::{self, ToBase32};
use serde::{Deserialize, Serialize};
use rand::Rng;
use rand::rngs::OsRng;
use std::collections::HashSet;
use std::fs::File;
use std::io::{BufRead, BufReader, Read, Write};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::thread;
use std::time::{Duration, Instant};
use crossbeam_channel::{unbounded, Receiver, Sender, select};
use anyhow::{bail, Result};
use primitive_types::U256;
use chrono::{DateTime, Local};
use std::sync::Mutex;
use num_bigint::BigUint;
use num_traits::Zero;
use std::str::FromStr;

use eframe::{egui, CreationContext, Frame};
use egui::{CentralPanel, ScrollArea, TopBottomPanel, RichText, TextEdit, Color32, Grid, FontData, FontDefinitions, FontFamily};
use rfd::FileDialog;
use sysinfo::System;

// ========================== Константы ==========================
const PERCENT_DECIMALS: usize = 80;
fn percent_scale() -> BigUint { BigUint::from(10u32).pow(PERCENT_DECIMALS as u32) }
fn max_percent_raw() -> BigUint { BigUint::from(100u32) * percent_scale() }

// Шрифты - размер
const MONOSPACE_FONT_SIZE: f32 = 12.0;

#[derive(Parser, Debug, Clone)]
struct CliConfig {
    #[arg(long, value_parser = parse_range_percent)]
    range_percent: (BigUint, BigUint),
    #[arg(short, long, default_value_t = num_cpus::get())]
    threads: usize,
    #[arg(long)]
    hash_file: Option<String>,
    #[arg(long)]
    hash_bin: Option<String>,
    #[arg(long)]
    output: Option<String>,
    #[arg(long)]
    random: bool,
}

fn parse_range_percent(s: &str) -> Result<(BigUint, BigUint)> {
    let parts: Vec<&str> = s.split('-').collect();
    if parts.len() != 2 {
        bail!("Формат должен быть 'start-end'");
    }
    let start = parse_percent_raw(parts[0])?;
    let end = parse_percent_raw(parts[1])?;
    if start > end {
        bail!("Начальный процент не может быть больше конечного");
    }
    if start > max_percent_raw() || end > max_percent_raw() {
        bail!("Проценты должны быть в диапазоне 0.00 .. 100.00");
    }
    Ok((start, end))
}

fn parse_percent_raw(s: &str) -> Result<BigUint> {
    let s = s.trim();
    if s.is_empty() { bail!("Пустое значение"); }
    let s = s.replace(',', ".");
    let parts: Vec<&str> = s.split('.').collect();
    match parts.len() {
        1 => {
            let int = BigUint::from_str(parts[0])?;
            if int > BigUint::from(100u32) { bail!("Процент не может превышать 100"); }
            Ok(int * percent_scale())
        }
        2 => {
            let int = BigUint::from_str(parts[0])?;
            if int > BigUint::from(100u32) { bail!("Процент не может превышать 100"); }
            let frac_str = parts[1];
            if frac_str.len() > PERCENT_DECIMALS { bail!("Дробная часть не может быть длиннее {} цифр", PERCENT_DECIMALS); }
            let mut padded = frac_str.to_string();
            while padded.len() < PERCENT_DECIMALS { padded.push('0'); }
            let frac = BigUint::from_str(&padded)?;
            Ok(int * percent_scale() + frac)
        }
        _ => bail!("Неверный формат числа"),
    }
}

fn u256_to_bytes(key: U256) -> [u8; 32] {
    let mut bytes = [0u8; 32];
    key.to_big_endian(&mut bytes);
    bytes
}

fn bytes_to_u256(bytes: &[u8; 32]) -> U256 {
    U256::from_big_endian(bytes)
}

fn hash160(data: &[u8]) -> [u8; 20] {
    let sha = Sha256::digest(data);
    let mut hasher = Ripemd160::new();
    hasher.update(&sha);
    let rip = hasher.finalize();
    rip.into()
}

fn generate_addresses(priv_key: &[u8; 32]) -> Result<(String, String, String, String, String, String, String)> {
    let secp = Secp256k1::new();
    let secret_key = SecretKey::from_slice(priv_key)?;
    let pub_key = PublicKey::from_secret_key(&secp, &secret_key);

    let uncompressed = pub_key.serialize_uncompressed();
    let compressed = pub_key.serialize();

    let hash160_uncompressed = hash160(&uncompressed);
    let hash160_compressed = hash160(&compressed);

    fn legacy_address(hash: &[u8; 20]) -> String {
        let mut payload = vec![0x00];
        payload.extend_from_slice(hash);
        let checksum = Sha256::digest(&Sha256::digest(&payload));
        payload.extend_from_slice(&checksum[0..4]);
        payload.to_base58()
    }

    let legacy_uncompressed = legacy_address(&hash160_uncompressed);
    let legacy_compressed = legacy_address(&hash160_compressed);

    fn p2sh_address(inner_hash: &[u8; 20]) -> String {
        let witness_program = [0x00, 0x14];
        let mut script = Vec::with_capacity(22);
        script.extend_from_slice(&witness_program);
        script.extend_from_slice(inner_hash);
        let script_hash = hash160(&script);
        let mut payload = vec![0x05];
        payload.extend_from_slice(&script_hash);
        let checksum = Sha256::digest(&Sha256::digest(&payload));
        payload.extend_from_slice(&checksum[0..4]);
        payload.to_base58()
    }

    let p2sh_uncompressed = p2sh_address(&hash160_uncompressed);
    let p2sh_compressed = p2sh_address(&hash160_compressed);

    fn bech32_address(hash: &[u8; 20]) -> String {
        let hrp = "bc";
        let mut bytes = Vec::with_capacity(21);
        bytes.push(0u8);
        bytes.extend_from_slice(hash);
        let data = bytes.to_base32();
        bech32::encode(hrp, data, bech32::Variant::Bech32).unwrap()
    }

    let bech32 = bech32_address(&hash160_compressed);

    let priv_hex = hex::encode(priv_key);
    let ripemd_hex = hex::encode(hash160_compressed);

    Ok((
        priv_hex,
        ripemd_hex,
        legacy_uncompressed,
        legacy_compressed,
        p2sh_uncompressed,
        p2sh_compressed,
        bech32,
    ))
}

#[derive(Debug)]
enum WorkerMessage {
    Stats(u64, usize, u64, u32),
    Match(u64, usize, [u8; 32], [u8; 20], String),
    MinMax(u64, usize, U256, U256),
    LastKey(u64, usize, U256),
    Finished(u64, usize),
    SectorStats(u64, usize, U256, U256, U256),
}

fn update_minmax(key: U256, min: &mut Option<U256>, max: &mut Option<U256>) {
    *min = Some(min.map_or(key, |m| if key < m { key } else { m }));
    *max = Some(max.map_or(key, |m| if key > m { key } else { m }));
}

fn random_key_in_range(start: U256, end: U256, rng: &mut OsRng) -> U256 {
    if end <= start {
        return start;
    }
    let range_width = end - start + U256::from(1u64);
    if range_width == U256::zero() {
        return start;
    }
    let offset = if range_width > U256::from(u64::MAX) {
        let mut bytes = [0u8; 32];
        rng.fill(&mut bytes);
        U256::from_big_endian(&bytes) % range_width
    } else {
        U256::from(rng.gen_range(0..range_width.low_u64()))
    };
    start + offset
}

fn worker_main(
    session_id: u64,
    thread_id: usize,
    start_key: U256,
    end_key: U256,
    step: U256,
    running: Arc<AtomicBool>,
    tx: Sender<WorkerMessage>,
    target_hashes: Arc<HashSet<[u8; 20]>>,
    mode: &str,
) {
    let secp = Secp256k1::new();
    let mut local_attempts = 0u64;
    let mut local_found = 0u32;
    let mut last_minmax_report = Instant::now();
    let mut local_min: Option<U256> = None;
    let mut local_max: Option<U256> = None;
    let mut last_stats_report = Instant::now();
    let mut last_sector_stats_report = Instant::now();
    let mut sector_local_min: Option<U256> = None;
    let mut sector_local_max: Option<U256> = None;
    let mut sector_last_key: Option<U256> = None;

    if mode == "sector" {
        let threads_total = step.low_u64() as usize;
        if thread_id == 0 {
            let mut current = start_key;
            while running.load(Ordering::SeqCst) && current <= end_key {
                update_minmax(current, &mut local_min, &mut local_max);
                update_minmax(current, &mut sector_local_min, &mut sector_local_max);
                sector_last_key = Some(current);
                let _ = tx.send(WorkerMessage::LastKey(session_id, thread_id, current));

                let key_bytes = u256_to_bytes(current);
                if let Ok(secret) = SecretKey::from_slice(&key_bytes) {
                    let pub_key = PublicKey::from_secret_key(&secp, &secret);
                    let compressed = pub_key.serialize();
                    let h160_compressed = hash160(&compressed);
                    if target_hashes.contains(&h160_compressed) {
                        local_found += 1;
                        let _ = tx.send(WorkerMessage::Match(session_id, thread_id, key_bytes, h160_compressed, "compressed".into()));
                    }
                }

                local_attempts += 1;
                current += U256::from(1u64);

                if last_stats_report.elapsed() >= Duration::from_secs(1) {
                    let _ = tx.send(WorkerMessage::Stats(session_id, thread_id, local_attempts, local_found));
                    last_stats_report = Instant::now();
                }
                if last_minmax_report.elapsed() >= Duration::from_secs(10) {
                    if let (Some(min), Some(max)) = (local_min, local_max) {
                        let _ = tx.send(WorkerMessage::MinMax(session_id, thread_id, min, max));
                    }
                    local_min = None;
                    local_max = None;
                    last_minmax_report = Instant::now();
                }
                if last_sector_stats_report.elapsed() >= Duration::from_secs(2) {
                    if let (Some(min), Some(max), Some(last)) = (sector_local_min, sector_local_max, sector_last_key) {
                        let _ = tx.send(WorkerMessage::SectorStats(session_id, thread_id, last, min, max));
                    }
                    sector_local_min = None;
                    sector_local_max = None;
                    sector_last_key = None;
                    last_sector_stats_report = Instant::now();
                }
            }
        } else if thread_id == threads_total - 1 {
            let mut current = end_key;
            while running.load(Ordering::SeqCst) && current >= start_key {
                update_minmax(current, &mut local_min, &mut local_max);
                update_minmax(current, &mut sector_local_min, &mut sector_local_max);
                sector_last_key = Some(current);
                let _ = tx.send(WorkerMessage::LastKey(session_id, thread_id, current));

                let key_bytes = u256_to_bytes(current);
                if let Ok(secret) = SecretKey::from_slice(&key_bytes) {
                    let pub_key = PublicKey::from_secret_key(&secp, &secret);
                    let compressed = pub_key.serialize();
                    let h160_compressed = hash160(&compressed);
                    if target_hashes.contains(&h160_compressed) {
                        local_found += 1;
                        let _ = tx.send(WorkerMessage::Match(session_id, thread_id, key_bytes, h160_compressed, "compressed".into()));
                    }
                }

                local_attempts += 1;
                if current == U256::zero() { break; }
                current -= U256::from(1u64);

                if last_stats_report.elapsed() >= Duration::from_secs(1) {
                    let _ = tx.send(WorkerMessage::Stats(session_id, thread_id, local_attempts, local_found));
                    last_stats_report = Instant::now();
                }
                if last_minmax_report.elapsed() >= Duration::from_secs(10) {
                    if let (Some(min), Some(max)) = (local_min, local_max) {
                        let _ = tx.send(WorkerMessage::MinMax(session_id, thread_id, min, max));
                    }
                    local_min = None;
                    local_max = None;
                    last_minmax_report = Instant::now();
                }
                if last_sector_stats_report.elapsed() >= Duration::from_secs(2) {
                    if let (Some(min), Some(max), Some(last)) = (sector_local_min, sector_local_max, sector_last_key) {
                        let _ = tx.send(WorkerMessage::SectorStats(session_id, thread_id, last, min, max));
                    }
                    sector_local_min = None;
                    sector_local_max = None;
                    sector_last_key = None;
                    last_sector_stats_report = Instant::now();
                }
            }
        } else {
            let mut rng = OsRng;
            while running.load(Ordering::SeqCst) {
                let current = random_key_in_range(start_key, end_key, &mut rng);
                update_minmax(current, &mut local_min, &mut local_max);
                update_minmax(current, &mut sector_local_min, &mut sector_local_max);
                sector_last_key = Some(current);
                let _ = tx.send(WorkerMessage::LastKey(session_id, thread_id, current));

                let key_bytes = u256_to_bytes(current);
                if let Ok(secret) = SecretKey::from_slice(&key_bytes) {
                    let pub_key = PublicKey::from_secret_key(&secp, &secret);
                    let compressed = pub_key.serialize();
                    let h160_compressed = hash160(&compressed);
                    if target_hashes.contains(&h160_compressed) {
                        local_found += 1;
                        let _ = tx.send(WorkerMessage::Match(session_id, thread_id, key_bytes, h160_compressed, "compressed".into()));
                    }
                }

                local_attempts += 1;

                if last_stats_report.elapsed() >= Duration::from_secs(1) {
                    let _ = tx.send(WorkerMessage::Stats(session_id, thread_id, local_attempts, local_found));
                    last_stats_report = Instant::now();
                }
                if last_minmax_report.elapsed() >= Duration::from_secs(10) {
                    if let (Some(min), Some(max)) = (local_min, local_max) {
                        let _ = tx.send(WorkerMessage::MinMax(session_id, thread_id, min, max));
                    }
                    local_min = None;
                    local_max = None;
                    last_minmax_report = Instant::now();
                }
                if last_sector_stats_report.elapsed() >= Duration::from_secs(2) {
                    if let (Some(min), Some(max), Some(last)) = (sector_local_min, sector_local_max, sector_last_key) {
                        let _ = tx.send(WorkerMessage::SectorStats(session_id, thread_id, last, min, max));
                    }
                    sector_local_min = None;
                    sector_local_max = None;
                    sector_last_key = None;
                    last_sector_stats_report = Instant::now();
                }
            }
        }
    } else if mode == "random" {
        let mut rng = OsRng;
        while running.load(Ordering::SeqCst) {
            let current = random_key_in_range(start_key, end_key, &mut rng);
            update_minmax(current, &mut local_min, &mut local_max);
            update_minmax(current, &mut sector_local_min, &mut sector_local_max);
            sector_last_key = Some(current);
            let _ = tx.send(WorkerMessage::LastKey(session_id, thread_id, current));

            let key_bytes = u256_to_bytes(current);
            if let Ok(secret) = SecretKey::from_slice(&key_bytes) {
                let pub_key = PublicKey::from_secret_key(&secp, &secret);
                let compressed = pub_key.serialize();
                let h160_compressed = hash160(&compressed);
                if target_hashes.contains(&h160_compressed) {
                    local_found += 1;
                    let _ = tx.send(WorkerMessage::Match(session_id, thread_id, key_bytes, h160_compressed, "compressed".into()));
                }
            }

            local_attempts += 1;

            if last_stats_report.elapsed() >= Duration::from_secs(1) {
                let _ = tx.send(WorkerMessage::Stats(session_id, thread_id, local_attempts, local_found));
                last_stats_report = Instant::now();
            }
            if last_minmax_report.elapsed() >= Duration::from_secs(10) {
                if let (Some(min), Some(max)) = (local_min, local_max) {
                    let _ = tx.send(WorkerMessage::MinMax(session_id, thread_id, min, max));
                }
                local_min = None;
                local_max = None;
                last_minmax_report = Instant::now();
            }
            if last_sector_stats_report.elapsed() >= Duration::from_secs(2) {
                if let (Some(min), Some(max), Some(last)) = (sector_local_min, sector_local_max, sector_last_key) {
                    let _ = tx.send(WorkerMessage::SectorStats(session_id, thread_id, last, min, max));
                }
                sector_local_min = None;
                sector_local_max = None;
                sector_last_key = None;
                last_sector_stats_report = Instant::now();
            }
        }
    } else if mode == "sequential" {
        let step = step;
        let mut current = start_key + U256::from(thread_id);
        while running.load(Ordering::SeqCst) && current <= end_key {
            update_minmax(current, &mut local_min, &mut local_max);
            update_minmax(current, &mut sector_local_min, &mut sector_local_max);
            sector_last_key = Some(current);
            let _ = tx.send(WorkerMessage::LastKey(session_id, thread_id, current));

            let key_bytes = u256_to_bytes(current);
            if let Ok(secret) = SecretKey::from_slice(&key_bytes) {
                let pub_key = PublicKey::from_secret_key(&secp, &secret);
                let compressed = pub_key.serialize();
                let h160_compressed = hash160(&compressed);
                if target_hashes.contains(&h160_compressed) {
                    local_found += 1;
                    let _ = tx.send(WorkerMessage::Match(session_id, thread_id, key_bytes, h160_compressed, "compressed".into()));
                }
            }

            local_attempts += 1;
            current += step;

            if last_stats_report.elapsed() >= Duration::from_secs(1) {
                let _ = tx.send(WorkerMessage::Stats(session_id, thread_id, local_attempts, local_found));
                last_stats_report = Instant::now();
            }
            if last_minmax_report.elapsed() >= Duration::from_secs(10) {
                if let (Some(min), Some(max)) = (local_min, local_max) {
                    let _ = tx.send(WorkerMessage::MinMax(session_id, thread_id, min, max));
                }
                local_min = None;
                local_max = None;
                last_minmax_report = Instant::now();
            }
            if last_sector_stats_report.elapsed() >= Duration::from_secs(2) {
                if let (Some(min), Some(max), Some(last)) = (sector_local_min, sector_local_max, sector_last_key) {
                    let _ = tx.send(WorkerMessage::SectorStats(session_id, thread_id, last, min, max));
                }
                sector_local_min = None;
                sector_local_max = None;
                sector_last_key = None;
                last_sector_stats_report = Instant::now();
            }
        }
    } else if mode == "random_sectors" {
        let mut rng = OsRng;
        while running.load(Ordering::SeqCst) {
            let current = random_key_in_range(start_key, end_key, &mut rng);
            update_minmax(current, &mut local_min, &mut local_max);
            update_minmax(current, &mut sector_local_min, &mut sector_local_max);
            sector_last_key = Some(current);
            let _ = tx.send(WorkerMessage::LastKey(session_id, thread_id, current));

            let key_bytes = u256_to_bytes(current);
            if let Ok(secret) = SecretKey::from_slice(&key_bytes) {
                let pub_key = PublicKey::from_secret_key(&secp, &secret);
                let compressed = pub_key.serialize();
                let h160_compressed = hash160(&compressed);
                if target_hashes.contains(&h160_compressed) {
                    local_found += 1;
                    let _ = tx.send(WorkerMessage::Match(session_id, thread_id, key_bytes, h160_compressed, "compressed".into()));
                }
            }

            local_attempts += 1;

            if last_stats_report.elapsed() >= Duration::from_secs(1) {
                let _ = tx.send(WorkerMessage::Stats(session_id, thread_id, local_attempts, local_found));
                last_stats_report = Instant::now();
            }
            if last_minmax_report.elapsed() >= Duration::from_secs(10) {
                if let (Some(min), Some(max)) = (local_min, local_max) {
                    let _ = tx.send(WorkerMessage::MinMax(session_id, thread_id, min, max));
                }
                local_min = None;
                local_max = None;
                last_minmax_report = Instant::now();
            }
            if last_sector_stats_report.elapsed() >= Duration::from_secs(2) {
                if let (Some(min), Some(max), Some(last)) = (sector_local_min, sector_local_max, sector_last_key) {
                    let _ = tx.send(WorkerMessage::SectorStats(session_id, thread_id, last, min, max));
                }
                sector_local_min = None;
                sector_local_max = None;
                sector_last_key = None;
                last_sector_stats_report = Instant::now();
            }
        }
    }

    let _ = tx.send(WorkerMessage::Stats(session_id, thread_id, local_attempts, local_found));
    let _ = tx.send(WorkerMessage::Finished(session_id, thread_id));
}

fn max_key() -> U256 {
    U256::from_str_radix("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364140", 16).unwrap()
}

fn min_key() -> U256 {
    U256::from(1u64)
}

fn compute_offset(total: U256, raw: &BigUint) -> U256 {
    let total_bytes = u256_to_bytes(total);
    let total_big = BigUint::from_bytes_be(&total_bytes);
    let offset_big = (total_big * raw) / max_percent_raw();
    let offset_bytes = offset_big.to_bytes_be();
    let mut bytes = [0u8; 32];
    let start = 32 - offset_bytes.len();
    bytes[start..].copy_from_slice(&offset_bytes);
    U256::from_big_endian(&bytes)
}

#[derive(Default, Clone)]
struct ThreadStats {
    attempts: u64,
    found: u32,
}

pub enum GuiMessage {
    Stats { session_id: u64, total_attempts: u64, total_found: u32, speed: f64 },
    MinMax { session_id: u64, min_hex: String, max_hex: String },
    MatchFound { session_id: u64, private_key: String, address: String, addr_type: String, hash160: String, all_addresses: (String, String, String, String, String, String, String) },
    LastKey { session_id: u64, thread_id: usize, key_hex: String },
    Finished { session_id: u64 },
    Error(String),
    CarouselTrigger { session_id: u64 },
    SectorStats { session_id: u64, thread_id: usize, last_key: String, min_hex: String, max_hex: String },
    HashLoadProgress { loaded: usize, total: Option<usize> },
    HashLoadFinished { hashes: Arc<HashSet<[u8; 20]>>, count: usize, file_path: String, file_type: String },
}

#[derive(Clone)]
struct SearchConfig {
    hash_file: Option<String>,
    hash_bin: Option<String>,
    output_file: Option<String>,
    threads: usize,
    range_percent: (BigUint, BigUint),
    stats_batch_size: u64,
    carousel_enabled: bool,
    carousel_keys_limit: u64,
    carousel_step_percent: BigUint,
    generation_mode: String,
    sequential_state_file: Option<String>,
}

#[derive(Serialize, Deserialize)]
struct SequentialState {
    last_keys: Vec<String>,
    session_id: u64,
}

pub struct SearchEngine {
    config: SearchConfig,
    session_id: u64,
    target_hashes: Arc<HashSet<[u8; 20]>>,
    found_keys: Arc<Mutex<HashSet<[u8; 32]>>>,
    start_key: U256,
    end_key: U256,
    _step: U256,
    running: Arc<AtomicBool>,
    stop_rx: Receiver<()>,
    tx: Sender<WorkerMessage>,
    rx: Receiver<WorkerMessage>,
    handles: Vec<thread::JoinHandle<()>>,
    thread_stats: Vec<ThreadStats>,
    total_attempts: u64,
    total_found: u32,
    last_stats_send: u64,
    last_force_send: Instant,
    gui_tx: crossbeam_channel::Sender<GuiMessage>,
    start_time: Option<Instant>,
    stats_batch_size: u64,
    carousel_triggered: bool,
    last_carousel_check_attempts: u64,
    worker_starts: Vec<U256>,
}

impl SearchEngine {
    fn new(
        session_id: u64,
        config: SearchConfig,
        gui_tx: crossbeam_channel::Sender<GuiMessage>,
        stop_rx: Receiver<()>,
        target_hashes: Arc<HashSet<[u8; 20]>>,
    ) -> Result<Self> {
        let threads = config.threads;
        let output_file = config.output_file.clone();
        let range_percent = config.range_percent.clone();
        let stats_batch_size = config.stats_batch_size;

        let found_keys = Arc::new(Mutex::new(HashSet::new()));

        if let Some(ref path) = output_file {
            if let Ok(file) = File::open(path) {
                let reader = BufReader::new(file);
                for line in reader.lines() {
                    let line = line?;
                    let parts: Vec<&str> = line.split('\t').collect();
                    if parts.len() >= 1 {
                        if let Ok(key_bytes) = hex::decode(parts[0]) {
                            if key_bytes.len() == 32 {
                                let mut arr = [0u8; 32];
                                arr.copy_from_slice(&key_bytes);
                                found_keys.lock().unwrap().insert(arr);
                            }
                        }
                    }
                }
                eprintln!("Loaded {} already found keys from {}", found_keys.lock().unwrap().len(), path);
            }
        }

        let total_keys = max_key() - min_key() + U256::from(1u64);
        let total_minus_1 = total_keys - U256::from(1u64);
        let (start_raw, end_raw) = range_percent;

        let start_offset = compute_offset(total_minus_1, &start_raw);
        let end_offset = compute_offset(total_minus_1, &end_raw);

        let start_key = min_key() + start_offset;
        let end_key = min_key() + end_offset;

        if start_key > end_key {
            bail!("Внутренняя ошибка: start_key > end_key");
        }

        let running = Arc::new(AtomicBool::new(true));
        let (tx, rx) = unbounded();

        let worker_starts = if config.generation_mode == "sequential" {
            if let Some(ref state_path) = config.sequential_state_file {
                if let Ok(file) = File::open(state_path) {
                    if let Ok(state) = serde_json::from_reader::<_, SequentialState>(file) {
                        if state.session_id == session_id {
                            let mut starts = Vec::with_capacity(threads);
                            for (i, hex_key) in state.last_keys.iter().enumerate() {
                                if i >= threads {
                                    break;
                                }
                                if let Ok(bytes) = hex::decode(hex_key) {
                                    if bytes.len() == 32 {
                                        let mut arr = [0u8; 32];
                                        arr.copy_from_slice(&bytes);
                                        starts.push(bytes_to_u256(&arr));
                                        continue;
                                    }
                                }
                                starts.push(start_key + U256::from(i));
                            }
                            starts
                        } else {
                            (0..threads).map(|i| start_key + U256::from(i)).collect()
                        }
                    } else {
                        (0..threads).map(|i| start_key + U256::from(i)).collect()
                    }
                } else {
                    (0..threads).map(|i| start_key + U256::from(i)).collect()
                }
            } else {
                (0..threads).map(|i| start_key + U256::from(i)).collect()
            }
        } else {
            Vec::new()
        };

        Ok(Self {
            config,
            session_id,
            target_hashes,
            found_keys,
            start_key,
            end_key,
            _step: U256::from(threads),
            running,
            stop_rx,
            tx,
            rx,
            handles: Vec::new(),
            thread_stats: Vec::new(),
            total_attempts: 0,
            total_found: 0,
            last_stats_send: 0,
            last_force_send: Instant::now(),
            gui_tx,
            start_time: None,
            stats_batch_size,
            carousel_triggered: false,
            last_carousel_check_attempts: 0,
            worker_starts,
        })
    }

    fn run(&mut self) -> Result<()> {
        self.start_time = Some(Instant::now());
        let threads = self.config.threads;

        let session_id = self.session_id;

        for i in 0..threads {
            let (start, end) = if self.config.generation_mode == "random_sectors" {
                let total_range = self.end_key - self.start_key + U256::from(1);
                let threads_u256 = U256::from(threads);
                let part_size = total_range / threads_u256;
                let remainder = total_range % threads_u256;
                let i_u256 = U256::from(i);
                let part_start = if i == 0 {
                    self.start_key
                } else {
                    self.start_key + part_size * i_u256 + if i_u256 <= remainder { i_u256 } else { remainder }
                };
                let part_end = if i == threads - 1 {
                    self.end_key
                } else {
                    part_start + part_size - U256::from(1) + if i_u256 < remainder { U256::from(1) } else { U256::from(0) }
                };
                (part_start, part_end)
            } else if self.config.generation_mode == "sequential" && i < self.worker_starts.len() {
                (self.worker_starts[i], self.end_key)
            } else {
                (self.start_key, self.end_key)
            };

            let step = U256::from(threads);
            let running = self.running.clone();
            let tx = self.tx.clone();
            let target_hashes = self.target_hashes.clone();
            let mode = self.config.generation_mode.clone();

            let handle = thread::spawn(move || {
                worker_main(
                    session_id,
                    i,
                    start,
                    end,
                    step,
                    running,
                    tx,
                    target_hashes,
                    &mode,
                );
            });
            self.handles.push(handle);
            self.thread_stats.push(ThreadStats::default());
        }

        let mut last_minmax_display = Instant::now();
        let mut global_min: Option<U256> = None;
        let mut global_max: Option<U256> = None;

        loop {
            select! {
                recv(self.rx) -> msg => {
                    match msg {
                        Ok(WorkerMessage::Stats(session_id, thread_id, attempts, found)) => {
                            if session_id != self.session_id { continue; }
                            self.thread_stats[thread_id].attempts = attempts;
                            self.thread_stats[thread_id].found = found;
                            self.recalc_totals();
                        }
                        Ok(WorkerMessage::Match(session_id, thread_id, key_bytes, hash160, addr_type)) => {
                            if session_id != self.session_id { continue; }
                            let mut found_keys = self.found_keys.lock().unwrap();
                            if !found_keys.contains(&key_bytes) {
                                found_keys.insert(key_bytes);
                                drop(found_keys);

                                if let Ok(addresses) = generate_addresses(&key_bytes) {
                                    if let Err(e) = self.save_match(&addresses) {
                                        let _ = self.gui_tx.send(GuiMessage::Error(format!("Ошибка сохранения: {}", e)));
                                    }
                                    let addresses_clone = addresses.clone();
                                    let _ = self.gui_tx.send(GuiMessage::MatchFound {
                                        session_id,
                                        private_key: addresses.0,
                                        address: addresses.2,
                                        addr_type,
                                        hash160: hex::encode(hash160),
                                        all_addresses: addresses_clone,
                                    });
                                }
                                self.total_found += 1;
                                self.thread_stats[thread_id].found += 1;
                            }
                        }
                        Ok(WorkerMessage::MinMax(session_id, _thread_id, min_key, max_key)) => {
                            if session_id != self.session_id { continue; }
                            global_min = Some(global_min.map_or(min_key, |g| if min_key < g { min_key } else { g }));
                            global_max = Some(global_max.map_or(max_key, |g| if max_key > g { max_key } else { g }));
                        }
                        Ok(WorkerMessage::LastKey(session_id, thread_id, key)) => {
                            if session_id != self.session_id { continue; }
                            let _ = self.gui_tx.send(GuiMessage::LastKey {
                                session_id,
                                thread_id,
                                key_hex: hex::encode(u256_to_bytes(key)),
                            });
                        }
                        Ok(WorkerMessage::Finished(session_id, _thread_id)) => {
                            if session_id != self.session_id { continue; }
                        }
                        Ok(WorkerMessage::SectorStats(session_id, thread_id, last_key, min_key, max_key)) => {
                            if session_id != self.session_id { continue; }
                            let _ = self.gui_tx.send(GuiMessage::SectorStats {
                                session_id,
                                thread_id,
                                last_key: hex::encode(u256_to_bytes(last_key)),
                                min_hex: hex::encode(u256_to_bytes(min_key)),
                                max_hex: hex::encode(u256_to_bytes(max_key)),
                            });
                        }
                        Err(_) => break,
                    }
                }
                recv(self.stop_rx) -> _ => {
                    self.running.store(false, Ordering::SeqCst);
                    eprintln!("\nОстановка потоков...");
                    break;
                }
            }

            if !self.running.load(Ordering::SeqCst) {
                break;
            }

            if self.config.carousel_enabled && !self.carousel_triggered {
                let limit = self.config.carousel_keys_limit;
                if limit > 0 && self.total_attempts >= self.last_carousel_check_attempts + limit {
                    eprintln!("[КАРУСЕЛЬ] Достигнут лимит {} ключей, отправка сигнала", limit);
                    let _ = self.gui_tx.send(GuiMessage::CarouselTrigger { session_id: self.session_id });
                    self.carousel_triggered = true;
                }
            }

            let now = Instant::now();
            if self.total_attempts - self.last_stats_send >= self.stats_batch_size
                || (now - self.last_force_send >= Duration::from_secs(10) && self.total_attempts > self.last_stats_send)
            {
                let speed = if let Some(start) = self.start_time {
                    self.total_attempts as f64 / start.elapsed().as_secs_f64()
                } else { 0.0 };
                let _ = self.gui_tx.send(GuiMessage::Stats {
                    session_id: self.session_id,
                    total_attempts: self.total_attempts,
                    total_found: self.total_found,
                    speed,
                });
                self.last_stats_send = self.total_attempts;
                self.last_force_send = now;
            }

            if last_minmax_display.elapsed() >= Duration::from_secs(60) {
                if let (Some(min), Some(max)) = (global_min, global_max) {
                    let _ = self.gui_tx.send(GuiMessage::MinMax {
                        session_id: self.session_id,
                        min_hex: hex::encode(u256_to_bytes(min)),
                        max_hex: hex::encode(u256_to_bytes(max)),
                    });
                }
                global_min = None;
                global_max = None;
                last_minmax_display = Instant::now();
            }
        }

        for handle in self.handles.drain(..) {
            let _ = handle.join();
        }

        if self.config.generation_mode == "sequential" {
            if let Some(ref state_path) = self.config.sequential_state_file {
                let last_keys: Vec<String> = self.thread_stats.iter().enumerate().map(|(_, _)| "".to_string()).collect();
                let state = SequentialState {
                    last_keys,
                    session_id: self.session_id,
                };
                let _ = std::fs::write(state_path, serde_json::to_string_pretty(&state).unwrap());
            }
        }

        let _ = self.gui_tx.send(GuiMessage::Finished { session_id: self.session_id });
        Ok(())
    }

    fn recalc_totals(&mut self) {
        self.total_attempts = self.thread_stats.iter().map(|s| s.attempts).sum();
        self.total_found = self.thread_stats.iter().map(|s| s.found).sum();
    }

    fn save_match(&self, addresses: &(String, String, String, String, String, String, String)) -> Result<()> {
        let line = format!(
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
            addresses.0, addresses.1, addresses.2, addresses.3, addresses.4, addresses.5, addresses.6
        );
        if let Some(ref output_path) = self.config.output_file {
            let mut file = std::fs::OpenOptions::new()
                .create(true)
                .append(true)
                .open(output_path)?;
            file.write_all(line.as_bytes())?;
        } else {
            print!("{}", line);
        }
        Ok(())
    }
}

#[derive(Clone, Serialize, Deserialize)]
struct SessionInfo {
    session_id: u64,
    start_time: String,
    end_time: Option<String>,
    duration_secs: Option<u64>,
    mode: String,
    generator_name: String,
    range_percent: (String, String),
    total_attempts: u64,
    total_found: u32,
    avg_speed: f64,
    hash_file: String,
    output_file: String,
    carousel_enabled: bool,
    enable_workers: bool,
}

#[derive(Serialize, Deserialize)]
struct AppConfig {
    last_hash_file: Option<String>,
    last_hash_bin: Option<String>,
    status_color: Option<[f32; 3]>,
    carousel_enabled: bool,
    carousel_keys_limit_input: u64,
    carousel_step_input: String,
    carousel_step_hex_input: String,
    start_percent_str: String,
    end_percent_str: String,
    start_hex_str: String,
    end_hex_str: String,
    threads_input: usize,
    generation_mode: String,
    sequential_state_file: Option<String>,
}

impl Default for AppConfig {
    fn default() -> Self {
        let tiny = format!("0.{:0>width$}", "1", width = PERCENT_DECIMALS);
        let tiny2 = format!("0.{:0>width$}", "2", width = PERCENT_DECIMALS);
        Self {
            last_hash_file: None,
            last_hash_bin: None,
            status_color: Some([0.0, 1.0, 0.0]),
            carousel_enabled: true,
            carousel_keys_limit_input: 13,
            carousel_step_input: tiny.clone(),
            carousel_step_hex_input: "0000000000000000000000000000000000000000000000000000000000000001".to_string(),
            start_percent_str: tiny,
            end_percent_str: tiny2,
            start_hex_str: "0000000000000000000000000000000000000000000000000000000000000001".to_string(),
            end_hex_str: "0000000000000000000000000000000000000000000000000000000000000002".to_string(),
            threads_input: num_cpus::get(),
            generation_mode: "sector".to_string(),
            sequential_state_file: None,
        }
    }
}

struct WorkerStatsGui {
    thread_id: usize,
    last_key: String,
    min_2s: String,
    max_2s: String,
    last_update: Instant,
}

impl Default for WorkerStatsGui {
    fn default() -> Self {
        Self {
            thread_id: 0,
            last_key: "-".to_string(),
            min_2s: "-".to_string(),
            max_2s: "-".to_string(),
            last_update: Instant::now(),
        }
    }
}

struct FoundKeyEntry {
    private_key: String,
    ripemd160: String,
    legacy_uncompressed: String,
    legacy_compressed: String,
    bech32: String,
}

#[derive(PartialEq)]
enum TableOrientation {
    Horizontal,
    Vertical,
}

struct App {
    config: SearchConfig,
    gui_tx: crossbeam_channel::Sender<GuiMessage>,
    gui_rx: crossbeam_channel::Receiver<GuiMessage>,
    current_session_id: u64,
    stop_tx: Option<crossbeam_channel::Sender<()>>,
    search_handle: Option<thread::JoinHandle<()>>,
    running: bool,
    stats: Option<(u64, u32, f64)>,
    min_max: Option<(String, String)>,
    found_keys: Vec<FoundKeyEntry>,
    carousel_log: Vec<String>,
    sessions: Vec<SessionInfo>,
    current_session_start: Option<DateTime<Local>>,
    sys: System,
    memory_usage: f64,
    memory_total: u64,
    show_error: Option<String>,
    error_timer: Option<Instant>,
    start_raw: BigUint,
    end_raw: BigUint,
    start_percent_str: String,
    end_percent_str: String,
    start_hex_str: String,
    end_hex_str: String,
    start_key: U256,
    end_key: U256,
    threads_input: usize,
    loaded_hashes_count: usize,
    range_display: String,
    selected_tab: usize,
    current_speed: f64,
    sessions_desc: bool,
    carousel_enabled: bool,
    carousel_keys_limit_input: u64,
    carousel_step_input: String,
    carousel_step_raw: BigUint,
    carousel_step_hex_str: String,
    carousel_step_hex_raw: U256,
    carousel_desc: bool,
    //last_key: String,
    status_message: String,
    status_color: Color32,
    last_carousel_attempts: u64,
    last_carousel_start: Option<Instant>,
    sector_stats: Vec<WorkerStatsGui>,
    sector_stats_enabled: bool,
    end_manually_edited: bool,
    loading_progress: Option<String>,
    loaded_hashes: Option<Arc<HashSet<[u8; 20]>>>,
    orientation: TableOrientation,
    scroll_offset_x: f32,
    generation_mode: String,
    sequential_state_file: Option<String>,
}

impl App {
    fn new(cc: &CreationContext<'_>) -> Self {
        // Загрузка шрифта Courier New
        let mut fonts = FontDefinitions::default();
        // Пытаемся загрузить cour.ttf из текущей директории или системного пути Windows
        if let Ok(courier_data) = std::fs::read("cour.ttf") {
            fonts.font_data.insert("Courier New".to_owned(), FontData::from_owned(courier_data));
            if let Some(monospace_family) = fonts.families.get_mut(&FontFamily::Monospace) {
                monospace_family.insert(0, "Courier New".to_owned());
            }
        } else if let Ok(courier_data) = std::fs::read("C:\\Windows\\Fonts\\cour.ttf") {
            fonts.font_data.insert("Courier New".to_owned(), FontData::from_owned(courier_data));
            if let Some(monospace_family) = fonts.families.get_mut(&FontFamily::Monospace) {
                monospace_family.insert(0, "Courier New".to_owned());
            }
        }
        cc.egui_ctx.set_fonts(fonts);

        Self::play_sound();

        let (gui_tx, gui_rx) = crossbeam_channel::unbounded();

        let mut app_config: AppConfig = if let Ok(file) = File::open("app_config.json") {
            serde_json::from_reader(file).unwrap_or_default()
        } else {
            AppConfig::default()
        };

        let default_tiny = format!("0.{:0>width$}", "1", width = PERCENT_DECIMALS);
        let default_tiny2 = format!("0.{:0>width$}", "2", width = PERCENT_DECIMALS);

        let is_valid_percent = |s: &str| -> bool {
            if let Some(dot_pos) = s.find('.') {
                let frac_part = &s[dot_pos+1..];
                frac_part.len() == PERCENT_DECIMALS
            } else {
                false
            }
        };

        if !is_valid_percent(&app_config.start_percent_str) {
            app_config.start_percent_str = default_tiny.clone();
        }
        if !is_valid_percent(&app_config.end_percent_str) {
            app_config.end_percent_str = default_tiny2.clone();
        }
        if !is_valid_percent(&app_config.carousel_step_input) {
            app_config.carousel_step_input = default_tiny.clone();
        }

        let status_color = if let Some(c) = app_config.status_color {
            Color32::from_rgb((c[0] * 255.0) as u8, (c[1] * 255.0) as u8, (c[2] * 255.0) as u8)
        } else {
            Color32::GREEN
        };

        let step_raw = parse_percent_raw(&app_config.carousel_step_input).unwrap_or_else(|_| BigUint::from(1u32));

        let mut config = SearchConfig {
            range_percent: (BigUint::zero(), percent_scale()),
            threads: app_config.threads_input,
            hash_file: app_config.last_hash_file.clone(),
            hash_bin: app_config.last_hash_bin.clone(),
            output_file: Some("found_keys.txt".to_string()),
            stats_batch_size: 1_200_000,
            carousel_enabled: app_config.carousel_enabled,
            carousel_keys_limit: app_config.carousel_keys_limit_input * 1_000_000,
            carousel_step_percent: step_raw.clone(),
            generation_mode: app_config.generation_mode.clone(),
            sequential_state_file: app_config.sequential_state_file.clone(),
        };

        let (start_raw, end_raw, start_key, end_key) = if let (Ok(s), Ok(e)) = (parse_percent_raw(&app_config.start_percent_str), parse_percent_raw(&app_config.end_percent_str)) {
            let total_keys = max_key() - min_key() + U256::from(1u64);
            let total_minus_1 = total_keys - U256::from(1u64);
            let start_offset = compute_offset(total_minus_1, &s);
            let end_offset = compute_offset(total_minus_1, &e);
            let start_key = min_key() + start_offset;
            let end_key = min_key() + end_offset;
            (s, e, start_key, end_key)
        } else {
            (BigUint::zero(), percent_scale(), min_key(), min_key())
        };
        config.range_percent = (start_raw.clone(), end_raw.clone());

        let threads_input = config.threads;

        let mut sys = System::new();
        sys.refresh_memory();
        let memory_total = sys.total_memory();

        let start_percent_str = app_config.start_percent_str.clone();
        let end_percent_str = app_config.end_percent_str.clone();
        let start_hex_str = app_config.start_hex_str.clone();
        let end_hex_str = app_config.end_hex_str.clone();

        let loaded_hashes_count = 0;

        let generation_mode = config.generation_mode.clone();
        let sequential_state_file = config.sequential_state_file.clone();

        // Инициализация HEX шага карусели
        let (step_hex_raw, step_hex_str) = Self::percent_to_hex_step(&step_raw);
        let carousel_step_hex_raw = step_hex_raw;
        let carousel_step_hex_str = if app_config.carousel_step_hex_input.len() == 64 && app_config.carousel_step_hex_input.chars().all(|c| c.is_ascii_hexdigit()) {
            app_config.carousel_step_hex_input.clone()
        } else {
            step_hex_str.clone()
        };

        let mut app = Self {
            config,
            gui_tx,
            gui_rx,
            current_session_id: 0,
            stop_tx: None,
            search_handle: None,
            running: false,
            stats: None,
            min_max: None,
            found_keys: Vec::new(),
            carousel_log: Vec::new(),
            sessions: Vec::new(),
            current_session_start: None,
            sys,
            memory_usage: 0.0,
            memory_total,
            show_error: None,
            error_timer: None,
            start_raw,
            end_raw,
            start_percent_str,
            end_percent_str,
            start_hex_str,
            end_hex_str,
            start_key,
            end_key,
            threads_input,
            loaded_hashes_count,
            range_display: String::new(),
            selected_tab: 0,
            current_speed: 0.0,
            sessions_desc: true,
            carousel_enabled: app_config.carousel_enabled,
            carousel_keys_limit_input: app_config.carousel_keys_limit_input,
            carousel_step_input: app_config.carousel_step_input.clone(),
            carousel_step_raw: step_raw,
            carousel_step_hex_str,
            carousel_step_hex_raw,
            carousel_desc: true,
            //last_key: String::new(),
            status_message: String::new(),
            status_color,
            last_carousel_attempts: 0,
            last_carousel_start: None,
            sector_stats: Vec::new(),
            sector_stats_enabled: false,
            end_manually_edited: false,
            loading_progress: None,
            loaded_hashes: None,
            orientation: TableOrientation::Horizontal,
            scroll_offset_x: 0.0,
            generation_mode,
            sequential_state_file,
        };

        // Принудительная установка HEX диапазона 0x1 ... 0x2 при первом запуске или если сохранённый конфиг использует дефолтные проценты
        if app_config.start_percent_str == default_tiny && app_config.end_percent_str == default_tiny2 {
            let desired_start_hex = "0000000000000000000000000000000000000000000000000000000000000001";
            let desired_end_hex = "0000000000000000000000000000000000000000000000000000000000000002";
            if let Some(start_key_fixed) = Self::hex_to_key(desired_start_hex) {
                let start_raw_fixed = Self::key_to_percent_raw(start_key_fixed);
                if start_raw_fixed <= max_percent_raw() {
                    let start_percent_str_fixed = Self::format_percent(&start_raw_fixed);
                    app.start_raw = start_raw_fixed;
                    app.start_percent_str = start_percent_str_fixed;
                    app.start_hex_str = desired_start_hex.to_string();
                    app.start_key = start_key_fixed;
                }
            }
            if let Some(end_key_fixed) = Self::hex_to_key(desired_end_hex) {
                let end_raw_fixed = Self::key_to_percent_raw(end_key_fixed);
                if end_raw_fixed <= max_percent_raw() && end_raw_fixed >= app.start_raw {
                    let end_percent_str_fixed = Self::format_percent(&end_raw_fixed);
                    app.end_raw = end_raw_fixed;
                    app.end_percent_str = end_percent_str_fixed;
                    app.end_hex_str = desired_end_hex.to_string();
                    app.end_key = end_key_fixed;
                    app.config.range_percent = (app.start_raw.clone(), app.end_raw.clone());
                    app.update_range_display();
                }
            }
        }

        app.update_range_display();
        app.load_sessions_from_file();
        app.load_found_keys_from_file();
        // Файл хешей НЕ загружается автоматически
        app
    }

    // ================== Вспомогательные функции для конвертации ==================
    fn key_to_hex(key: &U256) -> String {
        format!("{:064x}", key)
    }

    fn hex_to_key(hex: &str) -> Option<U256> {
        let hex = hex.trim();
        if hex.len() > 64 { return None; }
        let padded = format!("{:0>64}", hex);
        if let Ok(key) = U256::from_str_radix(&padded, 16) {
            if key >= min_key() && key <= max_key() {
                Some(key)
            } else {
                None
            }
        } else {
            None
        }
    }

    fn normalize_hex(hex: &str) -> String {
        let trimmed = hex.trim();
        if trimmed.len() <= 64 && trimmed.chars().all(|c| c.is_ascii_hexdigit()) {
            format!("{:0>64}", trimmed)
        } else {
            hex.to_string()
        }
    }

    fn key_to_percent_raw(key: U256) -> BigUint {
        if key < min_key() || key > max_key() {
            return BigUint::zero();
        }
        let total_keys = max_key() - min_key() + U256::from(1u64);
        let total_minus_1 = total_keys - U256::from(1u64);
        let offset = key - min_key();
        let offset_big = BigUint::from_bytes_be(&u256_to_bytes(offset));
        let total_big = BigUint::from_bytes_be(&u256_to_bytes(total_minus_1));
        (offset_big * max_percent_raw()) / total_big
    }

    fn percent_to_key(raw: &BigUint) -> U256 {
        let total_keys = max_key() - min_key() + U256::from(1u64);
        let total_minus_1 = total_keys - U256::from(1u64);
        let offset = compute_offset(total_minus_1, raw);
        min_key() + offset
    }

    fn percent_to_hex_step(percent: &BigUint) -> (U256, String) {
        let total_keys = max_key() - min_key() + U256::from(1u64);
        let total_minus_1 = total_keys - U256::from(1u64);
        let offset = compute_offset(total_minus_1, percent);
        (offset, Self::key_to_hex(&offset))
    }

    fn hex_step_to_percent(hex: &str) -> Option<BigUint> {
        if let Some(offset) = Self::hex_to_key(hex) {
            if offset >= min_key() && offset <= max_key() {
                let total_keys = max_key() - min_key() + U256::from(1u64);
                let total_minus_1 = total_keys - U256::from(1u64);
                let offset_big = BigUint::from_bytes_be(&u256_to_bytes(offset));
                let total_big = BigUint::from_bytes_be(&u256_to_bytes(total_minus_1));
                let percent_raw = (offset_big * max_percent_raw()) / total_big;
                if percent_raw <= max_percent_raw() {
                    return Some(percent_raw);
                }
            }
        }
        None
    }

    // ================== Синхронизация ==================
    fn sync_hex_from_percent_start(&mut self) {
        self.start_key = Self::percent_to_key(&self.start_raw);
        self.start_hex_str = Self::key_to_hex(&self.start_key);
    }

    fn sync_hex_from_percent_end(&mut self) {
        self.end_key = Self::percent_to_key(&self.end_raw);
        self.end_hex_str = Self::key_to_hex(&self.end_key);
    }

    fn apply_hex_start(&mut self) {
        let normalized = Self::normalize_hex(&self.start_hex_str);
        if normalized.len() != 64 { return; }
        if let Some(key) = Self::hex_to_key(&normalized) {
            self.start_key = key;
            self.start_raw = Self::key_to_percent_raw(key);
            if self.start_raw <= max_percent_raw() {
                let percent_str = Self::format_percent(&self.start_raw);
                if self.start_raw <= self.end_raw {
                    self.start_percent_str = percent_str;
                    self.start_hex_str = normalized;
                    self.config.range_percent = (self.start_raw.clone(), self.end_raw.clone());
                    self.update_range_display();
                    self.save_config();
                    return;
                }
            }
        }
        self.sync_hex_from_percent_start();
    }

    fn apply_hex_end(&mut self) {
        let normalized = Self::normalize_hex(&self.end_hex_str);
        if normalized.len() != 64 { return; }
        if let Some(key) = Self::hex_to_key(&normalized) {
            self.end_key = key;
            self.end_raw = Self::key_to_percent_raw(key);
            if self.end_raw <= max_percent_raw() {
                let percent_str = Self::format_percent(&self.end_raw);
                if self.start_raw <= self.end_raw {
                    self.end_percent_str = percent_str;
                    self.end_hex_str = normalized;
                    self.config.range_percent = (self.start_raw.clone(), self.end_raw.clone());
                    self.update_range_display();
                    self.save_config();
                    return;
                }
            }
        }
        self.sync_hex_from_percent_end();
    }

    fn copy_hex_start(&self) {
        self.copy_to_clipboard(&self.start_hex_str);
    }

    fn copy_hex_end(&self) {
        self.copy_to_clipboard(&self.end_hex_str);
    }

    fn paste_hex_start(&mut self) {
        if let Ok(mut clipboard) = arboard::Clipboard::new() {
            if let Ok(text) = clipboard.get_text() {
                let trimmed = text.trim();
                if trimmed.len() <= 64 && trimmed.chars().all(|c| c.is_ascii_hexdigit()) {
                    self.start_hex_str = format!("{:0>64}", trimmed);
                    self.apply_hex_start();
                }
            }
        }
    }

    fn paste_hex_end(&mut self) {
        if let Ok(mut clipboard) = arboard::Clipboard::new() {
            if let Ok(text) = clipboard.get_text() {
                let trimmed = text.trim();
                if trimmed.len() <= 64 && trimmed.chars().all(|c| c.is_ascii_hexdigit()) {
                    self.end_hex_str = format!("{:0>64}", trimmed);
                    self.apply_hex_end();
                }
            }
        }
    }

    fn sync_step_from_percent(&mut self) {
        let (hex_raw, hex_str) = Self::percent_to_hex_step(&self.carousel_step_raw);
        self.carousel_step_hex_raw = hex_raw;
        self.carousel_step_hex_str = hex_str;
        self.config.carousel_step_percent = self.carousel_step_raw.clone();
        self.save_config();
    }

    fn sync_step_from_hex(&mut self) {
        if let Some(percent) = Self::hex_step_to_percent(&self.carousel_step_hex_str) {
            self.carousel_step_raw = percent.clone();
            self.carousel_step_input = Self::format_percent(&percent);
            self.config.carousel_step_percent = percent.clone();
            let (hex_raw, _) = Self::percent_to_hex_step(&percent);
            self.carousel_step_hex_raw = hex_raw;
            self.save_config();
        } else {
            self.sync_step_from_percent();
        }
    }

    fn apply_hex_step(&mut self) {
        let normalized = Self::normalize_hex(&self.carousel_step_hex_str);
        if normalized.len() == 64 {
            self.carousel_step_hex_str = normalized;
            self.sync_step_from_hex();
        } else {
            self.sync_step_from_percent();
        }
    }

    fn copy_hex_step(&self) {
        self.copy_to_clipboard(&self.carousel_step_hex_str);
    }

    fn paste_hex_step(&mut self) {
        if let Ok(mut clipboard) = arboard::Clipboard::new() {
            if let Ok(text) = clipboard.get_text() {
                let trimmed = text.trim();
                if trimmed.len() <= 64 && trimmed.chars().all(|c| c.is_ascii_hexdigit()) {
                    self.carousel_step_hex_str = format!("{:0>64}", trimmed);
                    self.apply_hex_step();
                }
            }
        }
    }

    // ================== Остальные методы ==================
    fn play_sound() {
        std::thread::spawn(|| {
            use rodio::{Decoder, OutputStream, Sink};
            use std::fs::File;
            use std::io::BufReader;

            let file_path = "alerta.wav";
            if let Ok(file) = File::open(file_path) {
                if let Ok(source) = Decoder::new(BufReader::new(file)) {
                    if let Ok((_stream, stream_handle)) = OutputStream::try_default() {
                        if let Ok(sink) = Sink::try_new(&stream_handle) {
                            sink.append(source);
                            sink.sleep_until_end();
                        }
                    }
                }
            }
        });
    }

    fn copy_to_clipboard(&self, text: &str) {
        if let Ok(mut clipboard) = arboard::Clipboard::new() {
            let _ = clipboard.set_text(text);
        }
    }

    fn open_directory(&self) {
        if let Some(ref path) = self.config.output_file {
            if let Some(parent) = std::path::Path::new(path).parent() {
                let _ = open::that(parent);
            }
        }
    }

    fn open_file(&self) {
        if let Some(ref path) = self.config.output_file {
            let _ = open::that(path);
        }
    }

    fn load_found_keys_from_file(&mut self) {
        if let Some(ref path) = self.config.output_file {
            if let Ok(file) = File::open(path) {
                let reader = BufReader::new(file);
                for line in reader.lines() {
                    let line = line.unwrap_or_default();
                    if line.trim().is_empty() {
                        continue;
                    }
                    let parts: Vec<&str> = line.split('\t').collect();
                    if parts.len() >= 7 {
                        let entry = FoundKeyEntry {
                            private_key: parts[0].to_string(),
                            ripemd160: parts[1].to_string(),
                            legacy_uncompressed: parts[2].to_string(),
                            legacy_compressed: parts[3].to_string(),
                            bech32: parts[6].to_string(),
                        };
                        self.found_keys.push(entry);
                    }
                }
                while self.found_keys.len() > 1000 {
                    self.found_keys.remove(0);
                }
            }
        }
    }

    fn reset_to_defaults(&mut self) {
        let desired_start_hex = "0000000000000000000000000000000000000000000000000000000000000001";
        let desired_end_hex = "0000000000000000000000000000000000000000000000000000000000000002";

        if let Some(start_key_fixed) = Self::hex_to_key(desired_start_hex) {
            let start_raw_fixed = Self::key_to_percent_raw(start_key_fixed);
            if start_raw_fixed <= max_percent_raw() {
                let start_percent_str_fixed = Self::format_percent(&start_raw_fixed);
                self.start_raw = start_raw_fixed;
                self.start_percent_str = start_percent_str_fixed;
                self.start_hex_str = desired_start_hex.to_string();
                self.start_key = start_key_fixed;
            }
        }
        if let Some(end_key_fixed) = Self::hex_to_key(desired_end_hex) {
            let end_raw_fixed = Self::key_to_percent_raw(end_key_fixed);
            if end_raw_fixed <= max_percent_raw() && end_raw_fixed >= self.start_raw {
                let end_percent_str_fixed = Self::format_percent(&end_raw_fixed);
                self.end_raw = end_raw_fixed;
                self.end_percent_str = end_percent_str_fixed;
                self.end_hex_str = desired_end_hex.to_string();
                self.end_key = end_key_fixed;
                self.config.range_percent = (self.start_raw.clone(), self.end_raw.clone());
                self.update_range_display();
            }
        }

        self.config.threads = num_cpus::get();
        self.threads_input = self.config.threads;

        self.config.hash_file = None;
        self.config.hash_bin = None;
        self.loaded_hashes_count = 0;
        self.loaded_hashes = None;

        self.config.output_file = Some("found_keys.txt".to_string());

        self.carousel_enabled = true;
        self.config.carousel_enabled = true;
        self.carousel_keys_limit_input = 13;
        self.config.carousel_keys_limit = 13_000_000;

        self.end_manually_edited = false;

        self.generation_mode = "sector".to_string();
        self.config.generation_mode = "sector".to_string();
        self.sequential_state_file = None;
        self.config.sequential_state_file = None;

        self.carousel_step_raw = BigUint::from(1u32);
        self.carousel_step_input = Self::format_percent(&self.carousel_step_raw);
        self.sync_step_from_percent();

        self.sync_hex_from_percent_start();
        self.sync_hex_from_percent_end();

        if self.running {
            self.stop_search_and_wait();
        }
        self.save_config();
    }

    fn format_percent(raw: &BigUint) -> String {
        let scale = percent_scale();
        let int = raw / &scale;
        let frac = raw % &scale;
        let frac_str = format!("{:0>width$}", frac.to_str_radix(10), width = PERCENT_DECIMALS);
        format!("{}.{}", int.to_str_radix(10), frac_str)
    }

    fn save_config(&self) {
        let app_config = AppConfig {
            last_hash_file: self.config.hash_file.clone(),
            last_hash_bin: self.config.hash_bin.clone(),
            status_color: Some([
                self.status_color.r() as f32 / 255.0,
                self.status_color.g() as f32 / 255.0,
                self.status_color.b() as f32 / 255.0,
            ]),
            carousel_enabled: self.carousel_enabled,
            carousel_keys_limit_input: self.carousel_keys_limit_input,
            carousel_step_input: self.carousel_step_input.clone(),
            carousel_step_hex_input: self.carousel_step_hex_str.clone(),
            start_percent_str: self.start_percent_str.clone(),
            end_percent_str: self.end_percent_str.clone(),
            start_hex_str: self.start_hex_str.clone(),
            end_hex_str: self.end_hex_str.clone(),
            threads_input: self.threads_input,
            generation_mode: self.generation_mode.clone(),
            sequential_state_file: self.sequential_state_file.clone(),
        };
        let _ = std::fs::write("app_config.json", serde_json::to_string_pretty(&app_config).unwrap());
    }

    fn apply_range_percent(&mut self) {
        if let (Ok(s), Ok(e)) = (parse_percent_raw(&self.start_percent_str), parse_percent_raw(&self.end_percent_str)) {
            if s <= e && s <= max_percent_raw() && e <= max_percent_raw() {
                self.start_raw = s;
                self.end_raw = e;
                self.config.range_percent = (self.start_raw.clone(), self.end_raw.clone());
                self.update_range_display();
                self.sync_hex_from_percent_start();
                self.sync_hex_from_percent_end();
            } else {
                self.show_error = Some("Некорректный диапазон процентов".to_string());
                self.error_timer = Some(Instant::now());
            }
        } else {
            self.start_percent_str = Self::format_percent(&self.start_raw);
            self.end_percent_str = Self::format_percent(&self.end_raw);
        }
    }

    fn update_range_display(&mut self) {
        let total_keys = if self.start_key <= self.end_key {
            self.end_key - self.start_key + U256::from(1u64)
        } else {
            U256::zero()
        };
        self.range_display = total_keys.to_string();
    }

    fn apply_threads(&mut self) {
        self.config.threads = self.threads_input;
    }

    fn apply_carousel_settings(&mut self) {
        self.config.carousel_enabled = self.carousel_enabled;
        self.config.carousel_keys_limit = self.carousel_keys_limit_input * 1_000_000;
        self.config.carousel_step_percent = self.carousel_step_raw.clone();
    }

    fn start_search_sync(&mut self) {
        if self.running {
            return;
        }

        let target_hashes = if let Some(ref hashes) = self.loaded_hashes {
            hashes.clone()
        } else {
            let _ = self.gui_tx.send(GuiMessage::Error("Выберите файл с хешами".to_string()));
            return;
        };

        self.apply_carousel_settings();
        self.config.generation_mode = self.generation_mode.clone();
        self.config.sequential_state_file = self.sequential_state_file.clone();

        let session_id = self.current_session_id + 1;
        self.current_session_id = session_id;

        let start = Local::now();
        let mode_name = match self.generation_mode.as_str() {
            "sector" => "Секторный".to_string(),
            "random" => "Случайный".to_string(),
            "random_sectors" => "Случайный долями".to_string(),
            "sequential" => "Последовательный".to_string(),
            _ => "Unknown".to_string(),
        };
        let session = SessionInfo {
            session_id,
            start_time: start.to_rfc3339(),
            end_time: None,
            duration_secs: None,
            mode: mode_name.clone(),
            generator_name: mode_name,
            range_percent: (self.start_percent_str.clone(), self.end_percent_str.clone()),
            total_attempts: 0,
            total_found: 0,
            avg_speed: 0.0,
            hash_file: self.config.hash_file.clone().unwrap_or_else(|| self.config.hash_bin.clone().unwrap_or_default()),
            output_file: self.config.output_file.clone().unwrap_or_default(),
            carousel_enabled: self.config.carousel_enabled,
            enable_workers: false,
        };

        self.sessions.push(session);
        self.save_sessions_to_file();

        let gui_tx = self.gui_tx.clone();
        let (stop_tx, stop_rx) = crossbeam_channel::bounded(1);
        self.stop_tx = Some(stop_tx);
        let mut config_for_thread = self.config.clone();
        config_for_thread.range_percent = (self.start_raw.clone(), self.end_raw.clone());

        let handle = std::thread::spawn(move || {
            let mut engine = match SearchEngine::new(session_id, config_for_thread, gui_tx, stop_rx, target_hashes) {
                Ok(e) => e,
                Err(e) => {
                    eprintln!("Ошибка создания движка: {}", e);
                    return;
                }
            };
            if let Err(e) = engine.run() {
                eprintln!("Ошибка выполнения: {}", e);
            }
        });

        if let Some(old_handle) = self.search_handle.take() {
            std::mem::drop(old_handle);
        }
        self.search_handle = Some(handle);
        self.running = true;
        self.current_session_start = Some(start);
        self.stats = None;
        self.min_max = None;
        self.last_carousel_attempts = 0;
        self.last_carousel_start = Some(Instant::now());
        self.sector_stats.clear();
        for i in 0..self.config.threads {
            self.sector_stats.push(WorkerStatsGui::default());
            self.sector_stats[i].thread_id = i;
        }
        self.save_config();
    }

    fn stop_search_and_wait(&mut self) {
        if !self.running && self.search_handle.is_none() {
            return;
        }
        if let Some(stop_tx) = self.stop_tx.take() {
            let _ = stop_tx.send(());
        }
        if let Some(handle) = self.search_handle.take() {
            let _ = handle.join();
        }
        self.running = false;
        self.save_config();
    }

    fn handle_carousel_trigger(&mut self, session_id: u64) {
        if session_id != self.current_session_id {
            return;
        }
        if !self.config.carousel_enabled {
            return;
        }

        eprintln!("[КАРУСЕЛЬ] Получен сигнал для сессии {}", session_id);

        let old_start_raw = self.start_raw.clone();
        let old_end_raw = self.end_raw.clone();
        let old_range_str = format!("{}%–{}%", Self::format_percent(&old_start_raw), Self::format_percent(&old_end_raw));

        if let Some(start) = self.current_session_start.take() {
            let end = Local::now();
            let duration = end - start;
            let duration_secs = duration.num_seconds().max(0) as u64;
            if let Some(last) = self.sessions.last_mut() {
                if last.session_id == session_id {
                    last.end_time = Some(end.to_rfc3339());
                    last.duration_secs = Some(duration_secs);
                    last.total_attempts = self.stats.map(|(a, _, _)| a).unwrap_or(0);
                    last.total_found = self.stats.map(|(_, f, _)| f).unwrap_or(0);
                    last.avg_speed = self.stats.map(|(_, _, s)| s).unwrap_or(0.0);
                }
            }
            self.save_sessions_to_file();
        }

        self.stop_search_and_wait();

        let step_raw = &self.carousel_step_raw;
        if step_raw == &BigUint::zero() {
            let _ = self.gui_tx.send(GuiMessage::Error("Шаг карусели слишком мал".to_string()));
            return;
        }

        let new_start_raw = &self.start_raw + step_raw;
        let new_end_raw = &self.end_raw + step_raw;

        if new_end_raw <= max_percent_raw() {
            self.start_raw = new_start_raw;
            self.end_raw = new_end_raw;
            self.start_percent_str = Self::format_percent(&self.start_raw);
            self.end_percent_str = Self::format_percent(&self.end_raw);
            self.config.range_percent = (self.start_raw.clone(), self.end_raw.clone());
            self.update_range_display();
            self.sync_hex_from_percent_start();
            self.sync_hex_from_percent_end();

            let new_range_str = format!("{}%–{}%", Self::format_percent(&self.start_raw), Self::format_percent(&self.end_raw));
            let (old_start_hex, old_end_hex) = (self.old_start_hex(), self.old_end_hex());
            let (new_start_hex, new_end_hex) = (self.start_hex_str.clone(), self.end_hex_str.clone());

            let now = Local::now();
            let timestamp = now.format("%Y-%m-%d %H:%M:%S").to_string();

            let round_attempts = self.stats.map(|(a, _, _)| a).unwrap_or(0) - self.last_carousel_attempts;
            let round_duration = self.last_carousel_start.map_or("?".to_string(), |start| {
                let dur = start.elapsed();
                format!("{}.{:03}s", dur.as_secs(), dur.subsec_millis())
            });
            self.last_carousel_attempts = self.stats.map(|(a, _, _)| a).unwrap_or(0);
            self.last_carousel_start = Some(Instant::now());

            let log_msg = format!(
                "[{}] 🔄 КАРУСЕЛЬ: {} → {}\n   Старый диапазон: {} – {}\n   Новый диапазон: {} – {}\n   Hex старого: {} – {}\n   Hex нового: {} – {}\n   Время раунда: {}\n   Проверено ключей за раунд: {}",
                timestamp, old_range_str, new_range_str,
                Self::format_percent(&old_start_raw), Self::format_percent(&old_end_raw),
                Self::format_percent(&self.start_raw), Self::format_percent(&self.end_raw),
                old_start_hex, old_end_hex, new_start_hex, new_end_hex,
                round_duration, round_attempts
            );
            self.carousel_log.push(log_msg.clone());
            if self.carousel_log.len() > 1000 {
                self.carousel_log.remove(0);
            }
            self.status_message = format!("🔄 Карусель: {} – {}", new_start_hex, new_end_hex);
            eprintln!("{}", log_msg);
        } else {
            self.config.carousel_enabled = false;
            self.carousel_enabled = false;
            let now = Local::now();
            let timestamp = now.format("%Y-%m-%d %H:%M:%S").to_string();
            let log_msg = format!("[{}] ⏹️ Карусель завершена (достигнут 100%)", timestamp);
            self.carousel_log.push(log_msg.clone());
            self.status_message = "Карусель завершена".to_string();
            eprintln!("{}", log_msg);
            let _ = self.gui_tx.send(GuiMessage::Error("Карусель завершена".to_string()));
            return;
        }

        self.start_search_sync();
    }

    fn old_start_hex(&self) -> String {
        let total_keys = max_key() - min_key() + U256::from(1u64);
        let total_minus_1 = total_keys - U256::from(1u64);
        let old_start_offset = compute_offset(total_minus_1, &self.start_raw);
        let old_start_key = min_key() + old_start_offset;
        Self::key_to_hex(&old_start_key)
    }

    fn old_end_hex(&self) -> String {
        let total_keys = max_key() - min_key() + U256::from(1u64);
        let total_minus_1 = total_keys - U256::from(1u64);
        let old_end_offset = compute_offset(total_minus_1, &self.end_raw);
        let old_end_key = min_key() + old_end_offset;
        Self::key_to_hex(&old_end_key)
    }

    fn clear_sessions(&mut self) {
        self.sessions.clear();
        self.carousel_log.clear();
        self.found_keys.clear();
        self.save_sessions_to_file();
        self.status_message = "Журнал очищен".to_string();
    }

    fn finalize_session(&mut self, session_id: u64) {
        if let Some(start) = self.current_session_start.take() {
            if self.current_session_id == session_id {
                let end = Local::now();
                let duration = end - start;
                let duration_secs = duration.num_seconds().max(0) as u64;
                if let Some(last) = self.sessions.last_mut() {
                    if last.session_id == session_id {
                        last.end_time = Some(end.to_rfc3339());
                        last.duration_secs = Some(duration_secs);
                        last.total_attempts = self.stats.map(|(a, _, _)| a).unwrap_or(0);
                        last.total_found = self.stats.map(|(_, f, _)| f).unwrap_or(0);
                        last.avg_speed = self.stats.map(|(_, _, s)| s).unwrap_or(0.0);
                    }
                }
                self.save_sessions_to_file();
            }
        }
    }

    fn save_sessions_to_file(&self) {
        let sessions = self.sessions.clone();
        std::thread::spawn(move || {
            if let Ok(file) = File::create("sessions.json") {
                let _ = serde_json::to_writer_pretty(file, &sessions);
            }
        });
    }

    fn load_sessions_from_file(&mut self) {
        match File::open("sessions.json") {
            Ok(file) => {
                match serde_json::from_reader(file) {
                    Ok(sessions) => self.sessions = sessions,
                    Err(e) => eprintln!("Не удалось разобрать sessions.json: {}. Начинаем с чистого листа.", e),
                }
            }
            Err(_) => {}
        }
    }

    fn update_memory(&mut self) {
        self.sys.refresh_memory();
        self.memory_usage = self.sys.used_memory() as f64 / (1024.0 * 1024.0);
    }

    fn handle_messages(&mut self) {
        while let Ok(msg) = self.gui_rx.try_recv() {
            match msg {
                GuiMessage::Stats { session_id, total_attempts, total_found, speed } => {
                    if session_id == self.current_session_id {
                        self.stats = Some((total_attempts, total_found, speed));
                        self.current_speed = speed;
                    }
                }
                GuiMessage::MinMax { session_id, min_hex, max_hex } => {
                    if session_id == self.current_session_id {
                        self.min_max = Some((min_hex, max_hex));
                    }
                }
                GuiMessage::MatchFound { session_id, private_key, address: _, addr_type: _, hash160, all_addresses } => {
                    if session_id == self.current_session_id {
                        let entry = FoundKeyEntry {
                            private_key: private_key.clone(),
                            ripemd160: hash160.clone(),
                            legacy_uncompressed: all_addresses.2.clone(),
                            legacy_compressed: all_addresses.3.clone(),
                            bech32: all_addresses.6.clone(),
                        };
                        self.found_keys.push(entry);
                        if self.found_keys.len() > 1000 {
                            self.found_keys.remove(0);
                        }
                        Self::play_sound();
                    }
                }
                GuiMessage::LastKey { session_id, thread_id, key_hex } => {
                    if session_id == self.current_session_id && self.sector_stats_enabled {
                        if thread_id < self.sector_stats.len() {
                            self.sector_stats[thread_id].last_key = key_hex;
                            self.sector_stats[thread_id].last_update = Instant::now();
                        }
                    }
                }
                GuiMessage::Finished { session_id } => {
                    if session_id == self.current_session_id {
                        self.running = false;
                        self.finalize_session(session_id);
                    }
                }
                GuiMessage::CarouselTrigger { session_id } => {
                    self.handle_carousel_trigger(session_id);
                }
                GuiMessage::SectorStats { session_id, thread_id, last_key, min_hex, max_hex } => {
                    if session_id == self.current_session_id && self.sector_stats_enabled {
                        if thread_id < self.sector_stats.len() {
                            self.sector_stats[thread_id].last_key = last_key;
                            self.sector_stats[thread_id].min_2s = min_hex;
                            self.sector_stats[thread_id].max_2s = max_hex;
                            self.sector_stats[thread_id].last_update = Instant::now();
                        } else {
                            while self.sector_stats.len() <= thread_id {
                                self.sector_stats.push(WorkerStatsGui::default());
                            }
                            self.sector_stats[thread_id].thread_id = thread_id;
                            self.sector_stats[thread_id].last_key = last_key;
                            self.sector_stats[thread_id].min_2s = min_hex;
                            self.sector_stats[thread_id].max_2s = max_hex;
                            self.sector_stats[thread_id].last_update = Instant::now();
                        }
                    }
                }
                GuiMessage::Error(err) => {
                    self.show_error = Some(err);
                    self.error_timer = Some(Instant::now());
                }
                GuiMessage::HashLoadProgress { loaded, total } => {
                    let total_str = total.map(|t| t.to_string()).unwrap_or_else(|| "?".to_string());
                    self.loading_progress = Some(format!("Загружено {} из {} хэшей", loaded, total_str));
                }
                GuiMessage::HashLoadFinished { hashes, count, file_path, file_type } => {
                    self.loaded_hashes = Some(hashes);
                    self.loaded_hashes_count = count;
                    self.loading_progress = None;
                    if file_type == "txt" {
                        self.config.hash_file = Some(file_path);
                        self.config.hash_bin = None;
                    } else {
                        self.config.hash_bin = Some(file_path);
                        self.config.hash_file = None;
                    }
                    self.save_config();
                }
            }
        }
        for stat in &mut self.sector_stats {
            if stat.last_update.elapsed() > Duration::from_secs(3) {
                stat.min_2s = "-".to_string();
                stat.max_2s = "-".to_string();
            }
        }
        if let Some(timer) = self.error_timer {
            if timer.elapsed() > Duration::from_secs(5) {
                self.show_error = None;
                self.error_timer = None;
            }
        }
    }

    fn load_hash_file_async(&mut self, file_type: &str, path: String) {
        self.loading_progress = Some("Начинаем загрузку...".to_string());
        let gui_tx = self.gui_tx.clone();
        let file_type = file_type.to_string();

        std::thread::spawn(move || {
            let result = if file_type == "txt" {
                Self::load_hashes_text_async(&path, gui_tx.clone())
            } else {
                Self::load_hashes_bin_async(&path, gui_tx.clone())
            };
            match result {
                Ok((hashes, count)) => {
                    let _ = gui_tx.send(GuiMessage::HashLoadFinished {
                        hashes: Arc::new(hashes),
                        count,
                        file_path: path,
                        file_type,
                    });
                }
                Err(e) => {
                    let _ = gui_tx.send(GuiMessage::Error(format!("Неверная длина хеша: {}", e)));
                }
            }
        });
    }

    fn load_hashes_text_async(path: &str, gui_tx: crossbeam_channel::Sender<GuiMessage>) -> Result<(HashSet<[u8; 20]>, usize)> {
        let file = File::open(path)?;
        let reader = BufReader::new(file);
        let mut set = HashSet::new();
        let mut loaded = 0;
        let batch_size = 100_000;
        let mut batch_counter = 0;
        for line in reader.lines() {
            let line = line?.trim().to_string();
            if line.is_empty() {
                continue;
            }
            if line.len() != 40 {
                bail!("Invalid hash length: {} in file {}", line, path);
            }
            let bytes = hex::decode(&line)?;
            let mut arr = [0u8; 20];
            arr.copy_from_slice(&bytes);
            set.insert(arr);
            loaded += 1;
            batch_counter += 1;
            if batch_counter >= batch_size {
                let _ = gui_tx.send(GuiMessage::HashLoadProgress { loaded, total: None });
                batch_counter = 0;
            }
        }
        Ok((set, loaded))
    }

    fn load_hashes_bin_async(path: &str, gui_tx: crossbeam_channel::Sender<GuiMessage>) -> Result<(HashSet<[u8; 20]>, usize)> {
        let mut file = File::open(path)?;
        let metadata = file.metadata()?;
        let file_size = metadata.len();
        if file_size % 20 != 0 {
            bail!("Binary file size {} is not a multiple of 20 bytes", path);
        }
        let num_hashes = (file_size / 20) as usize;
        let mut set = HashSet::with_capacity(num_hashes);
        let mut buffer = vec![0u8; file_size as usize];
        file.read_exact(&mut buffer)?;
        let mut loaded = 0;
        let batch_size = 100_000;
        for chunk in buffer.chunks_exact(20) {
            let mut arr = [0u8; 20];
            arr.copy_from_slice(chunk);
            set.insert(arr);
            loaded += 1;
            if loaded % batch_size == 0 {
                let _ = gui_tx.send(GuiMessage::HashLoadProgress { loaded, total: Some(num_hashes) });
            }
        }
        Ok((set, loaded))
    }

    fn load_hash_file(&mut self, file_type: &str) {
        let path = if file_type == "txt" {
            FileDialog::new().add_filter("txt", &["txt"]).pick_file()
        } else {
            FileDialog::new().add_filter("bin", &["bin"]).pick_file()
        };
        if let Some(path) = path {
            let path_str = path.to_string_lossy().to_string();
            self.load_hash_file_async(file_type, path_str);
        }
    }

    fn get_range_hex(&self) -> (String, String) {
        (self.start_hex_str.clone(), self.end_hex_str.clone())
    }

    fn get_total_keys_in_range(&self) -> U256 {
        if self.start_key <= self.end_key {
            self.end_key - self.start_key + U256::from(1u64)
        } else {
            U256::zero()
        }
    }

    fn auto_update_end_from_start(&mut self) {
        if self.end_manually_edited {
            return;
        }
        let step_raw = &self.carousel_step_raw;
        let new_end_raw = &self.start_raw + step_raw;
        if new_end_raw <= max_percent_raw() {
            self.end_raw = new_end_raw;
            self.end_percent_str = Self::format_percent(&self.end_raw);
            self.apply_range_percent();
        }
    }

    fn increase_start(&mut self) {
        let step_raw = BigUint::from(1u32);
        let new_start = &self.start_raw + &step_raw;
        if new_start <= max_percent_raw() {
            self.start_raw = new_start;
            self.start_percent_str = Self::format_percent(&self.start_raw);
            self.auto_update_end_from_start();
            self.sync_hex_from_percent_start();
            self.save_config();
        }
    }

    fn decrease_start(&mut self) {
        let step_raw = BigUint::from(1u32);
        if self.start_raw >= step_raw {
            self.start_raw -= &step_raw;
        } else {
            self.start_raw = BigUint::zero();
        }
        self.start_percent_str = Self::format_percent(&self.start_raw);
        self.auto_update_end_from_start();
        self.sync_hex_from_percent_start();
        self.save_config();
    }

    fn increase_end(&mut self) {
        let step_raw = BigUint::from(1u32);
        let new_end = &self.end_raw + &step_raw;
        if new_end <= max_percent_raw() {
            self.end_raw = new_end;
            self.end_percent_str = Self::format_percent(&self.end_raw);
            self.apply_range_percent();
            self.end_manually_edited = true;
            self.sync_hex_from_percent_end();
            self.save_config();
        }
    }

    fn decrease_end(&mut self) {
        let step_raw = BigUint::from(1u32);
        if self.end_raw >= step_raw {
            self.end_raw -= &step_raw;
        } else {
            self.end_raw = BigUint::zero();
        }
        self.end_percent_str = Self::format_percent(&self.end_raw);
        self.apply_range_percent();
        self.end_manually_edited = true;
        self.sync_hex_from_percent_end();
        self.save_config();
    }

    fn sync_start_from_str(&mut self) {
        if let Ok(val) = parse_percent_raw(&self.start_percent_str) {
            if val <= max_percent_raw() {
                self.start_raw = val;
                self.start_percent_str = Self::format_percent(&self.start_raw);
                self.auto_update_end_from_start();
                self.sync_hex_from_percent_start();
                self.save_config();
            } else {
                self.start_percent_str = Self::format_percent(&self.start_raw);
            }
        } else {
            self.start_percent_str = Self::format_percent(&self.start_raw);
        }
    }

    fn sync_end_from_str(&mut self) {
        if let Ok(val) = parse_percent_raw(&self.end_percent_str) {
            if val <= max_percent_raw() {
                self.end_raw = val;
                self.end_percent_str = Self::format_percent(&self.end_raw);
                self.apply_range_percent();
                self.end_manually_edited = true;
                self.sync_hex_from_percent_end();
                self.save_config();
            } else {
                self.end_percent_str = Self::format_percent(&self.end_raw);
            }
        } else {
            self.end_percent_str = Self::format_percent(&self.end_raw);
        }
    }

    fn sync_step_from_str(&mut self) {
        if let Ok(val) = parse_percent_raw(&self.carousel_step_input) {
            self.carousel_step_raw = val;
            self.sync_step_from_percent();
            self.save_config();
        } else {
            self.carousel_step_input = Self::format_percent(&self.carousel_step_raw);
        }
    }

    fn open_state_file(&self) {
        if let Some(ref path) = self.sequential_state_file {
            let _ = open::that(path);
        }
    }

    fn load_state_file(&mut self) {
        if let Some(path) = FileDialog::new().add_filter("json", &["json"]).pick_file() {
            self.sequential_state_file = Some(path.to_string_lossy().to_string());
            self.save_config();
        }
    }

    fn open_state_dir(&self) {
        if let Some(ref path) = self.sequential_state_file {
            if let Some(parent) = std::path::Path::new(path).parent() {
                let _ = open::that(parent);
            }
        }
    }
}

fn format_with_separator_u64(num: u64) -> String {
    let s = num.to_string();
    let mut result = String::new();
    let len = s.len();
    for (i, ch) in s.chars().enumerate() {
        if i > 0 && (len - i) % 3 == 0 {
            result.push(' ');
        }
        result.push(ch);
    }
    result
}

fn format_duration(secs: u64) -> String {
    let days = secs / 86400;
    let hours = (secs % 86400) / 3600;
    let minutes = (secs % 3600) / 60;
    let seconds = secs % 60;
    if days > 0 {
        format!("{}д {}ч {}м {}с", days, hours, minutes, seconds)
    } else if hours > 0 {
        format!("{}ч {}м {}с", hours, minutes, seconds)
    } else {
        format!("{}м {}с", minutes, seconds)
    }
}

impl eframe::App for App {
    fn update(&mut self, ctx: &egui::Context, _frame: &mut Frame) {
        self.handle_messages();
        self.update_memory();

        ctx.set_visuals(egui::Visuals::light());

        TopBottomPanel::top("control_panel").show(ctx, |ui| {
            ui.horizontal(|ui| {
                ui.heading(RichText::new("Bitcoin365 Carousel Searcher").size(18.0));
                ui.with_layout(egui::Layout::right_to_left(egui::Align::Center), |ui| {
                    let start_btn = egui::Button::new(RichText::new("Старт").size(18.0))
                        .min_size(egui::vec2(120.0, 30.0))
                        .fill(if !self.running { Color32::from_rgb(0, 200, 0) } else { Color32::GRAY });
                    if ui.add(start_btn).clicked() && !self.running {
                        self.start_search_sync();
                    }
                    let stop_btn = egui::Button::new(RichText::new("Стоп").size(18.0))
                        .min_size(egui::vec2(120.0, 30.0))
                        .fill(if self.running { Color32::from_rgb(200, 0, 0) } else { Color32::GRAY });
                    if ui.add(stop_btn).clicked() && self.running {
                        self.stop_search_and_wait();
                    }
                });
            });
        });

        TopBottomPanel::top("tab_panel").show(ctx, |ui| {
            ui.add_space(8.0);
            ui.horizontal(|ui| {
                ui.selectable_value(&mut self.selected_tab, 0, RichText::new("Настройки").size(18.0));
                ui.selectable_value(&mut self.selected_tab, 1, RichText::new("Карусель").size(18.0));
                ui.selectable_value(&mut self.selected_tab, 2, RichText::new("Найденные ключи").size(18.0));
                ui.selectable_value(&mut self.selected_tab, 3, RichText::new("Журнал сессий").size(18.0));
                ui.selectable_value(&mut self.selected_tab, 4, RichText::new("Воркеры").size(18.0));
            });
            ui.add_space(8.0);
            ui.separator();
        });

        match self.selected_tab {
            0 => {
                CentralPanel::default().show(ctx, |ui| {
                    egui::ScrollArea::vertical().show(ui, |ui| {
                        ui.add_space(12.0);
                        ui.label(RichText::new("Файл хэшей:").size(18.0));
                        ui.horizontal(|ui| {
                            let btn = egui::Button::new(RichText::new("📄 Текстовый").size(12.0)).min_size(egui::vec2(120.0, 20.0));
                            if ui.add(btn).clicked() { self.load_hash_file("txt"); }
                            let btn = egui::Button::new(RichText::new("🔢 Бинарный").size(12.0)).min_size(egui::vec2(120.0, 20.0));
                            if ui.add(btn).clicked() { self.load_hash_file("bin"); }
                            if let Some(progress) = &self.loading_progress {
                                ui.label(RichText::new(progress).size(12.0).color(Color32::BLUE));
                            } else {
                                let loaded_str = format!("Загружено: {} хэшей", format_with_separator_u64(self.loaded_hashes_count as u64));
                                ui.label(RichText::new(loaded_str).size(12.0));
                            }
                        });
                        if let Some(ref path) = self.config.hash_file {
                            ui.label(RichText::new(format!("Файл хэшей (текст): {}", path)).size(12.0));
                        } else if let Some(ref path) = self.config.hash_bin {
                            ui.label(RichText::new(format!("Файл хэшей (бинарный): {}", path)).size(12.0));
                        } else {
                            ui.label(RichText::new("Файл не выбран").size(12.0));
                        }

                        ui.add_space(12.0);
                        ui.separator();
                        ui.add_space(12.0);

                        ui.label(RichText::new("Диапазон сканирования в %:").size(18.0));

                        ui.label(RichText::new("Start (%)").size(12.0));
                        ui.horizontal(|ui| {
                            let start_edit = TextEdit::singleline(&mut self.start_percent_str)
                                .desired_width(600.0)
                                .font(egui::FontId::new(MONOSPACE_FONT_SIZE, FontFamily::Monospace));
                            if ui.add(start_edit).changed() {
                                self.sync_start_from_str();
                            }
                            if ui.button("🔼").clicked() { self.increase_start(); }
                            if ui.button("🔽").clicked() { self.decrease_start(); }
                            if ui.button("OK").clicked() { self.apply_range_percent(); }
                        });

                        ui.label(RichText::new("End (%)").size(12.0));
                        ui.horizontal(|ui| {
                            let end_edit = TextEdit::singleline(&mut self.end_percent_str)
                                .desired_width(600.0)
                                .font(egui::FontId::new(MONOSPACE_FONT_SIZE, FontFamily::Monospace));
                            if ui.add(end_edit).changed() {
                                self.sync_end_from_str();
                            }
                            if ui.button("🔼").clicked() { self.increase_end(); }
                            if ui.button("🔽").clicked() { self.decrease_end(); }
                            if ui.button("OK").clicked() { self.apply_range_percent(); }
                        });

                        ui.label(RichText::new("Start HEX (64 символа)").size(12.0));
                        ui.horizontal(|ui| {
                            let mut hex_start = self.start_hex_str.clone();
                            let resp = ui.add(TextEdit::singleline(&mut hex_start)
                                .desired_width(600.0)
                                .font(egui::FontId::new(MONOSPACE_FONT_SIZE, FontFamily::Monospace)));
                            if resp.changed() {
                                if hex_start.len() > 64 {
                                    hex_start = hex_start[..64].to_string();
                                }
                                self.start_hex_str = hex_start;
                            }
                            if resp.lost_focus() {
                                self.apply_hex_start();
                            }
                            if ui.button("Ок").clicked() {
                                self.apply_hex_start();
                            }
                            if ui.button("Копировать").clicked() {
                                self.copy_hex_start();
                            }
                            if ui.button("Вставить").clicked() {
                                self.paste_hex_start();
                            }
                        });
                        ui.label(RichText::new(format!("{}/64 символов", self.start_hex_str.len())).size(10.0).color(Color32::DARK_GRAY));

                        ui.label(RichText::new("End HEX (64 символа)").size(12.0));
                        ui.horizontal(|ui| {
                            let mut hex_end = self.end_hex_str.clone();
                            let resp = ui.add(TextEdit::singleline(&mut hex_end)
                                .desired_width(600.0)
                                .font(egui::FontId::new(MONOSPACE_FONT_SIZE, FontFamily::Monospace)));
                            if resp.changed() {
                                if hex_end.len() > 64 {
                                    hex_end = hex_end[..64].to_string();
                                }
                                self.end_hex_str = hex_end;
                            }
                            if resp.lost_focus() {
                                self.apply_hex_end();
                            }
                            if ui.button("Ок").clicked() {
                                self.apply_hex_end();
                            }
                            if ui.button("Копировать").clicked() {
                                self.copy_hex_end();
                            }
                            if ui.button("Вставить").clicked() {
                                self.paste_hex_end();
                            }
                        });
                        ui.label(RichText::new(format!("{}/64 символов", self.end_hex_str.len())).size(10.0).color(Color32::DARK_GRAY));

                        let (start_hex, end_hex) = self.get_range_hex();
                        ui.label(RichText::new(format!("Start: {}", start_hex)).size(12.0));
                        ui.label(RichText::new(format!("Finish: {}", end_hex)).size(12.0));

                        let total_keys = self.get_total_keys_in_range();
                        let total_keys_str = total_keys.to_string();
                        let total_keys_digits = total_keys_str.len();
                        ui.label(RichText::new(format!("Ключей в диапазоне: {}", total_keys_str)).size(12.0));
                        ui.label(RichText::new(format!("Количество знаков: {}", total_keys_digits)).size(10.0).color(Color32::DARK_GRAY));

                        ui.add_space(12.0);
                        ui.separator();
                        ui.add_space(12.0);

                        ui.horizontal(|ui| {
                            let threads_label = format!("Потоки: доступно [{}]", num_cpus::get());
                            ui.label(RichText::new(threads_label).size(18.0));
                            let minus_btn = egui::Button::new("-").min_size(egui::vec2(24.0, 24.0));
                            if ui.add(minus_btn).clicked() && self.threads_input > 1 {
                                self.threads_input -= 1;
                                self.save_config();
                            }
                            ui.label(RichText::new(self.threads_input.to_string()).size(12.0));
                            let plus_btn = egui::Button::new("+").min_size(egui::vec2(24.0, 24.0));
                            if ui.add(plus_btn).clicked() && self.threads_input < 512 {
                                self.threads_input += 1;
                                self.save_config();
                            }
                            let ok_btn = egui::Button::new(RichText::new("OK").size(12.0)).min_size(egui::vec2(40.0, 24.0));
                            if ui.add(ok_btn).clicked() {
                                self.apply_threads();
                                self.save_config();
                            }
                            ui.add_space(20.0);
                            ui.label(RichText::new("Файл результатов:").size(18.0));
                            let mut output = self.config.output_file.clone().unwrap_or_default();
                            let text_edit = TextEdit::singleline(&mut output)
                                .desired_width(300.0)
                                .font(egui::FontId::new(MONOSPACE_FONT_SIZE, FontFamily::Monospace));
                            if ui.add(text_edit).changed() {
                                if !output.is_empty() {
                                    self.config.output_file = Some(output);
                                } else {
                                    self.config.output_file = None;
                                }
                                self.save_config();
                            }
                            let btn = egui::Button::new(RichText::new("Выбрать...").size(12.0)).min_size(egui::vec2(80.0, 24.0));
                            if ui.add(btn).clicked() {
                                if let Some(path) = FileDialog::new().save_file() {
                                    self.config.output_file = Some(path.to_string_lossy().to_string());
                                    self.save_config();
                                }
                            }
                            if self.config.output_file.is_some() {
                                let dir_btn = egui::Button::new(RichText::new("📂 Открыть директорию").size(12.0)).min_size(egui::vec2(120.0, 24.0));
                                if ui.add(dir_btn).clicked() { self.open_directory(); }
                                let file_btn = egui::Button::new(RichText::new("📄 Открыть файл").size(12.0)).min_size(egui::vec2(100.0, 24.0));
                                if ui.add(file_btn).clicked() { self.open_file(); }
                            }
                        });

                        ui.add_space(12.0);
                        ui.separator();
                        ui.add_space(12.0);

                        ui.label(RichText::new("Режим генерации ключей:").size(18.0));
                        ui.horizontal(|ui| {
                            if ui.selectable_label(self.generation_mode == "sector", "Секторный (охват краёв)").clicked() {
                                self.generation_mode = "sector".to_string();
                                self.save_config();
                            }
                            if ui.selectable_label(self.generation_mode == "random", "Случайный").clicked() {
                                self.generation_mode = "random".to_string();
                                self.save_config();
                            }
                            if ui.selectable_label(self.generation_mode == "random_sectors", "Случайный долями").clicked() {
                                self.generation_mode = "random_sectors".to_string();
                                self.save_config();
                            }
                            if ui.selectable_label(self.generation_mode == "sequential", "Последовательный").clicked() {
                                self.generation_mode = "sequential".to_string();
                                self.save_config();
                            }
                        });
                        if self.generation_mode == "sector" {
                            ui.colored_label(egui::Color32::GRAY, "→ Воркер 0: вперёд, последний воркер: назад, остальные случайно");
                        }
                        if self.generation_mode == "random_sectors" {
                            ui.colored_label(egui::Color32::GRAY, "→ Диапазон делится на равные части, каждый воркер случайно перебирает свою часть");
                        }
                        if self.generation_mode == "sequential" {
                            ui.horizontal(|ui| {
                                ui.label(RichText::new("Файл состояния:").size(12.0));
                                let mut state_file = self.sequential_state_file.clone().unwrap_or_default();
                                if ui.add(TextEdit::singleline(&mut state_file).desired_width(300.0)).changed() {
                                    if state_file.is_empty() {
                                        self.sequential_state_file = None;
                                    } else {
                                        self.sequential_state_file = Some(state_file);
                                    }
                                    self.save_config();
                                }
                                if ui.button("Продолжить").clicked() && self.sequential_state_file.is_some() {}
                                if ui.button("Открыть файл").clicked() { self.open_state_file(); }
                                if ui.button("Загрузить файл").clicked() { self.load_state_file(); }
                                if ui.button("Открыть путь").clicked() { self.open_state_dir(); }
                            });
                        }

                        ui.add_space(12.0);
                        ui.separator();
                        ui.add_space(12.0);

                        ui.checkbox(&mut self.carousel_enabled, RichText::new("Карусель (по количеству ключей)").size(12.0));
                        if self.carousel_enabled {
                            ui.label(RichText::new("Лимит (млн ключей):").size(12.0));
                            let mut limit = self.carousel_keys_limit_input;
                            let limit_str = limit.to_string();
                            let mut limit_str_edit = limit_str;
                            if ui.add(TextEdit::singleline(&mut limit_str_edit).desired_width(100.0)).changed() {
                                if let Ok(val) = limit_str_edit.parse::<u64>() {
                                    limit = val;
                                    self.carousel_keys_limit_input = limit;
                                    self.save_config();
                                }
                            }
                            ui.label(RichText::new("Шаг (%):").size(12.0));
                            ui.horizontal(|ui| {
                                let mut step_str = self.carousel_step_input.clone();
                                if ui.add(TextEdit::singleline(&mut step_str).desired_width(600.0).font(egui::FontId::new(MONOSPACE_FONT_SIZE, FontFamily::Monospace))).changed() {
                                    self.carousel_step_input = step_str;
                                    self.sync_step_from_str();
                                }
                            });
                            ui.label(RichText::new("Шаг (HEX64):").size(12.0));
                            ui.horizontal(|ui| {
                                let mut step_hex_str = self.carousel_step_hex_str.clone();
                                if ui.add(TextEdit::singleline(&mut step_hex_str).desired_width(600.0).font(egui::FontId::new(MONOSPACE_FONT_SIZE, FontFamily::Monospace))).changed() {
                                    if step_hex_str.len() > 64 {
                                        step_hex_str = step_hex_str[..64].to_string();
                                    }
                                    self.carousel_step_hex_str = step_hex_str;
                                }
                                if ui.button("Ок").clicked() { self.apply_hex_step(); }
                                if ui.button("Копировать").clicked() { self.copy_hex_step(); }
                                if ui.button("Вставить").clicked() { self.paste_hex_step(); }
                            });
                            ui.label(RichText::new(format!("Количество символов: {}", self.carousel_step_hex_str.len())).size(10.0).color(Color32::DARK_GRAY));
                        }

                        ui.add_space(12.0);
                        ui.separator();
                        ui.add_space(12.0);

                        let memory_free = self.memory_total as f64 / (1024.0 * 1024.0) - self.memory_usage;
                        let memory_str = format!("Память: занято {:.1} МБ / свободно {:.1} МБ", self.memory_usage, memory_free);
                        ui.label(RichText::new(memory_str).size(12.0));
                        let memory_frac = self.memory_usage / (self.memory_total as f64 / (1024.0 * 1024.0));
                        ui.add(egui::ProgressBar::new(memory_frac as f32).text(format!("{:.1}%", memory_frac * 100.0)));

                        ui.add_space(12.0);
                        ui.separator();
                        ui.add_space(12.0);

                        ui.add_space(50.0);
                        let reset_btn = egui::Button::new(RichText::new("Сбросить настройки").size(18.0))
                            .min_size(egui::vec2(200.0, 30.0))
                            .fill(egui::Color32::from_rgb(255, 165, 0));
                        if ui.add(reset_btn).clicked() {
                            self.reset_to_defaults();
                        }
                        ui.add_space(20.0);
                    });
                });
            }
            1 => {
                CentralPanel::default().show(ctx, |ui| {
                    ui.heading(RichText::new("Карусель").size(18.0));
                    ui.add_space(8.0);
                    ui.horizontal(|ui| {
                        if ui.button("Сначала новые").clicked() { self.carousel_desc = true; }
                        if ui.button("Сначала старые").clicked() { self.carousel_desc = false; }
                        ui.add_space(20.0);
                        if ui.button("Стереть").clicked() {
                            self.carousel_log.clear();
                            self.status_message = "Карусель очищена".to_string();
                        }
                    });
                    ui.add_space(8.0);
                    ScrollArea::vertical().max_height(f32::INFINITY).show(ui, |ui| {
                        let log_iter: Box<dyn Iterator<Item = &String>> = if self.carousel_desc {
                            Box::new(self.carousel_log.iter().rev())
                        } else {
                            Box::new(self.carousel_log.iter())
                        };
                        for msg in log_iter {
                            ui.label(RichText::new(msg).size(12.0).color(Color32::BLACK));
                            ui.add_space(4.0);
                        }
                        if self.carousel_log.is_empty() {
                            ui.label(RichText::new("Нет событий карусели").size(12.0).color(Color32::BLACK));
                        }
                    });
                });
            }
            2 => {
                CentralPanel::default().show(ctx, |ui| {
                    ui.heading(RichText::new("Найденные ключи").size(18.0));
                    ui.add_space(8.0);
                    ui.horizontal(|ui| {
                        ui.label(RichText::new("Файл результатов:").size(12.0));
                        let output_path = self.config.output_file.clone().unwrap_or_default();
                        ui.label(RichText::new(&output_path).size(12.0).color(Color32::BLUE));
                        let select_btn = egui::Button::new(RichText::new("Выбрать...").size(12.0)).min_size(egui::vec2(80.0, 24.0));
                        if ui.add(select_btn).clicked() {
                            if let Some(path) = FileDialog::new().save_file() {
                                self.config.output_file = Some(path.to_string_lossy().to_string());
                                self.save_config();
                            }
                        }
                        if self.config.output_file.is_some() {
                            let dir_btn = egui::Button::new(RichText::new("📂 Открыть директорию").size(12.0)).min_size(egui::vec2(120.0, 24.0));
                            if ui.add(dir_btn).clicked() { self.open_directory(); }
                            let file_btn = egui::Button::new(RichText::new("📄 Открыть файл").size(12.0)).min_size(egui::vec2(100.0, 24.0));
                            if ui.add(file_btn).clicked() { self.open_file(); }
                        }
                        ui.add_space(10.0);
                        ui.label(RichText::new("Отображение:").size(12.0));
                        let horiz_btn = egui::Button::new(RichText::new("Горизонтально").size(12.0)).min_size(egui::vec2(100.0, 24.0));
                        if ui.add(horiz_btn).clicked() { self.orientation = TableOrientation::Horizontal; }
                        let vert_btn = egui::Button::new(RichText::new("Вертикально").size(12.0)).min_size(egui::vec2(100.0, 24.0));
                        if ui.add(vert_btn).clicked() { self.orientation = TableOrientation::Vertical; }
                    });
                    ui.add_space(8.0);
                    if self.orientation == TableOrientation::Horizontal {
                        ui.horizontal(|ui| {
                            if ui.button("◀").clicked() { self.scroll_offset_x = (self.scroll_offset_x - 100.0).max(0.0); }
                            if ui.button("▶").clicked() { self.scroll_offset_x += 100.0; }
                        });
                        ui.add_space(8.0);
                    }
                    if self.orientation == TableOrientation::Horizontal {
                        ScrollArea::both()
                            .auto_shrink([false; 2])
                            .scroll_offset(egui::Vec2::new(self.scroll_offset_x, 0.0))
                            .show(ui, |ui| {
                                if self.found_keys.is_empty() {
                                    ui.label(RichText::new("Нет найденных ключей").size(12.0).color(Color32::BLACK));
                                } else {
                                    Grid::new("found_keys_grid_horiz").num_columns(5).striped(true).show(ui, |ui| {
                                        ui.label(RichText::new("Приватный ключ").size(12.0).strong());
                                        ui.label(RichText::new("RIPEMD-160").size(12.0).strong());
                                        ui.label(RichText::new("Legacy (uncomp)").size(12.0).strong());
                                        ui.label(RichText::new("Legacy (comp)").size(12.0).strong());
                                        ui.label(RichText::new("Bech32").size(12.0).strong());
                                        ui.end_row();
                                        for (i, entry) in self.found_keys.iter().enumerate() {
                                            let bg = if i % 2 == 0 { Color32::from_rgb(240,240,240) } else { Color32::from_rgb(255,255,200) };
                                            egui::Frame::none().fill(bg).show(ui, |ui| {
                                                let resp = ui.selectable_label(true, &entry.private_key);
                                                if resp.clicked() { self.copy_to_clipboard(&entry.private_key); }
                                                resp.on_hover_text("Кликните, чтобы скопировать");
                                            });
                                            egui::Frame::none().fill(bg).show(ui, |ui| {
                                                let resp = ui.selectable_label(true, &entry.ripemd160);
                                                if resp.clicked() { self.copy_to_clipboard(&entry.ripemd160); }
                                                resp.on_hover_text("Кликните, чтобы скопировать");
                                            });
                                            egui::Frame::none().fill(bg).show(ui, |ui| {
                                                let resp = ui.selectable_label(true, &entry.legacy_uncompressed);
                                                if resp.clicked() { self.copy_to_clipboard(&entry.legacy_uncompressed); }
                                                resp.on_hover_text("Кликните, чтобы скопировать");
                                            });
                                            egui::Frame::none().fill(bg).show(ui, |ui| {
                                                let resp = ui.selectable_label(true, &entry.legacy_compressed);
                                                if resp.clicked() { self.copy_to_clipboard(&entry.legacy_compressed); }
                                                resp.on_hover_text("Кликните, чтобы скопировать");
                                            });
                                            egui::Frame::none().fill(bg).show(ui, |ui| {
                                                let resp = ui.selectable_label(true, &entry.bech32);
                                                if resp.clicked() { self.copy_to_clipboard(&entry.bech32); }
                                                resp.on_hover_text("Кликните, чтобы скопировать");
                                            });
                                            ui.end_row();
                                        }
                                    });
                                }
                            });
                    } else {
                        ScrollArea::vertical().show(ui, |ui| {
                            if self.found_keys.is_empty() {
                                ui.label(RichText::new("Нет найденных ключей").size(12.0).color(Color32::BLACK));
                            } else {
                                for (i, entry) in self.found_keys.iter().enumerate() {
                                    let bg = if i % 2 == 0 { Color32::from_rgb(240,240,240) } else { Color32::from_rgb(255,255,200) };
                                    egui::Frame::none().fill(bg).show(ui, |ui| {
                                        Grid::new(format!("entry_{}", i)).num_columns(2).striped(false).show(ui, |ui| {
                                            ui.label(RichText::new("Приватный ключ").size(12.0).strong());
                                            let resp = ui.selectable_label(true, &entry.private_key);
                                            if resp.clicked() { self.copy_to_clipboard(&entry.private_key); }
                                            resp.on_hover_text("Кликните, чтобы скопировать");
                                            ui.end_row();
                                            ui.label(RichText::new("RIPEMD-160").size(12.0).strong());
                                            let resp = ui.selectable_label(true, &entry.ripemd160);
                                            if resp.clicked() { self.copy_to_clipboard(&entry.ripemd160); }
                                            resp.on_hover_text("Кликните, чтобы скопировать");
                                            ui.end_row();
                                            ui.label(RichText::new("Legacy (uncomp)").size(12.0).strong());
                                            let resp = ui.selectable_label(true, &entry.legacy_uncompressed);
                                            if resp.clicked() { self.copy_to_clipboard(&entry.legacy_uncompressed); }
                                            resp.on_hover_text("Кликните, чтобы скопировать");
                                            ui.end_row();
                                            ui.label(RichText::new("Legacy (comp)").size(12.0).strong());
                                            let resp = ui.selectable_label(true, &entry.legacy_compressed);
                                            if resp.clicked() { self.copy_to_clipboard(&entry.legacy_compressed); }
                                            resp.on_hover_text("Кликните, чтобы скопировать");
                                            ui.end_row();
                                            ui.label(RichText::new("Bech32").size(12.0).strong());
                                            let resp = ui.selectable_label(true, &entry.bech32);
                                            if resp.clicked() { self.copy_to_clipboard(&entry.bech32); }
                                            resp.on_hover_text("Кликните, чтобы скопировать");
                                            ui.end_row();
                                        });
                                    });
                                    ui.add_space(8.0);
                                }
                            }
                        });
                    }
                });
            }
            3 => {
                CentralPanel::default().show(ctx, |ui| {
                    ui.heading(RichText::new("Журнал сессий").size(18.0));
                    ui.add_space(8.0);
                    ui.horizontal(|ui| {
                        ui.label(RichText::new("Сортировка:").size(12.0).color(Color32::BLACK));
                        if ui.button("Сначала новые").clicked() { self.sessions_desc = true; }
                        if ui.button("Сначала старые").clicked() { self.sessions_desc = false; }
                        ui.add_space(20.0);
                        if ui.button("Стереть журнал").clicked() { self.clear_sessions(); }
                    });
                    ui.add_space(8.0);
                    ScrollArea::vertical().max_height(f32::INFINITY).show(ui, |ui| {
                        let sessions_iter: Box<dyn Iterator<Item = &SessionInfo>> = if self.sessions_desc {
                            Box::new(self.sessions.iter().rev())
                        } else {
                            Box::new(self.sessions.iter())
                        };
                        for session in sessions_iter {
                            let start_str = chrono::DateTime::parse_from_rfc3339(&session.start_time)
                                .map(|dt| dt.format("%Y-%m-%d %H:%M:%S").to_string())
                                .unwrap_or(session.start_time.clone());
                            let end_str = if let Some(end) = &session.end_time {
                                chrono::DateTime::parse_from_rfc3339(end)
                                    .map(|dt| dt.format("%Y-%m-%d %H:%M:%S").to_string())
                                    .unwrap_or(end.clone())
                            } else {
                                "не завершена".to_string()
                            };
                            let duration_str = if let Some(secs) = session.duration_secs {
                                format_duration(secs)
                            } else {
                                "—".to_string()
                            };
                            let (range_str, start_hex, end_hex) = {
                                let (s_raw, e_raw) = (parse_percent_raw(&session.range_percent.0).unwrap(), parse_percent_raw(&session.range_percent.1).unwrap());
                                let range_str = format!("{}%-{}%", Self::format_percent(&s_raw), Self::format_percent(&e_raw));
                                let total_keys = max_key() - min_key() + U256::from(1u64);
                                let total_minus_1 = total_keys - U256::from(1u64);
                                let start_offset = compute_offset(total_minus_1, &s_raw);
                                let end_offset = compute_offset(total_minus_1, &e_raw);
                                let start_key = min_key() + start_offset;
                                let end_key = min_key() + end_offset;
                                let s_hex = hex::encode(u256_to_bytes(start_key));
                                let e_hex = hex::encode(u256_to_bytes(end_key));
                                (range_str, s_hex, e_hex)
                            };
                            let carousel_str = if session.carousel_enabled { "Да" } else { "Нет" };
                            let log_msg = format!(
                                "Сессия № {} | {} – {}\n  Длительность: {}\n  Режим: {} ({})\n  Карусель: {}\n  Диапазон: {}\n  Диапазон: {}-{}\n  Проверено: {} ключей, найдено: {}\n  Средняя скорость: {} к/с\n  Файл хешей: {}",
                                session.session_id, start_str, end_str, duration_str,
                                session.mode, session.generator_name, carousel_str,
                                range_str, start_hex, end_hex,
                                format_with_separator_u64(session.total_attempts), session.total_found,
                                session.avg_speed, session.hash_file
                            );
                            ui.label(RichText::new(log_msg).size(12.0).color(Color32::BLACK));
                            ui.add_space(8.0);
                            ui.separator();
                            ui.add_space(8.0);
                        }
                    });
                });
            }
            4 => {
                CentralPanel::default().show(ctx, |ui| {
                    ui.heading(RichText::new("Воркеры").size(18.0));
                    ui.add_space(8.0);
                    ui.horizontal(|ui| {
                        let btn_text = if self.sector_stats_enabled { "Выключить" } else { "Включить" };
                        if ui.button(btn_text).clicked() {
                            self.sector_stats_enabled = !self.sector_stats_enabled;
                            if !self.sector_stats_enabled {
                                self.sector_stats.clear();
                            } else {
                                self.sector_stats.clear();
                                for i in 0..self.config.threads {
                                    self.sector_stats.push(WorkerStatsGui::default());
                                    self.sector_stats[i].thread_id = i;
                                }
                            }
                            self.save_config();
                        }
                    });
                    ui.add_space(8.0);
                    if self.sector_stats.is_empty() {
                        ui.label(RichText::new("Статистика воркеров выключена. Нажмите 'Включить'.").size(12.0).color(Color32::BLACK));
                    } else {
                        Grid::new("workers_grid").num_columns(4).striped(true).show(ui, |ui| {
                            ui.label(RichText::new("Воркер").size(12.0).strong());
                            ui.label(RichText::new("Мин за 2с").size(12.0).strong());
                            ui.label(RichText::new("Последний ключ").size(12.0).strong());
                            ui.label(RichText::new("Макс за 2с").size(12.0).strong());
                            ui.end_row();
                            for stat in &self.sector_stats {
                                ui.label(RichText::new(format!("Worker {}", stat.thread_id)).size(12.0));
                                let resp_min = ui.selectable_label(false, &stat.min_2s);
                                if resp_min.clicked() { self.copy_to_clipboard(&stat.min_2s); }
                                resp_min.on_hover_text("Кликните, чтобы скопировать");
                                let resp_last = ui.selectable_label(false, &stat.last_key);
                                if resp_last.clicked() { self.copy_to_clipboard(&stat.last_key); }
                                resp_last.on_hover_text("Кликните, чтобы скопировать");
                                let resp_max = ui.selectable_label(false, &stat.max_2s);
                                if resp_max.clicked() { self.copy_to_clipboard(&stat.max_2s); }
                                resp_max.on_hover_text("Кликните, чтобы скопировать");
                                ui.end_row();
                            }
                        });
                    }

                    ui.add_space(20.0);
                    ui.separator();
                    ui.add_space(10.0);
                    ui.heading(RichText::new("Общая статистика").size(16.0));
                    ui.add_space(8.0);

                    let total_attempts_all: u64 = self.sessions.iter().map(|s| s.total_attempts).sum();
                    let (attempts_current, found_current, speed_current) = self.stats.unwrap_or((0, 0, 0.0));
                    let speed_per_min = speed_current * 60.0;
                    let (range_min_hex, range_max_hex) = self.get_range_hex();
                    let (min_last_min, max_last_min) = self.min_max.clone().unwrap_or(("-".to_string(), "-".to_string()));
                    let start_time_str = self.current_session_start.map(|t| t.format("%Y-%m-%d %H:%M:%S").to_string()).unwrap_or("not started".to_string());
                    let duration_secs = self.current_session_start.map(|t| (Local::now() - t).num_seconds().max(0) as u64).unwrap_or(0);
                    let duration_str = format_duration(duration_secs);

                    let speed_str = format!("{:.0} к/с :: {:.0} к/мин", speed_current, speed_per_min);
                    let rows = vec![
                        ("Всего проверено ключей за всё время", format_with_separator_u64(total_attempts_all)),
                        ("Всего проверено ключей за текущую сессию", format_with_separator_u64(attempts_current)),
                        ("Скорость проверки в среднем", speed_str),
                        ("Минимальный ключ выставленного диапазона", range_min_hex),
                        ("Минимальный ключ за последнюю минуту", min_last_min),
                        ("Максимальный ключ за последнюю минуту", max_last_min),
                        ("Максимальный ключ выставленного диапазона", range_max_hex),
                        ("Время старта сканирования", start_time_str.clone()),
                        ("Время работы сессии", duration_str.clone()),
                        ("Количество запусков программы", self.sessions.len().to_string()),
                        ("Найдено совпадений ключей", found_current.to_string()),
                    ];

                    let available_height = ui.available_height() - 20.0;
                    ScrollArea::vertical()
                        .max_height(available_height)
                        .auto_shrink([false; 2])
                        .show(ui, |ui| {
                            Grid::new("stats_grid").num_columns(2).striped(true).show(ui, |ui| {
                                for (i, (label, value)) in rows.iter().enumerate() {
                                    let bg = if i % 2 == 0 { Color32::from_rgb(240, 240, 240) } else { Color32::from_rgb(255, 255, 200) };
                                    egui::Frame::none().fill(bg).show(ui, |ui| { ui.label(RichText::new(*label).size(12.0).color(Color32::BLACK)); });
                                    egui::Frame::none().fill(bg).show(ui, |ui| { ui.label(RichText::new(value).size(12.0).color(Color32::BLACK)); });
                                    ui.end_row();
                                }
                            });
                        });

                    let total_keys_str = self.get_total_keys_in_range().to_string();
                    ui.add_space(8.0);
                    ui.label(RichText::new("Ключей в диапазоне:").size(12.0).color(Color32::BLACK));
                    ui.horizontal(|ui| {
                        let mut text = total_keys_str.clone();
                        let edit = TextEdit::singleline(&mut text).desired_width(639.0).font(egui::FontId::new(MONOSPACE_FONT_SIZE, FontFamily::Monospace));
                        ui.add(edit);
                    });
                    ui.label(RichText::new(format!("Количество символов: {}", total_keys_str.len())).size(10.0).color(Color32::DARK_GRAY));
                });
            }
            _ => {}
        }

        TopBottomPanel::bottom("status_bar").show(ctx, |ui| {
            ui.horizontal(|ui| {
                let speed_str = format!("Скорость: {:.0} к/с", self.current_speed);
                ui.label(RichText::new(speed_str).size(12.0).color(Color32::BLACK));
                ui.add_space(20.0);
                if self.running {
                    ui.label(RichText::new("● Активно").size(12.0).color(Color32::GREEN));
                } else {
                    ui.label(RichText::new("○ Остановлено").size(12.0).color(Color32::RED));
                }
                ui.add_space(20.0);
                let range_text = format!("Диапазон: {} – {}", self.start_hex_str, self.end_hex_str);
                if self.carousel_enabled {
                    let limit_str = format!(" (лимит: {} млн)", self.carousel_keys_limit_input);
                    ui.label(RichText::new(format!("{}{}", range_text, limit_str)).size(12.0).color(Color32::BLACK));
                } else {
                    ui.label(RichText::new(range_text).size(12.0).color(Color32::BLACK));
                }
                ui.add_space(20.0);
                if !self.status_message.is_empty() {
                    ui.label(RichText::new(&self.status_message).size(12.0).color(self.status_color));
                }
                ui.add_space(10.0);
                if egui::color_picker::color_edit_button_srgba(ui, &mut self.status_color, egui::color_picker::Alpha::OnlyBlend).changed() {
                    self.save_config();
                }
            });
        });

        ctx.request_repaint_after(Duration::from_millis(100));
    }
}

fn main() -> Result<()> {
    let options = eframe::NativeOptions {
        viewport: egui::ViewportBuilder::default()
            .with_min_inner_size([640.0, 480.0])
            .with_inner_size([1200.0, 800.0]),
        ..Default::default()
    };
    eframe::run_native(
        "Bitcoin365 Carousel Searcher",
        options,
        Box::new(|cc| Box::new(App::new(cc))),
    )
    .unwrap();
    Ok(())
}