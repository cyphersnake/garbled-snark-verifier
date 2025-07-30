#![feature(maybe_uninit_array_assume_init)]

use std::{
    collections::{HashMap, HashSet, VecDeque},
    fs,
    io::{self, BufWriter, Write},
    mem::MaybeUninit,
    ptr,
    sync::{
        Arc, Mutex,
        atomic::{AtomicUsize, Ordering},
    },
    thread,
    time::{Duration, Instant, SystemTime, UNIX_EPOCH},
};

use crossbeam::channel;
use garbled_snark_verifier::{
    Circuit, Delta, GarbledWire, GarbledWires, S, WireId,
    circuit::{GateProvider, errors::CircuitError, file_gate_provider::FileGateProvider},
    process_monitor::{CircuitInfo, ProcessMonitor, ThreadStatus},
    tui_monitor::run_tui,
};
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha8Rng;
use serde::{Deserialize, Serialize};

// Include wire values generated from main branch
include!("../wire_values.rs");

/// Create input handler with actual proof values from main branch
fn create_proof_input_handler() -> Box<dyn Fn(WireId) -> Option<bool>> {
    // Create a HashMap for fast lookup
    let mut wire_values = HashMap::new();

    // Add all proof component values to the map
    for (wire_id, value) in PUBLIC_WIRE_VALUES.iter() {
        wire_values.insert(WireId(*wire_id as usize), *value);
    }

    for (wire_id, value) in PROOF_A_WIRE_VALUES.iter() {
        wire_values.insert(WireId(*wire_id as usize), *value);
    }

    for (wire_id, value) in PROOF_B_WIRE_VALUES.iter() {
        wire_values.insert(WireId(*wire_id as usize), *value);
    }

    for (wire_id, value) in PROOF_C_WIRE_VALUES.iter() {
        wire_values.insert(WireId(*wire_id as usize), *value);
    }

    Box::new(move |wire_id| wire_values.get(&wire_id).copied())
}

type DefaultHasher = blake3::Hasher;

#[derive(Serialize, Deserialize)]
struct LabelPair([u8; 16], [u8; 16]);

#[derive(Deserialize)]
struct Config {
    circuit_file_path: String,
    num_of_garbling: Option<usize>,
    /// Garbling IDs that should be skipped
    skip_garbling_ids: Option<Vec<usize>>,
    save_path: String,
    save_ciphertext_ids: Vec<usize>,
    worker_memory_gb: Option<u64>,
    memory_check_interval_ms: Option<u64>,
}

struct ThreadStats {
    thread_id: usize,
    gates_processed: usize,
    duration: Duration,
    xor_result: S,
}

#[derive(Serialize)]
struct ThreadResultExport {
    thread_id: usize,
    memory_usage_gb: f64,
    xor_result_hex: String,
    error: Option<String>,
    hash160: Option<String>,
}

#[derive(Serialize)]
struct MemoryPoint {
    elapsed_seconds: f64,
    memory_gb: f64,
    active_workers: usize,
}

#[derive(Serialize)]
struct MemoryAnalysisExport {
    baseline_gb: f64,
    peak_gb: f64,
    final_gb: f64,
    growth_rate_gb_per_hour: f64,
    efficiency_gb_per_worker: f64,
    peak_workers: usize,
    memory_timeline: Vec<MemoryPoint>,
}

#[derive(Serialize)]
struct ExperimentInfo {
    timestamp: u64,
    config_file_path: String,
    circuit_file_path: String,
    total_runtime_seconds: f64,
    status: String,
}

#[derive(Serialize)]
struct PerformanceExport {
    total_gates_processed: usize,
    peak_throughput_gates_per_sec: f64,
    memory_per_gate_bytes: f64,
}

#[derive(Serialize)]
struct ExperimentExport {
    experiment: ExperimentInfo,
    memory_analysis: MemoryAnalysisExport,
    performance: PerformanceExport,
    threads: Vec<ThreadResultExport>,
}

fn export_experiment_results_to_toml(
    snapshot: &garbled_snark_verifier::process_monitor::MonitorSnapshot,
    results: &[ThreadStats],
    config_path: &str,
    circuit_path: &str,
    save_dir: &str,
) -> std::io::Result<()> {
    let experiment = ExperimentInfo {
        timestamp: SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs(),
        config_file_path: config_path.to_string(),
        circuit_file_path: circuit_path.to_string(),
        total_runtime_seconds: snapshot.runtime.as_secs_f64(),
        status: "completed".to_string(),
    };

    let timeline = snapshot
        .system
        .memory_history
        .iter()
        .map(|(d, m)| MemoryPoint {
            elapsed_seconds: d.as_secs_f64(),
            memory_gb: *m,
            active_workers: snapshot.system.active_workers,
        })
        .collect();

    let memory_analysis = MemoryAnalysisExport {
        baseline_gb: snapshot.system.memory_baseline_gb,
        peak_gb: snapshot.system.memory_peak_gb,
        final_gb: snapshot.system.process_memory_gb,
        growth_rate_gb_per_hour: snapshot.system.memory_rate_gb_per_hour,
        efficiency_gb_per_worker: snapshot.system.memory_per_worker_gb,
        peak_workers: snapshot.system.max_workers,
        memory_timeline: timeline,
    };

    let performance = PerformanceExport {
        total_gates_processed: snapshot.total_gates_processed,
        peak_throughput_gates_per_sec: snapshot.total_speed,
        memory_per_gate_bytes: if snapshot.total_gates_processed > 0 {
            (snapshot.system.memory_peak_gb * 1024.0 * 1024.0 * 1024.0)
                / snapshot.total_gates_processed as f64
        } else {
            0.0
        },
    };

    let mut threads = Vec::new();
    for (snap, stats) in snapshot.threads.iter().zip(results.iter()) {
        threads.push(ThreadResultExport {
            thread_id: snap.thread_id,
            memory_usage_gb: snap.memory_usage_gb,
            xor_result_hex: stats.xor_result.to_hex(),
            error: snap.error_message.clone(),
            hash160: snap.input_hash160.clone(),
        });
    }

    let export = ExperimentExport {
        experiment,
        memory_analysis,
        performance,
        threads,
    };

    let toml_str = toml::to_string_pretty(&export).unwrap();
    std::fs::create_dir_all(save_dir)?;
    let path = format!("{}/experiment.toml", save_dir);
    std::fs::write(&path, toml_str)?;
    Ok(())
}

fn get_system_memory_info() -> Option<(f64, f64)> {
    use std::fs;

    // Try to read /proc/meminfo for more accurate system memory info
    if let Ok(meminfo) = fs::read_to_string("/proc/meminfo") {
        let mut total_mem_kb = None;
        let mut available_mem_kb = None;
        let mut swap_total_kb = None;
        let mut swap_free_kb = None;

        for line in meminfo.lines() {
            if line.starts_with("MemTotal:") {
                total_mem_kb = line.split_whitespace().nth(1)?.parse::<u64>().ok();
            } else if line.starts_with("MemAvailable:") {
                available_mem_kb = line.split_whitespace().nth(1)?.parse::<u64>().ok();
            } else if line.starts_with("SwapTotal:") {
                swap_total_kb = line.split_whitespace().nth(1)?.parse::<u64>().ok();
            } else if line.starts_with("SwapFree:") {
                swap_free_kb = line.split_whitespace().nth(1)?.parse::<u64>().ok();
            }
        }

        if let (Some(total), Some(available), Some(swap_total), Some(swap_free)) =
            (total_mem_kb, available_mem_kb, swap_total_kb, swap_free_kb)
        {
            let total_virtual_gb = (total + swap_total) as f64 / 1024.0 / 1024.0;
            let available_virtual_gb = (available + swap_free) as f64 / 1024.0 / 1024.0;
            return Some((total_virtual_gb, available_virtual_gb));
        }
    }

    // Fallback to memory_stats crate if /proc/meminfo fails
    memory_stats::memory_stats().map(|stats| {
        let virtual_gb = stats.virtual_mem as f64 / 1024.0 / 1024.0 / 1024.0;
        // Assume 80% of virtual memory is available as a conservative estimate
        (virtual_gb, virtual_gb * 0.8)
    })
}

fn calculate_max_workers_by_virtual_memory(
    available_virtual_gb: f64,
    worker_memory_gb: u64,
    max_cap: usize,
) -> usize {
    let max_by_memory = (available_virtual_gb / worker_memory_gb as f64).floor() as usize;
    max_by_memory.min(max_cap)
}

#[derive(Clone)]
struct TaskConfig {
    task_id: usize,
    circuit_file_path: String,
    input_wires: Vec<WireId>,
    output_wires: Vec<WireId>,
    num_wire: usize,
    timestamped_save_path: String,
    should_save_ciphertexts: bool,
}

struct VirtualMemoryController {
    max_workers: usize,
    worker_memory_gb: u64,
    memory_check_interval: Duration,
    pending_tasks: Arc<Mutex<VecDeque<TaskConfig>>>,
    active_workers: Arc<Mutex<Vec<thread::JoinHandle<Result<ThreadStats, CircuitError>>>>>,
}

fn spawn_progress_monitor(
    gate_counter: Arc<AtomicUsize>,
    total_gates: usize,
    thread_id: Option<usize>,
) -> thread::JoinHandle<()> {
    thread::spawn(move || {
        let start_time = Instant::now();
        let mut last_count = 0;
        let mut last_time = start_time;

        loop {
            thread::sleep(Duration::from_millis(1000));

            let current_count = gate_counter.load(Ordering::Relaxed);
            let current_time = Instant::now();

            if current_count == 0 {
                continue;
            }
            if current_count == usize::MAX {
                break;
            }

            let elapsed = (current_time - last_time).as_secs_f64();
            let gates_per_second = if elapsed > 0.0 {
                (current_count - last_count) as f64 / elapsed
            } else {
                0.0
            };

            let mem_info = if let Some(usage) = memory_stats::memory_stats() {
                format!(
                    "Physical: {:.2} MB, Virtual: {:.2} MB",
                    usage.physical_mem as f64 / 1024.0 / 1024.0,
                    usage.virtual_mem as f64 / 1024.0 / 1024.0
                )
            } else {
                "Memory: N/A".to_string()
            };

            let percentage = if total_gates > 0 {
                (current_count as f64 / total_gates as f64) * 100.0
            } else {
                0.0
            };

            let thread_prefix = if let Some(id) = thread_id {
                format!("Thread {}: ", id)
            } else {
                String::new()
            };

            if let Some(id) = thread_id {
                // For multi-threaded: use ANSI escape codes to update specific line
                print!(
                    "\x1b[s\x1b[{}H{}Gate: {current_count}/{total_gates} ({percentage:.1}%) | Speed: {gates_per_second:.0} gates/s | {mem_info}\x1b[K\x1b[u",
                    id + 1,
                    thread_prefix
                );
            } else {
                // For single-threaded: use carriage return
                print!(
                    "\r{}Gate: {current_count}/{total_gates} ({percentage:.1}%) | Speed: {gates_per_second:.0} gates/s | {mem_info}",
                    thread_prefix
                );
            }
            io::stdout().flush().unwrap();

            last_count = current_count;
            last_time = current_time;

            if current_count > 0 && gates_per_second == 0.0 && elapsed > 3.0 {
                break;
            }
        }
    })
}

fn discover_completed_garblings(base_path: &str) -> io::Result<HashSet<usize>> {
    let mut completed = HashSet::new();
    if let Ok(entries) = fs::read_dir(base_path) {
        for entry in entries.flatten() {
            if let Ok(id) = entry.file_name().to_string_lossy().parse::<usize>() {
                let path = entry.path();
                if path.join("ciphertext_hash.bin").exists()
                    || path.join("output_labels.json").exists()
                {
                    completed.insert(id);
                }
            }
        }
    }
    Ok(completed)
}

fn run_multiple_garbling<H: digest::Digest + Default + Clone>(
    circuit_file_path: &str,
    circuit_template: &Circuit<FileGateProvider>,
    num_of_garbling: usize,
    save_path: &str,
    skip_garbling_ids: &[usize],
    save_ciphertext_ids: &[usize],
    worker_memory_gb: u64,
    memory_check_interval: Duration,
) -> Result<Vec<ThreadStats>, CircuitError> {
    // Create timestamp for this run
    let timestamp = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_secs();
    let timestamp_dir = format!("{}/{}", save_path, timestamp);

    // Combine skip list from config with already completed garblings
    let mut skip_set: HashSet<usize> = skip_garbling_ids.iter().copied().collect();
    skip_set.extend(
        discover_completed_garblings(save_path).map_err(|e| {
            CircuitError::GarblingFailed(format!("Failed to scan save directory: {}", e))
        })?,
    );
    let total_tasks = num_of_garbling.saturating_sub(skip_set.len());

    if !skip_set.is_empty() {
        println!("Skipping garbling IDs: {:?}", skip_set);
    }
    println!(
        "Starting {} independent garbling threads with smart memory management...",
        total_tasks
    );
    println!(
        "Worker memory requirement: {}GB per thread",
        worker_memory_gb
    );
    println!("Saving to timestamped directory: {}", timestamp_dir);

    // Initialize ProcessMonitor
    let circuit_info = CircuitInfo {
        num_wire: circuit_template.num_wire,
        input_wire_count: circuit_template.input_wires.len(),
        output_wire_count: circuit_template.output_wires.len(),
        total_gates: circuit_template.gates.gate_count().unwrap_or(0),
    };

    let initial_memory_gb = if let Some(usage) = memory_stats::memory_stats() {
        usage.virtual_mem as f64 / 1024.0 / 1024.0 / 1024.0
    } else {
        1.0 // Start with minimal baseline if can't detect
    };

    // Get system memory information
    let (total_virtual_gb, available_virtual_gb) = get_system_memory_info().ok_or_else(|| {
        CircuitError::GarblingFailed("Failed to get system memory stats".to_string())
    })?;

    println!(
        "Total virtual memory (RAM + Swap): {:.2}GB",
        total_virtual_gb
    );
    println!("Available virtual memory: {:.2}GB", available_virtual_gb);

    // Calculate initial number of workers we can start
    let initial_workers = calculate_max_workers_by_virtual_memory(
        available_virtual_gb,
        worker_memory_gb,
        total_tasks,
    );

    println!(
        "Starting with {} workers (limited by memory)",
        initial_workers
    );

    ProcessMonitor::initialize(
        circuit_info,
        timestamp_dir.clone(),
        initial_memory_gb,
        initial_workers,
        total_tasks,
    );

    // Create task queue with all remaining tasks
    let mut pending_tasks = VecDeque::new();
    for task_id in 0..num_of_garbling {
        if skip_set.contains(&task_id) {
            continue;
        }
        pending_tasks.push_back(TaskConfig {
            task_id,
            circuit_file_path: circuit_file_path.to_string(),
            input_wires: circuit_template.input_wires.clone(),
            output_wires: circuit_template.output_wires.clone(),
            num_wire: circuit_template.num_wire,
            timestamped_save_path: timestamp_dir.clone(),
            should_save_ciphertexts: save_ciphertext_ids.contains(&task_id),
        });
    }

    let pending_tasks = Arc::new(Mutex::new(pending_tasks));
    let active_workers = Arc::new(Mutex::new(Vec::new()));
    let completed_results = Arc::new(Mutex::new(Vec::new()));

    // Reserve space for thread progress lines
    for _ in 0..num_of_garbling {
        println!();
    }

    // Start initial workers
    for _ in 0..initial_workers {
        if let Some(task) = pending_tasks.lock().unwrap().pop_front() {
            let handle = spawn_worker_task::<H>(task, Arc::clone(&completed_results));
            active_workers.lock().unwrap().push(handle);
        }
    }

    // Start TUI in background thread
    let tui_handle = thread::spawn(|| {
        if let Err(e) = run_tui() {
            eprintln!("TUI failed: {}", e);
        }
    });

    // Memory monitoring and worker management loop
    let pending_tasks_clone = Arc::clone(&pending_tasks);
    let active_workers_clone = Arc::clone(&active_workers);
    let completed_results_clone = Arc::clone(&completed_results);

    let poll_interval = Duration::from_millis(100);
    let mut last_metrics = Instant::now();

    loop {
        thread::sleep(poll_interval);

        if last_metrics.elapsed() >= memory_check_interval {
            if let Some((total_gb, available_gb)) = get_system_memory_info() {
                // Get REAL current process memory usage from system
                let process_memory_gb = if let Some(usage) = memory_stats::memory_stats() {
                    usage.virtual_mem as f64 / 1024.0 / 1024.0 / 1024.0
                } else {
                    0.0 // If can't get real measurement, show 0 instead of fake calculations
                };

                if let Some(monitor) = ProcessMonitor::instance() {
                    if let Ok(guard) = monitor.lock() {
                        guard.update_system_metrics(
                            total_gb,
                            available_gb,
                            process_memory_gb,
                            pending_tasks_clone.lock().unwrap().len(),
                        );
                        guard.update_storage_metrics();
                        guard.save_snapshot_to_file();
                    }
                }
            }
            last_metrics = Instant::now();
        }

        // Check for completed workers
        let mut workers = active_workers_clone.lock().unwrap();
        let mut i = 0;
        while i < workers.len() {
            if workers[i].is_finished() {
                let completed_handle = workers.remove(i);
                match completed_handle.join() {
                    Ok(result) => {
                        match result {
                            Ok(stats) => {
                                completed_results_clone.lock().unwrap().push(stats);
                                // Mark task as completed in ProcessMonitor
                                if let Some(monitor) = ProcessMonitor::instance() {
                                    if let Ok(guard) = monitor.lock() {
                                        guard.mark_task_completed();
                                    }
                                }
                            }
                            Err(_) => {
                                // Mark task as failed in ProcessMonitor
                                if let Some(monitor) = ProcessMonitor::instance() {
                                    if let Ok(guard) = monitor.lock() {
                                        guard.mark_task_failed();
                                    }
                                }
                            }
                        }
                    }
                    Err(_) => {
                        eprintln!("Worker thread panicked");
                        // Mark task as failed in ProcessMonitor
                        if let Some(monitor) = ProcessMonitor::instance() {
                            if let Ok(guard) = monitor.lock() {
                                guard.mark_task_failed();
                            }
                        }
                    }
                }

                // Try to start a new worker immediately when one finishes
                if let Some((_, current_available_gb)) = get_system_memory_info() {
                    let pending_count = pending_tasks_clone.lock().unwrap().len();
                    let max_workers = calculate_max_workers_by_virtual_memory(
                        current_available_gb,
                        worker_memory_gb,
                        pending_count + workers.len(),
                    );

                    if workers.len() < max_workers {
                        if let Some(task) = pending_tasks_clone.lock().unwrap().pop_front() {
                            let handle =
                                spawn_worker_task::<H>(task, Arc::clone(&completed_results_clone));
                            workers.push(handle);
                        }
                    }
                }
            } else {
                i += 1;
            }
        }

        // Check if we can start more workers
        let pending_count = pending_tasks_clone.lock().unwrap().len();
        let active_count = workers.len();

        if pending_count == 0 && active_count == 0 {
            break; // All tasks completed
        }

        if pending_count > 0 {
            if let Some((_, current_available_gb)) = get_system_memory_info() {
                let max_new_workers = calculate_max_workers_by_virtual_memory(
                    current_available_gb,
                    worker_memory_gb,
                    pending_count,
                );

                let workers_to_start = max_new_workers.saturating_sub(active_count);

                for _ in 0..workers_to_start {
                    if let Some(task) = pending_tasks_clone.lock().unwrap().pop_front() {
                        let handle =
                            spawn_worker_task::<H>(task, Arc::clone(&completed_results_clone));
                        workers.push(handle);
                    } else {
                        break;
                    }
                }
            }
        }
    }

    // Wait for TUI to finish (user pressed 'q')
    let _ = tui_handle.join();

    // Extract final results
    let results = Arc::try_unwrap(completed_results)
        .map_err(|_| CircuitError::GarblingFailed("Failed to extract results".to_string()))?
        .into_inner()
        .map_err(|_| CircuitError::GarblingFailed("Failed to unlock results".to_string()))?;

    Ok(results)
}

fn spawn_worker_task<H: digest::Digest + Default + Clone>(
    task: TaskConfig,
    _completed_results: Arc<Mutex<Vec<ThreadStats>>>,
) -> thread::JoinHandle<Result<ThreadStats, CircuitError>> {
    thread::spawn(move || {
        let start_time = Instant::now();
        let mut rng = ChaCha8Rng::seed_from_u64(task.task_id as u64);
        let thread_dir = format!("{}/{}", task.timestamped_save_path, task.task_id);
        let _ = fs::create_dir_all(&thread_dir);

        // Create a new FileGateProvider for this thread first to get gate count
        let file_gate_provider = match FileGateProvider::new(&task.circuit_file_path) {
            Ok(provider) => provider,
            Err(e) => {
                let error_msg = format!("Failed to create FileGateProvider: {}", e);
                // Update ProcessMonitor with error
                if let Some(monitor) = ProcessMonitor::instance() {
                    if let Ok(guard) = monitor.lock() {
                        guard.update_thread_error(task.task_id, error_msg.clone());
                    }
                }
                return Err(CircuitError::GarblingFailed(error_msg));
            }
        };

        let total_gates = file_gate_provider.gate_count().unwrap_or(0);

        // Register with ProcessMonitor
        let gate_counter = if let Some(monitor) = ProcessMonitor::instance() {
            if let Ok(guard) = monitor.lock() {
                guard.update_thread_status(task.task_id, ThreadStatus::Starting);
                Some(guard.register_thread(task.task_id, total_gates))
            } else {
                None
            }
        } else {
            None
        };

        // Create a new circuit for this thread
        let thread_circuit = Circuit {
            num_wire: task.num_wire,
            input_wires: task.input_wires,
            output_wires: task.output_wires,
            gates: file_gate_provider,
            gate_count: Default::default(),
        };

        // Update status to running
        if let Some(monitor) = ProcessMonitor::instance() {
            if let Ok(guard) = monitor.lock() {
                guard.update_thread_status(task.task_id, ThreadStatus::Running);
            }
        }

        match garble_with_streaming_thread::<H, _>(
            &thread_circuit,
            &mut rng,
            Some(task.task_id),
            &task.timestamped_save_path,
            task.should_save_ciphertexts,
            gate_counter,
        ) {
            Ok((_, xor_result)) => {
                let duration = start_time.elapsed();

                // Update final status and result
                if let Some(monitor) = ProcessMonitor::instance() {
                    if let Ok(guard) = monitor.lock() {
                        guard.update_thread_status(task.task_id, ThreadStatus::Finished);
                        guard.update_thread_result(task.task_id, xor_result);
                        guard.save_snapshot_to_file();
                    }
                }

                let result_export = ThreadResultExport {
                    thread_id: task.task_id,
                    memory_usage_gb: 0.0,
                    xor_result_hex: xor_result.to_hex(),
                    error: None,
                    hash160: None,
                };
                let path = format!("{}/result.toml", thread_dir);
                if let Ok(text) = toml::to_string_pretty(&result_export) {
                    let _ = fs::write(path, text);
                }

                Ok(ThreadStats {
                    thread_id: task.task_id,
                    gates_processed: thread_circuit.gates.gate_count().unwrap_or(0),
                    duration,
                    xor_result,
                })
            }
            Err(e) => {
                // Update error status with error message
                if let Some(monitor) = ProcessMonitor::instance() {
                    if let Ok(guard) = monitor.lock() {
                        guard.update_thread_error(task.task_id, format!("{:?}", e));
                        guard.save_snapshot_to_file();
                    }
                }
                let result_export = ThreadResultExport {
                    thread_id: task.task_id,
                    memory_usage_gb: 0.0,
                    xor_result_hex: String::new(),
                    error: Some(format!("{:?}", e)),
                    hash160: None,
                };
                let path = format!("{}/result.toml", thread_dir);
                if let Ok(text) = toml::to_string_pretty(&result_export) {
                    let _ = fs::write(path, text);
                }
                Err(e)
            }
        }
    })
}

fn garble_with_streaming<H: digest::Digest + Default + Clone, G: GateProvider>(
    circuit: &Circuit<G>,
    rng: &mut impl Rng,
) -> Result<(GarbledWires, S), CircuitError> {
    garble_with_streaming_thread::<H, G>(circuit, rng, None, "", false, None)
}

#[inline(always)]
pub fn concat_16<T: Copy>(a: &[T; 16], b: &[T; 16]) -> [T; 32] {
    // --- choose ONE of the two lines below ---------------------------
    // Modern compiler (≥1.70):
    // let mut out: [MaybeUninit<T>; 32] = MaybeUninit::uninit_array();

    // Legacy compiler:
    let mut out: [MaybeUninit<T>; 32] =
        unsafe { MaybeUninit::<[MaybeUninit<T>; 32]>::uninit().assume_init() };
    // ------------------------------------------------------------------

    unsafe {
        ptr::copy_nonoverlapping(a.as_ptr(), out.as_mut_ptr() as *mut T, 16);
        ptr::copy_nonoverlapping(b.as_ptr(), (out.as_mut_ptr() as *mut T).add(16), 16);

        MaybeUninit::array_assume_init(out)
    }
}

fn garble_with_streaming_thread<H: digest::Digest + Default + Clone, G: GateProvider>(
    circuit: &Circuit<G>,
    rng: &mut impl Rng,
    thread_id: Option<usize>,
    save_path: &str,
    should_save_ciphertexts: bool,
    external_gate_counter: Option<Arc<AtomicUsize>>,
) -> Result<(GarbledWires, S), CircuitError> {
    log::debug!(
        "garble_streaming: start wires={} gates={:?}",
        circuit.num_wire,
        circuit.gates.gate_count()
    );

    // Create save directory if needed
    let save_dir = if !save_path.is_empty() && thread_id.is_some() {
        let dir_path = format!("{}/{}", save_path, thread_id.unwrap());
        fs::create_dir_all(&dir_path).map_err(|e| {
            CircuitError::GarblingFailed(format!(
                "Failed to create save directory {}: {}",
                dir_path, e
            ))
        })?;
        Some(dir_path)
    } else {
        None
    };

    // Setup ciphertext file writer if needed
    let mut ciphertext_writer = if should_save_ciphertexts && save_dir.is_some() {
        let ciphertext_path = format!("{}/ciphertexts.bin", save_dir.as_ref().unwrap());
        let file = fs::File::create(&ciphertext_path).map_err(|e| {
            CircuitError::GarblingFailed(format!(
                "Failed to create ciphertext file {}: {}",
                ciphertext_path, e
            ))
        })?;
        Some(BufWriter::new(file))
    } else {
        None
    };

    let delta = Delta::generate(rng);
    let mut wires = GarbledWires::new(circuit.num_wire);
    let mut issue_fn = || GarbledWire::random(rng, &delta);

    [
        circuit.get_false_wire_constant(),
        circuit.get_true_wire_constant(),
    ]
    .iter()
    .chain(circuit.input_wires.iter())
    .for_each(|wire_id| {
        wires.get_or_init(*wire_id, &mut issue_fn).unwrap();
    });

    // Print bitcoin::hash160 of all public input wires (garbled) - accumulated
    let mut all_input_bytes = Vec::new();
    for &wire_id in &circuit.input_wires {
        if let Ok(garbled_wire) = wires.get(wire_id) {
            all_input_bytes.extend_from_slice(&garbled_wire.label0.0);
            all_input_bytes.extend_from_slice(&garbled_wire.label1.0);
        }
    }
    let input_hash =
        <bitcoin::hashes::hash160::Hash as bitcoin::hashes::Hash>::hash(&all_input_bytes);

    // Report hash160 to ProcessMonitor instead of printing
    if let Some(id) = thread_id {
        if let Some(monitor) = ProcessMonitor::instance() {
            if let Ok(guard) = monitor.lock() {
                guard.update_thread_hash160(id, format!("{:?}", input_hash));
            }
        }
    }

    // Save input labels if save directory exists
    if let Some(ref save_dir) = save_dir {
        let mut input_labels = Vec::new();
        for &wire_id in &circuit.input_wires {
            if let Ok(garbled_wire) = wires.get(wire_id) {
                input_labels.push(LabelPair(garbled_wire.label0.0, garbled_wire.label1.0));
            }
        }
        let input_labels_path = format!("{}/inputs_labels.json", save_dir);
        let input_labels_json = serde_json::to_string_pretty(&input_labels).map_err(|e| {
            CircuitError::GarblingFailed(format!("Failed to serialize input labels: {}", e))
        })?;
        fs::write(&input_labels_path, input_labels_json).map_err(|e| {
            CircuitError::GarblingFailed(format!(
                "Failed to write input labels to {}: {}",
                input_labels_path, e
            ))
        })?;
    }

    log::debug!("garble_streaming: delta={delta:?}");

    let (sender, receiver) = channel::bounded::<S>(10000);

    // Progress tracking with atomic counter
    // Use external counter if provided, otherwise create new one
    let (gate_counter, should_spawn_monitor) = match external_gate_counter {
        Some(counter) => (counter, false),
        None => (Arc::new(AtomicUsize::new(0)), true),
    };

    // Spawn progress monitoring thread only if we don't have external counter (avoid double monitoring)
    let total_gates = circuit.gates.gate_count().unwrap_or(0);
    let progress_thread = if should_spawn_monitor {
        Some(spawn_progress_monitor(
            gate_counter.clone(),
            total_gates,
            thread_id,
        ))
    } else {
        None
    };

    let ciphertext_accumulator_thread = thread::spawn(move || {
        let mut xor_result = S::zero();
        while let Ok(ciphertext) = receiver.recv() {
            xor_result = S(
                blake3::hash(&concat_16(&xor_result.0, &ciphertext.0)).as_bytes()[0..16]
                    .try_into()
                    .unwrap(),
            );

            // Write ciphertext to file if writer is available
            if let Some(ref mut writer) = ciphertext_writer {
                if let Err(e) = writer.write_all(&ciphertext.0) {
                    log::error!("Failed to write ciphertext to file: {}", e);
                    break;
                }
            }
        }

        // Flush the writer if it exists
        if let Some(ref mut writer) = ciphertext_writer {
            if let Err(e) = writer.flush() {
                log::error!("Failed to flush ciphertext file: {}", e);
            }
        }

        xor_result
    });

    circuit.gates.gates().enumerate().try_for_each(|(i, g)| {
        gate_counter.store(i + 1, Ordering::Relaxed);

        match g.as_ref().garble::<H>(i, &mut wires, &delta, rng) {
            Ok(Some(row)) => {
                log::debug!("garble_streaming: gate[{i}] table_entries={row:?}");
                if let Err(err) = sender.send(row) {
                    return Err(CircuitError::GarblingFailed(format!("Send failed {err:?}")));
                }
                Ok(())
            }
            Ok(None) => {
                log::debug!("garble_streaming: gate[{i}] free");
                Ok(())
            }
            Err(err) => {
                log::error!("garble_streaming: gate[{i}] error={err:?}");
                Err(err)
            }
        }?;

        Ok(())
    })?;

    // eval done - don't print to avoid TUI interference

    drop(sender);

    let xor_result = ciphertext_accumulator_thread
        .join()
        .map_err(|_| CircuitError::GarblingFailed("XOR thread join failed".to_string()))?;

    // xor_result computed - don't print to avoid TUI interference

    // Wait for progress thread to finish and print final newline
    if let Some(thread) = progress_thread {
        gate_counter.store(usize::MAX, Ordering::Relaxed);
        let _ = thread.join();
        // newline - removed to avoid TUI interference
    }

    // Print bitcoin::hash160 of all output wires (garbled) - after full garbling process
    let mut all_output_bytes = Vec::new();
    for &wire_id in &circuit.output_wires {
        if let Ok(garbled_wire) = wires.get(wire_id) {
            all_output_bytes.extend_from_slice(&garbled_wire.label0.0);
            all_output_bytes.extend_from_slice(&garbled_wire.label1.0);
        }
    }
    let output_hash =
        <bitcoin::hashes::hash160::Hash as bitcoin::hashes::Hash>::hash(&all_output_bytes);
    // Output hash computed - don't print to avoid TUI interference

    // Save output labels and ciphertext hash if save directory exists
    if let Some(ref save_dir) = save_dir {
        // Save output labels
        let mut output_labels = Vec::new();
        for &wire_id in &circuit.output_wires {
            if let Ok(garbled_wire) = wires.get(wire_id) {
                output_labels.push(LabelPair(garbled_wire.label0.0, garbled_wire.label1.0));
            }
        }
        let output_labels_path = format!("{}/output_labels.json", save_dir);
        let output_labels_json = serde_json::to_string_pretty(&output_labels).map_err(|e| {
            CircuitError::GarblingFailed(format!("Failed to serialize output labels: {}", e))
        })?;
        fs::write(&output_labels_path, output_labels_json).map_err(|e| {
            CircuitError::GarblingFailed(format!(
                "Failed to write output labels to {}: {}",
                output_labels_path, e
            ))
        })?;

        // Save ciphertext hash
        let hash_path = format!("{}/ciphertext_hash.bin", save_dir);
        fs::write(&hash_path, &xor_result.0).map_err(|e| {
            CircuitError::GarblingFailed(format!(
                "Failed to write ciphertext hash to {}: {}",
                hash_path, e
            ))
        })?;
    }

    log::debug!("garble_streaming: complete xor_result={xor_result:?}");
    Ok((wires, xor_result))
}

fn evaluate_with_streaming<G: GateProvider>(
    circuit: &Circuit<G>,
    get_input: impl Fn(WireId) -> Option<bool>,
) -> Result<impl Iterator<Item = (WireId, bool)>, garbled_snark_verifier::circuit::evaluation::Error>
{
    log::debug!(
        "evaluate_streaming: start wires={} gates={:?}",
        circuit.num_wire,
        circuit.gates.gate_count()
    );

    use bitvec::prelude::*;
    let mut wire_values = bitvec![0; circuit.num_wire];

    // Initialize constant wires
    wire_values.set(circuit.get_false_wire_constant().0, false);
    wire_values.set(circuit.get_true_wire_constant().0, true);

    // Initialize input wires
    for &wire_id in &circuit.input_wires {
        let value = get_input(wire_id)
            .ok_or(garbled_snark_verifier::circuit::evaluation::Error::LostInput(wire_id))?;
        wire_values.set(wire_id.0, value);
    }

    // Progress tracking with atomic counter
    let gate_counter = Arc::new(AtomicUsize::new(0));

    // Spawn progress monitoring thread
    let total_gates = circuit.gates.gate_count().unwrap_or(0);
    let progress_thread = spawn_progress_monitor(gate_counter.clone(), total_gates, None);

    // Process gates with progress tracking
    circuit
        .gates
        .gates()
        .enumerate()
        .try_for_each(|(i, gate)| {
            gate_counter.store(i + 1, Ordering::Relaxed);

            let a = wire_values[gate.wire_a().0];
            let b = wire_values[gate.wire_b().0];
            let result = gate.gate_type().f()(a, b);
            wire_values.set(gate.wire_c().0, result);

            log::debug!("evaluate_streaming: gate[{i}] a={a} b={b} result={result}");

            Ok::<(), garbled_snark_verifier::circuit::evaluation::Error>(())
        })?;

    // Wait for progress thread to finish and print final newline
    gate_counter.store(usize::MAX, Ordering::Relaxed);
    let _ = progress_thread.join();
    println!();

    log::debug!("evaluate_streaming: complete");

    Ok(circuit
        .output_wires
        .iter()
        .map(move |&wire_id| (wire_id, wire_values[wire_id.0])))
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("File-based Circuit Example");
    println!("=========================");

    // Load config file from command line argument
    let config_file_path = std::env::args()
        .nth(1)
        .ok_or("Usage: cargo run --example file_circuit_example <config.toml>")?;

    println!("Loading config file: {config_file_path}");

    // Read and parse TOML config file
    let config_contents = std::fs::read_to_string(&config_file_path)
        .map_err(|e| format!("Failed to read config file '{}': {}", config_file_path, e))?;

    let config: Config = toml::from_str(&config_contents)
        .map_err(|e| format!("Failed to parse config file '{}': {}", config_file_path, e))?;

    let circuit_file_path = config.circuit_file_path;
    let num_of_garbling = config.num_of_garbling.unwrap_or_else(|| {
        thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(4)
    });
    let save_path = config.save_path;
    let save_ciphertext_ids = config.save_ciphertext_ids;
    let worker_memory_gb = config.worker_memory_gb.unwrap_or(357);
    let memory_check_interval =
        Duration::from_millis(config.memory_check_interval_ms.unwrap_or(2000));

    println!("Loading circuit file: {circuit_file_path}");
    println!("Using {num_of_garbling} garblings for parallel processing");
    println!("Save path: {save_path}");
    println!(
        "Save ciphertext for garbling IDs: {:?}",
        save_ciphertext_ids
    );

    // Create a FileGateProvider from the circuit file
    let file_gate_provider = FileGateProvider::new(&circuit_file_path)?;
    println!(
        "File contains {} gates",
        file_gate_provider.gate_count().unwrap()
    );

    // Create a Circuit using the FileGateProvider
    // For now, we'll use placeholder values - in reality these would be detected
    let file_circuit = Circuit {
        num_wire: 11659311111,
        input_wires: PUBLIC_WIRE_VALUES
            .iter()
            .chain(PROOF_A_WIRE_VALUES.iter())
            .chain(PROOF_B_WIRE_VALUES.iter())
            .chain(PROOF_C_WIRE_VALUES.iter())
            .map(|(wire_id, _val)| WireId(*wire_id as usize))
            .collect::<Vec<WireId>>(),
        output_wires: vec![WireId(OUTPUT_WIRE_VALUE.0 as usize)],
        gates: file_gate_provider,
        gate_count: Default::default(),
    };

    println!("Created file-based circuit (input/output detection not implemented)");

    // Use proof values from main branch as input handler
    let _input_handler = create_proof_input_handler();

    println!(
        "Created input handler with {} wire values",
        PUBLIC_WIRE_VALUES.len()
            + PROOF_A_WIRE_VALUES.len()
            + PROOF_B_WIRE_VALUES.len()
            + PROOF_C_WIRE_VALUES.len()
    );

    // Run circuit evaluation with progress tracking
    println!("\nRunning circuit evaluation with progress tracking...");

    //let start_time = Instant::now();
    //let _result = evaluate_with_streaming(&file_circuit, input_handler)?.collect::<Vec<_>>()[0].1;
    //let evaluation_duration = start_time.elapsed();

    //// Display final evaluation statistics
    //let total_gates = file_circuit.gates.gate_count().unwrap_or(0);
    //let gates_per_sec = if evaluation_duration.as_secs_f64() > 0.0 {
    //    total_gates as f64 / evaluation_duration.as_secs_f64()
    //} else {
    //    0.0
    //};

    //println!("\nEvaluation completed!");
    //println!("  Total gates: {total_gates}");
    //println!("  Total time: {:.2}s", evaluation_duration.as_secs_f64());
    //println!("  Average throughput: {gates_per_sec:.0} gates/s");

    //let final_mem_info = if let Some(usage) = memory_stats::memory_stats() {
    //    format!(
    //        "Physical: {:.2} MB, Virtual: {:.2} MB",
    //        usage.physical_mem as f64 / 1024.0 / 1024.0,
    //        usage.virtual_mem as f64 / 1024.0 / 1024.0
    //    )
    //} else {
    //    "Memory: N/A".to_string()
    //};
    //println!("  Final memory usage: {final_mem_info}");

    println!("\nTesting multiple parallel garbling...");
    match run_multiple_garbling::<DefaultHasher>(
        &circuit_file_path,
        &file_circuit,
        num_of_garbling,
        &save_path,
        config
            .skip_garbling_ids
            .as_deref()
            .unwrap_or_default(),
        &save_ciphertext_ids,
        worker_memory_gb,
        memory_check_interval,
    ) {
        Ok(results) => {
            println!(
                "All {} garbling threads completed successfully!",
                results.len()
            );

            let total_gates: usize = results.iter().map(|r| r.gates_processed).sum();
            let total_duration = results
                .iter()
                .map(|r| r.duration)
                .max()
                .unwrap_or(Duration::ZERO);
            let avg_gates_per_sec = if total_duration.as_secs_f64() > 0.0 {
                total_gates as f64 / total_duration.as_secs_f64()
            } else {
                0.0
            };

            println!("\nAggregate Statistics:");
            println!("  Total gates processed: {}", total_gates);
            println!("  Total time: {:.2}s", total_duration.as_secs_f64());
            println!("  Average throughput: {:.0} gates/s", avg_gates_per_sec);

            println!("\nPer-thread Statistics:");
            for stats in &results {
                let gates_per_sec = if stats.duration.as_secs_f64() > 0.0 {
                    stats.gates_processed as f64 / stats.duration.as_secs_f64()
                } else {
                    0.0
                };
                println!(
                    "  Thread {}: {} gates in {:.2}s ({:.0} gates/s)",
                    stats.thread_id,
                    stats.gates_processed,
                    stats.duration.as_secs_f64(),
                    gates_per_sec
                );
            }

            if let Some(monitor) = ProcessMonitor::instance() {
                if let Ok(guard) = monitor.lock() {
                    let snap = guard.get_snapshot();
                    let save_dir = guard.save_folder();
                    if let Err(e) = export_experiment_results_to_toml(
                        &snap,
                        &results,
                        &config_file_path,
                        &circuit_file_path,
                        &save_dir,
                    ) {
                        eprintln!("Failed to export results: {}", e);
                    }
                }
            }
        }
        Err(e) => {
            println!("Multiple garbling failed: {:?}", e);
        }
    }

    println!("\nFile-based circuit loading successful!");
    println!("Next steps: Implement input/output wire detection for your specific circuit");

    Ok(())
}
