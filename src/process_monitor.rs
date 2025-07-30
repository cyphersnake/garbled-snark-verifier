use std::{
    collections::{HashMap, VecDeque},
    fs,
    path::Path,
    sync::{
        atomic::{AtomicUsize, Ordering},
        Arc, Mutex,
    },
    time::{Duration, Instant},
};

use once_cell::sync::Lazy;
use serde::Serialize;

use crate::S;

#[derive(Debug, Clone, Copy, PartialEq, Serialize)]
pub enum ThreadStatus {
    Starting,
    Running,
    Completing,
    Finished,
    Error,
}

#[derive(Debug, Clone, Serialize)]
pub struct ThreadMetrics {
    pub thread_id: usize,
    #[serde(serialize_with = "serialize_atomic_usize")]
    pub current_gate: Arc<AtomicUsize>,
    pub total_gates: usize,
    pub gates_per_second: f64,
    pub memory_usage_gb: f64,
    pub status: ThreadStatus,
    pub xor_result: Option<S>,
    #[serde(serialize_with = "serialize_instant")]
    pub start_time: Instant,
    #[serde(serialize_with = "serialize_duration")]
    pub duration: Duration,
    pub speed_history: VecDeque<f64>,
    pub error_message: Option<String>,
    pub input_hash160: Option<String>,
}

#[derive(Debug, Clone, Serialize)]
pub struct SystemMetrics {
    pub total_memory_gb: f64,
    pub available_memory_gb: f64,
    pub process_memory_gb: f64,
    pub memory_baseline_gb: f64,
    pub memory_peak_gb: f64,
    pub memory_rate_gb_per_hour: f64,
    pub active_workers: usize,
    pub max_workers: usize,
    pub pending_tasks: usize,
    pub save_folder_size_gb: f64,
    pub disk_free_gb: f64,
    pub files_written: usize,
    #[serde(serialize_with = "serialize_memory_history")]
    pub memory_history: Vec<(Duration, f64)>,
    pub memory_per_worker_gb: f64,
    // Global context from config
    pub total_garbling_tasks: usize,
    pub completed_tasks: usize,
    pub failed_tasks: usize,
}

#[derive(Debug, Clone, Serialize)]
pub struct CircuitInfo {
    pub num_wire: usize,
    pub input_wire_count: usize,
    pub output_wire_count: usize,
    pub total_gates: usize,
}

#[derive(Debug)]
pub struct ProcessMonitor {
    threads: Arc<Mutex<HashMap<usize, ThreadMetrics>>>,
    system: Arc<Mutex<SystemMetrics>>,
    circuit: CircuitInfo,
    start_time: Instant,
    save_folder_path: String,
    stats_lock: Arc<Mutex<()>>,
}

static PROCESS_MONITOR: Lazy<Arc<Mutex<Option<ProcessMonitor>>>> = 
    Lazy::new(|| Arc::new(Mutex::new(None)));

impl ProcessMonitor {
    pub fn initialize(
        circuit_info: CircuitInfo,
        save_folder_path: String,
        initial_memory_gb: f64,
        max_workers: usize,
        total_garbling_tasks: usize,
    ) {
        let monitor = ProcessMonitor {
            threads: Arc::new(Mutex::new(HashMap::new())),
            system: Arc::new(Mutex::new(SystemMetrics {
                total_memory_gb: 0.0,
                available_memory_gb: 0.0,
                process_memory_gb: initial_memory_gb,
                memory_baseline_gb: initial_memory_gb,
                memory_peak_gb: initial_memory_gb,
                memory_rate_gb_per_hour: 0.0,
                active_workers: 0,
                max_workers,
                pending_tasks: 0,
                save_folder_size_gb: 0.0,
                disk_free_gb: 0.0,
                files_written: 0,
                memory_history: Vec::new(),
                memory_per_worker_gb: 0.0,
                total_garbling_tasks,
                completed_tasks: 0,
                failed_tasks: 0,
            })),
            circuit: circuit_info,
            start_time: Instant::now(),
            save_folder_path,
            stats_lock: Arc::new(Mutex::new(())),
        };

        *PROCESS_MONITOR.lock().unwrap() = Some(monitor);
    }

    pub fn instance() -> Option<Arc<Mutex<ProcessMonitor>>> {
        PROCESS_MONITOR.lock().unwrap().as_ref().map(|monitor| {
            // Clone the monitor to return an Arc<Mutex<ProcessMonitor>>
            Arc::new(Mutex::new(ProcessMonitor {
                threads: Arc::clone(&monitor.threads),
                system: Arc::clone(&monitor.system),
                circuit: monitor.circuit.clone(),
                start_time: monitor.start_time,
                save_folder_path: monitor.save_folder_path.clone(),
                stats_lock: Arc::clone(&monitor.stats_lock),
            }))
        })
    }

    pub fn register_thread(&self, thread_id: usize, total_gates: usize) -> Arc<AtomicUsize> {
        let gate_counter = Arc::new(AtomicUsize::new(0));
        
        let thread_metrics = ThreadMetrics {
            thread_id,
            current_gate: Arc::clone(&gate_counter),
            total_gates,
            gates_per_second: 0.0,
            memory_usage_gb: 0.0,
            status: ThreadStatus::Starting,
            xor_result: None,
            start_time: Instant::now(),
            duration: Duration::ZERO,
            speed_history: VecDeque::with_capacity(60), // Keep 1 minute of history
            error_message: None,
            input_hash160: None,
        };

        self.threads.lock().unwrap().insert(thread_id, thread_metrics);
        
        // Update active workers count
        let mut system = self.system.lock().unwrap();
        system.active_workers += 1;
        
        gate_counter
    }

    pub fn update_thread_status(&self, thread_id: usize, status: ThreadStatus) {
        if let Some(thread) = self.threads.lock().unwrap().get_mut(&thread_id) {
            thread.status = status;
            
            if status == ThreadStatus::Finished || status == ThreadStatus::Error {
                thread.duration = thread.start_time.elapsed();
                
                // Update active workers count
                let mut system = self.system.lock().unwrap();
                system.active_workers = system.active_workers.saturating_sub(1);
            }
        }
    }

    pub fn update_thread_result(&self, thread_id: usize, xor_result: S) {
        if let Some(thread) = self.threads.lock().unwrap().get_mut(&thread_id) {
            thread.xor_result = Some(xor_result);
        }
    }

    pub fn update_thread_error(&self, thread_id: usize, error_message: String) {
        if let Some(thread) = self.threads.lock().unwrap().get_mut(&thread_id) {
            thread.status = ThreadStatus::Error;
            thread.error_message = Some(error_message);
            thread.duration = thread.start_time.elapsed();
            
            // Update active workers count
            let mut system = self.system.lock().unwrap();
            system.active_workers = system.active_workers.saturating_sub(1);
        }
    }

    pub fn update_thread_hash160(&self, thread_id: usize, hash160: String) {
        if let Some(thread) = self.threads.lock().unwrap().get_mut(&thread_id) {
            thread.input_hash160 = Some(hash160);
        }
    }

    pub fn update_thread_memory(&self, thread_id: usize, memory_gb: f64) {
        if let Some(thread) = self.threads.lock().unwrap().get_mut(&thread_id) {
            thread.memory_usage_gb = memory_gb;
        }
    }

    pub fn mark_task_completed(&self) {
        let mut system = self.system.lock().unwrap();
        system.completed_tasks += 1;
    }

    pub fn mark_task_failed(&self) {
        let mut system = self.system.lock().unwrap();
        system.failed_tasks += 1;
    }

    pub fn save_folder(&self) -> String {
        self.save_folder_path.clone()
    }

    pub fn update_system_metrics(
        &self,
        total_memory_gb: f64,
        available_memory_gb: f64,
        process_memory_gb: f64,
        pending_tasks: usize,
    ) {
        let mut system = self.system.lock().unwrap();
        system.total_memory_gb = total_memory_gb;
        system.available_memory_gb = available_memory_gb;
        system.process_memory_gb = process_memory_gb;
        system.pending_tasks = pending_tasks;

        // Update memory peak
        if process_memory_gb > system.memory_peak_gb {
            system.memory_peak_gb = process_memory_gb;
        }

        // Calculate memory growth rate (GB/hour)
        let runtime_hours = self.start_time.elapsed().as_secs_f64() / 3600.0;
        if runtime_hours > 0.0 {
            system.memory_rate_gb_per_hour =
                (process_memory_gb - system.memory_baseline_gb) / runtime_hours;
        }

        system.memory_history.push((self.start_time.elapsed(), process_memory_gb));
        system.memory_per_worker_gb = if system.active_workers > 0 {
            process_memory_gb / system.active_workers as f64
        } else {
            process_memory_gb
        };
    }

    pub fn update_storage_metrics(&self) {
        if let Ok(metadata) = self.get_folder_size(&self.save_folder_path) {
            let mut system = self.system.lock().unwrap();
            system.save_folder_size_gb = metadata.0;
            system.files_written = metadata.1;
        }

        // Get actual disk free space using statvfs
        if let Ok(stat) = self.get_disk_space(&self.save_folder_path) {
            let mut system = self.system.lock().unwrap();
            system.disk_free_gb = stat;
        }
    }

    fn get_folder_size(&self, path: &str) -> Result<(f64, usize), std::io::Error> {
        let mut total_size = 0u64;
        let mut file_count = 0usize;

        if Path::new(path).exists() {
            fn visit_dir(dir: &Path, total_size: &mut u64, file_count: &mut usize) -> Result<(), std::io::Error> {
                for entry in fs::read_dir(dir)? {
                    let entry = entry?;
                    let path = entry.path();
                    if path.is_dir() {
                        visit_dir(&path, total_size, file_count)?;
                    } else {
                        *total_size += entry.metadata()?.len();
                        *file_count += 1;
                    }
                }
                Ok(())
            }

            visit_dir(Path::new(path), &mut total_size, &mut file_count)?;
        }

        Ok((total_size as f64 / 1024.0 / 1024.0 / 1024.0, file_count))
    }

    fn get_disk_space(&self, path: &str) -> Result<f64, std::io::Error> {
        // Try to read disk space from /proc/mounts and statvfs
        use std::process::Command;
        
        let output = Command::new("df")
            .arg("-BG")
            .arg(path)
            .output()?;
            
        if output.status.success() {
            let output_str = String::from_utf8_lossy(&output.stdout);
            if let Some(line) = output_str.lines().nth(1) {
                let parts: Vec<&str> = line.split_whitespace().collect();
                if parts.len() >= 4 {
                    if let Ok(available_gb) = parts[3].trim_end_matches('G').parse::<f64>() {
                        return Ok(available_gb);
                    }
                }
            }
        }
        
        // Fallback: use available memory * 10 as rough disk estimate
        let fallback = if let Some(usage) = memory_stats::memory_stats() {
            (usage.virtual_mem as f64 / 1024.0 / 1024.0 / 1024.0) * 10.0
        } else {
            5000.0 // Very conservative 5TB fallback
        };
        Ok(fallback)
    }

    pub fn get_snapshot(&self) -> MonitorSnapshot {
        let threads = self.threads.lock().unwrap();
        let system = self.system.lock().unwrap();

        // Calculate current speeds and update history
        let mut thread_snapshots = Vec::new();
        for (_, thread) in threads.iter() {
            let current_gate = thread.current_gate.load(Ordering::Relaxed);
            let elapsed = thread.start_time.elapsed().as_secs_f64();
            let speed = if elapsed > 0.0 { current_gate as f64 / elapsed } else { 0.0 };

            thread_snapshots.push(ThreadSnapshot {
                thread_id: thread.thread_id,
                current_gate,
                total_gates: thread.total_gates,
                gates_per_second: speed,
                memory_usage_gb: thread.memory_usage_gb,
                status: thread.status,
                duration: thread.start_time.elapsed(),
                progress_percent: if thread.total_gates > 0 {
                    (current_gate as f64 / thread.total_gates as f64) * 100.0
                } else {
                    0.0
                },
                error_message: thread.error_message.clone(),
                input_hash160: thread.input_hash160.clone(),
            });
        }

        // Calculate aggregate metrics
        let total_gates_processed: usize = thread_snapshots.iter()
            .map(|t| t.current_gate).sum();
        let total_speed: f64 = thread_snapshots.iter()
            .map(|t| t.gates_per_second).sum();
        let overall_progress = if self.circuit.total_gates > 0 {
            (total_gates_processed as f64 / self.circuit.total_gates as f64) * 100.0
        } else {
            0.0
        };

        MonitorSnapshot {
            threads: thread_snapshots,
            system: system.clone(),
            circuit: self.circuit.clone(),
            runtime: self.start_time.elapsed(),
            total_gates_processed,
            total_speed,
            overall_progress,
        }
    }

    pub fn save_snapshot_to_file(&self) {
        if let Ok(_guard) = self.stats_lock.lock() {
            if let Ok(snapshot) = toml::to_string_pretty(&self.get_snapshot()) {
                let path = format!("{}/global_stats.toml", self.save_folder_path);
                let _ = std::fs::write(path, snapshot);
            }
        }
    }
}

#[derive(Debug, Clone, Serialize)]
pub struct ThreadSnapshot {
    pub thread_id: usize,
    pub current_gate: usize,
    pub total_gates: usize,
    pub gates_per_second: f64,
    pub memory_usage_gb: f64,
    pub status: ThreadStatus,
    #[serde(serialize_with = "serialize_duration")]
    pub duration: Duration,
    pub progress_percent: f64,
    pub error_message: Option<String>,
    pub input_hash160: Option<String>,
}

#[derive(Debug, Clone, Serialize)]
pub struct MonitorSnapshot {
    pub threads: Vec<ThreadSnapshot>,
    pub system: SystemMetrics,
    pub circuit: CircuitInfo,
    #[serde(serialize_with = "serialize_duration")]
    pub runtime: Duration,
    pub total_gates_processed: usize,
    pub total_speed: f64,
    pub overall_progress: f64,
}

fn serialize_duration<S>(d: &Duration, serializer: S) -> Result<S::Ok, S::Error>
where
    S: serde::Serializer,
{
    serializer.serialize_f64(d.as_secs_f64())
}

fn serialize_instant<S>(i: &Instant, serializer: S) -> Result<S::Ok, S::Error>
where
    S: serde::Serializer,
{
    serializer.serialize_f64(i.elapsed().as_secs_f64())
}

fn serialize_atomic_usize<S>(a: &Arc<AtomicUsize>, serializer: S) -> Result<S::Ok, S::Error>
where
    S: serde::Serializer,
{
    serializer.serialize_u64(a.load(Ordering::Relaxed) as u64)
}

fn serialize_memory_history<S>(
    history: &Vec<(Duration, f64)>,
    serializer: S,
) -> Result<S::Ok, S::Error>
where
    S: serde::Serializer,
{
    let list: Vec<(f64, f64)> = history
        .iter()
        .map(|(d, m)| (d.as_secs_f64(), *m))
        .collect();
    list.serialize(serializer)
}
