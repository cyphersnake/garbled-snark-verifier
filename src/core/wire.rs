use crate::core::s::S;
use once_cell::sync::Lazy;
use std::sync::atomic::{AtomicU64, Ordering};

static WIRE_COUNTER: Lazy<AtomicU64> = Lazy::new(|| AtomicU64::new(0));

#[derive(Clone, Debug)]
pub struct Wire {
    pub id: u64,
    pub label0: Option<S>,
    pub label1: Option<S>,
    pub value: Option<bool>,
    pub label: Option<S>,
}

impl Default for Wire {
    fn default() -> Self {
        Self::new()
    }
}

impl Wire {
    pub fn new() -> Self {
        // A strictly monotonic sequence is sufficient for assigning
        // unique IDs, so relaxed ordering is enough here.
        let id = WIRE_COUNTER.fetch_add(1, Ordering::Relaxed);
        Self {
            id,
            label0: None,
            label1: None,
            value: None,
            label: None,
        }
    }

    pub fn select(&self, selector: bool) -> S {
        if selector {
            self.label1.unwrap()
        } else {
            self.label0.unwrap()
        }
    }

    pub fn select_hash(&self, selector: bool) -> S {
        if selector {
            self.label1.unwrap().hash()
        } else {
            self.label0.unwrap().hash()
        }
    }

    pub fn get_value(&self) -> bool {
        assert!(self.value.is_some());
        self.value.unwrap()
    }

    pub fn get_label(&self) -> S {
        assert!(self.value.is_some());
        self.label.unwrap()
    }

    pub fn set_labels(&mut self) {
        todo!()
    }

    pub fn set(&mut self, bit: bool) {
        assert!(self.value.is_none());
        self.value = Some(bit);
    }

    pub fn set2(&mut self, bit: bool, label: S) {
        assert!(self.value.is_none());
        self.value = Some(bit);
        self.label = Some(label);
    }
}
