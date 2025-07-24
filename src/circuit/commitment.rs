use crate::{EvaluatedWire, S};

/// Simple commit, to be replaced in the future
pub type Commit = Vec<u8>;

/// Simple commit, to be replaced in the future
pub fn commit(wires: impl Iterator<Item = EvaluatedWire>) -> Commit {
    let mut hasher = blake3::Hasher::default();

    wires.for_each(|evaluated| {
        hasher.update(&evaluated.active_label.0);
        hasher.update(&[evaluated.value() as u8]);
    });

    hasher.finalize().as_bytes().to_vec()
}

/// Commit to pairs of garbled wire labels.
pub fn commit_labels(labels: impl Iterator<Item = (S, S)>) -> Commit {
    let mut hasher = blake3::Hasher::default();
    for (l0, l1) in labels {
        hasher.update(&l0.0);
        hasher.update(&l1.0);
    }
    hasher.finalize().as_bytes().to_vec()
}
