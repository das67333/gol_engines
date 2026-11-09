use super::*;
use serde_json::json;

fn fixture() -> (Settings, Progress, Pattern) {
    let settings = serde_json::from_value(json!({
        "engine": "streamlife", "topology": "torus", "mem_limit_gib": 1,
        "workers": 2, "output": "/tmp/result.mc", "population": false
    }))
    .unwrap();
    let progress = serde_json::from_value(json!({
        "generation": "0", "target": "64", "offset_x": "-12345678901234567890",
        "offset_y": "98765432109876543210", "step_log2": 3, "elapsed_seconds": 12.5
    }))
    .unwrap();
    (settings, progress, Pattern::random(6, Some(42)).unwrap())
}

#[test]
fn checkpoints_preserve_pattern_and_metadata_and_exclude_another_writer() {
    let directory = tempfile::tempdir().unwrap();
    let (settings, progress, pattern) = fixture();
    let mut store = Checkpoints::create(directory.path()).unwrap();
    store.save(&settings, &progress, &pattern).unwrap();
    assert!(Checkpoints::open(directory.path()).is_err());
    drop(store);
    let (mut store, saved_settings, saved_progress, saved_pattern) = Checkpoints::open(directory.path()).unwrap();
    assert_eq!(
        serde_json::to_value(&progress).unwrap(),
        serde_json::to_value(saved_progress).unwrap()
    );
    assert_eq!(
        serde_json::to_value(&settings).unwrap(),
        serde_json::to_value(saved_settings).unwrap()
    );
    assert_eq!(pattern.hash(), saved_pattern.hash());
    let mut empty = Pattern::new(None);
    empty.expand(16);
    store.save(&settings, &progress, &empty).unwrap();
    drop(store);
    let (_, _, _, restored) = Checkpoints::open(directory.path()).unwrap();
    assert_eq!(restored.get_size_log2(), empty.get_size_log2());
    assert_eq!(restored.hash(), empty.hash());
}

#[test]
fn uncommitted_snapshot_does_not_replace_the_last_checkpoint() {
    let directory = tempfile::tempdir().unwrap();
    let (settings, progress, pattern) = fixture();
    let mut store = Checkpoints::create(directory.path()).unwrap();
    store.save(&settings, &progress, &pattern).unwrap();
    fs::write(
        directory.path().join("checkpoint-interrupted.mc.gz"),
        b"incomplete write",
    )
    .unwrap();
    drop(store);
    let (_, _, _, restored) = Checkpoints::open(directory.path()).unwrap();
    assert_eq!(restored.hash(), pattern.hash());
}

#[test]
fn damaged_checkpoints_and_paths_outside_the_job_are_rejected() {
    let directory = tempfile::tempdir().unwrap();
    let (settings, progress, pattern) = fixture();
    let mut store = Checkpoints::create(directory.path()).unwrap();
    store.save(&settings, &progress, &pattern).unwrap();
    let manifest_path = directory.path().join("job.json");
    let mut manifest: serde_json::Value = serde_json::from_slice(&fs::read(&manifest_path).unwrap()).unwrap();
    fs::write(
        directory.path().join(manifest["snapshot"].as_str().unwrap()),
        b"damaged",
    )
    .unwrap();
    drop(store);
    assert!(
        Checkpoints::open(directory.path())
            .err()
            .unwrap()
            .to_string()
            .contains("checksum")
    );
    manifest["snapshot"] = json!("../elsewhere.mc.gz");
    fs::write(manifest_path, serde_json::to_vec(&manifest).unwrap()).unwrap();
    assert!(
        Checkpoints::open(directory.path())
            .err()
            .unwrap()
            .to_string()
            .contains("filename")
    );
}
