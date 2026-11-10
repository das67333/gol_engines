//! A checkpoint is committed by replacing its manifest after its snapshot is durable.
use super::update::{Progress, Settings};
use anyhow::{Context, Result, ensure};
use gol_engines::{Pattern, PatternFormat};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::{
    fs::{self, File},
    io::Write,
    path::{Component, Path, PathBuf},
};

#[derive(Serialize, Deserialize)]
struct Manifest {
    version: u32,
    snapshot: String,
    sha256: String,
    settings: Settings,
    progress: Progress,
}

pub(super) struct Checkpoints {
    directory: PathBuf,
    // The OS releases the lock even after SIGKILL; a leftover file is not a stale lock.
    _lock: File,
    previous: Option<String>,
}

impl Checkpoints {
    pub(super) fn create(directory: &Path) -> Result<Self> {
        fs::create_dir_all(directory)?;
        let store = Self::lock(directory)?;
        ensure!(
            !directory.join("job.json").exists(),
            "A checkpoint already exists; use resume"
        );
        Ok(store)
    }

    fn lock(directory: &Path) -> Result<Self> {
        let lock = File::options()
            .create(true)
            .truncate(false)
            .write(true)
            .open(directory.join(".lock"))?;
        lock.try_lock()
            .context("Another process is using this checkpoint directory")?;
        Ok(Self {
            directory: directory.to_owned(),
            _lock: lock,
            previous: None,
        })
    }

    pub(super) fn open(directory: &Path) -> Result<(Self, Settings, Progress, Pattern)> {
        let mut store = Self::lock(directory)?;
        let manifest: Manifest = serde_json::from_slice(&fs::read(directory.join("job.json"))?)?;
        ensure!(
            manifest.version == 1,
            "Unsupported checkpoint version {}",
            manifest.version
        );
        let mut components = Path::new(&manifest.snapshot).components();
        ensure!(
            matches!(components.next(), Some(Component::Normal(_))) && components.next().is_none(),
            "Invalid snapshot filename"
        );
        manifest.settings.validate()?;
        manifest.progress.validate()?;
        let data = fs::read(directory.join(&manifest.snapshot))?;
        ensure!(
            format!("{:x}", Sha256::digest(&data)) == manifest.sha256,
            "Checkpoint checksum mismatch"
        );
        let pattern = Pattern::from_format(PatternFormat::CompressedMacrocell, &data)?;
        store.previous = Some(manifest.snapshot);
        Ok((store, manifest.settings, manifest.progress, pattern))
    }

    pub(super) fn save(&mut self, settings: &Settings, progress: &Progress, pattern: &Pattern) -> Result<()> {
        let data = pattern.to_format(PatternFormat::CompressedMacrocell)?;
        let mut snapshot = tempfile::Builder::new()
            .prefix("checkpoint-")
            .suffix(".mc.gz")
            .tempfile_in(&self.directory)?;
        snapshot.write_all(&data)?;
        snapshot.as_file().sync_all()?;
        let (_, path) = snapshot.keep()?;
        sync_directory(&self.directory)?;
        let snapshot = path
            .file_name()
            .unwrap()
            .to_str()
            .context("Non-UTF8 snapshot filename")?
            .to_owned();
        let manifest = Manifest {
            version: 1,
            snapshot: snapshot.clone(),
            sha256: format!("{:x}", Sha256::digest(&data)),
            settings: settings.clone(),
            progress: progress.clone(),
        };
        atomic_write(&self.directory.join("job.json"), &serde_json::to_vec_pretty(&manifest)?)?;
        if let Some(previous) = self.previous.replace(snapshot) {
            // Failure to remove an obsolete snapshot must not invalidate the new checkpoint.
            if let Err(error) = fs::remove_file(self.directory.join(previous)) {
                eprintln!("Could not remove obsolete checkpoint: {error}");
            }
        }
        Ok(())
    }
}

pub(super) fn atomic_write(path: &Path, data: &[u8]) -> Result<()> {
    let directory = path
        .parent()
        .filter(|p| !p.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    let mut file = tempfile::NamedTempFile::new_in(directory)?;
    file.write_all(data)?;
    file.as_file().sync_all()?;
    file.persist(path)?;
    sync_directory(directory)
}

fn sync_directory(path: &Path) -> Result<()> {
    #[cfg(unix)]
    File::open(path)?.sync_all()?;
    #[cfg(not(unix))]
    let _ = path;
    Ok(())
}

#[cfg(test)]
mod tests;
