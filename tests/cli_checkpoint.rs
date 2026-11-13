#![cfg(feature = "cli_deps")]
use gol_engines::{Pattern, PatternFormat};
use serde_json::Value;
use std::{fs, path::Path, process::Command};

fn cli(args: &[&str]) -> Command {
    let mut command = Command::new(env!("CARGO_BIN_EXE_gol_engines_cli"));
    command.args(args);
    command
}

fn read_manifest(directory: &Path) -> Value {
    serde_json::from_slice(&fs::read(directory.join("job.json")).unwrap()).unwrap()
}

#[test]
fn resume_uses_saved_progress_and_settings() {
    let directory = tempfile::tempdir().unwrap();
    let root = directory.path();
    let pattern = Pattern::from_format(PatternFormat::RLE, b"x = 32, y = 32, rule = B3/S23\nbo$2bo$3o!").unwrap();
    pattern.to_file(root.join("input.mc")).unwrap();
    for engine in ["hashlife", "streamlife"] {
        let job = root.join(engine);
        let output = root.join(format!("{engine}.mc"));
        let result = cli(&[
            "update",
            "input.mc",
            "--engine",
            engine,
            "--mem-limit-gib",
            "1",
            "--gens-log2",
            "3",
            "--checkpoint-dir",
            job.to_str().unwrap(),
            "--output",
            output.to_str().unwrap(),
        ])
        .current_dir(root)
        .output()
        .unwrap();
        assert!(result.status.success(), "{}", String::from_utf8_lossy(&result.stderr));
        // A valid mid-run manifest: eight generations completed out of 32.
        let mut manifest = read_manifest(&job);
        manifest["progress"]["target"] = Value::String("32".into());
        // Manifests written before offsets were removed remain readable.
        manifest["progress"]["offset_x"] = Value::String("-12345678901234567890".into());
        manifest["progress"]["offset_y"] = Value::String("98765432109876543210".into());
        fs::write(job.join("job.json"), serde_json::to_vec(&manifest).unwrap()).unwrap();
        let result = cli(&["resume", job.to_str().unwrap(), "--workers", "2"])
            .current_dir(root.parent().unwrap())
            .output()
            .unwrap();
        assert!(result.status.success(), "{}", String::from_utf8_lossy(&result.stderr));
        let reference = root.join(format!("{engine}-reference"));
        assert!(
            cli(&[
                "update",
                "input.mc",
                "--engine",
                engine,
                "--mem-limit-gib",
                "1",
                "--workers",
                "2",
                "--gens-log2",
                "5",
                "--step-log2",
                "3",
                "--checkpoint-dir",
                reference.to_str().unwrap(),
                "--output",
                "reference.mc"
            ])
            .current_dir(root)
            .output()
            .unwrap()
            .status
            .success()
        );
        assert_eq!(
            Pattern::from_file(output).unwrap().hash(),
            Pattern::from_file(root.join("reference.mc")).unwrap().hash()
        );
        let resumed = read_manifest(&job);
        let straight = read_manifest(&reference);
        for field in ["generation", "target"] {
            assert_eq!(resumed["progress"][field], straight["progress"][field], "{field}");
        }
    }
}

#[cfg(unix)]
#[test]
fn nohup_ignores_hangup_and_sigint_preserves_the_checkpoint() {
    use std::{
        io::{BufRead, BufReader},
        os::unix::process::CommandExt,
        process::Stdio,
        time::{Duration, Instant},
    };
    for (generations, signal, expected_status) in [("3", libc::SIGHUP, 0), ("30", libc::SIGINT, 130)] {
        let directory = tempfile::tempdir().unwrap();
        let root = directory.path();
        let pattern = Pattern::random(10, Some(42)).unwrap();
        pattern.to_file(root.join("input.mc")).unwrap();
        let mut command = cli(&[
            "update",
            "input.mc",
            "--engine",
            "streamlife",
            "--mem-limit-gib",
            "1",
            "--workers",
            "4",
            "--gens-log2",
            generations,
            "--checkpoint-dir",
            "job",
            "--output",
            "output.mc",
        ]);
        // Match nohup's inherited disposition; the child must still complete after SIGHUP.
        unsafe {
            command.pre_exec(|| {
                if libc::signal(libc::SIGHUP, libc::SIG_IGN) == libc::SIG_ERR {
                    return Err(std::io::Error::last_os_error());
                }
                Ok(())
            });
        }
        let mut child = command.current_dir(root).stdout(Stdio::piped()).spawn().unwrap();
        let mut output = BufReader::new(child.stdout.take().unwrap());
        let mut line = String::new();
        loop {
            assert!(
                output.read_line(&mut line).unwrap() > 0,
                "CLI exited before starting the update"
            );
            if line.contains("Initialized and loaded") {
                break;
            }
            line.clear();
        }
        let reader = std::thread::spawn(move || std::io::copy(&mut output, &mut std::io::sink()).unwrap());
        std::thread::sleep(Duration::from_millis(10));
        assert_eq!(unsafe { libc::kill(child.id() as i32, signal) }, 0);
        let deadline = Instant::now() + Duration::from_secs(30);
        let status = loop {
            if let Some(status) = child.try_wait().unwrap() {
                break status;
            }
            if Instant::now() > deadline {
                child.kill().unwrap();
                child.wait().unwrap();
                panic!("CLI failed to terminate");
            }
            std::thread::sleep(Duration::from_millis(10));
        };
        reader.join().unwrap();
        assert_eq!(status.code(), Some(expected_status));
        let manifest = read_manifest(&root.join("job"));
        if expected_status == 0 {
            assert_eq!(manifest["progress"]["generation"], "8");
            assert!(root.join("output.mc").exists());
        } else {
            assert_eq!(manifest["progress"]["generation"], "0");
            let snapshot = root.join("job").join(manifest["snapshot"].as_str().unwrap());
            assert_eq!(Pattern::from_file(snapshot).unwrap().hash(), pattern.hash());
            assert!(!root.join("output.mc").exists());
        }
    }
}
