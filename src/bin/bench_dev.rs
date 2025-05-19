use gol_engines::*;

fn detect_format(filename: &str) -> Option<PatternFormat> {
    if filename.ends_with(".rle") {
        Some(PatternFormat::RLE)
    } else if filename.ends_with(".mc") {
        Some(PatternFormat::Macrocell)
    } else if filename.ends_with(".mc.gz") {
        Some(PatternFormat::CompressedMacrocell)
    } else {
        None
    }
}

fn main() {
    // updating all patterns in res/very_large_patterns
    let paths = std::fs::read_dir("res/very_large_patterns").unwrap();
    let mut engine = HashLifeEngineSync::new(16 << 10);
    for (i, path) in paths.enumerate() {
        let path = path.unwrap().path();
        let name = path.file_name().unwrap().to_str().unwrap();
        println!("i={i}\t{name}");

        let format = detect_format(name).unwrap();
        let data = std::fs::read(path).unwrap();
        let pattern = Pattern::from_format(format, &data).unwrap();

        for gens_log2 in 5..=5 {
            engine.load_pattern(&pattern, Topology::Unbounded).unwrap();

            let timer = std::time::Instant::now();
            engine.update(gens_log2).unwrap();
            let elapsed_update = timer.elapsed();
            println!("{} -> {:?}", gens_log2, elapsed_update.as_secs_f64());
            if elapsed_update.as_secs_f64() > 60.0 {
                break;
            }
        }
    }
}
