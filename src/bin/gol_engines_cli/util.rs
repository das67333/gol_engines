use chrono::Local;
use gol_engines::Pattern;
use num_format::{CustomFormat, Grouping, ToFormattedString};

pub(super) fn print_population(pattern: &Pattern) {
    let population = pattern.population();
    let fmt = CustomFormat::builder()
        .grouping(Grouping::Standard)
        .separator("_")
        .build()
        .unwrap();
    println!("Population: {}", population.to_formatted_string(&fmt));
}

pub(super) fn local_time() -> String {
    Local::now().format("%Y-%m-%dT%H:%M:%S%.3f").to_string()
}
