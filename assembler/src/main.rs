// use std::error::Error;
use std::env;
use std::fs::read_to_string;

fn main() {
    let args: Vec<String> = env::args().collect();
    println!(r#"Arguments: {:?}"#, args);

    if let Some(arg) = args.get(1) {
        println!("Processing file: {}", arg);
        match read_to_string(&args[1]) {
            Ok(content) => process_file(content),
            Err(e) => eprintln!("Error reading file: {}", e),
        }
    } else {
        eprintln!("No file provided. Usage: cargo run <filename>");
        return;
    }
}

fn process_file(content: String) {
    for line in content.lines() {
        match parse_line(line) {
            Ok(parsed) => println!("Line {}: {}", line, parsed),
            Err(e) => eprintln!("Error parsing line {}: {}", line, e),
        }
    }
}

fn parse_line(line: &str) -> Result<String, String> {
    if line.is_empty() {
        Err("Empty line".to_string())
    } else if let Some(captures) = line.strip_prefix('@').and_then(|s| s.parse::<u16>().ok()) {
        // If the line starts with '@' followed by a number, return its binary representation
        Ok(format!("{0:015b}", captures))
    } else {
        Ok(format!("{0:015b}", 8))
    }
}
