use c16::assemble;
use std::path::Path;
use std::process;

fn main() {
    let args: Vec<String> = std::env::args().collect();

    if args.len() < 2 || args.len() > 3 {
        eprintln!("Usage: {} <input.asm> [output.c16]", args[0]);
        process::exit(1);
    }

    let input_file = &args[1];
    let output_file = if args.len() == 3 {
        args[2].clone()
    } else {
        // Generate output filename from input filename with .c16 extension
        let input_path = Path::new(input_file);
        let stem = input_path.file_stem().unwrap_or_default();
        format!("{}.c16", stem.to_string_lossy())
    };

    if let Err(e) = assemble(input_file, &output_file) {
        eprintln!("Error: {}", e);
        process::exit(1);
    }
}
