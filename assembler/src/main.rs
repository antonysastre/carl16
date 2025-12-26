use c16::assemble;
use std::process;

fn main() {
    let args: Vec<String> = std::env::args().collect();

    if args.len() != 3 {
        eprintln!("Usage: {} <input.asm> <output.c16>", args[0]);
        process::exit(1);
    }

    if let Err(e) = assemble(&args[1], &args[2]) {
        eprintln!("Error: {}", e);
        process::exit(1);
    }
}
