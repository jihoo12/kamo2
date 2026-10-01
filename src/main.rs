#![forbid(unsafe_code)]
use kamo::{CheckedProgram, Options};
use std::{env, fs, io::Read, process::ExitCode};

fn run() -> std::result::Result<(), String> {
    let mut args = env::args().skip(1).collect::<Vec<_>>();
    if args.is_empty() || args[0] == "--help" || args[0] == "-h" {
        println!(
            "Kamo — experimental Cartesian cubical kernel\n\nUsage:\n  kamo check FILE [options]\n  kamo normalize FILE NAME [options]\n  kamo check-surface FILE [options]\n  kamo normalize-surface FILE NAME [options]\n\nDefault limits per declaration/evaluation: 1,000,000 steps; 250,000 arena nodes.\nFor a hard process limit, use scripts/with-limits.sh (512 MiB, 30 seconds)."
        );
        return Ok(());
    }
    let mut options = Options::default();
    let mut stats = false;
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--max-nodes" => {
                if i + 1 >= args.len() {
                    return Err("--max-nodes requires a positive integer".into());
                }
                options.max_nodes = args[i + 1].parse().map_err(|_| "invalid node budget")?;
                if options.max_nodes == 0 {
                    return Err("node budget must be positive".into());
                }
                args.drain(i..=i + 1);
            }
            "--fuel" => {
                if i + 1 >= args.len() {
                    return Err("--fuel requires a positive integer".into());
                }
                options.fuel = args[i + 1].parse().map_err(|_| "invalid fuel")?;
                if options.fuel == 0 {
                    return Err("fuel must be positive".into());
                }
                args.drain(i..=i + 1);
            }
            "--reference" => {
                options.optimized = false;
                args.remove(i);
            }
            "--stats" => {
                stats = true;
                args.remove(i);
            }
            _ => i += 1,
        }
    }
    let valid = matches!(
        args.first().map(String::as_str),
        Some("check" | "check-surface")
    ) && args.len() == 2
        || matches!(
            args.first().map(String::as_str),
            Some("normalize" | "normalize-surface")
        ) && args.len() == 3;
    if !valid {
        return Err("usage: kamo check FILE | kamo normalize FILE NAME (see --help)".into());
    }
    let file = &args[1];
    let surface = args[0].ends_with("surface");
    let program = if surface {
        CheckedProgram::check_surface_file_with(file, options)
            .map_err(|e| format!("{file}: {e}"))?
    } else {
        let input = fs::File::open(file).map_err(|e| format!("{file}: {e}"))?;
        let mut source = String::new();
        input
            .take(kamo::MAX_SOURCE_BYTES as u64 + 1)
            .read_to_string(&mut source)
            .map_err(|e| format!("{file}: {e}"))?;
        CheckedProgram::check_with(&source, options).map_err(|e| e.render(file, &source))?
    };
    if args[0] == "check" || args[0] == "check-surface" {
        println!("checked {} declarations", program.names().count());
    } else {
        let result = program
            .normalize_with(&args[2], options)
            .map_err(|e| format!("{file}: {e}"))?;
        println!("{}", result.text);
        if stats {
            eprintln!("{:?}", result.statistics);
        }
    }
    Ok(())
}
fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("{e}");
            ExitCode::FAILURE
        }
    }
}
