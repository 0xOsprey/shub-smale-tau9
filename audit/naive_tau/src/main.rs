mod census;
mod poly;
mod slp;

use census::*;
use poly::*;
use rayon::prelude::*;
use slp::*;
use std::collections::{HashMap, HashSet};
use std::fs::File;
use std::io::{self, BufRead, BufReader, Write};
use std::sync::Mutex;
use std::time::Instant;

// ------------------------------------------------------------------------------------------
// Deterministic PRNG (SplitMix64) for random-canonical
// ------------------------------------------------------------------------------------------
struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self {
        Rng(seed.wrapping_add(0x9e3779b97f4a7c15))
    }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e3779b97f4a7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
        z ^ (z >> 31)
    }
    fn gen_range(&mut self, n: usize) -> usize {
        (self.next_u64() as usize) % n
    }
}

fn gate_key(t: &Gate) -> u32 {
    t.op as u32 * 1024 + t.i as u32 * 32 + t.j as u32
}

/// Generate one random canonical SLP of length `t_gates` using a constrained random walk
/// with exact polynomial arithmetic, verified by `is_canonical`.
fn sample_one_canonical(t_gates: usize, rng: &mut Rng) -> Vec<Gate> {
    if t_gates == 0 {
        return vec![];
    }
    loop {
        let mut wires: Vec<Poly> = Vec::with_capacity(t_gates + 2);
        wires.push(Poly::one());
        wires.push(Poly::x());
        let mut gates: Vec<Gate> = Vec::with_capacity(t_gates);
        let mut used_mask: u64 = 0; // bit m set if wire m (m>=2) has been used as an operand
        let mut ok = true;

        // Bias mode per attempt for shape diversity:
        // 0 = uniform among all valid continuations
        // 1 = prefer independent gates (not using previous wire) -> bushier DAGs
        // 2 = prefer chaining (using previous wire) -> deeper chains
        let mode = rng.gen_range(3);

        for k in 0..t_gates {
            let nw = k + 2;
            let rem_after = t_gates - 1 - k; // number of gates after gate k
            // All currently existing gate wires are 2..nw; bitmask of those is ((1<<(nw-2))-1) << 2.
            let existing_gate_bits: u64 = if nw > 2 { ((1u64 << (nw - 2)) - 1) << 2 } else { 0 };
            let unused_now = existing_gate_bits & !used_mask;

            let mut cands: Vec<(Gate, Poly, u64)> = Vec::new();
            let mut preferred: Vec<usize> = Vec::new();

            for op in [ADD, SUB, MUL] {
                for i in 0..nw {
                    let j_start = if op == SUB { i + 1 } else { i };
                    for j in j_start..nw {
                        let g = Gate { op, i: i as u8, j: j as u8 };
                        // Check (lex) for 1 <= k <= t_gates - 2
                        if k >= 1 && k + 2 <= t_gates {
                            let prev_wire = (k + 1) as u8;
                            if g.i != prev_wire && g.j != prev_wire && gate_key(&gates[k - 1]) > gate_key(&g) {
                                continue;
                            }
                        }
                        // Check (used) feasibility
                        let mut consumed = 0u64;
                        if i >= 2 {
                            consumed |= 1u64 << i;
                        }
                        if j >= 2 {
                            consumed |= 1u64 << j;
                        }
                        let unused_after_old = unused_now & !consumed;
                        let u_old = unused_after_old.count_ones() as usize;
                        if rem_after == 0 {
                            // Last gate must leave zero unused previous gates
                            if u_old != 0 {
                                continue;
                            }
                        } else {
                            // New wire k+2 will also be unused right after gate k,
                            // so total unused after gate k is u_old + 1.
                            // Remaining rem_after gates can consume at most rem_after + 1
                            // existing unused wires (since they also create rem_after - 1 new ones
                            // and have 2 * rem_after operand slots).
                            if u_old + 1 > rem_after + 1 {
                                continue;
                            }
                        }

                        // Exact polynomial check: (nonzero) and (nodup)
                        let c = apply(op, &wires[i], &wires[j]);
                        if c.is_zero() {
                            continue;
                        }
                        let nc = c.neg();
                        let mut dup = false;
                        for w in &wires {
                            if *w == c || *w == nc {
                                dup = true;
                                break;
                            }
                        }
                        if dup {
                            continue;
                        }

                        let idx = cands.len();
                        let uses_prev = k >= 1 && (i == k + 1 || j == k + 1);
                        if (mode == 1 && !uses_prev) || (mode == 2 && uses_prev) {
                            preferred.push(idx);
                        }
                        cands.push((g, c, consumed));
                    }
                }
            }

            if cands.is_empty() {
                ok = false;
                break;
            }
            let pick = if !preferred.is_empty() && rng.gen_range(4) != 0 {
                preferred[rng.gen_range(preferred.len())]
            } else {
                rng.gen_range(cands.len())
            };
            let (g, c, consumed) = cands.swap_remove(pick);
            used_mask |= consumed;
            gates.push(g);
            wires.push(c);
        }

        if ok {
            assert_eq!(is_canonical(&gates), Ok(()), "sampler produced non-canonical SLP!");
            return gates;
        }
    }
}

fn cmd_random_canonical(args: &[String]) {
    if args.len() < 3 {
        eprintln!("Usage: naive_tau random-canonical T N SEED");
        std::process::exit(2);
    }
    let t: usize = args[0].parse().expect("bad T");
    let n: usize = args[1].parse().expect("bad N");
    let seed: u64 = args[2].parse().expect("bad SEED");
    let mut rng = Rng::new(seed);
    let stdout = io::stdout();
    let mut out = io::BufWriter::new(stdout.lock());
    for _ in 0..n {
        let g = sample_one_canonical(t, &mut rng);
        writeln!(out, "{}", format_compact(&g)).unwrap();
    }
    out.flush().unwrap();
}

fn cmd_is_canonical(args: &[String]) {
    if args.is_empty() {
        eprintln!("Usage: naive_tau is-canonical FILE|--stdin");
        std::process::exit(2);
    }
    let reader: Box<dyn BufRead> = if args[0] == "--stdin" || args[0] == "-" {
        Box::new(BufReader::new(io::stdin()))
    } else {
        Box::new(BufReader::new(File::open(&args[0]).expect("cannot open input file")))
    };
    let stdout = io::stdout();
    let mut out = io::BufWriter::new(stdout.lock());
    let mut total = 0u64;
    let mut ok_cnt = 0u64;
    let mut reasons: HashMap<&'static str, u64> = HashMap::new();
    for line_res in reader.lines() {
        let line = line_res.expect("read error");
        let s = line.trim();
        if s.is_empty() {
            continue;
        }
        total += 1;
        match parse_compact(s) {
            Err(_) => {
                *reasons.entry("parse").or_insert(0) += 1;
            }
            Ok(g) => match is_canonical(&g) {
                Ok(()) => {
                    ok_cnt += 1;
                    writeln!(out, "{}", s).unwrap();
                }
                Err(why) => {
                    *reasons.entry(why).or_insert(0) += 1;
                }
            },
        }
    }
    out.flush().unwrap();
    let mut rvec: Vec<(&str, u64)> = reasons.into_iter().collect();
    rvec.sort_by_key(|x| x.0);
    eprintln!(
        "is-canonical: total={} canonical={} rejected={} reasons={:?}",
        total,
        ok_cnt,
        total - ok_cnt,
        rvec
    );
}

// ------------------------------------------------------------------------------------------
// eval-dump: streaming exact evaluation and cross-check against New±(T)
// ------------------------------------------------------------------------------------------
const NSH_DUMP: usize = 256;
#[inline]
fn dump_shard(h: u64) -> usize {
    ((h >> 40) as usize) & (NSH_DUMP - 1)
}

fn cmd_eval_dump(args: &[String]) {
    let mut file_arg: Option<String> = None;
    let mut t_arg: Option<usize> = None;
    let mut use_stdin = false;
    let mut buckets: Option<usize> = None;
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--stdin" => {
                use_stdin = true;
                i += 1;
            }
            "--buckets" => {
                buckets = Some(args[i + 1].parse().expect("bad --buckets"));
                i += 2;
            }
            a => {
                if file_arg.is_none() && !use_stdin {
                    if a == "-" {
                        use_stdin = true;
                    } else {
                        file_arg = Some(a.to_string());
                    }
                } else if t_arg.is_none() {
                    t_arg = Some(a.parse().expect("bad T"));
                } else {
                    eprintln!("unexpected arg: {}", a);
                    std::process::exit(2);
                }
                i += 1;
            }
        }
    }
    let t = t_arg.expect("Usage: naive_tau eval-dump FILE T [--stdin] [--buckets B]");
    if t == 0 {
        eprintln!("T must be >= 1");
        std::process::exit(2);
    }
    let bn = buckets.unwrap_or(if t >= 7 { 4 } else { 1 }).max(1);

    let t0 = Instant::now();
    eprintln!("[eval-dump] building reference census up to tau={}...", t - 1);
    let c = build_census(t - 1);
    eprintln!(
        "[eval-dump] reference census tau<={} built in {:.1}s ({} interned polys, |L_{}|={})",
        t - 1,
        t0.elapsed().as_secs_f64(),
        c.it.len(),
        t - 1,
        c.levels[t - 1].len()
    );

    // Sharded sets for dump classes:
    // - dump_lo: canonical reps with min(tau(f), tau(-f)) < T (already in c.it, incl. 1, x)
    // - dump_hi: canonical reps NOT in c.it (and != 0); value = matched in New±(T)
    let dump_lo: Vec<Mutex<HashSet<HP, IdBuild>>> = (0..NSH_DUMP).map(|_| Mutex::new(HashSet::default())).collect();
    let dump_hi: Vec<Mutex<HashMap<HP, bool, IdBuild>>> =
        (0..NSH_DUMP).map(|_| Mutex::new(HashMap::default())).collect();
    let dump_has_zero = std::sync::atomic::AtomicBool::new(false);
    let mut lines_read = 0u64;

    let mut reader: Box<dyn BufRead> = if use_stdin {
        Box::new(BufReader::new(io::stdin()))
    } else {
        let path = file_arg.as_deref().expect("missing FILE");
        Box::new(BufReader::new(File::open(path).expect("cannot open dump file")))
    };

    let t_read = Instant::now();
    let mut chunk: Vec<String> = Vec::with_capacity(65536);
    let process_chunk = |lines: &[String]| {
        lines.par_chunks(1024).for_each(|sub| {
            let mut loc_lo: Vec<HP> = Vec::new();
            let mut loc_hi: Vec<HP> = Vec::new();
            let mut saw_zero = false;
            for line in sub {
                let g = parse_compact(line).unwrap_or_else(|e| panic!("parse error on {:?}: {}", line, e));
                let p = eval_last(&g).unwrap_or_else(|e| panic!("eval error on {:?}: {}", line, e));
                if p.is_zero() {
                    saw_zero = true;
                    continue;
                }
                let (rep, _) = p.canon();
                let h = rep.phash();
                let nrep = rep.neg();
                let in_lo = c.it.get(&rep, h).is_some() || c.it.get(&nrep, rep.hash_with(true)).is_some();
                if in_lo {
                    loc_lo.push(HP { h, p: rep });
                } else {
                    loc_hi.push(HP { h, p: rep });
                }
            }
            if saw_zero {
                dump_has_zero.store(true, std::sync::atomic::Ordering::Relaxed);
            }
            if !loc_lo.is_empty() {
                let mut by: Vec<Vec<HP>> = (0..NSH_DUMP).map(|_| Vec::new()).collect();
                for hp in loc_lo {
                    by[dump_shard(hp.h)].push(hp);
                }
                for (s, v) in by.into_iter().enumerate() {
                    if !v.is_empty() {
                        let mut g = dump_lo[s].lock().unwrap();
                        for hp in v {
                            g.insert(hp);
                        }
                    }
                }
            }
            if !loc_hi.is_empty() {
                let mut by: Vec<Vec<HP>> = (0..NSH_DUMP).map(|_| Vec::new()).collect();
                for hp in loc_hi {
                    by[dump_shard(hp.h)].push(hp);
                }
                for (s, v) in by.into_iter().enumerate() {
                    if !v.is_empty() {
                        let mut g = dump_hi[s].lock().unwrap();
                        for hp in v {
                            g.entry(hp).or_insert(false);
                        }
                    }
                }
            }
        });
    };

    let mut line_buf = String::new();
    loop {
        line_buf.clear();
        let n = reader.read_line(&mut line_buf).expect("read error");
        if n == 0 {
            break;
        }
        let trimmed = line_buf.trim();
        if trimmed.is_empty() {
            continue;
        }
        lines_read += 1;
        chunk.push(trimmed.to_string());
        if chunk.len() >= 65536 {
            process_chunk(&chunk);
            chunk.clear();
        }
    }
    if !chunk.is_empty() {
        process_chunk(&chunk);
        chunk.clear();
    }

    let lo_cnt: u64 = dump_lo.iter().map(|m| m.lock().unwrap().len() as u64).sum();
    let hi_cnt: u64 = dump_hi.iter().map(|m| m.lock().unwrap().len() as u64).sum();
    let zero_cnt: u64 = if dump_has_zero.load(std::sync::atomic::Ordering::Relaxed) { 1 } else { 0 };
    let dump_total_pm = zero_cnt + lo_cnt + hi_cnt;
    eprintln!(
        "[eval-dump] evaluated {} lines in {:.1}s -> |DumpSet±|={} (zero={}, tau<T={}, tau>=T={})",
        lines_read,
        t_read.elapsed().as_secs_f64(),
        dump_total_pm,
        zero_cnt,
        lo_cnt,
        hi_cnt
    );

    // Now enumerate New±(T) via top_pass in bn buckets and cross-check against dump_hi
    let mut new_pm_total = 0u64;
    let missing_count = std::sync::atomic::AtomicU64::new(0);
    let missing_examples: Mutex<Vec<Poly>> = Mutex::new(Vec::new());

    for b in 0..bn {
        let tp = Instant::now();
        let out = top_pass(&c.it, &c.levels[t - 1], b, bn, false);
        let lo_check = |p: &Poly, h: u64| c.it.get(p, h).is_some();
        let bucket_pm: u64 = out
            .acc
            .shards
            .par_iter()
            .map(|m| {
                let g = m.lock().unwrap();
                let mut pm = 0u64;
                for (k, _) in g.iter() {
                    let nf = k.p.neg();
                    if lo_check(&k.p, k.h) || lo_check(&nf, k.p.hash_with(true)) {
                        continue;
                    }
                    pm += 1;
                    let mut dg = dump_hi[dump_shard(k.h)].lock().unwrap();
                    if let Some(matched) = dg.get_mut(k) {
                        *matched = true;
                    } else {
                        drop(dg);
                        missing_count.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                        let mut ex = missing_examples.lock().unwrap();
                        if ex.len() < 20 {
                            ex.push(k.p.clone());
                        }
                    }
                }
                pm
            })
            .sum();
        new_pm_total += bucket_pm;
        eprintln!("[eval-dump] top pass {}/{}: New±({}) bucket={} ({:.1}s)", b + 1, bn, t, bucket_pm, tp.elapsed().as_secs_f64());
    }

    // Check for any dump_hi entries NOT matched in New±(T)
    let mut extra_count = 0u64;
    let mut extra_examples: Vec<Poly> = Vec::new();
    for sh in &dump_hi {
        let g = sh.lock().unwrap();
        for (k, &matched) in g.iter() {
            if !matched {
                extra_count += 1;
                if extra_examples.len() < 20 {
                    extra_examples.push(k.p.clone());
                }
            }
        }
    }

    let missing = missing_count.load(std::sync::atomic::Ordering::Relaxed);
    println!("eval_dump_T={}", t);
    println!("lines_evaluated={}", lines_read);
    println!("DumpSet_pm={}", dump_total_pm);
    println!("New_pm_T={}", new_pm_total);
    println!("missing_from_dump=|New±(T) \\ DumpSet±|={}", missing);
    println!("extra_in_dump=|DumpSet± \\ (Union_{{k<=T}} New±(k) U {{0,+-1,+-x}})|={}", extra_count);

    let exs = missing_examples.into_inner().unwrap();
    if !exs.is_empty() {
        println!("--- Missing polynomial examples (up to 20) ---");
        for (idx, p) in exs.iter().enumerate() {
            let w_str = match find_witness(&c, p, t) {
                Some(w) => format!("tau={} slp=[{}] computes=[{}]", w.tau, format_compact(&w.slp), w.computes.coeff_line()),
                None => "witness=NOT_FOUND".to_string(),
            };
            println!("MISSING[{}]: coeffs=[{}] {}", idx + 1, p.coeff_line(), w_str);
        }
    }
    if !extra_examples.is_empty() {
        println!("--- Extra polynomial examples (up to 20) ---");
        for (idx, p) in extra_examples.iter().enumerate() {
            println!("EXTRA[{}]: coeffs=[{}]", idx + 1, p.coeff_line());
        }
    }
    if missing == 0 && extra_count == 0 {
        println!("RESULT: PASS (exact match)");
    } else {
        println!("RESULT: FAIL (missing={}, extra={})", missing, extra_count);
        std::process::exit(1);
    }
}

// ------------------------------------------------------------------------------------------
// census CLI wrapper
// ------------------------------------------------------------------------------------------
fn cmd_census(args: &[String], threads: usize) {
    if args.is_empty() {
        eprintln!("Usage: naive_tau census T [--buckets B] [--out DIR] [--exact-upto E] [--keep-cand] [--no-flint]");
        std::process::exit(2);
    }
    let t_max: usize = args[0].parse().expect("bad T");
    let mut opts = Opts {
        buckets: if t_max >= 8 { 16 } else if t_max == 7 { 4 } else { 1 },
        out: "results".to_string(),
        exact_upto: 6,
        keep_cand: false,
        no_flint: false,
        workers: threads,
    };
    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--buckets" => {
                opts.buckets = args[i + 1].parse().expect("bad --buckets");
                i += 2;
            }
            "--out" => {
                opts.out = args[i + 1].clone();
                i += 2;
            }
            "--exact-upto" => {
                opts.exact_upto = args[i + 1].parse().expect("bad --exact-upto");
                i += 2;
            }
            "--keep-cand" => {
                opts.keep_cand = true;
                i += 1;
            }
            "--no-flint" => {
                opts.no_flint = true;
                i += 1;
            }
            other => {
                eprintln!("unknown option: {}", other);
                std::process::exit(2);
            }
        }
    }
    census(t_max, &opts);
}

fn main() {
    let raw_args: Vec<String> = std::env::args().skip(1).collect();
    // Extract global --threads N if present anywhere
    let mut threads: usize = 6;
    let mut args: Vec<String> = Vec::new();
    let mut i = 0;
    while i < raw_args.len() {
        if raw_args[i] == "--threads" {
            threads = raw_args[i + 1].parse().expect("bad --threads");
            i += 2;
        } else {
            args.push(raw_args[i].clone());
            i += 1;
        }
    }
    rayon::ThreadPoolBuilder::new().num_threads(threads).build_global().expect("failed to configure rayon pool");

    if args.is_empty() {
        eprintln!("Usage: naive_tau [--threads N] <census|eval-dump|random-canonical|is-canonical> ...");
        std::process::exit(2);
    }
    match args[0].as_str() {
        "census" => cmd_census(&args[1..], threads),
        "eval-dump" => cmd_eval_dump(&args[1..]),
        "random-canonical" => cmd_random_canonical(&args[1..]),
        "is-canonical" => cmd_is_canonical(&args[1..]),
        cmd => {
            eprintln!("Unknown subcommand: {}", cmd);
            std::process::exit(2);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn random_canonical_samples_are_valid_and_diverse() {
        let mut rng = Rng::new(42);
        for t in 1..=5 {
            let mut seen = HashSet::new();
            for _ in 0..30 {
                let g = sample_one_canonical(t, &mut rng);
                assert_eq!(g.len(), t);
                assert_eq!(is_canonical(&g), Ok(()));
                seen.insert(format_compact(&g));
            }
            if t >= 2 {
                assert!(seen.len() > 5, "t={} lacked diversity: {}", t, seen.len());
            }
        }
    }
}
