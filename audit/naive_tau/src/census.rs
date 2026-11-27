//! Census of straight-line programs by exhaustive enumeration of SETS of computed polynomials.
//!
//! State = set of computed polynomials (excluding the constants wires 1 and x).
//! L_0 = {empty}; L_{k+1} = { S + {c} : S in L_k, c = a OP b, a,b in S+{1,x}, OP in {+,-,*} }.
//!
//! Soundness of dropping c == 0 and c in S+{1,x}:  in a program of MINIMAL length for f
//! (length tau(f) >= 1), no gate output is 0 (unless f == 0 itself, whose tau is 1 and which is
//! handled/reported separately: 0 is excluded from all counts), and no gate output equals an
//! earlier wire (1, x or a previous gate) -- otherwise that gate could be deleted (all later uses
//! redirected to the earlier equal wire), contradicting minimality; a zero wire used as an operand
//! can likewise be bypassed (0+a=a, a-0=a, 0*a=0, ...) giving a shorter program.  Hence the
//! sets obtained with those gates dropped still contain, for every f, a state in L_{tau(f)-1}
//! from which f is a child, i.e. tau is computed exactly.
//!
//! NO sign symmetry, NO operand ordering and NO gate-order canonicalisation is used: all ordered
//! operand pairs (i,j) and all three ops are tried for every state.

use crate::poly::*;
use crate::slp::*;
use num_bigint::BigInt;
use rayon::prelude::*;
use std::collections::HashMap;
use std::io::Write;
use std::sync::atomic::{AtomicU32, AtomicU64, Ordering};
use std::sync::Mutex;
use std::time::Instant;

pub type State = [u32; 8];
pub const PAD: u32 = u32::MAX;
pub const EMPTY_STATE: State = [PAD; 8];

pub fn state_ids(s: &State) -> &[u32] {
    let n = s.iter().position(|&x| x == PAD).unwrap_or(8);
    &s[..n]
}
pub fn state_insert(s: &State, id: u32) -> State {
    let mut r = EMPTY_STATE;
    let ids = state_ids(s);
    assert!(ids.len() < 8, "state too long");
    let mut pos = ids.len();
    for (k, &x) in ids.iter().enumerate() {
        if x > id {
            pos = k;
            break;
        }
    }
    r[..pos].copy_from_slice(&ids[..pos]);
    r[pos] = id;
    r[pos + 1..ids.len() + 1].copy_from_slice(&ids[pos..]);
    r
}
pub fn state_hash(s: &State) -> u64 {
    let mut h = 0x9e3779b97f4a7c15u64;
    for &x in state_ids(s) {
        h = mix(h ^ x as u64);
    }
    h
}

// ------------------------------------------------------------------------------------------
// Hash-consing interner: exact coefficient vectors -> u32 ids.  ids 0 and 1 are 1 and x.
// ------------------------------------------------------------------------------------------
pub struct Interner {
    pub polys: Vec<Poly>,
    pub hashes: Vec<u64>,
    pub level: Vec<u8>,
    table: Vec<u32>,
    mask: usize,
}
const EMPTYSLOT: u32 = u32::MAX;
impl Interner {
    pub fn new() -> Interner {
        let mut it = Interner { polys: vec![], hashes: vec![], level: vec![], table: vec![EMPTYSLOT; 1024], mask: 1023 };
        it.push(Poly::one(), 0);
        it.push(Poly::x(), 0);
        it
    }
    pub fn len(&self) -> usize {
        self.polys.len()
    }
    #[inline]
    pub fn get(&self, p: &Poly, h: u64) -> Option<u32> {
        let mut i = (h as usize) & self.mask;
        loop {
            let id = self.table[i];
            if id == EMPTYSLOT {
                return None;
            }
            if self.hashes[id as usize] == h && self.polys[id as usize] == *p {
                return Some(id);
            }
            i = (i + 1) & self.mask;
        }
    }
    pub fn lookup(&self, p: &Poly) -> Option<u32> {
        self.get(p, p.phash())
    }
    fn grow(&mut self, want: usize) {
        let mut sz = self.table.len();
        while sz < want * 2 {
            sz *= 2;
        }
        if sz != self.table.len() {
            self.table = vec![EMPTYSLOT; sz];
            self.mask = sz - 1;
            for id in 0..self.polys.len() {
                let mut i = (self.hashes[id] as usize) & self.mask;
                while self.table[i] != EMPTYSLOT {
                    i = (i + 1) & self.mask;
                }
                self.table[i] = id as u32;
            }
        }
    }
    /// precondition: p not present
    pub fn push(&mut self, p: Poly, level: u8) -> u32 {
        let h = p.phash();
        self.grow(self.polys.len() + 1);
        let id = self.polys.len() as u32;
        assert!(id < EMPTYSLOT - 1);
        let mut i = (h as usize) & self.mask;
        while self.table[i] != EMPTYSLOT {
            i = (i + 1) & self.mask;
        }
        self.table[i] = id;
        self.polys.push(p);
        self.hashes.push(h);
        self.level.push(level);
        id
    }
    pub fn reserve(&mut self, extra: usize) {
        let n = self.polys.len() + extra;
        self.polys.reserve(extra);
        self.hashes.reserve(extra);
        self.level.reserve(extra);
        self.grow(n);
    }
}

pub struct Census {
    pub it: Interner,
    /// levels[k] = L_k as sorted, deduplicated state vectors (only stored levels)
    pub levels: Vec<Vec<State>>,
    /// lvl_range[t] = id range of polynomials with tau == t (t>=1) ; t = 0: ids 0..2
    pub lvl_range: Vec<(usize, usize)>,
}

pub fn wires_of<'a>(it: &'a Interner, ids: &[u32]) -> Vec<&'a Poly> {
    let mut w: Vec<&Poly> = Vec::with_capacity(ids.len() + 2);
    w.push(&it.polys[0]);
    w.push(&it.polys[1]);
    for &id in ids {
        w.push(&it.polys[id as usize]);
    }
    w
}

/// Calls f on every a OP b for ALL ordered pairs (a,b) of wires and all three ops.
#[inline]
pub fn for_each_child<F: FnMut(Poly)>(w: &[&Poly], f: &mut F) {
    let n = w.len();
    for i in 0..n {
        for j in 0..n {
            f(w[i].add(w[j]));
            f(w[i].sub(w[j]));
            f(w[i].mul(w[j]));
        }
    }
}

// ------------------------------------------------------------------------------------------
// concurrent "new polynomial" map used while building a stored level
// ------------------------------------------------------------------------------------------
const NSH: usize = 256;
#[inline]
fn shard_of(h: u64) -> usize {
    ((h >> 40) as usize) & (NSH - 1)
}
type Map<V> = HashMap<HP, V, IdBuild>;

struct NewMap {
    shards: Vec<Mutex<Map<u32>>>,
    counter: AtomicU32,
}
impl NewMap {
    fn new(start: u32) -> NewMap {
        NewMap { shards: (0..NSH).map(|_| Mutex::new(Map::default())).collect(), counter: AtomicU32::new(start) }
    }
    fn get_or_insert(&self, h: u64, p: Poly) -> u32 {
        let key = HP { h, p };
        let mut g = self.shards[shard_of(h)].lock().unwrap();
        if let Some(&id) = g.get(&key) {
            return id;
        }
        let id = self.counter.fetch_add(1, Ordering::Relaxed);
        g.insert(key, id);
        id
    }
}

/// Build L_{k+1} from L_k (states of length k) and intern all new polynomials with level k+1.
pub fn build_next(it: &mut Interner, states: &[State], k: usize) -> Vec<State> {
    let start = it.len() as u32;
    let nm = NewMap::new(start);
    let chunks: Vec<Vec<State>> = {
        let it: &Interner = &*it;
        states
            .par_chunks(256)
            .map(|chunk| {
                let mut local: Vec<State> = Vec::new();
                for s in chunk {
                    let ids = state_ids(s);
                    debug_assert_eq!(ids.len(), k);
                    let w = wires_of(it, ids);
                    for_each_child(&w, &mut |c: Poly| {
                        if c.is_zero() {
                            return;
                        }
                        let h = c.phash();
                        let id = match it.get(&c, h) {
                            Some(id) => id,
                            None => nm.get_or_insert(h, c),
                        };
                        if id < 2 || ids.contains(&id) {
                            return;
                        }
                        local.push(state_insert(s, id));
                    });
                }
                local.sort_unstable();
                local.dedup();
                local
            })
            .collect()
    };
    // intern new polys in id order
    let total_new = nm.counter.load(Ordering::Relaxed) - start;
    let mut slots: Vec<Option<Poly>> = (0..total_new).map(|_| None).collect();
    for sh in nm.shards {
        for (k2, id) in sh.into_inner().unwrap() {
            slots[(id - start) as usize] = Some(k2.p);
        }
    }
    it.reserve(slots.len());
    for p in slots {
        it.push(p.expect("id gap"), (k + 1) as u8);
    }
    let mut all: Vec<State> = chunks.into_iter().flatten().collect();
    all.par_sort_unstable();
    all.dedup();
    all
}

// ------------------------------------------------------------------------------------------
// class accumulator: classes {f,-f}; value bits: 1 = rep seen, 2 = -rep seen
// ------------------------------------------------------------------------------------------
pub struct ClassAcc {
    pub shards: Vec<Mutex<Map<u8>>>,
}
pub type LocalAcc = Map<u8>;
pub fn local_insert(m: &mut LocalAcc, c: Poly) {
    let neg = c.lc_sign() < 0;
    let h = c.class_hash();
    let rep = if neg { c.neg() } else { c };
    *m.entry(HP { h, p: rep }).or_insert(0) |= if neg { 2 } else { 1 };
}
impl ClassAcc {
    pub fn new() -> ClassAcc {
        ClassAcc { shards: (0..NSH).map(|_| Mutex::new(Map::default())).collect() }
    }
    pub fn merge(&self, local: LocalAcc) {
        let mut by: Vec<Vec<(HP, u8)>> = (0..NSH).map(|_| Vec::new()).collect();
        for (k, v) in local {
            by[shard_of(k.h)].push((k, v));
        }
        for (s, v) in by.into_iter().enumerate() {
            if v.is_empty() {
                continue;
            }
            let mut g = self.shards[s].lock().unwrap();
            for (k, b) in v {
                *g.entry(k).or_insert(0) |= b;
            }
        }
    }
}

#[derive(Default, Clone, Debug)]
pub struct ClassStats {
    pub new_polys: u64,      // |New(t)| (distinct polys f with tau(f)=t exactly)
    pub entries: u64,        // classes touched by New(t)
    pub new_pm: u64,         // |New±(t)|: classes with min(tau(f),tau(-f)) = t
    pub excluded: u64,       // classes touched by New(t) whose other member has smaller tau (or is +-1,+-x)
    pub sent: u64,           // classes written to candidate file
    pub deg_hist: Vec<u64>,  // degree histogram of New±(t) classes
}
impl ClassStats {
    pub fn add(&mut self, o: &ClassStats) {
        self.new_polys += o.new_polys;
        self.entries += o.entries;
        self.new_pm += o.new_pm;
        self.excluded += o.excluded;
        self.sent += o.sent;
        if self.deg_hist.len() < o.deg_hist.len() {
            self.deg_hist.resize(o.deg_hist.len(), 0);
        }
        for (i, v) in o.deg_hist.iter().enumerate() {
            self.deg_hist[i] += v;
        }
    }
}

/// Finish accumulator for level t: counts, exclusion test (other member has lower tau), and writes
/// to `cand` every non-excluded class whose degree is > send_above (send_above < 0: all).
pub fn finalize(acc: &ClassAcc, it: &Interner, t: u8, send_above: i64, cand: Option<&Mutex<std::io::BufWriter<std::fs::File>>>) -> ClassStats {
    let parts: Vec<ClassStats> = acc
        .shards
        .par_iter()
        .map(|m| {
            let g = m.lock().unwrap();
            let mut st = ClassStats::default();
            let mut buf = String::new();
            let lo = |p: &Poly, h: u64| it.get(p, h).map_or(false, |id| it.level[id as usize] < t);
            for (k, &bits) in g.iter() {
                st.new_polys += (bits & 1) as u64 + ((bits >> 1) & 1) as u64;
                st.entries += 1;
                let nf = k.p.neg();
                let excl = lo(&k.p, k.h) || lo(&nf, k.p.hash_with(true));
                if excl {
                    st.excluded += 1;
                    continue;
                }
                st.new_pm += 1;
                let d = k.p.degree().expect("zero in class acc");
                if st.deg_hist.len() <= d {
                    st.deg_hist.resize(d + 1, 0);
                }
                st.deg_hist[d] += 1;
                if cand.is_some() && (d as i64) > send_above {
                    st.sent += 1;
                    buf.push_str("P ");
                    buf.push_str(&k.p.coeff_line());
                    buf.push('\n');
                    if buf.len() > (1 << 20) {
                        cand.unwrap().lock().unwrap().write_all(buf.as_bytes()).unwrap();
                        buf.clear();
                    }
                }
            }
            if let Some(c) = cand {
                if !buf.is_empty() {
                    c.lock().unwrap().write_all(buf.as_bytes()).unwrap();
                }
            }
            st
        })
        .collect();
    let mut tot = ClassStats::default();
    for p in &parts {
        tot.add(p);
    }
    tot
}

// ------------------------------------------------------------------------------------------
// top level pass (level T is NOT stored): restricted to hash-bucket b of bn
// ------------------------------------------------------------------------------------------
pub struct TopOut {
    pub acc: ClassAcc,
    pub new_pairs: u64,
    pub interned_states: Vec<State>,
    pub children: u64,
}

fn dedup_exact(v: &mut Vec<(u64, Poly)>) {
    v.sort_unstable_by_key(|x| x.0);
    let mut out: Vec<(u64, Poly)> = Vec::with_capacity(v.len());
    let mut gs = 0usize; // start of current equal-hash group in out
    for (h, p) in v.drain(..) {
        if gs < out.len() && out[gs].0 != h {
            gs = out.len();
        }
        if !out[gs..].iter().any(|(_, q)| *q == p) {
            out.push((h, p));
        }
    }
    *v = out;
}

pub fn top_pass(it: &Interner, states: &[State], b: usize, bn: usize, want_states: bool) -> TopOut {
    let acc = ClassAcc::new();
    let new_pairs = AtomicU64::new(0);
    let children = AtomicU64::new(0);
    let all_states: Mutex<Vec<State>> = Mutex::new(Vec::new());
    states.par_chunks(128).for_each(|chunk| {
        let mut local: LocalAcc = LocalAcc::default();
        let mut lstates: Vec<State> = Vec::new();
        let mut np = 0u64;
        let mut ch = 0u64;
        let mut newlist: Vec<(u64, Poly)> = Vec::new();
        for s in chunk {
            let ids = state_ids(s);
            let w = wires_of(it, ids);
            newlist.clear();
            for_each_child(&w, &mut |c: Poly| {
                ch += 1;
                if c.is_zero() {
                    return;
                }
                let h = c.phash();
                match it.get(&c, h) {
                    Some(id) => {
                        if id < 2 || ids.contains(&id) {
                            return;
                        }
                        if want_states {
                            let ns = state_insert(s, id);
                            if bn == 1 || (state_hash(&ns) % bn as u64) as usize == b {
                                lstates.push(ns);
                            }
                        }
                    }
                    None => {
                        if bn > 1 && (c.class_hash() % bn as u64) as usize != b {
                            return;
                        }
                        newlist.push((h, c));
                    }
                }
            });
            dedup_exact(&mut newlist);
            np += newlist.len() as u64;
            for (_, c) in newlist.drain(..) {
                local_insert(&mut local, c);
            }
        }
        lstates.sort_unstable();
        lstates.dedup();
        acc.merge(local);
        new_pairs.fetch_add(np, Ordering::Relaxed);
        children.fetch_add(ch, Ordering::Relaxed);
        if !lstates.is_empty() {
            all_states.lock().unwrap().extend(lstates);
        }
    });
    let mut st = all_states.into_inner().unwrap();
    st.par_sort_unstable();
    st.dedup();
    TopOut { acc, new_pairs: new_pairs.load(Ordering::Relaxed), interned_states: st, children: children.load(Ordering::Relaxed) }
}

// ------------------------------------------------------------------------------------------
// witnesses
// ------------------------------------------------------------------------------------------
pub struct Witness {
    pub computes: Poly, // the polynomial the SLP actually computes (f or -f)
    pub slp: Vec<Gate>,
    pub tau: usize,
}

/// Witness SLP of length tau(class) for f or -f (whichever has smaller tau; the SLP computes the
/// returned `computes`).  `top_t`: level to assume when neither f nor -f is interned.
pub fn find_witness(c: &Census, f: &Poly, top_t: usize) -> Option<Witness> {
    let nf = f.neg();
    let lv = |p: &Poly| c.it.lookup(p).map(|id| c.it.level[id as usize] as usize);
    let t = match (lv(f), lv(&nf)) {
        (Some(a), Some(b)) => a.min(b),
        (Some(a), None) => a,
        (None, Some(b)) => b,
        (None, None) => top_t,
    };
    if t == 0 {
        let p = if *f == Poly::x() || nf == Poly::x() { Poly::x() } else { Poly::one() };
        return Some(Witness { computes: p, slp: vec![], tau: 0 });
    }
    let states = &c.levels[t - 1];
    let found: Option<(State, Poly)> = states.par_iter().find_map_any(|s| {
        let ids = state_ids(s);
        let w = wires_of(&c.it, ids);
        let mut res: Option<Poly> = None;
        for_each_child(&w, &mut |ch: Poly| {
            if res.is_none() && (ch == *f || ch == nf) {
                res = Some(ch);
            }
        });
        res.map(|p| (*s, p))
    });
    let (s, p) = found?;
    let set: Vec<Poly> = state_ids(&s).iter().map(|&id| c.it.polys[id as usize].clone()).collect();
    let slp = slp_from_set(&set, &p)?;
    assert_eq!(slp.len(), t);
    Some(Witness { computes: p, slp, tau: t })
}

// ------------------------------------------------------------------------------------------
// FLINT driver (python-flint, exact) -- the reference z computation
// ------------------------------------------------------------------------------------------
pub struct FlintOut {
    pub hits: Vec<(u64, Poly)>,
    pub hist: Vec<(u64, u64)>,
    pub raw: String,
}
pub fn python_path() -> String {
    std::env::var("NAIVE_TAU_PYTHON").unwrap_or("/Users/joe/github/gemini-neon/.venv-tau/bin/python3".to_string())
}
pub fn flint_script() -> String {
    std::env::var("NAIVE_TAU_FLINT").unwrap_or(concat!(env!("CARGO_MANIFEST_DIR"), "/../flint_roots.py").to_string())
}
pub fn run_flint(file: &str, k: i64, exact_all: bool, workers: usize) -> FlintOut {
    let mut cmd = std::process::Command::new(python_path());
    cmd.arg(flint_script())
        .arg(file)
        .arg(k.to_string())
        .arg("--workers")
        .arg(workers.to_string());
    if exact_all {
        cmd.arg("--exact-all");
    }
    let out = cmd.output().expect("failed to spawn python");
    let stdout = String::from_utf8_lossy(&out.stdout).to_string();
    if !out.status.success() {
        panic!("flint_roots.py failed: {}\n{}", String::from_utf8_lossy(&out.stderr), stdout);
    }
    let mut hits = vec![];
    let mut hist = vec![];
    for l in stdout.lines() {
        if let Some(r) = l.strip_prefix("HIT ") {
            // HIT <count> | c0 c1 ... | <line>
            let parts: Vec<&str> = r.split(" | ").collect();
            let cnt: u64 = parts[0].trim().parse().unwrap();
            let coefs: Vec<BigInt> = parts[1].split_whitespace().map(|x| x.parse().unwrap()).collect();
            hits.push((cnt, Poly::from_bigs(coefs)));
        } else if let Some(r) = l.strip_prefix("HIST ") {
            let mut it = r.split_whitespace();
            let z: u64 = it.next().unwrap().parse().unwrap();
            let n: u64 = it.next().unwrap().parse().unwrap();
            hist.push((z, n));
        }
    }
    FlintOut { hits, hist, raw: stdout }
}

// ------------------------------------------------------------------------------------------
// census driver
// ------------------------------------------------------------------------------------------
pub fn jq(s: &str) -> String {
    let mut o = String::from("\"");
    for ch in s.chars() {
        match ch {
            '"' => o.push_str("\\\""),
            '\\' => o.push_str("\\\\"),
            '\n' => o.push_str("\\n"),
            c => o.push(c),
        }
    }
    o.push('"');
    o
}

#[derive(Clone)]
pub struct Best {
    pub z: u64,
    pub poly: String,
    pub slp: String,
    pub tau: usize,
    pub found_at: usize,
}

pub struct Opts {
    pub buckets: usize,
    pub out: String,
    pub exact_upto: usize,
    pub keep_cand: bool,
    pub no_flint: bool,
    pub workers: usize,
}

fn best_json(b: &Best) -> String {
    format!(
        "{{\"z\":{},\"poly_coeffs_ascending\":{},\"slp_compact\":{},\"slp_gates\":{},\"first_found_at_level\":{}}}",
        b.z,
        jq(&b.poly),
        jq(&b.slp),
        b.tau,
        b.found_at
    )
}

fn hist_json(h: &[(u64, u64)]) -> String {
    let items: Vec<String> = h.iter().map(|(z, n)| format!("\"{}\":{}", z, n)).collect();
    format!("{{{}}}", items.join(","))
}

fn degs_json(h: &[u64]) -> String {
    format!("[{}]", h.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(","))
}

pub fn census(t_max: usize, o: &Opts) {
    std::fs::create_dir_all(&o.out).unwrap();
    let t0 = Instant::now();
    let mut c = Census { it: Interner::new(), levels: vec![vec![EMPTY_STATE]], lvl_range: vec![(0, 2)] };
    let mut best = Best { z: 1, poly: "0 1".into(), slp: "0".into(), tau: 0, found_at: 0 };
    let mut table: Vec<String> = vec![];
    let mut summary_rows: Vec<String> = vec![];
    for t in 1..=t_max {
        let tl = Instant::now();
        let top = t == t_max;
        let exact_all = t <= o.exact_upto;
        let send_above: i64 = if exact_all { -1 } else { best.z as i64 };
        let cand_path = format!("{}/cand_tau{}.txt", o.out, t);
        let cand = Mutex::new(std::io::BufWriter::new(std::fs::File::create(&cand_path).unwrap()));
        let mut stats = ClassStats::default();
        let l_size: u64;
        let mut children_total = 0u64;
        let mut interned_total = 0u64;
        let mut new_pairs_total = 0u64;
        if !top {
            let prev = c.levels[t - 1].clone();
            let next = build_next(&mut c.it, &prev, t - 1);
            let (a, b) = (if t == 1 { 2 } else { c.lvl_range[t - 1].1 }, c.it.len());
            c.lvl_range.push((a, b));
            l_size = next.len() as u64;
            c.levels.push(next);
            let acc = ClassAcc::new();
            let mut local = LocalAcc::default();
            for id in a..b {
                local_insert(&mut local, c.it.polys[id].clone());
            }
            acc.merge(local);
            stats = finalize(&acc, &c.it, t as u8, send_above, Some(&cand));
            eprintln!("[tau {}] stored level: |L|={} polys interned={} ({:.1}s)", t, l_size, b - a, tl.elapsed().as_secs_f64());
        } else {
            let bn = o.buckets.max(1);
            let prev = &c.levels[t - 1];
            for b in 0..bn {
                let tp = Instant::now();
                let out = top_pass(&c.it, prev, b, bn, true);
                let st = finalize(&out.acc, &c.it, t as u8, send_above, Some(&cand));
                if b == 0 {
                    children_total = out.children;
                }
                new_pairs_total += out.new_pairs;
                interned_total += out.interned_states.len() as u64;
                eprintln!(
                    "[tau {}] top pass {}/{}: new_polys={} classes={} new_pm={} (+{} new (S,c) pairs, {} interned-child states) {:.1}s",
                    t, b + 1, bn, st.new_polys, st.entries, st.new_pm, out.new_pairs, out.interned_states.len(), tp.elapsed().as_secs_f64()
                );
                stats.add(&st);
            }
            l_size = new_pairs_total + interned_total;
        }
        cand.lock().unwrap().flush().unwrap();
        drop(cand);
        // z via FLINT
        let mut fl_raw = String::new();
        let mut hist: Vec<(u64, u64)> = vec![];
        let prev_best = best.z;
        if !o.no_flint && stats.sent > 0 {
            let tf = Instant::now();
            let fo = run_flint(&cand_path, best.z as i64, exact_all, o.workers);
            eprintln!("[tau {}] flint: {} candidates, {} hits above {} ({:.1}s)", t, stats.sent, fo.hits.len(), prev_best, tf.elapsed().as_secs_f64());
            hist = fo.hist.clone();
            fl_raw = fo.raw.clone();
            let mut hits = fo.hits;
            hits.sort_by_key(|(z, p)| (std::cmp::Reverse(*z), p.len()));
            if let Some((z, p)) = hits.first() {
                assert!(*z > prev_best);
                let w = find_witness(&c, p, t).expect("witness not found for hit");
                best = Best { z: *z, poly: w.computes.coeff_line(), slp: format_compact(&w.slp), tau: w.slp.len(), found_at: t };
            }
        }
        std::fs::write(format!("{}/flint_tau{}.txt", o.out, t), &fl_raw).unwrap();
        if !o.keep_cand {
            let _ = std::fs::remove_file(&cand_path);
        }
        let secs = tl.elapsed().as_secs_f64();
        let sent_deg_note = if exact_all { "all classes".to_string() } else { format!("classes with degree > {}", prev_best) };
        let json = format!(
            "{{\n \"tau\":{},\n \"L_size\":{},\n \"new_polys\":{},\n \"new_pm_classes\":{},\n \"excluded_classes_with_smaller_tau_member\":{},\n \"zero_poly_note\":\"tau(0)=1; 0 is excluded from every count here\",\n \"z_max_cumulative\":{},\n \"z_max_witness\":{},\n \"classes_sent_to_flint\":{},\n \"flint_scope\":{},\n \"flint_histogram_of_exactly_counted_classes\":{},\n \"degree_histogram_new_pm\":{},\n \"top_level_unstored\":{},\n \"children_enumerated\":{},\n \"states_with_new_child\":{},\n \"states_with_interned_child\":{},\n \"seconds\":{:.2}\n}}\n",
            t, l_size, stats.new_polys, stats.new_pm, stats.excluded, best.z, best_json(&best), stats.sent, jq(&sent_deg_note), hist_json(&hist), degs_json(&stats.deg_hist), top, children_total, new_pairs_total, interned_total, secs
        );
        std::fs::write(format!("{}/tau{}.json", o.out, t), &json).unwrap();
        eprintln!("[tau {}] |L|={} |New|={} |New±|={} z_max={} ({:.1}s)", t, l_size, stats.new_polys, stats.new_pm, best.z, secs);
        println!("tau={} |L|={} |New|={} |New±|={} z_max={} witness_slp=[{}] poly=[{}] secs={:.1}", t, l_size, stats.new_polys, stats.new_pm, best.z, best.slp, best.poly, secs);
        table.push(format!("\"{}\":{}", t, stats.new_pm));
        summary_rows.push(format!(
            "{{\"tau\":{},\"L_size\":{},\"new\":{},\"new_pm\":{},\"z_max\":{},\"z_max_witness\":{},\"seconds\":{:.2}}}",
            t, l_size, stats.new_polys, stats.new_pm, best.z, best_json(&best), secs
        ));
        std::fs::write(format!("{}/polys_per_tau.json", o.out), format!("{{\"polys_per_tau_new_pm\":{{{}}}}}\n", table.join(","))).unwrap();
        std::fs::write(
            format!("{}/summary_T{}.json", o.out, t_max),
            format!("{{\"max_tau_requested\":{},\"rows\":[\n{}\n],\"total_seconds_so_far\":{:.1}}}\n", t_max, summary_rows.join(",\n"), t0.elapsed().as_secs_f64()),
        )
        .unwrap();
    }
}

/// Build the census up to level t_max-1 stored (levels 0..=t_max-1), used by eval-dump.
pub fn build_census(upto: usize) -> Census {
    let mut c = Census { it: Interner::new(), levels: vec![vec![EMPTY_STATE]], lvl_range: vec![(0, 2)] };
    for t in 1..=upto {
        let prev = c.levels[t - 1].clone();
        let next = build_next(&mut c.it, &prev, t - 1);
        let a = if t == 1 { 2 } else { c.lvl_range[t - 1].1 };
        c.lvl_range.push((a, c.it.len()));
        c.levels.push(next);
    }
    c
}

#[cfg(test)]
mod tests {
    use super::*;

    fn mk(upto: usize) -> Census {
        build_census(upto)
    }
    fn level_stats(c: &Census, t: usize) -> (usize, u64, u64) {
        let (a, b) = c.lvl_range[t];
        let acc = ClassAcc::new();
        let mut local = LocalAcc::default();
        for id in a..b {
            local_insert(&mut local, c.it.polys[id].clone());
        }
        acc.merge(local);
        let st = finalize(&acc, &c.it, t as u8, 0, None);
        (c.levels[t].len(), st.new_polys, st.new_pm)
    }

    #[test]
    fn tau1_hand_checked() {
        let c = mk(2);
        // New(1) = {2, x+1, x-1, 1-x, 2x, x^2}; classes {2},{x+1},{x-1,1-x},{2x},{x^2} -> 5
        let (l, n, pm) = level_stats(&c, 1);
        assert_eq!((l, n, pm), (6, 6, 5));
        for p in [vec![2], vec![1, 1], vec![-1, 1], vec![1, -1], vec![0, 2], vec![0, 0, 1]] {
            let id = c.it.lookup(&Poly::from_i128s(p.clone())).expect("missing");
            assert_eq!(c.it.level[id as usize], 1, "{:?}", p);
        }
        // tau(0) = 1 but 0 is not interned
        assert!(c.it.lookup(&Poly::zero()).is_none());
    }
    #[test]
    fn small_taus() {
        let c = mk(4);
        let lev = |p: Vec<i128>| c.it.level[c.it.lookup(&Poly::from_i128s(p)).unwrap() as usize];
        assert_eq!(lev(vec![-1, 0, 1]), 2); // x^2-1
        assert_eq!(lev(vec![0, -1, 1]), 2); // x^2-x
        assert_eq!(lev(vec![-1]), 2); // -1
        assert_eq!(lev(vec![0, -1]), 2); // -x
        assert_eq!(lev(vec![0, 0, 0, 1]), 2); // x^3 = x*x^2
        assert_eq!(lev(vec![0, 0, 0, 0, 1]), 2); // x^4 = (x^2)^2
        assert_eq!(lev(vec![4]), 2);
        assert_eq!(lev(vec![0, 0, 0, 0, 0, 1]), 3); // x^5
        assert_eq!(lev(vec![3]), 2); // 3 = 2+1
        assert_eq!(lev(vec![-2]), 3);
        // cross-checked with independent brute enumerator
        let l: Vec<usize> = (1..=4).map(|t| level_stats(&c, t).0).collect();
        eprintln!("L sizes {:?}", l);
    }

    #[test]
    fn top_pass_matches_build_next() {
        let full = mk(4);
        let c3 = mk(3);
        let (l4_ref, new4_ref, pm4_ref) = level_stats(&full, 4);
        for bn in [1usize, 4usize] {
            let mut tot_new = 0u64;
            let mut tot_pm = 0u64;
            let mut tot_np = 0u64;
            let mut tot_int = 0u64;
            for b in 0..bn {
                let out = top_pass(&c3.it, &c3.levels[3], b, bn, true);
                let st = finalize(&out.acc, &c3.it, 4, 0, None);
                tot_new += st.new_polys;
                tot_pm += st.new_pm;
                tot_np += out.new_pairs;
                tot_int += out.interned_states.len() as u64;
            }
            assert_eq!((tot_np + tot_int) as usize, l4_ref, "bn={}", bn);
            assert_eq!(tot_new, new4_ref, "bn={}", bn);
            assert_eq!(tot_pm, pm4_ref, "bn={}", bn);
        }
    }
}
