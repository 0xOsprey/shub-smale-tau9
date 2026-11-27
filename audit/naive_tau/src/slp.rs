//! Straight-line programs in the COMPACT format, exact evaluation, canonical predicate.

use crate::poly::Poly;

pub const ADD: u8 = 0;
pub const SUB: u8 = 1;
pub const MUL: u8 = 2;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Gate {
    pub op: u8,
    pub i: u8,
    pub j: u8,
}

pub fn apply(op: u8, a: &Poly, b: &Poly) -> Poly {
    match op {
        ADD => a.add(b),
        SUB => a.sub(b),
        MUL => a.mul(b),
        _ => panic!("bad op"),
    }
}

pub fn op_char(op: u8) -> char {
    match op {
        ADD => 'a',
        SUB => 's',
        MUL => 'm',
        _ => '?',
    }
}

pub fn format_compact(g: &[Gate]) -> String {
    let mut s = g.len().to_string();
    for t in g {
        s.push(' ');
        s.push(op_char(t.op));
        s.push_str(&format!("{}.{}", t.i, t.j));
    }
    s
}

/// Parse `<n> <tok> ...`.  Does NOT check well-formedness of wire indices (see `eval_wires`).
pub fn parse_compact(line: &str) -> Result<Vec<Gate>, String> {
    let mut it = line.split_whitespace();
    let n: usize = it
        .next()
        .ok_or("empty line")?
        .parse()
        .map_err(|_| "bad gate count".to_string())?;
    let mut g = Vec::with_capacity(n);
    for _ in 0..n {
        let t = it.next().ok_or_else(|| format!("expected {} tokens", n))?;
        let b = t.as_bytes();
        let op = match b.first() {
            Some(b'a') => ADD,
            Some(b's') => SUB,
            Some(b'm') => MUL,
            _ => return Err(format!("bad op in token {}", t)),
        };
        let rest = &t[1..];
        let (si, sj) = rest.split_once('.').ok_or_else(|| format!("bad token {}", t))?;
        let i: u8 = si.parse().map_err(|_| format!("bad index in {}", t))?;
        let j: u8 = sj.parse().map_err(|_| format!("bad index in {}", t))?;
        g.push(Gate { op, i, j });
    }
    if it.next().is_some() {
        return Err(format!("more than {} tokens", n));
    }
    Ok(g)
}

/// All wires [1, x, g0, g1, ...]; error if an operand index is >= current wire count (wf).
pub fn eval_wires(g: &[Gate]) -> Result<Vec<Poly>, String> {
    let mut w: Vec<Poly> = Vec::with_capacity(g.len() + 2);
    w.push(Poly::one());
    w.push(Poly::x());
    for (k, t) in g.iter().enumerate() {
        if (t.i as usize) >= k + 2 || (t.j as usize) >= k + 2 {
            return Err(format!("gate {} operand out of range", k));
        }
        let c = apply(t.op, &w[t.i as usize], &w[t.j as usize]);
        w.push(c);
    }
    Ok(w)
}

pub fn eval_last(g: &[Gate]) -> Result<Poly, String> {
    Ok(eval_wires(g)?.pop().unwrap())
}

fn key(t: &Gate) -> u32 {
    t.op as u32 * 1024 + t.i as u32 * 32 + t.j as u32
}

/// The CANONICAL predicate from the spec, evaluated with exact polynomial arithmetic.
/// Returns Err(name of the first violated clause).
pub fn is_canonical(g: &[Gate]) -> Result<(), &'static str> {
    let n = g.len();
    let mut w: Vec<Poly> = vec![Poly::one(), Poly::x()];
    for k in 0..n {
        let t = &g[k];
        let (i, j) = (t.i as usize, t.j as usize);
        if i >= k + 2 || j >= k + 2 {
            return Err("wf");
        }
        if t.op == SUB {
            if !(i < j) {
                return Err("ord");
            }
        } else if !(i <= j) {
            return Err("ord");
        }
        let c = apply(t.op, &w[i], &w[j]);
        if c.is_zero() {
            return Err("nonzero");
        }
        let nc = c.neg();
        for m in 0..k + 2 {
            if c == w[m] || nc == w[m] {
                return Err("nodup");
            }
        }
        w.push(c);
    }
    // used: every gate except the last is an operand of some later gate
    for k in 0..n.saturating_sub(1) {
        let wire = (k + 2) as u8;
        if !g[k + 1..].iter().any(|t| t.i == wire || t.j == wire) {
            return Err("used");
        }
    }
    // lex: for 1 <= k <= n-2, if gate k uses neither operand equal to k+1 then key(k-1) <= key(k)
    if n >= 3 {
        for k in 1..=n - 2 {
            let prev_wire = (k + 1) as u8;
            if g[k].i != prev_wire && g[k].j != prev_wire && key(&g[k - 1]) > key(&g[k]) {
                return Err("lex");
            }
        }
    }
    Ok(())
}

/// Order the polynomials `set` (+ final `target`) into an SLP, via greedy closure
/// (computability is monotone in the set of available wires, so greedy succeeds iff some order does).
pub fn slp_from_set(set: &[Poly], target: &Poly) -> Option<Vec<Gate>> {
    let mut wires: Vec<Poly> = vec![Poly::one(), Poly::x()];
    let mut gates: Vec<Gate> = vec![];
    let mut remaining: Vec<Poly> = set.to_vec();
    let find = |wires: &Vec<Poly>, t: &Poly| -> Option<Gate> {
        let n = wires.len();
        for i in 0..n {
            for j in 0..n {
                for op in [ADD, SUB, MUL] {
                    if apply(op, &wires[i], &wires[j]) == *t {
                        return Some(Gate { op, i: i as u8, j: j as u8 });
                    }
                }
            }
        }
        None
    };
    while !remaining.is_empty() {
        let mut found = None;
        for (r, p) in remaining.iter().enumerate() {
            if let Some(g) = find(&wires, p) {
                found = Some((r, g));
                break;
            }
        }
        let (r, g) = found?;
        gates.push(g);
        wires.push(remaining.remove(r));
    }
    let g = find(&wires, target)?;
    gates.push(g);
    Some(gates)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn parse_eval_example() {
        // g0=1+x, g1=g0*g0, g2=x-g1
        let g = parse_compact("3 a0.1 m2.2 s1.3").unwrap();
        let p = eval_last(&g).unwrap();
        assert_eq!(p, Poly::from_i128s(vec![-1, -1, -1]));
        assert_eq!(format_compact(&g), "3 a0.1 m2.2 s1.3");
        assert!(parse_compact("3 a0.1 m2.2").is_err());
        assert!(eval_wires(&parse_compact("1 a0.2").unwrap()).is_err());
    }
    #[test]
    fn canonical_basic() {
        // x^2-1 : g0 = x*x, g1 = g0 - 1 -> sub requires i<j: 1(w0) - w2 would be -(x^2-1); canonical must use i<j
        assert!(is_canonical(&parse_compact("2 m1.1 s0.2").unwrap()).is_ok()); // 1 - x^2
        assert_eq!(is_canonical(&parse_compact("2 m1.1 s2.0").unwrap()), Err("ord"));
        assert_eq!(is_canonical(&parse_compact("1 s1.1").unwrap()), Err("ord"));
        assert_eq!(is_canonical(&parse_compact("1 m0.1").unwrap()), Err("nodup"));
        assert_eq!(is_canonical(&parse_compact("2 a0.1 m1.1").unwrap()), Err("used"));
        // lex: gates 0,1 independent, key(g0)=add(0)... g0 = mul, g1 = add not using wire 2 -> key(g0)>key(g1)
        // 4 gates: g0=x*x(m1.1), g1=x+1 (a0.1), g2 = g0+g1 (uses 3 = previous wire -> exempt), g3 = g2*g2
        assert_eq!(is_canonical(&parse_compact("4 m1.1 a0.1 a2.3 m4.4").unwrap()), Err("lex"));
        assert!(is_canonical(&parse_compact("4 a0.1 m1.1 a2.3 m4.4").unwrap()).is_ok());
    }
    #[test]
    fn slp_from_set_works() {
        let x = Poly::x();
        let x2 = x.mul(&x);
        let a = x.add(&Poly::one());
        let t = x2.sub(&a);
        let g = slp_from_set(&[a.clone(), x2.clone()], &t).unwrap();
        assert_eq!(g.len(), 3);
        assert_eq!(eval_last(&g).unwrap(), t);
    }
}
