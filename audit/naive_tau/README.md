# `naive_tau` — Independent Deliberately Naive Cross-Check for the Shub-Smale $\tau$-Conjecture

This crate implements an independent, deliberately naive, exact enumerator for straight-line programs (SLPs) over $\mathbb{Z}[x]$ with inputs $w_0 = 1, w_1 = x$ and binary gates $+, -, \times$, together with an independent exact integer-root counter ([flint_roots.py](../flint_roots.py)) powered by `python-flint`.

## Design & Soundness

- **No pruning / no symmetries**: NO sign symmetry, NO operand ordering, NO gate-order canonicalization. Every ordered operand pair $(i, j)$ and every op in $\{+, -, \times\}$ is enumerated.
- **State-set BFS**: A state is a sorted, deduplicated set of computed polynomial IDs (excluding $1$ and $x$).
  - $L_0 = \{\emptyset\}$.
  - $L_{k+1} = \{ S \cup \{c\} : S \in L_k,\; c = a \mathbin{\mathrm{op}} b,\; a, b \in S \cup \{1, x\},\; c \notin S \cup \{1, x\},\; c \neq 0 \}$.
  - Skipping $c = 0$ and $c \in S \cup \{1, x\}$ is trivially sound for $\tau(f)$ of nonzero $f$: in a minimal SLP, any gate producing a duplicate wire can be deleted and redirected, and any zero wire used as an operand can be simplified away; $\tau(0) = 1$ is excluded and noted separately.
- **Exact arithmetic only**: Polynomials use checked `i128` coefficient vectors with automatic fallback to `num_bigint::BigInt` on any overflow (never silent wrap), normalized so equality is exact value equality.
- **Exact hash-consing**: Polynomials are interned to `u32` IDs keyed by exact coefficient vector (64-bit hashes are used only for table bucketing).
- **Exact root counting**: Distinct integer roots $z(f)$ are counted by calling `python-flint`'s exact `fmpz_poly.factor()` via [flint_roots.py](../flint_roots.py).

## Build & Test

```bash
cd /tmp/shub-smale-tau9/audit/naive_tau
cargo test --release
cargo build --release
cp target/release/naive_tau /Users/joe/github/gemini-neon/runs/bin/naive_tau
```

## CLI Modes

All commands accept `--threads N` (default `6`).

### 1. `census T`
Runs the exhaustive state-set census for $\tau = 1 \dots T$, writing JSON results (`tau<t>.json`, `polys_per_tau.json`, `summary_T<T>.json`, `flint_tau<t>.txt`) to `--out DIR` (default `results`).

```bash
naive_tau --threads 6 census 7 --out /tmp/shub-smale-tau9/audit/naive_tau/results --buckets 4 --exact-upto 5
```

### 2. `eval-dump FILE T`
Streams COMPACT-format leaf SLPs (`<n> <op><i>.<j> ...`, supporting plain text or `--stdin`), evaluates each polynomial exactly, deduplicates up to sign, and cross-checks against $\mathrm{New}^\pm(T)$ and $\bigcup_{k \le T} \mathrm{New}^\pm(k) \cup \{0, \pm 1, \pm x\}$. Reports both set differences (must be 0) and prints up to 20 missing examples with witness SLPs.

```bash
naive_tau --threads 6 eval-dump /path/to/dump.txt 6
cat dump.txt | naive_tau --threads 6 eval-dump --stdin 6
```

### 3. `random-canonical T N SEED`
Emits `N` diverse random `T`-gate SLPs in COMPACT format satisfying the `CANONICAL` predicate (`wf`, `ord`, `nonzero`, `nodup`, `used`, `lex`), verified with exact polynomial arithmetic.

```bash
naive_tau random-canonical 5 100 12345
```

### 4. `is-canonical FILE|--stdin`
Filters/checks COMPACT SLP lines against the `CANONICAL` predicate, writing canonical lines to stdout and summary/rejection breakdown to stderr.

```bash
naive_tau is-canonical candidates.txt
```

### 5. `flint_roots.py FILE K`
Independent exact integer-root counter using `python-flint`:

```bash
/Users/joe/github/gemini-neon/.venv-tau/bin/python3 /tmp/shub-smale-tau9/audit/flint_roots.py FILE 5 --workers 6
```

Accepts `P <c0> <c1> ...` bare coefficient lists, COMPACT SLPs, and legacy SLPs (`h1 h2 h3 | g1 = 1 + x; ...`). Asserts `processed == nonempty_lines` and fails loudly on any error.

## Summary of Results ($\tau = 1 \dots 7$)

| $\tau$ | $\|L_\tau\|$ | $\|\mathrm{New}(\tau)\|$ | $\|\mathrm{New}^\pm(\tau)\|$ | $z_{\max}(\tau)$ | Witness SLP (COMPACT) | Witness Polynomial (ascending) | Time (s) |
|---:|---:|---:|---:|---:|---|---|---:|
| 1 | 6 | 6 | 5 | 1 | `0` | `0 1` ($x$) | 0.21 |
| 2 | 59 | 27 | 20 | 2 | `2 a0.1 m1.2` | `0 1 1` ($x + x^2$) | 0.20 |
| 3 | 805 | 150 | 104 | 3 | `3 m1.1 s0.2 m1.3` | `0 1 0 -1` ($x - x^3$) | 0.21 |
| 4 | 15,144 | 1,084 | 716 | 3 | `3 m1.1 s0.2 m1.3` | `0 1 0 -1` ($x - x^3$) | 0.21 |
| 5 | 377,992 | 10,134 | 6,409 | 4 | `5 s0.1 m2.2 s1.3 m4.4 s0.5` | `0 6 -11 6 -1` ($-x(x-1)(x-2)(x-3)$) | 0.26 |
| 6 | 12,008,914 | 122,339 | 74,275 | 5 | `6 a0.0 m1.1 s2.3 m4.4 s3.5 m1.6` | `0 -4 0 5 0 -1` ($-x(x^2-1)(x^2-4)$) | 1.61 |
| 7 | 469,476,460 | 1,866,020 | 1,092,330 | 5 | `6 a0.0 m1.1 s2.3 m4.4 s3.5 m1.6` | `0 -4 0 5 0 -1` ($-x(x^2-1)(x^2-4)$) | 156.22 |

Note: $\tau(0) = 1$; the zero polynomial is excluded from all counts above.

## Feasibility of $\tau = 8$

See `results/tau8_infeasibility.json`. Under the deliberately naive state-set algorithm (no sign symmetry, no operand ordering, no canonicalization), $|L_7| = 469,476,460$ states:
- Storing deduplicated $L_7$ as `[u32; 8]` takes **15.02 GB** RAM, and building/sorting/deduplicating $L_7$ from $L_6$ peaks at **>32 GB** RAM (exceeding the 20 GB RAM cap).
- Expanding $L_7$ to $L_8$ requires $469.5\text{M} \times 9 \times 9 \times 3 \approx 1.14 \times 10^{11}$ polynomial operations (~32 min per pass on 6 threads), and fitting $\mathrm{New}(8)$ ($\sim 30\text{M}$ polys) and interned-child states within 20 GB RAM requires $\ge 8$ hash-bucket passes (**>4 hours** wall time, exceeding the 1.5h budget).
