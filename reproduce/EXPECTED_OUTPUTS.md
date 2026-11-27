# Expected Outputs for `reproduce/reproduce.sh`

All runs below were verified on Apple M3 Pro (12 cores, 36 GB RAM) using `tau_certify_exact.c` (`cc -O3 -march=native -pthread -Wall -Wextra -Werror`), `verify_survivors.py`, `audit/naive_tau` (`cargo build --release`), and `audit/flint_roots.py` (`python-flint 0.9.0`).

## 1. Independent Naive Rust Enumerator (`audit/naive_tau`, $\tau = 1 \dots 7$)

| $\tau$ | $|L_\tau|$ | $|\mathrm{New}(\tau)|$ | $|\mathrm{New}^\pm(\tau)|$ | C Dump $|\mathrm{DumpSet}^\pm|$ | Missing (`New± \ Dump`) | Extra (`Dump \ ∪New±`) | $z_{\max}(\tau)$ |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 1 | 6 | 6 | 5 | 5 | 0 | 0 | 1 |
| 2 | 59 | 27 | 20 | 21 | 0 | 0 | 2 |
| 3 | 805 | 150 | 104 | 127 | 0 | 0 | 3 |
| 4 | 15,144 | 1,084 | 716 | 842 | 0 | 0 | 3 |
| 5 | 377,992 | 10,134 | 6,409 | 7,254 | 0 | 0 | 4 |
| 6 | 12,008,914 | 122,339 | 74,275 | 81,529 | 0 | 0 | 5 |
| 7 | 469,476,460 | 1,866,020 | 1,092,330 | 1,173,859 | 0 | 0 | 5 |

## 2. Exact-CRT Certifier (`tau_certify_exact`, $K = 6$, $\tau = 1 \dots 9$)

All `dup_false_positive`, `zero_false_positive`, and `surv_false_positive` counters must be `0`, and `conservation_check` must be `PASS`.

| $\tau$ | `nodes_visited` (+prefix) | `leaves_checked` | `survivors_raw` | `survivors_uniq` | `dup_hash_hits` (`FP`) | `verify_survivors.py` CE | `flint_roots.py` `max_z` (hits) |
|---:|---:|---:|---:|---:|---:|---:|---|
| 1 | 0 | 7 | 0 | 0 | 0 (0) | 0 | — |
| 2 | 5 | 40 | 0 | 0 | 2 (0) | 0 | — |
| 3 | 44 | 349 | 0 | 0 | 26 (0) | 0 | — |
| 4 | 519 | 4,560 | 0 | 0 | 236 (0) | 0 | — |
| 5 | 8,676 (+44) | 78,543 | 2 | 2 | 3,158 (0) | 0 | 3 (0) |
| 6 | 195,403 (+44) | 1,724,358 | 476 | 172 | 57,001 (0) | 0 | 3 (0) |
| 7 | 5,531,334 (+44) | 46,799,099 | 45,675 | 9,237 | 1,347,164 (0) | 0 | 4 (0) |
| 8 | 190,402,194 (+529) | 1,531,518,439 | 3,452,422 | 342,991 | 39,947,616 (0) | 0 | 5 (0) |
| **9** | **7,767,648,995** (+529) | **59,308,136,697** | **235,889,807** | **28,755,668** (per-item) | **1,432,372,962** (0) | **0** (`max_exact_hensel=5`) | **6** (0) |

### Detailed $\tau = 9, K = 6$ Breakdown (Default & `-DALT_PRIMES`, `per-item diff == 0`)

- `work_items`: `485 / 485` (`split = 3`)
- `prefix_nodes`: `529` (`nodes_total = 7,767,649,524`)
- `cert_deg`: `44,427,829,968` (74.91%)
- `cert_prod`: `6,343,706,401` (10.70%)
- `cert_p31`: `4,178,330,044` (7.05%)
- `cert_taylor31`: `2,991,794,570` (5.04%)
- `cert_dup_zero`: `221,875,029` (0.37%)
- `cert_p19`: `675,427,005` (1.1388%)
- `cert_p23`: `213,548,025` (0.3601%)
- `cert_p29`: `19,735,848` (0.0333%)
- `survivors_raw`: `235,889,807`
- `survivors_uniq` (per-item deduped): `28,755,668`
- `verify_survivors.py`: `deg=3,255,332`, `sqf_deg=9,315,446`, `sqf_mod=15,506,965`, `hensel_ok=677,925`, `COUNTEREXAMPLE=0`, `accounting_check=PASS`.
- `flint_roots.py`: `HIST 0: 2,752,412; 1: 15,722,336; 2: 7,715,229; 3: 2,364,256; 4: 104,544; 5: 5,635; 6: 65`, `max_z=6`, `hits=0`.

## 3. Lean 4.36.0 Verification

```bash
lake exe cache get
lake build Research
```

Expected: 8 modules under `Research/PvsNP/Tau/` (4,228 LOC, 204 theorem/lemma declarations), `0 sorry`, strictly `{propext, Classical.choice, Quot.sound}`.

## 4. $\tau = 10, K = 7$ (Exact-CRT, 18 Batches / 8,774 Items)

- `work_items`: `8,774 / 8,774` (`split = 4`)
- `prefix_nodes`: `9,303` (`nodes_total = 368,616,396,762`, `nodes_visited = 368,616,387,459`)
- `leaves_checked`: `2,675,837,421,376` (`conservation_check = PASS`)
- `cert_deg`: `1,956,601,429,194` (73.12%)
- `cert_prod`: `301,560,591,276` (11.27%)
- `cert_p31`: `221,045,840,732` (8.26%)
- `cert_taylor31`: `137,831,162,613` (5.15%)
- `cert_dup_zero`: `9,737,432,438` (0.36%)
- `cert_p19`: `28,243,748,808` (1.0555%)
- `cert_p23`: `7,799,738,507` (0.2915%)
- `cert_p29`: `965,278,098` (0.0361%)
- `survivors_raw`: `12,052,199,710`
- `survivors_uniq` (per-item deduped): `1,333,049,433`
- `dup_hash_hits`: `58,105,780,935` (`dup_exact_confirmed = 58,105,780,935`, `dup_false_positive = 0`)
- `surv_hash_hits`: `10,719,150,277` (`surv_exact_confirmed = 10,719,150,277`, `surv_false_positive = 0`)
- `audit/flint_roots.py` (all 18 batches, `processed == nonempty == 1,333,049,433`):
  - `HIST z=0: 131,545,405; z=1: 724,188,908; z=2: 356,137,666; z=3: 109,874,319; z=4: 5,102,526; z=5: 259,635; z=6: 7,670; z=7: 19`
  - `skipped_deg_le_7 = 5,933,285`, `factored = 1,327,116,148`, `max_z = 7`, `hits = 0` (`z_max(10) = 7`).
