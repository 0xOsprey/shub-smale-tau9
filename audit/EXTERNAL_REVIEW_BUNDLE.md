# External Adversarial Review Bundle (Copy-Paste Ready for a Second Model or Human Mathematician)

> **How to use this file:** Copy everything below the horizontal rule and paste it into a **completely different AI model** (e.g., Claude / GPT / o3 in a fresh session) or send it to a human mathematician. It contains verbatim Lean 4 definitions/theorems and **excerpts** of the C core (`dfs`, `check_leaf`, `exact_check_rel`, `compute_hash_and_check_dup_ex`) that sit at the trust boundary of $z_{\max}(9) = 6$ and $z_{\max}(10) = 7$. Pinned full-source links (commit `0ee42a8`) are provided for every excerpted block.

---

## Prompt for External Reviewer

You are reviewing an AI-assisted computational proof of $z_{\max}(9) = 6$ and $z_{\max}(10) = 7$ for the Shub–Smale $\tau$-conjecture (Smale's 4th Problem), extending Santibáñez-Leal (2026). Lean 4.36.0's kernel already checked the proofs (`0 sorry`, strictly `{propext, Classical.choice, Quot.sound}`), and `python-flint` (`libflint`) verified all surviving polynomials.

**Your job is to try to BREAK this result.** Do NOT assume it is correct. Specifically audit the 4 things that Lean's kernel does NOT check:
1. **Faithfulness of Lean definitions (`Section 1`):** Do `SLPOp`, `SLP`, `evalWire`, `evalPoly`, `intRootCount`, `zMaxGe`, `GateSpec`, `wireVals`, `output`, and `Canonical` accurately capture constant-free SLPs over $\{1, x\}$ with $\{+, -, \times\}$ and distinct integer roots over all of $\mathbb{Z}$, with NO hidden loophole or vacuous hypothesis?
2. **Faithfulness of `zmax9_le_six_of_checklist` / `zmax10_le_seven_of_checklist` (`Section 2`):** Does the Lean statement genuinely imply $z_{\max}(9) \le 6$ and $z_{\max}(10) \le 7$ if every canonical gate list of length $1 \le n \le \tau$ is certified?
3. **Correspondence between Lean `Canonical` and C `dfs()` (`Section 3`):** Could ANY `Canonical` gate list `gs` of length `tau` (`1 <= tau <= 10`) be missed by `dfs()`? Check sign canonicalization, dead-gate pruning (`max_unused_after = rem_after + 1`, leaf cases `unused_cnt == 2 / 0 / else`), lex-key pruning (`k = (op<<10)|(i<<5)|j`, `uses_prev`), and `compute_hash_and_check_dup`.
4. **Soundness of `check_leaf()` and `exact_check_rel()` (`Section 4`):** Could ANY nonzero polynomial with $> K$ distinct integer roots in $\mathbb{Z}$ be falsely certified by `cert_deg`, `cert_prod`, mod-31 fast path, `cert_dup_zero`, `cert_taylor`, or fallback primes `{19, 23, 29}`? Could `exact_check_rel()` falsely declare two unequal polynomials equal (check `deg_ub`, `nb`, CRT prime count `r = (max_nb+2)/60 + 1` with primes in `(2^60, 2^61)`, and `eval_q0` caching)?

For every issue found, give a concrete counterexample or exact line numbers. If you find no fatal flaw, explicitly state what remains unverified.

---

## Section 1 — Verbatim Lean 4 Core Definitions (`Research/PvsNP/Tau/TauConjecture.lean`, lines 23–145)

```lean
inductive SLPOp
  | add
  | sub
  | mul
  deriving DecidableEq, Repr

noncomputable def SLPOp.applyPoly : SLPOp → Polynomial ℤ → Polynomial ℤ → Polynomial ℤ
  | .add, p, q => p + q
  | .sub, p, q => p - q
  | .mul, p, q => p * q

inductive SLP : ℕ → Type
  | nil : SLP 0
  | snoc {τ : ℕ} (P : SLP τ) (op : SLPOp) (i j : Fin (τ + 2)) : SLP (τ + 1)
  deriving DecidableEq, Repr

noncomputable def SLP.evalWire : {τ : ℕ} → SLP τ → Fin (τ + 2) → Polynomial ℤ
  | 0, .nil, k => if k.val = 0 then 1 else Polynomial.X
  | τ + 1, .snoc P op i j, k =>
      if h : k.val < τ + 2 then
        P.evalWire ⟨k.val, h⟩
      else
        op.applyPoly (P.evalWire i) (P.evalWire j)

noncomputable def SLP.evalPoly {τ : ℕ} (P : SLP τ) : Polynomial ℤ :=
  P.evalWire ⟨τ + 1, Nat.lt_succ_self _⟩

noncomputable def intRootSet (f : Polynomial ℤ) : Finset ℤ :=
  f.roots.toFinset

noncomputable def intRootCount (f : Polynomial ℤ) : ℕ :=
  (intRootSet f).card

def zMaxGe (τ r : ℕ) : Prop :=
  ∃ P : SLP τ, P.evalPoly ≠ 0 ∧ r ≤ intRootCount P.evalPoly
```

---

## Section 2 — Verbatim Lean 4 `Canonical` Predicate & Checklist Theorems (`Research/PvsNP/Tau/Canonical.lean`)

```lean
-- lines 32-57
structure GateSpec where
  op : SLPOp
  i : ℕ
  j : ℕ
  deriving DecidableEq, Repr

noncomputable def wireValsAux : List (Polynomial ℤ) → List GateSpec → List (Polynomial ℤ)
  | acc, [] => acc
  | acc, g :: rest =>
      wireValsAux (acc ++ [g.op.applyPoly (acc.getD g.i 0) (acc.getD g.j 0)]) rest

noncomputable def wireVals (gs : List GateSpec) : List (Polynomial ℤ) :=
  wireValsAux [1, Polynomial.X] gs

noncomputable def output (gs : List GateSpec) : Polynomial ℤ :=
  (wireVals gs).getD (gs.length + 1) 0

def WellFormed (gs : List GateSpec) : Prop :=
  ∀ (k : ℕ) (hk : k < gs.length), gs[k].i < k + 2 ∧ gs[k].j < k + 2

-- lines 260-330
def SLPOp.idx : SLPOp → ℕ
  | .add => 0
  | .sub => 1
  | .mul => 2

def GateSpec.Ord (g : GateSpec) : Prop :=
  match g.op with
  | .sub => g.i < g.j
  | .add | .mul => g.i ≤ g.j

def GateSpec.keyLe (g₁ g₂ : GateSpec) : Prop :=
  g₁.op.idx < g₂.op.idx ∨
  (g₁.op.idx = g₂.op.idx ∧ (g₁.i < g₂.i ∨ (g₁.i = g₂.i ∧ g₁.j ≤ g₂.j)))

def OrdCanonical (gs : List GateSpec) : Prop :=
  ∀ (k : ℕ) (hk : k < gs.length), gs[k].Ord

def NonzeroWires (gs : List GateSpec) : Prop :=
  ∀ (k : ℕ) (hk : k < gs.length), (wireVals gs).getD (k + 2) 0 ≠ 0

def NodupWires (gs : List GateSpec) : Prop :=
  ∀ (k : ℕ) (hk : k < gs.length) (m : ℕ), m < k + 2 →
    (wireVals gs).getD (k + 2) 0 ≠ (wireVals gs).getD m 0 ∧
    (wireVals gs).getD (k + 2) 0 ≠ -((wireVals gs).getD m 0)

def UsedGates (gs : List GateSpec) : Prop :=
  ∀ (k : ℕ), k + 1 < gs.length →
    ∃ (k' : ℕ) (hk' : k' < gs.length), k < k' ∧ (gs[k'].i = k + 2 ∨ gs[k'].j = k + 2)

def LexOrdered (gs : List GateSpec) : Prop :=
  ∀ (k : ℕ), 1 ≤ k → k + 1 < gs.length →
    (h1 : k - 1 < gs.length) → (h2 : k < gs.length) →
    gs[k].i ≠ k + 1 → gs[k].j ≠ k + 1 → (gs[k - 1]'h1).keyLe (gs[k]'h2)

structure Canonical (gs : List GateSpec) : Prop where
  wf : WellFormed gs
  ord : OrdCanonical gs
  nonzero : NonzeroWires gs
  nodup : NodupWires gs
  used : UsedGates gs
  lex : LexOrdered gs

-- lines 1823-1840 (verified with 0 sorry, axioms: [propext, Classical.choice, Quot.sound])
theorem zmax9_le_six_of_checklist
    (hcheck : ∀ gs : List GateSpec, Canonical gs → 1 ≤ gs.length → gs.length ≤ 9 →
      output gs ≠ 0 → intRootCount (output gs) ≤ 6) :
    ∀ t ≤ 9, ∀ P : SLP t, P.evalPoly ≠ 0 → intRootCount P.evalPoly ≤ 6

theorem zmax10_le_seven_of_checklist
    (hcheck : ∀ gs : List GateSpec, Canonical gs → 1 ≤ gs.length → gs.length ≤ 10 →
      output gs ≠ 0 → intRootCount (output gs) ≤ 7) :
    ∀ t ≤ 10, ∀ P : SLP t, P.evalPoly ≠ 0 → intRootCount P.evalPoly ≤ 7
```

---

## Section 3 — C DFS Enumeration Loop Excerpt (`experiments/pvsnp/tau/tau_certify_exact.c`, lines 1300–1430; mutation/dump `#ifdef`s omitted)

Pinned full unabridged source: https://github.com/0xOsprey/shub-smale-tau9/blob/0ee42a8/experiments/pvsnp/tau/tau_certify_exact.c#L1300-L1430

```c
static inline void check_leaf_pair(SearchCtx *ctx, int depth, int idx, int i, int j) {
    check_leaf(ctx, depth, idx, 0, i, j);
    if (i != j) check_leaf(ctx, depth, idx, 1, i, j);
    check_leaf(ctx, depth, idx, 2, i, j);
}

static void dfs(SearchCtx *ctx, int depth, uint32_t unused_mask, int unused_cnt) {
    int tau = ctx->target_tau;
    int idx = depth + 2;
    int rem_after = tau - 1 - depth;
    int max_unused_after = rem_after + 1;
    int prev_idx = idx - 1;

    if (depth == tau - 1) {
        if (unused_cnt > 2) return;
        if (unused_cnt == 2) {
            int i = __builtin_ctz(unused_mask);
            int j = __builtin_ctz(unused_mask ^ (1U << i));
            check_leaf_pair(ctx, depth, idx, i, j);
            return;
        }
        if (unused_cnt == 0) {
            for (int i = 0; i < idx; i++) {
                for (int j = i; j < idx; j++) {
                    check_leaf_pair(ctx, depth, idx, i, j);
                }
            }
            return;
        }
        int u0 = __builtin_ctz(unused_mask);
        for (int other = 0; other < idx; other++) {
            int i = other < u0 ? other : u0;
            int j = other < u0 ? u0 : other;
            check_leaf_pair(ctx, depth, idx, i, j);
        }
        return;
    }

    int min_removed = unused_cnt + 1 - max_unused_after;

    for (int i = 0; i < idx; i++) {
        int ui = (int)((unused_mask >> i) & 1U);
        if (min_removed == 2 && !ui) continue;
        for (int j = i; j < idx; j++) {
            int uj = (int)((unused_mask >> j) & 1U);
            int removed = (i == j) ? ui : (ui + uj);
            if (removed < min_removed) continue;

            int uses_prev = (depth > 0) && (i == prev_idx || j == prev_idx);

            for (int op = 0; op < 3; op++) {
                if (op == 1 && i == j) continue;
                int k = (op << 10) | (i << 5) | j;
                if (depth > 0 && !uses_prev && k < ctx->key[depth - 1]) continue;

                uint32_t r1;
                uint64_t r2;
                if (!compute_hash_and_check_dup(ctx, idx, op, i, j, &r1, &r2)) continue;

                ctx->st.nodes_visited++;
                ctx->h1[idx] = r1;
                ctx->h2[idx] = r2;
                ctx->nh1[idx] = r1 == 0 ? 0 : MP - r1;
                ctx->nh2[idx] = r2 == 0 ? 0 : P2 - r2;
                ctx->path[depth] = (Gate){op, i, j};
                ctx->key[depth] = k;

                eval_gate_p1(ctx, idx, op, i, j);

                uint32_t next_mask = (unused_mask & ~(1U << i) & ~(1U << j)) | (1U << idx);
                int next_cnt = unused_cnt - removed + 1;
                dfs(ctx, depth + 1, next_mask, next_cnt);
            }
        }
    }
}
```
*(Mutation/dump `#ifdef` blocks omitted for readability; default production build has none defined. `collect_work()` uses the exact same loop down to `split_depth`, and `worker_fn()` replays each prefix via `compute_hash_only` + `eval_gate_p1` before calling `dfs()`.)*

---

## Section 4 — C Leaf Certifier & Exact-CRT Confirm-on-Hit Excerpt (`tau_certify_exact.c`, lines 641–853 & 1150–1298; ellipses at `eval_q0` / inner CRT loop / `known_doubles`)

Pinned full unabridged source:
- `exact_check_rel` & `compute_hash_and_check_dup_ex`: https://github.com/0xOsprey/shub-smale-tau9/blob/0ee42a8/experiments/pvsnp/tau/tau_certify_exact.c#L641-L853
- `check_leaf`: https://github.com/0xOsprey/shub-smale-tau9/blob/0ee42a8/experiments/pvsnp/tau/tau_certify_exact.c#L1150-L1298
- `certify_taylor_roots` & `certify_slp_mod_p`: https://github.com/0xOsprey/shub-smale-tau9/blob/0ee42a8/experiments/pvsnp/tau/tau_certify_exact.c#L955-L1147

```c
/* Exact CRT check: returns 1 iff candidate gate (op,i,j) == 0 (sign==0) or sign*wire[target_m] (sign=+-1).
 * Precondition: 40 distinct hard-coded primes EXACT_PRIMES[0..39] in (2^60, 2^61), EXACT_PRIMES[0] = 2^61 - 1.
 * deg_ub[w] >= deg(wire[w]); ||wire[w]||_1 <= 2^{nb[w]} (nb[0]=nb[1]=0, add/sub: max+1, mul: sum). */
static int exact_check_rel(SearchCtx *ctx, int idx, int op, int i, int j,
                           int target_m, int sign) {
    uint16_t cand_deg = (op == 2)
        ? (uint16_t)(ctx->deg_ub[i] + ctx->deg_ub[j])
        : (ctx->deg_ub[i] > ctx->deg_ub[j] ? ctx->deg_ub[i] : ctx->deg_ub[j]);
    uint32_t cand_nb = (op == 2)
        ? (ctx->nb[i] + ctx->nb[j])
        : ((ctx->nb[i] > ctx->nb[j] ? ctx->nb[i] : ctx->nb[j]) + 1U);

    int D;
    uint32_t max_nb;
    if (sign == 0) { D = (int)cand_deg; max_nb = cand_nb; }
    else {
        uint16_t md = ctx->deg_ub[target_m];
        uint32_t mn = ctx->nb[target_m];
        D = (cand_deg > md) ? (int)cand_deg : (int)md;
        max_nb = (cand_nb > mn) ? cand_nb : mn;
    }

    int r = (int)((max_nb + 2U) / 60U) + 1;
    if (r > NUM_EXACT_PRIMES) exit(3);

    int start_p = 0;
    if (D <= Q0_CACHE_MAX_D) {
        ensure_q0_cache(ctx, idx, D);
        /* checks t = 0..D mod (2^61 - 1); returns 0 on any mismatch; else start_p = 1 */
        ...
        start_p = 1;
    }
    uint64_t val[MAX_TAU + 2];
    for (int p_idx = start_p; p_idx < r; p_idx++) {
        uint64_t q = EXACT_PRIMES[p_idx];
        for (int t = 0; t <= D; t++) {
            val[0] = 1; val[1] = (uint64_t)t;
            for (int w = 2; w < idx; w++) { /* evaluate prefix SLP mod q at x = t */ }
            /* compute candidate v = val[i] op val[j] mod q; return 0 if v != target mod q */
        }
    }
    return 1;
}

static inline int compute_hash_and_check_dup_ex(
    SearchCtx *ctx, int idx, int op, int i, int j,
    uint32_t *out_h1, uint64_t *out_h2, int *out_reason
) {
    uint32_t r1; uint64_t r2;
    compute_hash_only(ctx, op, i, j, &r1, &r2);
    if (r1 == 0 && r2 == 0) {
        ctx->st.zero_hash_hits++;
        if (exact_check_rel(ctx, idx, op, i, j, 0, 0)) {
            ctx->st.zero_exact_confirmed++;
            if (out_reason) *out_reason = 1;
            return 0;
        }
        ctx->st.zero_false_positive++;
    }
    for (int m = 0; m < idx; m++) {
        int mp = (r1 == ctx->h1[m] && r2 == ctx->h2[m]);
        int mn = (r1 == ctx->nh1[m] && r2 == ctx->nh2[m]);
        if (mp || mn) {
            ctx->st.dup_hash_hits++;
            int eq = 0;
            if (mp && exact_check_rel(ctx, idx, op, i, j, m, 1)) eq = 1;
            else if (mn && exact_check_rel(ctx, idx, op, i, j, m, -1)) eq = 1;
            if (eq) {
                ctx->st.dup_exact_confirmed++;
                if (out_reason) *out_reason = 2;
                return 0;
            }
            ctx->st.dup_false_positive++;
        }
    }
    *out_h1 = r1; *out_h2 = r2;
    if (out_reason) *out_reason = 0;
    return 1;
}

static inline void check_leaf(SearchCtx *ctx, int depth, int idx, int op, int i, int j) {
    ctx->st.leaves_checked++;
    int K = ctx->cert_bound; /* enforced 1 <= K <= 18 < 19 */

    /* 0a: exact degree upper bound */
    int dub = (op == 2)
        ? ((int)ctx->deg_ub[i] + (int)ctx->deg_ub[j])
        : (ctx->deg_ub[i] > ctx->deg_ub[j] ? (int)ctx->deg_ub[i] : (int)ctx->deg_ub[j]);
    if (dub <= K) { ctx->st.cert_deg++; return; }

    /* 0b: atomic product-factor union bound & z(A+A) = z(A) */
    if (op == 2) {
        uint16_t pmask = ctx->prod_mask[i] | ctx->prod_mask[j];
        if (sum_mask_ub(pmask, ctx->z_ub) <= K) { ctx->st.cert_prod++; return; }
    } else if (op == 0 && i == j) {
        if (ctx->z_ub[i] <= K) { ctx->st.cert_prod++; return; }
    }

    /* 1: Simple-Root Modular Certificate mod p1 = 31 */
    const uint8_t * __restrict va = ctx->v31[i], * __restrict da = ctx->d31[i];
    const uint8_t * __restrict vb = ctx->v31[j], * __restrict db = ctx->d31[j];
    int zeros = 0, doubles = 0;
    if (op == 0) {
        for (int a = 0; a < 31; a++) {
            uint8_t sv = va[a] + vb[a], sd = da[a] + db[a];
            int iz = (sv == 0) | (sv == 31), idz = (sd == 0) | (sd == 31);
            zeros += iz; doubles += (iz & idz);
        }
    } else if (op == 1) {
        for (int a = 0; a < 31; a++) {
            int iz = (va[a] == vb[a]), idz = (da[a] == db[a]);
            zeros += iz; doubles += (iz & idz);
        }
    } else {
        for (int a = 0; a < 31; a++) {
            int za = (va[a] == 0), zb = (vb[a] == 0);
            zeros += (za | zb);
            doubles += (za & zb) | (za & (da[a] == 0)) | (zb & (db[a] == 0));
        }
    }
    if (zeros <= K && doubles == 0) { ctx->st.cert_p1++; return; }

    /* Zero / duplicate leaf (exact-CRT confirmed) */
    uint32_t r1; uint64_t r2;
    if (!compute_hash_and_check_dup(ctx, idx, op, i, j, &r1, &r2)) {
        ctx->st.cert_dup_zero++; return;
    }

    /* 1b: Taylor-stripped modular cert mod 31 (only double roots in {0, +-1, +-2, +-3},
     * overflow-checked __int128 Taylor to deg 11, lowest nonzero coeff cm has m >= 1 and cm % 31 != 0) */
    ctx->path[depth] = (Gate){op, i, j};
    if (zeros <= K && doubles > 0) {
        /* counts known_doubles at {0, 1, 30, 2, 29, 3, 28}; if known_doubles == doubles -> certify_taylor_roots */
        ...
    }

    /* Fallback primes {19, 23, 29} */
    for (int f = 0; f < NUM_FALLBACK_PRIMES; f++) {
        if (certify_slp_mod_p(ctx->path, ctx->target_tau, FALLBACK_PRIMES[f], K)) {
            ctx->st.cert_fallback[f]++; return;
        }
    }

    /* Survivor: exact-CRT deduplicated & logged for python-flint / verify_survivors.py */
    ctx->st.survivors_raw++;
    record_survivor(ctx, ctx->path, ctx->target_tau, r1, r2);
}
```
