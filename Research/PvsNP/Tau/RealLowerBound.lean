module

public import Research.PvsNP.Tau.TauConjecture
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

namespace Research.PvsNP.Tau

/-!
# Unconditional Real-Root Lower Bound Beating Chebyshev (`z_max^{ℝ}(5k + 4) ≥ 8 · 7^(k - 1)`)

Classical Chebyshev polynomials achieve `z_max^{ℝ}(τ) ≥ 2 ^ ((τ - 1) / 2)` (exponential growth
rate `α_ℝ ≥ 1/2 = 0.50`, base `√2 ≈ 1.4142`).

This module formalizes the constant-free `5`-gate-per-step family **`5C`**:
- `u(y) = y * (4 - y)`
- `Q(y) = (u(y) * (u(y) - 3)) ^ 2`
- `f_k(x) = Q^[k](x) - 1`

which has constant-free SLP length `τ(f_k) = 5 * k + 4` and at least `8 * 7 ^ (k - 1)` distinct
real roots for every `k ≥ 1`, improving the unconditional real-root exponential rate to
`α_ℝ ≥ (log_2 7) / 5 ≈ 0.56147 > 0.50` (base `7^(1/5) ≈ 1.4758 > √2`).

The proof is completely elementary: for every `t ∈ (0, 5)`, the eight preimages of `Q(y) = t`
are constructed explicitly via nested square roots and placed in one strictly increasing chain
`y4m < 0 < y1m < y2m < y3m < 2 < y3p < y2p < y1p < 4 < y4p < 5`, yielding seven distinct
preimages inside `(0, 5)` and one additional preimage in `(-1, 0)`.
-/

/-! ## 1. Wire-Evaluation Helpers & Constant-Free SLP of Length `5k + 4` -/

theorem SLP.evalWire_snoc_lt {τ : ℕ} (P : SLP τ) (op : SLPOp) (i j : Fin (τ + 2))
    (k : Fin (τ + 3)) (hk : k.val < τ + 2) :
    (P.snoc op i j).evalWire k = P.evalWire ⟨k.val, hk⟩ := by
  simp [SLP.evalWire, hk]

theorem SLP.evalWire_snoc_last {τ : ℕ} (P : SLP τ) (op : SLPOp) (i j : Fin (τ + 2))
    (k : Fin (τ + 3)) (hk : k.val = τ + 2) :
    (P.snoc op i j).evalWire k = op.applyPoly (P.evalWire i) (P.evalWire j) := by
  have hnot : ¬ k.val < τ + 2 := by omega
  simp [SLP.evalWire, hnot]

/-- One iteration of the 5-gate polynomial map `Q₅C(w) = (w(4 - w) · (w(4 - w) - 3)) ^ 2`. -/
noncomputable def q5cStep (w : Polynomial ℤ) : Polynomial ℤ :=
  let u := w * (4 - w)
  (u * (u - 3)) ^ 2

/-- `k`-fold iterate `Q₅C^[k](X)` in `ℤ[X]`. -/
noncomputable def real5CPoly : ℕ → Polynomial ℤ
  | 0 => Polynomial.X
  | k + 1 => q5cStep (real5CPoly k)

/-- Append one 5-gate `5C` iteration to an arbitrary `P : SLP τ` given wires `i3`, `i4`, `iw`. -/
def real5CStepSLP {τ : ℕ} (P : SLP τ) (i3 i4 iw : Fin (τ + 2)) : SLP (τ + 5) :=
  let s1 : SLP (τ + 1) := .snoc P .sub i4 iw
  let s2 : SLP (τ + 2) := .snoc s1 .mul ⟨iw.val, by omega⟩ ⟨τ + 2, by omega⟩
  let s3 : SLP (τ + 3) := .snoc s2 .sub ⟨τ + 3, by omega⟩ ⟨i3.val, by omega⟩
  let s4 : SLP (τ + 4) := .snoc s3 .mul ⟨τ + 3, by omega⟩ ⟨τ + 4, by omega⟩
  .snoc s4 .mul ⟨τ + 5, by omega⟩ ⟨τ + 5, by omega⟩

theorem real5CStepSLP_evalWire_lt {τ : ℕ} (P : SLP τ) (i3 i4 iw : Fin (τ + 2))
    (k : Fin (τ + 7)) (hk : k.val < τ + 2) :
    (real5CStepSLP P i3 i4 iw).evalWire k = P.evalWire ⟨k.val, hk⟩ := by
  unfold real5CStepSLP
  dsimp only
  rw [SLP.evalWire_snoc_lt _ _ _ _ _ (by omega),
      SLP.evalWire_snoc_lt _ _ _ _ _ (by dsimp; omega),
      SLP.evalWire_snoc_lt _ _ _ _ _ (by dsimp; omega),
      SLP.evalWire_snoc_lt _ _ _ _ _ (by dsimp; omega),
      SLP.evalWire_snoc_lt _ _ _ _ _ (by dsimp; omega)]

theorem real5CStepSLP_evalPoly {τ : ℕ} (P : SLP τ) (i3 i4 iw : Fin (τ + 2))
    (h3 : P.evalWire i3 = 3) (h4 : P.evalWire i4 = 4) :
    (real5CStepSLP P i3 i4 iw).evalPoly = q5cStep (P.evalWire iw) := by
  unfold SLP.evalPoly real5CStepSLP
  dsimp only
  set s1 : SLP (τ + 1) := .snoc P .sub i4 iw
  set s2 : SLP (τ + 2) := .snoc s1 .mul ⟨iw.val, by omega⟩ ⟨τ + 2, by omega⟩
  set s3 : SLP (τ + 3) := .snoc s2 .sub ⟨τ + 3, by omega⟩ ⟨i3.val, by omega⟩
  set s4 : SLP (τ + 4) := .snoc s3 .mul ⟨τ + 3, by omega⟩ ⟨τ + 4, by omega⟩
  have hs1 : s1.evalWire ⟨τ + 2, by omega⟩ = 4 - P.evalWire iw := by
    rw [SLP.evalWire_snoc_last _ _ _ _ _ rfl]
    simp [SLPOp.applyPoly, h4]
  have hs2 : s2.evalWire ⟨τ + 3, by omega⟩ = P.evalWire iw * (4 - P.evalWire iw) := by
    rw [SLP.evalWire_snoc_last _ _ _ _ _ rfl]
    simp only [SLPOp.applyPoly, hs1]
    rw [SLP.evalWire_snoc_lt _ _ _ _ _ iw.isLt]
  have hs3 : s3.evalWire ⟨τ + 4, by omega⟩ = P.evalWire iw * (4 - P.evalWire iw) - 3 := by
    rw [SLP.evalWire_snoc_last _ _ _ _ _ rfl]
    simp only [SLPOp.applyPoly, hs2]
    have hi3 : i3.val < τ + 2 := i3.isLt
    rw [SLP.evalWire_snoc_lt _ _ _ _ _ (by dsimp; omega),
        SLP.evalWire_snoc_lt _ _ _ _ _ (by dsimp; omega), h3]
  have hs4 : s4.evalWire ⟨τ + 5, by omega⟩ =
      P.evalWire iw * (4 - P.evalWire iw) * (P.evalWire iw * (4 - P.evalWire iw) - 3) := by
    rw [SLP.evalWire_snoc_last _ _ _ _ _ rfl]
    simp only [SLPOp.applyPoly, hs3]
    rw [SLP.evalWire_snoc_lt _ _ _ _ _ (by dsimp; omega), hs2]
  rw [SLP.evalWire_snoc_last _ _ _ _ _ rfl]
  simp only [SLPOp.applyPoly, hs4, q5cStep, sq]

/-- Wire index holding `real5CPoly k` inside `real5CBaseSLP k`. -/
def real5CWire (k : ℕ) : ℕ :=
  if k = 0 then 1 else 5 * k + 4

/-- Constant-free SLP of length `5 * k + 3` computing `3` at wire `3`, `4` at wire `4`,
and `real5CPoly k` at wire `real5CWire k`. -/
def real5CBaseSLP : (k : ℕ) → SLP (5 * k + 3)
  | 0 =>
      let p1 : SLP 1 := .snoc .nil .add ⟨0, by omega⟩ ⟨0, by omega⟩   -- w2 = 2
      let p2 : SLP 2 := .snoc p1 .add ⟨2, by omega⟩ ⟨0, by omega⟩     -- w3 = 3
      .snoc p2 .add ⟨2, by omega⟩ ⟨2, by omega⟩                       -- w4 = 4
  | k + 1 =>
      real5CStepSLP (real5CBaseSLP k) ⟨3, by omega⟩ ⟨4, by omega⟩
        ⟨real5CWire k, by dsimp [real5CWire]; split_ifs <;> omega⟩

/-- Constant-free SLP of length `5 * k + 4` computing `real5CPoly k - 1`. -/
def real5CSLP (k : ℕ) : SLP (5 * k + 4) :=
  .snoc (real5CBaseSLP k) .sub
    ⟨real5CWire k, by dsimp [real5CWire]; split_ifs <;> omega⟩
    ⟨0, by omega⟩

theorem real5CBaseSLP_wires (k : ℕ) :
    (real5CBaseSLP k).evalWire ⟨3, by omega⟩ = (3 : Polynomial ℤ) ∧
    (real5CBaseSLP k).evalWire ⟨4, by omega⟩ = (4 : Polynomial ℤ) ∧
    (real5CBaseSLP k).evalWire ⟨real5CWire k, by dsimp [real5CWire]; split_ifs <;> omega⟩ =
      real5CPoly k := by
  induction k with
  | zero =>
      refine ⟨?_, ?_, ?_⟩
      · simp [real5CBaseSLP, SLP.evalWire, SLPOp.applyPoly]; norm_num
      · simp [real5CBaseSLP, SLP.evalWire, SLPOp.applyPoly]; norm_num
      · simp [real5CBaseSLP, real5CWire, SLP.evalWire, real5CPoly]
  | succ k ih =>
      rcases ih with ⟨h3, h4, hW⟩
      refine ⟨?_, ?_, ?_⟩
      · simpa [real5CBaseSLP] using
          (real5CStepSLP_evalWire_lt (real5CBaseSLP k) ⟨3, by omega⟩ ⟨4, by omega⟩
            ⟨real5CWire k, by dsimp [real5CWire]; split_ifs <;> omega⟩
            ⟨3, by omega⟩ (by dsimp; omega)).trans h3
      · simpa [real5CBaseSLP] using
          (real5CStepSLP_evalWire_lt (real5CBaseSLP k) ⟨3, by omega⟩ ⟨4, by omega⟩
            ⟨real5CWire k, by dsimp [real5CWire]; split_ifs <;> omega⟩
            ⟨4, by omega⟩ (by dsimp; omega)).trans h4
      · have hfin : (⟨real5CWire (k + 1), by dsimp [real5CWire]; omega⟩ :
            Fin (5 * (k + 1) + 3 + 2)) = ⟨(5 * k + 3) + 5 + 1, by omega⟩ := by
          ext; simp [real5CWire]; omega
        rw [hfin]
        simpa [real5CBaseSLP, SLP.evalPoly, real5CPoly, hW] using
          real5CStepSLP_evalPoly (real5CBaseSLP k) ⟨3, by omega⟩ ⟨4, by omega⟩
            ⟨real5CWire k, by dsimp [real5CWire]; split_ifs <;> omega⟩ h3 h4

theorem real5CSLP_evalPoly (k : ℕ) : (real5CSLP k).evalPoly = real5CPoly k - 1 := by
  unfold SLP.evalPoly real5CSLP
  rw [SLP.evalWire_snoc_last _ _ _ _ _ rfl]
  simp only [SLPOp.applyPoly]
  rw [(real5CBaseSLP_wires k).2.2]
  have h0 : (⟨0, by omega⟩ : Fin (5 * k + 3 + 2)) = 0 := rfl
  rw [h0, (real5CBaseSLP k).evalWire_zero]

theorem real5CPoly_eval_zero (k : ℕ) : (real5CPoly k).eval 0 = 0 := by
  induction k with
  | zero => simp [real5CPoly]
  | succ k ih =>
      simp [real5CPoly, q5cStep, ih]

theorem real5CSLP_ne_zero (k : ℕ) : (real5CSLP k).evalPoly ≠ 0 := by
  rw [real5CSLP_evalPoly]
  intro h0
  have hev := congrArg (fun p : Polynomial ℤ => p.eval 0) h0
  simp [real5CPoly_eval_zero] at hev

/-! ## 2. Real 1D 7-Branch Horseshoe on `(0, 5)` -/

/-- Real evaluation of one `5C` step: `q5c y = (y(4 - y) · (y(4 - y) - 3)) ^ 2`. -/
def q5c (y : ℝ) : ℝ :=
  (y * (4 - y) * (y * (4 - y) - 3)) ^ 2

theorem aeval_real5CPoly (k : ℕ) (r : ℝ) :
    Polynomial.aeval r (real5CPoly k) = q5c^[k] r := by
  induction k with
  | zero => simp [real5CPoly]
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      simp only [real5CPoly, q5cStep, q5c, map_pow, map_mul, map_sub, map_ofNat, ih]

/-- For every `t ∈ (0, 5)`, `q5c y = t` admits 7 distinct solutions in `(0, 5)` and
8 distinct solutions in `ℝ` (explicitly ordered via nested square roots). -/
theorem q5c_preimages (t : ℝ) (ht0 : 0 < t) (ht5 : t < 5) :
    ∃ (S_in S_all : Finset ℝ),
      S_in.card = 7 ∧
      S_all.card = 8 ∧
      (∀ y ∈ S_in, 0 < y ∧ y < 5 ∧ q5c y = t) ∧
      (∀ y ∈ S_all, q5c y = t) := by
  classical
  let s : ℝ := Real.sqrt t
  have hs0 : 0 < s := Real.sqrt_pos.mpr ht0
  have hssq : s ^ 2 = t := Real.sq_sqrt ht0.le
  have hs_lt : s < 9 / 4 := by nlinarith only [hs0, hssq, ht5]
  have hA_pos : 0 < 9 - 4 * s := by linarith only [hs_lt]
  have hB_gt : 9 < 9 + 4 * s := by linarith only [hs0]
  have hB_lt : 9 + 4 * s < 25 := by linarith only [hs_lt]
  let d1 : ℝ := Real.sqrt (9 - 4 * s)
  let d2 : ℝ := Real.sqrt (9 + 4 * s)
  have hd1_pos : 0 < d1 := Real.sqrt_pos.mpr hA_pos
  have hd1_sq : d1 ^ 2 = 9 - 4 * s := Real.sq_sqrt hA_pos.le
  have hd1_lt : d1 < 3 := by nlinarith only [hd1_pos, hd1_sq, hs0]
  have hd2_pos : 0 < d2 := Real.sqrt_pos.mpr (by linarith only [hB_gt])
  have hd2_sq : d2 ^ 2 = 9 + 4 * s := Real.sq_sqrt (by linarith only [hB_gt])
  have hd2_gt : 3 < d2 := by nlinarith only [hd2_pos, hd2_sq, hB_gt]
  have hd2_lt : d2 < 5 := by nlinarith only [hd2_pos, hd2_sq, hB_lt]
  let u1 : ℝ := (3 - d1) / 2
  let u2 : ℝ := (3 + d1) / 2
  let u3 : ℝ := (3 + d2) / 2
  let u4 : ℝ := (3 - d2) / 2
  have hu4_gt : -1 < u4 := by dsimp [u4]; linarith only [hd2_lt]
  have hu4_lt : u4 < 0 := by dsimp [u4]; linarith only [hd2_gt]
  have hu1_gt : 0 < u1 := by dsimp [u1]; linarith only [hd1_lt]
  have hu12 : u1 < u2 := by dsimp [u1, u2]; linarith only [hd1_pos]
  have hu23 : u2 < u3 := by dsimp [u2, u3]; linarith only [hd1_lt, hd2_gt]
  have hu3_lt : u3 < 4 := by dsimp [u3]; linarith only [hd2_lt]
  have hu1_eq : u1 * (u1 - 3) = -s := by dsimp [u1]; nlinarith only [hd1_sq]
  have hu2_eq : u2 * (u2 - 3) = -s := by dsimp [u2]; nlinarith only [hd1_sq]
  have hu3_eq : u3 * (u3 - 3) = s := by dsimp [u3]; nlinarith only [hd2_sq]
  have hu4_eq : u4 * (u4 - 3) = s := by dsimp [u4]; nlinarith only [hd2_sq]
  let r1 : ℝ := Real.sqrt (4 - u1)
  let r2 : ℝ := Real.sqrt (4 - u2)
  let r3 : ℝ := Real.sqrt (4 - u3)
  let r4 : ℝ := Real.sqrt (4 - u4)
  have hr3_pos : 0 < r3 := Real.sqrt_pos.mpr (by linarith only [hu3_lt])
  have hr2_pos : 0 < r2 := Real.sqrt_pos.mpr (by linarith only [hu23, hu3_lt])
  have hr1_pos : 0 < r1 := Real.sqrt_pos.mpr (by linarith only [hu12, hu23, hu3_lt])
  have hr4_pos : 0 < r4 := Real.sqrt_pos.mpr (by linarith only [hu4_lt])
  have hr1_sq : r1 ^ 2 = 4 - u1 := Real.sq_sqrt (by linarith only [hu12, hu23, hu3_lt])
  have hr2_sq : r2 ^ 2 = 4 - u2 := Real.sq_sqrt (by linarith only [hu23, hu3_lt])
  have hr3_sq : r3 ^ 2 = 4 - u3 := Real.sq_sqrt (by linarith only [hu3_lt])
  have hr4_sq : r4 ^ 2 = 4 - u4 := Real.sq_sqrt (by linarith only [hu4_lt])
  have hr32 : r3 < r2 := by nlinarith only [hr3_pos, hr2_pos, hr3_sq, hr2_sq, hu23]
  have hr21 : r2 < r1 := by nlinarith only [hr2_pos, hr1_pos, hr2_sq, hr1_sq, hu12]
  have hr1_lt2 : r1 < 2 := by nlinarith only [hr1_pos, hr1_sq, hu1_gt]
  have hr4_gt2 : 2 < r4 := by nlinarith only [hr4_pos, hr4_sq, hu4_lt]
  have hr4_lt3 : r4 < 3 := by nlinarith only [hr4_pos, hr4_sq, hu4_gt]
  let y4m : ℝ := 2 - r4
  let y1m : ℝ := 2 - r1
  let y2m : ℝ := 2 - r2
  let y3m : ℝ := 2 - r3
  let y3p : ℝ := 2 + r3
  let y2p : ℝ := 2 + r2
  let y1p : ℝ := 2 + r1
  let y4p : ℝ := 2 + r4
  have hq : ∀ {u r y : ℝ}, r ^ 2 = 4 - u → (y = 2 - r ∨ y = 2 + r) →
      (u * (u - 3) = -s ∨ u * (u - 3) = s) → q5c y = t := by
    intro u r y hrsq hy hu
    have hyu : y * (4 - y) = u := by rcases hy with rfl | rfl <;> nlinarith only [hrsq]
    unfold q5c
    rw [hyu]
    rcases hu with h | h <;> rw [h] <;> nlinarith only [hssq]
  have hq_y4m : q5c y4m = t := hq hr4_sq (Or.inl rfl) (Or.inr hu4_eq)
  have hq_y1m : q5c y1m = t := hq hr1_sq (Or.inl rfl) (Or.inl hu1_eq)
  have hq_y2m : q5c y2m = t := hq hr2_sq (Or.inl rfl) (Or.inl hu2_eq)
  have hq_y3m : q5c y3m = t := hq hr3_sq (Or.inl rfl) (Or.inr hu3_eq)
  have hq_y3p : q5c y3p = t := hq hr3_sq (Or.inr rfl) (Or.inr hu3_eq)
  have hq_y2p : q5c y2p = t := hq hr2_sq (Or.inr rfl) (Or.inl hu2_eq)
  have hq_y1p : q5c y1p = t := hq hr1_sq (Or.inr rfl) (Or.inl hu1_eq)
  have hq_y4p : q5c y4p = t := hq hr4_sq (Or.inr rfl) (Or.inr hu4_eq)
  have hc0 : y4m < 0 := by dsimp [y4m]; linarith only [hr4_gt2]
  have hc1 : 0 < y1m := by dsimp [y1m]; linarith only [hr1_lt2]
  have hc2 : y1m < y2m := by dsimp [y1m, y2m]; linarith only [hr21]
  have hc3 : y2m < y3m := by dsimp [y2m, y3m]; linarith only [hr32]
  have hc4 : y3m < y3p := by dsimp [y3m, y3p]; linarith only [hr3_pos]
  have hc5 : y3p < y2p := by dsimp [y3p, y2p]; linarith only [hr32]
  have hc6 : y2p < y1p := by dsimp [y2p, y1p]; linarith only [hr21]
  have hc7 : y1p < y4p := by dsimp [y1p, y4p]; linarith only [hr1_lt2, hr4_gt2]
  have hc8 : y4p < 5 := by dsimp [y4p]; linarith only [hr4_lt3]
  let L_in : List ℝ := [y1m, y2m, y3m, y3p, y2p, y1p, y4p]
  let L_all : List ℝ := y4m :: L_in
  have hpair_in : L_in.Pairwise (· < ·) := by
    simp only [L_in, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, List.Pairwise.nil, false_implies, implies_true, and_true]
    repeat' constructor
    all_goals linarith only [hc2, hc3, hc4, hc5, hc6, hc7]
  have hpair_all : L_all.Pairwise (· < ·) := by
    refine List.pairwise_cons.mpr ⟨?_, hpair_in⟩
    intro x hx
    simp only [L_in, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      linarith only [hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7]
  have hnodup_in : L_in.Nodup := hpair_in.imp ne_of_lt
  have hnodup_all : L_all.Nodup := hpair_all.imp ne_of_lt
  refine ⟨L_in.toFinset, L_all.toFinset, ?_, ?_, ?_, ?_⟩
  · rw [List.toFinset_card_of_nodup hnodup_in]; rfl
  · rw [List.toFinset_card_of_nodup hnodup_all]; rfl
  · intro y hy
    rw [List.mem_toFinset] at hy
    simp only [L_in, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by linarith only [hc1], by linarith only [hc2, hc3, hc4, hc5, hc6, hc7, hc8], hq_y1m⟩
    · exact ⟨by linarith only [hc1, hc2], by linarith only [hc3, hc4, hc5, hc6, hc7, hc8], hq_y2m⟩
    · exact ⟨by linarith only [hc1, hc2, hc3], by linarith only [hc4, hc5, hc6, hc7, hc8], hq_y3m⟩
    · exact ⟨by linarith only [hc1, hc2, hc3, hc4], by linarith only [hc5, hc6, hc7, hc8], hq_y3p⟩
    · exact ⟨by linarith only [hc1, hc2, hc3, hc4, hc5], by linarith only [hc6, hc7, hc8], hq_y2p⟩
    · exact ⟨by linarith only [hc1, hc2, hc3, hc4, hc5, hc6], by linarith only [hc7, hc8], hq_y1p⟩
    · exact ⟨by linarith only [hc1, hc2, hc3, hc4, hc5, hc6, hc7], by linarith only [hc8], hq_y4p⟩
  · intro y hy
    rw [List.mem_toFinset] at hy
    simp only [L_all, L_in, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hq_y4m
    · exact hq_y1m
    · exact hq_y2m
    · exact hq_y3m
    · exact hq_y3p
    · exact hq_y2p
    · exact hq_y1p
    · exact hq_y4p

/-- `k`-step preimage tree inside `(0, 5)`: for every `k : ℕ` and `t ∈ (0, 5)`, there exist
`7 ^ k` distinct reals `r ∈ (0, 5)` with `q5c^[k] r = t`. -/
theorem q5c_iter_preimages_in (k : ℕ) :
    ∀ t : ℝ, 0 < t → t < 5 →
      ∃ S : Finset ℝ, S.card = 7 ^ k ∧ ∀ r ∈ S, 0 < r ∧ r < 5 ∧ q5c^[k] r = t := by
  classical
  induction k with
  | zero =>
      intro t ht0 ht5
      refine ⟨{t}, by simp, ?_⟩
      intro r hr
      rw [Finset.mem_singleton] at hr
      subst hr
      exact ⟨ht0, ht5, rfl⟩
  | succ k ih =>
      intro t ht0 ht5
      rcases q5c_preimages t ht0 ht5 with ⟨S_in, _, hcard_in, _, hS_in, _⟩
      choose F hF_card hF_prop using fun (y : ℝ) (hy : y ∈ S_in) =>
        ih y (hS_in y hy).1 (hS_in y hy).2.1
      let S : Finset ℝ := S_in.attach.biUnion (fun y => F y.1 y.2)
      have hdisj : Set.PairwiseDisjoint (S_in.attach : Set {y // y ∈ S_in})
          (fun y => F y.1 y.2) := by
        intro a _ b _ hab
        dsimp [Function.onFun]
        rw [Finset.disjoint_left]
        intro r hra hrb
        have ha_eq := (hF_prop a.1 a.2 r hra).2.2
        have hb_eq := (hF_prop b.1 b.2 r hrb).2.2
        exact hab (Subtype.ext (ha_eq.symm.trans hb_eq))
      refine ⟨S, ?_, ?_⟩
      · rw [Finset.card_biUnion hdisj]
        calc
          ∑ y ∈ S_in.attach, (F y.1 y.2).card
              = ∑ _y ∈ S_in.attach, 7 ^ k :=
                  Finset.sum_congr rfl (fun y _ => hF_card y.1 y.2)
          _ = S_in.attach.card * 7 ^ k := by simp
          _ = 7 ^ (k + 1) := by rw [Finset.card_attach, hcard_in, pow_succ']
      · intro r hr
        rcases Finset.mem_biUnion.mp hr with ⟨y, _, hry⟩
        have h1 := hF_prop y.1 y.2 r hry
        have h2 := hS_in y.1 y.2
        refine ⟨h1.1, h1.2.1, ?_⟩
        rw [Function.iterate_succ_apply', h1.2.2, h2.2.2]

/-- **Unconditional Real-Root Lower Bound Beating Chebyshev (`z_max^{ℝ}(5k + 4) ≥ 8 · 7^(k - 1)`):**
For every `k ≥ 1`, there exists a constant-free SLP `P : SLP (5 * k + 4)` computing a nonzero
polynomial `f ∈ ℤ[X]` with at least `8 * 7 ^ (k - 1)` distinct real roots. -/
theorem tau_real_5C (k : ℕ) (hk : 1 ≤ k) :
    ∃ P : SLP (5 * k + 4),
      P.evalPoly ≠ 0 ∧
      ∃ S : Finset ℝ,
        S.card = 8 * 7 ^ (k - 1) ∧ ∀ r ∈ S, Polynomial.aeval r P.evalPoly = 0 := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  refine ⟨real5CSLP (m + 1), real5CSLP_ne_zero (m + 1), ?_⟩
  rcases q5c_iter_preimages_in m 1 (by norm_num) (by norm_num) with ⟨T, hT_card, hT_prop⟩
  have hstep8 : ∀ (y : ℝ) (hy : y ∈ T), ∃ S_all : Finset ℝ, S_all.card = 8 ∧ ∀ r ∈ S_all, q5c r = y := by
    intro y hy
    rcases q5c_preimages y (hT_prop y hy).1 (hT_prop y hy).2.1 with ⟨_, S_all, _, hc, _, hq⟩
    exact ⟨S_all, hc, hq⟩
  choose G hG_card hG_prop using hstep8
  let S : Finset ℝ := T.attach.biUnion (fun y => G y.1 y.2)
  have hdisj : Set.PairwiseDisjoint (T.attach : Set {y // y ∈ T})
      (fun y => G y.1 y.2) := by
    intro a _ b _ hab
    dsimp [Function.onFun]
    rw [Finset.disjoint_left]
    intro r hra hrb
    have ha_eq := hG_prop a.1 a.2 r hra
    have hb_eq := hG_prop b.1 b.2 r hrb
    exact hab (Subtype.ext (ha_eq.symm.trans hb_eq))
  refine ⟨S, ?_, ?_⟩
  · rw [Finset.card_biUnion hdisj]
    calc
      ∑ y ∈ T.attach, (G y.1 y.2).card
          = ∑ _y ∈ T.attach, 8 := Finset.sum_congr rfl (fun y _ => hG_card y.1 y.2)
      _ = T.attach.card * 8 := by simp
      _ = 8 * 7 ^ m := by rw [Finset.card_attach, hT_card]; ring
  · intro r hr
    rcases Finset.mem_biUnion.mp hr with ⟨y, _, hry⟩
    rw [real5CSLP_evalPoly, map_sub, map_one, aeval_real5CPoly, Function.iterate_succ_apply,
      hG_prop y.1 y.2 r hry, (hT_prop y.1 y.2).2.2, sub_self]

/-- Explicit finite domination over Chebyshev's `2 ^ (τ / 2)` rate for all `k ≥ 5` (`τ = 5k + 4`):
`8 * 7 ^ (k - 1) > 2 ^ ((5 * k + 4) / 2)`. -/
theorem tau_real_5C_beats_chebyshev (k : ℕ) (hk : 5 ≤ k) :
    ∃ P : SLP (5 * k + 4),
      P.evalPoly ≠ 0 ∧
      ∃ S : Finset ℝ,
        2 ^ ((5 * k + 4) / 2) < S.card ∧ ∀ r ∈ S, Polynomial.aeval r P.evalPoly = 0 := by
  rcases tau_real_5C k (by omega) with ⟨P, hne, S, hcard, hroots⟩
  refine ⟨P, hne, S, ?_, hroots⟩
  rw [hcard]
  clear P hne S hcard hroots
  obtain ⟨d, rfl⟩ : ∃ d, k = d + 5 := ⟨k - 5, by omega⟩
  clear hk
  induction d using Nat.strong_induction_on with
  | ind d ih =>
      match d with
      | 0 => norm_num
      | 1 => norm_num
      | d' + 2 =>
          have hprev := ih d' (by omega)
          have hdiv : (5 * (d' + 2 + 5) + 4) / 2 = (5 * (d' + 5) + 4) / 2 + 5 := by omega
          rw [hdiv, pow_add]
          have hexp : d' + 2 + 5 - 1 = (d' + 5 - 1) + 2 := by omega
          rw [hexp, pow_add]
          have h32 : 2 ^ 5 < 7 ^ 2 := by norm_num
          calc
            2 ^ ((5 * (d' + 5) + 4) / 2) * 2 ^ 5
                < (8 * 7 ^ (d' + 5 - 1)) * 2 ^ 5 :=
                  Nat.mul_lt_mul_of_pos_right hprev (by positivity)
            _ ≤ (8 * 7 ^ (d' + 5 - 1)) * 7 ^ 2 :=
                  Nat.mul_le_mul_left _ h32.le
            _ = 8 * (7 ^ (d' + 5 - 1) * 7 ^ 2) := by ring

end Research.PvsNP.Tau

end
