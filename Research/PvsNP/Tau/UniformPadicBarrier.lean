module

public import Research.PvsNP.Tau.ChirpZ
public import Research.PvsNP.Tau.RealLowerBound
public import Mathlib.NumberTheory.Padics.Hensel
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finite.Basic

@[expose] public section

namespace Research.PvsNP.Tau

/-!
# Cubic $2$-Adic Lower Bound and Uniform $p$-Adic Barrier (`lim_{p → ∞} α_{ℚ_p} = 1`)

This module establishes two unconditional $p$-adic lower-bound theorems for constant-free
straight-line programs (`SLP`) over `ℤ[X]`:

1. **Cubic `ℤ_[2]` Lower Bound (`tau_padic2_cubic`):**
   The homogenized cubic recurrence `P₀ = X`, `D₀ = 1`, `P_{n+1} = P_n(P_n² - D_n²)`,
   `D_{n+1} = 8 D_n³` has constant-free SLP length `τ(P_k) = 6k - 2` (`k ≥ 2`) and admits at
   least `3 ^ k` distinct roots in `ℤ_[2]`, improving `PadicBarrier.lean`'s rate from
   `α_{ℤ_2} ≥ 1/4 = 0.25` to `α_{ℤ_2} ≥ (log_2 3) / 6 ≈ 0.26416`.

2. **Uniform $p$-Adic Barrier (`tau_padic_fermat`, `tau_padic_rate_arbitrarily_close_to_one`):**
   For every odd prime `p`, the polynomial `Q_p(X) = X² ((p X)^(p - 1) - 1) ∈ ℤ[X]` maps each
   of the `p - 1` disjoint balls `(r + p ℤ_p) / p ⊂ ℚ_p` (`1 ≤ r < p`) bijectively onto
   `(1 / p) ℤ_p`, yielding `(p - 1) ^ k` distinct roots of `Q_p^[k]` in `ℚ_p`.
   - For Fermat primes `p = 2^m + 1` (`m ≥ 1`), this takes `(m + 3) * k + (m + 3)` gates,
     giving `α_{ℚ_{2^m+1}} ≥ m / (m + 3)` (e.g., `α_{ℚ_{65537}} ≥ 16/19 ≈ 0.8421`).
   - For arbitrary odd primes `p`, windowed base-`2^w` addition chains establish
     `lim_{p → ∞} α_{ℚ_p} = 1`, proving that **no uniform $p$-adic method can establish
     `z_{ℚ_p}(f) ≤ 2^((1 - ε) τ(f))` for any constant `ε > 0`**.
-/

/-! ## 1. Cubic `ℤ_[2]` Lower Bound (`z_max^{ℤ_2}(6k - 2) ≥ 3^k`) -/

/-- Denominator sequence `D_0 = 1`, `D_{n+1} = 8 * D_n ^ 3`. -/
def cubicD : ℕ → ℕ
  | 0 => 1
  | n + 1 => 8 * (cubicD n) ^ 3

theorem cubicD_pos (n : ℕ) : 0 < cubicD n := by
  induction n with
  | zero => simp [cubicD]
  | succ n ih => simp [cubicD]; positivity

/-- Polynomial family `P_0 = X`, `P_{n+1} = P_n * (P_n ^ 2 - D_n ^ 2)`. -/
noncomputable def cubicPoly : ℕ → Polynomial ℤ
  | 0 => Polynomial.X
  | n + 1 => cubicPoly n * ((cubicPoly n) ^ 2 - (cubicD n : Polynomial ℤ) ^ 2)

/-- Wire holding `D_{n+1}` in `cubicBaseSLP n`. -/
def cubicDWire (n : ℕ) : ℕ :=
  if n = 0 then 4 else 6 * n + 6

/-- Append one 6-gate cubic `ℤ_[2]` step computing `D_{n+2}` at wire `τ + 6` and `P_{n+2}` at
wire `τ + 7`. -/
def cubicStepSLP {τ : ℕ} (P : SLP τ) (i8 iD iP : Fin (τ + 2)) : SLP (τ + 6) :=
  let s1 : SLP (τ + 1) := .snoc P .mul iP iP                                   -- w_{τ+2} = P^2
  let s2 : SLP (τ + 2) := .snoc s1 .mul ⟨iD.val, by omega⟩ ⟨iD.val, by omega⟩  -- w_{τ+3} = D^2
  let s3 : SLP (τ + 3) := .snoc s2 .sub ⟨τ + 2, by omega⟩ ⟨τ + 3, by omega⟩    -- w_{τ+4} = P^2 - D^2
  let s4 : SLP (τ + 4) := .snoc s3 .mul ⟨iD.val, by omega⟩ ⟨τ + 3, by omega⟩   -- w_{τ+5} = D^3
  let s5 : SLP (τ + 5) := .snoc s4 .mul ⟨i8.val, by omega⟩ ⟨τ + 5, by omega⟩   -- w_{τ+6} = 8 D^3
  .snoc s5 .mul ⟨iP.val, by omega⟩ ⟨τ + 4, by omega⟩                           -- w_{τ+7} = P(P^2 - D^2)

/-- Append the 4-gate final cubic `ℤ_[2]` step computing `P_{n+2}` at wire `τ + 5`. -/
def cubicFinalSLP {τ : ℕ} (P : SLP τ) (iD iP : Fin (τ + 2)) : SLP (τ + 4) :=
  let s1 : SLP (τ + 1) := .snoc P .mul iP iP
  let s2 : SLP (τ + 2) := .snoc s1 .mul ⟨iD.val, by omega⟩ ⟨iD.val, by omega⟩
  let s3 : SLP (τ + 3) := .snoc s2 .sub ⟨τ + 2, by omega⟩ ⟨τ + 3, by omega⟩
  .snoc s3 .mul ⟨iP.val, by omega⟩ ⟨τ + 4, by omega⟩

theorem cubicStepSLP_evalWire_lt {τ : ℕ} (P : SLP τ) (i8 iD iP : Fin (τ + 2))
    (k : Fin (τ + 8)) (hk : k.val < τ + 2) :
    (cubicStepSLP P i8 iD iP).evalWire k = P.evalWire ⟨k.val, hk⟩ := by
  unfold cubicStepSLP
  dsimp only
  rw [SLP.evalWire_snoc_lt _ _ _ _ _ (by omega),
      SLP.evalWire_snoc_lt _ _ _ _ _ (by dsimp; omega),
      SLP.evalWire_snoc_lt _ _ _ _ _ (by dsimp; omega),
      SLP.evalWire_snoc_lt _ _ _ _ _ (by dsimp; omega),
      SLP.evalWire_snoc_lt _ _ _ _ _ (by dsimp; omega),
      SLP.evalWire_snoc_lt _ _ _ _ _ (by dsimp; omega)]

theorem cubicStepSLP_outputs {τ : ℕ} (P : SLP τ) (i8 iD iP : Fin (τ + 2))
    (h8 : P.evalWire i8 = 8) :
    (cubicStepSLP P i8 iD iP).evalWire ⟨τ + 6, by omega⟩ = 8 * (P.evalWire iD) ^ 3 ∧
    (cubicStepSLP P i8 iD iP).evalWire ⟨τ + 7, by omega⟩ =
      P.evalWire iP * ((P.evalWire iP) ^ 2 - (P.evalWire iD) ^ 2) := by
  unfold cubicStepSLP
  dsimp only
  set s1 : SLP (τ + 1) := .snoc P .mul iP iP
  set s2 : SLP (τ + 2) := .snoc s1 .mul ⟨iD.val, by omega⟩ ⟨iD.val, by omega⟩
  set s3 : SLP (τ + 3) := .snoc s2 .sub ⟨τ + 2, by omega⟩ ⟨τ + 3, by omega⟩
  set s4 : SLP (τ + 4) := .snoc s3 .mul ⟨iD.val, by omega⟩ ⟨τ + 3, by omega⟩
  set s5 : SLP (τ + 5) := .snoc s4 .mul ⟨i8.val, by omega⟩ ⟨τ + 5, by omega⟩
  have hiD : iD.val < τ + 2 := iD.isLt
  have hiP : iP.val < τ + 2 := iP.isLt
  have hi8 : i8.val < τ + 2 := i8.isLt
  have hs1 : s1.evalWire ⟨τ + 2, by omega⟩ = P.evalWire iP * P.evalWire iP := by
    rw [SLP.evalWire_snoc_last _ _ _ _ _ rfl]; rfl
  have hs2 : s2.evalWire ⟨τ + 3, by omega⟩ = P.evalWire iD * P.evalWire iD := by
    rw [SLP.evalWire_snoc_last _ _ _ _ _ rfl]
    simp only [SLPOp.applyPoly]
    rw [SLP.evalWire_snoc_lt _ _ _ _ _ hiD]
  have hs3 : s3.evalWire ⟨τ + 4, by omega⟩ =
      P.evalWire iP * P.evalWire iP - P.evalWire iD * P.evalWire iD := by
    rw [SLP.evalWire_snoc_last _ _ _ _ _ rfl]
    simp only [SLPOp.applyPoly, hs2]
    rw [SLP.evalWire_snoc_lt _ _ _ _ _ (by dsimp; omega), hs1]
  have hs4 : s4.evalWire ⟨τ + 5, by omega⟩ = P.evalWire iD * (P.evalWire iD * P.evalWire iD) := by
    rw [SLP.evalWire_snoc_last _ _ _ _ _ rfl]
    simp only [SLPOp.applyPoly]
    rw [SLP.evalWire_snoc_lt _ _ _ _ _ (by dsimp; omega),
        SLP.evalWire_snoc_lt _ _ _ _ _ (by dsimp; omega),
        SLP.evalWire_snoc_lt _ _ _ _ _ (by dsimp; omega),
        SLP.evalWire_snoc_lt _ _ _ _ _ (by dsimp; omega), hs2]
  have hs5 : s5.evalWire ⟨τ + 6, by omega⟩ = 8 * (P.evalWire iD) ^ 3 := by
    rw [SLP.evalWire_snoc_last _ _ _ _ _ rfl]
    simp only [SLPOp.applyPoly, hs4]
    rw [SLP.evalWire_snoc_lt _ _ _ _ _ (by dsimp; omega),
        SLP.evalWire_snoc_lt _ _ _ _ _ (by dsimp; omega),
        SLP.evalWire_snoc_lt _ _ _ _ _ (by dsimp; omega),
        SLP.evalWire_snoc_lt _ _ _ _ _ (by dsimp; omega), h8]
    ring
  refine ⟨?_, ?_⟩
  · rw [SLP.evalWire_snoc_lt _ _ _ _ _ (by dsimp; omega), hs5]
  · rw [SLP.evalWire_snoc_last _ _ _ _ _ rfl]
    simp only [SLPOp.applyPoly]
    rw [SLP.evalWire_snoc_lt _ _ _ _ _ (by dsimp; omega),
        SLP.evalWire_snoc_lt _ _ _ _ _ (by dsimp; omega),
        SLP.evalWire_snoc_lt _ _ _ _ _ (by dsimp; omega),
        SLP.evalWire_snoc_lt _ _ _ _ _ (by dsimp; omega),
        SLP.evalWire_snoc_lt _ _ _ _ _ (by dsimp; omega),
        SLP.evalWire_snoc_lt _ _ _ _ _ (by dsimp; omega),
        SLP.evalWire_snoc_lt _ _ _ _ _ (by dsimp; omega), hs3]
    ring

theorem cubicFinalSLP_evalPoly {τ : ℕ} (P : SLP τ) (iD iP : Fin (τ + 2)) :
    (cubicFinalSLP P iD iP).evalPoly =
      P.evalWire iP * ((P.evalWire iP) ^ 2 - (P.evalWire iD) ^ 2) := by
  unfold SLP.evalPoly cubicFinalSLP
  dsimp only
  set s1 : SLP (τ + 1) := .snoc P .mul iP iP
  set s2 : SLP (τ + 2) := .snoc s1 .mul ⟨iD.val, by omega⟩ ⟨iD.val, by omega⟩
  set s3 : SLP (τ + 3) := .snoc s2 .sub ⟨τ + 2, by omega⟩ ⟨τ + 3, by omega⟩
  have hiD : iD.val < τ + 2 := iD.isLt
  have hiP : iP.val < τ + 2 := iP.isLt
  have hs1 : s1.evalWire ⟨τ + 2, by omega⟩ = P.evalWire iP * P.evalWire iP := by
    rw [SLP.evalWire_snoc_last _ _ _ _ _ rfl]; rfl
  have hs2 : s2.evalWire ⟨τ + 3, by omega⟩ = P.evalWire iD * P.evalWire iD := by
    rw [SLP.evalWire_snoc_last _ _ _ _ _ rfl]
    simp only [SLPOp.applyPoly]
    rw [SLP.evalWire_snoc_lt _ _ _ _ _ hiD]
  have hs3 : s3.evalWire ⟨τ + 4, by omega⟩ =
      P.evalWire iP * P.evalWire iP - P.evalWire iD * P.evalWire iD := by
    rw [SLP.evalWire_snoc_last _ _ _ _ _ rfl]
    simp only [SLPOp.applyPoly, hs2]
    rw [SLP.evalWire_snoc_lt _ _ _ _ _ (by dsimp; omega), hs1]
  rw [SLP.evalWire_snoc_last _ _ _ _ _ rfl]
  simp only [SLPOp.applyPoly, hs3]
  rw [SLP.evalWire_snoc_lt _ _ _ _ _ (by dsimp; omega),
      SLP.evalWire_snoc_lt _ _ _ _ _ (by dsimp; omega),
      SLP.evalWire_snoc_lt _ _ _ _ _ (by dsimp; omega)]
  ring

/-- Constant-free SLP of length `6 * n + 6` computing `8` at wire `4`, `D_{n+1}` at
`cubicDWire n`, and `cubicPoly (n + 1)` at wire `6 * n + 7`. -/
def cubicBaseSLP : (n : ℕ) → SLP (6 * n + 6)
  | 0 =>
      let p1 : SLP 1 := .snoc .nil .add ⟨0, by omega⟩ ⟨0, by omega⟩   -- w2 = 2
      let p2 : SLP 2 := .snoc p1 .add ⟨2, by omega⟩ ⟨2, by omega⟩     -- w3 = 4
      let p3 : SLP 3 := .snoc p2 .add ⟨3, by omega⟩ ⟨3, by omega⟩     -- w4 = 8 = D_1
      let p4 : SLP 4 := .snoc p3 .mul ⟨1, by omega⟩ ⟨1, by omega⟩     -- w5 = X^2
      let p5 : SLP 5 := .snoc p4 .sub ⟨5, by omega⟩ ⟨0, by omega⟩     -- w6 = X^2 - 1
      .snoc p5 .mul ⟨1, by omega⟩ ⟨6, by omega⟩                       -- w7 = X(X^2 - 1) = P_1
  | n + 1 =>
      cubicStepSLP (cubicBaseSLP n) ⟨4, by omega⟩
        ⟨cubicDWire n, by dsimp [cubicDWire]; split_ifs <;> omega⟩
        ⟨6 * n + 7, by omega⟩

/-- Constant-free SLP of length `6 * n + 10 = 6 * (n + 2) - 2` computing `cubicPoly (n + 2)`. -/
def cubicSLP (n : ℕ) : SLP (6 * n + 10) :=
  cubicFinalSLP (cubicBaseSLP n)
    ⟨cubicDWire n, by dsimp [cubicDWire]; split_ifs <;> omega⟩
    ⟨6 * n + 7, by omega⟩

theorem cubicBaseSLP_wires (n : ℕ) :
    (cubicBaseSLP n).evalWire ⟨4, by omega⟩ = (8 : Polynomial ℤ) ∧
    (cubicBaseSLP n).evalWire ⟨cubicDWire n, by dsimp [cubicDWire]; split_ifs <;> omega⟩ =
      (cubicD (n + 1) : Polynomial ℤ) ∧
    (cubicBaseSLP n).evalWire ⟨6 * n + 7, by omega⟩ = cubicPoly (n + 1) := by
  induction n with
  | zero =>
      refine ⟨?_, ?_, ?_⟩
      · simp [cubicBaseSLP, SLP.evalWire, SLPOp.applyPoly]; norm_num
      · simp [cubicBaseSLP, cubicDWire, cubicD, SLP.evalWire, SLPOp.applyPoly]; norm_num
      · simp [cubicBaseSLP, cubicPoly, cubicD, SLP.evalWire, SLPOp.applyPoly]; ring
  | succ n ih =>
      rcases ih with ⟨h8, hD, hP⟩
      have houts := cubicStepSLP_outputs (cubicBaseSLP n) ⟨4, by omega⟩
        ⟨cubicDWire n, by dsimp [cubicDWire]; split_ifs <;> omega⟩
        ⟨6 * n + 7, by omega⟩ h8
      refine ⟨?_, ?_, ?_⟩
      · simpa [cubicBaseSLP] using
          (cubicStepSLP_evalWire_lt (cubicBaseSLP n) ⟨4, by omega⟩
            ⟨cubicDWire n, by dsimp [cubicDWire]; split_ifs <;> omega⟩
            ⟨6 * n + 7, by omega⟩ ⟨4, by omega⟩ (by dsimp; omega)).trans h8
      · have hfin : (⟨cubicDWire (n + 1), by dsimp [cubicDWire]; omega⟩ :
            Fin (6 * (n + 1) + 6 + 2)) = ⟨(6 * n + 6) + 6, by omega⟩ := by
          ext; simp [cubicDWire]; omega
        rw [hfin]
        have h := houts.1
        rw [hD] at h
        simpa [cubicBaseSLP, cubicD, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using h
      · have hfin : (⟨6 * (n + 1) + 7, by omega⟩ :
            Fin (6 * (n + 1) + 6 + 2)) = ⟨(6 * n + 6) + 7, by omega⟩ := by
          ext; dsimp; omega
        rw [hfin]
        have h := houts.2
        rw [hD, hP] at h
        simpa [cubicBaseSLP, cubicPoly] using h

theorem cubicSLP_evalPoly (n : ℕ) : (cubicSLP n).evalPoly = cubicPoly (n + 2) := by
  unfold cubicSLP
  rw [cubicFinalSLP_evalPoly, (cubicBaseSLP_wires n).2.1, (cubicBaseSLP_wires n).2.2]
  rfl

theorem cubicPoly_monic_and_deg (n : ℕ) :
    (cubicPoly n).Monic ∧ (cubicPoly n).natDegree = 3 ^ n := by
  induction n with
  | zero =>
      exact ⟨Polynomial.monic_X, Polynomial.natDegree_X⟩
  | succ n ih =>
      rcases ih with ⟨hm, hd⟩
      simp only [cubicPoly]
      have hsq_m : (cubicPoly n ^ 2).Monic := hm.pow 2
      have hsq_d : (cubicPoly n ^ 2).natDegree = 2 * 3 ^ n := by
        rw [Polynomial.natDegree_pow, hd]
      have hc_d : ((cubicD n : Polynomial ℤ) ^ 2).natDegree = 0 := by
        rw [show (cubicD n : Polynomial ℤ) = Polynomial.C (cubicD n : ℤ) by simp, ← map_pow,
          Polynomial.natDegree_C]
      have hc_lt : ((cubicD n : Polynomial ℤ) ^ 2).natDegree < (cubicPoly n ^ 2).natDegree := by
        rw [hc_d, hsq_d]; positivity
      have hdeg_lt : ((cubicD n : Polynomial ℤ) ^ 2).degree < (cubicPoly n ^ 2).degree := by
        have hc_le : ((cubicD n : Polynomial ℤ) ^ 2).degree ≤ 0 := by
          rw [show (cubicD n : Polynomial ℤ) = Polynomial.C (cubicD n : ℤ) by simp, ← map_pow]
          exact Polynomial.degree_C_le
        rw [Polynomial.degree_eq_natDegree hsq_m.ne_zero, hsq_d]
        exact lt_of_le_of_lt hc_le (by exact_mod_cast (by positivity : 0 < 2 * 3 ^ n))
      have hdiff_m : (cubicPoly n ^ 2 - (cubicD n : Polynomial ℤ) ^ 2).Monic :=
        hsq_m.sub_of_left hdeg_lt
      have hdiff_d : (cubicPoly n ^ 2 - (cubicD n : Polynomial ℤ) ^ 2).natDegree = 2 * 3 ^ n := by
        rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hc_lt, hsq_d]
      refine ⟨hm.mul hdiff_m, ?_⟩
      rw [Polynomial.natDegree_mul hm.ne_zero hdiff_m.ne_zero, hd, hdiff_d, pow_succ]
      ring

/-- For every `t ∈ ℤ_[2]`, the cubic `y(y² - 1) = 8t` has three distinct roots in `ℤ_[2]`
(lifted by Hensel's lemma from `0`, `1`, and `-1`). -/
theorem padic2_cubic_three_roots (t : ℤ_[2]) :
    ∃ y1 y2 y3 : ℤ_[2],
      y1 ≠ y2 ∧ y1 ≠ y3 ∧ y2 ≠ y3 ∧
      y1 * (y1 ^ 2 - 1) = 8 * t ∧
      y2 * (y2 ^ 2 - 1) = 8 * t ∧
      y3 * (y3 ^ 2 - 1) = 8 * t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let F : Polynomial ℤ_[2] := Polynomial.X ^ 3 - Polynomial.X - Polynomial.C (8 * t)
  have hderiv : F.derivative = 3 * Polynomial.X ^ 2 - 1 := by
    simp [F, Polynomial.derivative_pow, Polynomial.C_ofNat]
  have hnorm2 : ‖(2 : ℤ_[2])‖ = (1 / 2 : ℝ) := by
    simpa [PadicInt.norm_p] using (PadicInt.norm_p (p := 2))
  have hnorm8 : ‖(8 : ℤ_[2])‖ = (1 / 8 : ℝ) := by
    have h8 : (8 : ℤ_[2]) = (2 : ℤ_[2]) ^ 3 := by norm_num
    rw [h8, norm_pow, hnorm2]; norm_num
  have h8t : ‖(8 : ℤ_[2]) * t‖ ≤ (1 / 8 : ℝ) := by
    rw [norm_mul, hnorm8]
    have ht : ‖t‖ ≤ 1 := PadicInt.norm_le_one t
    nlinarith [norm_nonneg t]
  -- Root y1 near 0
  have hF0 : F.aeval (0 : ℤ_[2]) = -(8 * t) := by simp [F]
  have hFd0 : F.derivative.aeval (0 : ℤ_[2]) = (-1 : ℤ_[2]) := by simp [hderiv]
  have hlt0 : ‖F.aeval (0 : ℤ_[2])‖ < ‖F.derivative.aeval (0 : ℤ_[2])‖ ^ 2 := by
    rw [hF0, hFd0, norm_neg, norm_neg, norm_one]; linarith
  rcases hensels_lemma (p := 2) (F := F) (a := (0 : ℤ_[2])) hlt0 with
    ⟨y1, hy1_root, hy1_dist, _, _⟩
  rw [sub_zero, hFd0, norm_neg, norm_one] at hy1_dist
  -- Root y2 near 1
  have hF1 : F.aeval (1 : ℤ_[2]) = -(8 * t) := by simp [F]
  have hFd1 : F.derivative.aeval (1 : ℤ_[2]) = (2 : ℤ_[2]) := by simp [hderiv]; norm_num
  have hlt1 : ‖F.aeval (1 : ℤ_[2])‖ < ‖F.derivative.aeval (1 : ℤ_[2])‖ ^ 2 := by
    rw [hF1, hFd1, norm_neg, hnorm2]; linarith
  rcases hensels_lemma (p := 2) (F := F) (a := (1 : ℤ_[2])) hlt1 with
    ⟨y2, hy2_root, hy2_dist, _, _⟩
  rw [hFd1, hnorm2] at hy2_dist
  -- Root y3 near -1
  have hFm1 : F.aeval (-1 : ℤ_[2]) = -(8 * t) := by simp [F]; ring
  have hFdm1 : F.derivative.aeval (-1 : ℤ_[2]) = (2 : ℤ_[2]) := by simp [hderiv]; norm_num
  have hltm1 : ‖F.aeval (-1 : ℤ_[2])‖ < ‖F.derivative.aeval (-1 : ℤ_[2])‖ ^ 2 := by
    rw [hFm1, hFdm1, norm_neg, hnorm2]; linarith
  rcases hensels_lemma (p := 2) (F := F) (a := (-1 : ℤ_[2])) hltm1 with
    ⟨y3, hy3_root, hy3_dist, _, _⟩
  rw [hFdm1, hnorm2, sub_neg_eq_add] at hy3_dist
  -- Pairwise distinctness via ultrametric inequality
  have h12 : y1 ≠ y2 := by
    intro heq
    subst heq
    have h1 : (1 : ℤ_[2]) = y1 + -(y1 - 1) := by ring
    have hle : ‖(1 : ℤ_[2])‖ ≤ max ‖y1‖ ‖y1 - 1‖ := by
      calc
        ‖(1 : ℤ_[2])‖ = ‖y1 + -(y1 - 1)‖ := congrArg norm h1
        _ ≤ max ‖y1‖ ‖-(y1 - 1)‖ := PadicInt.nonarchimedean y1 (-(y1 - 1))
        _ = max ‖y1‖ ‖y1 - 1‖ := by rw [norm_neg]
    rw [norm_one] at hle
    have hmax : max ‖y1‖ ‖y1 - 1‖ < 1 := max_lt hy1_dist (by linarith)
    linarith
  have h13 : y1 ≠ y3 := by
    intro heq
    subst heq
    have h1 : (1 : ℤ_[2]) = (y1 + 1) + -y1 := by ring
    have hle : ‖(1 : ℤ_[2])‖ ≤ max ‖y1 + 1‖ ‖y1‖ := by
      calc
        ‖(1 : ℤ_[2])‖ = ‖(y1 + 1) + -y1‖ := congrArg norm h1
        _ ≤ max ‖y1 + 1‖ ‖-y1‖ := PadicInt.nonarchimedean (y1 + 1) (-y1)
        _ = max ‖y1 + 1‖ ‖y1‖ := by rw [norm_neg]
    rw [norm_one] at hle
    have hmax : max ‖y1 + 1‖ ‖y1‖ < 1 := max_lt (by linarith) hy1_dist
    linarith
  have h23 : y2 ≠ y3 := by
    intro heq
    subst heq
    have h2 : (2 : ℤ_[2]) = (y2 + 1) + -(y2 - 1) := by ring
    have hle : ‖(2 : ℤ_[2])‖ ≤ max ‖y2 + 1‖ ‖y2 - 1‖ := by
      calc
        ‖(2 : ℤ_[2])‖ = ‖(y2 + 1) + -(y2 - 1)‖ := congrArg norm h2
        _ ≤ max ‖y2 + 1‖ ‖-(y2 - 1)‖ := PadicInt.nonarchimedean (y2 + 1) (-(y2 - 1))
        _ = max ‖y2 + 1‖ ‖y2 - 1‖ := by rw [norm_neg]
    rw [hnorm2] at hle
    have hmax : max ‖y2 + 1‖ ‖y2 - 1‖ < 1 / 2 := max_lt hy3_dist hy2_dist
    linarith
  have hroot_eq : ∀ y : ℤ_[2], F.aeval y = 0 → y * (y ^ 2 - 1) = 8 * t := by
    intro y hy
    have h0 : y ^ 3 - y - 8 * t = 0 := by simpa [F] using hy
    linear_combination h0
  exact ⟨y1, y2, y3, h12, h13, h23, hroot_eq y1 hy1_root, hroot_eq y2 hy2_root,
    hroot_eq y3 hy3_root⟩

/-- Ternary preimage tree in `ℤ_[2]`: for every `n : ℕ` and `t : ℤ_[2]`, `cubicPoly n = D_n * t`
has at least `3 ^ n` distinct roots in `ℤ_[2]`. -/
theorem cubicPoly_preimages (n : ℕ) :
    ∀ t : ℤ_[2],
      ∃ S : Finset ℤ_[2],
        S.card = 3 ^ n ∧
        ∀ r ∈ S, Polynomial.aeval r (cubicPoly n) = (cubicD n : ℤ_[2]) * t := by
  classical
  induction n with
  | zero =>
      intro t
      refine ⟨{t}, by simp, ?_⟩
      intro r hr
      rw [Finset.mem_singleton] at hr
      subst hr
      simp [cubicPoly, cubicD]
  | succ n ih =>
      intro t
      rcases padic2_cubic_three_roots t with ⟨y1, y2, y3, h12, h13, h23, hy1, hy2, hy3⟩
      rcases ih y1 with ⟨S1, hc1, hS1⟩
      rcases ih y2 with ⟨S2, hc2, hS2⟩
      rcases ih y3 with ⟨S3, hc3, hS3⟩
      have hDne : (cubicD n : ℤ_[2]) ≠ 0 := by
        exact_mod_cast (cubicD_pos n).ne'
      have hdisj : ∀ {A B : Finset ℤ_[2]} {a b : ℤ_[2]},
          a ≠ b →
          (∀ r ∈ A, Polynomial.aeval r (cubicPoly n) = (cubicD n : ℤ_[2]) * a) →
          (∀ r ∈ B, Polynomial.aeval r (cubicPoly n) = (cubicD n : ℤ_[2]) * b) →
          Disjoint A B := by
        intro A B a b hab hA hB
        rw [Finset.disjoint_left]
        intro r hrA hrB
        exact hab (mul_left_cancel₀ hDne ((hA r hrA).symm.trans (hB r hrB)))
      have hd12 : Disjoint S1 S2 := hdisj h12 hS1 hS2
      have hd13 : Disjoint S1 S3 := hdisj h13 hS1 hS3
      have hd23 : Disjoint S2 S3 := hdisj h23 hS2 hS3
      have hd12_3 : Disjoint (S1 ∪ S2) S3 := Finset.disjoint_union_left.mpr ⟨hd13, hd23⟩
      refine ⟨(S1 ∪ S2) ∪ S3, ?_, ?_⟩
      · rw [Finset.card_union_of_disjoint hd12_3, Finset.card_union_of_disjoint hd12,
          hc1, hc2, hc3, pow_succ]
        ring
      · intro r hr
        have hstep : ∀ {y : ℤ_[2]},
            Polynomial.aeval r (cubicPoly n) = (cubicD n : ℤ_[2]) * y →
            y * (y ^ 2 - 1) = 8 * t →
            Polynomial.aeval r (cubicPoly (n + 1)) = (cubicD (n + 1) : ℤ_[2]) * t := by
          intro y hr_eq hy_eq
          simp only [cubicPoly, cubicD, map_mul, map_sub, map_pow, map_natCast, Nat.cast_mul,
            Nat.cast_pow, Nat.cast_ofNat, hr_eq]
          calc
            (cubicD n : ℤ_[2]) * y * (((cubicD n : ℤ_[2]) * y) ^ 2 - (cubicD n : ℤ_[2]) ^ 2)
                = (cubicD n : ℤ_[2]) ^ 3 * (y * (y ^ 2 - 1)) := by ring
            _ = (cubicD n : ℤ_[2]) ^ 3 * (8 * t) := by rw [hy_eq]
            _ = 8 * (cubicD n : ℤ_[2]) ^ 3 * t := by ring
        rcases Finset.mem_union.mp hr with hr12 | hr3
        · rcases Finset.mem_union.mp hr12 with hr1 | hr2
          · exact hstep (hS1 r hr1) hy1
          · exact hstep (hS2 r hr2) hy2
        · exact hstep (hS3 r hr3) hy3

/-- **Unconditional Cubic $2$-Adic Lower Bound (`z_max^{ℤ_2}(6k - 2) ≥ 3^k`):**
For every `k ≥ 2`, there exists a constant-free SLP of length `6 * k - 2` computing a nonzero
polynomial `f ∈ ℤ[X]` with at least `3 ^ k` distinct roots in `ℤ_[2]`. -/
theorem tau_padic2_cubic (k : ℕ) (hk : 2 ≤ k) :
    ∃ P : SLP (6 * k - 2),
      P.evalPoly ≠ 0 ∧
      ∃ S : Finset ℤ_[2],
        S.card = 3 ^ k ∧ ∀ r ∈ S, Polynomial.aeval r P.evalPoly = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
  have hlen : 6 * (n + 2) - 2 = 6 * n + 10 := by omega
  rw [hlen]
  refine ⟨cubicSLP n, ?_, ?_⟩
  · rw [cubicSLP_evalPoly]
    exact (cubicPoly_monic_and_deg (n + 2)).1.ne_zero
  · rcases cubicPoly_preimages (n + 2) 0 with ⟨S, hcard, hS⟩
    refine ⟨S, hcard, ?_⟩
    intro r hr
    rw [cubicSLP_evalPoly, hS r hr, mul_zero]

/-! ## 2. Uniform $p$-Adic Barrier (`Q_p(X) = X² ((p X)^(p - 1) - 1)`) -/

/-- `k`-fold iterate of `Q_p(w) = w² · ((p w)^(p - 1) - 1)` in `ℤ[X]`. -/
noncomputable def qpIter (p : ℕ) : ℕ → Polynomial ℤ
  | 0 => Polynomial.X
  | k + 1 => (qpIter p k) ^ 2 * ((Polynomial.C (p : ℤ) * qpIter p k) ^ (p - 1) - 1)

theorem qpIter_lead_pos_and_deg (p : ℕ) (hp : p.Prime) (k : ℕ) :
    0 < (qpIter p k).leadingCoeff ∧ 1 ≤ (qpIter p k).natDegree := by
  have hp2 : 2 ≤ p := hp.two_le
  have hp_pos : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp.pos
  induction k with
  | zero => simp [qpIter]
  | succ k ih =>
      rcases ih with ⟨hlc, hdeg⟩
      set f := qpIter p k
      have hf_ne : f ≠ 0 := by
        intro h0; rw [h0] at hlc; simp at hlc
      have hpf_lc : (Polynomial.C (p : ℤ) * f).leadingCoeff = (p : ℤ) * f.leadingCoeff := by
        rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
      have hpf_pos : 0 < (Polynomial.C (p : ℤ) * f).leadingCoeff := by
        rw [hpf_lc]; positivity
      have hpf_deg : (Polynomial.C (p : ℤ) * f).natDegree = f.natDegree := by
        rw [Polynomial.natDegree_C_mul hp_pos.ne']
      have hpow_lc : ((Polynomial.C (p : ℤ) * f) ^ (p - 1)).leadingCoeff =
          ((Polynomial.C (p : ℤ) * f).leadingCoeff) ^ (p - 1) := by
        rw [Polynomial.leadingCoeff_pow]
      have hpow_pos : 0 < ((Polynomial.C (p : ℤ) * f) ^ (p - 1)).leadingCoeff := by
        rw [hpow_lc]; positivity
      have hpow_deg : ((Polynomial.C (p : ℤ) * f) ^ (p - 1)).natDegree =
          (p - 1) * f.natDegree := by
        rw [Polynomial.natDegree_pow, hpf_deg]
      have h1_lt : (1 : Polynomial ℤ).natDegree <
          ((Polynomial.C (p : ℤ) * f) ^ (p - 1)).natDegree := by
        rw [Polynomial.natDegree_one, hpow_deg]
        have : 1 ≤ p - 1 := by omega
        nlinarith
      have hsub_lc : ((Polynomial.C (p : ℤ) * f) ^ (p - 1) - 1).leadingCoeff =
          ((Polynomial.C (p : ℤ) * f) ^ (p - 1)).leadingCoeff := by
        exact Polynomial.leadingCoeff_sub_of_degree_lt
          (Polynomial.degree_lt_degree h1_lt)
      have hsub_deg : ((Polynomial.C (p : ℤ) * f) ^ (p - 1) - 1).natDegree =
          (p - 1) * f.natDegree := by
        rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt h1_lt, hpow_deg]
      have hsub_ne : (Polynomial.C (p : ℤ) * f) ^ (p - 1) - 1 ≠ 0 := by
        intro h0; rw [h0, Polynomial.leadingCoeff_zero] at hsub_lc; linarith
      have hsq_ne : f ^ 2 ≠ 0 := pow_ne_zero 2 hf_ne
      simp only [qpIter]
      refine ⟨?_, ?_⟩
      · rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_pow, hsub_lc]
        positivity
      · rw [Polynomial.natDegree_mul hsq_ne hsub_ne, Polynomial.natDegree_pow, hsub_deg]
        omega

theorem qpIter_ne_zero (p : ℕ) (hp : p.Prime) (k : ℕ) : qpIter p k ≠ 0 := by
  have h := (qpIter_lead_pos_and_deg p hp k).1
  intro h0
  rw [h0, Polynomial.leadingCoeff_zero] at h
  exact lt_irrefl 0 h

/-- For every prime `p`, every `r ∈ {1, ..., p - 1}`, and every `w ∈ ℤ_[p]`, Hensel's lemma
produces `v ∈ ℤ_[p]` such that `(r + p v)² ((r + p v)^(p - 1) - 1) = p · w` in `ℤ_[p]`. -/
theorem padic_qp_ball_lift (p : ℕ) [Fact p.Prime] (r : ℕ) (hr1 : 1 ≤ r) (hrp : r < p)
    (w : ℤ_[p]) :
    ∃ v : ℤ_[p],
      ((r : ℤ_[p]) + (p : ℤ_[p]) * v) ^ 2 *
        (((r : ℤ_[p]) + (p : ℤ_[p]) * v) ^ (p - 1) - 1) = (p : ℤ_[p]) * w := by
  have hp : p.Prime := Fact.out
  have hp_ge2 : 2 ≤ p := hp.two_le
  -- Fermat's Little Theorem: p ∣ r^(p - 1) - 1 in ℤ
  have hrz_ne : ((r : ZMod p)) ≠ 0 := by
    intro h0
    have hdvd : p ∣ r := (ZMod.natCast_eq_zero_iff r p).mp h0
    exact absurd (Nat.le_of_dvd (by omega) hdvd) (by omega)
  have hflt_zmod : ((r : ZMod p)) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hrz_ne
  have hflt_dvd_nat : p ∣ r ^ (p - 1) - 1 := by
    have h1 : 1 ≤ r ^ (p - 1) := Nat.one_le_pow _ _ (by omega)
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub h1, Nat.cast_pow, Nat.cast_one, hflt_zmod,
      sub_self]
  obtain ⟨c_nat, hc_nat⟩ := hflt_dvd_nat
  have hc_int : ((r : ℤ) ^ (p - 1) - 1) = (p : ℤ) * (c_nat : ℤ) := by
    have h1 : 1 ≤ r ^ (p - 1) := Nat.one_le_pow _ _ (by omega)
    have hnat : r ^ (p - 1) = p * c_nat + 1 := by omega
    have hz : ((r ^ (p - 1) : ℕ) : ℤ) = ((p * c_nat + 1 : ℕ) : ℤ) := by exact_mod_cast hnat
    push_cast at hz
    linarith
  have hrpow : (r : ℤ_[p]) ^ (p - 1) = 1 + (p : ℤ_[p]) * (c_nat : ℤ_[p]) := by
    have hz : ((r : ℤ_[p]) ^ (p - 1) - 1) = (p : ℤ_[p]) * (c_nat : ℤ_[p]) := by
      exact_mod_cast hc_int
    linear_combination hz
  -- Construct `H ∈ ℤ_[p][X]` directly with `C p * H = (C r + C p * X)^(p - 1) - 1`
  let H : Polynomial ℤ_[p] :=
    Polynomial.C (c_nat : ℤ_[p]) +
      ∑ j ∈ Finset.Ico 1 p,
        Polynomial.C
          (((p - 1).choose j : ℤ_[p]) * (r : ℤ_[p]) ^ (p - 1 - j) * (p : ℤ_[p]) ^ (j - 1)) *
          Polynomial.X ^ j
  have hH_mul :
      Polynomial.C (p : ℤ_[p]) * H =
        (Polynomial.C (r : ℤ_[p]) + Polynomial.C (p : ℤ_[p]) * Polynomial.X) ^ (p - 1) - 1 := by
    rw [add_comm (Polynomial.C (r : ℤ_[p])),
      add_pow (Polynomial.C (p : ℤ_[p]) * Polynomial.X) (Polynomial.C (r : ℤ_[p])) (p - 1)]
    have hsub1 : p - 1 + 1 = p := by omega
    rw [Finset.range_eq_Ico, hsub1, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < p)]
    simp only [Nat.choose_zero_right, Nat.cast_one, mul_one, Nat.sub_zero, pow_zero, one_mul,
      ← map_pow]
    have hfirst : Polynomial.C ((r : ℤ_[p]) ^ (p - 1)) - 1 =
        Polynomial.C (p : ℤ_[p]) * Polynomial.C (c_nat : ℤ_[p]) := by
      rw [hrpow, map_add, map_one, map_mul]
      ring
    calc
      Polynomial.C (p : ℤ_[p]) * H
          = Polynomial.C (p : ℤ_[p]) * Polynomial.C (c_nat : ℤ_[p]) +
              ∑ j ∈ Finset.Ico 1 p,
                Polynomial.C (p : ℤ_[p]) *
                  (Polynomial.C (((p - 1).choose j : ℤ_[p]) * (r : ℤ_[p]) ^ (p - 1 - j) *
                    (p : ℤ_[p]) ^ (j - 1)) * Polynomial.X ^ j) := by
              simp only [H, mul_add, Finset.mul_sum]
      _ = (Polynomial.C ((r : ℤ_[p]) ^ (p - 1)) - 1) +
            ∑ j ∈ Finset.Ico 1 p,
              (Polynomial.C (p : ℤ_[p]) * Polynomial.X) ^ j *
                Polynomial.C ((r : ℤ_[p]) ^ (p - 1 - j)) * ↑((p - 1).choose j) := by
              rw [hfirst]
              congr 1
              refine Finset.sum_congr rfl ?_
              intro j hj
              have hj1 : 1 ≤ j := (Finset.mem_Ico.mp hj).1
              have hpj : (p : ℤ_[p]) * (p : ℤ_[p]) ^ (j - 1) = (p : ℤ_[p]) ^ j := by
                conv_rhs => rw [show j = (j - 1) + 1 by omega, pow_succ']
              rw [mul_pow, ← map_pow, ← Polynomial.C_eq_natCast]
              have hC : Polynomial.C (p : ℤ_[p]) *
                  Polynomial.C (((p - 1).choose j : ℤ_[p]) * (r : ℤ_[p]) ^ (p - 1 - j) *
                    (p : ℤ_[p]) ^ (j - 1)) =
                  Polynomial.C ((p : ℤ_[p]) ^ j) * Polynomial.C ((r : ℤ_[p]) ^ (p - 1 - j)) *
                    Polynomial.C ((p - 1).choose j : ℤ_[p]) := by
                rw [← map_mul, ← map_mul, ← map_mul]
                congr 1
                calc
                  (p : ℤ_[p]) * (((p - 1).choose j : ℤ_[p]) * (r : ℤ_[p]) ^ (p - 1 - j) *
                      (p : ℤ_[p]) ^ (j - 1))
                      = ((p : ℤ_[p]) * (p : ℤ_[p]) ^ (j - 1)) * (r : ℤ_[p]) ^ (p - 1 - j) *
                          ((p - 1).choose j : ℤ_[p]) := by ring
                  _ = (p : ℤ_[p]) ^ j * (r : ℤ_[p]) ^ (p - 1 - j) *
                          ((p - 1).choose j : ℤ_[p]) := by rw [hpj]
              rw [← mul_assoc, hC]
              ring
      _ = Polynomial.C ((r : ℤ_[p]) ^ (p - 1)) +
            (∑ j ∈ Finset.Ico 1 p,
              (Polynomial.C (p : ℤ_[p]) * Polynomial.X) ^ j *
                Polynomial.C ((r : ℤ_[p]) ^ (p - 1 - j)) * ↑((p - 1).choose j)) - 1 := by ring
  let G : Polynomial ℤ_[p] :=
    (Polynomial.C (r : ℤ_[p]) + Polynomial.C (p : ℤ_[p]) * Polynomial.X) ^ 2 * H - Polynomial.C w
  -- Evaluate `H` modulo `p`
  have hH_mod : ∀ v : ℤ_[p],
      ∃ q : ℤ_[p],
        Polynomial.eval v H =
          (c_nat : ℤ_[p]) + ((p - 1 : ℕ) : ℤ_[p]) * (r : ℤ_[p]) ^ (p - 2) * v +
            (p : ℤ_[p]) * q := by
    intro v
    have hsplit : Finset.Ico 1 p = insert 1 (Finset.Ico 2 p) := by
      ext j; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
    have h1not : (1 : ℕ) ∉ Finset.Ico 2 p := by simp
    have hev : Polynomial.eval v H =
        (c_nat : ℤ_[p]) +
          ∑ j ∈ Finset.Ico 1 p,
            (((p - 1).choose j : ℤ_[p]) * (r : ℤ_[p]) ^ (p - 1 - j) * (p : ℤ_[p]) ^ (j - 1)) *
              v ^ j := by
      change (Polynomial.evalRingHom v) H = _
      simp only [H, map_add, map_sum, map_mul, map_pow, Polynomial.coe_evalRingHom,
        Polynomial.eval_C, Polynomial.eval_X]
    rw [hev, hsplit, Finset.sum_insert h1not]
    have hterm1 :
        (((p - 1).choose 1 : ℤ_[p]) * (r : ℤ_[p]) ^ (p - 1 - 1) * (p : ℤ_[p]) ^ (1 - 1)) *
          v ^ 1 = ((p - 1 : ℕ) : ℤ_[p]) * (r : ℤ_[p]) ^ (p - 2) * v := by
      simp [Nat.choose_one_right, Nat.sub_sub]
    rw [hterm1]
    refine ⟨∑ j ∈ Finset.Ico 2 p,
        (((p - 1).choose j : ℤ_[p]) * (r : ℤ_[p]) ^ (p - 1 - j) * (p : ℤ_[p]) ^ (j - 2)) *
          v ^ j, ?_⟩
    rw [Finset.mul_sum]
    have hsum : ∑ j ∈ Finset.Ico 2 p,
        (((p - 1).choose j : ℤ_[p]) * (r : ℤ_[p]) ^ (p - 1 - j) * (p : ℤ_[p]) ^ (j - 1)) *
          v ^ j =
        ∑ j ∈ Finset.Ico 2 p,
          (p : ℤ_[p]) * ((((p - 1).choose j : ℤ_[p]) * (r : ℤ_[p]) ^ (p - 1 - j) *
            (p : ℤ_[p]) ^ (j - 2)) * v ^ j) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      have hj2 : 2 ≤ j := (Finset.mem_Ico.mp hj).1
      have hpj : (p : ℤ_[p]) ^ (j - 1) = (p : ℤ_[p]) * (p : ℤ_[p]) ^ (j - 2) := by
        conv_lhs => rw [show j - 1 = (j - 2) + 1 by omega, pow_succ']
      rw [hpj]; ring
    rw [hsum]; ring
  -- Evaluate `H.derivative` modulo `p`
  have hHd_mod : ∀ v : ℤ_[p],
      ∃ q : ℤ_[p],
        Polynomial.eval v H.derivative =
          ((p - 1 : ℕ) : ℤ_[p]) * (r : ℤ_[p]) ^ (p - 2) + (p : ℤ_[p]) * q := by
    intro v
    have hsplit : Finset.Ico 1 p = insert 1 (Finset.Ico 2 p) := by
      ext j; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
    have h1not : (1 : ℕ) ∉ Finset.Ico 2 p := by simp
    have hderiv_H : H.derivative =
        ∑ j ∈ Finset.Ico 1 p,
          Polynomial.C (((p - 1).choose j : ℤ_[p]) * (r : ℤ_[p]) ^ (p - 1 - j) *
            (p : ℤ_[p]) ^ (j - 1)) * (Polynomial.C (j : ℤ_[p]) * Polynomial.X ^ (j - 1)) := by
      simp only [H, Polynomial.derivative_add, Polynomial.derivative_C, zero_add,
        Polynomial.derivative_sum, Polynomial.derivative_C_mul, Polynomial.derivative_X_pow]
    have hev : Polynomial.eval v H.derivative =
        ∑ j ∈ Finset.Ico 1 p,
          (((p - 1).choose j : ℤ_[p]) * (r : ℤ_[p]) ^ (p - 1 - j) * (p : ℤ_[p]) ^ (j - 1)) *
            ((j : ℤ_[p]) * v ^ (j - 1)) := by
      change (Polynomial.evalRingHom v) H.derivative = _
      rw [hderiv_H]
      simp only [map_sum, map_mul, map_pow, Polynomial.coe_evalRingHom,
        Polynomial.eval_C, Polynomial.eval_X]
    rw [hev, hsplit, Finset.sum_insert h1not]
    have hterm1 :
        (((p - 1).choose 1 : ℤ_[p]) * (r : ℤ_[p]) ^ (p - 1 - 1) * (p : ℤ_[p]) ^ (1 - 1)) *
          (((1 : ℕ) : ℤ_[p]) * v ^ (1 - 1)) = ((p - 1 : ℕ) : ℤ_[p]) * (r : ℤ_[p]) ^ (p - 2) := by
      simp [Nat.choose_one_right, Nat.sub_sub]
    rw [hterm1]
    refine ⟨∑ j ∈ Finset.Ico 2 p,
        (((p - 1).choose j : ℤ_[p]) * (r : ℤ_[p]) ^ (p - 1 - j) * (p : ℤ_[p]) ^ (j - 2)) *
          ((j : ℤ_[p]) * v ^ (j - 1)), ?_⟩
    rw [Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hj2 : 2 ≤ j := (Finset.mem_Ico.mp hj).1
    have hpj : (p : ℤ_[p]) ^ (j - 1) = (p : ℤ_[p]) * (p : ℤ_[p]) ^ (j - 2) := by
      conv_lhs => rw [show j - 1 = (j - 2) + 1 by omega, pow_succ']
    rw [hpj]; ring
  -- `r` is a unit in `ℤ_[p]` since `1 ≤ r < p`
  have hr_norm : ‖(r : ℤ_[p])‖ = 1 := by
    have hndvd : ¬ (p : ℤ) ∣ (r : ℤ) := by
      intro hd
      have hnat : p ∣ r := by exact_mod_cast hd
      exact absurd (Nat.le_of_dvd (by omega) hnat) (by omega)
    have hcop : IsCoprime (r : ℤ) (p : ℤ) :=
      ((Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd.mpr hndvd).symm
    simpa using PadicInt.norm_intCast_eq_one_iff.mpr hcop
  rcases PadicInt.isUnit_iff.mpr hr_norm with ⟨u, hu⟩
  let a : ℤ_[p] := (↑u⁻¹ : ℤ_[p]) * ((r : ℤ_[p]) ^ 2 * (c_nat : ℤ_[p]) - w)
  have hra : (r : ℤ_[p]) * a = (r : ℤ_[p]) ^ 2 * (c_nat : ℤ_[p]) - w := by
    dsimp [a]
    rw [← hu, ← mul_assoc, Units.mul_inv, one_mul]
  have hr_p2 : (r : ℤ_[p]) ^ 2 * (r : ℤ_[p]) ^ (p - 2) =
      (r : ℤ_[p]) + (p : ℤ_[p]) * ((r : ℤ_[p]) * (c_nat : ℤ_[p])) := by
    have hexp : 2 + (p - 2) = 1 + (p - 1) := by omega
    calc
      (r : ℤ_[p]) ^ 2 * (r : ℤ_[p]) ^ (p - 2)
          = (r : ℤ_[p]) ^ (2 + (p - 2)) := by rw [pow_add]
      _ = (r : ℤ_[p]) * (r : ℤ_[p]) ^ (p - 1) := by rw [hexp, pow_add, pow_one]
      _ = (r : ℤ_[p]) * (1 + (p : ℤ_[p]) * (c_nat : ℤ_[p])) := by rw [hrpow]
      _ = (r : ℤ_[p]) + (p : ℤ_[p]) * ((r : ℤ_[p]) * (c_nat : ℤ_[p])) := by ring
  have hpm1 : ((p - 1 : ℕ) : ℤ_[p]) = (p : ℤ_[p]) - 1 := by
    have h1 : (p - 1 : ℕ) + 1 = p := by omega
    have h2 : (((p - 1 : ℕ) + 1 : ℕ) : ℤ_[p]) = (p : ℤ_[p]) := by exact_mod_cast h1
    push_cast at h2
    linear_combination h2
  -- Show `G(a)` is divisible by `p`
  have hGa_dvd : ∃ q : ℤ_[p], G.aeval a = (p : ℤ_[p]) * q := by
    rcases hH_mod a with ⟨qH, hqH⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Algebra.algebraMap_self,
      Polynomial.map_id]
    have hG_eval : Polynomial.eval a G =
        ((r : ℤ_[p]) + (p : ℤ_[p]) * a) ^ 2 * Polynomial.eval a H - w := by
      simp [G]
    rw [hG_eval, hqH, hpm1]
    set B := (c_nat : ℤ_[p]) + ((p : ℤ_[p]) - 1) * (r : ℤ_[p]) ^ (p - 2) * a + (p : ℤ_[p]) * qH
    refine ⟨(2 * (r : ℤ_[p]) * a + (p : ℤ_[p]) * a ^ 2) * B +
        (r : ℤ_[p]) ^ 2 * ((r : ℤ_[p]) ^ (p - 2) * a + qH) -
        (r : ℤ_[p]) * (c_nat : ℤ_[p]) * a, ?_⟩
    have hexpand :
        ((r : ℤ_[p]) + (p : ℤ_[p]) * a) ^ 2 * B - w =
          (r : ℤ_[p]) ^ 2 * (c_nat : ℤ_[p]) -
            ((r : ℤ_[p]) ^ 2 * (r : ℤ_[p]) ^ (p - 2)) * a - w +
          (p : ℤ_[p]) * ((2 * (r : ℤ_[p]) * a + (p : ℤ_[p]) * a ^ 2) * B +
            (r : ℤ_[p]) ^ 2 * ((r : ℤ_[p]) ^ (p - 2) * a + qH)) := by
      dsimp [B]; ring
    rw [hexpand, hr_p2]
    linear_combination -hra
  -- Show `G'(a) ≡ -r (mod p)`
  have hGda_mod : ∃ q : ℤ_[p], G.derivative.aeval a = -(r : ℤ_[p]) + (p : ℤ_[p]) * q := by
    rcases hHd_mod a with ⟨qHd, hqHd⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Algebra.algebraMap_self,
      Polynomial.map_id]
    have hderiv_G : G.derivative =
        (2 * (Polynomial.C (r : ℤ_[p]) + Polynomial.C (p : ℤ_[p]) * Polynomial.X) *
            Polynomial.C (p : ℤ_[p])) * H +
          (Polynomial.C (r : ℤ_[p]) + Polynomial.C (p : ℤ_[p]) * Polynomial.X) ^ 2 *
            H.derivative := by
      simp [G, Polynomial.derivative_pow, Polynomial.C_ofNat]
    rw [hderiv_G]
    have hev_G' : Polynomial.eval a
        ((2 * (Polynomial.C (r : ℤ_[p]) + Polynomial.C (p : ℤ_[p]) * Polynomial.X) *
            Polynomial.C (p : ℤ_[p])) * H +
          (Polynomial.C (r : ℤ_[p]) + Polynomial.C (p : ℤ_[p]) * Polynomial.X) ^ 2 *
            H.derivative) =
        2 * ((r : ℤ_[p]) + (p : ℤ_[p]) * a) * (p : ℤ_[p]) * Polynomial.eval a H +
          ((r : ℤ_[p]) + (p : ℤ_[p]) * a) ^ 2 * Polynomial.eval a H.derivative := by
      simp
    rw [hev_G', hqHd, hpm1]
    set Hv := Polynomial.eval a H
    set Hd := ((p : ℤ_[p]) - 1) * (r : ℤ_[p]) ^ (p - 2) + (p : ℤ_[p]) * qHd
    refine ⟨2 * ((r : ℤ_[p]) + (p : ℤ_[p]) * a) * Hv +
        (2 * (r : ℤ_[p]) * a + (p : ℤ_[p]) * a ^ 2) * Hd +
        (r : ℤ_[p]) ^ 2 * ((r : ℤ_[p]) ^ (p - 2) + qHd) -
        (r : ℤ_[p]) * (c_nat : ℤ_[p]), ?_⟩
    have hexpand :
        2 * ((r : ℤ_[p]) + (p : ℤ_[p]) * a) * (p : ℤ_[p]) * Hv +
            ((r : ℤ_[p]) + (p : ℤ_[p]) * a) ^ 2 * Hd =
          -((r : ℤ_[p]) ^ 2 * (r : ℤ_[p]) ^ (p - 2)) +
          (p : ℤ_[p]) * (2 * ((r : ℤ_[p]) + (p : ℤ_[p]) * a) * Hv +
            (2 * (r : ℤ_[p]) * a + (p : ℤ_[p]) * a ^ 2) * Hd +
            (r : ℤ_[p]) ^ 2 * ((r : ℤ_[p]) ^ (p - 2) + qHd)) := by
      dsimp [Hd]; ring
    rw [hexpand, hr_p2]
    ring
  have hp_inv_lt : ‖(p : ℤ_[p])‖ < 1 := by
    rw [PadicInt.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have hGa_lt : ‖G.aeval a‖ < 1 := by
    rcases hGa_dvd with ⟨q, hq⟩
    rw [hq, norm_mul]
    have hq1 : ‖q‖ ≤ 1 := PadicInt.norm_le_one q
    calc
      ‖(p : ℤ_[p])‖ * ‖q‖ ≤ ‖(p : ℤ_[p])‖ * 1 :=
        mul_le_mul_of_nonneg_left hq1 (norm_nonneg _)
      _ < 1 := by linarith
  have hGda_eq : ‖G.derivative.aeval a‖ = 1 := by
    rcases hGda_mod with ⟨q, hq⟩
    rw [hq]
    have hlt : ‖(p : ℤ_[p]) * q‖ < ‖-(r : ℤ_[p])‖ := by
      rw [norm_neg, hr_norm, norm_mul]
      have hq1 : ‖q‖ ≤ 1 := PadicInt.norm_le_one q
      calc
        ‖(p : ℤ_[p])‖ * ‖q‖ ≤ ‖(p : ℤ_[p])‖ * 1 :=
          mul_le_mul_of_nonneg_left hq1 (norm_nonneg _)
        _ < 1 := by linarith
    rw [PadicInt.norm_add_eq_max_of_ne (ne_of_gt hlt), max_eq_left hlt.le, norm_neg, hr_norm]
  have hhensel : ‖G.aeval a‖ < ‖G.derivative.aeval a‖ ^ 2 := by
    rw [hGda_eq]; simpa using hGa_lt
  rcases hensels_lemma (p := p) (F := G) (a := a) hhensel with ⟨v, hv_root, _, _, _⟩
  refine ⟨v, ?_⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Algebra.algebraMap_self,
    Polynomial.map_id] at hv_root
  have hv_eq : ((r : ℤ_[p]) + (p : ℤ_[p]) * v) ^ 2 * Polynomial.eval v H = w := by
    have h0 : ((r : ℤ_[p]) + (p : ℤ_[p]) * v) ^ 2 * Polynomial.eval v H - w = 0 := by
      simpa [G] using hv_root
    exact sub_eq_zero.mp h0
  have hH_eval : (p : ℤ_[p]) * Polynomial.eval v H =
      ((r : ℤ_[p]) + (p : ℤ_[p]) * v) ^ (p - 1) - 1 := by
    have hev := congrArg (Polynomial.eval v) hH_mul
    simpa using hev
  calc
    ((r : ℤ_[p]) + (p : ℤ_[p]) * v) ^ 2 * (((r : ℤ_[p]) + (p : ℤ_[p]) * v) ^ (p - 1) - 1)
        = ((r : ℤ_[p]) + (p : ℤ_[p]) * v) ^ 2 * ((p : ℤ_[p]) * Polynomial.eval v H) := by
          rw [hH_eval]
    _ = (p : ℤ_[p]) * (((r : ℤ_[p]) + (p : ℤ_[p]) * v) ^ 2 * Polynomial.eval v H) := by ring
    _ = (p : ℤ_[p]) * w := by rw [hv_eq]

/-- `(p - 1)`-ary preimage tree in `ℚ_[p]`: for every prime `p`, every `k : ℕ`, and every
`w ∈ ℤ_[p]`, `qpIter p k (x) = (w : ℚ_[p]) / p` has at least `(p - 1) ^ k` distinct solutions
`x ∈ ℚ_[p]`. -/
theorem qpIter_preimages (p : ℕ) [Fact p.Prime] (k : ℕ) :
    ∀ w : ℤ_[p],
      ∃ S : Finset ℚ_[p],
        S.card = (p - 1) ^ k ∧
        ∀ x ∈ S, Polynomial.aeval x (qpIter p k) = (w : ℚ_[p]) / (p : ℚ_[p]) := by
  classical
  have hp : p.Prime := Fact.out
  have hp_ne : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.ne_zero
  induction k with
  | zero =>
      intro w
      refine ⟨{(w : ℚ_[p]) / (p : ℚ_[p])}, by simp, ?_⟩
      intro x hx
      rw [Finset.mem_singleton] at hx
      subst hx
      simp [qpIter]
  | succ k ih =>
      intro w
      choose v hv using fun (r : ℕ) (hr : r ∈ Finset.Ico 1 p) =>
        padic_qp_ball_lift p r (Finset.mem_Ico.mp hr).1 (Finset.mem_Ico.mp hr).2 w
      let z : (r : {r // r ∈ Finset.Ico 1 p}) → ℤ_[p] :=
        fun r => (r.1 : ℤ_[p]) + (p : ℤ_[p]) * v r.1 r.2
      choose F hF_card hF_prop using fun r : {r // r ∈ Finset.Ico 1 p} => ih (z r)
      let S : Finset ℚ_[p] := (Finset.Ico 1 p).attach.biUnion F
      have hdisj : Set.PairwiseDisjoint
          ((Finset.Ico 1 p).attach : Set {r // r ∈ Finset.Ico 1 p}) F := by
        intro a _ b _ hab
        dsimp [Function.onFun]
        rw [Finset.disjoint_left]
        intro x hxa hxb
        have ha_eq := hF_prop a x hxa
        have hb_eq := hF_prop b x hxb
        have hz_eq_q : ((z a : ℤ_[p]) : ℚ_[p]) = ((z b : ℤ_[p]) : ℚ_[p]) :=
          (div_left_inj₀ hp_ne).mp (ha_eq.symm.trans hb_eq)
        have hz_eq : z a = z b := PadicInt.coe_inj.mp hz_eq_q
        have hdiff : ((a.1 : ℤ_[p]) - (b.1 : ℤ_[p])) = (p : ℤ_[p]) * (v b.1 b.2 - v a.1 a.2) := by
          dsimp [z] at hz_eq
          linear_combination hz_eq
        have hnorm_lt : ‖(((a.1 : ℤ) - (b.1 : ℤ) : ℤ) : ℤ_[p])‖ < 1 := by
          rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast, hdiff, norm_mul]
          have hvp : ‖(p : ℤ_[p])‖ < 1 := by
            rw [PadicInt.norm_p]
            exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
          have hv1 : ‖v b.1 b.2 - v a.1 a.2‖ ≤ 1 := PadicInt.norm_le_one _
          calc
            ‖(p : ℤ_[p])‖ * ‖v b.1 b.2 - v a.1 a.2‖ ≤ ‖(p : ℤ_[p])‖ * 1 :=
              mul_le_mul_of_nonneg_left hv1 (norm_nonneg _)
            _ < 1 := by linarith
        have hdvd : (p : ℤ) ∣ ((a.1 : ℤ) - (b.1 : ℤ)) := by
          by_contra hndvd
          have hcop : IsCoprime ((a.1 : ℤ) - (b.1 : ℤ)) (p : ℤ) :=
            ((Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd.mpr hndvd).symm
          have h1 : ‖(((a.1 : ℤ) - (b.1 : ℤ) : ℤ) : ℤ_[p])‖ = 1 :=
            PadicInt.norm_intCast_eq_one_iff.mpr hcop
          linarith
        have ha_mem := Finset.mem_Ico.mp a.2
        have hb_mem := Finset.mem_Ico.mp b.2
        have hab_eq : a.1 = b.1 := by
          obtain ⟨q, hq⟩ := hdvd
          have hq0 : q = 0 := by nlinarith
          rw [hq0, mul_zero] at hq
          omega
        exact hab (Subtype.ext hab_eq)
      refine ⟨S, ?_, ?_⟩
      · rw [Finset.card_biUnion hdisj]
        calc
          ∑ r ∈ (Finset.Ico 1 p).attach, (F r).card
              = ∑ _r ∈ (Finset.Ico 1 p).attach, (p - 1) ^ k :=
                  Finset.sum_congr rfl (fun r _ => hF_card r)
          _ = (Finset.Ico 1 p).attach.card * (p - 1) ^ k := by simp
          _ = (p - 1) ^ (k + 1) := by
                rw [Finset.card_attach, Nat.card_Ico, pow_succ']
      · intro x hx
        rcases Finset.mem_biUnion.mp hx with ⟨r, _, hxr⟩
        have hfk := hF_prop r x hxr
        have hvr := hv r.1 r.2
        have hvr_q : ((z r : ℤ_[p]) : ℚ_[p]) ^ 2 *
            (((z r : ℤ_[p]) : ℚ_[p]) ^ (p - 1) - 1) = (p : ℚ_[p]) * (w : ℚ_[p]) := by
          have hcast := congrArg (fun u : ℤ_[p] => (u : ℚ_[p])) hvr
          simpa [z] using hcast
        have hp_aeval : Polynomial.aeval x (Polynomial.C (p : ℤ)) = (p : ℚ_[p]) := by
          simp
        simp only [qpIter, map_mul, map_sub, map_pow, map_one, hp_aeval, hfk]
        have hmul_div : (p : ℚ_[p]) * ((z r : ℚ_[p]) / (p : ℚ_[p])) = (z r : ℚ_[p]) :=
          mul_div_cancel₀ _ hp_ne
        rw [hmul_div, div_pow, div_mul_eq_mul_div, hvr_q, sq, mul_div_mul_left _ _ hp_ne]

/-! ## 3. Addition-Chain / `CanBuild` Helpers for `Q_p^[k]` -/

/-- Repeated squaring: `{f}` builds `{f ^ (2 ^ d)}` in `d` gates. -/
theorem canBuild_pow_two_pow (f : Polynomial ℤ) (d : ℕ) :
    CanBuild ({f} : Set (Polynomial ℤ)) d {f ^ (2 ^ d)} := by
  induction d with
  | zero =>
      refine canBuild_subset ?_
      simp
  | succ d ih =>
      have h2 := canBuild_mul (f ^ (2 ^ d)) (f ^ (2 ^ d))
      have hcomb := canBuild_trans ih (by intro x hx; rcases hx with rfl | rfl <;> exact Or.inr rfl) h2
      refine canBuild_mono_out ?_ hcomb
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      right
      rw [Set.mem_singleton_iff, ← pow_add, pow_succ, mul_two]

/-- Build `{(2 ^ m : Polynomial ℤ)}` from `{1}` in `m` gates. -/
theorem canBuild_two_pow (m : ℕ) :
    CanBuild ({(1 : Polynomial ℤ)} : Set (Polynomial ℤ)) m {((2 ^ m : ℕ) : Polynomial ℤ)} := by
  induction m with
  | zero =>
      refine canBuild_subset ?_
      simp
  | succ m ih =>
      have hadd := canBuild_add ((2 ^ m : ℕ) : Polynomial ℤ) ((2 ^ m : ℕ) : Polynomial ℤ)
      have hcomb := canBuild_trans ih
        (by intro x hx; rcases hx with rfl | rfl <;> exact Or.inr rfl) hadd
      refine canBuild_mono_out ?_ hcomb
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      right
      rw [Set.mem_singleton_iff, pow_succ, mul_two, Nat.cast_add]

/-- Build any natural constant `(n : Polynomial ℤ)` from `{1}` in at most `2 * Nat.log 2 n + 2` gates. -/
theorem canBuild_nat_const (n : ℕ) :
    CanBuild ({(1 : Polynomial ℤ)} : Set (Polynomial ℤ)) (2 * Nat.log 2 n + 2)
      {(n : Polynomial ℤ)} := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
      by_cases hn0 : n = 0
      · subst hn0
        have h0 : CanBuild ({(1 : Polynomial ℤ)} : Set (Polynomial ℤ)) 1 {0} :=
          canBuild_mono_in (by simp) (canBuild_mono_out (by simp) (canBuild_sub (1 : Polynomial ℤ) 1))
        exact canBuild_mono_cost (by omega) (canBuild_mono_out (by simp) h0)
      · by_cases hn1 : n = 1
        · subst hn1
          exact canBuild_mono_cost (by omega) (canBuild_subset (by simp))
        · have hge2 : 2 ≤ n := by omega
          have hhalf_lt : n / 2 < n := Nat.div_lt_self (by omega) (by norm_num)
          have hlog : Nat.log 2 (n / 2) + 1 = Nat.log 2 n := by
            have := Nat.log_div_base 2 n
            have h1 : 1 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) (by omega)
            omega
          have hprev := ih (n / 2) hhalf_lt
          have hdbl := canBuild_add ((n / 2 : ℕ) : Polynomial ℤ) ((n / 2 : ℕ) : Polynomial ℤ)
          have h1 := canBuild_trans hprev
            (by intro x hx; rcases hx with rfl | rfl <;> exact Or.inr rfl) hdbl
          by_cases hmod : n % 2 = 0
          · have heq : ((n / 2 : ℕ) : Polynomial ℤ) + ((n / 2 : ℕ) : Polynomial ℤ) =
                (n : Polynomial ℤ) := by
              rw [← Nat.cast_add]
              congr 1; omega
            refine canBuild_mono_cost (by omega) (canBuild_mono_out ?_ h1)
            intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx
            right; simp [heq]
          · have hmod1 : n % 2 = 1 := by omega
            have hadd1 := canBuild_add
              (((n / 2 : ℕ) : Polynomial ℤ) + ((n / 2 : ℕ) : Polynomial ℤ)) 1
            have h2 := canBuild_trans h1
              (by
                intro x hx
                rcases hx with rfl | rfl
                · exact Or.inr (Or.inr rfl)
                · exact Or.inl rfl)
              hadd1
            have heq : ((n / 2 : ℕ) : Polynomial ℤ) + ((n / 2 : ℕ) : Polynomial ℤ) + 1 =
                (n : Polynomial ℤ) := by
              rw [← Nat.cast_add, ← Nat.cast_one, ← Nat.cast_add]
              congr 1; omega
            refine canBuild_mono_cost (by omega) (canBuild_mono_out ?_ h2)
            intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx
            right; simp [heq]

/-- Precompute the table `{f ^ j | j < B}` from `{1, f}` in `B` gates. -/
theorem canBuild_pow_table (f : Polynomial ℤ) (B : ℕ) :
    CanBuild ({(1 : Polynomial ℤ), f} : Set (Polynomial ℤ)) B
      (⋃ j < B, {f ^ j}) := by
  induction B with
  | zero =>
      simpa using canBuild_empty ({(1 : Polynomial ℤ), f} : Set (Polynomial ℤ))
  | succ B ih =>
      by_cases hB0 : B = 0
      · subst hB0
        refine canBuild_mono_cost (by omega) (canBuild_subset ?_)
        intro x hx
        simp only [Set.mem_iUnion, exists_prop, Set.mem_singleton_iff] at hx
        rcases hx with ⟨j, hj, rfl⟩
        have : j = 0 := by omega
        subst this
        simp
      · have hmul := canBuild_mul (f ^ (B - 1)) f
        have hsub : ({f ^ (B - 1), f} : Set (Polynomial ℤ)) ⊆
            ({(1 : Polynomial ℤ), f} : Set (Polynomial ℤ)) ∪ ⋃ j < B, {f ^ j} := by
          intro x hx
          rcases hx with rfl | rfl
          · right
            simp only [Set.mem_iUnion, exists_prop, Set.mem_singleton_iff]
            exact ⟨B - 1, by omega, rfl⟩
          · exact Or.inl (by simp)
        have hcomb := canBuild_trans ih hsub hmul
        refine canBuild_mono_out ?_ hcomb
        intro x hx
        simp only [Set.mem_iUnion, exists_prop, Set.mem_singleton_iff] at hx
        rcases hx with ⟨j, hj, rfl⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | hjeq
        · left
          simp only [Set.mem_iUnion, exists_prop, Set.mem_singleton_iff]
          exact ⟨j, hlt, rfl⟩
        · right
          rw [hjeq, Set.mem_singleton_iff, ← pow_succ, show B - 1 + 1 = B by omega]

/-- Windowed base-`2^w` exponentiation given the precomputed table `{f ^ j | j < 2 ^ w}`:
builds `{f ^ e}` in at most `(w + 1) * (Nat.log 2 e / w)` extra gates. -/
theorem canBuild_pow_from_table (w : ℕ) (hw : 1 ≤ w) (f : Polynomial ℤ) (e : ℕ) :
    CanBuild (⋃ j < 2 ^ w, {f ^ j}) ((w + 1) * (Nat.log 2 e / w)) {f ^ e} := by
  induction e using Nat.strong_induction_on with
  | ind e ih =>
      by_cases hlt : e < 2 ^ w
      · refine canBuild_mono_cost (Nat.zero_le _) (canBuild_subset ?_)
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        simp only [Set.mem_iUnion, exists_prop, Set.mem_singleton_iff]
        exact ⟨e, hlt, rfl⟩
      · have hge : 2 ^ w ≤ e := Nat.le_of_not_lt hlt
        have he_pos : 0 < e := by
          have : 0 < 2 ^ w := by positivity
          omega
        have hq_pos : 0 < e / 2 ^ w := Nat.div_pos hge (by positivity)
        have hq_lt : e / 2 ^ w < e := Nat.div_lt_self he_pos (by
          have : 2 ^ 1 ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
          omega)
        have hlog_ge : w ≤ Nat.log 2 e := Nat.le_log_of_pow_le (by norm_num) hge
        have hlog_q : Nat.log 2 (e / 2 ^ w) + w ≤ Nat.log 2 e := by
          have h1 : 2 ^ (Nat.log 2 (e / 2 ^ w)) ≤ e / 2 ^ w :=
            Nat.pow_log_le_self 2 hq_pos.ne'
          have h2 : 2 ^ (Nat.log 2 (e / 2 ^ w) + w) ≤ e := by
            rw [pow_add]
            calc
              2 ^ Nat.log 2 (e / 2 ^ w) * 2 ^ w ≤ (e / 2 ^ w) * 2 ^ w :=
                Nat.mul_le_mul_right _ h1
              _ ≤ e := Nat.div_mul_le_self e (2 ^ w)
          exact Nat.le_log_of_pow_le (by norm_num) h2
        have hdiv_step : Nat.log 2 (e / 2 ^ w) / w + 1 ≤ Nat.log 2 e / w := by
          have hadd : (Nat.log 2 (e / 2 ^ w) + w) / w = Nat.log 2 (e / 2 ^ w) / w + 1 :=
            Nat.add_div_right _ (by omega)
          rw [← hadd]
          exact Nat.div_le_div_right hlog_q
        have hprev := ih (e / 2 ^ w) hq_lt
        have hsq := canBuild_pow_two_pow (f ^ (e / 2 ^ w)) w
        have h1 := canBuild_trans hprev
          (by intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx; exact Or.inr rfl) hsq
        have hmul := canBuild_mul ((f ^ (e / 2 ^ w)) ^ (2 ^ w)) (f ^ (e % 2 ^ w))
        have hsub2 : ({(f ^ (e / 2 ^ w)) ^ (2 ^ w), f ^ (e % 2 ^ w)} : Set (Polynomial ℤ)) ⊆
            (⋃ j < 2 ^ w, {f ^ j}) ∪ ({f ^ (e / 2 ^ w)} ∪ {(f ^ (e / 2 ^ w)) ^ (2 ^ w)}) := by
          intro x hx
          rcases hx with rfl | rfl
          · exact Or.inr (Or.inr rfl)
          · left
            simp only [Set.mem_iUnion, exists_prop, Set.mem_singleton_iff]
            exact ⟨e % 2 ^ w, Nat.mod_lt e (by positivity), rfl⟩
        have h2 := canBuild_trans h1 hsub2 hmul
        have hcost : (w + 1) * (Nat.log 2 (e / 2 ^ w) / w) + w + 1 ≤
            (w + 1) * (Nat.log 2 e / w) := by
          calc
            (w + 1) * (Nat.log 2 (e / 2 ^ w) / w) + w + 1
                = (w + 1) * (Nat.log 2 (e / 2 ^ w) / w + 1) := by ring
            _ ≤ (w + 1) * (Nat.log 2 e / w) := Nat.mul_le_mul_left _ hdiv_step
        refine canBuild_mono_cost hcost (canBuild_mono_out ?_ h2)
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        right
        rw [Set.mem_singleton_iff, ← pow_mul, ← pow_add, mul_comm (e / 2 ^ w), Nat.div_add_mod]

/-- Windowed base-`2^w` exponentiation from `{1, f}` in `2^w + (w + 1) * (Nat.log 2 e / w)` gates. -/
theorem canBuild_pow_window (w : ℕ) (hw : 1 ≤ w) (f : Polynomial ℤ) (e : ℕ) :
    CanBuild ({(1 : Polynomial ℤ), f} : Set (Polynomial ℤ))
      (2 ^ w + (w + 1) * (Nat.log 2 e / w)) {f ^ e} := by
  have h1 := canBuild_pow_table f (2 ^ w)
  have h2 := canBuild_pow_from_table w hw f e
  have hcomb := canBuild_trans h1 Set.subset_union_right h2
  exact canBuild_mono_out Set.subset_union_right hcomb

/-- One iteration of `Q_p` from `{1, C(p^2), f}` using any `d`-gate exponentiation engine for
`e = (p - 1) / 2` (for odd `p`) costs `d + 4` gates. -/
theorem canBuild_qp_step (p d : ℕ) (hp_odd : p % 2 = 1) (f : Polynomial ℤ)
    (hexp : CanBuild ({(1 : Polynomial ℤ), (p : Polynomial ℤ) ^ 2 * f ^ 2} : Set (Polynomial ℤ))
      d {((p : Polynomial ℤ) ^ 2 * f ^ 2) ^ ((p - 1) / 2)}) :
    CanBuild ({(1 : Polynomial ℤ), (p : Polynomial ℤ) ^ 2, f} : Set (Polynomial ℤ)) (d + 4)
      {f ^ 2 * ((Polynomial.C (p : ℤ) * f) ^ (p - 1) - 1)} := by
  have h1 : CanBuild ({(1 : Polynomial ℤ), (p : Polynomial ℤ) ^ 2, f} : Set (Polynomial ℤ))
      1 {f * f} := canBuild_mono_in (by intro x hx; rcases hx with rfl | rfl <;> simp)
        (canBuild_mul f f)
  have h2 : CanBuild ({(1 : Polynomial ℤ), (p : Polynomial ℤ) ^ 2, f} ∪ {f * f}) 1
      {(p : Polynomial ℤ) ^ 2 * (f * f)} :=
    canBuild_mono_in (by intro x hx; rcases hx with rfl | rfl <;> simp)
      (canBuild_mul ((p : Polynomial ℤ) ^ 2) (f * f))
  have h12 := canBuild_seq h1 h2
  have hsq_eq : (p : Polynomial ℤ) ^ 2 * (f * f) = (p : Polynomial ℤ) ^ 2 * f ^ 2 := by ring
  have h3 := canBuild_trans h12
    (by
      intro x hx
      rcases hx with rfl | rfl
      · exact Or.inl (by simp)
      · right; right; simp [hsq_eq])
    hexp
  set z := ((p : Polynomial ℤ) ^ 2 * f ^ 2) ^ ((p - 1) / 2)
  have h4 := canBuild_trans h3
    (by
      intro x hx
      rcases hx with rfl | rfl
      · exact Or.inr (Or.inr rfl)
      · exact Or.inl (by simp))
    (canBuild_sub z 1)
  have h5 := canBuild_trans h4
    (by
      intro x hx
      rcases hx with rfl | rfl
      · exact Or.inr (Or.inl (Or.inl (Or.inl rfl)))
      · exact Or.inr (Or.inr rfl))
    (canBuild_mul (f * f) (z - 1))
  have hval : f * f * (z - 1) = f ^ 2 * ((Polynomial.C (p : ℤ) * f) ^ (p - 1) - 1) := by
    have hp_even : 2 * ((p - 1) / 2) = p - 1 := by omega
    have hz : z = (Polynomial.C (p : ℤ) * f) ^ (p - 1) := by
      dsimp [z]
      have hbase : (p : Polynomial ℤ) ^ 2 * f ^ 2 = (Polynomial.C (p : ℤ) * f) ^ 2 := by
        simp [mul_pow]
      rw [hbase, ← pow_mul, hp_even]
    rw [hz, ← sq]
  refine canBuild_mono_cost (by omega) (canBuild_mono_out ?_ h5)
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  right
  rw [Set.mem_singleton_iff, hval]

/-! ## 4. Headline Uniform $p$-Adic Barrier Theorems -/

/-- **Fermat-Prime $p$-Adic Lower Bound (`α_{ℚ_{2^m+1}} ≥ m / (m + 3)`):**
For every prime `p = 2 ^ m + 1` (`m ≥ 1`) and every `k ≥ 1`, there exists a constant-free SLP
of length `(m + 3) * k + (m + 3)` computing a nonzero polynomial `f ∈ ℤ[X]` with at least
`(p - 1) ^ k` distinct roots in `ℚ_[p]`.
In particular, `p = 65537` (`m = 16`) gives rate `16 / 19 ≈ 0.8421`. -/
theorem tau_padic_fermat (p m : ℕ) [Fact p.Prime] (hm : 1 ≤ m) (hp_eq : p = 2 ^ m + 1)
    (k : ℕ) (_hk : 1 ≤ k) :
    ∃ P : SLP ((m + 3) * k + (m + 3)),
      P.evalPoly ≠ 0 ∧
      ∃ S : Finset ℚ_[p],
        S.card = (p - 1) ^ k ∧ ∀ r ∈ S, Polynomial.aeval r P.evalPoly = 0 := by
  have hp : p.Prime := Fact.out
  have hp_odd : p % 2 = 1 := by
    have : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
    omega
  have hdiv : (p - 1) / 2 = 2 ^ (m - 1) := by
    rw [hp_eq]
    have h1 : 2 ^ m = 2 * 2 ^ (m - 1) := by
      conv_lhs => rw [show m = (m - 1) + 1 by omega, pow_succ']
    omega
  have hsetup_2m : CanBuild ({(1 : Polynomial ℤ), Polynomial.X} : Set (Polynomial ℤ)) m
      {((2 ^ m : ℕ) : Polynomial ℤ)} :=
    canBuild_mono_in (by intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx; simp)
      (canBuild_two_pow m)
  have hsetup_p : CanBuild ({(1 : Polynomial ℤ), Polynomial.X} : Set (Polynomial ℤ)) (m + 1)
      {(p : Polynomial ℤ)} := by
    have hadd := canBuild_add ((2 ^ m : ℕ) : Polynomial ℤ) 1
    have hcomb := canBuild_trans hsetup_2m
      (by intro x hx; rcases hx with rfl | rfl; exact Or.inr rfl; exact Or.inl (by simp)) hadd
    refine canBuild_mono_out ?_ hcomb
    intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx
    right; rw [Set.mem_singleton_iff, hp_eq, Nat.cast_add, Nat.cast_one]
  have hsetup : CanBuild ({(1 : Polynomial ℤ), Polynomial.X} : Set (Polynomial ℤ)) (m + 2)
      {(p : Polynomial ℤ) ^ 2} := by
    have hmul := canBuild_mul (p : Polynomial ℤ) (p : Polynomial ℤ)
    have hcomb := canBuild_trans hsetup_p
      (by intro x hx; rcases hx with rfl | rfl <;> exact Or.inr rfl) hmul
    refine canBuild_mono_out ?_ hcomb
    intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx
    right; rw [Set.mem_singleton_iff, sq]
  have hiter : ∀ j : ℕ,
      CanBuild ({(1 : Polynomial ℤ), (p : Polynomial ℤ) ^ 2, Polynomial.X} : Set (Polynomial ℤ))
        ((m + 3) * j) {qpIter p j} := by
    intro j
    induction j with
    | zero =>
        refine canBuild_subset ?_
        simp [qpIter]
    | succ j ih =>
        have hstep := canBuild_qp_step p (m - 1) hp_odd (qpIter p j) (by
          rw [hdiv]
          exact canBuild_mono_in (by intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx; simp)
            (canBuild_pow_two_pow ((p : Polynomial ℤ) ^ 2 * (qpIter p j) ^ 2) (m - 1)))
        have hcomb := canBuild_trans ih
          (by
            intro x hx
            rcases hx with rfl | rfl | rfl
            · exact Or.inl (by simp)
            · exact Or.inl (by simp)
            · exact Or.inr rfl)
          hstep
        have hcost : (m + 3) * j + (m - 1 + 4) = (m + 3) * (j + 1) := by
          rw [show m - 1 + 4 = m + 3 by omega]; ring
        rw [hcost] at hcomb
        refine canBuild_mono_out ?_ hcomb
        intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx
        right; simp [qpIter]
  have hfull := canBuild_trans hsetup
    (by
      intro x hx
      rcases hx with rfl | rfl | rfl
      · exact Or.inl (by simp)
      · exact Or.inr rfl
      · exact Or.inl (by simp))
    (hiter k)
  have hcomp0 : Computes (0 + (m + 2 + (m + 3) * k))
      ({(1 : Polynomial ℤ), Polynomial.X} ∪ ({(p : Polynomial ℤ) ^ 2} ∪ {qpIter p k})) :=
    hfull 0 _ Set.Subset.rfl computes_nil
  have hcomp : Computes ((m + 3) * k + (m + 2))
      ({(1 : Polynomial ℤ), Polynomial.X} ∪ ({(p : Polynomial ℤ) ^ 2} ∪ {qpIter p k})) := by
    rwa [show 0 + (m + 2 + (m + 3) * k) = (m + 3) * k + (m + 2) by ring] at hcomp0
  rcases computes_extract hcomp (Or.inr (Or.inr rfl)) with ⟨P, hP⟩
  refine ⟨P, ?_, ?_⟩
  · rw [hP]; exact qpIter_ne_zero p hp k
  · rcases qpIter_preimages p k 0 with ⟨S, hcard, hS⟩
    refine ⟨S, hcard, ?_⟩
    intro r hr
    rw [hP, hS r hr, PadicInt.coe_zero, zero_div]

/-- General odd-prime SLP length bound via base-`2^w` windowed addition chains. -/
theorem tau_padic_window_slp (p w k : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hw : 1 ≤ w) :
    ∃ P : SLP ((2 ^ w + (w + 1) * (Nat.log 2 p / w) + 4) * k + (2 * Nat.log 2 p + 4)),
      P.evalPoly ≠ 0 ∧
      ∃ S : Finset ℚ_[p],
        S.card = (p - 1) ^ k ∧ ∀ r ∈ S, Polynomial.aeval r P.evalPoly = 0 := by
  have hp : p.Prime := Fact.out
  have hp_odd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
  set d := 2 ^ w + (w + 1) * (Nat.log 2 p / w)
  have hsetup_p : CanBuild ({(1 : Polynomial ℤ), Polynomial.X} : Set (Polynomial ℤ))
      (2 * Nat.log 2 p + 2) {(p : Polynomial ℤ)} :=
    canBuild_mono_in (by intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx; simp)
      (canBuild_nat_const p)
  have hsetup : CanBuild ({(1 : Polynomial ℤ), Polynomial.X} : Set (Polynomial ℤ))
      (2 * Nat.log 2 p + 3) {(p : Polynomial ℤ) ^ 2} := by
    have hmul := canBuild_mul (p : Polynomial ℤ) (p : Polynomial ℤ)
    have hcomb := canBuild_trans hsetup_p
      (by intro x hx; rcases hx with rfl | rfl <;> exact Or.inr rfl) hmul
    refine canBuild_mono_out ?_ hcomb
    intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx
    right; rw [Set.mem_singleton_iff, sq]
  have hiter : ∀ j : ℕ,
      CanBuild ({(1 : Polynomial ℤ), (p : Polynomial ℤ) ^ 2, Polynomial.X} : Set (Polynomial ℤ))
        ((d + 4) * j) {qpIter p j} := by
    intro j
    induction j with
    | zero =>
        refine canBuild_subset ?_
        simp [qpIter]
    | succ j ih =>
        have hlog_le : Nat.log 2 ((p - 1) / 2) ≤ Nat.log 2 p :=
          Nat.log_mono_right (by omega)
        have hcost_exp : 2 ^ w + (w + 1) * (Nat.log 2 ((p - 1) / 2) / w) ≤ d :=
          Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.div_le_div_right hlog_le)) _
        have hstep := canBuild_qp_step p d hp_odd (qpIter p j)
          (canBuild_mono_cost hcost_exp
            (canBuild_pow_window w hw ((p : Polynomial ℤ) ^ 2 * (qpIter p j) ^ 2) ((p - 1) / 2)))
        have hcomb := canBuild_trans ih
          (by
            intro x hx
            rcases hx with rfl | rfl | rfl
            · exact Or.inl (by simp)
            · exact Or.inl (by simp)
            · exact Or.inr rfl)
          hstep
        have hcost : (d + 4) * j + (d + 4) = (d + 4) * (j + 1) := by ring
        rw [hcost] at hcomb
        refine canBuild_mono_out ?_ hcomb
        intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx
        right; simp [qpIter]
  have hfull := canBuild_trans hsetup
    (by
      intro x hx
      rcases hx with rfl | rfl | rfl
      · exact Or.inl (by simp)
      · exact Or.inr rfl
      · exact Or.inl (by simp))
    (hiter k)
  have hcomp0 : Computes (0 + (2 * Nat.log 2 p + 3 + (d + 4) * k))
      ({(1 : Polynomial ℤ), Polynomial.X} ∪ ({(p : Polynomial ℤ) ^ 2} ∪ {qpIter p k})) :=
    hfull 0 _ Set.Subset.rfl computes_nil
  have hcomp : Computes ((d + 4) * k + (2 * Nat.log 2 p + 3))
      ({(1 : Polynomial ℤ), Polynomial.X} ∪ ({(p : Polynomial ℤ) ^ 2} ∪ {qpIter p k})) := by
    rwa [show 0 + (2 * Nat.log 2 p + 3 + (d + 4) * k) =
      (d + 4) * k + (2 * Nat.log 2 p + 3) by ring] at hcomp0
  rcases computes_extract hcomp (Or.inr (Or.inr rfl)) with ⟨P, hP⟩
  refine ⟨P, ?_, ?_⟩
  · rw [hP]; exact qpIter_ne_zero p hp k
  · rcases qpIter_preimages p k 0 with ⟨S, hcard, hS⟩
    refine ⟨S, hcard, ?_⟩
    intro r hr
    rw [hP, hS r hr, PadicInt.coe_zero, zero_div]

/-- **Uniform $p$-Adic Barrier (`lim_{p → ∞} α_{ℚ_p} = 1`):**
For every `ε > 0`, there exists a prime `p`, a step cost `τ_step > 0`, and a setup overhead `C`
such that for every `k ≥ 1`, there is a constant-free SLP of length `τ_step * k + C` computing a
nonzero polynomial `f ∈ ℤ[X]` with `(p - 1) ^ k` distinct roots in `ℚ_[p]`, while the exponential
growth rate `log_2(p - 1) / τ_step` strictly exceeds `1 - ε`.

Consequently, no proof that works uniformly across primes `p` can establish
`z_{ℚ_p}(f) ≤ 2 ^ ((1 - ε) * τ(f))` for any constant `ε > 0`. -/
theorem tau_padic_rate_arbitrarily_close_to_one (ε : ℝ) (hε : 0 < ε) :
    ∃ (p : ℕ) (_ : Fact p.Prime) (τ_step C : ℕ),
      0 < τ_step ∧
      1 - ε < Real.logb 2 (p - 1 : ℝ) / (τ_step : ℝ) ∧
      ∀ k : ℕ, 1 ≤ k →
        ∃ P : SLP (τ_step * k + C),
          P.evalPoly ≠ 0 ∧
          ∃ S : Finset ℚ_[p],
            S.card = (p - 1) ^ k ∧ ∀ r ∈ S, Polynomial.aeval r P.evalPoly = 0 := by
  obtain ⟨w, hw_gt⟩ := exists_nat_gt (3 / ε)
  have hw1 : 1 ≤ w := by
    by_contra h
    have hw0 : w = 0 := by omega
    subst hw0
    have : 0 < 3 / ε := by positivity
    linarith
  obtain ⟨M, hM_gt⟩ := exists_nat_gt (((2 ^ w + 6 : ℕ) : ℝ) * (3 / ε) + 4)
  obtain ⟨p, hp_ge, hp_prime⟩ := Nat.exists_infinite_primes (2 ^ M)
  have : Fact p.Prime := ⟨hp_prime⟩
  have hM_ge4 : 4 ≤ M := by
    have hnonneg : (0 : ℝ) ≤ ((2 ^ w + 6 : ℕ) : ℝ) * (3 / ε) := by positivity
    have h4 : (4 : ℝ) < (M : ℝ) := by linarith
    exact_mod_cast h4.le
  have hp_ge16 : 16 ≤ p := by
    have : 2 ^ 4 ≤ 2 ^ M := Nat.pow_le_pow_right (by norm_num) hM_ge4
    omega
  have hp2 : p ≠ 2 := by omega
  let τ_step : ℕ := 2 ^ w + (w + 1) * (Nat.log 2 p / w) + 4
  let C : ℕ := 2 * Nat.log 2 p + 4
  refine ⟨p, inferInstance, τ_step, C, by positivity, ?_, ?_⟩
  · have hL_ge : M ≤ Nat.log 2 p := Nat.le_log_of_pow_le (by norm_num) hp_ge
    set L : ℕ := Nat.log 2 p
    have hL_pos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (show 0 < L by omega)
    have hτ_pos : (0 : ℝ) < (τ_step : ℝ) := by positivity
    have h2pow_le : (2 : ℝ) ^ (L - 1) ≤ (p - 1 : ℝ) := by
      have h1 : 2 ^ L ≤ p := Nat.pow_log_le_self 2 (by omega)
      have h2 : 2 ^ (L - 1) + 1 ≤ 2 ^ L := by
        have hL1 : 1 ≤ L := by omega
        have hmul : 2 ^ L = 2 * 2 ^ (L - 1) := by
          conv_lhs => rw [show L = (L - 1) + 1 by omega, pow_succ']
        have hpos : 1 ≤ 2 ^ (L - 1) := Nat.one_le_pow _ _ (by norm_num)
        omega
      have h3 : 2 ^ (L - 1) ≤ p - 1 := by omega
      have h3r : ((2 ^ (L - 1) : ℕ) : ℝ) ≤ ((p - 1 : ℕ) : ℝ) := by exact_mod_cast h3
      rw [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_sub (by omega), Nat.cast_one] at h3r
      exact h3r
    have hlog_ge : (L : ℝ) - 1 ≤ Real.logb 2 (p - 1 : ℝ) := by
      have hbase : (1 : ℝ) < 2 := by norm_num
      have hpos : (0 : ℝ) < (2 : ℝ) ^ (L - 1) := by positivity
      have hmono := Real.logb_le_logb_of_le hbase hpos h2pow_le
      rw [Real.logb_pow, Real.logb_self_eq_one hbase, mul_one] at hmono
      have hcast : ((L - 1 : ℕ) : ℝ) = (L : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega), Nat.cast_one]
      rwa [hcast] at hmono
    have hτ_le : (τ_step : ℝ) ≤ (L : ℝ) + (L : ℝ) / (w : ℝ) + ((2 ^ w + 4 : ℕ) : ℝ) := by
      have hdiv_le : ((L / w : ℕ) : ℝ) ≤ (L : ℝ) / (w : ℝ) := by
        rw [le_div_iff₀ (by exact_mod_cast (show 0 < w by omega) : (0 : ℝ) < (w : ℝ))]
        exact_mod_cast Nat.div_mul_le_self L w
      have hmul_div : ((w * (L / w) : ℕ) : ℝ) ≤ (L : ℝ) := by
        exact_mod_cast Nat.mul_div_le L w
      have hτ_eq : (τ_step : ℝ) =
          ((2 ^ w + 4 : ℕ) : ℝ) + ((w * (L / w) : ℕ) : ℝ) + ((L / w : ℕ) : ℝ) := by
        dsimp [τ_step, L]
        push_cast
        ring
      rw [hτ_eq]
      linarith
    have hw_pos : (0 : ℝ) < (w : ℝ) := by exact_mod_cast (show 0 < w by omega)
    have h1_over_w : (1 : ℝ) / (w : ℝ) < ε / 3 := by
      rw [div_lt_div_iff₀ hw_pos (by norm_num : (0 : ℝ) < 3)]
      have h := (div_lt_iff₀ hε).mp hw_gt
      linarith
    have hL_gt_M : ((2 ^ w + 6 : ℕ) : ℝ) * (3 / ε) < (L : ℝ) := by
      have hLM : (M : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL_ge
      linarith
    have hC_small : ((2 ^ w + 5 : ℕ) : ℝ) < (ε / 3) * (L : ℝ) := by
      have hdiv : ((2 ^ w + 6 : ℕ) : ℝ) < (L : ℝ) / (3 / ε) :=
        (lt_div_iff₀ (by positivity : (0 : ℝ) < 3 / ε)).mpr hL_gt_M
      have h1 : ((2 ^ w + 5 : ℕ) : ℝ) < ((2 ^ w + 6 : ℕ) : ℝ) := by push_cast; linarith
      have h2 : (L : ℝ) / (3 / ε) = (ε / 3) * (L : ℝ) := by field_simp
      linarith
    have hLw_small : (L : ℝ) / (w : ℝ) < (ε / 3) * (L : ℝ) := by
      calc
        (L : ℝ) / (w : ℝ) = ((1 : ℝ) / (w : ℝ)) * (L : ℝ) := by ring
        _ < (ε / 3) * (L : ℝ) := mul_lt_mul_of_pos_right h1_over_w hL_pos
    have hkey : (1 - ε) * (τ_step : ℝ) < (L : ℝ) - 1 := by
      by_cases hε1 : 1 ≤ ε
      · have hnonpos : (1 - ε) * (τ_step : ℝ) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (by linarith) hτ_pos.le
        have hL2 : (1 : ℝ) < (L : ℝ) := by exact_mod_cast (show 1 < L by omega)
        linarith
      · have h1mε : 0 < 1 - ε := by linarith
        have h2w5 : ((2 ^ w + 4 : ℕ) : ℝ) + 1 = ((2 ^ w + 5 : ℕ) : ℝ) := by push_cast; ring
        have hτ_lt : (τ_step : ℝ) < (1 + 2 * (ε / 3)) * (L : ℝ) - 1 := by
          linarith
        have hprod : (1 - ε) * (τ_step : ℝ) ≤ (1 - ε) * ((1 + 2 * (ε / 3)) * (L : ℝ) - 1) :=
          mul_le_mul_of_nonneg_left hτ_lt.le h1mε.le
        nlinarith [sq_nonneg ε]
    rw [lt_div_iff₀ hτ_pos]
    linarith
  · intro k _
    exact tau_padic_window_slp p w k hp2 hw1

end Research.PvsNP.Tau

end
