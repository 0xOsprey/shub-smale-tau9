module

public import Research.PvsNP.Tau.TauRecords

@[expose] public section

namespace Research.PvsNP.Tau

/-!
# Exact Sharpness for Bounded-Multiplication Straight-Line Programs (`m = 0, 1, 2, 3`)

This module proves that the exponential upper bound `intRootCount P.evalPoly ≤ 2 ^ m`
for constant-free straight-line programs (`SLP`) with at most `m` multiplication gates
is **exact and sharp** for every `m ∈ {0, 1, 2, 3}` (`2^0 = 1`, `2^1 = 2`, `2^2 = 4`,
`2^3 = 8`).

In particular, `slpThreeMulEight` constructs the degree-`8` polynomial
`((X * (X + 1) - 16)^2 - 106)^2 - 8100` using **exact `mulCount = 3`** (building all
constants via pure addition/subtraction chains) and achieves all `8` distinct integer
roots `{-6, -5, -4, -2, 1, 3, 4, 5}`.
-/

/-! ## 1. Bounded-Multiplication Root-Count Predicate & General Upper Bounds -/

/-- `zMaxMulGe m r` asserts that there exists a constant-free straight-line program
with at most `m` multiplication gates computing a nonzero polynomial in `ℤ[X]`
with at least `r` distinct integer roots. -/
def zMaxMulGe (m r : ℕ) : Prop :=
  ∃ (τ : ℕ) (P : SLP τ), P.mulCount ≤ m ∧ P.evalPoly ≠ 0 ∧ r ≤ intRootCount P.evalPoly

/-- Helper lemma to certify `zMaxMulGe m r` directly from computable integer evaluations
and `mulCount` of a concrete `P : SLP τ`. -/
theorem zMaxMulGe_of_evalInt {τ m r : ℕ} (P : SLP τ) (S : Finset ℤ) (b : ℤ)
    (hmul : P.mulCount ≤ m) (hcard : r ≤ S.card) (hb : P.evalInt b ≠ 0)
    (hS : ∀ a ∈ S, P.evalInt a = 0) :
    zMaxMulGe m r := by
  have hne : P.evalPoly ≠ 0 := by
    intro h0
    apply hb
    rw [P.evalInt_eq_eval, h0, Polynomial.eval_zero]
  refine ⟨τ, P, hmul, hne, ?_⟩
  have hsub : S ⊆ intRootSet P.evalPoly := by
    intro a ha
    rw [mem_intRootSet_iff]
    refine ⟨hne, ?_⟩
    rw [Polynomial.IsRoot, ← P.evalInt_eq_eval]
    exact hS a ha
  exact hcard.trans (Finset.card_le_card hsub)

/-- SLPs with at most `m` multiplication gates compute polynomials of degree at most `2 ^ m`. -/
theorem tau_mulCount_natDegree_le_two_pow {τ m : ℕ} (P : SLP τ) (hm : P.mulCount ≤ m) :
    P.evalPoly.natDegree ≤ 2 ^ m :=
  (slp_natDegree_le_two_pow_mulCount P ⟨τ + 1, Nat.lt_succ_self _⟩).trans
    (Nat.pow_le_pow_right (by omega) hm)

/-- Nonzero polynomials computed by SLPs with at most `m` multiplication gates
have at most `2 ^ m` distinct integer roots. -/
theorem tau_mulCount_intRootCount_le_two_pow {τ m : ℕ} (P : SLP τ) (hm : P.mulCount ≤ m)
    (hne : P.evalPoly ≠ 0) :
    intRootCount P.evalPoly ≤ 2 ^ m :=
  (intRootCount_le_natDegree hne).trans (tau_mulCount_natDegree_le_two_pow P hm)

/-- SLPs with at most `3` multiplication gates compute polynomials of degree at most `8`. -/
theorem tau_three_mul_natDegree_le_eight {τ : ℕ} (P : SLP τ) (hm : P.mulCount ≤ 3) :
    P.evalPoly.natDegree ≤ 8 :=
  tau_mulCount_natDegree_le_two_pow P hm

/-- Nonzero polynomials computed by SLPs with at most `3` multiplication gates
have at most `8` distinct integer roots. -/
theorem tau_three_mul_intRootCount_le_eight {τ : ℕ} (P : SLP τ) (hm : P.mulCount ≤ 3)
    (hne : P.evalPoly ≠ 0) :
    intRootCount P.evalPoly ≤ 8 :=
  (intRootCount_le_natDegree hne).trans (tau_three_mul_natDegree_le_eight P hm)

/-! ## 2. Three-Multiplication 8-Root Sharpness Witness -/

/-- Constant-free `SLP 25` with **exactly `3` multiplication gates** computing
`((X * (X + 1) - 16)^2 - 106)^2 - 8100`, with `8` distinct integer roots
`{-6, -5, -4, -2, 1, 3, 4, 5}`. All constants (`16`, `106`, `8100`) are constructed
via pure `add`/`sub` chains with zero extra multiplications. -/
def slpThreeMulEight : SLP 25 :=
  let p1  : SLP 1  := .snoc .nil .add ⟨0, by omega⟩ ⟨0, by omega⟩     -- w2  = 2
  let p2  : SLP 2  := .snoc p1   .add ⟨2, by omega⟩ ⟨2, by omega⟩     -- w3  = 4
  let p3  : SLP 3  := .snoc p2   .add ⟨3, by omega⟩ ⟨3, by omega⟩     -- w4  = 8
  let p4  : SLP 4  := .snoc p3   .add ⟨4, by omega⟩ ⟨4, by omega⟩     -- w5  = 16
  let p5  : SLP 5  := .snoc p4   .add ⟨5, by omega⟩ ⟨5, by omega⟩     -- w6  = 32
  let p6  : SLP 6  := .snoc p5   .add ⟨6, by omega⟩ ⟨6, by omega⟩     -- w7  = 64
  let p7  : SLP 7  := .snoc p6   .add ⟨7, by omega⟩ ⟨6, by omega⟩     -- w8  = 96
  let p8  : SLP 8  := .snoc p7   .add ⟨8, by omega⟩ ⟨4, by omega⟩     -- w9  = 104
  let p9  : SLP 9  := .snoc p8   .add ⟨9, by omega⟩ ⟨2, by omega⟩     -- w10 = 106
  let p10 : SLP 10 := .snoc p9   .add ⟨7, by omega⟩ ⟨7, by omega⟩     -- w11 = 128
  let p11 : SLP 11 := .snoc p10  .add ⟨11, by omega⟩ ⟨11, by omega⟩   -- w12 = 256
  let p12 : SLP 12 := .snoc p11  .add ⟨12, by omega⟩ ⟨12, by omega⟩   -- w13 = 512
  let p13 : SLP 13 := .snoc p12  .add ⟨13, by omega⟩ ⟨13, by omega⟩   -- w14 = 1024
  let p14 : SLP 14 := .snoc p13  .add ⟨14, by omega⟩ ⟨14, by omega⟩   -- w15 = 2048
  let p15 : SLP 15 := .snoc p14  .add ⟨15, by omega⟩ ⟨15, by omega⟩   -- w16 = 4096
  let p16 : SLP 16 := .snoc p15  .add ⟨16, by omega⟩ ⟨16, by omega⟩   -- w17 = 8192
  let p17 : SLP 17 := .snoc p16  .sub ⟨17, by omega⟩ ⟨8, by omega⟩    -- w18 = 8096
  let p18 : SLP 18 := .snoc p17  .add ⟨18, by omega⟩ ⟨3, by omega⟩    -- w19 = 8100
  let p19 : SLP 19 := .snoc p18  .add ⟨1, by omega⟩ ⟨0, by omega⟩     -- w20 = X + 1
  let p20 : SLP 20 := .snoc p19  .mul ⟨1, by omega⟩ ⟨20, by omega⟩    -- w21 = q = X*(X+1) (mul 1)
  let p21 : SLP 21 := .snoc p20  .sub ⟨21, by omega⟩ ⟨5, by omega⟩    -- w22 = q - 16
  let p22 : SLP 22 := .snoc p21  .mul ⟨22, by omega⟩ ⟨22, by omega⟩   -- w23 = (q-16)^2 (mul 2)
  let p23 : SLP 23 := .snoc p22  .sub ⟨23, by omega⟩ ⟨10, by omega⟩   -- w24 = (q-16)^2 - 106
  let p24 : SLP 24 := .snoc p23  .mul ⟨24, by omega⟩ ⟨24, by omega⟩   -- w25 = w24^2 (mul 3)
  .snoc p24 .sub ⟨25, by omega⟩ ⟨19, by omega⟩                        -- w26 = w25 - 8100

theorem slpThreeMulEight_mulCount : slpThreeMulEight.mulCount = 3 := by
  decide

/-! ## 3. Exact Sharpness Witnesses (`m = 0, 1, 2, 3`) -/

/-- Exact sharpness at `m = 0`: `X` uses `0` multiplications and has `1 = 2^0` integer root `{0}`. -/
theorem tau_zero_mul_sharp : zMaxMulGe 0 1 :=
  zMaxMulGe_of_evalInt slpWitness0 {0} 1
    (by decide) (by decide) (by decide) (by decide)

/-- Exact sharpness at `m = 1`: `X * (X - 1)` uses `1` multiplication and has `2 = 2^1`
distinct integer roots `{0, 1}`. -/
theorem tau_one_mul_sharp : zMaxMulGe 1 2 :=
  zMaxMulGe_of_evalInt slpWitness2 {0, 1} 2
    (by decide) (by decide) (by decide) (by decide)

/-- Exact sharpness at `m = 2`: `q * (q - 2)` where `q = X^2 - X` uses `2` multiplications
and has `4 = 2^2` distinct integer roots `{-1, 0, 1, 2}`. -/
theorem tau_two_mul_sharp : zMaxMulGe 2 4 :=
  zMaxMulGe_of_evalInt slpWitness5 {-1, 0, 1, 2} 3
    (by decide) (by decide) (by decide) (by decide)

/-- Exact sharpness at `m = 3`: `((X * (X + 1) - 16)^2 - 106)^2 - 8100` uses `3`
multiplications and has `8 = 2^3` distinct integer roots `{-6, -5, -4, -2, 1, 3, 4, 5}`. -/
theorem tau_three_mul_sharp : zMaxMulGe 3 8 :=
  zMaxMulGe_of_evalInt slpThreeMulEight {-6, -5, -4, -2, 1, 3, 4, 5} 0
    (by decide) (by decide) (by decide) (by decide)

/-! ## 4. Summary Theorem: Exact Sharpness for `m = 0, 1, 2, 3` -/

/-- **Exact Sharpness Theorem for Bounded-Multiplication SLPs (`m = 0, 1, 2, 3`):**
For every `m ∈ {0, 1, 2, 3}`, the maximum number of distinct integer roots of a nonzero
polynomial computed by a constant-free SLP with at most `m` multiplication gates is
**exactly** `2 ^ m` (`1`, `2`, `4`, `8` respectively). -/
theorem bounded_mult_exact_sharpness :
    (∀ {τ : ℕ} (P : SLP τ), P.mulCount ≤ 0 → P.evalPoly ≠ 0 → intRootCount P.evalPoly ≤ 1) ∧
    zMaxMulGe 0 1 ∧
    (∀ {τ : ℕ} (P : SLP τ), P.mulCount ≤ 1 → P.evalPoly ≠ 0 → intRootCount P.evalPoly ≤ 2) ∧
    zMaxMulGe 1 2 ∧
    (∀ {τ : ℕ} (P : SLP τ), P.mulCount ≤ 2 → P.evalPoly ≠ 0 → intRootCount P.evalPoly ≤ 4) ∧
    zMaxMulGe 2 4 ∧
    (∀ {τ : ℕ} (P : SLP τ), P.mulCount ≤ 3 → P.evalPoly ≠ 0 → intRootCount P.evalPoly ≤ 8) ∧
    zMaxMulGe 3 8 :=
  ⟨fun P hm hne => tau_mulCount_intRootCount_le_two_pow P hm hne, tau_zero_mul_sharp,
   fun P hm hne => tau_mulCount_intRootCount_le_two_pow P hm hne, tau_one_mul_sharp,
   fun P hm hne => tau_mulCount_intRootCount_le_two_pow P hm hne, tau_two_mul_sharp,
   fun P hm hne => tau_three_mul_intRootCount_le_eight P hm hne, tau_three_mul_sharp⟩

end Research.PvsNP.Tau

end
