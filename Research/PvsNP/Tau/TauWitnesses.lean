module

public import Research.PvsNP.Tau.TauConjecture

@[expose] public section

namespace Research.PvsNP.Tau

/-!
# Machine-Verified Record Witness Ladder for the Shub–Smale $\tau$-Conjecture

This module extends the witness ladder of `Research.PvsNP.Tau.TauConjecture` with
machine-verified constant-free straight-line program (`SLP`) witnesses matching the
exact record ladder up to $\tau = 13$ (`zMaxGe 6 5`, `zMaxGe 10 7` via both the
symmetric difference-of-squares and pronic families, `zMaxGe 11 8`, and `zMaxGe 13 9`),
together with the unconditional degree-4 / root-count-4 bound for SLPs with at most
two multiplication gates.
-/

/-! ## 1. Unconditional Bound for SLPs with at Most Two Multiplications -/

/-- SLPs with at most `2` multiplication gates compute polynomials of degree at most `4`. -/
theorem tau_two_mul_natDegree_le_four {τ : ℕ} (P : SLP τ) (hm : P.mulCount ≤ 2) :
    P.evalPoly.natDegree ≤ 4 := by
  have h := slp_natDegree_le_two_pow_mulCount P ⟨τ + 1, Nat.lt_succ_self _⟩
  have hpow : 2 ^ P.mulCount ≤ 4 := by
    calc
      2 ^ P.mulCount ≤ 2 ^ 2 := Nat.pow_le_pow_right (by omega) hm
      _ = 4 := by decide
  exact h.trans hpow

/-- Nonzero polynomials computed by SLPs with at most `2` multiplication gates
have at most `4` distinct integer roots. -/
theorem tau_two_mul_intRootCount_le_four {τ : ℕ} (P : SLP τ) (hm : P.mulCount ≤ 2)
    (hne : P.evalPoly ≠ 0) :
    intRootCount P.evalPoly ≤ 4 :=
  (intRootCount_le_natDegree hne).trans (tau_two_mul_natDegree_le_four P hm)

/-! ## 2. Concrete Record Witness SLPs (`τ = 6, 10, 11, 13`) -/

/-- Length-6 witness: `X * (X^2 - (2 - X^2)^2) = -X(X^2 - 1)(X^2 - 4)`,
with `5` distinct integer roots `{-2, -1, 0, 1, 2}` (matching `z_max(6) = 5`). -/
def slpWitness6 : SLP 6 :=
  let p1 : SLP 1 := .snoc .nil .add ⟨0, by omega⟩ ⟨0, by omega⟩   -- w2 = 2
  let p2 : SLP 2 := .snoc p1 .mul ⟨1, by omega⟩ ⟨1, by omega⟩     -- w3 = X^2
  let p3 : SLP 3 := .snoc p2 .sub ⟨2, by omega⟩ ⟨3, by omega⟩     -- w4 = 2 - X^2
  let p4 : SLP 4 := .snoc p3 .mul ⟨4, by omega⟩ ⟨4, by omega⟩     -- w5 = (2 - X^2)^2
  let p5 : SLP 5 := .snoc p4 .sub ⟨3, by omega⟩ ⟨5, by omega⟩     -- w6 = X^2 - (2 - X^2)^2
  .snoc p5 .mul ⟨1, by omega⟩ ⟨6, by omega⟩                       -- w7 = X * (X^2 - (2 - X^2)^2)

/-- Length-10 symmetric difference-of-squares witness:
`-X(X^2 - 1)(X^2 - 4)(X^2 - 9)`, with `7` distinct integer roots `{-3, -2, -1, 0, 1, 2, 3}`. -/
def slpWitness10 : SLP 10 :=
  let p7 : SLP 7 := .snoc slpWitness6 .add ⟨0, by omega⟩ ⟨2, by omega⟩  -- w8 = 1 + 2 = 3
  let p8 : SLP 8 := .snoc p7 .mul ⟨8, by omega⟩ ⟨8, by omega⟩           -- w9 = 9
  let p9 : SLP 9 := .snoc p8 .sub ⟨3, by omega⟩ ⟨9, by omega⟩           -- w10 = X^2 - 9
  .snoc p9 .mul ⟨7, by omega⟩ ⟨10, by omega⟩                            -- w11 = w7 * (X^2 - 9)

/-- Shared length-8 pronic prefix: `q * (2 - q) * (6 - q)` where `q = X * (1 + X)`,
with wires `w2 = 2`, `w4 = 4`, `w7 = 6 - q`, `w9 = q * (2 - q) * (6 - q)`. -/
def slpPronic8 : SLP 8 :=
  let p1 : SLP 1 := .snoc .nil .add ⟨0, by omega⟩ ⟨0, by omega⟩   -- w2 = 2
  let p2 : SLP 2 := .snoc p1 .add ⟨0, by omega⟩ ⟨1, by omega⟩     -- w3 = 1 + X
  let p3 : SLP 3 := .snoc p2 .add ⟨2, by omega⟩ ⟨2, by omega⟩     -- w4 = 4
  let p4 : SLP 4 := .snoc p3 .mul ⟨1, by omega⟩ ⟨3, by omega⟩     -- w5 = q = X * (1 + X)
  let p5 : SLP 5 := .snoc p4 .sub ⟨2, by omega⟩ ⟨5, by omega⟩     -- w6 = 2 - q
  let p6 : SLP 6 := .snoc p5 .add ⟨4, by omega⟩ ⟨6, by omega⟩     -- w7 = 6 - q
  let p7 : SLP 7 := .snoc p6 .mul ⟨5, by omega⟩ ⟨6, by omega⟩     -- w8 = q * (2 - q)
  .snoc p7 .mul ⟨7, by omega⟩ ⟨8, by omega⟩                       -- w9 = (6 - q) * q * (2 - q)

/-- Length-10 pronic witness: `q * (2 - q) * (6 - q) * (X + 4)` where `q = X * (1 + X)`,
with `7` distinct integer roots `{-4, -3, -2, -1, 0, 1, 2}`. -/
def slpWitness10Pronic : SLP 10 :=
  let p9 : SLP 9 := .snoc slpPronic8 .add ⟨1, by omega⟩ ⟨4, by omega⟩   -- w10 = X + 4
  .snoc p9 .mul ⟨9, by omega⟩ ⟨10, by omega⟩                            -- w11 = w9 * (X + 4)

/-- Length-11 pronic witness: `q * (2 - q) * (6 - q) * (12 - q)` where `q = X * (1 + X)`,
with `8` distinct integer roots `{-4, -3, -2, -1, 0, 1, 2, 3}`. -/
def slpWitness11 : SLP 11 :=
  let p9 : SLP 9 := .snoc slpPronic8 .add ⟨2, by omega⟩ ⟨4, by omega⟩   -- w10 = 2 + 4 = 6
  let p10 : SLP 10 := .snoc p9 .add ⟨7, by omega⟩ ⟨10, by omega⟩        -- w11 = (6 - q) + 6 = 12 - q
  .snoc p10 .mul ⟨9, by omega⟩ ⟨11, by omega⟩                           -- w12 = w9 * (12 - q)

/-- Length-13 pronic witness: `q * (2 - q) * (6 - q) * (12 - q) * (X - 4)` where `q = X * (1 + X)`,
with `9` distinct integer roots `{-4, -3, -2, -1, 0, 1, 2, 3, 4}`. -/
def slpWitness13 : SLP 13 :=
  let p12 : SLP 12 := .snoc slpWitness11 .sub ⟨1, by omega⟩ ⟨4, by omega⟩ -- w13 = X - 4
  .snoc p12 .mul ⟨12, by omega⟩ ⟨13, by omega⟩                            -- w14 = w12 * (X - 4)

/-! ## 3. Machine-Verified Record Lower Bounds (`zMaxGe`) -/

theorem tau_witness_6_five : zMaxGe 6 5 :=
  zMaxGe_of_evalInt slpWitness6 {-2, -1, 0, 1, 2} 3
    (by decide) (by decide) (by decide)

theorem tau_witness_10_seven : zMaxGe 10 7 :=
  zMaxGe_of_evalInt slpWitness10 {-3, -2, -1, 0, 1, 2, 3} 4
    (by decide) (by decide) (by decide)

theorem tau_witness_10_seven_pronic : zMaxGe 10 7 :=
  zMaxGe_of_evalInt slpWitness10Pronic {-4, -3, -2, -1, 0, 1, 2} 3
    (by decide) (by decide) (by decide)

theorem tau_witness_11_eight : zMaxGe 11 8 :=
  zMaxGe_of_evalInt slpWitness11 {-4, -3, -2, -1, 0, 1, 2, 3} 4
    (by decide) (by decide) (by decide)

theorem tau_witness_13_nine : zMaxGe 13 9 :=
  zMaxGe_of_evalInt slpWitness13 {-4, -3, -2, -1, 0, 1, 2, 3, 4} 5
    (by decide) (by decide) (by decide)

end Research.PvsNP.Tau

end
