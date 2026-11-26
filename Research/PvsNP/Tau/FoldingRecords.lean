module

public import Research.PvsNP.Tau.BoundedMult

@[expose] public section

namespace Research.PvsNP.Tau

/-!
# Iterated Folding Records (`τ = 16, 17, 18`) and Exact `m = 4` Multiplication Sharpness

This module formalizes two frontier advances on Smale's 4th Problem (the Shub–Smale
$\tau$-Conjecture):

1. **New High-$\tau$ Record Witnesses (`τ = 16, 17, 18`):**
   - `tau_record_16_twelve : zMaxGe 16 12`:
     `((q - 36)^2 - 36)((q - 36)^2 - 36^2)(q - 2)(q - 6)` where `q = X(1 + X)`,
     with `12` distinct integer roots `{-9, -7, -6, -3, -2, -1, 0, 1, 2, 5, 6, 8}`.
   - `tau_record_17_thirteen : zMaxGe 17 13`:
     Square-extraction extension `slpRecord13 * (X + 196) * (q - (X + 196))`,
     with `13` distinct integer roots `{-196, -14, -6, -5, -4, -2, -1, 0, 1, 3, 4, 5, 14}`.
   - `tau_record_18_fourteen : zMaxGe 18 14`:
     Pronic self-shift extension `slpRecord16 * ((q - 36) - 36^2)` using
     `a + a^2 = a(a + 1)`, with `14` distinct integer roots
     `{-37, -9, -7, -6, -3, -2, -1, 0, 1, 2, 5, 6, 8, 36}`.

2. **Exact Sharpness for `m = 4` Multiplications (`max_{mulCount ≤ 4} z(P) = 2^4 = 16`):**
   - `appendConst`, `appendSubConst`, `appendSubConstSq`: binary-doubling addition chains
     that synthesize arbitrary natural constants using **zero** multiplication gates.
   - `slpFourMulSixteen`: a constant-free SLP with **exact `mulCount = 4`** computing
     `(((X(X + 1) - 16851)^2 - 220362381)^2 - 2083869931842000)^2 - 1832844567153600^2`.
   - `tau_four_mul_sharp : zMaxMulGe 4 16` with `16` distinct integer roots
     `{-184, -180, -177, -172, -66, -51, -39, -6, 5, 38, 50, 65, 171, 176, 179, 183}`.
   - `tau_four_mul_intRootCount_le_sixteen` and `bounded_mult_exact_sharpness_four`,
     establishing that `max_{mulCount ≤ m} z(P) = 2^m` is exact and sharp for all
     `m ∈ {0, 1, 2, 3, 4}`.
-/

/-! ## 1. New High-$\tau$ Record Witness SLPs (`τ = 16, 17, 18`) -/

/-- Length-16 shifted pronic-square record witness with DAG constant reuse:
`((q - 36)^2 - 36) * ((q - 36)^2 - 36^2) * (q - 2) * (q - 6)` where `q = X * (1 + X)`,
with `12` distinct integer roots `{-9, -7, -6, -3, -2, -1, 0, 1, 2, 5, 6, 8}`. -/
def slpRecord16 : SLP 16 :=
  let p1  : SLP 1  := .snoc .nil .add ⟨0, by omega⟩ ⟨1, by omega⟩     -- w2  = 1 + X
  let p2  : SLP 2  := .snoc p1   .mul ⟨1, by omega⟩ ⟨2, by omega⟩     -- w3  = q = X * (1 + X)
  let p3  : SLP 3  := .snoc p2   .add ⟨0, by omega⟩ ⟨0, by omega⟩     -- w4  = 2
  let p4  : SLP 4  := .snoc p3   .add ⟨0, by omega⟩ ⟨4, by omega⟩     -- w5  = 3
  let p5  : SLP 5  := .snoc p4   .mul ⟨4, by omega⟩ ⟨5, by omega⟩     -- w6  = 6
  let p6  : SLP 6  := .snoc p5   .mul ⟨6, by omega⟩ ⟨6, by omega⟩     -- w7  = 36
  let p7  : SLP 7  := .snoc p6   .sub ⟨3, by omega⟩ ⟨7, by omega⟩     -- w8  = q - 36
  let p8  : SLP 8  := .snoc p7   .mul ⟨8, by omega⟩ ⟨8, by omega⟩     -- w9  = (q - 36)^2
  let p9  : SLP 9  := .snoc p8   .sub ⟨9, by omega⟩ ⟨7, by omega⟩     -- w10 = (q - 36)^2 - 36
  let p10 : SLP 10 := .snoc p9   .mul ⟨7, by omega⟩ ⟨7, by omega⟩     -- w11 = 36^2 = 1296
  let p11 : SLP 11 := .snoc p10  .sub ⟨9, by omega⟩ ⟨11, by omega⟩    -- w12 = (q - 36)^2 - 36^2
  let p12 : SLP 12 := .snoc p11  .mul ⟨10, by omega⟩ ⟨12, by omega⟩   -- w13 = w10 * w12
  let p13 : SLP 13 := .snoc p12  .sub ⟨3, by omega⟩ ⟨4, by omega⟩     -- w14 = q - 2
  let p14 : SLP 14 := .snoc p13  .mul ⟨13, by omega⟩ ⟨14, by omega⟩   -- w15 = w13 * (q - 2)
  let p15 : SLP 15 := .snoc p14  .sub ⟨3, by omega⟩ ⟨6, by omega⟩     -- w16 = q - 6
  .snoc p15 .mul ⟨15, by omega⟩ ⟨16, by omega⟩                        -- w17 = w15 * (q - 6)

/-- Length-17 square-extraction record witness extending `slpRecord13`:
`slpRecord13 * (X + 196) * (q - (X + 196))`, with `13` distinct integer roots
`{-196, -14, -6, -5, -4, -2, -1, 0, 1, 3, 4, 5, 14}`. -/
def slpRecord17 : SLP 17 :=
  let p14 : SLP 14 := .snoc slpRecord13 .add ⟨1, by omega⟩ ⟨10, by omega⟩  -- w15 = X + 196
  let p15 : SLP 15 := .snoc p14         .mul ⟨14, by omega⟩ ⟨15, by omega⟩ -- w16 = w14 * (X + 196)
  let p16 : SLP 16 := .snoc p15         .sub ⟨3, by omega⟩ ⟨15, by omega⟩  -- w17 = q - (X + 196) = X^2 - 196
  .snoc p16 .mul ⟨16, by omega⟩ ⟨17, by omega⟩                             -- w18 = w16 * w17

/-- Length-18 pronic self-shift record witness extending `slpRecord16`:
`slpRecord16 * ((q - 36) - 36^2)`, with `14` distinct integer roots
`{-37, -9, -7, -6, -3, -2, -1, 0, 1, 2, 5, 6, 8, 36}`. -/
def slpRecord18 : SLP 18 :=
  let p17 : SLP 17 := .snoc slpRecord16 .sub ⟨8, by omega⟩ ⟨11, by omega⟩  -- w18 = (q - 36) - 1296
  .snoc p17 .mul ⟨17, by omega⟩ ⟨18, by omega⟩                             -- w19 = w17 * w18

/-! ## 2. Machine-Verified High-$\tau$ Record Lower Bounds (`zMaxGe`) -/

theorem tau_record_16_twelve : zMaxGe 16 12 :=
  zMaxGe_of_evalInt slpRecord16 {-9, -7, -6, -3, -2, -1, 0, 1, 2, 5, 6, 8} 3
    (by decide) (by decide) (by decide)

theorem tau_record_17_thirteen : zMaxGe 17 13 :=
  zMaxGe_of_evalInt slpRecord17 {-196, -14, -6, -5, -4, -2, -1, 0, 1, 3, 4, 5, 14} 2
    (by decide) (by decide) (by decide)

theorem tau_record_18_fourteen : zMaxGe 18 14 :=
  zMaxGe_of_evalInt slpRecord18 {-37, -9, -7, -6, -3, -2, -1, 0, 1, 2, 5, 6, 8, 36} 3
    (by decide) (by decide) (by decide)

/-! ## 3. Zero-Multiplication Binary-Doubling Addition Chains -/

/-- Wire `0` of every `SLP` evaluates to `1` under `evalWireInt`. -/
theorem SLP.evalWireInt_zero :
    ∀ {τ : ℕ} (P : SLP τ) (a : ℤ), P.evalWireInt a 0 = 1
  | 0, .nil, _ => rfl
  | τ + 1, .snoc P _ _ _, a => by
      have h : (0 : ℕ) < τ + 2 := Nat.zero_lt_succ _
      simpa [SLP.evalWireInt, h] using P.evalWireInt_zero a

/-- Append a binary-doubling addition chain to `P : SLP τ` whose output wire evaluates
to the constant `(c : ℤ)` for all inputs, using **zero** multiplication gates. -/
def appendConst {τ : ℕ} (P : SLP τ) : ℕ → (d : ℕ) × SLP (τ + d)
  | 0 => ⟨1, P.snoc .sub 0 0⟩
  | n + 1 =>
      let c := n + 1
      let ⟨d, Q⟩ := appendConst P (c / 2)
      let Q2 : SLP (τ + (d + 1)) :=
        Q.snoc .add ⟨τ + d + 1, by omega⟩ ⟨τ + d + 1, by omega⟩
      if c % 2 = 0 then
        ⟨d + 1, Q2⟩
      else
        ⟨d + 2, Q2.snoc .add ⟨τ + d + 2, by omega⟩ 0⟩

private theorem appendConst_zero {τ : ℕ} (P : SLP τ) :
    appendConst P 0 = ⟨1, P.snoc .sub 0 0⟩ := by
  rw [appendConst]

private theorem appendConst_succ_even {τ : ℕ} (P : SLP τ) (n : ℕ) (heven : (n + 1) % 2 = 0) :
    appendConst P (n + 1) =
      ⟨(appendConst P ((n + 1) / 2)).1 + 1,
        (appendConst P ((n + 1) / 2)).2.snoc .add
          ⟨τ + (appendConst P ((n + 1) / 2)).1 + 1, by omega⟩
          ⟨τ + (appendConst P ((n + 1) / 2)).1 + 1, by omega⟩⟩ := by
  rw [appendConst]
  simp only [heven, ↓reduceIte]

private theorem appendConst_succ_odd {τ : ℕ} (P : SLP τ) (n : ℕ) (hodd : (n + 1) % 2 ≠ 0) :
    appendConst P (n + 1) =
      ⟨(appendConst P ((n + 1) / 2)).1 + 2,
        ((appendConst P ((n + 1) / 2)).2.snoc .add
          ⟨τ + (appendConst P ((n + 1) / 2)).1 + 1, by omega⟩
          ⟨τ + (appendConst P ((n + 1) / 2)).1 + 1, by omega⟩).snoc .add
          ⟨τ + (appendConst P ((n + 1) / 2)).1 + 2, by omega⟩ 0⟩ := by
  rw [appendConst]
  simp only [hodd, ↓reduceIte]

private theorem eq_sigma_mulCount {τ : ℕ} {r₁ r₂ : (d : ℕ) × SLP (τ + d)} (h : r₁ = r₂) :
    r₁.2.mulCount = r₂.2.mulCount := by
  subst h; rfl

private theorem eq_sigma_evalWireInt {τ : ℕ} {r₁ r₂ : (d : ℕ) × SLP (τ + d)} (h : r₁ = r₂)
    (a : ℤ) (k : ℕ) (hk : k < τ + 2) :
    r₁.2.evalWireInt a ⟨k, by omega⟩ = r₂.2.evalWireInt a ⟨k, by omega⟩ := by
  subst h; rfl

private theorem eq_sigma_evalInt {τ : ℕ} {r₁ r₂ : (d : ℕ) × SLP (τ + d)} (h : r₁ = r₂) (a : ℤ) :
    r₁.2.evalInt a = r₂.2.evalInt a := by
  subst h; rfl

theorem appendConst_mulCount {τ : ℕ} (P : SLP τ) (c : ℕ) :
    (appendConst P c).2.mulCount = P.mulCount := by
  induction c using Nat.strongRecOn with
  | ind c ih =>
    match c with
    | 0 =>
      rw [eq_sigma_mulCount (appendConst_zero P)]
      simp [SLP.mulCount]
    | n + 1 =>
      have hm : (n + 1) / 2 < n + 1 := Nat.div_lt_self (Nat.succ_pos n) (by decide)
      have hih := ih ((n + 1) / 2) hm
      by_cases heven : (n + 1) % 2 = 0
      · rw [eq_sigma_mulCount (appendConst_succ_even P n heven)]
        simpa [SLP.mulCount] using hih
      · rw [eq_sigma_mulCount (appendConst_succ_odd P n heven)]
        simpa [SLP.mulCount] using hih

theorem appendConst_evalWireInt_lt {τ : ℕ} (P : SLP τ) (c : ℕ) (a : ℤ)
    (k : ℕ) (hk : k < τ + 2) :
    (appendConst P c).2.evalWireInt a ⟨k, by omega⟩ = P.evalWireInt a ⟨k, hk⟩ := by
  induction c using Nat.strongRecOn with
  | ind c ih =>
    match c with
    | 0 =>
      rw [eq_sigma_evalWireInt (appendConst_zero P) a k hk]
      simp [SLP.evalWireInt, hk]
    | n + 1 =>
      have hm : (n + 1) / 2 < n + 1 := Nat.div_lt_self (Nat.succ_pos n) (by decide)
      have hih := ih ((n + 1) / 2) hm
      have hk1 : k < τ + (appendConst P ((n + 1) / 2)).1 + 2 := by omega
      have hk2 : k < τ + (appendConst P ((n + 1) / 2)).1 + 1 + 2 := by omega
      by_cases heven : (n + 1) % 2 = 0
      · rw [eq_sigma_evalWireInt (appendConst_succ_even P n heven) a k hk]
        simpa [SLP.evalWireInt, hk1] using hih
      · rw [eq_sigma_evalWireInt (appendConst_succ_odd P n heven) a k hk]
        simpa [SLP.evalWireInt, hk1, hk2] using hih

theorem appendConst_evalInt {τ : ℕ} (P : SLP τ) (c : ℕ) (a : ℤ) :
    (appendConst P c).2.evalInt a = (c : ℤ) := by
  induction c using Nat.strongRecOn with
  | ind c ih =>
    match c with
    | 0 =>
      rw [eq_sigma_evalInt (appendConst_zero P) a]
      simp [SLP.evalInt, SLP.evalWireInt, SLPOp.applyInt, P.evalWireInt_zero a]
    | n + 1 =>
      have hm : (n + 1) / 2 < n + 1 := Nat.div_lt_self (Nat.succ_pos n) (by decide)
      have hih := ih ((n + 1) / 2) hm
      by_cases heven : (n + 1) % 2 = 0
      · rw [eq_sigma_evalInt (appendConst_succ_even P n heven) a]
        have heval :
            ((appendConst P ((n + 1) / 2)).2.snoc .add
              ⟨τ + (appendConst P ((n + 1) / 2)).1 + 1, by omega⟩
              ⟨τ + (appendConst P ((n + 1) / 2)).1 + 1, by omega⟩).evalInt a =
            (appendConst P ((n + 1) / 2)).2.evalInt a +
              (appendConst P ((n + 1) / 2)).2.evalInt a := by
          simp [SLP.evalInt, SLP.evalWireInt, SLPOp.applyInt]
        rw [heval, hih]
        omega
      · rw [eq_sigma_evalInt (appendConst_succ_odd P n heven) a]
        have hzero :=
          ((appendConst P ((n + 1) / 2)).2.snoc .add
            ⟨τ + (appendConst P ((n + 1) / 2)).1 + 1, by omega⟩
            ⟨τ + (appendConst P ((n + 1) / 2)).1 + 1, by omega⟩).evalWireInt_zero a
        have heval :
            (((appendConst P ((n + 1) / 2)).2.snoc .add
                ⟨τ + (appendConst P ((n + 1) / 2)).1 + 1, by omega⟩
                ⟨τ + (appendConst P ((n + 1) / 2)).1 + 1, by omega⟩).snoc .add
              ⟨τ + (appendConst P ((n + 1) / 2)).1 + 2, by omega⟩
              0).evalInt a =
            (appendConst P ((n + 1) / 2)).2.evalInt a +
              (appendConst P ((n + 1) / 2)).2.evalInt a + 1 := by
          simp [SLP.evalInt, SLP.evalWireInt, SLPOp.applyInt, hzero]
        rw [heval, hih]
        omega

/-- Append gates computing `P.evalPoly - (c : ℤ)` using **zero** extra multiplications. -/
def appendSubConst {τ : ℕ} (P : SLP τ) (c : ℕ) : (d : ℕ) × SLP (τ + d) :=
  let ⟨d, Q⟩ := appendConst P c
  ⟨d + 1, Q.snoc .sub ⟨τ + 1, by omega⟩ ⟨τ + d + 1, by omega⟩⟩

theorem appendSubConst_mulCount {τ : ℕ} (P : SLP τ) (c : ℕ) :
    (appendSubConst P c).2.mulCount = P.mulCount := by
  simp [appendSubConst, SLP.mulCount, appendConst_mulCount]

theorem appendSubConst_evalInt {τ : ℕ} (P : SLP τ) (c : ℕ) (a : ℤ) :
    (appendSubConst P c).2.evalInt a = P.evalInt a - (c : ℤ) := by
  have hlt := appendConst_evalWireInt_lt P c a (τ + 1) (Nat.lt_succ_self _)
  have hc := appendConst_evalInt P c a
  simpa [appendSubConst, SLP.evalInt, SLP.evalWireInt, SLPOp.applyInt, hlt] using
    congrArg (P.evalInt a - ·) hc

/-- Append gates computing `(P.evalPoly - (c : ℤ)) ^ 2` using **exactly 1** extra
multiplication gate. -/
def appendSubConstSq {τ : ℕ} (P : SLP τ) (c : ℕ) : (d : ℕ) × SLP (τ + d) :=
  let ⟨d, Q⟩ := appendSubConst P c
  ⟨d + 1, Q.snoc .mul ⟨τ + d + 1, by omega⟩ ⟨τ + d + 1, by omega⟩⟩

theorem appendSubConstSq_mulCount {τ : ℕ} (P : SLP τ) (c : ℕ) :
    (appendSubConstSq P c).2.mulCount = P.mulCount + 1 := by
  simp [appendSubConstSq, SLP.mulCount, appendSubConst_mulCount]

theorem appendSubConstSq_evalInt {τ : ℕ} (P : SLP τ) (c : ℕ) (a : ℤ) :
    (appendSubConstSq P c).2.evalInt a = (P.evalInt a - (c : ℤ)) ^ 2 := by
  have hsub := appendSubConst_evalInt P c a
  have hstep :
      (appendSubConstSq P c).2.evalInt a =
        (appendSubConst P c).2.evalInt a * (appendSubConst P c).2.evalInt a := by
    simp [appendSubConstSq, SLP.evalInt, SLP.evalWireInt, SLPOp.applyInt]
  rw [hstep, hsub, sq]

/-! ## 4. Four-Multiplication 16-Root Sharpness Witness (`m = 4`, `2^4 = 16`) -/

/-- Length-2 SLP computing the pronic quadratic `X * (X + 1)` using `1` multiplication. -/
def slpPronic : SLP 2 :=
  let p1 : SLP 1 := .snoc .nil .add ⟨1, by omega⟩ ⟨0, by omega⟩   -- w2 = X + 1
  .snoc p1 .mul ⟨1, by omega⟩ ⟨2, by omega⟩                       -- w3 = X * (X + 1)

theorem slpPronic_mulCount : slpPronic.mulCount = 1 := by
  decide

theorem slpPronic_evalInt (a : ℤ) : slpPronic.evalInt a = a * (a + 1) := by
  simp [slpPronic, SLP.evalInt, SLP.evalWireInt, SLPOp.applyInt]

/-- Packaged 4-multiplication iterated-folding SLP computing
`(((X(X + 1) - 16851)^2 - 220362381)^2 - 2083869931842000)^2 - 1832844567153600^2`. -/
def slpFourMulSixteenPair : (τ : ℕ) × SLP τ :=
  let s1 := appendSubConstSq slpPronic 16851
  let s2 := appendSubConstSq s1.2 220362381
  let s3 := appendSubConstSq s2.2 2083869931842000
  let s4 := appendSubConst s3.2 (1832844567153600 ^ 2)
  ⟨_, s4.2⟩

/-- Constant-free SLP with **exact `mulCount = 4`** computing the degree-16
4-level folded polynomial with `16` distinct integer roots
`{-184, -180, -177, -172, -66, -51, -39, -6, 5, 38, 50, 65, 171, 176, 179, 183}`. -/
def slpFourMulSixteen : SLP slpFourMulSixteenPair.1 :=
  slpFourMulSixteenPair.2

theorem slpFourMulSixteen_mulCount : slpFourMulSixteen.mulCount = 4 := by
  simp [slpFourMulSixteen, slpFourMulSixteenPair, appendSubConst_mulCount,
    appendSubConstSq_mulCount, slpPronic_mulCount]

theorem slpFourMulSixteen_evalInt (a : ℤ) :
    slpFourMulSixteen.evalInt a =
      (((a * (a + 1) - 16851) ^ 2 - 220362381) ^ 2 - 2083869931842000) ^ 2 -
        (1832844567153600 : ℤ) ^ 2 := by
  simp only [slpFourMulSixteen, slpFourMulSixteenPair, appendSubConst_evalInt,
    appendSubConstSq_evalInt, slpPronic_evalInt]
  norm_num

/-- Nonzero polynomials computed by SLPs with at most `4` multiplication gates
have at most `16` distinct integer roots. -/
theorem tau_four_mul_intRootCount_le_sixteen {τ : ℕ} (P : SLP τ) (hm : P.mulCount ≤ 4)
    (hne : P.evalPoly ≠ 0) :
    intRootCount P.evalPoly ≤ 16 :=
  tau_mulCount_intRootCount_le_two_pow P hm hne

/-- Exact sharpness at `m = 4`: `slpFourMulSixteen` uses `4` multiplications and has
`16 = 2^4` distinct integer roots
`{-184, -180, -177, -172, -66, -51, -39, -6, 5, 38, 50, 65, 171, 176, 179, 183}`. -/
theorem tau_four_mul_sharp : zMaxMulGe 4 16 := by
  refine zMaxMulGe_of_evalInt slpFourMulSixteen
    {-184, -180, -177, -172, -66, -51, -39, -6, 5, 38, 50, 65, 171, 176, 179, 183} 0
    (by rw [slpFourMulSixteen_mulCount])
    (by decide)
    (by rw [slpFourMulSixteen_evalInt]; decide)
    ?_
  intro a ha
  rw [slpFourMulSixteen_evalInt]
  revert a ha
  decide

/-! ## 5. Summary Theorem: Exact Sharpness for `m = 0, 1, 2, 3, 4` -/

/-- **Exact Sharpness Theorem for Bounded-Multiplication SLPs (`m = 0, 1, 2, 3, 4`):**
For every `m ∈ {0, 1, 2, 3, 4}`, the maximum number of distinct integer roots of a nonzero
polynomial computed by a constant-free SLP with at most `m` multiplication gates is
**exactly** `2 ^ m` (`1`, `2`, `4`, `8`, `16` respectively). -/
theorem bounded_mult_exact_sharpness_four :
    (∀ {τ : ℕ} (P : SLP τ), P.mulCount ≤ 0 → P.evalPoly ≠ 0 → intRootCount P.evalPoly ≤ 1) ∧
    zMaxMulGe 0 1 ∧
    (∀ {τ : ℕ} (P : SLP τ), P.mulCount ≤ 1 → P.evalPoly ≠ 0 → intRootCount P.evalPoly ≤ 2) ∧
    zMaxMulGe 1 2 ∧
    (∀ {τ : ℕ} (P : SLP τ), P.mulCount ≤ 2 → P.evalPoly ≠ 0 → intRootCount P.evalPoly ≤ 4) ∧
    zMaxMulGe 2 4 ∧
    (∀ {τ : ℕ} (P : SLP τ), P.mulCount ≤ 3 → P.evalPoly ≠ 0 → intRootCount P.evalPoly ≤ 8) ∧
    zMaxMulGe 3 8 ∧
    (∀ {τ : ℕ} (P : SLP τ), P.mulCount ≤ 4 → P.evalPoly ≠ 0 → intRootCount P.evalPoly ≤ 16) ∧
    zMaxMulGe 4 16 :=
  ⟨bounded_mult_exact_sharpness.1, bounded_mult_exact_sharpness.2.1,
   bounded_mult_exact_sharpness.2.2.1, bounded_mult_exact_sharpness.2.2.2.1,
   bounded_mult_exact_sharpness.2.2.2.2.1, bounded_mult_exact_sharpness.2.2.2.2.2.1,
   bounded_mult_exact_sharpness.2.2.2.2.2.2.1, bounded_mult_exact_sharpness.2.2.2.2.2.2.2,
   fun P hm hne => tau_four_mul_intRootCount_le_sixteen P hm hne, tau_four_mul_sharp⟩

end Research.PvsNP.Tau

end
