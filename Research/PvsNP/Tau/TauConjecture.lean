module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Data.Finset.Card

@[expose] public section

namespace Research.PvsNP.Tau

/-!
# Smale's 4th Problem: The Shub–Smale $\tau$-Conjecture

This module formalizes constant-free straight-line programs (`SLP`) over `ℤ[X]`,
distinct integer root counts, the statement of the Shub–Smale $\tau$-conjecture
(`ShubSmaleTauConjecture`), unconditional degree and root-count upper bounds
(including the sharp `2 ^ mulCount` bound), and a machine-verified ladder of
exact concrete witnesses (`zMaxGe`) for `τ = 0, 1, 2, 3, 5, 7, 8`.
-/

/-! ## 1. Constant-Free Straight-Line Programs over `ℤ[X]` -/

/-- Arithmetic gate operations for constant-free straight-line programs. -/
inductive SLPOp
  | add
  | sub
  | mul
  deriving DecidableEq, Repr

/-- Apply an `SLPOp` to two polynomials over `ℤ`. -/
noncomputable def SLPOp.applyPoly : SLPOp → Polynomial ℤ → Polynomial ℤ → Polynomial ℤ
  | .add, p, q => p + q
  | .sub, p, q => p - q
  | .mul, p, q => p * q

/-- Apply an `SLPOp` to two integers. -/
def SLPOp.applyInt : SLPOp → ℤ → ℤ → ℤ
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b

theorem SLPOp.applyInt_eq_eval (op : SLPOp) (p q : Polynomial ℤ) (a : ℤ) :
    op.applyInt (p.eval a) (q.eval a) = (op.applyPoly p q).eval a := by
  cases op <;> simp [SLPOp.applyInt, SLPOp.applyPoly]

/-- A constant-free straight-line program of length `τ` over `ℤ[X]`.
Wire `0` holds the constant `1`, wire `1` holds the indeterminate `X`,
and each `snoc` appends a new wire combining two existing wires. -/
inductive SLP : ℕ → Type
  | nil : SLP 0
  | snoc {τ : ℕ} (P : SLP τ) (op : SLPOp) (i j : Fin (τ + 2)) : SLP (τ + 1)
  deriving DecidableEq, Repr

/-- Polynomial computed at wire `k : Fin (τ + 2)` of `P : SLP τ`. -/
noncomputable def SLP.evalWire : {τ : ℕ} → SLP τ → Fin (τ + 2) → Polynomial ℤ
  | 0, .nil, k => if k.val = 0 then 1 else Polynomial.X
  | τ + 1, .snoc P op i j, k =>
      if h : k.val < τ + 2 then
        P.evalWire ⟨k.val, h⟩
      else
        op.applyPoly (P.evalWire i) (P.evalWire j)

/-- Output polynomial of `P : SLP τ` (the last wire, or `X` when `τ = 0`). -/
noncomputable def SLP.evalPoly {τ : ℕ} (P : SLP τ) : Polynomial ℤ :=
  P.evalWire ⟨τ + 1, Nat.lt_succ_self _⟩

/-- Direct integer evaluation of wire `k : Fin (τ + 2)` of `P : SLP τ` at `a : ℤ`. -/
def SLP.evalWireInt : {τ : ℕ} → SLP τ → ℤ → Fin (τ + 2) → ℤ
  | 0, .nil, a, k => if k.val = 0 then 1 else a
  | τ + 1, .snoc P op i j, a, k =>
      if h : k.val < τ + 2 then
        P.evalWireInt a ⟨k.val, h⟩
      else
        op.applyInt (P.evalWireInt a i) (P.evalWireInt a j)

/-- Direct integer evaluation of the output wire of `P : SLP τ` at `a : ℤ`. -/
def SLP.evalInt {τ : ℕ} (P : SLP τ) (a : ℤ) : ℤ :=
  P.evalWireInt a ⟨τ + 1, Nat.lt_succ_self _⟩

theorem SLP.evalWireInt_eq_eval :
    ∀ {τ : ℕ} (P : SLP τ) (a : ℤ) (k : Fin (τ + 2)),
      P.evalWireInt a k = (P.evalWire k).eval a
  | 0, .nil, a, k => by
      simp only [SLP.evalWireInt, SLP.evalWire]
      split_ifs <;> simp
  | τ + 1, .snoc P op i j, a, k => by
      simp only [SLP.evalWireInt, SLP.evalWire]
      split_ifs with h
      · exact P.evalWireInt_eq_eval a ⟨k.val, h⟩
      · rw [P.evalWireInt_eq_eval a i, P.evalWireInt_eq_eval a j, SLPOp.applyInt_eq_eval]

theorem SLP.evalInt_eq_eval {τ : ℕ} (P : SLP τ) (a : ℤ) :
    P.evalInt a = P.evalPoly.eval a :=
  P.evalWireInt_eq_eval a ⟨τ + 1, Nat.lt_succ_self _⟩

/-- Wire `0` of every `SLP` evaluates to the constant polynomial `1`. -/
theorem SLP.evalWire_zero :
    ∀ {τ : ℕ} (P : SLP τ), P.evalWire 0 = 1
  | 0, .nil => by simp [SLP.evalWire]
  | τ + 1, .snoc P _ _ _ => by
      have h : (0 : ℕ) < τ + 2 := Nat.zero_lt_succ _
      simpa [SLP.evalWire, h] using P.evalWire_zero

/-- Number of multiplication gates (`SLPOp.mul`) in an `SLP`. -/
def SLP.mulCount : {τ : ℕ} → SLP τ → ℕ
  | 0, .nil => 0
  | _ + 1, .snoc P op _ _ => P.mulCount + if op = .mul then 1 else 0

theorem SLP.mulCount_le : ∀ {τ : ℕ} (P : SLP τ), P.mulCount ≤ τ
  | 0, .nil => Nat.le_refl 0
  | _ + 1, .snoc P op _ _ => by
      have ih := P.mulCount_le
      cases op <;> simp [SLP.mulCount] <;> omega

/-- `ComputesPoly τ f` holds when some length-`τ` constant-free SLP computes `f`. -/
def ComputesPoly (τ : ℕ) (f : Polynomial ℤ) : Prop :=
  ∃ P : SLP τ, P.evalPoly = f

/-! ## 2. Distinct Integer Roots & Statement of Smale's 4th Problem -/

/-- The finite set of distinct integer roots of `f ∈ ℤ[X]` (empty if `f = 0`). -/
noncomputable def intRootSet (f : Polynomial ℤ) : Finset ℤ :=
  f.roots.toFinset

/-- The number of distinct integer roots of `f ∈ ℤ[X]`. -/
noncomputable def intRootCount (f : Polynomial ℤ) : ℕ :=
  (intRootSet f).card

theorem mem_intRootSet_iff {f : Polynomial ℤ} {a : ℤ} :
    a ∈ intRootSet f ↔ f ≠ 0 ∧ f.IsRoot a := by
  simp [intRootSet]

/-- **Smale's 4th Problem (Shub–Smale $\tau$-Conjecture):**
There exist constants `c, k : ℕ` such that every nonzero polynomial `f ∈ ℤ[X]`
computed by a constant-free straight-line program of length `τ` has at most
`c * (τ ^ k + 1)` distinct integer roots. -/
def ShubSmaleTauConjecture : Prop :=
  ∃ c k : ℕ, ∀ (τ : ℕ) (P : SLP τ), P.evalPoly ≠ 0 →
    intRootCount P.evalPoly ≤ c * (τ ^ k + 1)

/-- `zMaxGe τ r` asserts that there exists a length-`τ` constant-free SLP
computing a nonzero polynomial in `ℤ[X]` with at least `r` distinct integer roots. -/
def zMaxGe (τ r : ℕ) : Prop :=
  ∃ P : SLP τ, P.evalPoly ≠ 0 ∧ r ≤ intRootCount P.evalPoly

/-- Padding a length-`τ` SLP by multiplying its output by wire `0` (constant `1`)
preserves the output polynomial. -/
theorem zMaxGe_succ {τ r : ℕ} (h : zMaxGe τ r) : zMaxGe (τ + 1) r := by
  rcases h with ⟨P, hne, hcard⟩
  let P' : SLP (τ + 1) := P.snoc .mul ⟨τ + 1, Nat.lt_succ_self _⟩ 0
  have heq : P'.evalPoly = P.evalPoly := by
    simp [P', SLP.evalPoly, SLP.evalWire, SLPOp.applyPoly, P.evalWire_zero]
  refine ⟨P', ?_, ?_⟩
  · rwa [heq]
  · rwa [heq]

/-! ## 3. Unconditional Foundational Theorems -/

/-- A nonzero polynomial `f ∈ ℤ[X]` has at most `f.natDegree` distinct integer roots. -/
theorem intRootCount_le_natDegree {f : Polynomial ℤ} (_hf : f ≠ 0) :
    intRootCount f ≤ f.natDegree := by
  calc
    intRootCount f = f.roots.toFinset.card := rfl
    _ ≤ f.roots.card := Multiset.toFinset_card_le f.roots
    _ ≤ f.natDegree := Polynomial.card_roots' f

/-- Subadditivity of distinct integer root counts under multiplication. -/
theorem intRootCount_mul_le {f g : Polynomial ℤ} (hfg : f * g ≠ 0) :
    intRootCount (f * g) ≤ intRootCount f + intRootCount g := by
  have hf : f ≠ 0 := left_ne_zero_of_mul hfg
  have hg : g ≠ 0 := right_ne_zero_of_mul hfg
  have hsub : intRootSet (f * g) ⊆ intRootSet f ∪ intRootSet g := by
    intro a ha
    rw [mem_intRootSet_iff] at ha
    rw [Finset.mem_union, mem_intRootSet_iff, mem_intRootSet_iff]
    have hmul : f.eval a * g.eval a = 0 := by
      simpa [Polynomial.IsRoot, Polynomial.eval_mul] using ha.2
    rcases mul_eq_zero.mp hmul with hfa | hga
    · exact Or.inl ⟨hf, hfa⟩
    · exact Or.inr ⟨hg, hga⟩
  calc
    intRootCount (f * g) ≤ (intRootSet f ∪ intRootSet g).card := Finset.card_le_card hsub
    _ ≤ intRootCount f + intRootCount g := Finset.card_union_le _ _

/-- Sharp degree bound in terms of the number of multiplication gates:
every wire of `P : SLP τ` has degree at most `2 ^ P.mulCount`. -/
theorem slp_natDegree_le_two_pow_mulCount :
    ∀ {τ : ℕ} (P : SLP τ) (i : Fin (τ + 2)),
      (P.evalWire i).natDegree ≤ 2 ^ P.mulCount
  | 0, .nil, i => by
      simp only [SLP.evalWire, SLP.mulCount, pow_zero]
      split_ifs
      · simp
      · simp
  | τ + 1, .snoc P op a b, i => by
      simp only [SLP.evalWire]
      split_ifs with h
      · have ih := slp_natDegree_le_two_pow_mulCount P ⟨i.val, h⟩
        have hle : P.mulCount ≤ (P.snoc op a b).mulCount := by
          simp [SLP.mulCount]
        exact ih.trans (Nat.pow_le_pow_right (by omega) hle)
      · have iha := slp_natDegree_le_two_pow_mulCount P a
        have ihb := slp_natDegree_le_two_pow_mulCount P b
        cases op with
        | add =>
            simp only [SLPOp.applyPoly, SLP.mulCount, reduceCtorEq, ↓reduceIte, add_zero]
            exact (Polynomial.natDegree_add_le _ _).trans (max_le iha ihb)
        | sub =>
            simp only [SLPOp.applyPoly, SLP.mulCount, reduceCtorEq, ↓reduceIte, add_zero]
            exact (Polynomial.natDegree_sub_le _ _).trans (max_le iha ihb)
        | mul =>
            simp only [SLPOp.applyPoly, SLP.mulCount, ↓reduceIte]
            calc
              (P.evalWire a * P.evalWire b).natDegree
                  ≤ (P.evalWire a).natDegree + (P.evalWire b).natDegree :=
                Polynomial.natDegree_mul_le
              _ ≤ 2 ^ P.mulCount + 2 ^ P.mulCount := Nat.add_le_add iha ihb
              _ = 2 ^ (P.mulCount + 1) := by ring

/-- Classical exponential degree upper bound: every wire of `P : SLP τ`
has degree at most `2 ^ τ`. -/
theorem slp_natDegree_le_two_pow (τ : ℕ) (P : SLP τ) (i : Fin (τ + 2)) :
    (P.evalWire i).natDegree ≤ 2 ^ τ :=
  (slp_natDegree_le_two_pow_mulCount P i).trans
    (Nat.pow_le_pow_right (by omega) P.mulCount_le)

/-- Classical exponential root-count upper bound: a nonzero polynomial computed
by a length-`τ` SLP has at most `2 ^ τ` distinct integer roots. -/
theorem slp_intRootCount_le_two_pow {τ : ℕ} (P : SLP τ) (hne : P.evalPoly ≠ 0) :
    intRootCount P.evalPoly ≤ 2 ^ τ :=
  (intRootCount_le_natDegree hne).trans (slp_natDegree_le_two_pow τ P _)

/-- Multiplication-free SLPs compute polynomials of degree at most `1`. -/
theorem slp_mulFree_natDegree_le_one {τ : ℕ} (P : SLP τ) (hm : P.mulCount = 0) :
    P.evalPoly.natDegree ≤ 1 := by
  have h := slp_natDegree_le_two_pow_mulCount P ⟨τ + 1, Nat.lt_succ_self _⟩
  simpa [SLP.evalPoly, hm] using h

/-- Nonzero polynomials computed by multiplication-free SLPs have at most `1` integer root. -/
theorem slp_mulFree_intRootCount_le_one {τ : ℕ} (P : SLP τ) (hm : P.mulCount = 0)
    (hne : P.evalPoly ≠ 0) :
    intRootCount P.evalPoly ≤ 1 :=
  (intRootCount_le_natDegree hne).trans (slp_mulFree_natDegree_le_one P hm)

/-- SLPs with at most `1` multiplication gate compute polynomials of degree at most `2`. -/
theorem slp_one_mul_natDegree_le_two {τ : ℕ} (P : SLP τ) (hm : P.mulCount ≤ 1) :
    P.evalPoly.natDegree ≤ 2 := by
  have h := slp_natDegree_le_two_pow_mulCount P ⟨τ + 1, Nat.lt_succ_self _⟩
  have hpow : 2 ^ P.mulCount ≤ 2 := by
    calc
      2 ^ P.mulCount ≤ 2 ^ 1 := Nat.pow_le_pow_right (by omega) hm
      _ = 2 := by norm_num
  exact h.trans hpow

/-- Nonzero polynomials computed by SLPs with at most `1` multiplication gate
have at most `2` distinct integer roots. -/
theorem slp_one_mul_intRootCount_le_two {τ : ℕ} (P : SLP τ) (hm : P.mulCount ≤ 1)
    (hne : P.evalPoly ≠ 0) :
    intRootCount P.evalPoly ≤ 2 :=
  (intRootCount_le_natDegree hne).trans (slp_one_mul_natDegree_le_two P hm)

/-! ## 4. Machine-Verified Exact Witness Ladder (`zMaxGe`) -/

/-- Helper lemma to certify `zMaxGe τ r` directly from computable integer evaluations
of a concrete `P : SLP τ`: a single nonzero point `b` proves `P.evalPoly ≠ 0`,
`P.evalInt a = 0` for all `a ∈ S` proves `S ⊆ intRootSet P.evalPoly`, and `r ≤ S.card`
certifies the lower bound. -/
theorem zMaxGe_of_evalInt {τ r : ℕ} (P : SLP τ) (S : Finset ℤ) (b : ℤ)
    (hcard : r ≤ S.card) (hb : P.evalInt b ≠ 0) (hS : ∀ a ∈ S, P.evalInt a = 0) :
    zMaxGe τ r := by
  have hne : P.evalPoly ≠ 0 := by
    intro h0
    apply hb
    rw [P.evalInt_eq_eval, h0, Polynomial.eval_zero]
  refine ⟨P, hne, ?_⟩
  have hsub : S ⊆ intRootSet P.evalPoly := by
    intro a ha
    rw [mem_intRootSet_iff]
    refine ⟨hne, ?_⟩
    rw [Polynomial.IsRoot, ← P.evalInt_eq_eval]
    exact hS a ha
  exact hcard.trans (Finset.card_le_card hsub)

/-- Length-0 witness: `X`, with `1` root `{0}`. -/
def slpWitness0 : SLP 0 := .nil

/-- Length-1 witness: `X - 1`, with `1` root `{1}`. -/
def slpWitness1 : SLP 1 :=
  .snoc .nil .sub ⟨1, by omega⟩ ⟨0, by omega⟩

/-- Length-2 witness: `X * (X - 1)`, with `2` roots `{0, 1}`. -/
def slpWitness2 : SLP 2 :=
  .snoc slpWitness1 .mul ⟨1, by omega⟩ ⟨2, by omega⟩

/-- Length-3 witness: `X * (X^2 - 1)`, with `3` roots `{-1, 0, 1}`. -/
def slpWitness3 : SLP 3 :=
  let p1 : SLP 1 := .snoc .nil .mul ⟨1, by omega⟩ ⟨1, by omega⟩   -- w2 = X^2
  let p2 : SLP 2 := .snoc p1 .sub ⟨2, by omega⟩ ⟨0, by omega⟩     -- w3 = X^2 - 1
  .snoc p2 .mul ⟨3, by omega⟩ ⟨1, by omega⟩                       -- w4 = (X^2 - 1) * X

/-- Length-5 witness: `q * (q - 2)` where `q = X^2 - X`, with `4` roots `{-1, 0, 1, 2}`. -/
def slpWitness5 : SLP 5 :=
  let p1 : SLP 1 := .snoc .nil .mul ⟨1, by omega⟩ ⟨1, by omega⟩   -- w2 = X^2
  let p2 : SLP 2 := .snoc p1 .sub ⟨2, by omega⟩ ⟨1, by omega⟩     -- w3 = q = X^2 - X
  let p3 : SLP 3 := .snoc p2 .add ⟨0, by omega⟩ ⟨0, by omega⟩     -- w4 = 2
  let p4 : SLP 4 := .snoc p3 .sub ⟨3, by omega⟩ ⟨4, by omega⟩     -- w5 = q - 2
  .snoc p4 .mul ⟨3, by omega⟩ ⟨5, by omega⟩                       -- w6 = q * (q - 2)

/-- Length-7 witness: `q * (q - 2) * (X + 2)`, with `5` roots `{-2, -1, 0, 1, 2}`. -/
def slpWitness7 : SLP 7 :=
  let p6 : SLP 6 := .snoc slpWitness5 .add ⟨1, by omega⟩ ⟨4, by omega⟩  -- w7 = X + 2
  .snoc p6 .mul ⟨6, by omega⟩ ⟨7, by omega⟩                             -- w8 = q*(q-2)*(X+2)

/-- Length-8 witness: `q * (q - 2) * (q - 6)` where `q = X^2 - X`,
with `6` roots `{-2, -1, 0, 1, 2, 3}`. -/
def slpWitness8 : SLP 8 :=
  let p6 : SLP 6 := .snoc slpWitness5 .add ⟨4, by omega⟩ ⟨4, by omega⟩  -- w7 = 4
  let p7 : SLP 7 := .snoc p6 .sub ⟨5, by omega⟩ ⟨7, by omega⟩           -- w8 = (q - 2) - 4 = q - 6
  .snoc p7 .mul ⟨6, by omega⟩ ⟨8, by omega⟩                             -- w9 = q*(q-2)*(q-6)

theorem tau_witness_0 : zMaxGe 0 1 :=
  zMaxGe_of_evalInt slpWitness0 {0} 1 (by decide) (by decide) (by decide)

theorem tau_witness_1 : zMaxGe 1 1 :=
  zMaxGe_of_evalInt slpWitness1 {1} 0 (by decide) (by decide) (by decide)

theorem tau_witness_2 : zMaxGe 2 2 :=
  zMaxGe_of_evalInt slpWitness2 {0, 1} 2 (by decide) (by decide) (by decide)

theorem tau_witness_3 : zMaxGe 3 3 :=
  zMaxGe_of_evalInt slpWitness3 {-1, 0, 1} 2 (by decide) (by decide) (by decide)

theorem tau_witness_5 : zMaxGe 5 4 :=
  zMaxGe_of_evalInt slpWitness5 {-1, 0, 1, 2} 3 (by decide) (by decide) (by decide)

theorem tau_witness_7 : zMaxGe 7 5 :=
  zMaxGe_of_evalInt slpWitness7 {-2, -1, 0, 1, 2} 3 (by decide) (by decide) (by decide)

theorem tau_witness_8 : zMaxGe 8 6 :=
  zMaxGe_of_evalInt slpWitness8 {-2, -1, 0, 1, 2, 3} 4 (by decide) (by decide) (by decide)

end Research.PvsNP.Tau

end
