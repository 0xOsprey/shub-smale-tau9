module

public import Research.PvsNP.Tau.Canonical
public import Research.PvsNP.Tau.ModularRootBound
public import Mathlib.Algebra.Polynomial.Taylor

@[expose] public section

namespace Research.PvsNP.Tau

/-!
# Soundness of Per-Leaf Root Certificates and Evaluation-Based Deduplication

This module formalizes the evaluation-based soundness of the leaf certificates and
hash/CRT checks used by the exhaustive $\tau$-conjecture verifier:

1. Generic commutative-ring SLP evaluation (`evalIn`, `outputIn`) commuting with ring
   homomorphisms.
2. Degree-bound propagation (`degUb`) and `intRootCount f ≤ degUb`.
3. Atomic product-factor bitmask bound (`prodMask`) including `intRootCount (A + A) = intRootCount A`,
   constant elimination, and union bounds over atomic factors.
4. Dual-number arithmetic (`Dual R`) evaluating `(f(a), f'(a)) mod p` in one pass,
   and the SLP-level simple-root modular certificate.
5. Exact Taylor-residue certificate (`taylor_root_eq_of_factor`, `intRootCount_le_of_taylor_zmod`)
   handling repeated small integer roots.
6. Soundness of hash-based inequality (`≠`) conclusions and CRT exact-equality-by-evaluation.
-/

/-! ## 1. Generic Ring Evaluation and Homomorphism Commutation -/

/-- Apply an `SLPOp` in any ring `R`. -/
def SLPOp.applyRing {R : Type*} [Ring R] : SLPOp → R → R → R
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b

theorem SLPOp.map_applyRing {R S : Type*} [Ring R] [Ring S]
    (φ : R →+* S) (op : SLPOp) (a b : R) :
    φ (op.applyRing a b) = op.applyRing (φ a) (φ b) := by
  cases op <;> simp [SLPOp.applyRing]

/-- Evaluate wire `k : Fin (τ + 2)` of `P : SLP τ` in an arbitrary ring `R`
with indeterminate `X` instantiated to `x : R`. -/
def SLP.evalWireIn {R : Type*} [Ring R] (x : R) : {τ : ℕ} → SLP τ → Fin (τ + 2) → R
  | 0, .nil, k => if k.val = 0 then 1 else x
  | τ + 1, .snoc P op i j, k =>
      if h : k.val < τ + 2 then
        P.evalWireIn x ⟨k.val, h⟩
      else
        op.applyRing (P.evalWireIn x i) (P.evalWireIn x j)

/-- Evaluate the output wire of `P : SLP τ` in any ring `R` at `x : R`. -/
def SLP.evalIn {R : Type*} [Ring R] (x : R) {τ : ℕ} (P : SLP τ) : R :=
  P.evalWireIn x ⟨τ + 1, Nat.lt_succ_self _⟩

theorem SLP.evalWireIn_X :
    ∀ {τ : ℕ} (P : SLP τ) (k : Fin (τ + 2)),
      P.evalWireIn (Polynomial.X : Polynomial ℤ) k = P.evalWire k
  | 0, .nil, k => by
      simp only [SLP.evalWireIn, SLP.evalWire]
  | τ + 1, .snoc P op i j, k => by
      simp only [SLP.evalWireIn, SLP.evalWire]
      split_ifs with h
      · exact P.evalWireIn_X ⟨k.val, h⟩
      · rw [P.evalWireIn_X i, P.evalWireIn_X j]
        cases op <;> rfl

theorem SLP.evalIn_X {τ : ℕ} (P : SLP τ) :
    P.evalIn (Polynomial.X : Polynomial ℤ) = P.evalPoly :=
  P.evalWireIn_X ⟨τ + 1, Nat.lt_succ_self _⟩

theorem SLP.map_evalWireIn {R S : Type*} [Ring R] [Ring S]
    (φ : R →+* S) (x : R) :
    ∀ {τ : ℕ} (P : SLP τ) (k : Fin (τ + 2)),
      φ (P.evalWireIn x k) = P.evalWireIn (φ x) k
  | 0, .nil, k => by
      simp only [SLP.evalWireIn]
      split_ifs <;> simp
  | τ + 1, .snoc P op i j, k => by
      simp only [SLP.evalWireIn]
      split_ifs with h
      · exact P.map_evalWireIn φ x ⟨k.val, h⟩
      · rw [SLPOp.map_applyRing, P.map_evalWireIn φ x i, P.map_evalWireIn φ x j]

theorem SLP.map_evalIn {R S : Type*} [Ring R] [Ring S]
    (φ : R →+* S) (x : R) {τ : ℕ} (P : SLP τ) :
    φ (P.evalIn x) = P.evalIn (φ x) :=
  P.map_evalWireIn φ x ⟨τ + 1, Nat.lt_succ_self _⟩

theorem SLP.evalIn_eq_eval₂ {R : Type*} [CommRing R] (x : R) {τ : ℕ} (P : SLP τ) :
    P.evalIn x = (P.evalPoly.map (Int.castRingHom R)).eval x := by
  let φ : Polynomial ℤ →+* R := Polynomial.eval₂RingHom (Int.castRingHom R) x
  have hφ : φ Polynomial.X = x := by simp [φ]
  have h := P.map_evalIn φ Polynomial.X
  rw [P.evalIn_X, hφ] at h
  simpa [φ, Polynomial.eval_map] using h.symm

theorem SLP.evalIn_int_eq_eval {τ : ℕ} (P : SLP τ) (a : ℤ) :
    P.evalIn a = P.evalPoly.eval a := by
  simpa using P.evalIn_eq_eval₂ a

/-- Accumulator evaluator for `List GateSpec` over any ring `R`. -/
def wireValsInAux {R : Type*} [Ring R] : List R → List GateSpec → List R
  | acc, [] => acc
  | acc, g :: rest =>
      wireValsInAux (acc ++ [g.op.applyRing (acc.getD g.i 0) (acc.getD g.j 0)]) rest

/-- Wire values of a gate list `gs` evaluated in a ring `R` at `x : R`. -/
def wireValsIn {R : Type*} [Ring R] (x : R) (gs : List GateSpec) : List R :=
  wireValsInAux [1, x] gs

/-- Output value of a gate list `gs` evaluated in a ring `R` at `x : R`. -/
def outputIn {R : Type*} [Ring R] (x : R) (gs : List GateSpec) : R :=
  (wireValsIn x gs).getD (gs.length + 1) 0

private lemma list_getD_map {R S : Type*} [Ring R] [Ring S] (φ : R →+* S)
    (l : List R) (i : ℕ) : (l.map φ).getD i 0 = φ (l.getD i 0) := by
  by_cases hi : i < l.length
  · simp [List.getD, hi]
  · simp [List.getD, hi]

theorem wireValsInAux_length {R : Type*} [Ring R] (acc : List R) (gs : List GateSpec) :
    (wireValsInAux acc gs).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [wireValsInAux]
  | cons g rest ih =>
      simp only [wireValsInAux]
      rw [ih]
      simp
      omega

theorem wireValsIn_length {R : Type*} [Ring R] (x : R) (gs : List GateSpec) :
    (wireValsIn x gs).length = gs.length + 2 := by
  rw [wireValsIn, wireValsInAux_length]
  simp
  omega

theorem wireValsIn_X (gs : List GateSpec) :
    wireValsIn (Polynomial.X : Polynomial ℤ) gs = wireVals gs := by
  have haux : ∀ (acc : List (Polynomial ℤ)) (gs : List GateSpec),
      wireValsInAux acc gs = wireValsAux acc gs := by
    intro acc gs
    induction gs generalizing acc with
    | nil => rfl
    | cons g rest ih =>
        simp only [wireValsInAux, wireValsAux]
        have hop : g.op.applyRing (acc.getD g.i 0) (acc.getD g.j 0) =
            g.op.applyPoly (acc.getD g.i 0) (acc.getD g.j 0) := by
          cases g.op <;> rfl
        rw [hop, ih]
  exact haux [1, Polynomial.X] gs

theorem outputIn_X (gs : List GateSpec) :
    outputIn (Polynomial.X : Polynomial ℤ) gs = output gs := by
  simp [outputIn, output, wireValsIn_X]

theorem wireValsIn_map {R S : Type*} [Ring R] [Ring S] (φ : R →+* S)
    (x : R) (gs : List GateSpec) :
    (wireValsIn x gs).map φ = wireValsIn (φ x) gs := by
  have haux : ∀ (acc : List R) (gs : List GateSpec),
      (wireValsInAux acc gs).map φ = wireValsInAux (acc.map φ) gs := by
    intro acc gs
    induction gs generalizing acc with
    | nil => rfl
    | cons g rest ih =>
        simp only [wireValsInAux, ih, List.map_append, List.map_singleton,
          SLPOp.map_applyRing, list_getD_map]
  simpa [wireValsIn] using haux [1, x] gs

theorem outputIn_map {R S : Type*} [Ring R] [Ring S] (φ : R →+* S)
    (x : R) (gs : List GateSpec) :
    φ (outputIn x gs) = outputIn (φ x) gs := by
  unfold outputIn
  rw [← wireValsIn_map φ x gs, list_getD_map]

theorem outputIn_eq_eval₂ {R : Type*} [CommRing R] (x : R) (gs : List GateSpec) :
    outputIn x gs = ((output gs).map (Int.castRingHom R)).eval x := by
  let φ : Polynomial ℤ →+* R := Polynomial.eval₂RingHom (Int.castRingHom R) x
  have hφ : φ Polynomial.X = x := by simp [φ]
  have h := outputIn_map φ Polynomial.X gs
  rw [outputIn_X, hφ] at h
  simpa [φ, Polynomial.eval_map] using h.symm

/-! ## 2. Degree-Bound Propagation -/

/-- Wire degree upper bound recurrence for `SLP`:
`1 ↦ 0`, `X ↦ 1`, `a ± b ↦ max`, `a * b ↦ sum`. -/
def SLP.wireDegUb : {τ : ℕ} → SLP τ → Fin (τ + 2) → ℕ
  | 0, .nil, k => if k.val = 0 then 0 else 1
  | τ + 1, .snoc P op i j, k =>
      if h : k.val < τ + 2 then
        P.wireDegUb ⟨k.val, h⟩
      else
        match op with
        | .add | .sub => max (P.wireDegUb i) (P.wireDegUb j)
        | .mul => P.wireDegUb i + P.wireDegUb j

/-- Output degree upper bound of `P : SLP τ`. -/
def SLP.degUb {τ : ℕ} (P : SLP τ) : ℕ :=
  P.wireDegUb ⟨τ + 1, Nat.lt_succ_self _⟩

private lemma wireDegUb_snoc {τ : ℕ} (P : SLP τ) (op : SLPOp) (i j : Fin (τ + 2))
    (k : Fin (τ + 1 + 2)) :
    (P.snoc op i j).wireDegUb k =
      if h : k.val < τ + 2 then
        P.wireDegUb ⟨k.val, h⟩
      else
        match op with
        | .add | .sub => max (P.wireDegUb i) (P.wireDegUb j)
        | .mul => P.wireDegUb i + P.wireDegUb j := rfl

theorem slp_natDegree_le_wireDegUb :
    ∀ {τ : ℕ} (P : SLP τ) (k : Fin (τ + 2)),
      (P.evalWire k).natDegree ≤ P.wireDegUb k
  | 0, .nil, k => by
      simp only [SLP.evalWire, SLP.wireDegUb]
      split_ifs <;> simp
  | τ + 1, .snoc P op i j, k => by
      rw [wireDegUb_snoc]
      by_cases h : k.val < τ + 2
      · simp only [SLP.evalWire, h, ↓reduceDIte]
        exact slp_natDegree_le_wireDegUb P ⟨k.val, h⟩
      · simp only [SLP.evalWire, h, ↓reduceDIte]
        have ihi := slp_natDegree_le_wireDegUb P i
        have ihj := slp_natDegree_le_wireDegUb P j
        cases op with
        | add => exact (Polynomial.natDegree_add_le _ _).trans (max_le_max ihi ihj)
        | sub => exact (Polynomial.natDegree_sub_le _ _).trans (max_le_max ihi ihj)
        | mul => exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add ihi ihj)

theorem slp_natDegree_le_degUb {τ : ℕ} (P : SLP τ) :
    P.evalPoly.natDegree ≤ P.degUb :=
  slp_natDegree_le_wireDegUb P ⟨τ + 1, Nat.lt_succ_self _⟩

/-- Degree upper bound root certificate for `SLP`. -/
theorem slp_intRootCount_le_degUb {τ : ℕ} (P : SLP τ) (hne : P.evalPoly ≠ 0) :
    intRootCount P.evalPoly ≤ P.degUb :=
  (intRootCount_le_natDegree hne).trans (slp_natDegree_le_degUb P)

/-- Degree upper bound accumulator for `List GateSpec`. -/
def wireDegUbsAux : List ℕ → List GateSpec → List ℕ
  | acc, [] => acc
  | acc, g :: rest =>
      let d :=
        match g.op with
        | .add | .sub => max (acc.getD g.i 0) (acc.getD g.j 0)
        | .mul => acc.getD g.i 0 + acc.getD g.j 0
      wireDegUbsAux (acc ++ [d]) rest

/-- Wire degree upper bounds for `gs : List GateSpec`. -/
def wireDegUbs (gs : List GateSpec) : List ℕ :=
  wireDegUbsAux [0, 1] gs

/-- Output degree upper bound for `gs : List GateSpec`. -/
def degUb (gs : List GateSpec) : ℕ :=
  (wireDegUbs gs).getD (gs.length + 1) 0

theorem wireVals_natDegree_le_wireDegUbs (gs : List GateSpec) :
    ∀ w : ℕ, ((wireVals gs).getD w 0).natDegree ≤ (wireDegUbs gs).getD w 0 := by
  have haux : ∀ (accP : List (Polynomial ℤ)) (accD : List ℕ) (gs : List GateSpec),
      accP.length = accD.length →
      (∀ w, (accP.getD w 0).natDegree ≤ accD.getD w 0) →
      ∀ w, ((wireValsAux accP gs).getD w 0).natDegree ≤ (wireDegUbsAux accD gs).getD w 0 := by
    intro accP accD gs
    induction gs generalizing accP accD with
    | nil =>
        intro _ h w
        exact h w
    | cons g rest ih =>
        intro hlen h w
        simp only [wireValsAux, wireDegUbsAux]
        refine ih _ _ (by simp [hlen]) ?_ w
        intro u
        by_cases hu : u < accP.length
        · have huD : u < accD.length := by omega
          simp only [List.getD, List.getElem?_append_left hu, List.getElem?_append_left huD]
          exact h u
        · have huD : accD.length ≤ u := by omega
          have huP : accP.length ≤ u := by omega
          by_cases heq : u = accP.length
          · subst heq
            simp only [List.getD, List.getElem?_append_right (le_refl _),
              List.getElem?_append_right hlen.le, hlen, Nat.sub_self,
              List.getElem?_cons_zero, Option.getD_some]
            have hi := h g.i
            have hj := h g.j
            cases g.op with
            | add => exact (Polynomial.natDegree_add_le _ _).trans (max_le_max hi hj)
            | sub => exact (Polynomial.natDegree_sub_le _ _).trans (max_le_max hi hj)
            | mul => exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add hi hj)
          · have h1 : (accP ++ [g.op.applyPoly (accP.getD g.i 0) (accP.getD g.j 0)]).length ≤ u := by
              simp; omega
            rw [List.getD, List.getElem?_eq_none h1]
            simp
  refine haux [1, Polynomial.X] [0, 1] gs rfl ?_
  intro w
  rcases w with _ | _ | w <;> simp [List.getD]

theorem output_natDegree_le_degUb (gs : List GateSpec) :
    (output gs).natDegree ≤ degUb gs :=
  wireVals_natDegree_le_wireDegUbs gs (gs.length + 1)

theorem output_intRootCount_le_degUb (gs : List GateSpec) (hne : output gs ≠ 0) :
    intRootCount (output gs) ≤ degUb gs :=
  (intRootCount_le_natDegree hne).trans (output_natDegree_le_degUb gs)

/-! ## 3. Atomic Product-Mask Bound -/

/-- Doubling a polynomial preserves its integer root set: `intRootSet (A + A) = intRootSet A`. -/
theorem intRootSet_add_self (A : Polynomial ℤ) :
    intRootSet (A + A) = intRootSet A := by
  ext r
  simp only [mem_intRootSet_iff, Polynomial.IsRoot, Polynomial.eval_add]
  have h0 : A + A = 0 ↔ A = 0 := by
    rw [← two_mul]
    exact mul_eq_zero.trans (by simp)
  constructor
  · rintro ⟨hne, hr⟩
    exact ⟨fun h => hne (h0.mpr h), by omega⟩
  · rintro ⟨hne, hr⟩
    exact ⟨fun h => hne (h0.mp h), by omega⟩

/-- `intRootCount (A + A) = intRootCount A`. -/
theorem intRootCount_add_self (A : Polynomial ℤ) :
    intRootCount (A + A) = intRootCount A := by
  simp [intRootCount, intRootSet_add_self]

/-- Nonzero constant polynomials in `ℤ[X]` have `0` integer roots. -/
theorem intRootCount_C (c : ℤ) (hc : c ≠ 0) :
    intRootCount (Polynomial.C c) = 0 :=
  Nat.eq_zero_of_le_zero ((intRootCount_le_natDegree (Polynomial.C_ne_zero.mpr hc)).trans (by simp))

/-- Generalized union bound: if every integer root of `f` is a root of at least one nonzero
atomic factor `w a` (`a ∈ M`) with `intRootCount (w a) ≤ ub a`, then
`intRootCount f ≤ ∑ a ∈ M, ub a`. -/
theorem intRootCount_le_sum_of_rootSet_subset_biUnion
    {f : Polynomial ℤ} {M : Finset ℕ} {w : ℕ → Polynomial ℤ} {ub : ℕ → ℕ}
    (hsub : intRootSet f ⊆ M.biUnion (fun a => intRootSet (w a)))
    (hub : ∀ a ∈ M, intRootCount (w a) ≤ ub a) :
    intRootCount f ≤ ∑ a ∈ M, ub a := by
  calc
    intRootCount f = (intRootSet f).card := rfl
    _ ≤ (M.biUnion (fun a => intRootSet (w a))).card := Finset.card_le_card hsub
    _ ≤ ∑ a ∈ M, (intRootSet (w a)).card := Finset.card_biUnion_le
    _ = ∑ a ∈ M, intRootCount (w a) := rfl
    _ ≤ ∑ a ∈ M, ub a := Finset.sum_le_sum hub

/-- Atomic product-factor bitmask (`Finset ℕ`) matching `prod_mask` in `tau_z9_unconditional.c`. -/
def SLP.wireProdMask : {τ : ℕ} → SLP τ → Fin (τ + 2) → Finset ℕ
  | 0, .nil, k => if k.val = 0 then ∅ else {1}
  | τ + 1, .snoc P op i j, k =>
      if h : k.val < τ + 2 then
        P.wireProdMask ⟨k.val, h⟩
      else
        if (P.snoc op i j).degUb = 0 then
          ∅
        else
          match op with
          | .mul => P.wireProdMask i ∪ P.wireProdMask j
          | .add => if i = j then P.wireProdMask i else {τ + 2}
          | .sub => {τ + 2}

/-- Output product-factor mask of `P : SLP τ`. -/
def SLP.prodMask {τ : ℕ} (P : SLP τ) : Finset ℕ :=
  P.wireProdMask ⟨τ + 1, Nat.lt_succ_self _⟩

private lemma wireProdMask_snoc {τ : ℕ} (P : SLP τ) (op : SLPOp) (i j : Fin (τ + 2))
    (k : Fin (τ + 1 + 2)) :
    (P.snoc op i j).wireProdMask k =
      if h : k.val < τ + 2 then P.wireProdMask ⟨k.val, h⟩
      else if (P.snoc op i j).degUb = 0 then ∅
      else match op with
        | .mul => P.wireProdMask i ∪ P.wireProdMask j
        | .add => if i = j then P.wireProdMask i else {τ + 2}
        | .sub => {τ + 2} := rfl

theorem slp_wireProdMask_bound {τ : ℕ} (P : SLP τ) :
    ∀ (k : Fin (τ + 2)),
      (∀ a ∈ P.wireProdMask k, a < τ + 2) ∧
      (P.evalWire k ≠ 0 →
        intRootSet (P.evalWire k) ⊆
          (P.wireProdMask k).biUnion (fun a =>
            if ha : a < τ + 2 then intRootSet (P.evalWire ⟨a, ha⟩) else ∅)) := by
  induction P with
  | nil =>
      intro k
      simp only [SLP.wireProdMask, SLP.evalWire]
      rcases k with ⟨kv, hkv⟩
      rcases kv with _ | _ | kv
      · simp [intRootSet]
      · refine ⟨by simp, fun _ => ?_⟩
        intro r hr
        rw [Finset.mem_biUnion]
        exact ⟨1, Finset.mem_singleton_self 1, by simpa⟩
      · omega
  | @snoc τ P op i j ih =>
      intro k
      have lift_mem : ∀ (a : ℕ) (ha : a < τ + 2) (r : ℤ),
          r ∈ intRootSet (P.evalWire ⟨a, ha⟩) →
          r ∈ (if ha' : a < τ + 1 + 2 then intRootSet ((P.snoc op i j).evalWire ⟨a, ha'⟩) else ∅) := by
        intro a ha r hr
        rw [dite_eq_left (ha.trans (Nat.lt_succ_self _))]
        simpa only [SLP.evalWire, ha, ↓reduceDIte] using hr
      rw [wireProdMask_snoc]
      by_cases h : k.val < τ + 2
      · simp only [SLP.evalWire, h, ↓reduceDIte]
        rcases ih ⟨k.val, h⟩ with ⟨ha_lt, hsub⟩
        refine ⟨fun a ha => (ha_lt a ha).trans (Nat.lt_succ_self _), fun hne => ?_⟩
        refine (hsub hne).trans ?_
        intro r hr
        rcases Finset.mem_biUnion.mp hr with ⟨a, ha, hr_a⟩
        have ha_lt' : a < τ + 2 := ha_lt a ha
        rw [dite_eq_left ha_lt'] at hr_a
        rw [Finset.mem_biUnion]
        exact ⟨a, ha, lift_mem a ha_lt' r hr_a⟩
      · simp only [SLP.evalWire, h, ↓reduceDIte]
        by_cases hdeg0 : (P.snoc op i j).degUb = 0
        · simp only [hdeg0, ↓reduceIte]
          refine ⟨by simp, fun hne => ?_⟩
          have hdeg_poly : ((P.snoc op i j).evalPoly).natDegree = 0 := by
            have hle := slp_natDegree_le_degUb (P.snoc op i j)
            omega
          have hpoly_eq : op.applyPoly (P.evalWire i) (P.evalWire j) = (P.snoc op i j).evalPoly := by
            simp only [SLP.evalPoly, SLP.evalWire, Nat.lt_irrefl, ↓reduceDIte]
          have hcard0 : (intRootSet (op.applyPoly (P.evalWire i) (P.evalWire j))).card = 0 := by
            rw [hpoly_eq]
            exact Nat.eq_zero_of_le_zero ((intRootCount_le_natDegree (by rwa [← hpoly_eq])).trans hdeg_poly.le)
          rw [Finset.card_eq_zero.mp hcard0]
          simp
        · simp only [hdeg0, ↓reduceIte]
          rcases ih i with ⟨hi_lt, hi_sub⟩
          rcases ih j with ⟨hj_lt, hj_sub⟩
          cases op
          · -- add
            by_cases hij : i = j
            · subst hij
              simp only [↓reduceIte]
              refine ⟨fun a ha => (hi_lt a ha).trans (Nat.lt_succ_self _), fun hne => ?_⟩
              have hne_i : P.evalWire i ≠ 0 := by
                intro h0
                apply hne
                simp [SLPOp.applyPoly, h0]
              have hrw : SLPOp.add.applyPoly (P.evalWire i) (P.evalWire i) =
                  P.evalWire i + P.evalWire i := rfl
              rw [hrw, intRootSet_add_self]
              refine (hi_sub hne_i).trans ?_
              intro r hr
              rcases Finset.mem_biUnion.mp hr with ⟨a, ha, hr_a⟩
              have ha_lt' := hi_lt a ha
              rw [dite_eq_left ha_lt'] at hr_a
              rw [Finset.mem_biUnion]
              exact ⟨a, ha, lift_mem a ha_lt' r hr_a⟩
            · simp only [hij, ↓reduceIte]
              refine ⟨by simp, fun _ r hr => ?_⟩
              rw [Finset.mem_biUnion]
              refine ⟨τ + 2, Finset.mem_singleton_self _, ?_⟩
              rw [dite_eq_left (Nat.lt_succ_self _)]
              simpa only [SLP.evalWire, Nat.lt_irrefl, ↓reduceDIte] using hr
          · -- sub
            refine ⟨by simp, fun _ r hr => ?_⟩
            rw [Finset.mem_biUnion]
            refine ⟨τ + 2, Finset.mem_singleton_self _, ?_⟩
            rw [dite_eq_left (Nat.lt_succ_self _)]
            simpa only [SLP.evalWire, Nat.lt_irrefl, ↓reduceDIte] using hr
          · -- mul
            refine ⟨fun a ha => ?_, fun hne => ?_⟩
            · rcases Finset.mem_union.mp ha with ha | ha
              · exact (hi_lt a ha).trans (Nat.lt_succ_self _)
              · exact (hj_lt a ha).trans (Nat.lt_succ_self _)
            · have hmul : P.evalWire i * P.evalWire j ≠ 0 := hne
              have hi_ne : P.evalWire i ≠ 0 := left_ne_zero_of_mul hmul
              have hj_ne : P.evalWire j ≠ 0 := right_ne_zero_of_mul hmul
              have hsub_mul : intRootSet (P.evalWire i * P.evalWire j) ⊆
                  intRootSet (P.evalWire i) ∪ intRootSet (P.evalWire j) := by
                intro r hr
                rw [mem_intRootSet_iff] at hr
                rw [Finset.mem_union, mem_intRootSet_iff, mem_intRootSet_iff]
                have hm : (P.evalWire i).eval r * (P.evalWire j).eval r = 0 := by
                  simpa [Polynomial.IsRoot, Polynomial.eval_mul] using hr.2
                rcases mul_eq_zero.mp hm with h1 | h2
                · exact Or.inl ⟨hi_ne, h1⟩
                · exact Or.inr ⟨hj_ne, h2⟩
              refine hsub_mul.trans ?_
              intro r hr
              rcases Finset.mem_union.mp hr with h1 | h2
              · rcases Finset.mem_biUnion.mp (hi_sub hi_ne h1) with ⟨a, ha, hr_a⟩
                have ha_lt' := hi_lt a ha
                rw [dite_eq_left ha_lt'] at hr_a
                rw [Finset.mem_biUnion]
                exact ⟨a, Finset.mem_union_left _ ha, lift_mem a ha_lt' r hr_a⟩
              · rcases Finset.mem_biUnion.mp (hj_sub hj_ne h2) with ⟨a, ha, hr_a⟩
                have ha_lt' := hj_lt a ha
                rw [dite_eq_left ha_lt'] at hr_a
                rw [Finset.mem_biUnion]
                exact ⟨a, Finset.mem_union_right _ ha, lift_mem a ha_lt' r hr_a⟩

/-- **SLP Atomic Product-Factor Union Bound:**
If `ub : Fin (τ + 2) → ℕ` bounds `intRootCount` of every nonzero wire of `P : SLP τ`,
then `intRootCount P.evalPoly ≤ ∑ a ∈ P.prodMask, if ha : a < τ + 2 then ub ⟨a, ha⟩ else 0`. -/
theorem slp_intRootCount_le_prodMask_sum {τ : ℕ} (P : SLP τ) (ub : Fin (τ + 2) → ℕ)
    (hub : ∀ k : Fin (τ + 2), P.evalWire k ≠ 0 → intRootCount (P.evalWire k) ≤ ub k)
    (hne : P.evalPoly ≠ 0) :
    intRootCount P.evalPoly ≤
      ∑ a ∈ P.prodMask, if ha : a < τ + 2 then ub ⟨a, ha⟩ else 0 := by
  rcases slp_wireProdMask_bound P ⟨τ + 1, Nat.lt_succ_self _⟩ with ⟨_, hsub⟩
  let w : ℕ → Polynomial ℤ := fun a => if ha : a < τ + 2 then P.evalWire ⟨a, ha⟩ else 0
  have hsub' : intRootSet P.evalPoly ⊆ P.prodMask.biUnion (fun a => intRootSet (w a)) := by
    refine (hsub hne).trans ?_
    intro r hr
    rcases Finset.mem_biUnion.mp hr with ⟨a, ha, hra⟩
    rw [Finset.mem_biUnion]
    refine ⟨a, ha, ?_⟩
    by_cases hlt : a < τ + 2
    · rw [dite_eq_left hlt] at hra
      simpa only [w, hlt, ↓reduceDIte] using hra
    · simp [hlt] at hra
  refine intRootCount_le_sum_of_rootSet_subset_biUnion (w := w) hsub' ?_
  intro a _
  by_cases ha : a < τ + 2
  · simp only [w, ha, ↓reduceDIte]
    by_cases hwa : P.evalWire ⟨a, ha⟩ = 0
    · simp [intRootCount, intRootSet, hwa]
    · exact hub ⟨a, ha⟩ hwa
  · simp [w, ha, intRootCount, intRootSet]

/-! ## 4. Dual-Number Evaluation & SLP Simple-Root Modular Certificate -/

/-- Dual numbers `R[ε]/(ε^2)` represented as pairs `(val, deriv)`. -/
@[ext]
structure Dual (R : Type*) where
  val : R
  deriv : R
  deriving DecidableEq, Repr

namespace Dual

section CommRing

variable {R : Type*} [CommRing R]

instance : Zero (Dual R) := ⟨⟨0, 0⟩⟩
instance : One (Dual R) := ⟨⟨1, 0⟩⟩
instance : Add (Dual R) := ⟨fun x y => ⟨x.val + y.val, x.deriv + y.deriv⟩⟩
instance : Sub (Dual R) := ⟨fun x y => ⟨x.val - y.val, x.deriv - y.deriv⟩⟩
instance : Neg (Dual R) := ⟨fun x => ⟨-x.val, -x.deriv⟩⟩
instance : Mul (Dual R) := ⟨fun x y => ⟨x.val * y.val, x.deriv * y.val + x.val * y.deriv⟩⟩

@[simp] lemma zero_val : (0 : Dual R).val = 0 := rfl
@[simp] lemma zero_deriv : (0 : Dual R).deriv = 0 := rfl
@[simp] lemma one_val : (1 : Dual R).val = 1 := rfl
@[simp] lemma one_deriv : (1 : Dual R).deriv = 0 := rfl
@[simp] lemma add_val (x y : Dual R) : (x + y).val = x.val + y.val := rfl
@[simp] lemma add_deriv (x y : Dual R) : (x + y).deriv = x.deriv + y.deriv := rfl
@[simp] lemma sub_val (x y : Dual R) : (x - y).val = x.val - y.val := rfl
@[simp] lemma sub_deriv (x y : Dual R) : (x - y).deriv = x.deriv - y.deriv := rfl
@[simp] lemma neg_val (x : Dual R) : (-x).val = -x.val := rfl
@[simp] lemma neg_deriv (x : Dual R) : (-x).deriv = -x.deriv := rfl
@[simp] lemma mul_val (x y : Dual R) : (x * y).val = x.val * y.val := rfl
@[simp] lemma mul_deriv (x y : Dual R) : (x * y).deriv = x.deriv * y.val + x.val * y.deriv := rfl

instance : CommRing (Dual R) where
  add := (· + ·)
  add_assoc a b c := by ext <;> dsimp <;> ring
  zero := 0
  zero_add a := by ext <;> dsimp <;> ring
  add_zero a := by ext <;> dsimp <;> ring
  nsmul := nsmulRec
  neg := (-·)
  sub := (· - ·)
  sub_eq_add_neg a b := by ext <;> dsimp <;> ring
  zsmul := zsmulRec
  neg_add_cancel a := by ext <;> dsimp <;> ring
  add_comm a b := by ext <;> dsimp <;> ring
  mul := (· * ·)
  left_distrib a b c := by ext <;> dsimp <;> ring
  right_distrib a b c := by ext <;> dsimp <;> ring
  zero_mul a := by ext <;> dsimp <;> ring
  mul_zero a := by ext <;> dsimp <;> ring
  mul_assoc a b c := by ext <;> dsimp <;> ring
  one := 1
  one_mul a := by ext <;> dsimp <;> ring
  mul_one a := by ext <;> dsimp <;> ring
  mul_comm a b := by ext <;> dsimp <;> ring

end CommRing

end Dual

/-- Evaluation into `Dual R` at `a : R` (`f ↦ (f(a), f'(a))`) is a ring homomorphism. -/
noncomputable def evalDualHom {R : Type*} [CommRing R] (a : R) : Polynomial R →+* Dual R where
  toFun f := ⟨f.eval a, f.derivative.eval a⟩
  map_one' := by ext <;> simp
  map_mul' f g := by ext <;> simp [Polynomial.derivative_mul]
  map_zero' := by ext <;> simp
  map_add' f g := by ext <;> simp

/-- **Dual-Number Evaluation Theorem for `SLP`:**
Evaluating `P : SLP τ` in `Dual (ZMod p)` at `⟨a, 1⟩` yields `(f_p(a), f_p'(a))`
where `f_p = P.evalPoly.map (Int.castRingHom (ZMod p))`. -/
theorem slp_evalIn_dual_zmod (p : ℕ) {τ : ℕ} (P : SLP τ) (a : ZMod p) :
    P.evalIn (⟨a, 1⟩ : Dual (ZMod p)) =
      ⟨(P.evalPoly.map (Int.castRingHom (ZMod p))).eval a,
       (P.evalPoly.map (Int.castRingHom (ZMod p))).derivative.eval a⟩ := by
  let φ : Polynomial ℤ →+* Dual (ZMod p) :=
    (evalDualHom a).comp (Polynomial.mapRingHom (Int.castRingHom (ZMod p)))
  have hX : φ Polynomial.X = ⟨a, 1⟩ := by
    ext <;> simp [φ, evalDualHom]
  have h := P.map_evalIn φ Polynomial.X
  rw [P.evalIn_X, hX] at h
  simpa [φ, evalDualHom] using h.symm

/-- Dual-number evaluation theorem for `List GateSpec`. -/
theorem outputIn_dual_zmod (p : ℕ) (gs : List GateSpec) (a : ZMod p) :
    outputIn (⟨a, 1⟩ : Dual (ZMod p)) gs =
      ⟨((output gs).map (Int.castRingHom (ZMod p))).eval a,
       ((output gs).map (Int.castRingHom (ZMod p))).derivative.eval a⟩ := by
  let φ : Polynomial ℤ →+* Dual (ZMod p) :=
    (evalDualHom a).comp (Polynomial.mapRingHom (Int.castRingHom (ZMod p)))
  have hX : φ Polynomial.X = ⟨a, 1⟩ := by
    ext <;> simp [φ, evalDualHom]
  have h := outputIn_map φ Polynomial.X gs
  rw [outputIn_X, hX] at h
  simpa [φ, evalDualHom] using h.symm

/-- **SLP-Level Simple-Root Modular Certificate:**
If `p` is prime, `K < p`, and dual-number evaluation of `P : SLP τ` over `ZMod p`
shows at most `K` zeros and no double zeros (`val = 0 → deriv ≠ 0`), then
`intRootCount P.evalPoly ≤ K` unconditionally over all of `ℤ`. -/
theorem slp_intRootCount_le_of_dual_eval_zmod (p : ℕ) [Fact p.Prime] {τ : ℕ} (P : SLP τ) (K : ℕ)
    (hKp : K < p)
    (hsimple : ∀ a : ZMod p,
      (P.evalIn (⟨a, 1⟩ : Dual (ZMod p))).val = 0 →
      (P.evalIn (⟨a, 1⟩ : Dual (ZMod p))).deriv ≠ 0)
    (hbound : (Finset.univ.filter (fun a : ZMod p =>
      (P.evalIn (⟨a, 1⟩ : Dual (ZMod p))).val = 0)).card ≤ K) :
    intRootCount P.evalPoly ≤ K := by
  have heval : ∀ a : ZMod p,
      (P.evalPoly.map (Int.castRingHom (ZMod p))).eval a =
        (P.evalIn (⟨a, 1⟩ : Dual (ZMod p))).val := by
    intro a
    rw [slp_evalIn_dual_zmod]
  have hderiv_eq : ∀ a : ZMod p,
      (P.evalPoly.map (Int.castRingHom (ZMod p))).derivative.eval a =
        (P.evalIn (⟨a, 1⟩ : Dual (ZMod p))).deriv := by
    intro a
    rw [slp_evalIn_dual_zmod]
  let Z := Finset.univ.filter (fun a : ZMod p =>
    (P.evalPoly.map (Int.castRingHom (ZMod p))).eval a = 0)
  have hZ_card : Z.card ≤ K := by
    simpa [Z, heval] using hbound
  have hne_pt : ∃ a : ZMod p, (P.evalPoly.map (Int.castRingHom (ZMod p))).eval a ≠ 0 := by
    by_contra hnone
    push Not at hnone
    have huniv : Finset.univ ⊆ Z := fun a _ => Finset.mem_filter.mpr ⟨Finset.mem_univ a, hnone a⟩
    have hcard : p ≤ Z.card := by
      calc
        p = Fintype.card (ZMod p) := (ZMod.card p).symm
        _ = (Finset.univ : Finset (ZMod p)).card := rfl
        _ ≤ Z.card := Finset.card_le_card huniv
    omega
  refine intRootCount_le_of_eval_zmod p P.evalPoly K hne_pt ?_ hZ_card
  intro a ha
  rw [hderiv_eq]
  apply hsimple a
  rwa [← heval]

/-! ## 5. Exact Taylor-Residue Certificate -/

/-- **Single-Point Taylor Factor Lemma:**
If `f = (X - C b)^m * g` in `ℤ[X]` and `g(b) ≢ 0 (mod p)` for prime `p`, then every
integer root `s` of `f` satisfying `s ≡ b (mod p)` must equal `b`. -/
theorem taylor_root_eq_of_factor (p : ℕ) [Fact p.Prime] (f g : Polynomial ℤ) (b : ℤ) (m : ℕ)
    (hfac : f = (Polynomial.X - Polynomial.C b) ^ m * g)
    (hgb : (g.map (Int.castRingHom (ZMod p))).eval (b : ZMod p) ≠ 0) :
    ∀ s : ℤ, f.IsRoot s → (s : ZMod p) = (b : ZMod p) → s = b := by
  intro s hs hmod
  have h0 : (s - b) ^ m * g.eval s = 0 := by
    simpa [Polynomial.IsRoot, hfac, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] using hs
  rcases mul_eq_zero.mp h0 with hpow | hgs
  · rcases eq_or_ne (s - b) 0 with hsb | hsb
    · exact sub_eq_zero.mp hsb
    · exact absurd hpow (pow_ne_zero m hsb)
  · exfalso
    apply hgb
    rw [← hmod, Polynomial.eval_map, Polynomial.eval₂_at_intCast]
    simp [hgs]

/-- Relating vanishing low-order Taylor coefficients `f(X + b)` to divisibility by `(X - b)^m`. -/
theorem factor_of_taylor_vanish (f : Polynomial ℤ) (b : ℤ) (m : ℕ)
    (hvan : ∀ j < m, (f.comp (Polynomial.X + Polynomial.C b)).coeff j = 0) :
    ∃ g : Polynomial ℤ,
      f = (Polynomial.X - Polynomial.C b) ^ m * g ∧
      g.eval b = (f.comp (Polynomial.X + Polynomial.C b)).coeff m := by
  let h := f.comp (Polynomial.X + Polynomial.C b)
  have hdvd : Polynomial.X ^ m ∣ h := Polynomial.X_pow_dvd_iff.mpr hvan
  rcases hdvd with ⟨q, hq⟩
  refine ⟨q.comp (Polynomial.X - Polynomial.C b), ?_, ?_⟩
  · have hcomp : ((Polynomial.X + Polynomial.C b).comp (Polynomial.X - Polynomial.C b)) = Polynomial.X := by
      simp [Polynomial.add_comp, Polynomial.X_comp]
    calc
      f = f.comp Polynomial.X := (Polynomial.comp_X).symm
      _ = f.comp ((Polynomial.X + Polynomial.C b).comp (Polynomial.X - Polynomial.C b)) := by rw [hcomp]
      _ = h.comp (Polynomial.X - Polynomial.C b) := (Polynomial.comp_assoc f _ _).symm
      _ = (Polynomial.X ^ m * q).comp (Polynomial.X - Polynomial.C b) := by rw [hq]
      _ = (Polynomial.X - Polynomial.C b) ^ m * q.comp (Polynomial.X - Polynomial.C b) := by
          simp [Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.X_comp]
  · have hq0 : q.coeff 0 = h.coeff m := by
      have hm : h.coeff (0 + m) = q.coeff 0 := by
        rw [hq, Polynomial.coeff_X_pow_mul]
      simpa using hm.symm
    rw [Polynomial.eval_comp]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self]
    rw [← Polynomial.coeff_zero_eq_eval_zero, hq0]

/-- **Combined Taylor-Residue Modular Certificate (Factor Form):**
Suppose `p` is prime, `f_p := f.map (Int.castRingHom (ZMod p)) ≠ 0`, `f_p` has no double root
outside the residues of a finite set `S ⊂ ℤ`, and for each `b ∈ S` there exist `m ≥ 1` and
cofactor `g` with `f = (X - C b)^m * g` and `g(b) ≢ 0 (mod p)`. If `f_p` has at most `K`
distinct zeros in `ZMod p`, then `intRootCount f ≤ K` unconditionally over `ℤ`. -/
theorem intRootCount_le_of_factor_zmod (p : ℕ) [Fact p.Prime] (f : Polynomial ℤ)
    (S : Finset ℤ) (K : ℕ)
    (_hf_p : f.map (Int.castRingHom (ZMod p)) ≠ 0)
    (houtside : ∀ a : ZMod p,
      (f.map (Int.castRingHom (ZMod p))).IsRoot a →
      (f.map (Int.castRingHom (ZMod p))).derivative.IsRoot a →
      ∃ b ∈ S, (b : ZMod p) = a)
    (hfactor : ∀ b ∈ S, ∃ (m : ℕ) (g : Polynomial ℤ),
      1 ≤ m ∧ f = (Polynomial.X - Polynomial.C b) ^ m * g ∧
      (g.map (Int.castRingHom (ZMod p))).eval (b : ZMod p) ≠ 0)
    (hbound : (Finset.univ.filter (fun a : ZMod p =>
      (f.map (Int.castRingHom (ZMod p))).eval a = 0)).card ≤ K) :
    intRootCount f ≤ K := by
  set φ := Int.castRingHom (ZMod p)
  set f_p := f.map φ
  let Z := Finset.univ.filter (fun a : ZMod p => f_p.eval a = 0)
  have hmaps : ∀ r ∈ intRootSet f, (r : ZMod p) ∈ Z := by
    intro r hr
    rw [mem_intRootSet_iff] at hr
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [Polynomial.eval_map, Polynomial.eval₂_at_intCast]
    simp [hr.2.eq_zero]
  have hinj : Set.InjOn (fun r : ℤ => (r : ZMod p)) (intRootSet f) := by
    intro r₁ hr₁ r₂ hr₂ hmod
    by_contra hne
    have hsub : ∀ r ∈ ({r₁, r₂} : Finset ℤ), f.IsRoot r := by
      intro r hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl
      · exact (mem_intRootSet_iff.mp hr₁).2
      · exact (mem_intRootSet_iff.mp hr₂).2
    have hdvd_Z : (Polynomial.X - Polynomial.C r₁) * (Polynomial.X - Polynomial.C r₂) ∣ f := by
      have hprod := prod_linear_dvd_of_roots f {r₁, r₂} hsub
      rwa [Finset.prod_pair hne] at hprod
    have hsq_p : (Polynomial.X - Polynomial.C (r₁ : ZMod p)) ^ 2 ∣ f_p := by
      rcases hdvd_Z with ⟨q, hq⟩
      refine ⟨q.map φ, ?_⟩
      dsimp only at hmod
      have h1 : f_p = ((Polynomial.X - Polynomial.C r₁) * (Polynomial.X - Polynomial.C r₂)).map φ * q.map φ := by
        dsimp only [f_p]
        rw [hq, Polynomial.map_mul]
      rw [h1, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_sub,
        Polynomial.map_X, Polynomial.map_C, Polynomial.map_C]
      simp only [φ, Int.coe_castRingHom]
      rw [hmod, sq, mul_assoc]
    have hroot : f_p.IsRoot (r₁ : ZMod p) := by
      rw [Polynomial.IsRoot, Polynomial.eval_map, Polynomial.eval₂_at_intCast]
      simp [(mem_intRootSet_iff.mp hr₁).2.eq_zero]
    have hderiv : f_p.derivative.IsRoot (r₁ : ZMod p) := by
      rcases hsq_p with ⟨q, hq⟩
      have hq' : f_p = (Polynomial.X - Polynomial.C (r₁ : ZMod p)) *
          ((Polynomial.X - Polynomial.C (r₁ : ZMod p)) * q) := by
        rw [hq, sq, mul_assoc]
      rw [Polynomial.IsRoot, hq', Polynomial.derivative_mul]
      simp
    rcases houtside (r₁ : ZMod p) hroot hderiv with ⟨b, hbS, hb_eq⟩
    rcases hfactor b hbS with ⟨m, g, _, hfac, hgb⟩
    have hr1_eq : r₁ = b :=
      taylor_root_eq_of_factor p f g b m hfac hgb r₁ (mem_intRootSet_iff.mp hr₁).2 hb_eq.symm
    have hr2_eq : r₂ = b :=
      taylor_root_eq_of_factor p f g b m hfac hgb r₂ (mem_intRootSet_iff.mp hr₂).2
        (hmod.symm.trans hb_eq.symm)
    exact hne (hr1_eq.trans hr2_eq.symm)
  calc
    intRootCount f = (intRootSet f).card := rfl
    _ ≤ Z.card := Finset.card_le_card_of_injOn (fun r : ℤ => (r : ZMod p)) hmaps hinj
    _ ≤ K := hbound

/-- **Combined Taylor-Residue Modular Certificate (Exact Taylor Coefficient Form):**
This matches `certify_taylor_roots` in `tau_z9_unconditional.c`:
if `f_p` has `≤ K < p` zeros in `ZMod p` (ensuring `f_p ≠ 0`), no double roots outside
the residues of `S`, and for each `b ∈ S` the lowest nonzero Taylor coefficient
`c_m = (f.comp (X + C b)).coeff m` has index `m ≥ 1` and `¬ ((p : ℤ) ∣ c_m)`, then
`intRootCount f ≤ K`. -/
theorem intRootCount_le_of_taylor_zmod (p : ℕ) [Fact p.Prime] (f : Polynomial ℤ)
    (S : Finset ℤ) (K : ℕ) (hKp : K < p)
    (houtside : ∀ a : ZMod p,
      (f.map (Int.castRingHom (ZMod p))).IsRoot a →
      (f.map (Int.castRingHom (ZMod p))).derivative.IsRoot a →
      ∃ b ∈ S, (b : ZMod p) = a)
    (htaylor : ∀ b ∈ S, ∃ m : ℕ, 1 ≤ m ∧
      (∀ j < m, (f.comp (Polynomial.X + Polynomial.C b)).coeff j = 0) ∧
      ¬ ((p : ℤ) ∣ (f.comp (Polynomial.X + Polynomial.C b)).coeff m))
    (hbound : (Finset.univ.filter (fun a : ZMod p =>
      (f.map (Int.castRingHom (ZMod p))).eval a = 0)).card ≤ K) :
    intRootCount f ≤ K := by
  have hf_p : f.map (Int.castRingHom (ZMod p)) ≠ 0 := by
    by_contra h0
    have huniv : Finset.univ ⊆ Finset.univ.filter (fun a : ZMod p =>
        (f.map (Int.castRingHom (ZMod p))).eval a = 0) := by
      intro a _
      simp [h0]
    have hcard : p ≤ K := by
      calc
        p = Fintype.card (ZMod p) := (ZMod.card p).symm
        _ = (Finset.univ : Finset (ZMod p)).card := rfl
        _ ≤ _ := Finset.card_le_card huniv
        _ ≤ K := hbound
    omega
  refine intRootCount_le_of_factor_zmod p f S K hf_p houtside ?_ hbound
  intro b hbS
  rcases htaylor b hbS with ⟨m, hm1, hvan, hndvd⟩
  rcases factor_of_taylor_vanish f b m hvan with ⟨g, hfac, hgb⟩
  refine ⟨m, g, hm1, hfac, ?_⟩
  rw [Polynomial.eval_map, Polynomial.eval₂_at_intCast]
  change ((g.eval b : ℤ) : ZMod p) ≠ 0
  rw [hgb, ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact hndvd

/-- The 7 known small root centers `{0, 1, -1, 2, -2, 3, -3}` have pairwise distinct
residues modulo any prime/modulus `p ≥ 7` (in particular `p ≥ 19`). -/
theorem known_centers_distinct_zmod (p : ℕ) (hp : 7 ≤ p) :
    ∀ b₁ ∈ ({0, 1, -1, 2, -2, 3, -3} : Finset ℤ),
    ∀ b₂ ∈ ({0, 1, -1, 2, -2, 3, -3} : Finset ℤ),
      (b₁ : ZMod p) = (b₂ : ZMod p) → b₁ = b₂ := by
  intro b₁ hb₁ b₂ hb₂ hmod
  have hsub : ((b₁ - b₂ : ℤ) : ZMod p) = 0 := by push_cast; exact sub_eq_zero.mpr hmod
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hsub
  have hb1' : -3 ≤ b₁ ∧ b₁ ≤ 3 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb₁
    rcases hb₁ with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hb2' : -3 ≤ b₂ ∧ b₂ ≤ 3 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb₂
    rcases hb₂ with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  rcases hsub with ⟨k, hk⟩
  have hlt : (b₁ - b₂).natAbs < p := by omega
  by_cases h0 : b₁ - b₂ = 0
  · omega
  · have hge : p ≤ (b₁ - b₂).natAbs := by
      have hk0 : k ≠ 0 := fun h => h0 (by simp [hk, h])
      have hk1 : 1 ≤ k.natAbs := Int.natAbs_pos.mpr hk0
      have : (b₁ - b₂).natAbs = p * k.natAbs := by
        have := congrArg Int.natAbs hk
        simpa [Int.natAbs_mul] using this
      nlinarith
    omega

/-- Evaluating an `SLP` in `ℤ[X]` at `X + C b` produces the Taylor-shifted polynomial
`P.evalPoly.comp (X + C b)`. -/
theorem slp_evalIn_taylor {τ : ℕ} (P : SLP τ) (b : ℤ) :
    P.evalIn (Polynomial.X + Polynomial.C b) =
      P.evalPoly.comp (Polynomial.X + Polynomial.C b) := by
  let φ : Polynomial ℤ →+* Polynomial ℤ :=
    Polynomial.eval₂RingHom Polynomial.C (Polynomial.X + Polynomial.C b)
  have hX : φ Polynomial.X = Polynomial.X + Polynomial.C b := by simp [φ]
  have h := P.map_evalIn φ Polynomial.X
  rw [P.evalIn_X, hX] at h
  rw [← h]
  rfl

/-! ## 6. Exact-Equality-by-Evaluation & Hash Mismatch Soundness -/

/-- **Hash Mismatch Soundness (`≠`):**
Because `evalIn` commutes with ring homomorphisms, any discrepancy between `P₁.evalIn x`
and `P₂.evalIn x` (or `-P₂.evalIn x`) in any commutative ring `R` proves `P₁.evalPoly ≠ P₂.evalPoly`
(respectively `≠ -P₂.evalPoly`). -/
theorem slp_evalPoly_ne_of_evalIn_ne {R : Type*} [CommRing R] (x : R)
    {τ₁ τ₂ : ℕ} (P₁ : SLP τ₁) (P₂ : SLP τ₂) (hne : P₁.evalIn x ≠ P₂.evalIn x) :
    P₁.evalPoly ≠ P₂.evalPoly := by
  intro heq
  apply hne
  rw [P₁.evalIn_eq_eval₂ x, P₂.evalIn_eq_eval₂ x, heq]

theorem slp_evalPoly_ne_neg_of_evalIn_ne {R : Type*} [CommRing R] (x : R)
    {τ₁ τ₂ : ℕ} (P₁ : SLP τ₁) (P₂ : SLP τ₂) (hne : P₁.evalIn x ≠ -P₂.evalIn x) :
    P₁.evalPoly ≠ -P₂.evalPoly := by
  intro heq
  apply hne
  rw [P₁.evalIn_eq_eval₂ x, P₂.evalIn_eq_eval₂ x, heq, Polynomial.map_neg, Polynomial.eval_neg]

/-- **Single-Prime Evaluation Vanishing Lemma:**
If `h ∈ ℤ[X]` has `natDegree ≤ D` and reduces to `0` at `D + 1` distinct residues
modulo a prime `q`, then `h ≡ 0 (mod q)` (every coefficient of `h` is divisible by `q`). -/
theorem poly_map_zmod_eq_zero_of_roots (q : ℕ) [Fact q.Prime] (h : Polynomial ℤ) (D : ℕ)
    (hdeg : h.natDegree ≤ D) (T : Finset (ZMod q)) (hT : D + 1 ≤ T.card)
    (hvan : ∀ t ∈ T, (h.map (Int.castRingHom (ZMod q))).eval t = 0) :
    h.map (Int.castRingHom (ZMod q)) = 0 := by
  set hq := h.map (Int.castRingHom (ZMod q))
  by_contra hne
  have hsub : T ⊆ hq.roots.toFinset := by
    intro t ht
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hne]
    exact hvan t ht
  have hcard : D + 1 ≤ hq.natDegree := by
    calc
      D + 1 ≤ T.card := hT
      _ ≤ hq.roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ hq.roots.card := Multiset.toFinset_card_le _
      _ ≤ hq.natDegree := Polynomial.card_roots' hq
  have hdeg_le : hq.natDegree ≤ D := (Polynomial.natDegree_map_le).trans hdeg
  omega

/-- Helper: if a finite set of distinct primes each divide `c : ℤ`, then their product divides `c`. -/
private lemma prod_primes_dvd_of_forall_dvd (Q : Finset ℕ) (hQ : ∀ q ∈ Q, Nat.Prime q)
    (c : ℤ) (hdvd : ∀ q ∈ Q, (q : ℤ) ∣ c) :
    ((∏ q ∈ Q, q : ℕ) : ℤ) ∣ c := by
  classical
  induction Q using Finset.induction_on with
  | empty => simp
  | @insert q s hqs ih =>
      have hq_prime : Nat.Prime q := hQ q (Finset.mem_insert_self q s)
      have hs_prime : ∀ r ∈ s, Nat.Prime r := fun r hr => hQ r (Finset.mem_insert_of_mem hr)
      have hs_dvd : ((∏ r ∈ s, r : ℕ) : ℤ) ∣ c :=
        ih hs_prime (fun r hr => hdvd r (Finset.mem_insert_of_mem hr))
      have hq_dvd : (q : ℤ) ∣ c := hdvd q (Finset.mem_insert_self q s)
      have hcop_aux : ∀ t : Finset ℕ, q ∉ t → (∀ r ∈ t, Nat.Prime r) → Nat.Coprime q (∏ r ∈ t, r) := by
        intro t
        induction t using Finset.induction_on with
        | empty => intro _ _; simp
        | @insert r t hrt ihr =>
            intro hq_not ht_prime
            rw [Finset.prod_insert hrt]
            have hr_ne : q ≠ r := fun h => hq_not (h ▸ Finset.mem_insert_self r t)
            have hr_prime : Nat.Prime r := ht_prime r (Finset.mem_insert_self r t)
            have hqr : Nat.Coprime q r :=
              (hq_prime.coprime_iff_not_dvd).mpr (fun h =>
                hr_ne ((Nat.prime_dvd_prime_iff_eq hq_prime hr_prime).mp h))
            have hqt : Nat.Coprime q (∏ x ∈ t, x) :=
              ihr (fun h => hq_not (Finset.mem_insert_of_mem h))
                (fun x hx => ht_prime x (Finset.mem_insert_of_mem hx))
            exact hqr.mul_right hqt
      have hcop : Nat.Coprime q (∏ r ∈ s, r) := hcop_aux s hqs hs_prime
      have hcopZ : IsCoprime (q : ℤ) ((∏ r ∈ s, r : ℕ) : ℤ) := hcop.isCoprime
      rw [Finset.prod_insert hqs, Nat.cast_mul]
      exact hcopZ.mul_dvd hq_dvd hs_dvd

/-- **CRT Exact-Zero Certificate by Evaluation:**
If `h ∈ ℤ[X]` has `natDegree ≤ D`, vanishes at `D + 1` distinct residues modulo each prime
`q ∈ Q`, and every coefficient satisfies `2 * |h.coeff n| < ∏ q ∈ Q, q`, then `h = 0`. -/
theorem poly_eq_zero_of_crt_eval (Q : Finset ℕ) (hQ : ∀ q ∈ Q, Nat.Prime q)
    (h : Polynomial ℤ) (D : ℕ) (hdeg : h.natDegree ≤ D)
    (hvan : ∀ q ∈ Q, ∃ T : Finset (ZMod q), D + 1 ≤ T.card ∧
      ∀ t ∈ T, (h.map (Int.castRingHom (ZMod q))).eval t = 0)
    (hsmall : ∀ n ≤ D, 2 * (h.coeff n).natAbs < ∏ q ∈ Q, q) :
    h = 0 := by
  have hmod : ∀ q ∈ Q, h.map (Int.castRingHom (ZMod q)) = 0 := by
    intro q hq
    have : Fact q.Prime := ⟨hQ q hq⟩
    rcases hvan q hq with ⟨T, hT, ht⟩
    exact poly_map_zmod_eq_zero_of_roots q h D hdeg T hT ht
  ext n
  simp only [Polynomial.coeff_zero]
  by_cases hn : n ≤ D
  · have hdvd_all : ∀ q ∈ Q, (q : ℤ) ∣ h.coeff n := by
      intro q hq
      have hq0 := congrArg (fun p : Polynomial (ZMod q) => p.coeff n) (hmod q hq)
      simp only [Polynomial.coeff_map, Polynomial.coeff_zero, Int.coe_castRingHom] at hq0
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd (h.coeff n) q).mp hq0
    have hprod_dvd : ((∏ q ∈ Q, q : ℕ) : ℤ) ∣ h.coeff n :=
      prod_primes_dvd_of_forall_dvd Q hQ (h.coeff n) hdvd_all
    have hnat_dvd : (∏ q ∈ Q, q) ∣ (h.coeff n).natAbs :=
      Int.natCast_dvd.mp hprod_dvd
    have hbound := hsmall n hn
    by_contra hne
    have hpos : 0 < (h.coeff n).natAbs := Int.natAbs_pos.mpr hne
    have hle : ∏ q ∈ Q, q ≤ (h.coeff n).natAbs := Nat.le_of_dvd hpos hnat_dvd
    omega
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

end Research.PvsNP.Tau

end
