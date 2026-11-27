module

public import Research.PvsNP.Tau.TauConjecture

@[expose] public section

namespace Research.PvsNP.Tau

/-!
# Canonicalization and Pruning Soundness for Constant-Free SLPs

This module formalizes the list-based straight-line program (`GateSpec`) representation,
its equivalence with `SLP τ`, the canonicalization predicate `Canonical` used by the
exhaustive enumerator, and the soundness theorems:

1. `exists_canonical`: every nonzero polynomial `f` computed by a length-`t` `SLP`
   either belongs to `{1, -1, X, -X}` or is computed up to sign (`±f`) by a
   `Canonical` gate list of length `1 ≤ k ≤ t`.
2. `deadgate_count_bound`: in any `Canonical` (or `UsedGates`) gate list of length `n`,
   after `d < n` gates, the number of unused gate wires `unusedWires gs d` satisfies
   `≤ n - d + 1`, and at the last gate (`d = n - 1`) at most `2` gate wires remain unused
   and every unused gate wire must be an operand of the last gate.
3. `zmax_le_of_checklist`, `zmax9_le_six_of_checklist`, `zmax10_le_seven_of_checklist`:
   conditional upper bounds transferring root-count bounds on all `Canonical` gate lists
   of length `1 ≤ n ≤ τ` to all nonzero `SLP t` with `t ≤ τ`.
-/

/-! ## 1. List-Based Gate Representation & Equivalence with `SLP` -/

/-- A single gate in a list-based constant-free straight-line program.
Gate `k` (0-based) reads wires `i` and `j` and outputs wire `k + 2`. -/
structure GateSpec where
  op : SLPOp
  i : ℕ
  j : ℕ
  deriving DecidableEq, Repr

instance : Inhabited GateSpec := ⟨⟨.add, 0, 0⟩⟩

/-- Auxiliary accumulator evaluator for a list of gate specifications over `ℤ[X]`. -/
noncomputable def wireValsAux : List (Polynomial ℤ) → List GateSpec → List (Polynomial ℤ)
  | acc, [] => acc
  | acc, g :: rest =>
      wireValsAux (acc ++ [g.op.applyPoly (acc.getD g.i 0) (acc.getD g.j 0)]) rest

/-- Polynomial values of all wires `0, 1, ..., gs.length + 1` computed by `gs`.
Wire `0` holds `1`, wire `1` holds `X`, and gate `k` computes wire `k + 2`. -/
noncomputable def wireVals (gs : List GateSpec) : List (Polynomial ℤ) :=
  wireValsAux [1, Polynomial.X] gs

/-- Output polynomial of `gs` (wire `gs.length + 1`, or `X` when `gs = []`). -/
noncomputable def output (gs : List GateSpec) : Polynomial ℤ :=
  (wireVals gs).getD (gs.length + 1) 0

/-- A gate list `gs` is well-formed when every gate `k` reads only wires `< k + 2`. -/
def WellFormed (gs : List GateSpec) : Prop :=
  ∀ (k : ℕ) (hk : k < gs.length), gs[k].i < k + 2 ∧ gs[k].j < k + 2

private lemma getD_eq_getElem_of_lt {α : Type*} (l : List α) (d : α) {i : ℕ}
    (hi : i < l.length) : l.getD i d = l[i] := by
  simp [List.getD, hi]

private lemma getD_append_left {α : Type*} (l₁ l₂ : List α) (d : α) {i : ℕ}
    (hi : i < l₁.length) : (l₁ ++ l₂).getD i d = l₁.getD i d := by
  have hi' : i < (l₁ ++ l₂).length := by simp; omega
  rw [getD_eq_getElem_of_lt _ d hi', getD_eq_getElem_of_lt _ d hi, List.getElem_append_left hi]

private lemma getD_append_right {α : Type*} (l₁ l₂ : List α) (d : α) {i : ℕ}
    (hi : l₁.length ≤ i) : (l₁ ++ l₂).getD i d = l₂.getD (i - l₁.length) d := by
  by_cases hlt : i < (l₁ ++ l₂).length
  · have hlt2 : i - l₁.length < l₂.length := by simp at hlt; omega
    rw [getD_eq_getElem_of_lt _ d hlt, getD_eq_getElem_of_lt _ d hlt2, List.getElem_append_right hi]
  · have hge1 : (l₁ ++ l₂).length ≤ i := Nat.le_of_not_lt hlt
    have hge2 : l₂.length ≤ i - l₁.length := by simp at hge1; omega
    simp [List.getD, List.getElem?_eq_none hge1, List.getElem?_eq_none hge2]

theorem wireValsAux_length (acc : List (Polynomial ℤ)) (gs : List GateSpec) :
    (wireValsAux acc gs).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [wireValsAux]
  | cons g rest ih =>
      simp only [wireValsAux]
      rw [ih]
      simp
      omega

theorem wireVals_length (gs : List GateSpec) :
    (wireVals gs).length = gs.length + 2 := by
  rw [wireVals, wireValsAux_length]
  simp
  omega

theorem wireValsAux_append (acc : List (Polynomial ℤ)) (gs₁ gs₂ : List GateSpec) :
    wireValsAux acc (gs₁ ++ gs₂) = wireValsAux (wireValsAux acc gs₁) gs₂ := by
  induction gs₁ generalizing acc with
  | nil => simp [wireValsAux]
  | cons g rest ih => simp [wireValsAux, ih]

theorem wireVals_snoc (gs : List GateSpec) (g : GateSpec) :
    wireVals (gs ++ [g]) =
      wireVals gs ++ [g.op.applyPoly ((wireVals gs).getD g.i 0) ((wireVals gs).getD g.j 0)] := by
  simp [wireVals, wireValsAux_append, wireValsAux]

theorem wireValsAux_getD_lt (acc : List (Polynomial ℤ)) (gs : List GateSpec)
    {w : ℕ} (hw : w < acc.length) :
    (wireValsAux acc gs).getD w 0 = acc.getD w 0 := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g rest ih =>
      have hw' : w < (acc ++ [g.op.applyPoly (acc.getD g.i 0) (acc.getD g.j 0)]).length := by
        simp; omega
      rw [wireValsAux, ih _ hw', getD_append_left _ _ _ hw]

theorem wireVals_zero (gs : List GateSpec) : (wireVals gs).getD 0 0 = 1 := by
  have h := wireValsAux_getD_lt [1, Polynomial.X] gs (w := 0) (by decide)
  simpa [wireVals] using h

theorem wireVals_one (gs : List GateSpec) : (wireVals gs).getD 1 0 = Polynomial.X := by
  have h := wireValsAux_getD_lt [1, Polynomial.X] gs (w := 1) (by decide)
  simpa [wireVals] using h

theorem wireVals_take_getD (gs : List GateSpec) {m w : ℕ}
    (hm : m ≤ gs.length) (hw : w < m + 2) :
    (wireVals (gs.take m)).getD w 0 = (wireVals gs).getD w 0 := by
  have hsplit : gs = gs.take m ++ gs.drop m := (List.take_append_drop m gs).symm
  have hlen : (wireVals (gs.take m)).length = m + 2 := by
    rw [wireVals_length, List.length_take, Nat.min_eq_left hm]
  have haux : wireVals gs = wireValsAux (wireVals (gs.take m)) (gs.drop m) := by
    rw [wireVals, wireVals, ← wireValsAux_append, ← hsplit]
  rw [haux]
  exact (wireValsAux_getD_lt (wireVals (gs.take m)) (gs.drop m) (hw.trans_eq hlen.symm)).symm

theorem wireVals_gate_take (gs : List GateSpec) {k : ℕ} (hk : k < gs.length) :
    (wireVals gs).getD (k + 2) 0 =
      (gs[k]).op.applyPoly
        ((wireVals (gs.take k)).getD (gs[k]).i 0)
        ((wireVals (gs.take k)).getD (gs[k]).j 0) := by
  have htake : gs.take (k + 1) = gs.take k ++ [gs[k]] := List.take_add_one.trans (by simp [hk])
  have hlen : (wireVals (gs.take k)).length = k + 2 := by
    rw [wireVals_length, List.length_take, Nat.min_eq_left hk.le]
  have hw := wireVals_take_getD gs (m := k + 1) (w := k + 2) hk (by omega)
  rw [← hw, htake, wireVals_snoc, getD_append_right _ _ _ hlen.le]
  simp [hlen]

theorem wireVals_gate (gs : List GateSpec) {k : ℕ} (hk : k < gs.length)
    (hi : gs[k].i < k + 2) (hj : gs[k].j < k + 2) :
    (wireVals gs).getD (k + 2) 0 =
      (gs[k]).op.applyPoly ((wireVals gs).getD gs[k].i 0) ((wireVals gs).getD gs[k].j 0) := by
  rw [wireVals_gate_take gs hk,
    wireVals_take_getD gs hk.le hi,
    wireVals_take_getD gs hk.le hj]

theorem wireVals_gate_wf {gs : List GateSpec} (hwf : WellFormed gs) {k : ℕ} (hk : k < gs.length) :
    (wireVals gs).getD (k + 2) 0 =
      (gs[k]).op.applyPoly ((wireVals gs).getD gs[k].i 0) ((wireVals gs).getD gs[k].j 0) :=
  wireVals_gate gs hk (hwf k hk).1 (hwf k hk).2

/-- Convert an `SLP τ` into a well-formed list of `τ` gate specifications. -/
def SLP.toGateList : {τ : ℕ} → SLP τ → List GateSpec
  | 0, .nil => []
  | _ + 1, .snoc P op i j => P.toGateList ++ [⟨op, i.val, j.val⟩]

theorem SLP.toGateList_length : ∀ {τ : ℕ} (P : SLP τ), P.toGateList.length = τ
  | 0, .nil => rfl
  | _ + 1, .snoc P _ _ _ => by simp [SLP.toGateList, P.toGateList_length]

theorem SLP.toGateList_wellFormed : ∀ {τ : ℕ} (P : SLP τ), WellFormed P.toGateList
  | 0, .nil => fun k hk => by simp [SLP.toGateList] at hk
  | τ + 1, .snoc P op i j => by
      intro k hk
      simp only [SLP.toGateList, List.length_append, List.length_singleton, P.toGateList_length] at hk
      by_cases hlt : k < τ
      · have hlen : k < P.toGateList.length := by simpa [P.toGateList_length] using hlt
        simpa [SLP.toGateList, List.getElem_append_left hlen] using P.toGateList_wellFormed k hlen
      · have heq : k = τ := by omega
        subst k
        have hlen : P.toGateList.length = τ := P.toGateList_length
        simp only [SLP.toGateList, List.getElem_append_right hlen.le, hlen, Nat.sub_self,
          List.getElem_singleton]
        exact ⟨i.isLt, j.isLt⟩

theorem SLP.wireVals_toGateList :
    ∀ {τ : ℕ} (P : SLP τ) (k : Fin (τ + 2)),
      (wireVals P.toGateList).getD k.val 0 = P.evalWire k
  | 0, .nil, k => by
      simp only [SLP.toGateList, wireVals, wireValsAux, SLP.evalWire]
      rcases k with ⟨kv, hkv⟩
      rcases kv with _ | _ | kv
      · simp [List.getD]
      · simp [List.getD]
      · omega
  | τ + 1, .snoc P op i j, k => by
      simp only [SLP.toGateList, wireVals_snoc, SLP.evalWire]
      have hlen : (wireVals P.toGateList).length = τ + 2 := by
        rw [wireVals_length, P.toGateList_length]
      split_ifs with hk
      · rw [getD_append_left _ _ _ (hk.trans_eq hlen.symm)]
        exact P.wireVals_toGateList ⟨k.val, hk⟩
      · have hk_eq : k.val = τ + 2 := by omega
        rw [getD_append_right _ _ _ (by omega)]
        simp only [hlen, hk_eq, Nat.sub_self]
        rw [getD_eq_getElem_of_lt _ _ (by simp), List.getElem_singleton]
        rw [P.wireVals_toGateList i, P.wireVals_toGateList j]

theorem SLP.output_toGateList {τ : ℕ} (P : SLP τ) :
    output P.toGateList = P.evalPoly := by
  have h := P.wireVals_toGateList ⟨τ + 1, Nat.lt_succ_self _⟩
  simpa [output, SLP.evalPoly, P.toGateList_length] using h

/-- Auxiliary builder turning the prefix of length `n ≤ gs.length` of a well-formed gate list
into an `SLP n`. -/
def SLP.ofGateListAux (gs : List GateSpec) (hwf : WellFormed gs) :
    (n : ℕ) → n ≤ gs.length → SLP n
  | 0, _ => .nil
  | n + 1, hn =>
      let P := SLP.ofGateListAux gs hwf n (Nat.le_of_lt hn)
      let g := gs[n]'hn
      let hg := hwf n hn
      P.snoc g.op ⟨g.i, hg.1⟩ ⟨g.j, hg.2⟩

/-- Convert a well-formed gate list `gs` back into an `SLP gs.length`. -/
def SLP.ofGateList (gs : List GateSpec) (hwf : WellFormed gs) : SLP gs.length :=
  SLP.ofGateListAux gs hwf gs.length le_rfl

theorem SLP.evalWire_ofGateListAux (gs : List GateSpec) (hwf : WellFormed gs) :
    ∀ (n : ℕ) (hn : n ≤ gs.length) (k : Fin (n + 2)),
      (SLP.ofGateListAux gs hwf n hn).evalWire k = (wireVals (gs.take n)).getD k.val 0
  | 0, _, k => by
      simp only [SLP.ofGateListAux, SLP.evalWire, List.take_zero, wireVals, wireValsAux]
      rcases k with ⟨kv, hkv⟩
      rcases kv with _ | _ | kv
      · simp [List.getD]
      · simp [List.getD]
      · omega
  | n + 1, hn, k => by
      simp only [SLP.ofGateListAux, SLP.evalWire]
      have htake : gs.take (n + 1) = gs.take n ++ [gs[n]'hn] := by
        rw [List.take_add_one, List.getElem?_eq_getElem (Nat.lt_of_succ_le hn)]
        rfl
      have hlen : (wireVals (gs.take n)).length = n + 2 := by
        rw [wireVals_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hn)]
      split_ifs with hk
      · rw [SLP.evalWire_ofGateListAux gs hwf n (Nat.le_of_lt hn) ⟨k.val, hk⟩,
          htake, wireVals_snoc, getD_append_left _ _ _ (hk.trans_eq hlen.symm)]
      · have hk_eq : k.val = n + 2 := by omega
        rw [htake, wireVals_snoc, getD_append_right _ _ _ (by omega)]
        simp only [hlen, hk_eq, Nat.sub_self]
        rw [getD_eq_getElem_of_lt _ _ (by simp), List.getElem_singleton]
        rw [SLP.evalWire_ofGateListAux gs hwf n (Nat.le_of_lt hn),
          SLP.evalWire_ofGateListAux gs hwf n (Nat.le_of_lt hn)]

theorem SLP.evalPoly_ofGateList (gs : List GateSpec) (hwf : WellFormed gs) :
    (SLP.ofGateList gs hwf).evalPoly = output gs := by
  have h := SLP.evalWire_ofGateListAux gs hwf gs.length le_rfl ⟨gs.length + 1, Nat.lt_succ_self _⟩
  simpa [SLP.ofGateList, SLP.evalPoly, output] using h

/-! ## 2. Canonical Predicate -/

/-- Canonical numeric index of an `SLPOp` (`add = 0`, `sub = 1`, `mul = 2`). -/
def SLPOp.idx : SLPOp → ℕ
  | .add => 0
  | .sub => 1
  | .mul => 2

/-- Operand-order condition `(ord)` for a single gate:
`i < j` for subtraction, `i ≤ j` for addition and multiplication. -/
def GateSpec.Ord (g : GateSpec) : Prop :=
  match g.op with
  | .sub => g.i < g.j
  | .add | .mul => g.i ≤ g.j

/-- Lexicographic `≤` comparison on `(op.idx, i, j)` triples. -/
def GateSpec.keyLe (g₁ g₂ : GateSpec) : Prop :=
  g₁.op.idx < g₂.op.idx ∨
  (g₁.op.idx = g₂.op.idx ∧ (g₁.i < g₂.i ∨ (g₁.i = g₂.i ∧ g₁.j ≤ g₂.j)))

/-- Strict lexicographic `<` comparison on `(op.idx, i, j)` triples. -/
def GateSpec.keyLt (g₁ g₂ : GateSpec) : Prop :=
  g₁.op.idx < g₂.op.idx ∨
  (g₁.op.idx = g₂.op.idx ∧ (g₁.i < g₂.i ∨ (g₁.i = g₂.i ∧ g₁.j < g₂.j)))

/-- Base-32 packed integer key `op * 1024 + i * 32 + j` used by the C enumerator
when wire indices are `< 32` (which holds whenever `gs.length ≤ 30` and `WellFormed gs`). -/
def GateSpec.key32 (g : GateSpec) : ℕ :=
  g.op.idx * 1024 + g.i * 32 + g.j

theorem GateSpec.not_keyLe_iff {g₁ g₂ : GateSpec} : ¬ g₁.keyLe g₂ ↔ g₂.keyLt g₁ := by
  unfold GateSpec.keyLe GateSpec.keyLt
  omega

theorem GateSpec.keyLe_iff_key32 {g₁ g₂ : GateSpec}
    (hi₁ : g₁.i < 32) (hj₁ : g₁.j < 32) (hi₂ : g₂.i < 32) (hj₂ : g₂.j < 32) :
    g₁.keyLe g₂ ↔ g₁.key32 ≤ g₂.key32 := by
  unfold GateSpec.keyLe GateSpec.key32
  omega

/-- Every gate in `gs` satisfies the operand-order condition `(ord)`. -/
def OrdCanonical (gs : List GateSpec) : Prop :=
  ∀ (k : ℕ) (hk : k < gs.length), gs[k].Ord

/-- Every gate wire `k + 2` in `gs` evaluates to a nonzero polynomial `(nonzero)`. -/
def NonzeroWires (gs : List GateSpec) : Prop :=
  ∀ (k : ℕ) (hk : k < gs.length), (wireVals gs).getD (k + 2) 0 ≠ 0

/-- No gate wire `k + 2` duplicates an earlier wire `m < k + 2` up to sign `(nodup)`. -/
def NodupWires (gs : List GateSpec) : Prop :=
  ∀ (k : ℕ) (hk : k < gs.length) (m : ℕ), m < k + 2 →
    (wireVals gs).getD (k + 2) 0 ≠ (wireVals gs).getD m 0 ∧
    (wireVals gs).getD (k + 2) 0 ≠ -((wireVals gs).getD m 0)

/-- Every gate except the last is an operand of at least one later gate `(used)`. -/
def UsedGates (gs : List GateSpec) : Prop :=
  ∀ (k : ℕ), k + 1 < gs.length →
    ∃ (k' : ℕ) (hk' : k' < gs.length), k < k' ∧ (gs[k'].i = k + 2 ∨ gs[k'].j = k + 2)

/-- For every non-final gate `k` (`1 ≤ k ≤ n - 2`) that does not use gate `k - 1`
(wire `k + 1`), the key triple of gate `k - 1` precedes or equals that of gate `k` `(lex)`. -/
def LexOrdered (gs : List GateSpec) : Prop :=
  ∀ (k : ℕ), 1 ≤ k → k + 1 < gs.length →
    (h1 : k - 1 < gs.length) → (h2 : k < gs.length) →
    gs[k].i ≠ k + 1 → gs[k].j ≠ k + 1 → (gs[k - 1]'h1).keyLe (gs[k]'h2)

/-- Complete canonicality predicate matching the exhaustive enumerator. -/
structure Canonical (gs : List GateSpec) : Prop where
  wf : WellFormed gs
  ord : OrdCanonical gs
  nonzero : NonzeroWires gs
  nodup : NodupWires gs
  used : UsedGates gs
  lex : LexOrdered gs

/-! ## 3. Reduction Lemmas Toward `exists_canonical` -/

/-- Target predicate: `gs` computes `f` or `-f`. -/
def ComputesSigned (f : Polynomial ℤ) (gs : List GateSpec) : Prop :=
  output gs = f ∨ output gs = -f

private noncomputable def sgnVal (b : Bool) : Polynomial ℤ :=
  if b then -1 else 1

private lemma sgnVal_mul_self (b : Bool) : sgnVal b * sgnVal b = 1 := by
  cases b <;> simp [sgnVal]

private lemma sgnVal_xor (b₁ b₂ : Bool) : sgnVal (xor b₁ b₂) = sgnVal b₁ * sgnVal b₂ := by
  cases b₁ <;> cases b₂ <;> simp [sgnVal]

private lemma sgnVal_not (b : Bool) : sgnVal (!b) = -sgnVal b := by
  cases b <;> simp [sgnVal]

private lemma sgnVal_ne_zero (b : Bool) : sgnVal b ≠ 0 := by
  cases b <;> simp [sgnVal]

private def flipAddSub : SLPOp → SLPOp
  | .add => .sub
  | .sub => .add
  | .mul => .mul

private lemma applyPoly_signed_combine (op : SLPOp) (s₁ s₂ : Bool) (a b : Polynomial ℤ) :
    (match op with
      | .mul => sgnVal (xor s₁ s₂) * (a * b)
      | .add => sgnVal s₁ * ((if s₁ = s₂ then op else flipAddSub op).applyPoly a b)
      | .sub => sgnVal s₁ * ((if s₁ = s₂ then op else flipAddSub op).applyPoly a b)) =
      op.applyPoly (sgnVal s₁ * a) (sgnVal s₂ * b) := by
  cases op <;> cases s₁ <;> cases s₂ <;>
    simp [sgnVal, flipAddSub, SLPOp.applyPoly] <;> ring

private def shiftDown (k w : ℕ) : ℕ :=
  if k + 2 < w then w - 1 else w

private lemma shiftDown_lt {k m w : ℕ} (hm : k ≤ m) (hw : w < m + 3) (hne : w ≠ k + 2) :
    shiftDown k w < m + 2 := by
  unfold shiftDown
  split_ifs <;> omega

private lemma shiftDown_inv {k w : ℕ} (hne : w ≠ k + 2) :
    (if shiftDown k w < k + 2 then shiftDown k w else shiftDown k w + 1) = w := by
  unfold shiftDown
  split_ifs <;> omega

/-- Delete unused gate `k` (`k + 1 < gs.length`) and shift wire indices `> k + 2` down by `1`. -/
private def deleteUnused (gs : List GateSpec) (k : ℕ) : List GateSpec :=
  List.ofFn (fun m : Fin (gs.length - 1) =>
    if m.val < k then
      gs[m.val]'(by omega)
    else
      let g := gs[m.val + 1]'(by omega)
      ⟨g.op, shiftDown k g.i, shiftDown k g.j⟩)

private lemma deleteUnused_length (gs : List GateSpec) (k : ℕ) :
    (deleteUnused gs k).length = gs.length - 1 := by
  simp [deleteUnused]

private lemma deleteUnused_wellFormed {gs : List GateSpec} (hwf : WellFormed gs)
    {k : ℕ} (hdead : ∀ (k' : ℕ) (hk' : k' < gs.length), k < k' → gs[k'].i ≠ k + 2 ∧ gs[k'].j ≠ k + 2) :
    WellFormed (deleteUnused gs k) := by
  intro m hm
  rw [deleteUnused_length] at hm
  simp only [deleteUnused, List.getElem_ofFn]
  split_ifs with hmk
  · exact hwf m (by omega)
  · have hm1 : m + 1 < gs.length := by omega
    have hgm := hwf (m + 1) hm1
    have hd := hdead (m + 1) hm1 (by omega)
    exact ⟨shiftDown_lt (by omega) hgm.1 hd.1, shiftDown_lt (by omega) hgm.2 hd.2⟩

private lemma deleteUnused_wireVals {gs : List GateSpec} (hwf : WellFormed gs)
    {k : ℕ} (hk : k + 1 < gs.length)
    (hdead : ∀ (k' : ℕ) (hk' : k' < gs.length), k < k' → gs[k'].i ≠ k + 2 ∧ gs[k'].j ≠ k + 2) :
    ∀ (w : ℕ), w < (deleteUnused gs k).length + 2 →
      (wireVals (deleteUnused gs k)).getD w 0 =
        (wireVals gs).getD (if w < k + 2 then w else w + 1) 0 := by
  have hwf' := deleteUnused_wellFormed hwf hdead
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
      intro hw
      rcases w with _ | _ | m
      · rw [if_pos (by omega), wireVals_zero, wireVals_zero]
      · change (wireVals (deleteUnused gs k)).getD 1 0 =
          (wireVals gs).getD (if 1 < k + 2 then 1 else 1 + 1) 0
        rw [if_pos (by omega), wireVals_one, wireVals_one]
      · have hm : m < (deleteUnused gs k).length := by omega
        have hm' : m < gs.length - 1 := by simpa [deleteUnused_length] using hm
        rw [wireVals_gate_wf hwf' hm]
        have hi_lt := (hwf' m hm).1
        have hj_lt := (hwf' m hm).2
        rw [ih _ hi_lt (by omega), ih _ hj_lt (by omega)]
        by_cases hmk : m < k
        · have hg_eq : (deleteUnused gs k)[m] = gs[m]'(by omega) := by
            simp [deleteUnused, hmk]
          have hm_lt : m < gs.length := by omega
          have hmi : gs[m].i < k + 2 := (hwf m hm_lt).1.trans_le (by omega)
          have hmj : gs[m].j < k + 2 := (hwf m hm_lt).2.trans_le (by omega)
          rw [hg_eq, if_pos hmi, if_pos hmj, if_pos (by omega), wireVals_gate_wf hwf hm_lt]
        · have hm1 : m + 1 < gs.length := by omega
          have hd := hdead (m + 1) hm1 (by omega)
          have hg_eq : (deleteUnused gs k)[m] =
              ⟨(gs[m + 1]'hm1).op, shiftDown k (gs[m + 1]'hm1).i, shiftDown k (gs[m + 1]'hm1).j⟩ := by
            simp [deleteUnused, hmk]
          rw [hg_eq, shiftDown_inv hd.1, shiftDown_inv hd.2, if_neg (by omega),
            wireVals_gate_wf hwf hm1]

private lemma deleteUnused_output {gs : List GateSpec} (hwf : WellFormed gs)
    {k : ℕ} (hk : k + 1 < gs.length)
    (hdead : ∀ (k' : ℕ) (hk' : k' < gs.length), k < k' → gs[k'].i ≠ k + 2 ∧ gs[k'].j ≠ k + 2) :
    output (deleteUnused gs k) = output gs := by
  have hlen : (deleteUnused gs k).length = gs.length - 1 := deleteUnused_length gs k
  have h := deleteUnused_wireVals hwf hk hdead ((deleteUnused gs k).length + 1) (by omega)
  have hge : ¬ ((deleteUnused gs k).length + 1 < k + 2) := by omega
  have heq : (deleteUnused gs k).length + 1 + 1 = gs.length + 1 := by omega
  simpa [output, hge, heq] using h

/-- Sign tracking function for redirecting wire `k + 2` to `(m, flip)` (`m < k + 2`)
and deleting gate `k` (`k + 1 < gs.length`). Here `w` is the new wire index. -/
private def redirSign (gs : List GateSpec) (k m : ℕ) (flip : Bool) : ℕ → Bool
  | 0 => false
  | 1 => false
  | idx + 2 =>
      if hidx : idx < k then
        false
      else if hlen : idx + 1 < gs.length then
        let g := gs[idx + 1]'hlen
        let si : Bool :=
          if g.i < k + 2 then false
          else if g.i = k + 2 then flip
          else if g.i - 1 < idx + 2 then redirSign gs k m flip (g.i - 1)
          else false
        match g.op with
        | .mul =>
            let sj : Bool :=
              if g.j < k + 2 then false
              else if g.j = k + 2 then flip
              else if g.j - 1 < idx + 2 then redirSign gs k m flip (g.j - 1)
              else false
            xor si sj
        | .add | .sub => si
      else false
termination_by w => w
decreasing_by all_goals omega

private lemma redirSign_lt {gs : List GateSpec} {k m : ℕ} {flip : Bool}
    {w : ℕ} (hw : w < k + 2) : redirSign gs k m flip w = false := by
  rcases w with _ | _ | idx
  · simp [redirSign]
  · simp [redirSign]
  · unfold redirSign
    simp [show idx < k by omega]

private def redirOperand (gs : List GateSpec) (k m : ℕ) (flip : Bool) (u : ℕ) : ℕ × Bool :=
  if u < k + 2 then (u, false)
  else if u = k + 2 then (m, flip)
  else (u - 1, redirSign gs k m flip (u - 1))

private lemma redirOperand_idx_lt {k m idx u : ℕ} {gs : List GateSpec} {flip : Bool}
    (hk : k ≤ idx) (hm : m < k + 2) (hu : u < idx + 3) :
    (redirOperand gs k m flip u).1 < idx + 2 := by
  unfold redirOperand
  split_ifs <;> omega

private def redirGate (gs : List GateSpec) (k m : ℕ) (flip : Bool) : List GateSpec :=
  List.ofFn (fun idx : Fin (gs.length - 1) =>
    if idx.val < k then
      gs[idx.val]'(by omega)
    else
      let g := gs[idx.val + 1]'(by omega)
      let p₁ := redirOperand gs k m flip g.i
      let p₂ := redirOperand gs k m flip g.j
      let op' :=
        match g.op with
        | .mul => .mul
        | .add | .sub => if p₁.2 = p₂.2 then g.op else flipAddSub g.op
      ⟨op', p₁.1, p₂.1⟩)

private lemma redirGate_length (gs : List GateSpec) (k m : ℕ) (flip : Bool) :
    (redirGate gs k m flip).length = gs.length - 1 := by
  simp [redirGate]

private lemma redirGate_wellFormed {gs : List GateSpec} (hwf : WellFormed gs)
    {k m : ℕ} (hm : m < k + 2) (flip : Bool) :
    WellFormed (redirGate gs k m flip) := by
  intro idx hidx
  rw [redirGate_length] at hidx
  by_cases hk : idx < k
  · simp only [redirGate, List.getElem_ofFn, hk, ↓reduceIte]
    exact hwf idx (by omega)
  · simp only [redirGate, List.getElem_ofFn, hk, ↓reduceIte]
    have hidx1 : idx + 1 < gs.length := by omega
    have hg := hwf (idx + 1) hidx1
    exact ⟨redirOperand_idx_lt (by omega) hm hg.1, redirOperand_idx_lt (by omega) hm hg.2⟩

private lemma redirSign_succ_ge {gs : List GateSpec} (hwf : WellFormed gs)
    {k m idx : ℕ} (hk : k ≤ idx) (hidx1 : idx + 1 < gs.length) (flip : Bool) :
    let g := gs[idx + 1]'hidx1
    let p₁ := redirOperand gs k m flip g.i
    let p₂ := redirOperand gs k m flip g.j
    redirSign gs k m flip (idx + 2) =
      match g.op with
      | .mul => xor p₁.2 p₂.2
      | .add | .sub => p₁.2 := by
  intro g p₁ p₂
  have hgi : g.i - 1 < idx + 2 := by
    have := (hwf (idx + 1) hidx1).1
    dsimp only [g]
    omega
  have hgj : g.j - 1 < idx + 2 := by
    have := (hwf (idx + 1) hidx1).2
    dsimp only [g]
    omega
  conv_lhs => unfold redirSign
  rw [dif_neg (by omega), dif_pos hidx1]
  dsimp only [p₁, p₂, redirOperand, g] at hgi hgj ⊢
  cases (gs[idx + 1]'hidx1).op <;> simp only [hgi, hgj, ↓reduceIte] <;> split_ifs <;> rfl

private lemma redirGate_wireVals {gs : List GateSpec} (hwf : WellFormed gs)
    {k m : ℕ} (hk : k + 1 < gs.length) (hm : m < k + 2) (flip : Bool)
    (hdup : (wireVals gs).getD (k + 2) 0 = sgnVal flip * (wireVals gs).getD m 0) :
    ∀ (w : ℕ), w < (redirGate gs k m flip).length + 2 →
      (wireVals (redirGate gs k m flip)).getD w 0 =
        sgnVal (redirSign gs k m flip w) *
          (wireVals gs).getD (if w < k + 2 then w else w + 1) 0 := by
  have hwf' := redirGate_wellFormed hwf hm flip
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
      intro hw
      rcases w with _ | _ | idx
      · rw [if_pos (by omega), wireVals_zero, wireVals_zero]
        simp [redirSign, sgnVal]
      · change (wireVals (redirGate gs k m flip)).getD 1 0 =
          sgnVal (redirSign gs k m flip 1) * (wireVals gs).getD (if 1 < k + 2 then 1 else 1 + 1) 0
        rw [if_pos (by omega), wireVals_one, wireVals_one]
        simp [redirSign, sgnVal]
      · have hidx_len : idx < (redirGate gs k m flip).length := by omega
        have hidx1 : idx + 1 < gs.length := by
          rw [redirGate_length] at hidx_len
          omega
        rw [wireVals_gate_wf hwf' hidx_len]
        by_cases hlt : idx < k
        · have hidx_gs : idx < gs.length := by omega
          have hi : gs[idx].i < idx + 2 := (hwf idx hidx_gs).1
          have hj : gs[idx].j < idx + 2 := (hwf idx hidx_gs).2
          have hgi_k : gs[idx].i < k + 2 := by omega
          have hgj_k : gs[idx].j < k + 2 := by omega
          have hg_eq : (redirGate gs k m flip)[idx] = gs[idx] := by
            simp [redirGate, hlt]
          rw [hg_eq]
          have ihi := ih gs[idx].i hi (by omega)
          have ihj := ih gs[idx].j hj (by omega)
          rw [if_pos hgi_k, redirSign_lt hgi_k] at ihi
          rw [if_pos hgj_k, redirSign_lt hgj_k] at ihj
          rw [ihi, ihj, if_pos (show idx + 2 < k + 2 by omega),
            redirSign_lt (show idx + 2 < k + 2 by omega), wireVals_gate_wf hwf hidx_gs]
          simp [sgnVal]
        · have hk_le : k ≤ idx := by omega
          have hgi : gs[idx + 1].i < idx + 3 := (hwf (idx + 1) hidx1).1
          have hgj : gs[idx + 1].j < idx + 3 := (hwf (idx + 1) hidx1).2
          have hg_eq : (redirGate gs k m flip)[idx] =
              let g := gs[idx + 1]
              let p₁ := redirOperand gs k m flip g.i
              let p₂ := redirOperand gs k m flip g.j
              let op' :=
                match g.op with
                | .mul => .mul
                | .add | .sub => if p₁.2 = p₂.2 then g.op else flipAddSub g.op
              ⟨op', p₁.1, p₂.1⟩ := by
            simp [redirGate, hlt]
          have h_op : ∀ (u : ℕ), u < idx + 3 →
              (wireVals gs).getD u 0 =
                sgnVal (redirOperand gs k m flip u).2 *
                  (wireVals (redirGate gs k m flip)).getD (redirOperand gs k m flip u).1 0 := by
            intro u hu
            unfold redirOperand
            split_ifs with hu1 hu2
            · have ihu := ih u (by omega) (by omega)
              rw [if_pos hu1, redirSign_lt hu1] at ihu
              rw [ihu]
              simp [sgnVal]
            · subst hu2
              have ihm := ih m (by omega) (by omega)
              rw [if_pos hm, redirSign_lt hm] at ihm
              simp only [sgnVal, Bool.false_eq_true, ↓reduceIte, one_mul] at ihm
              rw [hdup, ihm]
            · have ihu := ih (u - 1) (by omega) (by omega)
              have hge : ¬ (u - 1 < k + 2) := by omega
              have hu_eq : u - 1 + 1 = u := by omega
              rw [if_neg hge, hu_eq] at ihu
              rw [ihu, ← mul_assoc, sgnVal_mul_self, one_mul]
          have h1 := h_op gs[idx + 1].i hgi
          have h2 := h_op gs[idx + 1].j hgj
          -- Since sgnVal s ∈ {1, -1}, multiply both sides by sgnVal s
          have h1' : (wireVals (redirGate gs k m flip)).getD (redirOperand gs k m flip gs[idx + 1].i).1 0 =
              sgnVal (redirOperand gs k m flip gs[idx + 1].i).2 * (wireVals gs).getD gs[idx + 1].i 0 := by
            rw [h1, ← mul_assoc, sgnVal_mul_self, one_mul]
          have h2' : (wireVals (redirGate gs k m flip)).getD (redirOperand gs k m flip gs[idx + 1].j).1 0 =
              sgnVal (redirOperand gs k m flip gs[idx + 1].j).2 * (wireVals gs).getD gs[idx + 1].j 0 := by
            rw [h2, ← mul_assoc, sgnVal_mul_self, one_mul]
          --Wait: express old = sgn * new, then compute new = sgn * old
          rw [hg_eq, if_neg (by omega)]
          have hs_eq := redirSign_succ_ge (m := m) hwf hk_le hidx1 flip
          dsimp only at hs_eq ⊢
          rw [hs_eq, wireVals_gate_wf hwf hidx1, h1, h2]
          -- Now simplify the goal: both sides are op' (new1) (new2) vs sgnVal (new_s) * op (sgn1 * new1) (sgn2 * new2)
          set a := (wireVals (redirGate gs k m flip)).getD (redirOperand gs k m flip gs[idx + 1].i).1 0
          set b := (wireVals (redirGate gs k m flip)).getD (redirOperand gs k m flip gs[idx + 1].j).1 0
          set s₁ := (redirOperand gs k m flip gs[idx + 1].i).2
          set s₂ := (redirOperand gs k m flip gs[idx + 1].j).2
          cases hop : gs[idx + 1].op <;> cases s₁ <;> cases s₂ <;>
            simp [sgnVal, flipAddSub, SLPOp.applyPoly] <;> ring

private lemma redirGate_computesSigned {f : Polynomial ℤ} {gs : List GateSpec}
    (hwf : WellFormed gs) (hcomp : ComputesSigned f gs)
    {k m : ℕ} (hk : k + 1 < gs.length) (hm : m < k + 2) (flip : Bool)
    (hdup : (wireVals gs).getD (k + 2) 0 = sgnVal flip * (wireVals gs).getD m 0) :
    ComputesSigned f (redirGate gs k m flip) := by
  have hlen := redirGate_length gs k m flip
  have h := redirGate_wireVals hwf hk hm flip hdup ((redirGate gs k m flip).length + 1) (by omega)
  have hge : ¬ ((redirGate gs k m flip).length + 1 < k + 2) := by omega
  have heq : (redirGate gs k m flip).length + 1 + 1 = gs.length + 1 := by omega
  rw [if_neg hge, heq] at h
  change output (redirGate gs k m flip) =
      sgnVal (redirSign gs k m flip ((redirGate gs k m flip).length + 1)) * output gs at h
  rcases hcomp with hcomp | hcomp <;>
    cases hs : redirSign gs k m flip ((redirGate gs k m flip).length + 1) <;>
    simp [ComputesSigned, h, hs, sgnVal, hcomp]

/-- Sign tracking function for `ordNormalize`. `normSign gs w` is `true` iff
normalized wire `w` holds `- (wireVals gs)[w]`. -/
private def normSign (gs : List GateSpec) : ℕ → Bool
  | 0 => false
  | 1 => false
  | k + 2 =>
      if hk : k < gs.length then
        let g := gs[k]'hk
        let s₁ := if g.i < k + 2 then normSign gs g.i else false
        let s₂ := if g.j < k + 2 then normSign gs g.j else false
        match g.op with
        | .mul => xor s₁ s₂
        | .add | .sub =>
            let op₁ := if s₁ = s₂ then g.op else flipAddSub g.op
            if op₁ = .sub ∧ g.j < g.i then !s₁ else s₁
      else false
termination_by w => w
decreasing_by all_goals omega

private def normGate (g : GateSpec) (s₁ s₂ : Bool) : GateSpec :=
  match g.op with
  | .mul => ⟨.mul, min g.i g.j, max g.i g.j⟩
  | .add | .sub =>
      let op₁ := if s₁ = s₂ then g.op else flipAddSub g.op
      match op₁ with
      | .add => ⟨.add, min g.i g.j, max g.i g.j⟩
      | .sub => if g.i ≤ g.j then ⟨.sub, g.i, g.j⟩ else ⟨.sub, g.j, g.i⟩
      | .mul => ⟨.mul, min g.i g.j, max g.i g.j⟩

private def ordNormalize (gs : List GateSpec) : List GateSpec :=
  List.ofFn (fun k : Fin gs.length =>
    let g := gs[k.val]
    normGate g (normSign gs g.i) (normSign gs g.j))

private lemma ordNormalize_length (gs : List GateSpec) :
    (ordNormalize gs).length = gs.length := by
  simp [ordNormalize]

private lemma normGate_operands (g : GateSpec) (s₁ s₂ : Bool) :
    ((normGate g s₁ s₂).i = g.i ∧ (normGate g s₁ s₂).j = g.j) ∨
    ((normGate g s₁ s₂).i = g.j ∧ (normGate g s₁ s₂).j = g.i) := by
  have hminmax : (min g.i g.j = g.i ∧ max g.i g.j = g.j) ∨
      (min g.i g.j = g.j ∧ max g.i g.j = g.i) := by
    by_cases h : g.i ≤ g.j
    · exact Or.inl ⟨min_eq_left h, max_eq_right h⟩
    · exact Or.inr ⟨min_eq_right (Nat.le_of_not_ge h), max_eq_left (Nat.le_of_not_ge h)⟩
  cases hop : g.op <;> cases s₁ <;> cases s₂ <;>
    simp only [normGate, hop, flipAddSub, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
  all_goals first
    | exact hminmax
    | (by_cases hij : g.i ≤ g.j
       · simp [hij]
       · simp [hij])

private lemma ordNormalize_wellFormed {gs : List GateSpec} (hwf : WellFormed gs) :
    WellFormed (ordNormalize gs) := by
  intro k hk
  rw [ordNormalize_length] at hk
  have hg := hwf k hk
  simp only [ordNormalize, List.getElem_ofFn]
  rcases normGate_operands gs[k] (normSign gs gs[k].i) (normSign gs gs[k].j) with ⟨hi, hj⟩ | ⟨hi, hj⟩
  · rw [hi, hj]; exact hg
  · rw [hi, hj]; exact ⟨hg.2, hg.1⟩

private lemma normGate_ord {g : GateSpec} {s₁ s₂ : Bool}
    (hne : ¬ ((if s₁ = s₂ then g.op else flipAddSub g.op) = .sub ∧ g.i = g.j)) :
    (normGate g s₁ s₂).Ord := by
  have hmm : min g.i g.j ≤ max g.i g.j := le_trans (min_le_left _ _) (le_max_left _ _)
  have hne' : (if s₁ = s₂ then g.op else flipAddSub g.op) = .sub → g.i ≠ g.j :=
    fun h1 h2 => hne ⟨h1, h2⟩
  cases hop : g.op <;> cases s₁ <;> cases s₂ <;>
    simp only [normGate, hop, flipAddSub, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte] at hne' ⊢
  all_goals first
    | exact hmm
    | (by_cases hij : g.i ≤ g.j
       · simp only [hij, ↓reduceIte, GateSpec.Ord]
         have : g.i ≠ g.j := hne' trivial
         omega
       · simp only [hij, ↓reduceIte, GateSpec.Ord]
         omega)

private lemma normGate_wire_eq {g : GateSpec} {s₁ s₂ : Bool}
    (hneq : ¬ ((if s₁ = s₂ then g.op else flipAddSub g.op) = .sub ∧ g.i = g.j))
    (new_i new_j : Polynomial ℤ) (heq : g.i = g.j → new_i = new_j) :
    let out_s :=
      match g.op with
      | .mul => xor s₁ s₂
      | .add | .sub =>
          let op₁ := if s₁ = s₂ then g.op else flipAddSub g.op
          if op₁ = .sub ∧ g.j < g.i then !s₁ else s₁
    let g' := normGate g s₁ s₂
    g'.op.applyPoly (if g'.i = g.i then new_i else new_j) (if g'.j = g.i then new_i else new_j) =
      sgnVal out_s * g.op.applyPoly (sgnVal s₁ * new_i) (sgnVal s₂ * new_j) := by
  by_cases hij_eq : g.i = g.j
  · have hnew : new_i = new_j := heq hij_eq
    subst hnew
    cases hop : g.op <;> cases s₁ <;> cases s₂ <;>
      simp [normGate, flipAddSub, SLPOp.applyPoly, sgnVal, hop, hij_eq] at hneq ⊢ <;> ring
  · by_cases hij : g.i ≤ g.j
    · have hlt : g.i < g.j := by omega
      have hnot_ji : ¬ (g.j < g.i) := by omega
      have hne_ji : g.j ≠ g.i := by omega
      cases hop : g.op <;> cases s₁ <;> cases s₂ <;>
        simp [normGate, flipAddSub, SLPOp.applyPoly, sgnVal, hop, hij, hnot_ji, hne_ji,
          min_eq_left hij, max_eq_right hij] <;> ring
    · have hlt : g.j < g.i := by omega
      have hji : g.j ≤ g.i := by omega
      have hne_ji : g.j ≠ g.i := by omega
      cases hop : g.op <;> cases s₁ <;> cases s₂ <;>
        simp [normGate, flipAddSub, SLPOp.applyPoly, sgnVal, hop, hij, hlt, hne_ji,
          min_eq_right hji, max_eq_left hji] <;> ring

private lemma ordNormalize_wireVals_and_ord {gs : List GateSpec}
    (hwf : WellFormed gs) (hnz : NonzeroWires gs) :
    (∀ (w : ℕ), w < gs.length + 2 →
      (wireVals (ordNormalize gs)).getD w 0 = sgnVal (normSign gs w) * (wireVals gs).getD w 0) ∧
    OrdCanonical (ordNormalize gs) := by
  -- Prove simultaneously by induction on w (and k for OrdCanonical)
  have hmain : ∀ (w : ℕ), w < gs.length + 2 →
      (wireVals (ordNormalize gs)).getD w 0 = sgnVal (normSign gs w) * (wireVals gs).getD w 0 := by
    intro w
    induction w using Nat.strongRecOn with
    | ind w ih =>
        intro hw
        rcases w with _ | _ | k
        · rw [wireVals_zero, wireVals_zero]; simp [normSign, sgnVal]
        · change (wireVals (ordNormalize gs)).getD 1 0 =
            sgnVal (normSign gs 1) * (wireVals gs).getD 1 0
          rw [wireVals_one, wireVals_one]; simp [normSign, sgnVal]
        · have hk : k < gs.length := by omega
          have hk' : k < (ordNormalize gs).length := by rwa [ordNormalize_length]
          have hwf' := ordNormalize_wellFormed hwf
          have hgi : gs[k].i < k + 2 := (hwf k hk).1
          have hgj : gs[k].j < k + 2 := (hwf k hk).2
          have h_old := wireVals_gate_wf hwf hk
          have h_new := wireVals_gate_wf hwf' hk'
          have h_neq : ¬ ((if normSign gs gs[k].i = normSign gs gs[k].j then gs[k].op
              else flipAddSub gs[k].op) = .sub ∧ gs[k].i = gs[k].j) := by
            intro ⟨hop_sub, hij⟩
            rw [hij, if_pos rfl] at hop_sub
            have h0 : (wireVals gs).getD (k + 2) 0 = 0 := by
              rw [h_old, hij, hop_sub]
              simp [SLPOp.applyPoly]
            exact hnz k hk h0
          have ihi_old := ih gs[k].i hgi (by omega)
          have ihj_old := ih gs[k].j hgj (by omega)
          have h_ng : (ordNormalize gs)[k] =
              normGate gs[k] (normSign gs gs[k].i) (normSign gs gs[k].j) := by
            simp [ordNormalize]
          have h_normSign_k : normSign gs (k + 2) =
              match gs[k].op with
              | .mul => xor (normSign gs gs[k].i) (normSign gs gs[k].j)
              | .add | .sub =>
                  let op₁ := if normSign gs gs[k].i = normSign gs gs[k].j then gs[k].op
                             else flipAddSub gs[k].op
                  if op₁ = .sub ∧ gs[k].j < gs[k].i then !(normSign gs gs[k].i)
                  else normSign gs gs[k].i := by
            conv_lhs => unfold normSign
            simp [hk, hgi, hgj]
          set g := gs[k]
          set s₁ := normSign gs g.i
          set s₂ := normSign gs g.j
          set g' := normGate g s₁ s₂
          have h_mem_i : g'.i = g.i ∨ g'.i = g.j := by
            rcases normGate_operands g s₁ s₂ with ⟨h1, _⟩ | ⟨h1, _⟩
            · exact Or.inl h1
            · exact Or.inr h1
          have h_mem_j : g'.j = g.i ∨ g'.j = g.j := by
            rcases normGate_operands g s₁ s₂ with ⟨_, h2⟩ | ⟨_, h2⟩
            · exact Or.inr h2
            · exact Or.inl h2
          have h_new_i_old : (wireVals (ordNormalize gs)).getD g'.i 0 =
              if g'.i = g.i then (wireVals (ordNormalize gs)).getD g.i 0
              else (wireVals (ordNormalize gs)).getD g.j 0 := by
            rcases h_mem_i with h | h <;> split_ifs with h1 <;> simp_all
          have h_new_j_old : (wireVals (ordNormalize gs)).getD g'.j 0 =
              if g'.j = g.i then (wireVals (ordNormalize gs)).getD g.i 0
              else (wireVals (ordNormalize gs)).getD g.j 0 := by
            rcases h_mem_j with h | h <;> split_ifs with h1 <;> simp_all
          rw [h_new, h_ng]
          change g'.op.applyPoly ((wireVals (ordNormalize gs)).getD g'.i 0)
              ((wireVals (ordNormalize gs)).getD g'.j 0) =
            sgnVal (normSign gs (k + 2)) * (wireVals gs).getD (k + 2) 0
          rw [h_new_i_old, h_new_j_old]
          have hlem := normGate_wire_eq h_neq
            ((wireVals (ordNormalize gs)).getD g.i 0)
            ((wireVals (ordNormalize gs)).getD g.j 0)
            (fun hij => by rw [hij])
          dsimp only at hlem
          rw [hlem, ← h_normSign_k, ihi_old, ihj_old, h_old]
          have h_old_i : sgnVal s₁ * (sgnVal s₁ * (wireVals gs).getD g.i 0) =
              (wireVals gs).getD g.i 0 := by
            rw [← mul_assoc, sgnVal_mul_self, one_mul]
          have h_old_j : sgnVal s₂ * (sgnVal s₂ * (wireVals gs).getD g.j 0) =
              (wireVals gs).getD g.j 0 := by
            rw [← mul_assoc, sgnVal_mul_self, one_mul]
          change sgnVal (normSign gs (k + 2)) *
              g.op.applyPoly (sgnVal s₁ * (sgnVal s₁ * (wireVals gs).getD g.i 0))
                (sgnVal s₂ * (sgnVal s₂ * (wireVals gs).getD g.j 0)) =
            sgnVal (normSign gs (k + 2)) * g.op.applyPoly ((wireVals gs).getD g.i 0) ((wireVals gs).getD g.j 0)
          rw [h_old_i, h_old_j]
  refine ⟨hmain, ?_⟩
  intro k hk
  rw [ordNormalize_length] at hk
  simp only [ordNormalize, List.getElem_ofFn]
  apply normGate_ord
  intro ⟨hop_sub, hij⟩
  rw [hij, if_pos rfl] at hop_sub
  have h0 : (wireVals gs).getD (k + 2) 0 = 0 := by
    rw [wireVals_gate_wf hwf hk, hij, hop_sub]
    simp [SLPOp.applyPoly]
  exact hnz k hk h0

private lemma ordNormalize_preserves_nonzero {gs : List GateSpec}
    (hwf : WellFormed gs) (hnz : NonzeroWires gs) :
    NonzeroWires (ordNormalize gs) := by
  intro k hk
  rw [ordNormalize_length] at hk
  rw [(ordNormalize_wireVals_and_ord hwf hnz).1 (k + 2) (by omega)]
  exact mul_ne_zero (sgnVal_ne_zero _) (hnz k hk)

private lemma ordNormalize_preserves_nodup {gs : List GateSpec}
    (hwf : WellFormed gs) (hnz : NonzeroWires gs) (hnodup : NodupWires gs) :
    NodupWires (ordNormalize gs) := by
  intro k hk m hm
  rw [ordNormalize_length] at hk
  have hvals := (ordNormalize_wireVals_and_ord hwf hnz).1
  rw [hvals (k + 2) (by omega), hvals m (by omega)]
  have hnd := hnodup k hk m hm
  cases hs1 : normSign gs (k + 2) <;> cases hs2 : normSign gs m <;> simp [sgnVal]
  · exact hnd
  · exact ⟨hnd.2, hnd.1⟩
  · exact ⟨fun h => hnd.2 (neg_eq_iff_eq_neg.mp h), fun h => hnd.1 h⟩
  · exact ⟨fun h => hnd.1 h, fun h => hnd.2 (neg_eq_iff_eq_neg.mp h)⟩

private lemma ordNormalize_preserves_used {gs : List GateSpec}
    (hused : UsedGates gs) : UsedGates (ordNormalize gs) := by
  intro k hk
  rw [ordNormalize_length] at hk
  rcases hused k hk with ⟨k', hk', hkk', hor⟩
  refine ⟨k', by rwa [ordNormalize_length], hkk', ?_⟩
  simp only [ordNormalize, List.getElem_ofFn]
  rcases normGate_operands gs[k'] (normSign gs gs[k'].i) (normSign gs gs[k'].j) with
    ⟨hi, hj⟩ | ⟨hi, hj⟩
  · rw [hi, hj]; exact hor
  · rw [hi, hj]; exact hor.symm

private lemma ordNormalize_computesSigned {f : Polynomial ℤ} {gs : List GateSpec}
    (hwf : WellFormed gs) (hnz : NonzeroWires gs) (hcomp : ComputesSigned f gs) :
    ComputesSigned f (ordNormalize gs) := by
  have h := (ordNormalize_wireVals_and_ord hwf hnz).1 (gs.length + 1) (by omega)
  have hlen := ordNormalize_length gs
  have hout : output (ordNormalize gs) = sgnVal (normSign gs (gs.length + 1)) * output gs := by
    simpa [output, hlen] using h
  rcases hcomp with hcomp | hcomp <;>
    cases hs : normSign gs (gs.length + 1) <;>
    simp [ComputesSigned, hout, hs, sgnVal, hcomp]

private lemma normSign_false_of_ord_prefix {gs : List GateSpec} (hwf : WellFormed gs)
    {p : ℕ} (hp : p ≤ gs.length)
    (hord : ∀ (m : ℕ) (hm : m < p), (gs[m]'(by omega)).Ord) :
    ∀ (w : ℕ), w < p + 2 → normSign gs w = false := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
      intro hw
      rcases w with _ | _ | m
      · simp [normSign]
      · simp [normSign]
      · have hm : m < p := by omega
        have hm_gs : m < gs.length := by omega
        have hgi : gs[m].i < m + 2 := (hwf m hm_gs).1
        have hgj : gs[m].j < m + 2 := (hwf m hm_gs).2
        have si_f : normSign gs gs[m].i = false := ih gs[m].i hgi (by omega)
        have sj_f : normSign gs gs[m].j = false := ih gs[m].j hgj (by omega)
        have hm_ord := hord m hm
        conv_lhs => unfold normSign
        simp only [hm_gs, ↓reduceDIte, hgi, hgj, si_f, sj_f]
        cases hop : gs[m].op <;> simp [GateSpec.Ord, hop] at hm_ord ⊢
        omega

private lemma ordNormalize_prefix_eq {gs : List GateSpec} (hwf : WellFormed gs)
    {p : ℕ} (hp : p ≤ gs.length)
    (hord : ∀ (m : ℕ) (hm : m < p), (gs[m]'(by omega)).Ord) :
    ∀ (m : ℕ) (hm : m < p), (ordNormalize gs)[m]'(by rw [ordNormalize_length]; omega) = gs[m]'(by omega) := by
  intro m hm
  have hm_gs : m < gs.length := by omega
  have hgi : gs[m].i < m + 2 := (hwf m hm_gs).1
  have hgj : gs[m].j < m + 2 := (hwf m hm_gs).2
  have si_f : normSign gs gs[m].i = false := normSign_false_of_ord_prefix hwf hp hord gs[m].i (by omega)
  have sj_f : normSign gs gs[m].j = false := normSign_false_of_ord_prefix hwf hp hord gs[m].j (by omega)
  have hm_ord := hord m hm
  simp only [ordNormalize, List.getElem_ofFn, si_f, sj_f]
  rcases hg : gs[m] with ⟨op, i, j⟩
  rw [hg] at hm_ord
  cases op <;> simp only [normGate, ↓reduceIte, GateSpec.Ord] at hm_ord ⊢
  · simp [min_eq_left hm_ord, max_eq_right hm_ord]
  · simp [hm_ord.le]
  · simp [min_eq_left hm_ord, max_eq_right hm_ord]

/-- Swap wires `a` and `b`, fixing all other indices. -/
private def swapIdx (a b x : ℕ) : ℕ :=
  if x = a then b else if x = b then a else x

private lemma swapIdx_invol (a b x : ℕ) : swapIdx a b (swapIdx a b x) = x := by
  unfold swapIdx
  split_ifs <;> omega

private lemma swapIdx_lt {a b m x : ℕ} (ha : a < m) (hb : b < m) (hx : x < m) :
    swapIdx a b x < m := by
  unfold swapIdx
  split_ifs <;> omega

private lemma swapIdx_lt_of_lt {a b x : ℕ} (hx1 : x < a) (hx2 : x < b) :
    swapIdx a b x = x := by
  unfold swapIdx
  split_ifs <;> omega

/-- Swap independent adjacent gates `k - 1` and `k` (`1 ≤ k`, `k + 1 < gs.length`)
and swap wire references `k + 1 ↔ k + 2` in all gates `> k`. -/
private def swapRaw (gs : List GateSpec) (k : ℕ) : List GateSpec :=
  List.ofFn (fun m : Fin gs.length =>
    if m.val = k - 1 then
      gs[k]!
    else if m.val = k then
      gs[k - 1]!
    else if m.val < k - 1 then
      gs[m.val]
    else
      let g := gs[m.val]
      ⟨g.op, swapIdx (k + 1) (k + 2) g.i, swapIdx (k + 1) (k + 2) g.j⟩)

private lemma swapRaw_length (gs : List GateSpec) (k : ℕ) :
    (swapRaw gs k).length = gs.length := by
  simp [swapRaw]

private lemma swapRaw_wellFormed {gs : List GateSpec} (hwf : WellFormed gs)
    {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k + 1 < gs.length)
    (hind_i : gs[k].i ≠ k + 1) (hind_j : gs[k].j ≠ k + 1) :
    WellFormed (swapRaw gs k) := by
  intro m hm
  rw [swapRaw_length] at hm
  simp only [swapRaw, List.getElem_ofFn]
  split_ifs with h1 h2 h3
  · have hgk := hwf k (by omega)
    have heq : gs[k]! = gs[k] := by simp [show k < gs.length by omega]
    rw [heq]
    omega
  · have hgk1 := hwf (k - 1) (by omega)
    have heq : gs[k - 1]! = gs[k - 1] := by simp [show k - 1 < gs.length by omega]
    rw [heq]
    omega
  · exact hwf m hm
  · have hgm := hwf m hm
    have hk_lt : k + 1 < m + 2 := by omega
    have hk2_lt : k + 2 < m + 2 := by omega
    exact ⟨swapIdx_lt hk_lt hk2_lt hgm.1, swapIdx_lt hk_lt hk2_lt hgm.2⟩

private lemma swapRaw_wireVals {gs : List GateSpec} (hwf : WellFormed gs)
    {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k + 1 < gs.length)
    (hind_i : gs[k].i ≠ k + 1) (hind_j : gs[k].j ≠ k + 1) :
    ∀ (w : ℕ), w < gs.length + 2 →
      (wireVals (swapRaw gs k)).getD w 0 = (wireVals gs).getD (swapIdx (k + 1) (k + 2) w) 0 := by
  have hwf' := swapRaw_wellFormed hwf hk1 hk2 hind_i hind_j
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
      intro hw
      rcases w with _ | _ | m
      · have h0 : swapIdx (k + 1) (k + 2) 0 = 0 := swapIdx_lt_of_lt (by omega) (by omega)
        rw [h0, wireVals_zero, wireVals_zero]
      · have h1 : swapIdx (k + 1) (k + 2) 1 = 1 := swapIdx_lt_of_lt (by omega) (by omega)
        change (wireVals (swapRaw gs k)).getD 1 0 = (wireVals gs).getD (swapIdx (k + 1) (k + 2) 1) 0
        rw [h1, wireVals_one, wireVals_one]
      · have hm : m < gs.length := by omega
        have hm' : m < (swapRaw gs k).length := by rwa [swapRaw_length]
        rw [wireVals_gate_wf hwf' hm']
        have hi' := (hwf' m hm').1
        have hj' := (hwf' m hm').2
        rw [ih _ hi' (by omega), ih _ hj' (by omega)]
        simp only [swapRaw, List.getElem_ofFn]
        split_ifs with h1 h2 h3
        · have heq : gs[k]! = gs[k] := by simp [show k < gs.length by omega]
          rw [heq]
          have hgk := hwf k (by omega)
          have hsi : swapIdx (k + 1) (k + 2) gs[k].i = gs[k].i :=
            swapIdx_lt_of_lt (by omega) (by omega)
          have hsj : swapIdx (k + 1) (k + 2) gs[k].j = gs[k].j :=
            swapIdx_lt_of_lt (by omega) (by omega)
          have hsw : swapIdx (k + 1) (k + 2) (m + 2) = k + 2 := by
            unfold swapIdx; split_ifs <;> omega
          rw [hsi, hsj, hsw, ← wireVals_gate_wf hwf (show k < gs.length by omega)]
        · have heq : gs[k - 1]! = gs[k - 1] := by simp [show k - 1 < gs.length by omega]
          rw [heq]
          have hgk1 := hwf (k - 1) (by omega)
          have hsi : swapIdx (k + 1) (k + 2) gs[k - 1].i = gs[k - 1].i :=
            swapIdx_lt_of_lt (by omega) (by omega)
          have hsj : swapIdx (k + 1) (k + 2) gs[k - 1].j = gs[k - 1].j :=
            swapIdx_lt_of_lt (by omega) (by omega)
          have hsw : swapIdx (k + 1) (k + 2) (m + 2) = k + 1 := by
            unfold swapIdx; split_ifs <;> omega
          have hk1_eq : (k - 1) + 2 = k + 1 := by omega
          rw [hsi, hsj, hsw, ← hk1_eq, ← wireVals_gate_wf hwf (show k - 1 < gs.length by omega)]
        · have hgm := hwf m hm
          have hsi : swapIdx (k + 1) (k + 2) gs[m].i = gs[m].i :=
            swapIdx_lt_of_lt (by omega) (by omega)
          have hsj : swapIdx (k + 1) (k + 2) gs[m].j = gs[m].j :=
            swapIdx_lt_of_lt (by omega) (by omega)
          have hsw : swapIdx (k + 1) (k + 2) (m + 2) = m + 2 :=
            swapIdx_lt_of_lt (by omega) (by omega)
          rw [hsi, hsj, hsw, ← wireVals_gate_wf hwf hm]
        · dsimp only
          rw [swapIdx_invol, swapIdx_invol]
          have hsw : swapIdx (k + 1) (k + 2) (m + 2) = m + 2 := by
            unfold swapIdx; split_ifs <;> omega
          rw [hsw, ← wireVals_gate_wf hwf hm]

private lemma swapRaw_preserves_nonzero {gs : List GateSpec} (hwf : WellFormed gs)
    (hnz : NonzeroWires gs) {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k + 1 < gs.length)
    (hind_i : gs[k].i ≠ k + 1) (hind_j : gs[k].j ≠ k + 1) :
    NonzeroWires (swapRaw gs k) := by
  intro m hm
  rw [swapRaw_length] at hm
  rw [swapRaw_wireVals hwf hk1 hk2 hind_i hind_j (m + 2) (by omega)]
  have hlt : swapIdx (k + 1) (k + 2) (m + 2) < gs.length + 2 :=
    swapIdx_lt (by omega) (by omega) (by omega)
  have hge2 : 2 ≤ swapIdx (k + 1) (k + 2) (m + 2) := by
    unfold swapIdx; split_ifs <;> omega
  have heq : swapIdx (k + 1) (k + 2) (m + 2) = (swapIdx (k + 1) (k + 2) (m + 2) - 2) + 2 := by omega
  rw [heq]
  exact hnz _ (by omega)

private lemma swapRaw_preserves_nodup {gs : List GateSpec} (hwf : WellFormed gs)
    (hnodup : NodupWires gs) {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k + 1 < gs.length)
    (hind_i : gs[k].i ≠ k + 1) (hind_j : gs[k].j ≠ k + 1) :
    NodupWires (swapRaw gs k) := by
  intro m hm u hu
  rw [swapRaw_length] at hm
  have hw := swapRaw_wireVals hwf hk1 hk2 hind_i hind_j
  rw [hw (m + 2) (by omega), hw u (by omega)]
  by_cases hmk : m = k
  · -- new wire k+2 holds old wire k+1; u < k+2 => either u < k+1 or u = k+1 (holds old k+2)
    subst m
    have hsw1 : swapIdx (k + 1) (k + 2) (k + 2) = k + 1 := by unfold swapIdx; split_ifs <;> omega
    rw [hsw1]
    by_cases huk : u = k + 1
    · subst u
      have hsw2 : swapIdx (k + 1) (k + 2) (k + 1) = k + 2 := by unfold swapIdx; split_ifs <;> omega
      rw [hsw2]
      have hnd := hnodup k (by omega) (k + 1) (by omega)
      constructor <;> intro h
      · exact hnd.1 h.symm
      · exact hnd.2 (neg_eq_iff_eq_neg.mp h.symm)
    · have hu_lt : u < k + 1 := by omega
      have hsw2 : swapIdx (k + 1) (k + 2) u = u := swapIdx_lt_of_lt hu_lt (by omega)
      rw [hsw2]
      have hk1_eq : (k - 1) + 2 = k + 1 := by omega
      rw [← hk1_eq]
      exact hnodup (k - 1) (by omega) u (by omega)
  · by_cases hmk1 : m = k - 1
    · -- new wire k+1 holds old wire k+2; u < k+1 => swapIdx u = u < k+2
      have hsw1 : swapIdx (k + 1) (k + 2) (m + 2) = k + 2 := by
        unfold swapIdx; split_ifs <;> omega
      have hsw2 : swapIdx (k + 1) (k + 2) u = u := swapIdx_lt_of_lt (by omega) (by omega)
      rw [hsw1, hsw2]
      exact hnodup k (by omega) u (by omega)
    · by_cases hlt : m < k - 1
      · have hsw1 : swapIdx (k + 1) (k + 2) (m + 2) = m + 2 :=
          swapIdx_lt_of_lt (by omega) (by omega)
        have hsw2 : swapIdx (k + 1) (k + 2) u = u :=
          swapIdx_lt_of_lt (by omega) (by omega)
        rw [hsw1, hsw2]
        exact hnodup m hm u hu
      · -- m > k, so m + 2 >= k + 3
        have hm_gt : k < m := by omega
        have hsw1 : swapIdx (k + 1) (k + 2) (m + 2) = m + 2 := by
          unfold swapIdx; split_ifs <;> omega
        have hu_lt : swapIdx (k + 1) (k + 2) u < m + 2 :=
          swapIdx_lt (by omega) (by omega) hu
        rw [hsw1]
        exact hnodup m hm _ hu_lt

private lemma swapRaw_preserves_used {gs : List GateSpec} (hused : UsedGates gs)
    {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k + 1 < gs.length)
    (hind_i : gs[k].i ≠ k + 1) (hind_j : gs[k].j ≠ k + 1) :
    UsedGates (swapRaw gs k) := by
  intro u hu
  rw [swapRaw_length] at hu
  have hlen : (swapRaw gs k).length = gs.length := swapRaw_length gs k
  by_cases huk : u = k
  · -- new wire k + 2 corresponds to old gate k - 1 (wire k + 1).
    -- Its user in gs cannot be gate k (by hind_i, hind_j), so it must be some m > k.
    subst u
    rcases hused (k - 1) (by omega) with ⟨m, hm, hkm, hor⟩
    have hm_gt : k < m := by
      by_contra hle
      have hmk : m = k := by omega
      subst m
      rcases hor with hi | hj
      · exact hind_i (by omega)
      · exact hind_j (by omega)
    refine ⟨m, by omega, hm_gt, ?_⟩
    simp only [swapRaw, List.getElem_ofFn]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    have hsw : swapIdx (k + 1) (k + 2) (k + 1) = k + 2 := by unfold swapIdx; split_ifs <;> omega
    rcases hor with hi | hj
    · left; dsimp; rw [show (k - 1) + 2 = k + 1 by omega] at hi; rw [hi, hsw]
    · right; dsimp; rw [show (k - 1) + 2 = k + 1 by omega] at hj; rw [hj, hsw]
  · by_cases huk1 : u = k - 1
    · -- new wire k + 1 corresponds to old gate k (wire k + 2); since k + 1 < gs.length, used by m > k
      rcases hused k hk2 with ⟨m, hm, hkm, hor⟩
      refine ⟨m, by omega, by omega, ?_⟩
      simp only [swapRaw, List.getElem_ofFn]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      have hsw : swapIdx (k + 1) (k + 2) (k + 2) = k + 1 := by unfold swapIdx; split_ifs <;> omega
      have hu2 : u + 2 = k + 1 := by omega
      rw [hu2]
      rcases hor with hi | hj
      · left; dsimp; rw [hi, hsw]
      · right; dsimp; rw [hj, hsw]
    · by_cases hlt : u < k - 1
      · rcases hused u (by omega) with ⟨m, hm, hum, hor⟩
        by_cases hmk : m = k
        · subst m
          refine ⟨k - 1, by omega, by omega, ?_⟩
          have hget : (swapRaw gs k)[k - 1]'(by omega) = gs[k]'(by omega) := by
            simp [swapRaw, show k < gs.length by omega]
          rw [hget]; exact hor
        · by_cases hmk1 : m = k - 1
          · refine ⟨k, by omega, by omega, ?_⟩
            have hne : k ≠ k - 1 := by omega
            have hget : (swapRaw gs k)[k]'(by omega) = gs[k - 1]'(by omega) := by
              simp [swapRaw, hne, show k - 1 < gs.length by omega]
            rw [hget]
            subst m
            exact hor
          · by_cases hm_lt : m < k - 1
            · refine ⟨m, by omega, hum, ?_⟩
              have hget : (swapRaw gs k)[m]'(by omega) = gs[m]'(by omega) := by
                simp [swapRaw, show m ≠ k - 1 by omega, show m ≠ k by omega, hm_lt]
              rw [hget]
              exact hor
            · have hm_gt : k < m := by omega
              refine ⟨m, by omega, hum, ?_⟩
              have hget : (swapRaw gs k)[m]'(by omega) =
                  ⟨gs[m].op, swapIdx (k + 1) (k + 2) gs[m].i, swapIdx (k + 1) (k + 2) gs[m].j⟩ := by
                simp [swapRaw, show m ≠ k - 1 by omega, show m ≠ k by omega, hm_lt]
              rw [hget]
              have hsw : swapIdx (k + 1) (k + 2) (u + 2) = u + 2 := swapIdx_lt_of_lt (by omega) (by omega)
              rcases hor with hi | hj
              · left; rw [hi, hsw]
              · right; rw [hj, hsw]
      · -- u > k
        have hu_gt : k < u := by omega
        rcases hused u hu with ⟨m, hm, hum, hor⟩
        refine ⟨m, by omega, hum, ?_⟩
        have hget : (swapRaw gs k)[m]'(by omega) =
            ⟨gs[m].op, swapIdx (k + 1) (k + 2) gs[m].i, swapIdx (k + 1) (k + 2) gs[m].j⟩ := by
          simp [swapRaw, show m ≠ k - 1 by omega, show m ≠ k by omega, show ¬ m < k - 1 by omega]
        rw [hget]
        have hsw : swapIdx (k + 1) (k + 2) (u + 2) = u + 2 := by
          unfold swapIdx; split_ifs <;> omega
        rcases hor with hi | hj
        · left; rw [hi, hsw]
        · right; rw [hj, hsw]

private lemma swapRaw_computesSigned {f : Polynomial ℤ} {gs : List GateSpec}
    (hwf : WellFormed gs) (hcomp : ComputesSigned f gs)
    {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k + 1 < gs.length)
    (hind_i : gs[k].i ≠ k + 1) (hind_j : gs[k].j ≠ k + 1) :
    ComputesSigned f (swapRaw gs k) := by
  have h := swapRaw_wireVals hwf hk1 hk2 hind_i hind_j (gs.length + 1) (by omega)
  have hsw : swapIdx (k + 1) (k + 2) (gs.length + 1) = gs.length + 1 := by
    unfold swapIdx; split_ifs <;> omega
  rw [hsw] at h
  have hout : output (swapRaw gs k) = output gs := by
    simpa [output, swapRaw_length] using h
  simpa [ComputesSigned, hout] using hcomp

private lemma swapRaw_ord_prefix {gs : List GateSpec} (hord : OrdCanonical gs)
    {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k + 1 < gs.length) :
    ∀ (m : ℕ) (hm : m < k + 1),
      ((swapRaw gs k)[m]'(by rw [swapRaw_length]; omega)).Ord := by
  intro m hm
  simp only [swapRaw, List.getElem_ofFn]
  split_ifs with h1 h2 h3
  · have heq : gs[k]! = gs[k] := by simp [show k < gs.length by omega]
    rw [heq]; exact hord k (by omega)
  · have heq : gs[k - 1]! = gs[k - 1] := by simp [show k - 1 < gs.length by omega]
    rw [heq]; exact hord (k - 1) (by omega)
  · exact hord m (by omega)
  · omega

/-! ### Weight Function for Lexicographic Minimization at Fixed Length -/

private def keyCode (M : ℕ) (g : GateSpec) : ℕ :=
  g.op.idx * M * M + g.i * M + g.j

private lemma keyCode_lt {M : ℕ} {g : GateSpec} (hi : g.i < M) (hj : g.j < M) :
    keyCode M g < 3 * M * M := by
  unfold keyCode
  have hop : g.op.idx ≤ 2 := by cases g.op <;> simp [SLPOp.idx]
  have h1 : g.i * M + g.j < M * M := by
    calc
      g.i * M + g.j < g.i * M + M := Nat.add_lt_add_left hj _
      _ = (g.i + 1) * M := by ring
      _ ≤ M * M := Nat.mul_le_mul_right M hi
  have h2 : g.op.idx * M * M ≤ 2 * M * M :=
    Nat.mul_le_mul_right M (Nat.mul_le_mul_right M hop)
  calc
    g.op.idx * M * M + g.i * M + g.j = g.op.idx * M * M + (g.i * M + g.j) := by ring
    _ < 2 * M * M + M * M := Nat.add_lt_add_of_le_of_lt h2 h1
    _ = 3 * M * M := by ring

private lemma keyCode_lt_iff {M : ℕ} {g₁ g₂ : GateSpec}
    (hi₁ : g₁.i < M) (hj₁ : g₁.j < M) (hi₂ : g₂.i < M) (hj₂ : g₂.j < M) :
    keyCode M g₁ < keyCode M g₂ ↔ g₁.keyLt g₂ := by
  unfold keyCode GateSpec.keyLt
  have htail : ∀ a b : ℕ, a < M → b < M → a * M + b < M * M := fun a b ha hb => by
    calc
      a * M + b < a * M + M := Nat.add_lt_add_left hb _
      _ = (a + 1) * M := by ring
      _ ≤ M * M := Nat.mul_le_mul_right M ha
  constructor
  · intro h
    by_cases hop : g₁.op.idx < g₂.op.idx
    · exact Or.inl hop
    · by_cases hop2 : g₂.op.idx < g₁.op.idx
      · exfalso
        have h1 : g₂.op.idx * M * M + g₂.i * M + g₂.j < (g₂.op.idx + 1) * M * M := by
          calc
            g₂.op.idx * M * M + g₂.i * M + g₂.j = g₂.op.idx * M * M + (g₂.i * M + g₂.j) := by ring
            _ < g₂.op.idx * M * M + M * M := Nat.add_lt_add_left (htail _ _ hi₂ hj₂) _
            _ = (g₂.op.idx + 1) * M * M := by ring
        have h2 : (g₂.op.idx + 1) * M * M ≤ g₁.op.idx * M * M :=
          Nat.mul_le_mul_right M (Nat.mul_le_mul_right M hop2)
        omega
      · have hop_eq : g₁.op.idx = g₂.op.idx := by omega
        right; refine ⟨hop_eq, ?_⟩
        rw [hop_eq] at h
        have h' : g₁.i * M + g₁.j < g₂.i * M + g₂.j := by omega
        by_cases hi : g₁.i < g₂.i
        · exact Or.inl hi
        · by_cases hi2 : g₂.i < g₁.i
          · exfalso
            have h1 : g₂.i * M + g₂.j < (g₂.i + 1) * M := by
              calc
                g₂.i * M + g₂.j < g₂.i * M + M := Nat.add_lt_add_left hj₂ _
                _ = (g₂.i + 1) * M := by ring
            have h2 : (g₂.i + 1) * M ≤ g₁.i * M := Nat.mul_le_mul_right M hi2
            omega
          · have hi_eq : g₁.i = g₂.i := by omega
            rw [hi_eq] at h'
            right; exact ⟨hi_eq, by omega⟩
  · intro h
    rcases h with hop | ⟨hop, hi | ⟨hi, hj⟩⟩
    · have h1 : g₁.op.idx * M * M + g₁.i * M + g₁.j < (g₁.op.idx + 1) * M * M := by
        calc
          g₁.op.idx * M * M + g₁.i * M + g₁.j = g₁.op.idx * M * M + (g₁.i * M + g₁.j) := by ring
          _ < g₁.op.idx * M * M + M * M := Nat.add_lt_add_left (htail _ _ hi₁ hj₁) _
          _ = (g₁.op.idx + 1) * M * M := by ring
      have h2 : (g₁.op.idx + 1) * M * M ≤ g₂.op.idx * M * M :=
        Nat.mul_le_mul_right M (Nat.mul_le_mul_right M hop)
      omega
    · rw [hop]
      have h1 : g₁.i * M + g₁.j < (g₁.i + 1) * M := by
        calc
          g₁.i * M + g₁.j < g₁.i * M + M := Nat.add_lt_add_left hj₁ _
          _ = (g₁.i + 1) * M := by ring
      have h2 : (g₁.i + 1) * M ≤ g₂.i * M := Nat.mul_le_mul_right M hi
      omega
    · rw [hop, hi]; omega

private def lexWeightAux (B M : ℕ) : List GateSpec → ℕ
  | [] => 0
  | g :: rest => keyCode M g * B ^ rest.length + lexWeightAux B M rest

private lemma lexWeightAux_lt {B M : ℕ} (hB : 0 < B) :
    ∀ (l : List GateSpec), (∀ g ∈ l, keyCode M g < B) → lexWeightAux B M l < B ^ l.length
  | [], _ => by simp [lexWeightAux]
  | g :: rest, h => by
      simp only [lexWeightAux, List.length_cons, pow_succ']
      have hg : keyCode M g < B := h g (by simp)
      have hrest := lexWeightAux_lt hB rest (fun x hx => h x (by simp [hx]))
      have hpow : 0 < B ^ rest.length := pow_pos hB _
      calc
        keyCode M g * B ^ rest.length + lexWeightAux B M rest
            < keyCode M g * B ^ rest.length + B ^ rest.length := Nat.add_lt_add_left hrest _
        _ = (keyCode M g + 1) * B ^ rest.length := by ring
        _ ≤ B * B ^ rest.length := Nat.mul_le_mul_right _ hg

private lemma lexWeightAux_lt_of_prefix {B M : ℕ} (hB : 0 < B) :
    ∀ (l₁ l₂ : List GateSpec) (p : ℕ)
      (hlen : l₁.length = l₂.length) (hp : p < l₁.length),
      (∀ g ∈ l₂, keyCode M g < B) →
      (∀ idx (h1 : idx < p), l₂[idx]'(by omega) = l₁[idx]'(by omega)) →
      keyCode M (l₂[p]'(by omega)) < keyCode M (l₁[p]'(by omega)) →
      lexWeightAux B M l₂ < lexWeightAux B M l₁
  | [], _, _, _, hp, _, _, _ => by simp at hp
  | _ :: _, [], _, hlen, _, _, _, _ => by simp at hlen
  | g₁ :: r₁, g₂ :: r₂, 0, hlen, _, hbound, _, hlt => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [List.getElem_cons_zero] at hlt
      simp only [lexWeightAux, ← hlen]
      have hrest := lexWeightAux_lt hB r₂ (fun x hx => hbound x (by simp [hx]))
      rw [← hlen] at hrest
      calc
        keyCode M g₂ * B ^ r₁.length + lexWeightAux B M r₂
            < keyCode M g₂ * B ^ r₁.length + B ^ r₁.length := Nat.add_lt_add_left hrest _
        _ = (keyCode M g₂ + 1) * B ^ r₁.length := by ring
        _ ≤ keyCode M g₁ * B ^ r₁.length := Nat.mul_le_mul_right _ hlt
        _ ≤ keyCode M g₁ * B ^ r₁.length + lexWeightAux B M r₁ := Nat.le_add_right _ _
  | g₁ :: r₁, g₂ :: r₂, p + 1, hlen, hp, hbound, hpref, hlt => by
      have hg : g₂ = g₁ := hpref 0 (by omega)
      subst hg
      simp only [lexWeightAux]
      have hlen' : r₁.length = r₂.length := by simp at hlen; omega
      rw [hlen']
      refine Nat.add_lt_add_left (lexWeightAux_lt_of_prefix hB r₁ r₂ p hlen' (by simp at hp; omega)
        (fun x hx => hbound x (by simp [hx])) ?_ ?_) _
      · intro idx hidx
        exact hpref (idx + 1) (by omega)
      · exact hlt

private def lexWeight (n : ℕ) (gs : List GateSpec) : ℕ :=
  lexWeightAux (3 * (n + 2) * (n + 2)) (n + 2) gs

/-! ## 4. Main Theorem: `exists_canonical` -/

/-- Minimal well-formed lists computing `±f` satisfy `UsedGates`. -/
private lemma minimal_used {f : Polynomial ℤ} {n : ℕ}
    (hmin : ∀ gs' : List GateSpec, WellFormed gs' → gs'.length < n → ¬ ComputesSigned f gs')
    {gs : List GateSpec} (hwf : WellFormed gs) (hlen : gs.length = n) (hcomp : ComputesSigned f gs) :
    UsedGates gs := by
  intro k hk
  by_contra hdead
  push Not at hdead
  have hdead' : ∀ (k' : ℕ) (hk' : k' < gs.length), k < k' → gs[k'].i ≠ k + 2 ∧ gs[k'].j ≠ k + 2 :=
    fun k' hk' hkk' => hdead k' hk' hkk'
  have hwf' := deleteUnused_wellFormed hwf hdead'
  have hlen' : (deleteUnused gs k).length < n := by rw [deleteUnused_length]; omega
  have hout := deleteUnused_output hwf hk hdead'
  have hcomp' : ComputesSigned f (deleteUnused gs k) := by simpa [ComputesSigned, hout] using hcomp
  exact hmin (deleteUnused gs k) hwf' hlen' hcomp'

/-- Minimal well-formed lists computing `±f` (with `f ∉ {1, -1, X, -X}`) satisfy `NodupWires`. -/
private lemma minimal_nodup {f : Polynomial ℤ}
    (hf1 : f ≠ 1) (hf1' : f ≠ -1) (hfX : f ≠ Polynomial.X) (hfX' : f ≠ -Polynomial.X)
    {n : ℕ}
    (hmin : ∀ gs' : List GateSpec, WellFormed gs' → gs'.length < n → ¬ ComputesSigned f gs')
    {gs : List GateSpec} (hwf : WellFormed gs) (hlen : gs.length = n) (hcomp : ComputesSigned f gs) :
    NodupWires gs := by
  intro k hk m hm
  suffices h : ∀ flip : Bool, (wireVals gs).getD (k + 2) 0 ≠ sgnVal flip * (wireVals gs).getD m 0 by
    exact ⟨by simpa [sgnVal] using h false, by simpa [sgnVal] using h true⟩
  intro flip hdup
  by_cases hlast : k + 1 = gs.length
  · have hout : output gs = (wireVals gs).getD (k + 2) 0 := by
      have h1 : gs.length + 1 = k + 2 := by omega
      simp [output, h1]
    rw [← hout] at hdup
    rcases m with _ | _ | m'
    · rw [wireVals_zero] at hdup
      rcases hcomp with hpos | hneg <;> cases flip <;> simp [sgnVal] at hdup
      · exact hf1 (hpos.symm.trans hdup)
      · exact hf1' (hpos.symm.trans hdup)
      · exact hf1' (neg_eq_iff_eq_neg.mp (hneg.symm.trans hdup))
      · exact hf1 (neg_inj.mp (hneg.symm.trans hdup))
    · rw [wireVals_one] at hdup
      rcases hcomp with hpos | hneg <;> cases flip <;> simp [sgnVal] at hdup
      · exact hfX (hpos.symm.trans hdup)
      · exact hfX' (hpos.symm.trans hdup)
      · exact hfX' (neg_eq_iff_eq_neg.mp (hneg.symm.trans hdup))
      · exact hfX (neg_inj.mp (hneg.symm.trans hdup))
    · have hm_lt : m' + 1 < gs.length := by omega
      let gs' := gs.take (m' + 1)
      have hlen' : gs'.length = m' + 1 := by simp [gs', hm_lt.le]
      have hwf' : WellFormed gs' := by
        intro r hr
        have hr1 : r < m' + 1 := by simpa [hlen'] using hr
        have hr_gs : r < gs.length := by omega
        have hget : gs'[r] = gs[r] := by simp [gs']
        rw [hget]
        exact hwf r hr_gs
      have hout' : output gs' = (wireVals gs).getD (m' + 2) 0 := by
        have htk := wireVals_take_getD gs hm_lt.le (w := m' + 2) (by omega)
        simpa [output, gs', hlen'] using htk
      have hcomp' : ComputesSigned f gs' := by
        rw [ComputesSigned, hout']
        rcases hcomp with hpos | hneg <;> cases flip <;> simp [sgnVal] at hdup
        · left; exact hdup.symm.trans hpos
        · right; exact neg_eq_iff_eq_neg.mp (hdup.symm.trans hpos)
        · right; exact hdup.symm.trans hneg
        · left; exact neg_inj.mp (hdup.symm.trans hneg)
      exact hmin gs' hwf' (by omega) hcomp'
  · have hk1 : k + 1 < gs.length := by omega
    have hwf' := redirGate_wellFormed hwf hm flip
    have hcomp' := redirGate_computesSigned hwf hcomp hk1 hm flip hdup
    have hlen' : (redirGate gs k m flip).length < n := by rw [redirGate_length]; omega
    exact hmin _ hwf' hlen' hcomp'

/-- Any `UsedGates` + `NodupWires` list with nonzero output has `NonzeroWires`. -/
private lemma nonzeroWires_of_used_nodup {gs : List GateSpec}
    (hwf : WellFormed gs) (hused : UsedGates gs) (hnodup : NodupWires gs)
    (hout : output gs ≠ 0) :
    NonzeroWires gs := by
  classical
  by_contra hnz
  simp only [NonzeroWires, not_forall, not_not] at hnz
  let S : Finset ℕ := (Finset.range gs.length).filter (fun k => (wireVals gs).getD (k + 2) 0 = 0)
  have hS_ne : S.Nonempty := by
    rcases hnz with ⟨k, hk, hk0⟩
    exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hk0⟩⟩
  let k := S.max' hS_ne
  have hk_mem : k ∈ S := Finset.max'_mem S hS_ne
  have hk_lt : k < gs.length := Finset.mem_range.mp (Finset.mem_filter.mp hk_mem).1
  have hk_zero : (wireVals gs).getD (k + 2) 0 = 0 := (Finset.mem_filter.mp hk_mem).2
  have hk_not_last : k + 1 < gs.length := by
    by_contra hge
    have hlast : k + 1 = gs.length := by omega
    have hout_eq : output gs = (wireVals gs).getD (k + 2) 0 := by
      have h1 : gs.length + 1 = k + 2 := by omega
      simp [output, h1]
    exact hout (hout_eq.trans hk_zero)
  rcases hused k hk_not_last with ⟨k', hk', hkk', hor⟩
  have hk'_ne : (wireVals gs).getD (k' + 2) 0 ≠ 0 := by
    intro h0
    have hmem : k' ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk', h0⟩
    have hle := Finset.le_max' S k' hmem
    omega
  have hgate := wireVals_gate_wf hwf hk'
  have hgi := (hwf k' hk').1
  have hgj := (hwf k' hk').2
  cases hop : gs[k'].op <;> simp only [hop, SLPOp.applyPoly] at hgate
  · rcases hor with hi | hj
    · rw [hi, hk_zero, zero_add] at hgate
      exact (hnodup k' hk' gs[k'].j hgj).1 hgate
    · rw [hj, hk_zero, add_zero] at hgate
      exact (hnodup k' hk' gs[k'].i hgi).1 hgate
  · rcases hor with hi | hj
    · rw [hi, hk_zero, zero_sub] at hgate
      exact (hnodup k' hk' gs[k'].j hgj).2 hgate
    · rw [hj, hk_zero, sub_zero] at hgate
      exact (hnodup k' hk' gs[k'].i hgi).1 hgate
  · rcases hor with hi | hj
    · rw [hi, hk_zero, zero_mul] at hgate
      exact hk'_ne hgate
    · rw [hj, hk_zero, mul_zero] at hgate
      exact hk'_ne hgate

/-- **Main Canonicalization Soundness Theorem (`exists_canonical`):**
For every `t` and `P : SLP t` with nonzero output `f := P.evalPoly ≠ 0`,
either `f ∈ {1, -1, X, -X}` or there exists a `Canonical` gate list `gs` with
`1 ≤ gs.length ≤ t` computing `f` or `-f`. -/
theorem exists_canonical {t : ℕ} (P : SLP t) (hf : P.evalPoly ≠ 0) :
    (P.evalPoly = 1 ∨ P.evalPoly = -1 ∨ P.evalPoly = Polynomial.X ∨ P.evalPoly = -Polynomial.X) ∨
    ∃ gs : List GateSpec, Canonical gs ∧ 1 ≤ gs.length ∧ gs.length ≤ t ∧
      (output gs = P.evalPoly ∨ output gs = -P.evalPoly) := by
  classical
  set f := P.evalPoly
  by_cases hbase : f = 1 ∨ f = -1 ∨ f = Polynomial.X ∨ f = -Polynomial.X
  · exact Or.inl hbase
  right
  push Not at hbase
  rcases hbase with ⟨hf1, hf1', hfX, hfX'⟩
  have hex_len : ∃ n : ℕ, ∃ gs : List GateSpec, WellFormed gs ∧ gs.length = n ∧ ComputesSigned f gs :=
    ⟨t, P.toGateList, P.toGateList_wellFormed, P.toGateList_length, Or.inl P.output_toGateList⟩
  let n := Nat.find hex_len
  have hn_spec : ∃ gs : List GateSpec, WellFormed gs ∧ gs.length = n ∧ ComputesSigned f gs :=
    Nat.find_spec hex_len
  have hn_le : n ≤ t := Nat.find_min' hex_len ⟨P.toGateList, P.toGateList_wellFormed,
    P.toGateList_length, Or.inl P.output_toGateList⟩
  have hn_min : ∀ gs' : List GateSpec, WellFormed gs' → gs'.length < n → ¬ ComputesSigned f gs' := by
    intro gs' hwf' hlt' hcomp'
    exact Nat.find_min hex_len hlt' ⟨gs', hwf', rfl, hcomp'⟩
  have hn_pos : 1 ≤ n := by
    by_contra h0
    have hn0 : n = 0 := by omega
    rcases hn_spec with ⟨gs, _, hlen, hcomp⟩
    have hnil : gs = [] := List.eq_nil_of_length_eq_zero (hlen.trans hn0)
    subst hnil
    have hout : output [] = Polynomial.X := by simp [output, wireVals, wireValsAux]
    rcases hcomp with hpos | hneg
    · exact hfX (hpos.symm.trans hout)
    · exact hfX' (neg_eq_iff_eq_neg.mp (hneg.symm.trans hout))
  -- Take one minimal-length witness and normalize it to get a GoodNormalized witness
  rcases hn_spec with ⟨gs₁, hwf₁, hlen₁, hcomp₁⟩
  have hused₁ := minimal_used hn_min hwf₁ hlen₁ hcomp₁
  have hnodup₁ := minimal_nodup hf1 hf1' hfX hfX' hn_min hwf₁ hlen₁ hcomp₁
  have hout₁ : output gs₁ ≠ 0 := by
    rcases hcomp₁ with h | h <;> rw [h]
    · exact hf
    · exact neg_ne_zero.mpr hf
  have hnz₁ := nonzeroWires_of_used_nodup hwf₁ hused₁ hnodup₁ hout₁
  let gs₂ := ordNormalize gs₁
  have hwf₂ := ordNormalize_wellFormed hwf₁
  have hlen₂ : gs₂.length = n := by simp [gs₂, ordNormalize_length, hlen₁]
  have hord₂ := (ordNormalize_wireVals_and_ord hwf₁ hnz₁).2
  have hnz₂ := ordNormalize_preserves_nonzero hwf₁ hnz₁
  have hnodup₂ := ordNormalize_preserves_nodup hwf₁ hnz₁ hnodup₁
  have hused₂ := ordNormalize_preserves_used hused₁
  have hcomp₂ := ordNormalize_computesSigned hwf₁ hnz₁ hcomp₁
  -- Minimize lexWeight among all GoodNormalized lists of length n
  let GoodNorm (gs : List GateSpec) : Prop :=
    WellFormed gs ∧ gs.length = n ∧ OrdCanonical gs ∧ NonzeroWires gs ∧
    NodupWires gs ∧ UsedGates gs ∧ ComputesSigned f gs
  have hex_w : ∃ w : ℕ, ∃ gs : List GateSpec, GoodNorm gs ∧ lexWeight n gs = w :=
    ⟨lexWeight n gs₂, gs₂, ⟨hwf₂, hlen₂, hord₂, hnz₂, hnodup₂, hused₂, hcomp₂⟩, rfl⟩
  let w_min := Nat.find hex_w
  rcases Nat.find_spec hex_w with ⟨gs, ⟨hwf, hlen, hord, hnz, hnodup, hused, hcomp⟩, hw_eq⟩
  have hlex : LexOrdered gs := by
    intro k hk1 hk2 h1 h2 hind_i hind_j
    by_contra hnot
    rw [GateSpec.not_keyLe_iff] at hnot
    -- Swap gates k-1 and k, then re-normalize
    let gs_sw := swapRaw gs k
    have hwf_sw := swapRaw_wellFormed hwf hk1 hk2 hind_i hind_j
    have hnz_sw := swapRaw_preserves_nonzero hwf hnz hk1 hk2 hind_i hind_j
    have hnodup_sw := swapRaw_preserves_nodup hwf hnodup hk1 hk2 hind_i hind_j
    have hused_sw := swapRaw_preserves_used hused hk1 hk2 hind_i hind_j
    have hcomp_sw := swapRaw_computesSigned hwf hcomp hk1 hk2 hind_i hind_j
    have hord_pref := swapRaw_ord_prefix hord hk1 hk2
    let gs' := ordNormalize gs_sw
    have hwf' := ordNormalize_wellFormed hwf_sw
    have hlen' : gs'.length = n := by
      dsimp only [gs', gs_sw]
      rw [ordNormalize_length, swapRaw_length, hlen]
    have hord' := (ordNormalize_wireVals_and_ord hwf_sw hnz_sw).2
    have hnz' := ordNormalize_preserves_nonzero hwf_sw hnz_sw
    have hnodup' := ordNormalize_preserves_nodup hwf_sw hnz_sw hnodup_sw
    have hused' := ordNormalize_preserves_used hused_sw
    have hcomp' := ordNormalize_computesSigned hwf_sw hnz_sw hcomp_sw
    -- Compare lexWeight n gs' < lexWeight n gs
    have hB : 0 < 3 * (n + 2) * (n + 2) := by positivity
    have hbound : ∀ g ∈ gs', keyCode (n + 2) g < 3 * (n + 2) * (n + 2) := by
      intro g hg
      rcases List.mem_iff_getElem.mp hg with ⟨m, hm, rfl⟩
      have hgm : gs'[m].i < m + 2 ∧ gs'[m].j < m + 2 := hwf' m hm
      rw [hlen'] at hm
      exact keyCode_lt (by omega) (by omega)
    have hpref_eq : ∀ idx (hidx : idx < k - 1),
        gs'[idx]'(by omega) = gs[idx]'(by omega) := by
      intro idx hidx
      have hnorm_eq := ordNormalize_prefix_eq hwf_sw (p := k + 1)
        (by rw [swapRaw_length]; omega) hord_pref idx (by omega)
      rw [hnorm_eq]
      simp [swapRaw, show idx ≠ k - 1 by omega, show idx ≠ k by omega, hidx]
    have hpk_eq : gs'[k - 1]'(by omega) = gs[k]'(by omega) := by
      have hnorm_eq := ordNormalize_prefix_eq hwf_sw (p := k + 1)
        (by rw [swapRaw_length]; omega) hord_pref (k - 1) (by omega)
      rw [hnorm_eq]
      simp [swapRaw, show k < gs.length by omega]
    have hlt_code : keyCode (n + 2) (gs'[k - 1]'(by omega)) <
        keyCode (n + 2) (gs[k - 1]'(by omega)) := by
      rw [hpk_eq]
      have hgk := hwf k (by omega)
      have hgk1 := hwf (k - 1) (by omega)
      rw [keyCode_lt_iff (by omega) (by omega) (by omega) (by omega)]
      exact hnot
    have hw_lt : lexWeight n gs' < lexWeight n gs :=
      lexWeightAux_lt_of_prefix hB gs gs' (k - 1) (by omega) (by omega) hbound hpref_eq hlt_code
    exact Nat.find_min hex_w (hw_eq ▸ hw_lt)
      ⟨gs', ⟨hwf', hlen', hord', hnz', hnodup', hused', hcomp'⟩, rfl⟩
  exact ⟨gs, ⟨hwf, hord, hnz, hnodup, hused, hlex⟩, by omega, by omega, hcomp⟩

/-! ## 5. Dead-Gate Pruning Bound (`deadgate_count_bound`) -/

/-- Set of gate wires among `{2, ..., d + 1}` that are not an operand of any of the
first `d` gates `0, ..., d - 1`. This matches `unused_mask` in the enumerator after `d` gates. -/
def unusedWires (gs : List GateSpec) (d : ℕ) : Finset ℕ :=
  (Finset.Ico 2 (d + 2)).filter (fun w =>
    ∀ k < d, (gs.getD k default).i ≠ w ∧ (gs.getD k default).j ≠ w)

theorem unusedWires_zero (gs : List GateSpec) : unusedWires gs 0 = ∅ := by
  simp [unusedWires]

theorem unusedWires_succ {gs : List GateSpec} (hwf : WellFormed gs) {d : ℕ} (hd : d < gs.length) :
    unusedWires gs (d + 1) =
      insert (d + 2) (unusedWires gs d \ {gs[d].i, gs[d].j}) := by
  ext w
  simp only [unusedWires, Finset.mem_insert, Finset.mem_sdiff, Finset.mem_filter,
    Finset.mem_Ico, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hw2, hwd3⟩, hnot⟩
    by_cases hweq : w = d + 2
    · exact Or.inl hweq
    · right
      refine ⟨⟨⟨hw2, by omega⟩, fun k hk => hnot k (by omega)⟩, ?_⟩
      have hd_get := hnot d (by omega)
      rw [getD_eq_getElem_of_lt _ _ hd] at hd_get
      tauto
  · rintro (rfl | ⟨⟨⟨hw2, hwd2⟩, hnot⟩, hne⟩)
    · refine ⟨⟨by omega, by omega⟩, fun k hk => ?_⟩
      have hk_gs : k < gs.length := by omega
      have hgk := hwf k hk_gs
      rw [getD_eq_getElem_of_lt _ _ hk_gs]
      omega
    · refine ⟨⟨hw2, by omega⟩, fun k hk => ?_⟩
      by_cases hkd : k < d
      · exact hnot k hkd
      · have heq : k = d := by omega
        subst heq
        rw [getD_eq_getElem_of_lt _ _ hd]
        tauto

/-- **Dead-Gate Pruning Soundness (`deadgate_count_bound`):**
For any gate list of length `n` satisfying `UsedGates` (in particular, any `Canonical` list)
and any prefix length `d < n`, the number of unused gate wires after `d` gates is at most
`n - d + 1`. Equivalently, with `depth = d - 1` and `rem_after = n - 1 - depth`,
`unused_cnt ≤ rem_after + 1`. -/
theorem deadgate_count_bound {gs : List GateSpec} (hused : UsedGates gs)
    {d : ℕ} (hd : d < gs.length) :
    (unusedWires gs d).card ≤ gs.length - d + 1 := by
  classical
  let n := gs.length
  let A : Finset ℕ := unusedWires gs d
  let B : Finset ℕ := Finset.Ico (d + 2) (n + 1)
  let Slots : Finset ℕ := (Finset.Ico d n).biUnion (fun k' =>
    ({(gs.getD k' default).i, (gs.getD k' default).j} : Finset ℕ))
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro w hwA hwB
    have h1 := (Finset.mem_Ico.mp (Finset.mem_filter.mp hwA).1).2
    have h2 := (Finset.mem_Ico.mp hwB).1
    omega
  have hA_sub : A ⊆ Slots := by
    intro w hwA
    have hw_ico := (Finset.mem_filter.mp hwA).1
    have hnot := (Finset.mem_filter.mp hwA).2
    have hw2 : 2 ≤ w := (Finset.mem_Ico.mp hw_ico).1
    have hwd : w < d + 2 := (Finset.mem_Ico.mp hw_ico).2
    have hu : w - 2 + 1 < n := by omega
    rcases hused (w - 2) hu with ⟨k', hk', huk', hor⟩
    have hdk' : d ≤ k' := by
      by_contra hlt
      have hk'_d : k' < d := by omega
      have hnd := hnot k' hk'_d
      rw [getD_eq_getElem_of_lt _ _ hk'] at hnd
      omega
    rw [Finset.mem_biUnion]
    refine ⟨k', Finset.mem_Ico.mpr ⟨hdk', hk'⟩, ?_⟩
    rw [getD_eq_getElem_of_lt _ _ hk', Finset.mem_insert, Finset.mem_singleton]
    omega
  have hB_sub : B ⊆ Slots := by
    intro w hwB
    have hw1 : d + 2 ≤ w := (Finset.mem_Ico.mp hwB).1
    have hw2 : w < n + 1 := (Finset.mem_Ico.mp hwB).2
    have hu : w - 2 + 1 < n := by omega
    rcases hused (w - 2) hu with ⟨k', hk', huk', hor⟩
    have hdk' : d ≤ k' := by omega
    rw [Finset.mem_biUnion]
    refine ⟨k', Finset.mem_Ico.mpr ⟨hdk', hk'⟩, ?_⟩
    rw [getD_eq_getElem_of_lt _ _ hk', Finset.mem_insert, Finset.mem_singleton]
    omega
  have hAB_sub : A ∪ B ⊆ Slots := Finset.union_subset hA_sub hB_sub
  have hSlots_card : Slots.card ≤ 2 * (n - d) := by
    calc
      Slots.card ≤ ∑ k' ∈ Finset.Ico d n,
          ({(gs.getD k' default).i, (gs.getD k' default).j} : Finset ℕ).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _k' ∈ Finset.Ico d n, 2 :=
        Finset.sum_le_sum (fun _ _ => Finset.card_le_two)
      _ = (Finset.Ico d n).card * 2 := Finset.sum_const_nat (fun _ _ => rfl)
      _ = 2 * (n - d) := by rw [Nat.card_Ico]; ring
  have hB_card : B.card = n - d - 1 := by
    rw [Nat.card_Ico]
    omega
  have hAB_card : A.card + B.card ≤ 2 * (n - d) := by
    calc
      A.card + B.card = (A ∪ B).card := (Finset.card_union_of_disjoint hdisj).symm
      _ ≤ Slots.card := Finset.card_le_card hAB_sub
      _ ≤ 2 * (n - d) := hSlots_card
  dsimp only [A, n] at hAB_card hB_card
  omega

/-- Corollary for `Canonical` lists. -/
theorem deadgate_count_bound_of_canonical {gs : List GateSpec} (hcan : Canonical gs)
    {d : ℕ} (hd : d < gs.length) :
    (unusedWires gs d).card ≤ gs.length - d + 1 :=
  deadgate_count_bound hcan.used hd

/-- Leaf-level consequence of `UsedGates`: before the last gate (`1 ≤ gs.length`),
at most `2` gate wires remain unused, and every unused gate wire must be an operand
of the last gate `gs[gs.length - 1]`. -/
theorem unusedWires_last_gate {gs : List GateSpec} (hused : UsedGates gs)
    (hne : 1 ≤ gs.length) :
    (unusedWires gs (gs.length - 1)).card ≤ 2 ∧
    ∀ w ∈ unusedWires gs (gs.length - 1),
      w = (gs[gs.length - 1]'(by omega)).i ∨ w = (gs[gs.length - 1]'(by omega)).j := by
  have hcard : (unusedWires gs (gs.length - 1)).card ≤ 2 := by
    have h := deadgate_count_bound hused (d := gs.length - 1) (by omega)
    omega
  refine ⟨hcard, fun w hw => ?_⟩
  have hw_ico := (Finset.mem_filter.mp hw).1
  have hnot := (Finset.mem_filter.mp hw).2
  have hw2 : 2 ≤ w := (Finset.mem_Ico.mp hw_ico).1
  have hwd : w < gs.length - 1 + 2 := (Finset.mem_Ico.mp hw_ico).2
  rcases hused (w - 2) (by omega) with ⟨k', hk', huk', hor⟩
  have hk'_ge : gs.length - 1 ≤ k' := by
    by_contra hlt
    have hnd := hnot k' (by omega)
    rw [getD_eq_getElem_of_lt _ _ hk'] at hnd
    omega
  have hk'_eq : k' = gs.length - 1 := by omega
  subst hk'_eq
  rw [show w - 2 + 2 = w by omega] at hor
  exact hor.imp Eq.symm Eq.symm

/-! ## 6. Checklist Reduction Theorem (`zmax_le_of_checklist`) -/

/-- Negating a polynomial in `ℤ[X]` preserves its distinct integer root count. -/
theorem intRootCount_neg (f : Polynomial ℤ) : intRootCount (-f) = intRootCount f := by
  simp [intRootCount, intRootSet]

/-- The basic seed polynomials `{1, -1, X, -X}` each have at most `1` distinct integer root. -/
theorem intRootCount_le_one_of_basic {f : Polynomial ℤ}
    (hf : f = 1 ∨ f = -1 ∨ f = Polynomial.X ∨ f = -Polynomial.X) :
    intRootCount f ≤ 1 := by
  rcases hf with rfl | rfl | rfl | rfl
  · exact (intRootCount_le_natDegree one_ne_zero).trans (by simp)
  · rw [intRootCount_neg]
    exact (intRootCount_le_natDegree one_ne_zero).trans (by simp)
  · exact (intRootCount_le_natDegree Polynomial.X_ne_zero).trans (by simp)
  · rw [intRootCount_neg]
    exact (intRootCount_le_natDegree Polynomial.X_ne_zero).trans (by simp)

/-- **Checklist Soundness Theorem (`zmax_le_of_checklist`):**
If every `Canonical` gate list `gs` with `1 ≤ gs.length ≤ τ` and `output gs ≠ 0`
satisfies `intRootCount (output gs) ≤ K` (where `1 ≤ K`), then every nonzero `SLP t`
with `t ≤ τ` computes a polynomial with at most `K` distinct integer roots. -/
theorem zmax_le_of_checklist (τ K : ℕ) (hK : 1 ≤ K)
    (hcheck : ∀ gs : List GateSpec, Canonical gs → 1 ≤ gs.length → gs.length ≤ τ →
      output gs ≠ 0 → intRootCount (output gs) ≤ K) :
    ∀ t ≤ τ, ∀ P : SLP t, P.evalPoly ≠ 0 → intRootCount P.evalPoly ≤ K := by
  intro t ht P hne
  rcases exists_canonical P hne with hbasic | ⟨gs, hcan, h1, hlen_t, hout⟩
  · exact (intRootCount_le_one_of_basic hbasic).trans hK
  · have hlen_tau : gs.length ≤ τ := hlen_t.trans ht
    have hout_ne : output gs ≠ 0 := by
      rcases hout with h | h <;> rw [h]
      · exact hne
      · exact neg_ne_zero.mpr hne
    have hbound := hcheck gs hcan h1 hlen_tau hout_ne
    rcases hout with h | h
    · rwa [← h]
    · rwa [← intRootCount_neg P.evalPoly, ← h]

/-- **Conditional Upper Bound `z_max(9) ≤ 6`:**
If the exhaustive checklist over all `Canonical` gate lists of length `1 ≤ n ≤ 9`
with nonzero output establishes `intRootCount (output gs) ≤ 6`, then every nonzero
`SLP t` with `t ≤ 9` has at most `6` distinct integer roots.

*Verification boundary:* This theorem machine-checks the soundness of canonicalization
(`WellFormed`, `OrdCanonical`, `NonzeroWires`, `NodupWires`, `UsedGates`, `LexOrdered`)
and sign/length reduction. It does **not** internally verify the C/Python enumeration loop,
hash-table collision freeness, or the execution trace of external runs; those must be
supplied via the checklist hypothesis `hcheck` (or per-leaf certificates). -/
theorem zmax9_le_six_of_checklist
    (hcheck : ∀ gs : List GateSpec, Canonical gs → 1 ≤ gs.length → gs.length ≤ 9 →
      output gs ≠ 0 → intRootCount (output gs) ≤ 6) :
    ∀ t ≤ 9, ∀ P : SLP t, P.evalPoly ≠ 0 → intRootCount P.evalPoly ≤ 6 :=
  zmax_le_of_checklist 9 6 (by omega) hcheck

/-- **Conditional Upper Bound `z_max(10) ≤ 7`:**
If the exhaustive checklist over all `Canonical` gate lists of length `1 ≤ n ≤ 10`
with nonzero output establishes `intRootCount (output gs) ≤ 7`, then every nonzero
`SLP t` with `t ≤ 10` has at most `7` distinct integer roots.

*Verification boundary:* Same as `zmax9_le_six_of_checklist`; the external enumerator loop
itself is not verified inside Lean and appears as the hypothesis `hcheck`. -/
theorem zmax10_le_seven_of_checklist
    (hcheck : ∀ gs : List GateSpec, Canonical gs → 1 ≤ gs.length → gs.length ≤ 10 →
      output gs ≠ 0 → intRootCount (output gs) ≤ 7) :
    ∀ t ≤ 10, ∀ P : SLP t, P.evalPoly ≠ 0 → intRootCount P.evalPoly ≤ 7 :=
  zmax_le_of_checklist 10 7 (by omega) hcheck

end Research.PvsNP.Tau

end
