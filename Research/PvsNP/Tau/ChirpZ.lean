module

public import Research.PvsNP.Tau.TauConjecture
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

@[expose] public section

namespace Research.PvsNP.Tau

/-!
# Fraction-Free Chirp-$z$ $q$-Pochhammer SLPs and Refutation of Linear Growth ($c = 1$)

This module establishes:
1. A compositional wire-set framework (`Computes`, `CanBuild`) for constant-free straight-line
   programs (`SLP`) over `ℤ[X]`.
2. The fraction-free $q$-binomial theorem and Bluestein Chirp-$z$ identity over `ℤ[X]`
   with zero divisions.
3. Linear-gate preparation of the Chirp-$z$ input polynomials `chirpA m` and `chirpB m`,
   plus a general reduction `zMaxGe_of_chirp_outputs` from any scaled middle-product engine
   to `zMaxGe`.
4. Division-free Karatsuba polynomial multiplication via `CanBuild`, proving
   `tau_karatsuba_growth` (`zMaxGe (50 * 3 ^ k) (2 * 4 ^ k + 1)`) and unconditionally
   refuting the linear Shub–Smale $\tau$-conjecture (`c = 1`):
   `tau_refutes_linear`.
-/

/-! ## 1. Compositional Wire-Set Framework (`Computes`, `CanBuild`) -/

/-- `Computes τ S` asserts that there is a length-`τ` constant-free SLP whose wires contain
every polynomial in `S`. -/
def Computes (τ : ℕ) (S : Set (Polynomial ℤ)) : Prop :=
  ∃ P : SLP τ, ∀ f ∈ S, ∃ i : Fin (τ + 2), P.evalWire i = f

/-- `CanBuild S Δ T` asserts that from any SLP already containing all polynomials in `S`
(inside any larger wire set `U`), appending `Δ` gates suffices to also compute every
polynomial in `T`. -/
def CanBuild (S : Set (Polynomial ℤ)) (Δ : ℕ) (T : Set (Polynomial ℤ)) : Prop :=
  ∀ τ U, S ⊆ U → Computes τ U → Computes (τ + Δ) (U ∪ T)

theorem computes_nil : Computes 0 ({(1 : Polynomial ℤ), Polynomial.X} : Set (Polynomial ℤ)) := by
  refine ⟨.nil, ?_⟩
  intro f hf
  rcases hf with rfl | rfl
  · exact ⟨⟨0, by omega⟩, by simp [SLP.evalWire]⟩
  · exact ⟨⟨1, by omega⟩, by simp [SLP.evalWire]⟩

theorem computes_mono {τ : ℕ} {S₁ S₂ : Set (Polynomial ℤ)} (hsub : S₁ ⊆ S₂)
    (h : Computes τ S₂) : Computes τ S₁ := by
  rcases h with ⟨P, hP⟩
  exact ⟨P, fun f hf => hP f (hsub hf)⟩

theorem computes_snoc {τ : ℕ} {U : Set (Polynomial ℤ)} (h : Computes τ U)
    (op : SLPOp) {f g : Polynomial ℤ} (hf : f ∈ U) (hg : g ∈ U) :
    Computes (τ + 1) (U ∪ {op.applyPoly f g}) := by
  rcases h with ⟨P, hP⟩
  rcases hP f hf with ⟨i, hi⟩
  rcases hP g hg with ⟨j, hj⟩
  refine ⟨P.snoc op i j, ?_⟩
  intro q hq
  rcases hq with hqU | hqNew
  · rcases hP q hqU with ⟨k, hk⟩
    refine ⟨⟨k.val, by omega⟩, ?_⟩
    simpa [SLP.evalWire, k.isLt] using hk
  · rw [Set.mem_singleton_iff] at hqNew
    subst hqNew
    refine ⟨⟨τ + 2, by omega⟩, ?_⟩
    simp [SLP.evalWire, hi, hj]

theorem computes_pad {τ₁ τ₂ : ℕ} {U : Set (Polynomial ℤ)} (hle : τ₁ ≤ τ₂)
    (h : Computes τ₁ U) : Computes τ₂ U := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  clear hle
  induction d with
  | zero => simpa using h
  | succ d ih =>
      rcases ih with ⟨P, hP⟩
      refine ⟨P.snoc .mul 0 0, ?_⟩
      intro f hf
      rcases hP f hf with ⟨k, hk⟩
      refine ⟨⟨k.val, by omega⟩, ?_⟩
      simpa [SLP.evalWire, k.isLt] using hk

theorem computes_extract {τ : ℕ} {U : Set (Polynomial ℤ)} (h : Computes τ U)
    {f : Polynomial ℤ} (hf : f ∈ U) : ∃ P : SLP (τ + 1), P.evalPoly = f := by
  rcases h with ⟨P, hP⟩
  rcases hP f hf with ⟨i, hi⟩
  refine ⟨P.snoc .mul i 0, ?_⟩
  simp [SLP.evalPoly, SLP.evalWire, SLPOp.applyPoly, hi, P.evalWire_zero]

theorem canBuild_empty (S : Set (Polynomial ℤ)) : CanBuild S 0 ∅ := by
  intro τ U _ hU
  simpa using hU

theorem canBuild_subset {S T : Set (Polynomial ℤ)} (h : T ⊆ S) : CanBuild S 0 T := by
  intro τ U hSU hU
  have hEq : U ∪ T = U := Set.union_eq_left.mpr (h.trans hSU)
  simpa [hEq] using hU

theorem canBuild_mono_cost {S T : Set (Polynomial ℤ)} {Δ₁ Δ₂ : ℕ} (hle : Δ₁ ≤ Δ₂)
    (h : CanBuild S Δ₁ T) : CanBuild S Δ₂ T := by
  intro τ U hSU hU
  exact computes_pad (by omega) (h τ U hSU hU)

theorem canBuild_mono_out {S T₁ T₂ : Set (Polynomial ℤ)} {Δ : ℕ} (hsub : T₁ ⊆ T₂)
    (h : CanBuild S Δ T₂) : CanBuild S Δ T₁ := by
  intro τ U hSU hU
  exact computes_mono (Set.union_subset_union_right U hsub) (h τ U hSU hU)

/-- Outputs already present in `S` cost zero extra gates to include in `T₁`. -/
theorem canBuild_weaken_out {S T₁ T₂ : Set (Polynomial ℤ)} {Δ : ℕ} (hsub : T₁ ⊆ S ∪ T₂)
    (h : CanBuild S Δ T₂) : CanBuild S Δ T₁ := by
  intro τ U hSU hU
  have hUsub : U ∪ T₁ ⊆ U ∪ T₂ := by
    refine Set.union_subset Set.subset_union_left ?_
    exact hsub.trans (Set.union_subset_union_left T₂ hSU)
  exact computes_mono hUsub (h τ U hSU hU)

theorem canBuild_mono_in {S₁ S₂ T : Set (Polynomial ℤ)} {Δ : ℕ} (hsub : S₁ ⊆ S₂)
    (h : CanBuild S₁ Δ T) : CanBuild S₂ Δ T := by
  intro τ U hSU hU
  exact h τ U (hsub.trans hSU) hU

theorem canBuild_gate (op : SLPOp) (f g : Polynomial ℤ) :
    CanBuild ({f, g} : Set (Polynomial ℤ)) 1 {op.applyPoly f g} := by
  intro τ U hSU hU
  have hf : f ∈ U := hSU (by simp)
  have hg : g ∈ U := hSU (by simp)
  exact computes_snoc hU op hf hg

theorem canBuild_add (f g : Polynomial ℤ) :
    CanBuild ({f, g} : Set (Polynomial ℤ)) 1 {f + g} :=
  canBuild_gate .add f g

theorem canBuild_sub (f g : Polynomial ℤ) :
    CanBuild ({f, g} : Set (Polynomial ℤ)) 1 {f - g} :=
  canBuild_gate .sub f g

theorem canBuild_mul (f g : Polynomial ℤ) :
    CanBuild ({f, g} : Set (Polynomial ℤ)) 1 {f * g} :=
  canBuild_gate .mul f g

theorem canBuild_trans {S₁ S₂ T₁ T₂ : Set (Polynomial ℤ)} {Δ₁ Δ₂ : ℕ}
    (h1 : CanBuild S₁ Δ₁ T₁) (hsub : S₂ ⊆ S₁ ∪ T₁) (h2 : CanBuild S₂ Δ₂ T₂) :
    CanBuild S₁ (Δ₁ + Δ₂) (T₁ ∪ T₂) := by
  intro τ U hSU hU
  have h1' : Computes (τ + Δ₁) (U ∪ T₁) := h1 τ U hSU hU
  have hS2 : S₂ ⊆ U ∪ T₁ := hsub.trans (Set.union_subset_union_left T₁ hSU)
  have h2' : Computes (τ + Δ₁ + Δ₂) ((U ∪ T₁) ∪ T₂) := h2 (τ + Δ₁) (U ∪ T₁) hS2 h1'
  simpa [Nat.add_assoc, Set.union_assoc] using h2'

theorem canBuild_seq {S T₁ T₂ : Set (Polynomial ℤ)} {Δ₁ Δ₂ : ℕ}
    (h1 : CanBuild S Δ₁ T₁) (h2 : CanBuild (S ∪ T₁) Δ₂ T₂) :
    CanBuild S (Δ₁ + Δ₂) (T₁ ∪ T₂) :=
  canBuild_trans h1 Set.Subset.rfl h2

/-- Build a finite family of sets `T i` for `i < n`, each requiring at most `d` gates from `S`. -/
theorem canBuild_fin_union {n d : ℕ} {S : Set (Polynomial ℤ)} {T : ℕ → Set (Polynomial ℤ)}
    (h : ∀ i < n, CanBuild S d (T i)) :
    CanBuild S (n * d) (⋃ i < n, T i) := by
  induction n with
  | zero =>
      simpa using canBuild_empty S
  | succ n ih =>
      have hprev : CanBuild S (n * d) (⋃ i < n, T i) :=
        ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
      have hlast : CanBuild (S ∪ ⋃ i < n, T i) d (T n) :=
        canBuild_mono_in Set.subset_union_left (h n (Nat.lt_succ_self n))
      have hcomb := canBuild_seq hprev hlast
      have hcost : n * d + d = (n + 1) * d := by ring
      rw [hcost] at hcomb
      refine canBuild_mono_out ?_ hcomb
      intro f hf
      simp only [Set.mem_iUnion, exists_prop] at hf
      rcases hf with ⟨i, hi, hfi⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
      · exact Or.inl (by simp only [Set.mem_iUnion, exists_prop]; exact ⟨i, hlt, hfi⟩)
      · exact Or.inr hfi

/-- Sequential product `∏ i ∈ Finset.range n, f i` from `{1} ∪ {f i | i < n}` in `n` gates. -/
theorem canBuild_fin_prod (n : ℕ) (f : ℕ → Polynomial ℤ) :
    CanBuild ({(1 : Polynomial ℤ)} ∪ ⋃ i < n, {f i}) n
      {∏ i ∈ Finset.range n, f i} := by
  induction n with
  | zero =>
      refine canBuild_subset ?_
      simp
  | succ n ih =>
      have hsub1 : ({(1 : Polynomial ℤ)} ∪ ⋃ i < n, {f i}) ⊆
          ({(1 : Polynomial ℤ)} ∪ ⋃ i < n + 1, {f i}) := by
        intro x hx
        rcases hx with hx1 | hx2
        · exact Or.inl hx1
        · right
          simp only [Set.mem_iUnion, exists_prop] at hx2 ⊢
          rcases hx2 with ⟨i, hi, hxi⟩
          exact ⟨i, Nat.lt_succ_of_lt hi, hxi⟩
      have h1 := canBuild_mono_in hsub1 ih
      have h2 := canBuild_mul (∏ i ∈ Finset.range n, f i) (f n)
      have hsub2 : ({∏ i ∈ Finset.range n, f i, f n} : Set (Polynomial ℤ)) ⊆
          ({(1 : Polynomial ℤ)} ∪ ⋃ i < n + 1, {f i}) ∪ {∏ i ∈ Finset.range n, f i} := by
        intro x hx
        rcases hx with rfl | rfl
        · exact Or.inr rfl
        · left; right
          simp only [Set.mem_iUnion, exists_prop]
          exact ⟨n, Nat.lt_succ_self n, rfl⟩
      have hcomb := canBuild_trans h1 hsub2 h2
      refine canBuild_mono_out ?_ hcomb
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      right
      rw [Set.mem_singleton_iff, Finset.prod_range_succ]

/-- Sequential sum `∑ i ∈ Finset.range n, f i` from `{0} ∪ {f i | i < n}` in `n` gates. -/
theorem canBuild_fin_sum (n : ℕ) (f : ℕ → Polynomial ℤ) :
    CanBuild ({(0 : Polynomial ℤ)} ∪ ⋃ i < n, {f i}) n
      {∑ i ∈ Finset.range n, f i} := by
  induction n with
  | zero =>
      refine canBuild_subset ?_
      simp
  | succ n ih =>
      have hsub1 : ({(0 : Polynomial ℤ)} ∪ ⋃ i < n, {f i}) ⊆
          ({(0 : Polynomial ℤ)} ∪ ⋃ i < n + 1, {f i}) := by
        intro x hx
        rcases hx with hx0 | hx2
        · exact Or.inl hx0
        · right
          simp only [Set.mem_iUnion, exists_prop] at hx2 ⊢
          rcases hx2 with ⟨i, hi, hxi⟩
          exact ⟨i, Nat.lt_succ_of_lt hi, hxi⟩
      have h1 := canBuild_mono_in hsub1 ih
      have h2 := canBuild_add (∑ i ∈ Finset.range n, f i) (f n)
      have hsub2 : ({∑ i ∈ Finset.range n, f i, f n} : Set (Polynomial ℤ)) ⊆
          ({(0 : Polynomial ℤ)} ∪ ⋃ i < n + 1, {f i}) ∪ {∑ i ∈ Finset.range n, f i} := by
        intro x hx
        rcases hx with rfl | rfl
        · exact Or.inr rfl
        · left; right
          simp only [Set.mem_iUnion, exists_prop]
          exact ⟨n, Nat.lt_succ_self n, rfl⟩
      have hcomb := canBuild_trans h1 hsub2 h2
      refine canBuild_mono_out ?_ hcomb
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      right
      rw [Set.mem_singleton_iff, Finset.sum_range_succ]

/-- Build `{a ^ i | i ≤ n}` from `{1, a}` in `n` gates. -/
theorem canBuild_powers (n : ℕ) (a : Polynomial ℤ) :
    CanBuild ({(1 : Polynomial ℤ), a} : Set (Polynomial ℤ)) n
      (⋃ i < n + 1, {a ^ i}) := by
  induction n with
  | zero =>
      refine canBuild_subset ?_
      intro x hx
      simp only [Set.mem_iUnion, exists_prop, Set.mem_singleton_iff] at hx
      rcases hx with ⟨i, hi, rfl⟩
      have : i = 0 := by omega
      subst this
      simp
  | succ n ih =>
      have hmul := canBuild_mul (a ^ n) a
      have hsub : ({a ^ n, a} : Set (Polynomial ℤ)) ⊆
          ({(1 : Polynomial ℤ), a} : Set (Polynomial ℤ)) ∪ (⋃ i < n + 1, {a ^ i}) := by
        intro x hx
        rcases hx with rfl | rfl
        · right
          simp only [Set.mem_iUnion, exists_prop]
          exact ⟨n, Nat.lt_succ_self n, rfl⟩
        · left; simp
      have hcomb := canBuild_trans ih hsub hmul
      refine canBuild_mono_out ?_ hcomb
      intro x hx
      simp only [Set.mem_iUnion, exists_prop, Set.mem_singleton_iff] at hx
      rcases hx with ⟨i, hi, rfl⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
      · left
        simp only [Set.mem_iUnion, exists_prop]
        exact ⟨i, hlt, rfl⟩
      · right
        simp [pow_succ]

/-- Build all prefix products `∏ j ∈ Finset.range k, f j` for `k ≤ n` from `{1} ∪ {f j | j < n}`
in `n` gates. -/
theorem canBuild_prefix_prods (n : ℕ) (f : ℕ → Polynomial ℤ) :
    CanBuild ({(1 : Polynomial ℤ)} ∪ ⋃ j < n, {f j}) n
      (⋃ k < n + 1, {∏ j ∈ Finset.range k, f j}) := by
  induction n with
  | zero =>
      refine canBuild_subset ?_
      intro x hx
      simp only [Set.mem_iUnion, exists_prop, Set.mem_singleton_iff] at hx
      rcases hx with ⟨k, hk, rfl⟩
      have : k = 0 := by omega
      subst this
      simp
  | succ n ih =>
      have hsub1 : ({(1 : Polynomial ℤ)} ∪ ⋃ j < n, {f j}) ⊆
          ({(1 : Polynomial ℤ)} ∪ ⋃ j < n + 1, {f j}) := by
        intro x hx
        rcases hx with hx1 | hx2
        · exact Or.inl hx1
        · right
          simp only [Set.mem_iUnion, exists_prop] at hx2 ⊢
          rcases hx2 with ⟨j, hj, hxj⟩
          exact ⟨j, Nat.lt_succ_of_lt hj, hxj⟩
      have h1 := canBuild_mono_in hsub1 ih
      have hmul := canBuild_mul (∏ j ∈ Finset.range n, f j) (f n)
      have hsub2 : ({∏ j ∈ Finset.range n, f j, f n} : Set (Polynomial ℤ)) ⊆
          ({(1 : Polynomial ℤ)} ∪ ⋃ j < n + 1, {f j}) ∪
            (⋃ k < n + 1, {∏ j ∈ Finset.range k, f j}) := by
        intro x hx
        rcases hx with rfl | rfl
        · right
          simp only [Set.mem_iUnion, exists_prop]
          exact ⟨n, Nat.lt_succ_self n, rfl⟩
        · left; right
          simp only [Set.mem_iUnion, exists_prop]
          exact ⟨n, Nat.lt_succ_self n, rfl⟩
      have hcomb := canBuild_trans h1 hsub2 hmul
      refine canBuild_mono_out ?_ hcomb
      intro x hx
      simp only [Set.mem_iUnion, exists_prop, Set.mem_singleton_iff] at hx
      rcases hx with ⟨k, hk, rfl⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
      · left
        simp only [Set.mem_iUnion, exists_prop]
        exact ⟨k, hlt, rfl⟩
      · right
        rw [Set.mem_singleton_iff, Finset.prod_range_succ]

/-- Build `{w ^ (s * s) | s ≤ L}` and `{w ^ (2 * s + 1) | s ≤ L}` from `{1, w}` in `2 * L + 1`
gates via second differences: `odd(0) = w`, `odd(s+1) = odd(s) * w^2`, `sq(s+1) = sq(s) * odd(s)`. -/
theorem canBuild_sq_and_odd_powers (L : ℕ) (w : Polynomial ℤ) :
    CanBuild ({(1 : Polynomial ℤ), w} : Set (Polynomial ℤ)) (2 * L + 1)
      ((⋃ s < L + 1, {w ^ (s * s)}) ∪ (⋃ s < L + 1, {w ^ (2 * s + 1)})) := by
  have hstep : ∀ n : ℕ,
      CanBuild ({(1 : Polynomial ℤ), w, w ^ 2} : Set (Polynomial ℤ)) (2 * n)
        ((⋃ s < n + 1, {w ^ (s * s)}) ∪ (⋃ s < n + 1, {w ^ (2 * s + 1)})) := by
    intro n
    induction n with
    | zero =>
        refine canBuild_subset ?_
        intro x hx
        rcases hx with hx1 | hx2
        · simp only [Set.mem_iUnion, exists_prop, Set.mem_singleton_iff] at hx1
          rcases hx1 with ⟨s, hs, rfl⟩
          have : s = 0 := by omega
          subst this; simp
        · simp only [Set.mem_iUnion, exists_prop, Set.mem_singleton_iff] at hx2
          rcases hx2 with ⟨s, hs, rfl⟩
          have : s = 0 := by omega
          subst this; simp
    | succ n ih =>
        have hm1 := canBuild_mul (w ^ (n * n)) (w ^ (2 * n + 1))
        have hm2 := canBuild_mul (w ^ (2 * n + 1)) (w ^ 2)
        have h12 : CanBuild ({w ^ (n * n), w ^ (2 * n + 1), w ^ 2} : Set (Polynomial ℤ)) 2
            ({w ^ ((n + 1) * (n + 1)), w ^ (2 * (n + 1) + 1)} : Set (Polynomial ℤ)) := by
          have ha := canBuild_mono_in (S₂ := {w ^ (n * n), w ^ (2 * n + 1), w ^ 2})
            (by intro x hx; rcases hx with rfl | rfl <;> simp) hm1
          have hb := canBuild_trans ha
            (by intro x hx; rcases hx with rfl | rfl <;> simp) hm2
          refine canBuild_mono_out ?_ hb
          intro x hx
          rcases hx with rfl | rfl
          · left; rw [Set.mem_singleton_iff, ← pow_add]; congr 1; ring
          · right; rw [Set.mem_singleton_iff, ← pow_add]; congr 1
        have hsub : ({w ^ (n * n), w ^ (2 * n + 1), w ^ 2} : Set (Polynomial ℤ)) ⊆
            ({(1 : Polynomial ℤ), w, w ^ 2} : Set (Polynomial ℤ)) ∪
              ((⋃ s < n + 1, {w ^ (s * s)}) ∪ (⋃ s < n + 1, {w ^ (2 * s + 1)})) := by
          intro x hx
          rcases hx with rfl | rfl | rfl
          · right; left; simp only [Set.mem_iUnion, exists_prop]
            exact ⟨n, Nat.lt_succ_self n, rfl⟩
          · right; right; simp only [Set.mem_iUnion, exists_prop]
            exact ⟨n, Nat.lt_succ_self n, rfl⟩
          · left; simp
        have hcomb := canBuild_trans ih hsub h12
        refine canBuild_mono_out ?_ hcomb
        intro x hx
        rcases hx with hx1 | hx2
        · simp only [Set.mem_iUnion, exists_prop, Set.mem_singleton_iff] at hx1
          rcases hx1 with ⟨s, hs, rfl⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hlt | rfl
          · left; left; simp only [Set.mem_iUnion, exists_prop]
            exact ⟨s, hlt, rfl⟩
          · right; simp
        · simp only [Set.mem_iUnion, exists_prop, Set.mem_singleton_iff] at hx2
          rcases hx2 with ⟨s, hs, rfl⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hlt | rfl
          · left; right; simp only [Set.mem_iUnion, exists_prop]
            exact ⟨s, hlt, rfl⟩
          · right; simp
  have hw2 : CanBuild ({(1 : Polynomial ℤ), w} : Set (Polynomial ℤ)) 1 {w ^ 2} := by
    have h := canBuild_mul w w
    have h' := canBuild_mono_in (S₂ := {(1 : Polynomial ℤ), w})
      (by intro x hx; rcases hx with rfl | rfl <;> simp) h
    refine canBuild_mono_out ?_ h'
    intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx; exact Set.mem_singleton_iff.mpr (sq w)
  have hcomb := canBuild_trans hw2
    (by intro x hx; rcases hx with rfl | rfl | rfl <;> simp) (hstep L)
  have hcost : 1 + 2 * L = 2 * L + 1 := by ring
  rw [hcost] at hcomb
  exact canBuild_mono_out (fun x hx => Or.inr hx) hcomb

/-! ## 2. Fraction-Free $q$-Binomial Theorem & Bluestein Chirp-$z$ Identity -/

/-- `qDenom q m := ∏ j ∈ Finset.range m, (q ^ (j + 1) - 1)`. -/
def qDenom {R : Type*} [CommRing R] (q : R) (m : ℕ) : R :=
  ∏ j ∈ Finset.range m, (q ^ (j + 1) - 1)

/-- Fraction-free $q$-binomial numerator:
`qBinomNum q m r = (∏ j < r, (q ^ (m - j) - 1)) * (∏ j ∈ [r, m), (q ^ (j + 1) - 1))`. -/
def qBinomNum {R : Type*} [CommRing R] (q : R) (m r : ℕ) : R :=
  (∏ j ∈ Finset.range r, (q ^ (m - j) - 1)) *
    (∏ j ∈ Finset.Ico r m, (q ^ (j + 1) - 1))

theorem qDenom_succ {R : Type*} [CommRing R] (q : R) (m : ℕ) :
    qDenom q (m + 1) = (q ^ (m + 1) - 1) * qDenom q m := by
  simp [qDenom, Finset.prod_range_succ, mul_comm]

theorem qBinomNum_zero {R : Type*} [CommRing R] (q : R) (m : ℕ) :
    qBinomNum q m 0 = qDenom q m := by
  simp [qBinomNum, qDenom, Nat.Ico_zero_eq_range]

theorem qBinomNum_self {R : Type*} [CommRing R] (q : R) (m : ℕ) :
    qBinomNum q m m = qDenom q m := by
  simp only [qBinomNum, qDenom, Finset.Ico_self, Finset.prod_empty, mul_one]
  refine Finset.prod_bij (fun j _ => m - 1 - j) ?_ ?_ ?_ ?_
  · intro j hj; simp only [Finset.mem_range] at hj ⊢; omega
  · intro j₁ hj₁ j₂ hj₂ h; simp only [Finset.mem_range] at hj₁ hj₂; omega
  · intro b hb; simp only [Finset.mem_range] at hb
    refine ⟨m - 1 - b, Finset.mem_range.mpr (by omega), by omega⟩
  · intro j hj; simp only [Finset.mem_range] at hj; congr 2; omega

/-- Symmetry representation: both factors of `qBinomNum q m r` come from the single prefix-product
table `P(k) = ∏ j < k, (q ^ (m - j) - 1)`: `qBinomNum q m r = P r * P (m - r)`. -/
theorem qBinomNum_eq_prefix_mul {R : Type*} [CommRing R] (q : R) (m r : ℕ) (hrm : r ≤ m) :
    qBinomNum q m r =
      (∏ j ∈ Finset.range r, (q ^ (m - j) - 1)) *
        (∏ j ∈ Finset.range (m - r), (q ^ (m - j) - 1)) := by
  unfold qBinomNum
  congr 1
  refine Finset.prod_bij (fun j _ => m - 1 - j) ?_ ?_ ?_ ?_
  · intro j hj; simp only [Finset.mem_Ico, Finset.mem_range] at hj ⊢; omega
  · intro j₁ hj₁ j₂ hj₂ h; simp only [Finset.mem_Ico] at hj₁ hj₂; omega
  · intro k hk; simp only [Finset.mem_range] at hk
    refine ⟨m - 1 - k, Finset.mem_Ico.mpr (by omega), by omega⟩
  · intro j hj; simp only [Finset.mem_Ico] at hj; congr 2; omega

/-- **Fraction-free $q$-Pascal identity** (zero divisions, arbitrary commutative ring `R`). -/
theorem qBinomNum_pascal {R : Type*} [CommRing R] (q : R) (m r : ℕ)
    (hr1 : 1 ≤ r) (hrm : r ≤ m) :
    qBinomNum q (m + 1) r =
      (q ^ (m + 1) - 1) * (qBinomNum q m (r - 1) + q ^ r * qBinomNum q m r) := by
  set P := ∏ j ∈ Finset.range (r - 1), (q ^ (m - j) - 1)
  set S := ∏ j ∈ Finset.Ico r m, (q ^ (j + 1) - 1)
  have h1 : qBinomNum q m (r - 1) = P * S * (q ^ r - 1) := by
    unfold qBinomNum
    have hIco : Finset.Ico (r - 1) m = insert (r - 1) (Finset.Ico r m) := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
    have hnot : r - 1 ∉ Finset.Ico r m := by simp; omega
    rw [hIco, Finset.prod_insert hnot]
    have hidx : r - 1 + 1 = r := by omega
    rw [hidx]
    ring
  have h2 : qBinomNum q m r = P * S * (q ^ (m + 1 - r) - 1) := by
    unfold qBinomNum
    have hr_eq : r = (r - 1) + 1 := by omega
    have hprod : ∏ j ∈ Finset.range r, (q ^ (m - j) - 1) = P * (q ^ (m + 1 - r) - 1) := by
      conv_lhs => rw [hr_eq, Finset.prod_range_succ]
      have hidx : m - (r - 1) = m + 1 - r := by omega
      rw [hidx]
    rw [hprod]
    ring
  have h3 : qBinomNum q (m + 1) r = (q ^ (m + 1) - 1) * (q ^ (m + 1) - 1) * (P * S) := by
    unfold qBinomNum
    have hprodA : ∏ j ∈ Finset.range r, (q ^ (m + 1 - j) - 1) =
        (q ^ (m + 1) - 1) * P := by
      have hr_eq : r = (r - 1) + 1 := by omega
      rw [hr_eq, Finset.prod_range_succ']
      simp only [Nat.sub_zero, Nat.succ_sub_succ_eq_sub, mul_comm, P]
    have hprodB : ∏ j ∈ Finset.Ico r (m + 1), (q ^ (j + 1) - 1) =
        (q ^ (m + 1) - 1) * S := by
      rw [Finset.prod_Ico_succ_top hrm]
      simp only [S, mul_comm]
    rw [hprodA, hprodB]
    ring
  rw [h1, h2, h3]
  have hexp : q ^ r * q ^ (m + 1 - r) = q ^ (m + 1) := by
    rw [← pow_add]; congr 1; omega
  calc
    (q ^ (m + 1) - 1) * (q ^ (m + 1) - 1) * (P * S)
        = (q ^ (m + 1) - 1) * (P * S * (q ^ r - 1 + (q ^ (m + 1) - q ^ r))) := by ring
    _ = (q ^ (m + 1) - 1) * (P * S * (q ^ r - 1 + (q ^ r * q ^ (m + 1 - r) - q ^ r))) := by
        rw [hexp]
    _ = (q ^ (m + 1) - 1) * (P * S * (q ^ r - 1) + q ^ r * (P * S * (q ^ (m + 1 - r) - 1))) := by
        ring

/-- **Fraction-Free $q$-Binomial Theorem** (zero divisions, arbitrary commutative ring `R`). -/
theorem q_binomial_fraction_free {R : Type*} [CommRing R] (q u v : R) :
    ∀ m : ℕ,
      qDenom q m * ∏ j ∈ Finset.range m, (u - q ^ j * v) =
        ∑ r ∈ Finset.range (m + 1),
          (-1 : R) ^ (m - r) * q ^ ((m - r) * (m - r - 1) / 2) *
            qBinomNum q m r * u ^ r * v ^ (m - r)
  | 0 => by
      simp [qDenom, qBinomNum]
  | m + 1 => by
      rw [qDenom_succ, Finset.prod_range_succ]
      have ih := q_binomial_fraction_free q u v m
      have hmul :
          (q ^ (m + 1) - 1) * qDenom q m *
              ((∏ j ∈ Finset.range m, (u - q ^ j * v)) * (u - q ^ m * v)) =
            (q ^ (m + 1) - 1) * (u - q ^ m * v) *
              (qDenom q m * ∏ j ∈ Finset.range m, (u - q ^ j * v)) := by ring
      rw [hmul, ih]
      let T : ℕ → R := fun r =>
        (-1 : R) ^ (m - r) * q ^ ((m - r) * (m - r - 1) / 2) *
          qBinomNum q m r * u ^ r * v ^ (m - r)
      have hsplit :
          (u - q ^ m * v) * ∑ r ∈ Finset.range (m + 1), T r =
            (∑ r ∈ Finset.range (m + 1), u * T r) -
              (∑ r ∈ Finset.range (m + 1), q ^ m * v * T r) := by
        rw [sub_mul, Finset.mul_sum, Finset.mul_sum]
      rw [mul_assoc, hsplit, mul_sub, Finset.mul_sum, Finset.mul_sum]
      have hsum1 :
          ∑ r ∈ Finset.range (m + 1), (q ^ (m + 1) - 1) * (u * T r) =
            (q ^ (m + 1) - 1) * (u * T m) +
              ∑ r ∈ Finset.Ico 1 (m + 1), (q ^ (m + 1) - 1) * (u * T (r - 1)) := by
        rw [Finset.sum_range_succ, add_comm]
        congr 1
        refine Finset.sum_bij (fun r _ => r + 1) ?_ ?_ ?_ ?_
        · intro r hr; simp only [Finset.mem_range, Finset.mem_Ico] at hr ⊢; omega
        · intro a _ b _ h; omega
        · intro b hb; simp only [Finset.mem_Ico] at hb
          exact ⟨b - 1, Finset.mem_range.mpr (by omega), by omega⟩
        · intro r _; simp
      have hsum2 :
          ∑ r ∈ Finset.range (m + 1), (q ^ (m + 1) - 1) * (q ^ m * v * T r) =
            (q ^ (m + 1) - 1) * (q ^ m * v * T 0) +
              ∑ r ∈ Finset.Ico 1 (m + 1), (q ^ (m + 1) - 1) * (q ^ m * v * T r) := by
        rw [← Nat.Ico_zero_eq_range, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < m + 1)]
      let S : ℕ → R := fun r =>
        (-1 : R) ^ (m + 1 - r) * q ^ ((m + 1 - r) * (m + 1 - r - 1) / 2) *
          qBinomNum q (m + 1) r * u ^ r * v ^ (m + 1 - r)
      have hRHS :
          ∑ r ∈ Finset.range (m + 2), S r =
            S 0 + (∑ r ∈ Finset.Ico 1 (m + 1), S r) + S (m + 1) := by
        rw [Finset.sum_range_succ]
        congr 1
        rw [← Nat.Ico_zero_eq_range, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < m + 1)]
      rw [hsum1, hsum2, hRHS]
      have htop : (q ^ (m + 1) - 1) * (u * T m) = S (m + 1) := by
        simp only [T, S, Nat.sub_self, pow_zero, zero_mul, Nat.zero_div, one_mul, mul_one,
          qBinomNum_self, qDenom_succ]
        rw [pow_succ]
        ring
      have hbot : -((q ^ (m + 1) - 1) * (q ^ m * v * T 0)) = S 0 := by
        simp only [T, S, Nat.sub_zero, pow_zero, mul_one, qBinomNum_zero, qDenom_succ]
        have htri : (m + 1) * m / 2 = m + m * (m - 1) / 2 := by
          cases m with
          | zero => simp
          | succ k =>
              have h1 : (k + 2) * (k + 1) = 2 * (k + 1) + (k + 1) * k := by ring
              rw [h1, Nat.add_sub_cancel, Nat.mul_add_div (by omega)]
        rw [Nat.add_sub_cancel, htri, pow_add, pow_succ, pow_succ]
        ring
      have hmid :
          ∑ r ∈ Finset.Ico 1 (m + 1),
              ((q ^ (m + 1) - 1) * (u * T (r - 1)) -
                (q ^ (m + 1) - 1) * (q ^ m * v * T r)) =
            ∑ r ∈ Finset.Ico 1 (m + 1), S r := by
        refine Finset.sum_congr rfl ?_
        intro r hr
        simp only [Finset.mem_Ico] at hr
        have hr1 : 1 ≤ r := hr.1
        have hrm : r ≤ m := by omega
        have hsub1 : m - (r - 1) = m + 1 - r := by omega
        have hsub2 : m + 1 - r = (m - r) + 1 := by omega
        have htri : m + (m - r) * (m - r - 1) / 2 =
            (m + 1 - r) * (m + 1 - r - 1) / 2 + r := by
          set d := m - r
          have hm1 : m + 1 - r = d + 1 := by omega
          rw [hm1, Nat.add_sub_cancel]
          have h2 : (d + 1) * d = 2 * d + d * (d - 1) := by
            cases d with
            | zero => simp
            | succ t =>
                rw [Nat.add_sub_cancel]
                ring
          have hdiv : (d + 1) * d / 2 = d + d * (d - 1) / 2 := by
            rw [h2, Nat.mul_add_div (by omega)]
          rw [hdiv]
          omega
        simp only [T, S]
        rw [qBinomNum_pascal q m r hr1 hrm, hsub1]
        have hu : u * u ^ (r - 1) = u ^ r := by
          conv_rhs => rw [show r = (r - 1) + 1 by omega, pow_succ']
        have hv : v * v ^ (m - r) = v ^ (m + 1 - r) := by
          rw [hsub2, pow_succ']
        have hneg : (-1 : R) ^ (m + 1 - r) = -((-1 : R) ^ (m - r)) := by
          rw [hsub2, pow_succ]; ring
        have hqpow : q ^ m * q ^ ((m - r) * (m - r - 1) / 2) =
            q ^ ((m + 1 - r) * (m + 1 - r - 1) / 2) * q ^ r := by
          rw [← pow_add, ← pow_add, htri]
        calc
          (q ^ (m + 1) - 1) *
              (u * ((-1 : R) ^ (m + 1 - r) * q ^ ((m + 1 - r) * (m + 1 - r - 1) / 2) *
                qBinomNum q m (r - 1) * u ^ (r - 1) * v ^ (m + 1 - r))) -
            (q ^ (m + 1) - 1) *
              (q ^ m * v * ((-1 : R) ^ (m - r) * q ^ ((m - r) * (m - r - 1) / 2) *
                qBinomNum q m r * u ^ r * v ^ (m - r)))
              = (q ^ (m + 1) - 1) * ((-1 : R) ^ (m + 1 - r) *
                  q ^ ((m + 1 - r) * (m + 1 - r - 1) / 2) * qBinomNum q m (r - 1) *
                  (u * u ^ (r - 1)) * v ^ (m + 1 - r)) -
                (q ^ (m + 1) - 1) * ((-1 : R) ^ (m - r) *
                  (q ^ m * q ^ ((m - r) * (m - r - 1) / 2)) * qBinomNum q m r *
                  u ^ r * (v * v ^ (m - r))) := by ring
          _ = (q ^ (m + 1) - 1) * ((-1 : R) ^ (m + 1 - r) *
                  q ^ ((m + 1 - r) * (m + 1 - r - 1) / 2) * qBinomNum q m (r - 1) *
                  u ^ r * v ^ (m + 1 - r)) -
                (q ^ (m + 1) - 1) * ((-1 : R) ^ (m - r) *
                  (q ^ ((m + 1 - r) * (m + 1 - r - 1) / 2) * q ^ r) * qBinomNum q m r *
                  u ^ r * v ^ (m + 1 - r)) := by rw [hu, hv, hqpow]
          _ = (-1 : R) ^ (m + 1 - r) * q ^ ((m + 1 - r) * (m + 1 - r - 1) / 2) *
                ((q ^ (m + 1) - 1) * (qBinomNum q m (r - 1) + q ^ r * qBinomNum q m r)) *
                u ^ r * v ^ (m + 1 - r) := by rw [hneg]; ring
      rw [← hmid, Finset.sum_sub_distrib, ← htop, ← hbot]
      ring

/-- The Chirp-$z$ input coefficient `chirpA m r ∈ ℤ[X]` for `0 ≤ r ≤ m` (and `0` for `r > m`). -/
noncomputable def chirpA (m r : ℕ) : Polynomial ℤ :=
  if r ≤ m then
    (-1 : Polynomial ℤ) ^ (m - r) * (4 : Polynomial ℤ) ^ ((m - r) * (m - r - 1) / 2) *
      qBinomNum (4 : Polynomial ℤ) m r *
      ((2 : Polynomial ℤ) ^ m) ^ (m * m - (m - r) * (m - r)) *
      (Polynomial.X ^ 2) ^ r
  else 0

/-- The Chirp-$z$ kernel coefficient `chirpB m s ∈ ℤ[X]` for `s < 2 * m` (and `0` otherwise). -/
noncomputable def chirpB (m s : ℕ) : Polynomial ℤ :=
  if s < 2 * m then ((2 : Polynomial ℤ) ^ m) ^ (s * s) else 0

/-- Exact Bluestein Chirp-$z$ middle-product identity over `ℤ[X]`. -/
theorem chirp_middle_product_eq (m i : ℕ) (hi : i < m) :
    ∑ r ∈ Finset.range (m + 1), chirpA m r * chirpB m (i + m - r) =
      ((2 : Polynomial ℤ) ^ m) ^ (m * m + i * i) * qDenom (4 : Polynomial ℤ) m *
        ∏ j ∈ Finset.range m, (Polynomial.X ^ 2 - (4 : Polynomial ℤ) ^ (i * m + j)) := by
  have hq :
      qDenom (4 : Polynomial ℤ) m *
          ∏ j ∈ Finset.range m,
            (Polynomial.X ^ 2 - (4 : Polynomial ℤ) ^ j * (((2 : Polynomial ℤ) ^ m) ^ (2 * i))) =
        ∑ r ∈ Finset.range (m + 1),
          (-1 : Polynomial ℤ) ^ (m - r) * (4 : Polynomial ℤ) ^ ((m - r) * (m - r - 1) / 2) *
            qBinomNum (4 : Polynomial ℤ) m r * (Polynomial.X ^ 2) ^ r *
            (((2 : Polynomial ℤ) ^ m) ^ (2 * i)) ^ (m - r) :=
    q_binomial_fraction_free (4 : Polynomial ℤ) (Polynomial.X ^ 2)
      (((2 : Polynomial ℤ) ^ m) ^ (2 * i)) m
  have hprod_eq :
      ∏ j ∈ Finset.range m, (Polynomial.X ^ 2 - (4 : Polynomial ℤ) ^ (i * m + j)) =
        ∏ j ∈ Finset.range m,
          (Polynomial.X ^ 2 - (4 : Polynomial ℤ) ^ j * (((2 : Polynomial ℤ) ^ m) ^ (2 * i))) := by
    refine Finset.prod_congr rfl ?_
    intro j _
    congr 1
    have h4 : (4 : Polynomial ℤ) = (2 : Polynomial ℤ) ^ 2 := by norm_num
    rw [h4, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    ring
  rw [hprod_eq, mul_assoc, hq, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro r hr
  rw [Finset.mem_range] at hr
  have hrm : r ≤ m := by omega
  have hs : i + m - r < 2 * m := by omega
  simp only [chirpA, chirpB, hrm, hs, ↓reduceIte]
  have hexp :
      m * m - (m - r) * (m - r) + (i + m - r) * (i + m - r) =
        m * m + i * i + 2 * i * (m - r) := by
    have hle : (m - r) * (m - r) ≤ m * m := Nat.mul_le_mul (Nat.sub_le m r) (Nat.sub_le m r)
    have h1 : i + m - r = i + (m - r) := by omega
    rw [h1]
    zify [hle]
    ring
  have hpow :
      ((2 : Polynomial ℤ) ^ m) ^ (m * m - (m - r) * (m - r)) *
          ((2 : Polynomial ℤ) ^ m) ^ ((i + m - r) * (i + m - r)) =
        ((2 : Polynomial ℤ) ^ m) ^ (m * m + i * i) *
          (((2 : Polynomial ℤ) ^ m) ^ (2 * i)) ^ (m - r) := by
    rw [← pow_add, hexp, pow_add]
    congr 1
    rw [pow_mul]
  calc
    (-1 : Polynomial ℤ) ^ (m - r) * (4 : Polynomial ℤ) ^ ((m - r) * (m - r - 1) / 2) *
        qBinomNum (4 : Polynomial ℤ) m r *
        ((2 : Polynomial ℤ) ^ m) ^ (m * m - (m - r) * (m - r)) *
        (Polynomial.X ^ 2) ^ r *
        ((2 : Polynomial ℤ) ^ m) ^ ((i + m - r) * (i + m - r))
        = (-1 : Polynomial ℤ) ^ (m - r) * (4 : Polynomial ℤ) ^ ((m - r) * (m - r - 1) / 2) *
            qBinomNum (4 : Polynomial ℤ) m r * (Polynomial.X ^ 2) ^ r *
            (((2 : Polynomial ℤ) ^ m) ^ (m * m - (m - r) * (m - r)) *
              ((2 : Polynomial ℤ) ^ m) ^ ((i + m - r) * (i + m - r))) := by ring
    _ = (-1 : Polynomial ℤ) ^ (m - r) * (4 : Polynomial ℤ) ^ ((m - r) * (m - r - 1) / 2) *
            qBinomNum (4 : Polynomial ℤ) m r * (Polynomial.X ^ 2) ^ r *
            (((2 : Polynomial ℤ) ^ m) ^ (m * m + i * i) *
              (((2 : Polynomial ℤ) ^ m) ^ (2 * i)) ^ (m - r)) := by rw [hpow]
    _ = ((2 : Polynomial ℤ) ^ m) ^ (m * m + i * i) *
          ((-1 : Polynomial ℤ) ^ (m - r) * (4 : Polynomial ℤ) ^ ((m - r) * (m - r - 1) / 2) *
            qBinomNum (4 : Polynomial ℤ) m r * (Polynomial.X ^ 2) ^ r *
            (((2 : Polynomial ℤ) ^ m) ^ (2 * i)) ^ (m - r)) := by ring

/-- Root-count theorem for the Chirp-$z$ output polynomial:
for any `C > 0`, `C * X * ∏_{n < m^2} (X^2 - 4^n)` is nonzero and has at least
`2 * m^2 + 1` distinct integer roots `{0, ±2^0, ..., ±2^(m^2 - 1)}`. -/
theorem chirp_poly_root_count (m : ℕ) (C : ℤ) (hC : 0 < C) :
    let F : Polynomial ℤ :=
      Polynomial.C C * Polynomial.X *
        ∏ n ∈ Finset.range (m * m), (Polynomial.X ^ 2 - (4 : Polynomial ℤ) ^ n)
    F ≠ 0 ∧ 2 * (m * m) + 1 ≤ intRootCount F := by
  intro F
  let posSet : Finset ℤ := (Finset.range (m * m)).image (fun n : ℕ => (2 : ℤ) ^ n)
  let negSet : Finset ℤ := (Finset.range (m * m)).image (fun n : ℕ => -((2 : ℤ) ^ n))
  let S : Finset ℤ := insert 0 (posSet ∪ negSet)
  have hpos_inj : Function.Injective (fun n : ℕ => (2 : ℤ) ^ n) := by
    intro a b hab
    have hnat : (2 : ℕ) ^ a = (2 : ℕ) ^ b := by
      exact_mod_cast (show (((2 : ℕ) ^ a : ℕ) : ℤ) = (((2 : ℕ) ^ b : ℕ) : ℤ) by simpa using hab)
    exact Nat.pow_right_injective (by omega : 2 ≤ 2) hnat
  have hneg_inj : Function.Injective (fun n : ℕ => -((2 : ℤ) ^ n)) := by
    intro a b hab
    exact hpos_inj (neg_inj.mp hab)
  have hpos_card : posSet.card = m * m := by
    rw [Finset.card_image_of_injective _ hpos_inj, Finset.card_range]
  have hneg_card : negSet.card = m * m := by
    rw [Finset.card_image_of_injective _ hneg_inj, Finset.card_range]
  have hdisj : Disjoint posSet negSet := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [posSet, negSet, Finset.mem_image, Finset.mem_range] at ha hb
    rcases ha with ⟨i, _, rfl⟩
    rcases hb with ⟨j, _, hj⟩
    have h1 : (0 : ℤ) < (2 : ℤ) ^ i := by positivity
    have h2 : (0 : ℤ) < (2 : ℤ) ^ j := by positivity
    omega
  have h0not : (0 : ℤ) ∉ posSet ∪ negSet := by
    simp only [Finset.mem_union, posSet, negSet, Finset.mem_image, Finset.mem_range]
    rintro (⟨i, _, hi⟩ | ⟨i, _, hi⟩) <;>
    · have : (0 : ℤ) < (2 : ℤ) ^ i := by positivity
      omega
  have hScard : S.card = 2 * (m * m) + 1 := by
    rw [Finset.card_insert_of_notMem h0not, Finset.card_union_of_disjoint hdisj,
      hpos_card, hneg_card]
    ring
  have hFne : F ≠ 0 := by
    intro hzero
    have heval : F.eval 3 = 0 := by rw [hzero]; simp
    have hne : F.eval 3 ≠ 0 := by
      simp only [F, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
        Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_ofNat]
      refine mul_ne_zero (mul_ne_zero (by omega) (by omega)) ?_
      rw [Finset.prod_ne_zero_iff]
      intro n _
      cases n with
      | zero => norm_num
      | succ k =>
          have h4 : (4 : ℤ) ^ (k + 1) % 2 = 0 := by rw [pow_succ]; omega
          omega
    exact hne heval
  have hsub : S ⊆ intRootSet F := by
    intro a ha
    rw [mem_intRootSet_iff]
    refine ⟨hFne, ?_⟩
    simp only [Polynomial.IsRoot, F, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_ofNat]
    simp only [S, Finset.mem_insert, Finset.mem_union, posSet, negSet, Finset.mem_image,
      Finset.mem_range] at ha
    rcases ha with rfl | ⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩
    · simp
    · have hzero : ∏ k ∈ Finset.range (m * m), (((2 : ℤ) ^ n) ^ 2 - (4 : ℤ) ^ k) = 0 := by
        refine Finset.prod_eq_zero (Finset.mem_range.mpr hn) ?_
        have h4 : (4 : ℤ) = (2 : ℤ) ^ 2 := by norm_num
        rw [h4, ← pow_mul, ← pow_mul, mul_comm, sub_self]
      rw [hzero, mul_zero]
    · have hzero : ∏ k ∈ Finset.range (m * m), ((-((2 : ℤ) ^ n)) ^ 2 - (4 : ℤ) ^ k) = 0 := by
        refine Finset.prod_eq_zero (Finset.mem_range.mpr hn) ?_
        have h4 : (4 : ℤ) = (2 : ℤ) ^ 2 := by norm_num
        rw [neg_sq, h4, ← pow_mul, ← pow_mul, mul_comm, sub_self]
      rw [hzero, mul_zero]
  exact ⟨hFne, by rw [← hScard]; exact Finset.card_le_card hsub⟩

/-- Product of the `m` middle-product outputs (each scaled by `S_out > 0`) equals
`C_total * X * ∏_{n < m^2} (X^2 - 4^n)` for a strictly positive integer `C_total > 0`. -/
theorem chirp_final_poly_eq (m : ℕ) (S_out : ℤ) (hS : 0 < S_out) :
    ∃ C : ℤ, 0 < C ∧
      Polynomial.X *
          (∏ i ∈ Finset.range m,
            (Polynomial.C S_out *
              ∑ r ∈ Finset.range (m + 1), chirpA m r * chirpB m (i + m - r))) =
        Polynomial.C C * Polynomial.X *
          ∏ n ∈ Finset.range (m * m), (Polynomial.X ^ 2 - (4 : Polynomial ℤ) ^ n) := by
  let D : ℤ := qDenom (4 : ℤ) m
  have hDpos : 0 < D := by
    dsimp [D, qDenom]
    refine Finset.prod_pos ?_
    intro j _
    have h4 : (4 : ℤ) ≤ (4 : ℤ) ^ (j + 1) := by
      calc (4 : ℤ) = 4 ^ 1 := by norm_num
        _ ≤ 4 ^ (j + 1) := by gcongr; norm_num; omega
    omega
  have hDcast : (qDenom (4 : Polynomial ℤ) m) = Polynomial.C D := by
    simp only [D, qDenom, map_prod, map_sub, map_pow, map_ofNat, map_one]
  let c_i : ℕ → ℤ := fun i => S_out * ((2 : ℤ) ^ m) ^ (m * m + i * i) * D
  have hci_pos : ∀ i, 0 < c_i i := by
    intro i
    have h2 : (0 : ℤ) < ((2 : ℤ) ^ m) ^ (m * m + i * i) := by positivity
    exact mul_pos (mul_pos hS h2) hDpos
  refine ⟨∏ i ∈ Finset.range m, c_i i, Finset.prod_pos (fun i _ => hci_pos i), ?_⟩
  have hstep :
      ∏ i ∈ Finset.range m,
          (Polynomial.C S_out *
            ∑ r ∈ Finset.range (m + 1), chirpA m r * chirpB m (i + m - r)) =
        Polynomial.C (∏ i ∈ Finset.range m, c_i i) *
          ∏ i ∈ Finset.range m,
            ∏ j ∈ Finset.range m, (Polynomial.X ^ 2 - (4 : Polynomial ℤ) ^ (i * m + j)) := by
    rw [map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl ?_
    intro i hi
    rw [chirp_middle_product_eq m i (Finset.mem_range.mp hi), hDcast]
    simp only [c_i, map_mul, map_pow, map_ofNat]
    ring
  rw [hstep]
  have hdouble :
      ∏ i ∈ Finset.range m,
          ∏ j ∈ Finset.range m, (Polynomial.X ^ 2 - (4 : Polynomial ℤ) ^ (i * m + j)) =
        ∏ n ∈ Finset.range (m * m), (Polynomial.X ^ 2 - (4 : Polynomial ℤ) ^ n) := by
    rw [← Finset.prod_product']
    refine Finset.prod_bij (fun p _ => p.1 * m + p.2) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_product, Finset.mem_range] at hp ⊢
      nlinarith
    · intro p₁ hp₁ p₂ hp₂ h
      simp only [Finset.mem_product, Finset.mem_range] at hp₁ hp₂
      have hdiv : p₁.1 = p₂.1 := by
        have h1 : (p₁.1 * m + p₁.2) / m = p₁.1 := by
          rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hp₁.2, add_zero]
        have h2 : (p₂.1 * m + p₂.2) / m = p₂.1 := by
          rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hp₂.2, add_zero]
        rw [← h1, ← h2, h]
      have hrem : p₁.2 = p₂.2 := by nlinarith
      exact Prod.ext hdiv hrem
    · intro n hn
      rw [Finset.mem_range] at hn
      have hmpos : 0 < m := by
        rcases Nat.eq_zero_or_pos m with rfl | hpos
        · simp at hn
        · exact hpos
      refine ⟨(n / m, n % m), ?_, ?_⟩
      · simp only [Finset.mem_product, Finset.mem_range]
        exact ⟨Nat.div_lt_of_lt_mul hn, Nat.mod_lt n hmpos⟩
      · simpa [Nat.mul_comm] using Nat.div_add_mod n m
    · intro _ _; rfl
  rw [hdouble]
  ring

/-! ## 3. Linear-Gate Preparation of `chirpA m` and `chirpB m` -/

theorem sum_rev_odds_eq (m r : ℕ) (hrm : r ≤ m) :
    ∑ k ∈ Finset.range r, (2 * (m - 1 - k) + 1) = m * m - (m - r) * (m - r) := by
  induction r with
  | zero => simp
  | succ r ih =>
      have hrm' : r ≤ m := by omega
      rw [Finset.sum_range_succ, ih hrm']
      have h1 : (m - r) * (m - r) ≤ m * m := Nat.mul_le_mul (Nat.sub_le m r) (Nat.sub_le m r)
      have h2 : (m - (r + 1)) * (m - (r + 1)) ≤ m * m :=
        Nat.mul_le_mul (Nat.sub_le m (r + 1)) (Nat.sub_le m (r + 1))
      have h3 : m - r = (m - (r + 1)) + 1 := by omega
      have h4 : m - 1 - r = m - (r + 1) := by omega
      zify [h1, h2]
      rw [h4]
      have h3z : ((m - r : ℕ) : ℤ) = ((m - (r + 1) : ℕ) : ℤ) + 1 := by exact_mod_cast h3
      rw [h3z]
      ring

theorem prod_neg_four_pow (d : ℕ) :
    ∏ j ∈ Finset.range d, -((4 : Polynomial ℤ) ^ j) =
      (-1 : Polynomial ℤ) ^ d * (4 : Polynomial ℤ) ^ (d * (d - 1) / 2) := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [Finset.prod_range_succ, ih]
      have htri : (d + 1) * d / 2 = d * (d - 1) / 2 + d := by
        cases d with
        | zero => simp
        | succ t =>
            have h1 : (t + 2) * (t + 1) = (t + 1) * t + 2 * (t + 1) := by ring
            rw [h1, Nat.add_sub_cancel, Nat.add_mul_div_left _ _ (by omega)]
      rw [Nat.add_sub_cancel, htri, pow_add, pow_succ]
      ring

/-- Build `0, 2, 4, X^2` from `{1, X}` in `4` gates. -/
theorem canBuild_chirp_basics :
    CanBuild ({(1 : Polynomial ℤ), Polynomial.X} : Set (Polynomial ℤ)) 4
      ({(0 : Polynomial ℤ), (2 : Polynomial ℤ), (4 : Polynomial ℤ), Polynomial.X ^ 2} :
        Set (Polynomial ℤ)) := by
  have h0 : CanBuild ({(1 : Polynomial ℤ), Polynomial.X} : Set (Polynomial ℤ)) 1 {0} := by
    have h := canBuild_sub (1 : Polynomial ℤ) 1
    refine canBuild_mono_out (by simp)
      (canBuild_mono_in (by intro x hx; rcases hx with rfl | rfl <;> simp) h)
  have h2 : CanBuild ({(1 : Polynomial ℤ), Polynomial.X} : Set (Polynomial ℤ)) 1 {2} := by
    have h := canBuild_add (1 : Polynomial ℤ) 1
    refine canBuild_mono_out
      (by intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx; norm_num)
      (canBuild_mono_in (by intro x hx; rcases hx with rfl | rfl <;> simp) h)
  have h4 : CanBuild ({(2 : Polynomial ℤ)} : Set (Polynomial ℤ)) 1 {4} := by
    have h := canBuild_mul (2 : Polynomial ℤ) 2
    refine canBuild_mono_out
      (by intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx; norm_num)
      (canBuild_mono_in (by intro x hx; rcases hx with rfl | rfl <;> simp) h)
  have hx2 : CanBuild ({Polynomial.X} : Set (Polynomial ℤ)) 1 {Polynomial.X ^ 2} := by
    have h := canBuild_mul Polynomial.X Polynomial.X
    refine canBuild_mono_out
      (by intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx; simp [sq])
      (canBuild_mono_in (by intro x hx; rcases hx with rfl | rfl <;> simp) h)
  have s1 := canBuild_trans h0 (by intro x hx; rcases hx with rfl | rfl <;> simp) h2
  have s2 := canBuild_trans s1 (by intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx; simp) h4
  have s3 := canBuild_trans s2 (by intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx; simp) hx2
  refine canBuild_mono_out ?_ s3
  intro x hx
  rcases hx with rfl | rfl | rfl | rfl <;> simp

/-- All Chirp-$z$ input wires `{0} ∪ {chirpA m r | r ≤ m} ∪ {chirpB m s | s < 2m}`
can be built from `{1, X}` in `16 * m + 12` gates for every `m ≥ 1`. -/
theorem canBuild_chirp_inputs (m : ℕ) (_hm : 1 ≤ m) :
    CanBuild ({(1 : Polynomial ℤ), Polynomial.X} : Set (Polynomial ℤ)) (16 * m + 12)
      ({(0 : Polynomial ℤ)} ∪ (⋃ r < m + 1, {chirpA m r}) ∪ (⋃ s < 2 * m, {chirpB m s})) := by
  let w : Polynomial ℤ := (2 : Polynomial ℤ) ^ m
  -- Stage 1 (4 gates): {0, 2, 4, X^2}
  have h1 := canBuild_chirp_basics
  -- Stage 2 (m gates): {2^j | j ≤ m} (gives w = 2^m)
  have h2 := canBuild_powers m (2 : Polynomial ℤ)
  -- Stage 3 (m gates): {4^j | j ≤ m}
  have h3 := canBuild_powers m (4 : Polynomial ℤ)
  -- Stage 4 (m gates): {(X^2)^r | r ≤ m}
  have h4 := canBuild_powers m (Polynomial.X ^ 2)
  -- Stage 5 (m gates): {4^(m - j) - 1 | j < m}
  have h5 : CanBuild ({(1 : Polynomial ℤ)} ∪ ⋃ j < m + 1, {(4 : Polynomial ℤ) ^ j}) m
      (⋃ j < m, {(4 : Polynomial ℤ) ^ (m - j) - 1}) := by
    have h := canBuild_fin_union (n := m) (d := 1)
      (S := {(1 : Polynomial ℤ)} ∪ ⋃ j < m + 1, {(4 : Polynomial ℤ) ^ j})
      (T := fun j => {(4 : Polynomial ℤ) ^ (m - j) - 1}) (by
        intro j hj
        refine canBuild_mono_in ?_ (canBuild_sub ((4 : Polynomial ℤ) ^ (m - j)) 1)
        intro x hx
        rcases hx with rfl | rfl
        · right; simp only [Set.mem_iUnion, exists_prop]; exact ⟨m - j, by omega, rfl⟩
        · left; rfl)
    simpa using h
  -- Stage 6 (m gates): prefix products P_k = ∏_{j < k} (4^(m - j) - 1) for k ≤ m
  have h6 := canBuild_prefix_prods m (fun j => (4 : Polynomial ℤ) ^ (m - j) - 1)
  -- Stage 7 (m gates): {-4^j | j < m}
  have h7 : CanBuild ({(0 : Polynomial ℤ)} ∪ ⋃ j < m + 1, {(4 : Polynomial ℤ) ^ j}) m
      (⋃ j < m, {-((4 : Polynomial ℤ) ^ j)}) := by
    have h := canBuild_fin_union (n := m) (d := 1)
      (S := {(0 : Polynomial ℤ)} ∪ ⋃ j < m + 1, {(4 : Polynomial ℤ) ^ j})
      (T := fun j => {-((4 : Polynomial ℤ) ^ j)}) (by
        intro j hj
        have hsub := canBuild_sub (0 : Polynomial ℤ) ((4 : Polynomial ℤ) ^ j)
        refine canBuild_mono_out (by intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx; simp)
          (canBuild_mono_in ?_ hsub)
        intro x hx
        rcases hx with rfl | rfl
        · left; rfl
        · right; simp only [Set.mem_iUnion, exists_prop]; exact ⟨j, by omega, rfl⟩)
    simpa using h
  -- Stage 8 (m gates): signed 4-triangle products ∏_{j < d} (-4^j) = (-1)^d * 4^(C(d,2))
  have h8 := canBuild_prefix_prods m (fun j => -((4 : Polynomial ℤ) ^ j))
  -- Stage 9 (4*m + 1 gates): w^(s*s) and w^(2*s+1) for s ≤ 2*m
  have h9 := canBuild_sq_and_odd_powers (2 * m) w
  -- Stage 10 (m gates): W_r = ∏_{k < r} w^(2*(m-1-k)+1) = w^(m^2 - (m-r)^2) for r ≤ m
  have h10 := canBuild_prefix_prods m (fun k => w ^ (2 * (m - 1 - k) + 1))
  -- Compose stages 1..10
  have c12 := canBuild_trans h1 (by intro x hx; rcases hx with rfl | rfl <;> simp) h2
  have c13 := canBuild_trans c12 (by intro x hx; rcases hx with rfl | rfl <;> simp) h3
  have c14 := canBuild_trans c13 (by intro x hx; rcases hx with rfl | rfl <;> simp) h4
  have c15 := canBuild_trans c14 (by
    intro x hx; rcases hx with rfl | hx'
    · left; simp
    · right; left; right; exact hx') h5
  have c16 := canBuild_trans c15 (by
    intro x hx; rcases hx with rfl | hx'
    · left; simp
    · right; right; exact hx') h6
  have c17 := canBuild_trans c16 (by
    intro x hx; rcases hx with rfl | hx'
    · right; left; left; left; left; left; simp
    · right; left; left; left; right; exact hx') h7
  have c18 := canBuild_trans c17 (by
    intro x hx; rcases hx with rfl | hx'
    · left; simp
    · right; right; exact hx') h8
  have c19 := canBuild_trans c18 (by
    intro x hx; rcases hx with rfl | rfl
    · left; simp
    · right; left; left; left; left; left; left; right
      simp only [Set.mem_iUnion, exists_prop]
      exact ⟨m, Nat.lt_succ_self m, rfl⟩) h9
  have c110 := canBuild_trans c19 (by
    intro x hx; rcases hx with rfl | hx'
    · left; simp
    · right; right; right
      simp only [Set.mem_iUnion, exists_prop] at hx' ⊢
      rcases hx' with ⟨k, hk, hxk⟩
      exact ⟨m - 1 - k, by omega, hxk⟩) h10
  -- Stage 11 (4*(m+1) gates): assemble chirpA m r for r ≤ m
  -- Each chirpA m r is the product of 5 available wires:
  --   f1 = ∏_{j < m - r} (-4^j)            [from Stage 8]
  --   f2 = ∏_{j < r} (4^(m - j) - 1)       [from Stage 6]
  --   f3 = ∏_{j < m - r} (4^(m - j) - 1)   [from Stage 6]
  --   f4 = ∏_{k < r} w^(2*(m - 1 - k) + 1) [from Stage 10]
  --   f5 = (X^2)^r                         [from Stage 4]
  have hmul5 : ∀ a b c d e : Polynomial ℤ,
      CanBuild ({a, b, c, d, e} : Set (Polynomial ℤ)) 4 {a * b * c * d * e} := by
    intro a b c d e
    have m1 := canBuild_mul a b
    have m2 := canBuild_mul (a * b) c
    have m3 := canBuild_mul (a * b * c) d
    have m4 := canBuild_mul (a * b * c * d) e
    have s1 := canBuild_mono_in (S₂ := {a, b, c, d, e})
      (by intro x hx; rcases hx with rfl | rfl <;> simp) m1
    have s2 := canBuild_trans s1 (by intro x hx; rcases hx with rfl | rfl <;> simp) m2
    have s3 := canBuild_trans s2 (by intro x hx; rcases hx with rfl | rfl <;> simp) m3
    have s4 := canBuild_trans s3 (by intro x hx; rcases hx with rfl | rfl <;> simp) m4
    exact canBuild_mono_out (fun x hx => Or.inr hx) s4
  -- Assemble all m + 1 entries of chirpA m
  set U10 : Set (Polynomial ℤ) :=
    ({(1 : Polynomial ℤ), Polynomial.X} : Set (Polynomial ℤ)) ∪
      ((((((((({(0 : Polynomial ℤ), (2 : Polynomial ℤ), (4 : Polynomial ℤ), Polynomial.X ^ 2} ∪
        ⋃ i < m + 1, {(2 : Polynomial ℤ) ^ i}) ∪
        ⋃ i < m + 1, {(4 : Polynomial ℤ) ^ i}) ∪
        ⋃ i < m + 1, {(Polynomial.X ^ 2) ^ i}) ∪
        ⋃ j < m, {(4 : Polynomial ℤ) ^ (m - j) - 1}) ∪
        ⋃ k < m + 1, {∏ j ∈ Finset.range k, ((4 : Polynomial ℤ) ^ (m - j) - 1)}) ∪
        ⋃ j < m, {-((4 : Polynomial ℤ) ^ j)}) ∪
        ⋃ k < m + 1, {∏ j ∈ Finset.range k, -((4 : Polynomial ℤ) ^ j)}) ∪
        ((⋃ s < 2 * m + 1, {w ^ (s * s)}) ∪ (⋃ s < 2 * m + 1, {w ^ (2 * s + 1)}))) ∪
        ⋃ k < m + 1, {∏ j ∈ Finset.range k, w ^ (2 * (m - 1 - j) + 1)})
  have h11 : CanBuild U10 ((m + 1) * 4) (⋃ r < m + 1, {chirpA m r}) := by
    refine canBuild_fin_union (n := m + 1) (d := 4) (S := U10) (T := fun r => {chirpA m r}) ?_
    intro r hr
    have hrm : r ≤ m := by omega
    let f1 : Polynomial ℤ := ∏ j ∈ Finset.range (m - r), -((4 : Polynomial ℤ) ^ j)
    let f2 : Polynomial ℤ := ∏ j ∈ Finset.range r, ((4 : Polynomial ℤ) ^ (m - j) - 1)
    let f3 : Polynomial ℤ := ∏ j ∈ Finset.range (m - r), ((4 : Polynomial ℤ) ^ (m - j) - 1)
    let f4 : Polynomial ℤ := ∏ k ∈ Finset.range r, w ^ (2 * (m - 1 - k) + 1)
    let f5 : Polynomial ℤ := (Polynomial.X ^ 2) ^ r
    have hprod_eq : f1 * f2 * f3 * f4 * f5 = chirpA m r := by
      simp only [f1, f2, f3, f4, f5, chirpA, hrm, ↓reduceIte, prod_neg_four_pow,
        qBinomNum_eq_prefix_mul (4 : Polynomial ℤ) m r hrm]
      have hwprod : ∏ k ∈ Finset.range r, w ^ (2 * (m - 1 - k) + 1) =
          w ^ (m * m - (m - r) * (m - r)) := by
        rw [Finset.prod_pow_eq_pow_sum, sum_rev_odds_eq m r hrm]
      rw [hwprod]
      dsimp only [w]
      ring
    refine canBuild_mono_out (T₂ := {f1 * f2 * f3 * f4 * f5})
      (by intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx; rw [← hprod_eq]; rfl) ?_
    refine canBuild_mono_in ?_ (hmul5 f1 f2 f3 f4 f5)
    intro x hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · right; left; left; right
      simp only [Set.mem_iUnion, exists_prop]; exact ⟨m - r, by omega, rfl⟩
    · right; left; left; left; left; right
      simp only [Set.mem_iUnion, exists_prop]; exact ⟨r, by omega, rfl⟩
    · right; left; left; left; left; right
      simp only [Set.mem_iUnion, exists_prop]; exact ⟨m - r, by omega, rfl⟩
    · right; right
      simp only [Set.mem_iUnion, exists_prop]; exact ⟨r, by omega, rfl⟩
    · right; left; left; left; left; left; left; right
      simp only [Set.mem_iUnion, exists_prop]; exact ⟨r, by omega, rfl⟩
  have cAll := canBuild_trans c110 Set.Subset.rfl h11
  have cOut := canBuild_mono_out (T₁ := {(0 : Polynomial ℤ)} ∪ (⋃ r < m + 1, {chirpA m r}) ∪ (⋃ s < 2 * m, {chirpB m s})) (by
    intro x hx
    rcases hx with (hx0 | hxA) | hxB
    · rw [Set.mem_singleton_iff] at hx0; subst hx0
      left; left; left; left; left; left; left; left; left; left; simp
    · exact Or.inr hxA
    · simp only [Set.mem_iUnion, exists_prop, Set.mem_singleton_iff] at hxB
      rcases hxB with ⟨s, hs, rfl⟩
      simp only [chirpB, hs, ↓reduceIte]
      left; left; right; left
      simp only [Set.mem_iUnion, exists_prop]
      exact ⟨s, by omega, rfl⟩) cAll
  exact canBuild_mono_cost (by omega) cOut

/-- **Master Reduction from Scaled Middle-Product Engine to `zMaxGe`:**
If `Δ_mul` gates compute `{S_out * ∑_{r=0}^m chirpA m r * chirpB m (i + m - r) | i < m}`
(for some positive integer `S_out > 0`) from `{0} ∪ {chirpA m r | r ≤ m} ∪ {chirpB m s | s < 2m}`,
then `zMaxGe (17 * m + Δ_mul + 14) (2 * (m * m) + 1)`. -/
theorem zMaxGe_of_chirp_engine {m Δ_mul : ℕ} (hm : 1 ≤ m) (S_out : ℤ) (hS : 0 < S_out)
    (hmul :
      CanBuild
        ({(0 : Polynomial ℤ)} ∪ (⋃ r < m + 1, {chirpA m r}) ∪ (⋃ s < 2 * m, {chirpB m s}))
        Δ_mul
        (⋃ i < m, {Polynomial.C S_out *
          ∑ r ∈ Finset.range (m + 1), chirpA m r * chirpB m (i + m - r)})) :
    zMaxGe (17 * m + Δ_mul + 14) (2 * (m * m) + 1) := by
  let V : ℕ → Polynomial ℤ := fun i =>
    Polynomial.C S_out * ∑ r ∈ Finset.range (m + 1), chirpA m r * chirpB m (i + m - r)
  have h1 := canBuild_chirp_inputs m hm
  have h2 := canBuild_trans h1 Set.subset_union_right hmul
  have hprod := canBuild_fin_prod m V
  have h3 := canBuild_trans h2 (by
    intro x hx
    rcases hx with rfl | hx'
    · left; simp
    · right; right; exact hx') hprod
  have hfinal := canBuild_mul Polynomial.X (∏ i ∈ Finset.range m, V i)
  have h4 := canBuild_trans h3 (by
    intro x hx
    rcases hx with rfl | rfl
    · left; simp
    · right; right; rfl) hfinal
  have hcomp :
      Computes (0 + (16 * m + 12 + Δ_mul + m + 1))
        ({(1 : Polynomial ℤ), Polynomial.X} ∪
          (((({(0 : Polynomial ℤ)} ∪ (⋃ r < m + 1, {chirpA m r}) ∪ (⋃ s < 2 * m, {chirpB m s})) ∪
            ⋃ i < m, {V i}) ∪ {∏ i ∈ Finset.range m, V i}) ∪
            {Polynomial.X * ∏ i ∈ Finset.range m, V i})) :=
    h4 0 {(1 : Polynomial ℤ), Polynomial.X} Set.Subset.rfl computes_nil
  rcases computes_extract hcomp (by right; right; rfl) with ⟨P, hP⟩
  have hlen : 0 + (16 * m + 12 + Δ_mul + m + 1) + 1 = 17 * m + Δ_mul + 14 := by ring
  rcases chirp_final_poly_eq m S_out hS with ⟨C, hC, hFeq⟩
  rcases chirp_poly_root_count m C hC with ⟨hFne, hFcard⟩
  have hz : zMaxGe (0 + (16 * m + 12 + Δ_mul + m + 1) + 1) (2 * (m * m) + 1) := by
    refine ⟨P, ?_, ?_⟩
    · rw [hP, hFeq]; exact hFne
    · rw [hP, hFeq]; exact hFcard
  rwa [hlen] at hz

/-! ## 4. Division-Free Karatsuba Multiplication & Refutation of Linear Growth (`c = 1`) -/

/-- Exact polynomial product coefficient at degree `t` for length-`n` coefficient arrays `a, b`. -/
noncomputable def polyConv (n : ℕ) (a b : ℕ → Polynomial ℤ) (t : ℕ) : Polynomial ℤ :=
  ∑ i ∈ Finset.range n, if i ≤ t ∧ t - i < n then a i * b (t - i) else 0

theorem polyConv_chirp_eq (m n i : ℕ) (hmn : m < n) (h2mn : 2 * m ≤ n) (hi : i < m) :
    polyConv n (chirpA m) (chirpB m) (i + m) =
      ∑ r ∈ Finset.range (m + 1), chirpA m r * chirpB m (i + m - r) := by
  unfold polyConv
  have hsub : Finset.range (m + 1) ⊆ Finset.range n := Finset.range_mono (by omega)
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl ?_
    intro r hr
    rw [Finset.mem_range] at hr
    have hc : r ≤ i + m ∧ i + m - r < n := by omega
    simp [hc]
  · intro r hr hnot
    rw [Finset.mem_range] at hr hnot
    have hgt : ¬ r ≤ m := by omega
    simp [chirpA, hgt]

/-- Gate cost of division-free Karatsuba multiplication of size `2^k`:
`karatsubaCost 0 = 1`, `karatsubaCost (k + 1) = 3 * karatsubaCost k + 8 * 2 ^ k`. -/
def karatsubaCost : ℕ → ℕ
  | 0 => 1
  | k + 1 => 3 * karatsubaCost k + 8 * 2 ^ k

theorem karatsubaCost_le (k : ℕ) : karatsubaCost k ≤ 9 * 3 ^ k := by
  have hexact : karatsubaCost k + 8 * 2 ^ k = 9 * 3 ^ k := by
    induction k with
    | zero => simp [karatsubaCost]
    | succ k ih =>
        simp only [karatsubaCost, pow_succ]
        omega
  omega

/-- Karatsuba algebraic splitting identity for `polyConv (2 * h) a b t`. -/
theorem polyConv_double_eq (h : ℕ) (a b : ℕ → Polynomial ℤ) (t : ℕ) (_ht : t < 4 * h) :
    let a0 := fun i => a i
    let a1 := fun i => a (i + h)
    let b0 := fun i => b i
    let b1 := fun i => b (i + h)
    let p0 := polyConv h a0 b0
    let p2 := polyConv h a1 b1
    let p1 := fun u => polyConv h (fun i => a0 i + a1 i) (fun i => b0 i + b1 i) u - p0 u - p2 u
    polyConv (2 * h) a b t =
      (if t < 2 * h then p0 t else 0) +
      (if h ≤ t ∧ t < 3 * h then p1 (t - h) else 0) +
      (if 2 * h ≤ t then p2 (t - 2 * h) else 0) := by
  intro a0 a1 b0 b1 p0 p2 p1
  have hp1_eq : ∀ u, p1 u = polyConv h a0 b1 u + polyConv h a1 b0 u := by
    intro u
    simp only [p1, p0, p2, polyConv]
    have hsum :
        ∑ i ∈ Finset.range h,
            (if i ≤ u ∧ u - i < h then (a0 i + a1 i) * (b0 (u - i) + b1 (u - i)) else 0) =
          (∑ i ∈ Finset.range h, if i ≤ u ∧ u - i < h then a0 i * b0 (u - i) else 0) +
          (∑ i ∈ Finset.range h, if i ≤ u ∧ u - i < h then a0 i * b1 (u - i) else 0) +
          (∑ i ∈ Finset.range h, if i ≤ u ∧ u - i < h then a1 i * b0 (u - i) else 0) +
          (∑ i ∈ Finset.range h, if i ≤ u ∧ u - i < h then a1 i * b1 (u - i) else 0) := by
      simp only [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro i _
      split_ifs <;> ring
    rw [hsum]
    ring
  -- Split `range (2 * h)` into `i < h` and `i = j + h` (`j < h`)
  have hsplit :
      polyConv (2 * h) a b t =
        (∑ i ∈ Finset.range h, if i ≤ t ∧ t - i < 2 * h then a i * b (t - i) else 0) +
        (∑ j ∈ Finset.range h, if j + h ≤ t ∧ t - (j + h) < 2 * h then a (j + h) * b (t - (j + h)) else 0) := by
    unfold polyConv
    rw [show 2 * h = h + h by ring, Finset.sum_range_add]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro j _
    simp [Nat.add_comm]
  -- Further split each sum by whether `t - i < h` or `t - i ≥ h`
  have hpart1 :
      (∑ i ∈ Finset.range h, if i ≤ t ∧ t - i < 2 * h then a i * b (t - i) else 0) =
        (if t < 2 * h then p0 t else 0) +
        (if h ≤ t ∧ t < 3 * h then polyConv h a0 b1 (t - h) else 0) := by
    have hsplit_i :
        (∑ i ∈ Finset.range h, if i ≤ t ∧ t - i < 2 * h then a i * b (t - i) else 0) =
          (∑ i ∈ Finset.range h, if i ≤ t ∧ t - i < h then a0 i * b0 (t - i) else 0) +
          (∑ i ∈ Finset.range h, if i ≤ t ∧ h ≤ t - i ∧ t - i < 2 * h then a0 i * b (t - i) else 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro i _
      by_cases h1 : i ≤ t ∧ t - i < h
      · have h2 : i ≤ t ∧ t - i < 2 * h := ⟨h1.1, by omega⟩
        have h3 : ¬ (i ≤ t ∧ h ≤ t - i ∧ t - i < 2 * h) := by omega
        simp [h1, h2, h3, a0, b0]
      · by_cases h3 : i ≤ t ∧ h ≤ t - i ∧ t - i < 2 * h
        · have h2 : i ≤ t ∧ t - i < 2 * h := ⟨h3.1, h3.2.2⟩
          simp [h1, h2, h3, a0]
        · have h2 : ¬ (i ≤ t ∧ t - i < 2 * h) := by omega
          simp [h1, h2, h3]
    rw [hsplit_i]
    congr 1
    · by_cases ht2 : t < 2 * h
      · simp [ht2, p0, polyConv]
      · simp only [ht2, ↓reduceIte]
        refine Finset.sum_eq_zero ?_
        intro i hi
        rw [Finset.mem_range] at hi
        have : ¬ (i ≤ t ∧ t - i < h) := by omega
        simp [this]
    · by_cases htm : h ≤ t ∧ t < 3 * h
      · simp only [htm, polyConv]
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [Finset.mem_range] at hi
        by_cases hc : i ≤ t - h ∧ t - h - i < h
        · have hc' : i ≤ t ∧ h ≤ t - i ∧ t - i < 2 * h := by omega
          have hidx : t - i = t - h - i + h := by omega
          rw [if_pos hc', if_pos hc]; dsimp only [b1]; rw [hidx]
        · have hc' : ¬ (i ≤ t ∧ h ≤ t - i ∧ t - i < 2 * h) := by omega
          rw [if_neg hc', if_neg hc]
      · simp only [htm, ↓reduceIte]
        refine Finset.sum_eq_zero ?_
        intro i hi
        rw [Finset.mem_range] at hi
        have : ¬ (i ≤ t ∧ h ≤ t - i ∧ t - i < 2 * h) := by omega
        simp [this]
  have hpart2 :
      (∑ j ∈ Finset.range h,
          if j + h ≤ t ∧ t - (j + h) < 2 * h then a (j + h) * b (t - (j + h)) else 0) =
        (if h ≤ t ∧ t < 3 * h then polyConv h a1 b0 (t - h) else 0) +
        (if 2 * h ≤ t then p2 (t - 2 * h) else 0) := by
    have hsplit_j :
        (∑ j ∈ Finset.range h,
            if j + h ≤ t ∧ t - (j + h) < 2 * h then a (j + h) * b (t - (j + h)) else 0) =
          (∑ j ∈ Finset.range h, if j + h ≤ t ∧ t - (j + h) < h then a1 j * b0 (t - (j + h)) else 0) +
          (∑ j ∈ Finset.range h,
            if j + h ≤ t ∧ h ≤ t - (j + h) ∧ t - (j + h) < 2 * h then a1 j * b (t - (j + h)) else 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro j _
      by_cases h1 : j + h ≤ t ∧ t - (j + h) < h
      · have h2 : j + h ≤ t ∧ t - (j + h) < 2 * h := ⟨h1.1, by omega⟩
        have h3 : ¬ (j + h ≤ t ∧ h ≤ t - (j + h) ∧ t - (j + h) < 2 * h) := by omega
        simp [h1, h2, h3, a1, b0]
      · by_cases h3 : j + h ≤ t ∧ h ≤ t - (j + h) ∧ t - (j + h) < 2 * h
        · have h2 : j + h ≤ t ∧ t - (j + h) < 2 * h := ⟨h3.1, h3.2.2⟩
          simp [h1, h2, h3, a1]
        · have h2 : ¬ (j + h ≤ t ∧ t - (j + h) < 2 * h) := by omega
          simp [h1, h2, h3]
    rw [hsplit_j]
    congr 1
    · by_cases htm : h ≤ t ∧ t < 3 * h
      · simp only [htm, ↓reduceIte, polyConv]
        refine Finset.sum_congr rfl ?_
        intro j hj
        rw [Finset.mem_range] at hj
        by_cases hc : j ≤ t - h ∧ t - h - j < h
        · have hc' : j + h ≤ t ∧ t - (j + h) < h := by omega
          have hidx : t - (j + h) = t - h - j := by omega
          simp [hc, hc', hidx]
        · have hc' : ¬ (j + h ≤ t ∧ t - (j + h) < h) := by omega
          simp [hc, hc']
      · simp only [htm, ↓reduceIte]
        refine Finset.sum_eq_zero ?_
        intro j hj
        rw [Finset.mem_range] at hj
        have : ¬ (j + h ≤ t ∧ t - (j + h) < h) := by omega
        simp [this]
    · by_cases ht2 : 2 * h ≤ t
      · simp only [ht2, ↓reduceIte, p2, polyConv]
        refine Finset.sum_congr rfl ?_
        intro j hj
        rw [Finset.mem_range] at hj
        by_cases hc : j ≤ t - 2 * h ∧ t - 2 * h - j < h
        · have hc' : j + h ≤ t ∧ h ≤ t - (j + h) ∧ t - (j + h) < 2 * h := by omega
          have hidx : t - (j + h) = t - 2 * h - j + h := by omega
          rw [if_pos hc', if_pos hc]; dsimp only [b1]; rw [hidx]
        · have hc' : ¬ (j + h ≤ t ∧ h ≤ t - (j + h) ∧ t - (j + h) < 2 * h) := by omega
          rw [if_neg hc', if_neg hc]
      · simp only [ht2, ↓reduceIte]
        refine Finset.sum_eq_zero ?_
        intro j hj
        rw [Finset.mem_range] at hj
        have : ¬ (j + h ≤ t ∧ h ≤ t - (j + h) ∧ t - (j + h) < 2 * h) := by omega
        simp [this]
  rw [hsplit, hpart1, hpart2, hp1_eq]
  split_ifs <;> ring

/-- **Division-Free Karatsuba Polynomial Multiplication (`CanBuild`):**
Given `{0} ∪ {a i | i < 2^k} ∪ {b i | i < 2^k}`, computes `{polyConv (2^k) a b t | t < 2 * 2^k}`
in `karatsubaCost k ≤ 9 * 3^k` constant-free gates. -/
theorem canBuild_karatsuba :
    ∀ (k : ℕ) (a b : ℕ → Polynomial ℤ),
      CanBuild
        ({(0 : Polynomial ℤ)} ∪ (⋃ i < 2 ^ k, {a i}) ∪ (⋃ i < 2 ^ k, {b i}))
        (karatsubaCost k)
        (⋃ t < 2 * 2 ^ k, {polyConv (2 ^ k) a b t})
  | 0, a, b => by
      have hm := canBuild_mul (a 0) (b 0)
      have hm' := canBuild_mono_in
        (S₂ := {(0 : Polynomial ℤ)} ∪ (⋃ i < 2 ^ 0, {a i}) ∪ (⋃ i < 2 ^ 0, {b i})) (by
          intro x hx
          rcases hx with rfl | rfl
          · left; right; simp only [Set.mem_iUnion, exists_prop]; exact ⟨0, by omega, rfl⟩
          · right; simp only [Set.mem_iUnion, exists_prop]; exact ⟨0, by omega, rfl⟩) hm
      refine canBuild_weaken_out ?_ hm'
      intro x hx
      simp only [Set.mem_iUnion, exists_prop, Set.mem_singleton_iff] at hx
      rcases hx with ⟨t, ht, rfl⟩
      have hcases : t = 0 ∨ t = 1 := by omega
      rcases hcases with rfl | rfl
      · right; rw [Set.mem_singleton_iff]; simp [polyConv]
      · left; left; left; simp [polyConv]
  | k + 1, a, b => by
      set h := 2 ^ k
      have h2 : 2 ^ (k + 1) = 2 * h := by simp [h, pow_succ, mul_comm]
      let a0 := fun i => a i
      let a1 := fun i => a (i + h)
      let b0 := fun i => b i
      let b1 := fun i => b (i + h)
      let sa := fun i => a0 i + a1 i
      let sb := fun i => b0 i + b1 i
      let p0 := polyConv h a0 b0
      let p2 := polyConv h a1 b1
      let ps := polyConv h sa sb
      let p1 := fun u => ps u - p0 u - p2 u
      set S0 : Set (Polynomial ℤ) :=
        {(0 : Polynomial ℤ)} ∪ (⋃ i < 2 ^ (k + 1), {a i}) ∪ (⋃ i < 2 ^ (k + 1), {b i})
      -- Step 1 (`h` gates): sa i = a i + a (i + h) for i < h
      have h_sa : CanBuild S0 h (⋃ i < h, {sa i}) := by
        simpa using canBuild_fin_union (n := h) (d := 1) (S := S0) (T := fun i => {sa i}) (by
          intro i hi
          refine canBuild_mono_in ?_ (canBuild_add (a0 i) (a1 i))
          intro x hx
          rcases hx with rfl | rfl
          · left; right; simp only [Set.mem_iUnion, exists_prop]; exact ⟨i, by omega, rfl⟩
          · left; right; simp only [Set.mem_iUnion, exists_prop]; exact ⟨i + h, by omega, rfl⟩)
      -- Step 2 (`h` gates): sb i = b i + b (i + h) for i < h
      have h_sb : CanBuild S0 h (⋃ i < h, {sb i}) := by
        simpa using canBuild_fin_union (n := h) (d := 1) (S := S0) (T := fun i => {sb i}) (by
          intro i hi
          refine canBuild_mono_in ?_ (canBuild_add (b0 i) (b1 i))
          intro x hx
          rcases hx with rfl | rfl
          · right; simp only [Set.mem_iUnion, exists_prop]; exact ⟨i, by omega, rfl⟩
          · right; simp only [Set.mem_iUnion, exists_prop]; exact ⟨i + h, by omega, rfl⟩)
      -- Step 3 (3 * karatsubaCost k gates): recursive calls p0, p2, ps
      have h_p0 := canBuild_karatsuba k a0 b0
      have h_p2 := canBuild_karatsuba k a1 b1
      have h_ps := canBuild_karatsuba k sa sb
      have c1 := canBuild_trans h_sa Set.subset_union_left h_sb
      have c2 := canBuild_trans c1 (by
        intro x hx; rcases hx with (rfl | hxA) | hxB
        · left; left; left; rfl
        · left; left; right
          simp only [Set.mem_iUnion, exists_prop] at hxA ⊢
          rcases hxA with ⟨i, hi, hxi⟩; exact ⟨i, by omega, hxi⟩
        · left; right
          simp only [Set.mem_iUnion, exists_prop] at hxB ⊢
          rcases hxB with ⟨i, hi, hxi⟩; exact ⟨i, by omega, hxi⟩) h_p0
      have c3 := canBuild_trans c2 (by
        intro x hx; rcases hx with (rfl | hxA) | hxB
        · left; left; left; rfl
        · left; left; right
          simp only [Set.mem_iUnion, exists_prop] at hxA ⊢
          rcases hxA with ⟨i, hi, hxi⟩; exact ⟨i + h, by omega, hxi⟩
        · left; right
          simp only [Set.mem_iUnion, exists_prop] at hxB ⊢
          rcases hxB with ⟨i, hi, hxi⟩; exact ⟨i + h, by omega, hxi⟩) h_p2
      have c4 := canBuild_trans c3 (by
        intro x hx; rcases hx with (rfl | hxA) | hxB
        · left; left; left; rfl
        · right; left; left; left; exact hxA
        · right; left; left; right; exact hxB) h_ps
      -- Step 4 (`4 * h` gates): p1 u = (ps u - p0 u) - p2 u for u < 2 * h
      have h_p1 :
          CanBuild
            ((⋃ u < 2 * h, {p0 u}) ∪ (⋃ u < 2 * h, {p2 u}) ∪ (⋃ u < 2 * h, {ps u}))
            (2 * h * 2) (⋃ u < 2 * h, {p1 u}) := by
        refine canBuild_fin_union (n := 2 * h) (d := 2) (T := fun u => {p1 u}) ?_
        intro u hu
        have s1 := canBuild_sub (ps u) (p0 u)
        have s2 := canBuild_sub (ps u - p0 u) (p2 u)
        have s12 := canBuild_trans
          (canBuild_mono_in (S₂ := {ps u, p0 u, p2 u})
            (by intro x hx; rcases hx with rfl | rfl <;> simp) s1)
          (by intro x hx; rcases hx with rfl | rfl <;> simp) s2
        refine canBuild_mono_out (fun x hx => Or.inr hx) (canBuild_mono_in ?_ s12)
        intro x hx
        rcases hx with rfl | rfl | rfl
        · right; simp only [Set.mem_iUnion, exists_prop]; exact ⟨u, hu, rfl⟩
        · left; left; simp only [Set.mem_iUnion, exists_prop]; exact ⟨u, hu, rfl⟩
        · left; right; simp only [Set.mem_iUnion, exists_prop]; exact ⟨u, hu, rfl⟩
      have c5 := canBuild_trans c4 (by
        intro x hx; rcases hx with (hx0 | hx2) | hxs
        · right; left; left; right; exact hx0
        · right; left; right; exact hx2
        · right; right; exact hxs) h_p1
      -- Step 5 (`2 * h` gates): combine middle bands h ≤ t < 2h and 2h ≤ t < 3h
      have h_mid1 :
          CanBuild ((⋃ u < 2 * h, {p0 u}) ∪ (⋃ u < 2 * h, {p1 u})) h
            (⋃ j < h, {p0 (j + h) + p1 j}) := by
        simpa using canBuild_fin_union (n := h) (d := 1)
          (T := fun j => {p0 (j + h) + p1 j}) (by
            intro j hj
            refine canBuild_mono_in ?_ (canBuild_add (p0 (j + h)) (p1 j))
            intro x hx
            rcases hx with rfl | rfl
            · left; simp only [Set.mem_iUnion, exists_prop]; exact ⟨j + h, by omega, rfl⟩
            · right; simp only [Set.mem_iUnion, exists_prop]; exact ⟨j, by omega, rfl⟩)
      have h_mid2 :
          CanBuild ((⋃ u < 2 * h, {p2 u}) ∪ (⋃ u < 2 * h, {p1 u})) h
            (⋃ j < h, {p1 (j + h) + p2 j}) := by
        simpa using canBuild_fin_union (n := h) (d := 1)
          (T := fun j => {p1 (j + h) + p2 j}) (by
            intro j hj
            refine canBuild_mono_in ?_ (canBuild_add (p1 (j + h)) (p2 j))
            intro x hx
            rcases hx with rfl | rfl
            · right; simp only [Set.mem_iUnion, exists_prop]; exact ⟨j + h, by omega, rfl⟩
            · left; simp only [Set.mem_iUnion, exists_prop]; exact ⟨j, by omega, rfl⟩)
      have c6 := canBuild_trans c5 (by
        intro x hx; rcases hx with hx0 | hx1
        · right; left; left; left; right; exact hx0
        · right; right; exact hx1) h_mid1
      have c7 := canBuild_trans c6 (by
        intro x hx; rcases hx with hx2 | hx1
        · right; left; left; left; right; exact hx2
        · right; left; right; exact hx1) h_mid2
      have hcost :
          h + h + karatsubaCost k + karatsubaCost k + karatsubaCost k + 2 * h * 2 + h + h =
            karatsubaCost (k + 1) := by
        simp only [karatsubaCost, h]
        ring
      rw [hcost] at c7
      refine canBuild_weaken_out ?_ c7
      intro x hx
      simp only [Set.mem_iUnion, exists_prop, Set.mem_singleton_iff] at hx
      rcases hx with ⟨t, ht, rfl⟩
      have ht4 : t < 4 * h := by omega
      rw [h2, polyConv_double_eq h a b t ht4]
      by_cases hlt1 : t < h
      · have h1 : t < 2 * h := by omega
        have h2' : ¬ (h ≤ t ∧ t < 3 * h) := by omega
        have h3' : ¬ (2 * h ≤ t) := by omega
        simp only [h1, h2', h3', ↓reduceIte, add_zero]
        right; left; left; left; left; left; right
        simp only [Set.mem_iUnion, exists_prop]; exact ⟨t, h1, rfl⟩
      · by_cases hlt2 : t < 2 * h
        · have h2' : h ≤ t ∧ t < 3 * h := by omega
          have h3' : ¬ (2 * h ≤ t) := by omega
          simp only [hlt2, h2', h3', ↓reduceIte, add_zero]
          right; left; right
          simp only [Set.mem_iUnion, exists_prop]
          refine ⟨t - h, by omega, ?_⟩
          have hidx : t - h + h = t := by omega
          rw [hidx]; rfl
        · by_cases hlt3 : t < 3 * h
          · have h2' : h ≤ t ∧ t < 3 * h := by omega
            have h3' : 2 * h ≤ t := by omega
            simp only [hlt2, h2', h3', ↓reduceIte, zero_add]
            right; right
            simp only [Set.mem_iUnion, exists_prop]
            refine ⟨t - 2 * h, by omega, ?_⟩
            have hidx : t - 2 * h + h = t - h := by omega
            rw [hidx]; rfl
          · have h2' : ¬ (h ≤ t ∧ t < 3 * h) := by omega
            have h3' : 2 * h ≤ t := by omega
            simp only [hlt2, h2', h3', ↓reduceIte, zero_add]
            right; left; left; left; left; right
            simp only [Set.mem_iUnion, exists_prop]
            exact ⟨t - 2 * h, by omega, rfl⟩

/-- **Unconditional Superlinear Growth via Karatsuba Chirp-$z$:**
For every `k ≥ 1`, there exists a constant-free SLP of length `50 * 3 ^ k` computing a nonzero
polynomial in `ℤ[X]` with at least `2 * 4 ^ k + 1` distinct integer roots
(`z_max(τ) = Ω(τ ^ (2 / log₂ 3)) ≈ Ω(τ ^ 1.2618)`). -/
theorem tau_karatsuba_growth (k : ℕ) (hk : 1 ≤ k) :
    zMaxGe (50 * 3 ^ k) (2 * 4 ^ k + 1) := by
  set m := 2 ^ k
  have hm : 1 ≤ m := Nat.one_le_two_pow
  have hm2 : m * m = 4 ^ k := by
    simp only [m, ← pow_add, show k + k = 2 * k by ring, pow_mul]
    norm_num
  -- Apply Karatsuba of size `2^(k + 1) = 2 * m`
  have hkar := canBuild_karatsuba (k + 1) (chirpA m) (chirpB m)
  have h2k1 : 2 ^ (k + 1) = 2 * m := by simp [m, pow_succ, mul_comm]
  have hstep :
      CanBuild
        ({(0 : Polynomial ℤ)} ∪ (⋃ r < m + 1, {chirpA m r}) ∪ (⋃ s < 2 * m, {chirpB m s}))
        (karatsubaCost (k + 1))
        (⋃ i < m, {Polynomial.C (1 : ℤ) *
          ∑ r ∈ Finset.range (m + 1), chirpA m r * chirpB m (i + m - r)}) := by
    have hin :
        ({(0 : Polynomial ℤ)} ∪ (⋃ i < 2 ^ (k + 1), {chirpA m i}) ∪
            (⋃ i < 2 ^ (k + 1), {chirpB m i})) ⊆
          ({(0 : Polynomial ℤ)} ∪ (⋃ r < m + 1, {chirpA m r}) ∪ (⋃ s < 2 * m, {chirpB m s})) := by
      intro x hx
      rcases hx with (rfl | hxA) | hxB
      · left; left; rfl
      · simp only [Set.mem_iUnion, exists_prop, Set.mem_singleton_iff] at hxA
        rcases hxA with ⟨r, hr, rfl⟩
        by_cases hrm : r ≤ m
        · left; right; simp only [Set.mem_iUnion, exists_prop]; exact ⟨r, by omega, rfl⟩
        · left; left; simp [chirpA, hrm]
      · right
        simp only [Set.mem_iUnion, exists_prop, Set.mem_singleton_iff] at hxB ⊢
        rcases hxB with ⟨s, hs, rfl⟩
        exact ⟨s, by omega, rfl⟩
    have h1 := canBuild_mono_in hin hkar
    refine canBuild_mono_out ?_ h1
    intro x hx
    simp only [Set.mem_iUnion, exists_prop, Set.mem_singleton_iff] at hx ⊢
    rcases hx with ⟨i, hi, rfl⟩
    refine ⟨i + m, by omega, ?_⟩
    rw [map_one, one_mul, polyConv_chirp_eq m (2 ^ (k + 1)) i (by omega) (by omega) hi]
  have hz := zMaxGe_of_chirp_engine hm 1 (by omega) hstep
  rw [hm2] at hz
  -- Pad from `17 * 2^k + karatsubaCost (k + 1) + 14` to `50 * 3^k`
  have hle : 17 * m + karatsubaCost (k + 1) + 14 ≤ 50 * 3 ^ k := by
    have hk_le : karatsubaCost (k + 1) ≤ 9 * 3 ^ (k + 1) := karatsubaCost_le (k + 1)
    have h3k1 : 9 * 3 ^ (k + 1) = 27 * 3 ^ k := by rw [pow_succ]; ring
    have h23 : 2 ^ k ≤ 3 ^ k := Nat.pow_le_pow_left (by omega) k
    have h3pos : 3 ≤ 3 ^ k := by
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ k := Nat.pow_le_pow_right (by omega) hk
    omega
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
  rw [hd]
  clear hd hle
  induction d with
  | zero => simpa using hz
  | succ d ih => exact zMaxGe_succ ih

/-- **Unconditional Refutation of the Linear Shub–Smale $\tau$-Conjecture (`c = 1`):**
There is no constant `a : ℕ` such that every nonzero constant-free SLP of length `τ`
has at most `a * (τ + 1)` distinct integer roots. -/
theorem tau_refutes_linear :
    ¬ ∃ a : ℕ, ∀ (τ : ℕ) (P : SLP τ), P.evalPoly ≠ 0 →
      intRootCount P.evalPoly ≤ a * (τ + 1) := by
  rintro ⟨a, ha⟩
  -- For any k ≥ 1, `2 * 4^k + 1 ≤ a * (50 * 3^k + 1)`.
  -- Since `4^k / 3^k` grows exponentially (4^k ≥ 3^k + ...; concretely `(4/3)^3 > 2`, so 4^(3n) > 2^n * 3^(3n)):
  have hgrow : ∀ n : ℕ, 2 ^ n * 3 ^ (3 * n) ≤ 4 ^ (3 * n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have h1 : 2 ^ (n + 1) * 3 ^ (3 * (n + 1)) = 54 * (2 ^ n * 3 ^ (3 * n)) := by
          rw [pow_succ, show 3 * (n + 1) = 3 * n + 3 by ring, pow_add]; ring
        have h2 : 4 ^ (3 * (n + 1)) = 64 * 4 ^ (3 * n) := by
          rw [show 3 * (n + 1) = 3 * n + 3 by ring, pow_add]; ring
        rw [h1, h2]
        calc 54 * (2 ^ n * 3 ^ (3 * n)) ≤ 54 * 4 ^ (3 * n) := Nat.mul_le_mul_left 54 ih
          _ ≤ 64 * 4 ^ (3 * n) := Nat.mul_le_mul_right _ (by omega)
  let n := 51 * a + 2
  let k := 3 * n
  have hk : 1 ≤ k := by omega
  rcases tau_karatsuba_growth k hk with ⟨P, hne, hcard⟩
  have hub := ha (50 * 3 ^ k) P hne
  have hbound : 2 * 4 ^ k + 1 ≤ a * (50 * 3 ^ k + 1) := hcard.trans hub
  have h2n : n < 2 ^ n := Nat.lt_two_pow_self
  have hpow : 2 ^ n * 3 ^ k ≤ 4 ^ k := hgrow n
  have h3pos : 1 ≤ 3 ^ k := Nat.one_le_pow k 3 (by omega)
  have h4gt : 2 * (n * 3 ^ k) ≤ 2 * 4 ^ k := by
    have h1 : n * 3 ^ k ≤ 2 ^ n * 3 ^ k := Nat.mul_le_mul_right (3 ^ k) (Nat.le_of_lt h2n)
    exact Nat.mul_le_mul_left 2 (h1.trans hpow)
  have hupper : a * (50 * 3 ^ k + 1) ≤ (51 * a) * 3 ^ k := by
    calc a * (50 * 3 ^ k + 1) ≤ a * (50 * 3 ^ k + 3 ^ k) :=
          Nat.mul_le_mul_left a (Nat.add_le_add_left h3pos _)
      _ = (51 * a) * 3 ^ k := by ring
  have hlt : (51 * a) * 3 ^ k < 2 * (n * 3 ^ k) := by
    have hcoeff : 51 * a < 2 * n := by omega
    calc (51 * a) * 3 ^ k < (2 * n) * 3 ^ k := Nat.mul_lt_mul_of_pos_right hcoeff (by omega)
      _ = 2 * (n * 3 ^ k) := by ring
  omega

end Research.PvsNP.Tau

end