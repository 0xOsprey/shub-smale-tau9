module

public import Research.PvsNP.Tau.TauWitnesses
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Roots

@[expose] public section

namespace Research.PvsNP.Tau

/-!
# Modular Simple-Root Certificate & Unconditional Linear Lower Bound

This module establishes two unconditional results for the Shub–Smale $\tau$-conjecture:

1. **Modular $\mathbb{Z} \to \mathbb{F}_p$ Simple-Root Certificate
   (`intRootCount_le_zmod_roots_of_no_double_root`, `intRootCount_le_of_eval_zmod`):**
   If $p$ is prime and $f \in \mathbb{Z}[X]$ reduces modulo $p$ to a nonzero polynomial
   $f_p \in \mathbb{F}_p[X]$ with no repeated roots in $\mathbb{F}_p$ (verified via
   $f_p(a) = 0 \implies f_p'(a) \neq 0$), then the number of distinct integer roots of $f$
   over all of $\mathbb{Z}$ is bounded above by the number of distinct roots of $f_p$ in
   $\mathbb{F}_p$.

2. **Unconditional Asymptotic Linear Lower Bound (`tau_pronic_linear_growth`,
   `tau_linear_lower_bound`):**
   For every $k \ge 1$, there exists a constant-free straight-line program of length $3k$
   computing the pronic product $\prod_{j=0}^{k-1} (X(X - 1) - j(j + 1))$, which has at
   least $2k$ distinct integer roots $\{-k + 1, \dots, k\}$. Thus `zMaxGe (3 * k) (2 * k)`.
-/

/-! ## 1. Unconditional $\mathbb{Z} \to \mathbb{F}_p$ Simple-Root Certificate -/

/-- If every element of a finite set `S : Finset ℤ` is a root of `f ∈ ℤ[X]`,
then the product of linear factors `∏ r ∈ S, (X - C r)` divides `f` in `ℤ[X]`. -/
theorem prod_linear_dvd_of_roots (f : Polynomial ℤ) (S : Finset ℤ)
    (hS : ∀ r ∈ S, f.IsRoot r) :
    (∏ r ∈ S, (Polynomial.X - Polynomial.C r)) ∣ f := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      have hs : ∀ r ∈ s, f.IsRoot r := fun r hr => hS r (Finset.mem_insert_of_mem hr)
      rcases ih hs with ⟨g, hg⟩
      have hfa : f.eval a = 0 := hS a (Finset.mem_insert_self a s)
      rw [hg, Polynomial.eval_mul, Polynomial.eval_prod] at hfa
      have hprod_ne : (∏ r ∈ s, (Polynomial.X - Polynomial.C r).eval a) ≠ 0 := by
        rw [Finset.prod_ne_zero_iff]
        intro r hr
        simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_ne_zero]
        intro hEq
        exact ha (hEq ▸ hr)
      have hga : g.IsRoot a := by
        rw [Polynomial.IsRoot]
        exact (mul_eq_zero.mp hfa).resolve_left hprod_ne
      rcases Polynomial.dvd_iff_isRoot.mpr hga with ⟨h, hh⟩
      refine ⟨h, ?_⟩
      rw [Finset.prod_insert ha, hg, hh]
      ring

/-- Helper: in `(ZMod p)[X]`, any finite product of linear factors `X - C (r : ZMod p)`
indexed by `S : Finset ℤ` is nonzero and has `S.card` roots counted with multiplicity. -/
private theorem prod_linear_zmod_ne_zero_and_roots_card (p : ℕ) [Fact p.Prime] (S : Finset ℤ) :
    let P : Polynomial (ZMod p) := ∏ r ∈ S, (Polynomial.X - Polynomial.C (r : ZMod p))
    P ≠ 0 ∧ P.roots.card = S.card := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      rcases ih with ⟨hPs_ne, hPs_card⟩
      have hlin_ne : (Polynomial.X - Polynomial.C (a : ZMod p) : Polynomial (ZMod p)) ≠ 0 :=
        Polynomial.X_sub_C_ne_zero _
      have hP_eq :
          (∏ r ∈ insert a s, (Polynomial.X - Polynomial.C (r : ZMod p) : Polynomial (ZMod p))) =
            (Polynomial.X - Polynomial.C (a : ZMod p)) *
              (∏ r ∈ s, (Polynomial.X - Polynomial.C (r : ZMod p))) :=
        Finset.prod_insert ha
      refine ⟨?_, ?_⟩
      · rw [hP_eq]
        exact mul_ne_zero hlin_ne hPs_ne
      · rw [hP_eq, Polynomial.roots_mul (mul_ne_zero hlin_ne hPs_ne),
            Multiset.card_add, Polynomial.roots_X_sub_C, Multiset.card_singleton,
            hPs_card, Finset.card_insert_of_notMem ha]
        omega

/-- **Multiplicity-counted modular root bound:**
If `p` is prime and the reduction `f_p ∈ (ZMod p)[X]` of `f ∈ ℤ[X]` is nonzero, then
the number of distinct integer roots of `f` is at most the number of roots of `f_p`
in `ZMod p` counted with multiplicity. -/
theorem intRootCount_le_zmod_roots_card_mult (p : ℕ) [Fact p.Prime] (f : Polynomial ℤ)
    (hf_p : f.map (Int.castRingHom (ZMod p)) ≠ 0) :
    intRootCount f ≤ (f.map (Int.castRingHom (ZMod p))).roots.card := by
  let φ := Int.castRingHom (ZMod p)
  have hS : ∀ r ∈ intRootSet f, f.IsRoot r := fun r hr => (mem_intRootSet_iff.mp hr).2
  rcases prod_linear_dvd_of_roots f (intRootSet f) hS with ⟨g, hg⟩
  let P : Polynomial (ZMod p) := ∏ r ∈ intRootSet f, (Polynomial.X - Polynomial.C (r : ZMod p))
  have hmap_eq : f.map φ = P * g.map φ := by
    have h1 : f.map φ = (∏ r ∈ intRootSet f, (Polynomial.X - Polynomial.C r)).map φ * g.map φ := by
      conv_lhs => rw [hg]
      rw [Polynomial.map_mul]
    rw [h1, Polynomial.map_prod]
    congr 1
    refine Finset.prod_congr rfl ?_
    intro r _
    simp [φ, Polynomial.map_sub, Polynomial.map_X]
  have hP_card : P.roots.card = (intRootSet f).card :=
    (prod_linear_zmod_ne_zero_and_roots_card p (intRootSet f)).2
  have hmul_ne : P * g.map φ ≠ 0 := by rwa [← hmap_eq]
  calc
    intRootCount f = (intRootSet f).card := rfl
    _ = P.roots.card := hP_card.symm
    _ ≤ P.roots.card + (g.map φ).roots.card := Nat.le_add_right _ _
    _ = (P * g.map φ).roots.card := by
        rw [Polynomial.roots_mul hmul_ne, Multiset.card_add]
    _ = (f.map φ).roots.card := by rw [← hmap_eq]

/-- If `(X - C a)^2` divides `g`, then `a` is a common root of `g` and `g.derivative`. -/
private theorem isRoot_and_derivative_isRoot_of_sq_dvd {R : Type*} [CommRing R]
    {g : Polynomial R} {a : R} (hdvd : (Polynomial.X - Polynomial.C a) ^ 2 ∣ g) :
    g.IsRoot a ∧ g.derivative.IsRoot a := by
  rcases hdvd with ⟨q, hq⟩
  have hlin : (Polynomial.X - Polynomial.C a).eval a = 0 := by simp
  constructor
  · simp [Polynomial.IsRoot, hq, hlin]
  · have hq' : g = (Polynomial.X - Polynomial.C a) * ((Polynomial.X - Polynomial.C a) * q) := by
      rw [hq, sq, mul_assoc]
    rw [Polynomial.IsRoot, hq', Polynomial.derivative_mul]
    simp [hlin]

/-- **Unconditional $\mathbb{Z} \to \mathbb{F}_p$ Simple-Root Certificate Theorem:**
If `p` is prime and `f_p := f.map (Int.castRingHom (ZMod p))` is nonzero with no
common root of `f_p` and `f_p.derivative` in `ZMod p`, then every root of `f_p` is
simple and `intRootCount f ≤ f_p.roots.toFinset.card`. -/
theorem intRootCount_le_zmod_roots_of_no_double_root (p : ℕ) [Fact p.Prime] (f : Polynomial ℤ)
    (hf_p : f.map (Int.castRingHom (ZMod p)) ≠ 0)
    (hsimple : ∀ a : ZMod p,
      ¬((f.map (Int.castRingHom (ZMod p))).IsRoot a ∧
        (f.map (Int.castRingHom (ZMod p))).derivative.IsRoot a)) :
    intRootCount f ≤ (f.map (Int.castRingHom (ZMod p))).roots.toFinset.card := by
  set f_p := f.map (Int.castRingHom (ZMod p))
  have hnodup : f_p.roots.Nodup := by
    rw [Multiset.nodup_iff_count_le_one]
    intro a
    rw [Polynomial.count_roots]
    by_contra hgt
    have h2 : 2 ≤ f_p.rootMultiplicity a := by omega
    have hdvd : (Polynomial.X - Polynomial.C a) ^ 2 ∣ f_p :=
      (pow_dvd_pow (Polynomial.X - Polynomial.C a) h2).trans (Polynomial.pow_rootMultiplicity_dvd f_p a)
    exact hsimple a (isRoot_and_derivative_isRoot_of_sq_dvd hdvd)
  have hcard_eq : f_p.roots.toFinset.card = f_p.roots.card :=
    Multiset.toFinset_card_of_nodup hnodup
  rw [hcard_eq]
  exact intRootCount_le_zmod_roots_card_mult p f hf_p

/-- **Evaluation-form Simple-Root Certificate Corollary:**
If `f_p` is nonzero at some `a : ZMod p`, has nonzero derivative at every root in `ZMod p`,
and vanishes at most `B` times in `ZMod p`, then `intRootCount f ≤ B` unconditionally
over all of `ℤ`. -/
theorem intRootCount_le_of_eval_zmod (p : ℕ) [Fact p.Prime] (f : Polynomial ℤ) (B : ℕ)
    (hne_pt : ∃ a : ZMod p, (f.map (Int.castRingHom (ZMod p))).eval a ≠ 0)
    (hderiv : ∀ a : ZMod p,
      (f.map (Int.castRingHom (ZMod p))).eval a = 0 →
      (f.map (Int.castRingHom (ZMod p))).derivative.eval a ≠ 0)
    (hbound : (Finset.univ.filter (fun a : ZMod p =>
      (f.map (Int.castRingHom (ZMod p))).eval a = 0)).card ≤ B) :
    intRootCount f ≤ B := by
  set f_p := f.map (Int.castRingHom (ZMod p))
  have hf_p : f_p ≠ 0 := by
    rcases hne_pt with ⟨a, ha⟩
    intro h0
    apply ha
    rw [h0, Polynomial.eval_zero]
  have hsimple : ∀ a : ZMod p, ¬(f_p.IsRoot a ∧ f_p.derivative.IsRoot a) := by
    intro a ⟨hr, hdr⟩
    exact hderiv a hr hdr
  have hsub : f_p.roots.toFinset ⊆ Finset.univ.filter (fun a : ZMod p => f_p.eval a = 0) := by
    intro a ha
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ a, ?_⟩
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hf_p] at ha
    exact ha
  calc
    intRootCount f ≤ f_p.roots.toFinset.card :=
      intRootCount_le_zmod_roots_of_no_double_root p f hf_p hsimple
    _ ≤ (Finset.univ.filter (fun a : ZMod p => f_p.eval a = 0)).card :=
      Finset.card_le_card hsub
    _ ≤ B := hbound

/-! ## 2. Unconditional Asymptotic Linear Lower Bound (`zMaxGe (3 * k) (2 * k)`) -/

/-- Recursive constant-free SLP family of length `3 * (n + 1)` computing the pronic product
`∏ j ∈ Finset.range (n + 1), (X * (X - 1) - j * (j + 1))`.

Wire layout at stage `n` (`τ = 3 * (n + 1)`, wires `0 .. 3 * n + 4`):
- wire `2`: constant `2`
- wire `3 * n + 2`: `2 * (n + 1)`
- wire `if n = 0 then 4 else 3 * n + 3`: `X * (X - 1) - n * (n + 1)`
- wire `3 * n + 4` (output): `∏ j ∈ Finset.range (n + 1), (X * (X - 1) - j * (j + 1))`
-/
def pronicSLP : (n : ℕ) → SLP (3 * (n + 1))
  | 0 =>
      let p1 : SLP 1 := .snoc .nil .add ⟨0, by omega⟩ ⟨0, by omega⟩   -- w2 = 2
      let p2 : SLP 2 := .snoc p1 .sub ⟨1, by omega⟩ ⟨0, by omega⟩     -- w3 = X - 1
      .snoc p2 .mul ⟨1, by omega⟩ ⟨3, by omega⟩                       -- w4 = X * (X - 1)
  | n + 1 =>
      let prev : SLP (3 * (n + 1)) := pronicSLP n
      let s1 : SLP (3 * (n + 1) + 1) :=
        .snoc prev .add ⟨3 * n + 2, by omega⟩ ⟨2, by omega⟩
      let s2 : SLP (3 * (n + 1) + 2) :=
        .snoc s1 .sub ⟨if n = 0 then 4 else 3 * n + 3, by split_ifs <;> omega⟩
          ⟨3 * n + 2, by omega⟩
      .snoc s2 .mul ⟨3 * n + 4, by change 3 * n + 4 < 3 * (n + 1) + 4; omega⟩
        ⟨3 * n + 6, by change 3 * n + 6 < 3 * (n + 1) + 4; omega⟩

/-- Simultaneous invariant for integer evaluations of the four tracked wires of `pronicSLP n`. -/
theorem pronicSLP_evalWireInt (n : ℕ) (a : ℤ) :
    (pronicSLP n).evalWireInt a ⟨2, by omega⟩ = 2 ∧
    (pronicSLP n).evalWireInt a ⟨3 * n + 2, by omega⟩ = 2 * ((n : ℤ) + 1) ∧
    (pronicSLP n).evalWireInt a ⟨if n = 0 then 4 else 3 * n + 3, by split_ifs <;> omega⟩ =
      a * (a - 1) - (n : ℤ) * ((n : ℤ) + 1) ∧
    (pronicSLP n).evalWireInt a ⟨3 * n + 4, by omega⟩ =
      ∏ j ∈ Finset.range (n + 1), (a * (a - 1) - (j : ℤ) * ((j : ℤ) + 1)) := by
  induction n with
  | zero =>
      simp [pronicSLP, SLP.evalWireInt, SLPOp.applyInt]
  | succ n ih =>
      rcases ih with ⟨hTwo, hD, hF, hP⟩
      have hlt_two : 2 < 3 * (n + 1) + 2 := by omega
      have hlt_two1 : 2 < 3 * (n + 1) + 3 := by omega
      have hlt_two2 : 2 < 3 * (n + 1) + 4 := by omega
      have hlt_P1 : 3 * n + 4 < 3 * (n + 1) + 2 := by omega
      have hlt_P2 : 3 * n + 4 < 3 * (n + 1) + 3 := by omega
      have hlt_idxF : (if n = 0 then 4 else 3 * n + 3) < 3 * (n + 1) + 2 := by split_ifs <;> omega
      have hlt_idxD : 3 * n + 2 < 3 * (n + 1) + 2 := by omega
      have hnotF : ¬ (3 * n + 6 < 3 * (n + 1) + 1 + 2) := by omega
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- Wire 2 = 2
        simpa [pronicSLP, SLP.evalWireInt, hlt_two, hlt_two1, hlt_two2] using hTwo
      · -- Wire 3 * (n + 1) + 2 = 2 * ((n + 1) + 1)
        have hstep :
            (pronicSLP (n + 1)).evalWireInt a ⟨3 * (n + 1) + 2, by omega⟩ =
              (pronicSLP n).evalWireInt a ⟨3 * n + 2, by omega⟩ +
                (pronicSLP n).evalWireInt a ⟨2, by omega⟩ := by
          simp [pronicSLP, SLP.evalWireInt, SLPOp.applyInt]
        rw [hstep, hD, hTwo]
        push_cast
        ring
      · -- Wire 3 * (n + 1) + 3 = a * (a - 1) - (n + 1) * (n + 2)
        have hstep :
            (pronicSLP (n + 1)).evalWireInt a
                ⟨if n + 1 = 0 then 4 else 3 * (n + 1) + 3, by split_ifs <;> omega⟩ =
              (pronicSLP n).evalWireInt a
                ⟨if n = 0 then 4 else 3 * n + 3, by split_ifs <;> omega⟩ -
                (pronicSLP n).evalWireInt a ⟨3 * n + 2, by omega⟩ := by
          simp [pronicSLP, SLP.evalWireInt, SLPOp.applyInt, hlt_idxF, hlt_idxD]
        rw [hstep, hF, hD]
        push_cast
        ring
      · -- Wire 3 * (n + 1) + 4 = product over range (n + 2)
        have hstep :
            (pronicSLP (n + 1)).evalWireInt a ⟨3 * (n + 1) + 4, by omega⟩ =
              (pronicSLP n).evalWireInt a ⟨3 * n + 4, by omega⟩ *
                ((pronicSLP n).evalWireInt a
                    ⟨if n = 0 then 4 else 3 * n + 3, by split_ifs <;> omega⟩ -
                  (pronicSLP n).evalWireInt a ⟨3 * n + 2, by omega⟩) := by
          simp [pronicSLP, SLP.evalWireInt, SLPOp.applyInt, hlt_P1, hlt_P2, hlt_idxF, hlt_idxD, hnotF]
        rw [hstep, hP, hF, hD]
        conv_rhs => rw [Finset.prod_range_succ]
        congr 1
        push_cast
        ring

/-- Closed-form integer evaluation of the output wire of `pronicSLP n`. -/
theorem pronicSLP_evalInt (n : ℕ) (a : ℤ) :
    (pronicSLP n).evalInt a =
      ∏ j ∈ Finset.range (n + 1), (a * (a - 1) - (j : ℤ) * ((j : ℤ) + 1)) := by
  have hfin :
      (⟨3 * (n + 1) + 1, Nat.lt_succ_self _⟩ : Fin (3 * (n + 1) + 2)) =
        ⟨3 * n + 4, by omega⟩ := by
    ext
    dsimp
    omega
  rw [SLP.evalInt, hfin]
  exact (pronicSLP_evalWireInt n a).2.2.2

/-- **Unconditional Asymptotic Linear Lower Bound (pronic family):**
For every `k ≥ 1`, there exists a constant-free SLP of length `3 * k` computing a
nonzero polynomial in `ℤ[X]` with at least `2 * k` distinct integer roots. -/
theorem tau_pronic_linear_growth (k : ℕ) (hk : 1 ≤ k) : zMaxGe (3 * k) (2 * k) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = n + 1 := ⟨k - 1, by omega⟩
  let S : Finset ℤ := (Finset.range (2 * (n + 1))).image (fun m : ℕ => (m : ℤ) - (n : ℤ))
  have hcard : 2 * (n + 1) ≤ S.card := by
    have hEq : S.card = 2 * (n + 1) := by
      rw [Finset.card_image_of_injective, Finset.card_range]
      intro x y hxy
      dsimp at hxy
      omega
    exact hEq.ge
  have hb : (pronicSLP n).evalInt ((n : ℤ) + 2) ≠ 0 := by
    rw [pronicSLP_evalInt, Finset.prod_ne_zero_iff]
    intro j hj
    rw [Finset.mem_range] at hj
    have hjz : (j : ℤ) ≤ n := by omega
    have hpos : 0 < ((n : ℤ) + 2) * ((n : ℤ) + 2 - 1) - (j : ℤ) * ((j : ℤ) + 1) := by
      nlinarith
    omega
  have hS : ∀ a ∈ S, (pronicSLP n).evalInt a = 0 := by
    intro a ha
    rw [pronicSLP_evalInt]
    simp only [S, Finset.mem_image, Finset.mem_range] at ha
    rcases ha with ⟨m, hm, rfl⟩
    by_cases hpos : 1 ≤ (m : ℤ) - (n : ℤ)
    · refine Finset.prod_eq_zero (i := ((m : ℤ) - (n : ℤ) - 1).toNat) ?_ ?_
      · rw [Finset.mem_range]
        omega
      · have hcoe : (((m : ℤ) - (n : ℤ) - 1).toNat : ℤ) = (m : ℤ) - (n : ℤ) - 1 :=
          Int.toNat_of_nonneg (by omega)
        rw [hcoe]
        ring
    · refine Finset.prod_eq_zero (i := (-((m : ℤ) - (n : ℤ))).toNat) ?_ ?_
      · rw [Finset.mem_range]
        omega
      · have hcoe : ((-((m : ℤ) - (n : ℤ))).toNat : ℤ) = -((m : ℤ) - (n : ℤ)) :=
          Int.toNat_of_nonneg (by omega)
        rw [hcoe]
        ring
  exact zMaxGe_of_evalInt (pronicSLP n) S ((n : ℤ) + 2) hcard hb hS

/-- Alias for `tau_pronic_linear_growth`: `zMaxGe (3 * k) (2 * k)` for all `k ≥ 1`. -/
theorem tau_linear_lower_bound (k : ℕ) (hk : 1 ≤ k) : zMaxGe (3 * k) (2 * k) :=
  tau_pronic_linear_growth k hk

end Research.PvsNP.Tau

end
