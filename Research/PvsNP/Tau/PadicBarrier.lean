module

public import Research.PvsNP.Tau.TauConjecture
public import Mathlib.NumberTheory.Padics.Hensel

@[expose] public section

namespace Research.PvsNP.Tau

/-!
# Unconditional $2$-Adic Exponential Lower Bound (`z_max^{ℤ_2}(4k) ≥ 2^k`)

This module proves that the constant-free straight-line program family
- `P₀(X) = X^2 - 1`
- `c₁ = 64`, `c_{n+1} = 64 * c_n^2`
- `P_{n+1}(X) = P_n(X)^2 - c_{n+1}`

has constant-free SLP length `τ(P_n) ≤ 4 * (n + 1)` (exact length `2` for `n = 0` and
`4 * (n + 1)` for `n ≥ 1`), yet admits at least `2 ^ (n + 1)` distinct roots in the
$2$-adic integers `ℤ_[2]`.

Combined with Chebyshev polynomials over `ℝ` (`2 ^ ((τ - 1) / 2)` real roots) and
`X^(2^(τ-1)) - 1` over `𝔽_p`, this shows that **no purely Archimedean (`ℝ`), purely
$p$-adic (`ℚ_p`), or purely finite-field (`𝔽_p`) method can prove `z_max(τ) = 2^o(τ)`
or the Shub–Smale $\tau$-conjecture**.
-/

/-- Exponent sequence `exp2 n`: `exp2 0 = 0`, `exp2 1 = 3`, `exp2 (n + 2) = 2 * exp2 (n + 1) + 3`.
Thus `c_n = 2 ^ (2 * exp2 n)` satisfies `c_1 = 64` and `c_{n+1} = 64 * c_n ^ 2`. -/
def padicExp2 : ℕ → ℕ
  | 0 => 0
  | 1 => 3
  | n + 2 => 2 * padicExp2 (n + 1) + 3

/-- The polynomial family `padicPoly n ∈ ℤ[X]` with `2 ^ (n + 1)` distinct roots in `ℤ_[2]`. -/
noncomputable def padicPoly : ℕ → Polynomial ℤ
  | 0 => Polynomial.X ^ 2 - 1
  | n + 1 => (padicPoly n) ^ 2 - (2 : Polynomial ℤ) ^ (2 * padicExp2 (n + 1))

/-- Explicit constant-free SLP of length `4 * (n + 2)` computing `padicPoly (n + 1)` for `n : ℕ`.
Wire layout at stage `n` (`τ = 4 * (n + 2)`, wires `0 .. 4 * n + 9`):
- wire `5`: constant `64 = 2^6`
- wire `4 * n + 7` (or `5` when `n = 0`): `c_{n+1} = 2 ^ (2 * padicExp2 (n + 1))`
- wire `4 * n + 9` (output): `padicPoly (n + 1)`
-/
def padicSLP : (n : ℕ) → SLP (4 * (n + 2))
  | 0 =>
      let p1 : SLP 1 := .snoc .nil .mul ⟨1, by omega⟩ ⟨1, by omega⟩   -- w2 = X^2
      let p2 : SLP 2 := .snoc p1 .sub ⟨2, by omega⟩ ⟨0, by omega⟩     -- w3 = X^2 - 1 = P_0
      let p3 : SLP 3 := .snoc p2 .add ⟨0, by omega⟩ ⟨0, by omega⟩     -- w4 = 2
      let p4 : SLP 4 := .snoc p3 .mul ⟨4, by omega⟩ ⟨4, by omega⟩     -- w5 = 4
      let p5 : SLP 5 := .snoc p4 .mul ⟨4, by omega⟩ ⟨5, by omega⟩     -- w6 = 8
      let p6 : SLP 6 := .snoc p5 .mul ⟨6, by omega⟩ ⟨6, by omega⟩     -- w7 = 64 = c_1
      let p7 : SLP 7 := .snoc p6 .mul ⟨3, by omega⟩ ⟨3, by omega⟩     -- w8 = P_0^2
      .snoc p7 .sub ⟨8, by omega⟩ ⟨7, by omega⟩                       -- w9 = P_0^2 - 64 = P_1
  | n + 1 =>
      let prev : SLP (4 * (n + 2)) := padicSLP n
      let s1 : SLP (4 * (n + 2) + 1) :=
        .snoc prev .mul ⟨4 * n + 7, by omega⟩ ⟨4 * n + 7, by omega⟩   -- w_{4n+10} = c_{n+1}^2
      let s2 : SLP (4 * (n + 2) + 2) :=
        .snoc s1 .mul ⟨7, by omega⟩ ⟨4 * n + 10, by omega⟩            -- w_{4n+11} = 64 * c_{n+1}^2 = c_{n+2}
      let s3 : SLP (4 * (n + 2) + 3) :=
        .snoc s2 .mul ⟨4 * n + 9, by omega⟩ ⟨4 * n + 9, by omega⟩     -- w_{4n+12} = P_{n+1}^2
      .snoc s3 .sub ⟨4 * n + 12, by change 4 * n + 12 < 4 * (n + 3) + 1; omega⟩
        ⟨4 * n + 11, by change 4 * n + 11 < 4 * (n + 3) + 1; omega⟩   -- w_{4n+13} = P_{n+2}

theorem padicSLP_wires (n : ℕ) :
    (padicSLP n).evalWire ⟨7, by omega⟩ = (64 : Polynomial ℤ) ∧
    (padicSLP n).evalWire ⟨4 * n + 7, by omega⟩ = (2 : Polynomial ℤ) ^ (2 * padicExp2 (n + 1)) ∧
    (padicSLP n).evalWire ⟨4 * n + 9, by omega⟩ = padicPoly (n + 1) := by
  induction n with
  | zero =>
      refine ⟨?_, ?_, ?_⟩
      · simp [padicSLP, SLP.evalWire, SLPOp.applyPoly]; norm_num
      · simp [padicSLP, SLP.evalWire, SLPOp.applyPoly, padicExp2]; norm_num
      · simp [padicSLP, SLP.evalWire, SLPOp.applyPoly, padicPoly, padicExp2]; ring
  | succ n ih =>
      rcases ih with ⟨h64, hC, hP⟩
      have h7_1 : 7 < 4 * (n + 2) + 2 := by omega
      have h7_2 : 7 < 4 * (n + 2) + 3 := by omega
      have h7_3 : 7 < 4 * (n + 2) + 4 := by omega
      have h7_4 : 7 < 4 * (n + 2) + 5 := by omega
      have hC_1 : 4 * n + 7 < 4 * (n + 2) + 2 := by omega
      have hP_1 : 4 * n + 9 < 4 * (n + 2) + 2 := by omega
      have hP_2 : 4 * n + 9 < 4 * (n + 2) + 3 := by omega
      have hP_3 : 4 * n + 9 < 4 * (n + 2) + 4 := by omega
      refine ⟨?_, ?_, ?_⟩
      · simpa [padicSLP, SLP.evalWire, h7_1, h7_2, h7_3, h7_4] using h64
      · have hstep :
            (padicSLP (n + 1)).evalWire ⟨4 * (n + 1) + 7, by omega⟩ =
              (padicSLP n).evalWire ⟨7, by omega⟩ *
                ((padicSLP n).evalWire ⟨4 * n + 7, by omega⟩ *
                  (padicSLP n).evalWire ⟨4 * n + 7, by omega⟩) := by
          simp only [padicSLP, SLP.evalWire, SLPOp.applyPoly]
          split_ifs <;> first | rfl | omega
        rw [hstep, h64, hC]
        have h64pow : (64 : Polynomial ℤ) = (2 : Polynomial ℤ) ^ 6 := by norm_num
        rw [h64pow, ← pow_add, ← pow_add, padicExp2]
        congr 1
        ring
      · have hstep :
            (padicSLP (n + 1)).evalWire ⟨4 * (n + 1) + 9, by omega⟩ =
              (padicSLP n).evalWire ⟨4 * n + 9, by omega⟩ *
                  (padicSLP n).evalWire ⟨4 * n + 9, by omega⟩ -
                (padicSLP n).evalWire ⟨7, by omega⟩ *
                  ((padicSLP n).evalWire ⟨4 * n + 7, by omega⟩ *
                    (padicSLP n).evalWire ⟨4 * n + 7, by omega⟩) := by
          simp only [padicSLP, SLP.evalWire, SLPOp.applyPoly]
          split_ifs <;> first | rfl | omega
        rw [hstep, h64, hC, hP]
        change (padicPoly (n + 1)) * (padicPoly (n + 1)) -
            (64 : Polynomial ℤ) *
              ((2 : Polynomial ℤ) ^ (2 * padicExp2 (n + 1)) *
                (2 : Polynomial ℤ) ^ (2 * padicExp2 (n + 1))) =
          (padicPoly (n + 1)) ^ 2 - (2 : Polynomial ℤ) ^ (2 * padicExp2 (n + 2))
        have h64pow : (64 : Polynomial ℤ) = (2 : Polynomial ℤ) ^ 6 := by norm_num
        rw [h64pow, ← pow_add, ← pow_add]
        have hexp : 6 + (2 * padicExp2 (n + 1) + 2 * padicExp2 (n + 1)) =
            2 * padicExp2 (n + 2) := by
          simp only [padicExp2]
          ring
        rw [hexp, sq]

theorem padicSLP_evalPoly (n : ℕ) : (padicSLP n).evalPoly = padicPoly (n + 1) := by
  have hfin :
      (⟨4 * (n + 2) + 1, Nat.lt_succ_self _⟩ : Fin (4 * (n + 2) + 2)) =
        ⟨4 * n + 9, by omega⟩ := by
    ext; dsimp; omega
  rw [SLP.evalPoly, hfin]
  exact (padicSLP_wires n).2.2

/-- Every `1 + 8 * t` in `ℤ_[2]` has a square root `u ∈ ℤ_[2]` with `u ≠ -u`. -/
theorem padicInt_exists_sqrt_one_add_eight (t : ℤ_[2]) :
    ∃ u : ℤ_[2], u ^ 2 = 1 + 8 * t ∧ u ≠ -u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let F : Polynomial ℤ_[2] := Polynomial.X ^ 2 - Polynomial.C (1 + 8 * t)
  have hF1 : F.aeval (1 : ℤ_[2]) = -(8 * t) := by
    simp [F]
  have hderiv : F.derivative = 2 * Polynomial.X := by
    simp [F]; ring
  have hFd1 : F.derivative.aeval (1 : ℤ_[2]) = (2 : ℤ_[2]) := by
    simp [hderiv]
  have hnorm2 : ‖(2 : ℤ_[2])‖ = (1 / 2 : ℝ) := by
    simpa [PadicInt.norm_p] using (PadicInt.norm_p (p := 2))
  have hnorm8 : ‖(8 : ℤ_[2])‖ = (1 / 8 : ℝ) := by
    have h8 : (8 : ℤ_[2]) = (2 : ℤ_[2]) ^ 3 := by norm_num
    rw [h8, norm_pow, hnorm2]
    norm_num
  have hnorm_lt : ‖F.aeval (1 : ℤ_[2])‖ < ‖F.derivative.aeval (1 : ℤ_[2])‖ ^ 2 := by
    rw [hF1, hFd1, norm_neg, norm_mul, hnorm8, hnorm2]
    have ht : ‖t‖ ≤ 1 := PadicInt.norm_le_one t
    nlinarith [norm_nonneg t]
  rcases hensels_lemma (p := 2) (F := F) (a := (1 : ℤ_[2])) hnorm_lt with
    ⟨u, hu_root, hu_dist, _, _⟩
  have hu_sq : u ^ 2 = 1 + 8 * t := by
    have h0 : u ^ 2 - (1 + 8 * t) = 0 := by simpa [F] using hu_root
    exact sub_eq_zero.mp h0
  have hu_ne : u ≠ -u := by
    intro heq
    have h2u : (2 : ℤ_[2]) * u = 0 := by
      rw [two_mul]
      calc u + u = u + (-u) := by nth_rw 2 [heq]
        _ = 0 := add_neg_cancel u
    have hu0 : u = 0 := (mul_eq_zero.mp h2u).resolve_left (by norm_num)
    rw [hu0, zero_sub, norm_neg, norm_one, hFd1, hnorm2] at hu_dist
    norm_num at hu_dist
  exact ⟨u, hu_sq, hu_ne⟩

/-- Binary preimage tree in `ℤ_[2]`: for every `n : ℕ` and every `t : ℤ_[2]`, there exist
`2 ^ (n + 1)` distinct elements `r ∈ ℤ_[2]` such that
`Polynomial.aeval r (padicPoly n) = 2 ^ (padicExp2 (n + 1)) * t`. -/
theorem padicPoly_preimages (n : ℕ) :
    ∀ t : ℤ_[2],
      ∃ S : Finset ℤ_[2],
        S.card = 2 ^ (n + 1) ∧
        ∀ r ∈ S, Polynomial.aeval r (padicPoly n) = (2 : ℤ_[2]) ^ (padicExp2 (n + 1)) * t := by
  classical
  induction n with
  | zero =>
      intro t
      rcases padicInt_exists_sqrt_one_add_eight t with ⟨u, hu_sq, hu_ne⟩
      refine ⟨{u, -u}, ?_, ?_⟩
      · rw [Finset.card_pair hu_ne]; norm_num
      · intro r hr
        simp only [Finset.mem_insert, Finset.mem_singleton] at hr
        rcases hr with rfl | rfl
        · simp only [padicPoly, padicExp2, map_sub, map_pow, map_one, Polynomial.aeval_X, hu_sq]
          ring
        · simp only [padicPoly, padicExp2, map_sub, map_pow, map_one, Polynomial.aeval_X, neg_sq,
            hu_sq]
          ring
  | succ n ih =>
      intro t
      rcases padicInt_exists_sqrt_one_add_eight t with ⟨u, hu_sq, hu_ne⟩
      rcases ih u with ⟨S₁, hcard₁, hS₁⟩
      rcases ih (-u) with ⟨S₂, hcard₂, hS₂⟩
      have hdisj : Disjoint S₁ S₂ := by
        rw [Finset.disjoint_left]
        intro r hr₁ hr₂
        have h1 := hS₁ r hr₁
        have h2 := hS₂ r hr₂
        have heq : (2 : ℤ_[2]) ^ padicExp2 (n + 1) * u =
            (2 : ℤ_[2]) ^ padicExp2 (n + 1) * (-u) := h1.symm.trans h2
        have h2ne : (2 : ℤ_[2]) ^ padicExp2 (n + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
        exact hu_ne (mul_left_cancel₀ h2ne heq)
      refine ⟨S₁ ∪ S₂, ?_, ?_⟩
      · rw [Finset.card_union_of_disjoint hdisj, hcard₁, hcard₂, pow_succ]
        ring
      · intro r hr
        have hexp : padicExp2 (n + 2) = 2 * padicExp2 (n + 1) + 3 := by rfl
        simp only [padicPoly, map_sub, map_pow, map_ofNat]
        rcases Finset.mem_union.mp hr with hr₁ | hr₂
        · rw [hS₁ r hr₁, mul_pow, hu_sq, hexp, pow_add, ← pow_mul]
          have h23 : (2 : ℤ_[2]) ^ 3 = 8 := by norm_num
          rw [h23, mul_comm (padicExp2 (n + 1)) 2]
          ring
        · rw [hS₂ r hr₂, mul_pow, neg_sq, hu_sq, hexp, pow_add, ← pow_mul]
          have h23 : (2 : ℤ_[2]) ^ 3 = 8 := by norm_num
          rw [h23, mul_comm (padicExp2 (n + 1)) 2]
          ring

/-- `padicPoly m` is monic of degree `2 ^ (m + 1)`. -/
theorem padicPoly_monic_and_deg (m : ℕ) :
    (padicPoly m).Monic ∧ (padicPoly m).natDegree = 2 ^ (m + 1) := by
  induction m with
  | zero =>
      simp only [padicPoly]
      have hlt : (1 : Polynomial ℤ).degree < (Polynomial.X ^ 2 : Polynomial ℤ).degree := by
        simp [Polynomial.degree_one]
      have hmon : (Polynomial.X ^ 2 - (1 : Polynomial ℤ)).Monic :=
        (Polynomial.monic_X_pow 2).sub_of_left hlt
      have hdeg : (Polynomial.X ^ 2 - (1 : Polynomial ℤ)).natDegree = 2 := by
        rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
        · simp
        · simp
      exact ⟨hmon, by simpa using hdeg⟩
  | succ m ih =>
      rcases ih with ⟨hm, hd⟩
      simp only [padicPoly]
      have hsq_m : (padicPoly m ^ 2).Monic := hm.pow 2
      have hsq_d : (padicPoly m ^ 2).natDegree = 2 ^ (m + 2) := by
        rw [Polynomial.natDegree_pow, hd, pow_succ]; ring
      have hc_d : ((2 : Polynomial ℤ) ^ (2 * padicExp2 (m + 1))).natDegree = 0 := by
        rw [show (2 : Polynomial ℤ) = Polynomial.C 2 by simp, ← map_pow, Polynomial.natDegree_C]
      have hc_lt : ((2 : Polynomial ℤ) ^ (2 * padicExp2 (m + 1))).natDegree <
          (padicPoly m ^ 2).natDegree := by
        rw [hc_d, hsq_d]; positivity
      have hdeg_lt : ((2 : Polynomial ℤ) ^ (2 * padicExp2 (m + 1))).degree <
          (padicPoly m ^ 2).degree := by
        have hc_le : ((2 : Polynomial ℤ) ^ (2 * padicExp2 (m + 1))).degree ≤ 0 := by
          rw [show (2 : Polynomial ℤ) = Polynomial.C 2 by simp, ← map_pow]
          exact Polynomial.degree_C_le
        rw [Polynomial.degree_eq_natDegree hsq_m.ne_zero, hsq_d]
        exact lt_of_le_of_lt hc_le (by exact_mod_cast (by positivity : 0 < 2 ^ (m + 2)))
      exact ⟨hsq_m.sub_of_left hdeg_lt,
        by rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hc_lt, hsq_d]⟩

/-- **Unconditional $2$-Adic Exponential Lower Bound (`z_max^{ℤ_2}(4k) ≥ 2^k`):**
For every `k ≥ 2`, there exists a constant-free SLP of length `4 * k` computing a nonzero
polynomial `f ∈ ℤ[X]` with at least `2 ^ k` distinct roots in the $2$-adic integers `ℤ_[2]`. -/
theorem tau_padic_two_pow (k : ℕ) (hk : 2 ≤ k) :
    ∃ P : SLP (4 * k),
      P.evalPoly ≠ 0 ∧
      ∃ S : Finset ℤ_[2],
        S.card = 2 ^ k ∧ ∀ r ∈ S, Polynomial.aeval r P.evalPoly = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
  refine ⟨padicSLP n, ?_, ?_⟩
  · rw [padicSLP_evalPoly]
    exact (padicPoly_monic_and_deg (n + 1)).1.ne_zero
  · rcases padicPoly_preimages (n + 1) 0 with ⟨S, hcard, hS⟩
    refine ⟨S, hcard, ?_⟩
    intro r hr
    rw [padicSLP_evalPoly, hS r hr, mul_zero]

end Research.PvsNP.Tau

end