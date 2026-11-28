module

public import Research.PvsNP.Tau.ChirpZ
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace Research.PvsNP.Tau

/-!
# Division-Free Schönhage–Nussbaumer FFT & Unconditional Refutation of Every Sub-Quadratic Exponent (`c < 2`)

This module formalizes:
1. Negacyclic convolution `negConv N a b` over `R = ℤ[X]` (representing multiplication in
   `R[Y] / (Y^N + 1)`), together with exact shift-and-negate multiplication by `Y^s` (`negShift`).
2. Division-free cyclic DFT of power-of-2 size `K = 2^p` over `R[Z] / (Z^(2M) + 1)` using
   the exact power-of-`Z` root of unity `ω = Z^(2 * step)` (`K * step = 2 * M`), proving
   both Cooley–Tukey `CanBuild` gate complexity `O(p * 2^p * M)` and exact orthogonality
   `IDFT (DFT A) = K • A` over `ℤ[X]` without divisions.
3. Recursive Schönhage–Nussbaumer negacyclic multiplication of size `2^k` (with base case
   `k ≤ 3`), achieving exact uniform positive power-of-2 scaling `2^(snScale k)` in
   `snCost k ≤ C_sn * k * (Nat.log 2 k + 1) * 2^k` constant-free gates.
4. Combined with `ChirpZ.zMaxGe_of_chirp_engine` at `N_fft = 2 * m = 2^(k + 1)`:
   - `tau_subquadratic_growth`: `∃ C > 0, ∀ k ≥ 2, zMaxGe (C * k * (Nat.log 2 k + 1) * 2^k) (2 * 4^k + 1)`.
   - `tau_refutes_subquadratic`: for **every real exponent `c < 2`**,
     `¬ ∃ a : ℝ, ∀ (τ : ℕ) (P : SLP τ), P.evalPoly ≠ 0 → (intRootCount P.evalPoly : ℝ) ≤ a * ((τ : ℝ) + 1) ^ c`.
-/

/-! ## 1. Negacyclic Convolution and Shifts over `ℤ[X]` -/

/-- Exact negacyclic convolution of length `N` over `ℤ[X]`, representing the coefficient of `Y^t`
in `(∑_{i < N} a i * Y^i) * (∑_{j < N} b j * Y^j) mod (Y^N + 1)`. -/
noncomputable def negConv (N : ℕ) (a b : ℕ → Polynomial ℤ) (t : ℕ) : Polynomial ℤ :=
  ∑ i ∈ Finset.range N, if i ≤ t then a i * b (t - i) else -(a i * b (t + N - i))

/-- Multiplication by `Y^s` in `(ℤ[X])[Y] / (Y^N + 1)`, evaluated at coefficient `t < N`. -/
noncomputable def negShift (N s : ℕ) (a : ℕ → Polynomial ℤ) (t : ℕ) : Polynomial ℤ :=
  (-1 : Polynomial ℤ) ^ (s / N) *
    (if s % N ≤ t then a (t - s % N) else -(a (t + N - s % N)))

theorem negConv_chirp_eq (m i : ℕ) (hm : 1 ≤ m) (_hi : i < m) :
    negConv (2 * m) (chirpA m) (chirpB m) (i + m) =
      ∑ r ∈ Finset.range (m + 1), chirpA m r * chirpB m (i + m - r) := by
  unfold negConv
  have hsub : Finset.range (m + 1) ⊆ Finset.range (2 * m) := Finset.range_mono (by omega)
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl ?_
    intro r hr
    rw [Finset.mem_range] at hr
    have hle : r ≤ i + m := by omega
    simp [hle]
  · intro r hr hnot
    rw [Finset.mem_range] at hr hnot
    have hgt : ¬ r ≤ m := by omega
    simp [chirpA, hgt]

theorem negShift_zero (N : ℕ) (_hN : 0 < N) (a : ℕ → Polynomial ℤ) (t : ℕ) :
    negShift N 0 a t = a t := by
  simp [negShift, Nat.zero_div, Nat.zero_mod]

theorem negShift_add_N (N s : ℕ) (hN : 0 < N) (a : ℕ → Polynomial ℤ) (t : ℕ) :
    negShift N (s + N) a t = -(negShift N s a t) := by
  unfold negShift
  rw [Nat.add_div_right s hN, Nat.add_mod_right, pow_succ]
  ring

theorem negShift_add_mul_N (N s q : ℕ) (hN : 0 < N) (a : ℕ → Polynomial ℤ) (t : ℕ) :
    negShift N (s + q * N) a t = (-1 : Polynomial ℤ) ^ q * negShift N s a t := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [show s + (q + 1) * N = (s + q * N) + N by ring, negShift_add_N N _ hN, ih, pow_succ]
      ring

theorem negShift_mod_two_N (N s₁ s₂ : ℕ) (hN : 0 < N)
    (hmod : s₁ % (2 * N) = s₂ % (2 * N)) (a : ℕ → Polynomial ℤ) (t : ℕ) :
    negShift N s₁ a t = negShift N s₂ a t := by
  have hred : ∀ s, negShift N s a t = negShift N (s % (2 * N)) a t := by
    intro s
    have hdiv := Nat.div_add_mod s (2 * N)
    have h1 : s = s % (2 * N) + (2 * (s / (2 * N))) * N := by linarith
    conv_lhs => rw [h1]
    rw [negShift_add_mul_N N _ _ hN, pow_mul]
    norm_num
  rw [hred s₁, hred s₂, hmod]

theorem negShift_add (N s₁ s₂ : ℕ) (hN : 0 < N) (a : ℕ → Polynomial ℤ) (t : ℕ) (ht : t < N) :
    negShift N (s₁ + s₂) a t = negShift N s₁ (negShift N s₂ a) t := by
  have hdecomp : ∀ s f x,
      negShift N s f x = (-1 : Polynomial ℤ) ^ (s / N) * negShift N (s % N) f x := by
    intro s f x
    have hdiv := Nat.div_add_mod s N
    have h1 : s = s % N + (s / N) * N := by linarith
    conv_lhs => rw [h1]
    rw [negShift_add_mul_N N _ _ hN]
  rw [hdecomp s₁, hdecomp (s₁ + s₂)]
  have hlinear_smul : ∀ s (c : Polynomial ℤ) f x,
      negShift N s (fun y => c * f y) x = c * negShift N s f x := by
    intro s c f x; unfold negShift; split_ifs <;> ring
  have hrhs : negShift N (s₁ % N) (negShift N s₂ a) t =
      (-1 : Polynomial ℤ) ^ (s₂ / N) * negShift N (s₁ % N) (negShift N (s₂ % N) a) t := by
    have hfn : negShift N s₂ a = fun x => (-1 : Polynomial ℤ) ^ (s₂ / N) * negShift N (s₂ % N) a x := by
      funext x; exact hdecomp s₂ a x
    rw [hfn, hlinear_smul]
  rw [hrhs]
  set r₁ := s₁ % N
  set r₂ := s₂ % N
  have hr₁ : r₁ < N := Nat.mod_lt s₁ hN
  have hr₂ : r₂ < N := Nat.mod_lt s₂ hN
  have hq : (s₁ + s₂) / N = s₁ / N + s₂ / N + (r₁ + r₂) / N := by
    have h1 := Nat.div_add_mod s₁ N
    have h2 := Nat.div_add_mod s₂ N
    have hr1_eq : r₁ = s₁ % N := rfl
    have hr2_eq : r₂ = s₂ % N := rfl
    have h3 : s₁ + s₂ = (r₁ + r₂) + (s₁ / N + s₂ / N) * N := by linarith
    rw [h3, Nat.add_mul_div_right _ _ hN]
    omega
  have hr : (s₁ + s₂) % N = (r₁ + r₂) % N := Nat.add_mod s₁ s₂ N
  rw [hq, hr, pow_add, pow_add]
  have hcore :
      (-1 : Polynomial ℤ) ^ ((r₁ + r₂) / N) * negShift N ((r₁ + r₂) % N) a t =
        negShift N r₁ (negShift N r₂ a) t := by
    unfold negShift
    have hdiv1 : r₁ / N = 0 := Nat.div_eq_of_lt hr₁
    have hmod1 : r₁ % N = r₁ := Nat.mod_eq_of_lt hr₁
    have hdiv2 : r₂ / N = 0 := Nat.div_eq_of_lt hr₂
    have hmod2 : r₂ % N = r₂ := Nat.mod_eq_of_lt hr₂
    have hmod_lt : (r₁ + r₂) % N < N := Nat.mod_lt _ hN
    have hdiv_m : ((r₁ + r₂) % N) / N = 0 := Nat.div_eq_of_lt hmod_lt
    have hmod_m : ((r₁ + r₂) % N) % N = (r₁ + r₂) % N := Nat.mod_eq_of_lt hmod_lt
    simp only [hdiv1, hmod1, hdiv2, hmod2, hdiv_m, hmod_m, pow_zero, one_mul]
    by_cases hsum : r₁ + r₂ < N
    · have hd0 : (r₁ + r₂) / N = 0 := Nat.div_eq_of_lt hsum
      have hm0 : (r₁ + r₂) % N = r₁ + r₂ := Nat.mod_eq_of_lt hsum
      rw [hd0, hm0, pow_zero, one_mul]
      by_cases ht1 : r₁ ≤ t
      · by_cases ht2 : r₂ ≤ t - r₁
        · have ht12 : r₁ + r₂ ≤ t := by omega
          have hidx : t - (r₁ + r₂) = t - r₁ - r₂ := by omega
          simp [ht1, ht2, ht12, hidx]
        · have ht12 : ¬ (r₁ + r₂ ≤ t) := by omega
          have hidx : t + N - (r₁ + r₂) = t - r₁ + N - r₂ := by omega
          simp [ht1, ht2, ht12, hidx]
      · have ht12 : ¬ (r₁ + r₂ ≤ t) := by omega
        have ht2 : r₂ ≤ t + N - r₁ := by omega
        have hidx : t + N - (r₁ + r₂) = t + N - r₁ - r₂ := by omega
        simp [ht1, ht2, ht12, hidx]
    · have hlt2N : r₁ + r₂ - N < N := by omega
      have hsum_eq : r₁ + r₂ = (r₁ + r₂ - N) + N := by omega
      have hd1 : (r₁ + r₂) / N = 1 := by
        rw [hsum_eq, Nat.add_div_right _ hN, Nat.div_eq_of_lt hlt2N]
      have hm1 : (r₁ + r₂) % N = r₁ + r₂ - N := by
        conv_lhs => rw [hsum_eq]
        rw [Nat.add_mod_right, Nat.mod_eq_of_lt hlt2N]
      rw [hd1, hm1, pow_one]
      by_cases ht1 : r₁ ≤ t
      · have ht2 : ¬ (r₂ ≤ t - r₁) := by omega
        have ht12 : r₁ + r₂ - N ≤ t := by omega
        have hidx : t - (r₁ + r₂ - N) = t - r₁ + N - r₂ := by omega
        simp [ht1, ht2, ht12, hidx]
      · by_cases ht2 : r₂ ≤ t + N - r₁
        · have ht12 : r₁ + r₂ - N ≤ t := by omega
          have hidx : t - (r₁ + r₂ - N) = t + N - r₁ - r₂ := by omega
          simp [ht1, ht2, ht12, hidx]
        · have ht12 : ¬ (r₁ + r₂ - N ≤ t) := by omega
          have hidx : t + N - (r₁ + r₂ - N) = t + N - r₁ + N - r₂ := by omega
          simp [ht1, ht2, ht12, hidx]
  calc
    (-1 : Polynomial ℤ) ^ (s₁ / N) * (-1 : Polynomial ℤ) ^ (s₂ / N) *
        (-1 : Polynomial ℤ) ^ ((r₁ + r₂) / N) * negShift N ((r₁ + r₂) % N) a t
        = (-1 : Polynomial ℤ) ^ (s₁ / N) * (-1 : Polynomial ℤ) ^ (s₂ / N) *
            ((-1 : Polynomial ℤ) ^ ((r₁ + r₂) / N) * negShift N ((r₁ + r₂) % N) a t) := by ring
    _ = (-1 : Polynomial ℤ) ^ (s₁ / N) * ((-1 : Polynomial ℤ) ^ (s₂ / N) *
            negShift N r₁ (negShift N r₂ a) t) := by rw [hcore]; ring

theorem negShift_add_linear (N s : ℕ) (a b : ℕ → Polynomial ℤ) (t : ℕ) :
    negShift N s (fun x => a x + b x) t = negShift N s a t + negShift N s b t := by
  unfold negShift; split_ifs <;> ring

theorem negShift_neg_linear (N s : ℕ) (a : ℕ → Polynomial ℤ) (t : ℕ) :
    negShift N s (fun x => -(a x)) t = -(negShift N s a t) := by
  unfold negShift; split_ifs <;> ring

theorem negShift_smul_linear (N s : ℕ) (c : Polynomial ℤ) (a : ℕ → Polynomial ℤ) (t : ℕ) :
    negShift N s (fun x => c * a x) t = c * negShift N s a t := by
  unfold negShift; split_ifs <;> ring

theorem negShift_finset_sum {ι : Type*} (S : Finset ι) (N s : ℕ)
    (f : ι → ℕ → Polynomial ℤ) (t : ℕ) :
    negShift N s (fun x => ∑ i ∈ S, f i x) t = ∑ i ∈ S, negShift N s (f i) t := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [negShift]
  | insert i S hi ih =>
      simp only [Finset.sum_insert hi]
      rw [negShift_add_linear, ih]

theorem negConv_add_left (N : ℕ) (a₁ a₂ b : ℕ → Polynomial ℤ) (t : ℕ) :
    negConv N (fun i => a₁ i + a₂ i) b t = negConv N a₁ b t + negConv N a₂ b t := by
  unfold negConv
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _; split_ifs <;> ring

theorem negConv_add_right (N : ℕ) (a b₁ b₂ : ℕ → Polynomial ℤ) (t : ℕ) :
    negConv N a (fun j => b₁ j + b₂ j) t = negConv N a b₁ t + negConv N a b₂ t := by
  unfold negConv
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _; split_ifs <;> ring

theorem negConv_sum_left {ι : Type*} (S : Finset ι) (N : ℕ)
    (f : ι → ℕ → Polynomial ℤ) (b : ℕ → Polynomial ℤ) (t : ℕ) :
    negConv N (fun i => ∑ u ∈ S, f u i) b t = ∑ u ∈ S, negConv N (f u) b t := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [negConv]
  | insert u S hu ih =>
      simp only [Finset.sum_insert hu]
      rw [negConv_add_left, ih]

theorem negConv_sum_right {ι : Type*} (S : Finset ι) (N : ℕ)
    (a : ℕ → Polynomial ℤ) (g : ι → ℕ → Polynomial ℤ) (t : ℕ) :
    negConv N a (fun j => ∑ v ∈ S, g v j) t = ∑ v ∈ S, negConv N a (g v) t := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [negConv]
  | insert v S hv ih =>
      simp only [Finset.sum_insert hv]
      rw [negConv_add_right, ih]

theorem negConv_neg_left (N : ℕ) (a b : ℕ → Polynomial ℤ) (t : ℕ) :
    negConv N (fun i => -(a i)) b t = -(negConv N a b t) := by
  unfold negConv
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _; split_ifs <;> ring

theorem negConv_neg_right (N : ℕ) (a b : ℕ → Polynomial ℤ) (t : ℕ) :
    negConv N a (fun j => -(b j)) t = -(negConv N a b t) := by
  unfold negConv
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _; split_ifs <;> ring

theorem negConv_congr_left (N : ℕ) (a₁ a₂ b : ℕ → Polynomial ℤ)
    (h : ∀ i < N, a₁ i = a₂ i) (t : ℕ) :
    negConv N a₁ b t = negConv N a₂ b t := by
  unfold negConv
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [h i (Finset.mem_range.mp hi)]

theorem negShift_congr (N s : ℕ) (hN : 0 < N) (a₁ a₂ : ℕ → Polynomial ℤ)
    (h : ∀ i < N, a₁ i = a₂ i) (t : ℕ) (ht : t < N) :
    negShift N s a₁ t = negShift N s a₂ t := by
  unfold negShift
  have hmod : s % N < N := Nat.mod_lt s hN
  split_ifs with hst
  · rw [h (t - s % N) (by omega)]
  · rw [h (t + N - s % N) (by omega)]

theorem negConv_comm (N : ℕ) (a b : ℕ → Polynomial ℤ) (t : ℕ) (ht : t < N) :
    negConv N a b t = negConv N b a t := by
  unfold negConv
  refine Finset.sum_bij (fun i _ => if i ≤ t then t - i else t + N - i) ?_ ?_ ?_ ?_
  · intro i hi; rw [Finset.mem_range] at hi ⊢; split_ifs <;> omega
  · intro i₁ hi₁ i₂ hi₂ heq; rw [Finset.mem_range] at hi₁ hi₂; split_ifs at heq <;> omega
  · intro j hj; rw [Finset.mem_range] at hj
    by_cases hjt : j ≤ t
    · refine ⟨t - j, Finset.mem_range.mpr (by omega), ?_⟩
      have : t - j ≤ t := by omega
      simp [this]; omega
    · refine ⟨t + N - j, Finset.mem_range.mpr (by omega), ?_⟩
      have : ¬ (t + N - j ≤ t) := by omega
      simp [this]; omega
  · intro i hi; rw [Finset.mem_range] at hi
    by_cases hit : i ≤ t
    · have hj : t - i ≤ t := by omega
      have hb : t - (t - i) = i := by omega
      simp [hit, hj, hb, mul_comm]
    · have hj : ¬ (t + N - i ≤ t) := by omega
      have hb : t + N - (t + N - i) = i := by omega
      simp [hit, hj, hb, mul_comm]

/-- Shifting `a` by `Y^s` commutes with `negConv N`. -/
theorem negConv_negShift_left (N s : ℕ) (hN : 0 < N) (a b : ℕ → Polynomial ℤ)
    (t : ℕ) (ht : t < N) :
    negConv N (negShift N s a) b t = negShift N s (negConv N a b) t := by
  have hstep1 : ∀ (f : ℕ → Polynomial ℤ) (u : ℕ), u < N →
      negConv N (negShift N 1 f) b u = negShift N 1 (negConv N f b) u := by
    intro f u hu
    by_cases hN1 : N = 1
    · subst hN1
      have hu0 : u = 0 := by omega
      subst hu0
      simp [negConv, negShift]
    · have h1lt : 1 < N := by omega
      have hdiv1 : 1 / N = 0 := Nat.div_eq_of_lt h1lt
      have hmod1 : 1 % N = 1 := Nat.mod_eq_of_lt h1lt
      unfold negConv negShift
      simp only [hdiv1, hmod1, pow_zero, one_mul]
      have hLHS :
          ∑ i ∈ Finset.range N,
              (if i ≤ u then (if 1 ≤ i then f (i - 1) else -f (i + N - 1)) * b (u - i)
               else -((if 1 ≤ i then f (i - 1) else -f (i + N - 1)) * b (u + N - i))) =
            ∑ j ∈ Finset.range N,
              if 1 ≤ u then
                if j ≤ u - 1 then f j * b (u - 1 - j) else -(f j * b (u - 1 + N - j))
              else
                -(if j ≤ u + N - 1 then f j * b (u + N - 1 - j) else -(f j * b (u + N - 1 + N - j))) := by
        refine Finset.sum_bij (fun i _ => if 1 ≤ i then i - 1 else N - 1) ?_ ?_ ?_ ?_
        · intro i hi; rw [Finset.mem_range] at hi ⊢; split_ifs <;> omega
        · intro i₁ hi₁ i₂ hi₂ heq; rw [Finset.mem_range] at hi₁ hi₂; split_ifs at heq <;> omega
        · intro j hj; rw [Finset.mem_range] at hj
          by_cases hjN : j = N - 1
          · exact ⟨0, Finset.mem_range.mpr (by omega), by simp [hjN]⟩
          · exact ⟨j + 1, Finset.mem_range.mpr (by omega), by simp⟩
        · intro i hi
          rw [Finset.mem_range] at hi
          by_cases hi1 : 1 ≤ i
          · by_cases hu1 : 1 ≤ u
            · by_cases hiu : i ≤ u
              · have hj : i - 1 ≤ u - 1 := by omega
                have hb : u - i = u - 1 - (i - 1) := by omega
                simp [hi1, hu1, hiu, hj, hb]
              · have hj : ¬ (i - 1 ≤ u - 1) := by omega
                have hb : u + N - i = u - 1 + N - (i - 1) := by omega
                simp [hi1, hu1, hiu, hj, hb]
            · have hu0 : u = 0 := by omega
              have hiu : ¬ (i ≤ u) := by omega
              have hj : i - 1 ≤ u + N - 1 := by omega
              have hb : u + N - i = u + N - 1 - (i - 1) := by omega
              simp [hi1, hu1, hiu, hj, hb]
          · have hi0 : i = 0 := by omega
            subst hi0
            by_cases hu1 : 1 ≤ u
            · have hiu : 0 ≤ u := by omega
              have hj : ¬ (N - 1 ≤ u - 1) := by omega
              have hb : u - 0 = u - 1 + N - (N - 1) := by omega
              simp only [Nat.not_le.mpr (by omega : 0 < 1), ↓reduceIte, hiu, hu1, hj, Nat.zero_add,
                hb]
              ring
            · have hu0 : u = 0 := by omega
              subst hu0
              have hj : N - 1 ≤ 0 + N - 1 := by omega
              have hb : 0 + N - 1 - (N - 1) = 0 := by omega
              simp
      rw [hLHS]
      by_cases hu1 : 1 ≤ u
      · simp [hu1]
      · simp [hu1, Finset.sum_neg_distrib]
  induction s generalizing t with
  | zero =>
      rw [negConv_congr_left N _ a b (fun i _ => negShift_zero N hN a i), negShift_zero N hN]
  | succ s ih =>
      rw [negConv_congr_left N _ (negShift N 1 (negShift N s a)) b
        (fun i hi => by rw [Nat.add_comm, negShift_add N 1 s hN a i hi])]
      rw [hstep1 (negShift N s a) t ht]
      rw [negShift_congr N 1 hN _ (negShift N s (negConv N a b)) (fun i hi => ih i hi) t ht]
      rw [← negShift_add N 1 s hN _ t ht, Nat.add_comm]

/-- Shifting `b` by `Y^s` commutes with `negConv N`. -/
theorem negConv_negShift_right (N s : ℕ) (hN : 0 < N) (a b : ℕ → Polynomial ℤ)
    (t : ℕ) (ht : t < N) :
    negConv N a (negShift N s b) t = negShift N s (negConv N a b) t := by
  rw [negConv_comm N a _ t ht, negConv_negShift_left N s hN b a t ht]
  exact negShift_congr N s hN _ _ (fun i hi => negConv_comm N b a i hi) t ht

/-! ## 2. `CanBuild` for `negShift` and Schoolbook Base Case (`k ≤ 3`) -/

/-- Applying `negShift N s` to a length-`N` vector costs at most `N` gates (`0 - a j`). -/
theorem canBuild_negShift (N s : ℕ) (hN : 0 < N) (a : ℕ → Polynomial ℤ) :
    CanBuild ({(0 : Polynomial ℤ)} ∪ ⋃ i < N, {a i}) N
      (⋃ t < N, {negShift N s a t}) := by
  have h := canBuild_fin_union (n := N) (d := 1)
    (S := {(0 : Polynomial ℤ)} ∪ ⋃ i < N, {a i})
    (T := fun t => {negShift N s a t}) (by
      intro t ht
      have hmod : s % N < N := Nat.mod_lt s hN
      set j := if s % N ≤ t then t - s % N else t + N - s % N
      have hj : j < N := by dsimp only [j]; split_ifs <;> omega
      have hval : negShift N s a t = a j ∨ negShift N s a t = -(a j) := by
        unfold negShift
        rcases Nat.even_or_odd (s / N) with ⟨m, hm⟩ | ⟨m, hm⟩
        · rw [hm, show m + m = 2 * m by ring, pow_mul]
          norm_num
          split_ifs with hst
          · left; simp [j, hst]
          · right; simp [j, hst]
        · rw [hm, pow_add, pow_mul]
          norm_num
          split_ifs with hst
          · right; simp [j, hst]
          · left; simp [j, hst]
      rcases hval with hpos | hneg
      · refine canBuild_mono_cost (by omega : 0 ≤ 1) (canBuild_subset ?_)
        intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx
        rw [hpos]; right; simp only [Set.mem_iUnion, exists_prop]; exact ⟨j, hj, rfl⟩
      · have hsub := canBuild_sub (0 : Polynomial ℤ) (a j)
        refine canBuild_mono_out (by intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx; rw [hneg]; simp)
          (canBuild_mono_in ?_ hsub)
        intro x hx
        rcases hx with rfl | rfl
        · left; rfl
        · right; simp only [Set.mem_iUnion, exists_prop]; exact ⟨j, hj, rfl⟩)
  simpa using h

/-- Schoolbook negacyclic convolution of length `N` costs `3 * N * N` gates. -/
theorem canBuild_negConv_schoolbook (N : ℕ) (a b : ℕ → Polynomial ℤ) :
    CanBuild ({(0 : Polynomial ℤ)} ∪ (⋃ i < N, {a i}) ∪ (⋃ j < N, {b j})) (3 * N * N)
      (⋃ t < N, {negConv N a b t}) := by
  have h1 := canBuild_fin_union (n := N) (d := 3 * N)
    (S := {(0 : Polynomial ℤ)} ∪ (⋃ i < N, {a i}) ∪ (⋃ j < N, {b j}))
    (T := fun t => {negConv N a b t}) (by
      intro t ht
      let term : ℕ → Polynomial ℤ := fun i =>
        if i ≤ t then a i * b (t - i) else -(a i * b (t + N - i))
      have hterms : CanBuild ({(0 : Polynomial ℤ)} ∪ (⋃ i < N, {a i}) ∪ (⋃ j < N, {b j}))
          (N * 2) (⋃ i < N, {term i}) := by
        refine canBuild_fin_union (n := N) (d := 2) (T := fun i => {term i}) ?_
        intro i hi
        by_cases hit : i ≤ t
        · have hm := canBuild_mul (a i) (b (t - i))
          refine canBuild_mono_cost (by omega : 1 ≤ 2)
            (canBuild_mono_out (by intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx; simp [term, hit])
              (canBuild_mono_in ?_ hm))
          intro x hx
          rcases hx with rfl | rfl
          · left; right; simp only [Set.mem_iUnion, exists_prop]; exact ⟨i, hi, rfl⟩
          · right; simp only [Set.mem_iUnion, exists_prop]; exact ⟨t - i, by omega, rfl⟩
        · have hm := canBuild_mul (a i) (b (t + N - i))
          have hn := canBuild_sub (0 : Polynomial ℤ) (a i * b (t + N - i))
          have hmn := canBuild_trans
            (canBuild_mono_in (S₂ := {(0 : Polynomial ℤ), a i, b (t + N - i)})
              (by intro x hx; rcases hx with rfl | rfl <;> simp) hm)
            (by intro x hx; rcases hx with rfl | rfl <;> simp) hn
          refine canBuild_mono_out
            (by intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx; right; simp [term, hit])
            (canBuild_mono_in ?_ hmn)
          intro x hx
          rcases hx with rfl | rfl | rfl
          · left; left; rfl
          · left; right; simp only [Set.mem_iUnion, exists_prop]; exact ⟨i, hi, rfl⟩
          · right; simp only [Set.mem_iUnion, exists_prop]; exact ⟨t + N - i, by omega, rfl⟩
      have hsum := canBuild_fin_sum N term
      have hcomb := canBuild_trans hterms (by
        intro x hx; rcases hx with rfl | hx'
        · left; left; left; rfl
        · right; exact hx') hsum
      have hcost : N * 2 + N = 3 * N := by ring
      rw [hcost] at hcomb
      exact canBuild_mono_out (fun x hx => Or.inr hx) hcomb)
  have hcost : N * (3 * N) = 3 * N * N := by ring
  rwa [hcost] at h1

/-! ## 3. Division-Free Cyclic DFT over `R[Z] / (Z^L + 1)` -/

/-- Exact cyclic DFT of length `K` in `R[Z] / (Z^L + 1)` using twiddle angle `ang`
(multiplication by `Z^(ang * u * j)`):
`ringDFT L K ang A u t = ∑_{j < K} negShift L (ang * u * j) (A j) t`. -/
noncomputable def ringDFT (L K ang : ℕ) (A : ℕ → ℕ → Polynomial ℤ) (u t : ℕ) : Polynomial ℤ :=
  ∑ j ∈ Finset.range K, negShift L (ang * u * j) (A j) t

/-- Exact orthogonality of `ringDFT` over any commutative ring (zero divisions!):
if `K = 2^p` and `K * step = L` (`L > 0`), then for `0 < d < K`:
`∑_{u < K} negShift L (2 * step * u * d) x t = 0` for all `t < L`. -/
theorem negShift_geom_sum_zero :
    ∀ (p step L : ℕ), 0 < L → 2 ^ p * step = L →
      ∀ (d : ℕ), 0 < d → d < 2 ^ p →
        ∀ (x : ℕ → Polynomial ℤ) (t : ℕ), t < L →
          ∑ u ∈ Finset.range (2 ^ p), negShift L (2 * step * u * d) x t = 0
  | 0, _, _, _, _, d, hd0, hd1, _, _, _ => by simp at hd1; omega
  | p + 1, step, L, hL, hKS, d, hd0, hd1, x, t, ht => by
      have h2p : 2 ^ (p + 1) = 2 ^ p + 2 ^ p := by rw [pow_succ]; ring
      rw [h2p, Finset.sum_range_add, ← Finset.sum_add_distrib]
      have hshift_half : ∀ u : ℕ,
          negShift L (2 * step * (2 ^ p + u) * d) x t =
            (-1 : Polynomial ℤ) ^ d * negShift L (2 * step * u * d) x t := by
        intro u
        have heq : 2 * step * (2 ^ p + u) * d = 2 * step * u * d + d * L := by
          have : 2 * 2 ^ p * step = L := by rw [← hKS, pow_succ]; ring
          calc 2 * step * (2 ^ p + u) * d = 2 * step * u * d + d * (2 * 2 ^ p * step) := by ring
            _ = 2 * step * u * d + d * L := by rw [this]
        rw [heq, negShift_add_mul_N L _ d hL]
      rcases Nat.even_or_odd d with ⟨d', hd'⟩ | ⟨d', hd'⟩
      · have hsum2 :
            ∑ u ∈ Finset.range (2 ^ p),
                (negShift L (2 * step * u * d) x t + negShift L (2 * step * (2 ^ p + u) * d) x t) =
              2 * ∑ u ∈ Finset.range (2 ^ p), negShift L (2 * (2 * step) * u * d') x t := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro u _
          rw [hshift_half u, hd', show d' + d' = 2 * d' by ring, pow_mul]
          have harg : 2 * step * u * (2 * d') = 2 * (2 * step) * u * d' := by ring
          rw [harg]
          norm_num
          ring
        rw [hsum2]
        have hKS' : 2 ^ p * (2 * step) = L := by rw [← hKS, pow_succ]; ring
        have hzero := negShift_geom_sum_zero p (2 * step) L hL hKS' d' (by omega) (by omega) x t ht
        rw [hzero, mul_zero]
      · refine Finset.sum_eq_zero ?_
        intro u _
        rw [hshift_half u, hd', pow_add, pow_mul]
        norm_num

/-- **Exact Inversion of Division-Free `ringDFT`:**
If `K = 2^p`, `K * step = L` (`L > 0`), and `ang = 2 * step`, `angInv = 2 * step * (K - 1)`,
then `ringDFT L K angInv (ringDFT L K ang A) v t = (K : Polynomial ℤ) * A v t` for all `v < K, t < L`. -/
theorem ringDFT_inversion (p step L : ℕ) (hL : 0 < L) (hKS : 2 ^ p * step = L)
    (A : ℕ → ℕ → Polynomial ℤ) (v t : ℕ) (hv : v < 2 ^ p) (ht : t < L) :
    ringDFT L (2 ^ p) (2 * step * (2 ^ p - 1)) (ringDFT L (2 ^ p) (2 * step) A) v t =
      ((2 ^ p : ℕ) : Polynomial ℤ) * A v t := by
  set K := 2 ^ p
  have hKpos : 1 ≤ K := Nat.one_le_two_pow
  unfold ringDFT
  -- Push `negShift` inside the inner sum and swap sums over `u` and `j`
  have hpush :
      ∑ u ∈ Finset.range K,
          negShift L (2 * step * (K - 1) * v * u)
            (fun x => ∑ j ∈ Finset.range K, negShift L (2 * step * u * j) (A j) x) t =
        ∑ j ∈ Finset.range K,
          ∑ u ∈ Finset.range K,
            negShift L (2 * step * (K - 1) * v * u + 2 * step * u * j) (A j) t := by
    have h1 :
        ∀ u ∈ Finset.range K,
          negShift L (2 * step * (K - 1) * v * u)
            (fun x => ∑ j ∈ Finset.range K, negShift L (2 * step * u * j) (A j) x) t =
          ∑ j ∈ Finset.range K,
            negShift L (2 * step * (K - 1) * v * u + 2 * step * u * j) (A j) t := by
      intro u _
      rw [negShift_finset_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [negShift_add L _ _ hL _ t ht]
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  rw [hpush]
  -- Simplify the inner sum for each `j < K`: equals `K * A v t` if `j = v`, and `0` if `j ≠ v`
  have hinner :
      ∀ j ∈ Finset.range K,
        (∑ u ∈ Finset.range K,
            negShift L (2 * step * (K - 1) * v * u + 2 * step * u * j) (A j) t) =
          if j = v then ((K : ℕ) : Polynomial ℤ) * A j t else 0 := by
    intro j hj
    rw [Finset.mem_range] at hj
    by_cases hjv : j = v
    · subst hjv
      simp only [↓reduceIte]
      have hterm : ∀ u ∈ Finset.range K,
          negShift L (2 * step * (K - 1) * j * u + 2 * step * u * j) (A j) t = A j t := by
        intro u _
        have hmod : (2 * step * (K - 1) * j * u + 2 * step * u * j) % (2 * L) = 0 % (2 * L) := by
          have heq : 2 * step * (K - 1) * j * u + 2 * step * u * j = (j * u) * (2 * L) := by
            have hK1 : (K - 1) + 1 = K := by omega
            calc 2 * step * (K - 1) * j * u + 2 * step * u * j
                = 2 * step * ((K - 1) + 1) * j * u := by ring
              _ = 2 * step * K * j * u := by rw [hK1]
              _ = (j * u) * (2 * (K * step)) := by ring
              _ = (j * u) * (2 * L) := by rw [hKS]
          rw [heq, Nat.mul_mod_left, Nat.zero_mod]
        rw [negShift_mod_two_N L _ 0 hL hmod, negShift_zero L hL]
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    · simp only [hjv, ↓reduceIte]
      set d := (j + K - v) % K
      have hd0 : 0 < d := by
        dsimp only [d]
        by_cases hlt : v < j
        · have : (j + K - v) % K = j - v := by
            rw [show j + K - v = (j - v) + K by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          omega
        · have : (j + K - v) % K = j + K - v := Nat.mod_eq_of_lt (by omega)
          omega
      have hdK : d < K := Nat.mod_lt _ (by omega)
      have hmod_term : ∀ u ∈ Finset.range K,
          negShift L (2 * step * (K - 1) * v * u + 2 * step * u * j) (A j) t =
            negShift L (2 * step * u * d) (A j) t := by
        intro u _
        refine negShift_mod_two_N L _ _ hL ?_ (A j) t
        -- Both exponents are congruent mod `2 * L = 2 * K * step`
        have hmodK : ((K - 1) * v + j) % K = d := by
          rcases Nat.eq_zero_or_pos v with rfl | hvpos
          · simp [d]
          · have h1 : (K - 1) * v + j = (j + K - v) + (v - 1) * K := by
              zify [hKpos, hvpos, show v ≤ j + K by omega]; ring
            rw [h1, Nat.add_mul_mod_self_right]
        have hmul : (2 * step * u * ((K - 1) * v + j)) % (2 * L) = (2 * step * u * d) % (2 * L) := by
          have hdiv := Nat.div_add_mod ((K - 1) * v + j) K
          have h2 : (K - 1) * v + j = d + (((K - 1) * v + j) / K) * K := by linarith
          rw [h2, mul_add]
          have h3 : 2 * step * u * ((((K - 1) * v + j) / K) * K) =
              (u * (((K - 1) * v + j) / K)) * (2 * L) := by
            rw [← hKS]; ring
          rw [h3, Nat.add_mul_mod_self_right]
        have hcomm : 2 * step * (K - 1) * v * u + 2 * step * u * j =
            2 * step * u * ((K - 1) * v + j) := by ring
        rw [hcomm, hmul]
      rw [Finset.sum_congr rfl hmod_term]
      exact negShift_geom_sum_zero p step L hL hKS d hd0 hdK (A j) t ht
  rw [Finset.sum_congr rfl hinner, Finset.sum_ite_eq']
  simp [hv]

/-- **Convolution Theorem for `ringDFT`:**
If `K = 2^p` and `K * step = L` (`L > 0`), then pointwise `negConv L` in the `ringDFT` domain
inverts to `K` times the cyclic convolution in `R[Z]/(Z^L + 1)`. -/
theorem ringDFT_convolution (p step L : ℕ) (hL : 0 < L) (hKS : 2 ^ p * step = L)
    (A B : ℕ → ℕ → Polynomial ℤ) (v t : ℕ) (hv : v < 2 ^ p) (ht : t < L) :
    ringDFT L (2 ^ p) (2 * step * (2 ^ p - 1))
        (fun u => negConv L (ringDFT L (2 ^ p) (2 * step) A u)
          (ringDFT L (2 ^ p) (2 * step) B u)) v t =
      ((2 ^ p : ℕ) : Polynomial ℤ) *
        ∑ j₁ ∈ Finset.range (2 ^ p),
          negConv L (A j₁) (B ((v + 2 ^ p - j₁) % 2 ^ p)) t := by
  set K := 2 ^ p
  -- Expand pointwise product as `ringDFT` of the cyclic convolution `C`!
  let C : ℕ → ℕ → Polynomial ℤ := fun w x =>
    ∑ j₁ ∈ Finset.range K, negConv L (A j₁) (B ((w + K - j₁) % K)) x
  have hpointwise : ∀ u < K, ∀ x < L,
      negConv L (ringDFT L K (2 * step) A u) (ringDFT L K (2 * step) B u) x =
        ringDFT L K (2 * step) C u x := by
    intro u _ x hx
    unfold ringDFT
    rw [negConv_sum_left]
    simp_rw [negConv_sum_right]
    have hshift :
        ∑ j₁ ∈ Finset.range K, ∑ j₂ ∈ Finset.range K,
            negConv L (negShift L (2 * step * u * j₁) (A j₁))
              (negShift L (2 * step * u * j₂) (B j₂)) x =
          ∑ j₁ ∈ Finset.range K, ∑ j₂ ∈ Finset.range K,
            negShift L (2 * step * u * (j₁ + j₂)) (negConv L (A j₁) (B j₂)) x := by
      refine Finset.sum_congr rfl ?_
      intro j₁ _
      refine Finset.sum_congr rfl ?_
      intro j₂ _
      rw [negConv_negShift_left L _ hL _ _ x hx]
      rw [negShift_congr L _ hL _ _ (fun y hy => negConv_negShift_right L _ hL (A j₁) (B j₂) y hy) x hx]
      rw [← negShift_add L _ _ hL _ x hx]
      congr 1
      ring
    rw [hshift]
    have hrhs :
        ∑ w ∈ Finset.range K, negShift L (2 * step * u * w) (C w) x =
          ∑ j₁ ∈ Finset.range K, ∑ w ∈ Finset.range K,
            negShift L (2 * step * u * w) (negConv L (A j₁) (B ((w + K - j₁) % K))) x := by
      simp_rw [C, negShift_finset_sum]
      exact Finset.sum_comm
    rw [hrhs]
    refine Finset.sum_congr rfl ?_
    intro j₁ hj₁
    rw [Finset.mem_range] at hj₁
    refine Finset.sum_bij (fun j₂ _ => (j₁ + j₂) % K) ?_ ?_ ?_ ?_
    · intro j₂ _; exact Finset.mem_range.mpr (Nat.mod_lt _ (by positivity))
    · intro a ha b hb heq
      rw [Finset.mem_range] at ha hb
      have hsub : ∀ z < K, ((j₁ + z) % K + K - j₁) % K = z := by
        intro z hz
        by_cases hlt : j₁ + z < K
        · rw [Nat.mod_eq_of_lt hlt, show j₁ + z + K - j₁ = z + K by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt hz]
        · have hmod_sub : (j₁ + z) % K = j₁ + z - K := by
            have h1 : j₁ + z = (j₁ + z - K) + K := by omega
            conv_lhs => rw [h1]
            rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          rw [hmod_sub, show j₁ + z - K + K - j₁ = z by omega, Nat.mod_eq_of_lt hz]
      rw [← hsub a ha, ← hsub b hb, heq]
    · intro w hw
      rw [Finset.mem_range] at hw
      refine ⟨(w + K - j₁) % K, Finset.mem_range.mpr (Nat.mod_lt _ (by positivity)), ?_⟩
      by_cases hlt : j₁ ≤ w
      · rw [show w + K - j₁ = (w - j₁) + K by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega : w - j₁ < K), show j₁ + (w - j₁) = w by omega,
          Nat.mod_eq_of_lt hw]
      · rw [Nat.mod_eq_of_lt (by omega : w + K - j₁ < K),
          show j₁ + (w + K - j₁) = w + K by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hw]
    · intro j₂ hj₂
      rw [Finset.mem_range] at hj₂
      have hback : ((j₁ + j₂) % K + K - j₁) % K = j₂ := by
        by_cases hlt : j₁ + j₂ < K
        · rw [Nat.mod_eq_of_lt hlt, show j₁ + j₂ + K - j₁ = j₂ + K by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt hj₂]
        · have hmod_sub : (j₁ + j₂) % K = j₁ + j₂ - K := by
            have h1 : j₁ + j₂ = (j₁ + j₂ - K) + K := by omega
            conv_lhs => rw [h1]
            rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          rw [hmod_sub, show j₁ + j₂ - K + K - j₁ = j₂ by omega, Nat.mod_eq_of_lt hj₂]
      rw [hback]
      refine negShift_mod_two_N L _ _ hL ?_ _ x
      have hdiv := Nat.div_add_mod (j₁ + j₂) K
      have h1 : j₁ + j₂ = (j₁ + j₂) % K + ((j₁ + j₂) / K) * K := by linarith
      conv_lhs => rw [h1]
      rw [mul_add]
      have h2 : 2 * step * u * (((j₁ + j₂) / K) * K) = (u * ((j₁ + j₂) / K)) * (2 * L) := by
        rw [← hKS]; ring
      rw [h2, Nat.add_mul_mod_self_right]
  have hcongr :
      ringDFT L K (2 * step * (K - 1))
          (fun u => negConv L (ringDFT L K (2 * step) A u) (ringDFT L K (2 * step) B u)) v t =
        ringDFT L K (2 * step * (K - 1)) (ringDFT L K (2 * step) C) v t := by
    unfold ringDFT
    refine Finset.sum_congr rfl ?_
    intro u hu
    exact negShift_congr L _ hL _ _ (fun x hx => hpointwise u (Finset.mem_range.mp hu) x hx) t ht
  rw [hcongr]
  exact ringDFT_inversion p step L hL hKS C v t hv ht

/-- Cooley–Tukey gate cost for `ringDFT` of size `2^p` on length-`L` vectors: `3 * p * 2^p * L`. -/
def dftCost (p L : ℕ) : ℕ := 3 * p * 2 ^ p * L

/-- **Cooley–Tukey Butterfly `CanBuild` for `ringDFT`:**
Given `{0} ∪ {A j t | j < 2^p, t < L}`, computes `{ringDFT L (2^p) ang A u t | u < 2^p, t < L}`
in `dftCost p L = 3 * p * 2^p * L` gates, whenever `2^p * ang` is a multiple of `2 * L`
(Wait: specifically whenever `2^(p - 1) * ang ≡ L (mod 2 * L)`, i.e. `ang = 2 * step * c` with `c` odd
and `2^p * step = L`!). -/
theorem canBuild_ringDFT :
    ∀ (p step c L : ℕ), 0 < L → 2 ^ p * step = L → Odd c →
      ∀ (A : ℕ → ℕ → Polynomial ℤ),
        CanBuild
          ({(0 : Polynomial ℤ)} ∪ ⋃ j < 2 ^ p, ⋃ t < L, {A j t})
          (dftCost p L)
          (⋃ u < 2 ^ p, ⋃ t < L, {ringDFT L (2 ^ p) (2 * step * c) A u t})
  | 0, step, c, L, hL, _, _, A => by
      simp only [dftCost, mul_zero, zero_mul]
      refine canBuild_subset ?_
      intro x hx
      simp only [Set.mem_iUnion, exists_prop, Set.mem_singleton_iff] at hx
      rcases hx with ⟨u, hu, t, ht, rfl⟩
      have hu0 : u = 0 := by omega
      subst hu0
      right
      simp only [Set.mem_iUnion, exists_prop]
      refine ⟨0, by omega, t, ht, ?_⟩
      simp [ringDFT, negShift_zero L hL]
  | p + 1, step, c, L, hL, hKS, hc, A => by
      set K' := 2 ^ p
      have hKS' : K' * (2 * step) = L := by rw [← hKS, pow_succ]; ring
      let Aeven : ℕ → ℕ → Polynomial ℤ := fun j => A (2 * j)
      let Aodd : ℕ → ℕ → Polynomial ℤ := fun j => A (2 * j + 1)
      let E := ringDFT L K' (2 * (2 * step) * c) Aeven
      let O := ringDFT L K' (2 * (2 * step) * c) Aodd
      let T : ℕ → ℕ → Polynomial ℤ := fun u => negShift L (2 * step * c * u) (O u)
      set S0 : Set (Polynomial ℤ) :=
        {(0 : Polynomial ℤ)} ∪ ⋃ j < 2 ^ (p + 1), ⋃ t < L, {A j t}
      -- Step 1: Recursive DFT on Aeven and Aodd (`2 * dftCost p L` gates)
      have hE := canBuild_ringDFT p (2 * step) c L hL hKS' hc Aeven
      have hO := canBuild_ringDFT p (2 * step) c L hL hKS' hc Aodd
      have c1 := canBuild_mono_in (S₂ := S0) (by
        intro x hx; rcases hx with rfl | hx'
        · left; rfl
        · right; simp only [Set.mem_iUnion, exists_prop] at hx' ⊢
          rcases hx' with ⟨j, hj, t, ht, hxt⟩
          exact ⟨2 * j, by rw [pow_succ]; omega, t, ht, hxt⟩) hE
      have c2 := canBuild_trans c1 (by
        intro x hx; rcases hx with rfl | hx'
        · left; left; rfl
        · left; right; simp only [Set.mem_iUnion, exists_prop] at hx' ⊢
          rcases hx' with ⟨j, hj, t, ht, hxt⟩
          exact ⟨2 * j + 1, by rw [pow_succ]; omega, t, ht, hxt⟩) hO
      -- Step 2: Twiddle O u by `2 * step * c * u` for `u < K'` (`K' * L` gates)
      have hT :
          CanBuild ({(0 : Polynomial ℤ)} ∪ ⋃ u < K', ⋃ t < L, {O u t})
            (K' * L) (⋃ u < K', ⋃ t < L, {T u t}) := by
        refine canBuild_fin_union (n := K') (d := L) (T := fun u => ⋃ t < L, {T u t}) ?_
        intro u hu
        refine canBuild_mono_in ?_ (canBuild_negShift L (2 * step * c * u) hL (O u))
        intro x hx; rcases hx with rfl | hx'
        · left; rfl
        · right; simp only [Set.mem_iUnion, exists_prop] at hx' ⊢
          rcases hx' with ⟨t, ht, hxt⟩; exact ⟨u, hu, t, ht, hxt⟩
      have c3 := canBuild_trans c2 (by
        intro x hx; rcases hx with rfl | hx'
        · left; left; rfl
        · right; right; exact hx') hT
      -- Step 3: Butterflies `E u t + T u t` and `E u t - T u t` for `u < K', t < L` (`2 * K' * L` gates)
      have hB :
          CanBuild ((⋃ u < K', ⋃ t < L, {E u t}) ∪ (⋃ u < K', ⋃ t < L, {T u t}))
            (K' * (L * 2))
            (⋃ u < K', ⋃ t < L, ({E u t + T u t, E u t - T u t} : Set (Polynomial ℤ))) := by
        refine canBuild_fin_union (n := K') (d := L * 2)
          (T := fun u => ⋃ t < L, ({E u t + T u t, E u t - T u t} : Set (Polynomial ℤ))) ?_
        intro u hu
        refine canBuild_fin_union (n := L) (d := 2)
          (T := fun t => ({E u t + T u t, E u t - T u t} : Set (Polynomial ℤ))) ?_
        intro t ht
        have ha := canBuild_add (E u t) (T u t)
        have hs := canBuild_sub (E u t) (T u t)
        have has := canBuild_trans ha Set.subset_union_left hs
        refine canBuild_mono_in ?_ has
        intro x hx
        rcases hx with rfl | rfl
        · left; simp only [Set.mem_iUnion, exists_prop]; exact ⟨u, hu, t, ht, rfl⟩
        · right; simp only [Set.mem_iUnion, exists_prop]; exact ⟨u, hu, t, ht, rfl⟩
      have c4 := canBuild_trans c3 (by
        intro x hx; rcases hx with hxE | hxT
        · right; left; left; exact hxE
        · right; right; exact hxT) hB
      -- Check butterfly identity:
      -- `ringDFT L (2*K') (2*step*c) A u t = E u t + T u t` (for `u < K'`)
      -- `ringDFT L (2*K') (2*step*c) A (u + K') t = E u t - T u t` (for `u < K'`)
      have hsplit_dft : ∀ u t, t < L →
          ringDFT L (2 ^ (p + 1)) (2 * step * c) A u t =
            E (u % K') t + negShift L (2 * step * c * u) (O (u % K')) t := by
        intro u t ht
        unfold ringDFT
        have h2K : 2 ^ (p + 1) = 2 * K' := by rw [pow_succ]; ring
        rw [h2K]
        -- Split `range (2 * K')` into even `2 * j` and odd `2 * j + 1`
        have heven_odd : ∀ f : ℕ → Polynomial ℤ,
            ∑ j ∈ Finset.range (2 * K'), f j =
              (∑ j ∈ Finset.range K', f (2 * j)) + (∑ j ∈ Finset.range K', f (2 * j + 1)) := by
          intro f
          clear h2K
          induction K' with
          | zero => simp
          | succ n ihn =>
              rw [show 2 * (n + 1) = 2 * n + 2 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
                ihn, Finset.sum_range_succ, Finset.sum_range_succ]
              ring
        rw [heven_odd]
        congr 1
        · dsimp only [E, ringDFT, Aeven]
          refine Finset.sum_congr rfl ?_
          intro j _
          refine negShift_mod_two_N L _ _ hL ?_ _ t
          have hdiv := Nat.div_add_mod u K'
          have hu_eq : u = u % K' + (u / K') * K' := by linarith
          conv_lhs => rw [hu_eq]
          have h1 : 2 * step * c * (u % K' + u / K' * K') * (2 * j) =
              2 * (2 * step) * c * (u % K') * j + (c * (u / K') * j) * (2 * L) := by
            rw [← hKS']; ring
          rw [h1, Nat.add_mul_mod_self_right]
        · have hOfn : O (u % K') = fun x =>
              ∑ j ∈ Finset.range K', negShift L (2 * (2 * step) * c * (u % K') * j) (Aodd j) x := rfl
          rw [hOfn, negShift_finset_sum]
          dsimp only [Aodd]
          refine Finset.sum_congr rfl ?_
          intro j _
          rw [← negShift_add L _ _ hL _ t ht]
          refine negShift_mod_two_N L _ _ hL ?_ _ t
          have hdiv := Nat.div_add_mod u K'
          have hu_eq : u = u % K' + (u / K') * K' := by linarith
          have h1 : 2 * step * c * u * (2 * j + 1) =
              2 * step * c * u + 2 * (2 * step) * c * u * j := by ring
          rw [h1]
          conv_lhs => rw [show 2 * (2 * step) * c * u * j =
            2 * (2 * step) * c * (u % K' + u / K' * K') * j by rw [← hu_eq]]
          have h2 : 2 * step * c * u + 2 * (2 * step) * c * (u % K' + u / K' * K') * j =
              (2 * step * c * u + 2 * (2 * step) * c * (u % K') * j) +
                (c * (u / K') * j) * (2 * L) := by
            rw [← hKS']; ring
          rw [h2, Nat.add_mul_mod_self_right]
      have hcost : dftCost p L + dftCost p L + K' * L + K' * (L * 2) ≤ dftCost (p + 1) L := by
        simp only [dftCost, K', pow_succ]
        have h1 : 3 * p * 2 ^ p * L + 3 * p * 2 ^ p * L + 2 ^ p * L + 2 ^ p * (L * 2) =
            (6 * p + 3) * (2 ^ p * L) := by ring
        have h2 : 3 * (p + 1) * (2 ^ p * 2) * L = (6 * p + 6) * (2 ^ p * L) := by ring
        rw [h1, h2]
        exact Nat.mul_le_mul_right (2 ^ p * L) (by omega)
      refine canBuild_mono_cost hcost (canBuild_mono_out ?_ c4)
      intro x hx
      simp only [Set.mem_iUnion, exists_prop, Set.mem_singleton_iff] at hx
      rcases hx with ⟨u, hu, t, ht, rfl⟩
      rw [hsplit_dft u t ht]
      by_cases huK : u < K'
      · rw [Nat.mod_eq_of_lt huK]
        right; simp only [Set.mem_iUnion, exists_prop]
        exact ⟨u, huK, t, ht, Or.inl rfl⟩
      · set u' := u - K'
        have hu' : u' < K' := by rw [pow_succ] at hu; omega
        have hu_eq : u = u' + K' := by omega
        have hmod : u % K' = u' := by rw [hu_eq, Nat.add_mod_right, Nat.mod_eq_of_lt hu']
        rw [hmod]
        have htw : negShift L (2 * step * c * u) (O u') t = -(T u' t) := by
          dsimp only [T]
          have harg : 2 * step * c * u = 2 * step * c * u' + c * L := by
            rw [hu_eq, ← hKS']; ring
          rw [harg, negShift_add_mul_N L _ c hL]
          rcases hc with ⟨m, rfl⟩
          rw [pow_add, pow_mul]
          norm_num
        rw [htw, ← sub_eq_add_neg]
        right; simp only [Set.mem_iUnion, exists_prop]
        exact ⟨u', hu', t, ht, Or.inr rfl⟩

/-! ## 4. Recursive Schönhage–Nussbaumer Negacyclic Multiplication (`k ≥ 4`, Base `k ≤ 3`) -/

/-- Recursive size parameter `snSub k = (k + 1) / 2 + 1` (`2 * M` exponent).
For `k ≥ 4`, `snSub k < k`. -/
def snSub (k : ℕ) : ℕ := (k + 1) / 2 + 1

theorem snSub_lt (k : ℕ) (hk : 4 ≤ k) : snSub k < k := by
  unfold snSub; omega

/-- Uniform positive power-of-2 scale exponent `snScale k` produced by `canBuild_snMul`. -/
def snScale : ℕ → ℕ
  | k =>
      if h : k ≤ 3 then 0
      else snScale (snSub k) + k / 2
termination_by k => k
decreasing_by exact snSub_lt k (by omega)

/-- Exact gate cost `snCost k` of division-free Schönhage–Nussbaumer negacyclic multiplication
of length `2^k`. -/
def snCost : ℕ → ℕ
  | k =>
      if h : k ≤ 3 then 3 * (2 ^ k) * (2 ^ k)
      else
        let p := k / 2
        let K := 2 ^ p
        let L := 2 ^ (snSub k)
        K * snCost (snSub k) + 3 * dftCost p L + 3 * K * L + 2 * 2 ^ k
termination_by k => k
decreasing_by exact snSub_lt k (by omega)

/-- Chunk-recombination identity for Schönhage–Nussbaumer:
splitting length `N = K * M` into `K` chunks of length `M` (zero-padded to `2 * M`),
computing the negacyclic convolution of length `K` in `R[Z]/(Z^(2M) + 1)`, and recombining
overlapping halves recovers `negConv (K * M) a b` identically. -/
theorem negConv_chunk_recombine (K M : ℕ) (hK : 1 ≤ K) (hM : 1 ≤ M)
    (a b : ℕ → Polynomial ℤ) (q r : ℕ) (hq : q < K) (hr : r < M) :
    let A : ℕ → ℕ → Polynomial ℤ := fun j u => if u < M then a (j * M + u) else 0
    let B : ℕ → ℕ → Polynomial ℤ := fun j u => if u < M then b (j * M + u) else 0
    let C : ℕ → ℕ → Polynomial ℤ := fun w u =>
      ∑ j₁ ∈ Finset.range K,
        if j₁ ≤ w then negConv (2 * M) (A j₁) (B (w - j₁)) u
        else -(negConv (2 * M) (A j₁) (B (w + K - j₁)) u)
    negConv (K * M) a b (q * M + r) =
      C q r + (if 0 < q then C (q - 1) (r + M) else -(C (K - 1) (r + M))) := by
  intro A B C
  -- Helper: for any `j₁, j₂ < K`, compute `negConv (2*M) (A j₁) (B j₂) u` for `u = r` and `u = r + M`
  have hchunk_lo : ∀ j₁ j₂,
      negConv (2 * M) (A j₁) (B j₂) r =
        ∑ r₁ ∈ Finset.range M, if r₁ ≤ r then a (j₁ * M + r₁) * b (j₂ * M + (r - r₁)) else 0 := by
    intro j₁ j₂
    unfold negConv
    have hsub : Finset.range M ⊆ Finset.range (2 * M) := Finset.range_mono (by omega)
    rw [← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl ?_
      intro r₁ hr₁
      rw [Finset.mem_range] at hr₁
      by_cases hle : r₁ ≤ r
      · have hlt : r - r₁ < M := by omega
        simp [hle, A, B, hr₁, hlt]
      · have hnot : ¬ (r + 2 * M - r₁ < M) := by omega
        simp [hle, A, B, hr₁, hnot]
    · intro r₁ hr₁ hnot
      rw [Finset.mem_range] at hr₁ hnot
      have hge : ¬ (r₁ < M) := by omega
      simp [A, hge]
  have hchunk_hi : ∀ j₁ j₂,
      negConv (2 * M) (A j₁) (B j₂) (r + M) =
        ∑ r₁ ∈ Finset.range M, if r < r₁ then a (j₁ * M + r₁) * b (j₂ * M + (r + M - r₁)) else 0 := by
    intro j₁ j₂
    unfold negConv
    have hsub : Finset.range M ⊆ Finset.range (2 * M) := Finset.range_mono (by omega)
    rw [← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl ?_
      intro r₁ hr₁
      rw [Finset.mem_range] at hr₁
      have hle : r₁ ≤ r + M := by omega
      by_cases hgt : r < r₁
      · have hlt : r + M - r₁ < M := by omega
        simp [hle, hgt, A, B, hr₁, hlt]
      · have hnot : ¬ (r + M - r₁ < M) := by omega
        simp [hle, hgt, A, B, hr₁, hnot]
    · intro r₁ hr₁ hnot
      rw [Finset.mem_range] at hr₁ hnot
      have hge : ¬ (r₁ < M) := by omega
      simp [A, hge]
  -- Rewrite LHS as double sum over `j₁ < K, r₁ < M`
  have hLHS :
      negConv (K * M) a b (q * M + r) =
        ∑ j₁ ∈ Finset.range K, ∑ r₁ ∈ Finset.range M,
          if j₁ * M + r₁ ≤ q * M + r then
            a (j₁ * M + r₁) * b (q * M + r - (j₁ * M + r₁))
          else
            -(a (j₁ * M + r₁) * b (q * M + r + K * M - (j₁ * M + r₁))) := by
    unfold negConv
    rw [← Finset.sum_product']
    refine Finset.sum_bij (fun i _ => (i / M, i % M)) ?_ ?_ ?_ ?_
    · intro i hi
      rw [Finset.mem_range] at hi
      simp only [Finset.mem_product, Finset.mem_range]
      exact ⟨Nat.div_lt_of_lt_mul (by rwa [mul_comm]), Nat.mod_lt i (by omega)⟩
    · intro i₁ hi₁ i₂ hi₂ heq
      have h1 := congrArg Prod.fst heq
      have h2 := congrArg Prod.snd heq
      have d1 := Nat.div_add_mod i₁ M
      have d2 := Nat.div_add_mod i₂ M
      dsimp at h1 h2
      rw [h1, h2] at d1
      linarith
    · intro p hp
      simp only [Finset.mem_product, Finset.mem_range] at hp
      refine ⟨p.1 * M + p.2, Finset.mem_range.mpr (by nlinarith), ?_⟩
      ext
      · dsimp
        rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hp.2, add_zero]
      · dsimp
        rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hp.2]
    · intro i _
      have hi_eq : i / M * M + i % M = i := by
        have := Nat.div_add_mod i M; linarith
      simp [hi_eq]
  rw [hLHS]
  -- Push the `if 0 < q` inside the `j₁` sum on RHS and match term-by-term!
  have hRHS :
      C q r + (if 0 < q then C (q - 1) (r + M) else -(C (K - 1) (r + M))) =
        ∑ j₁ ∈ Finset.range K,
          ((if j₁ ≤ q then negConv (2 * M) (A j₁) (B (q - j₁)) r
            else -(negConv (2 * M) (A j₁) (B (q + K - j₁)) r)) +
           (if 0 < q then
              if j₁ ≤ q - 1 then negConv (2 * M) (A j₁) (B (q - 1 - j₁)) (r + M)
              else -(negConv (2 * M) (A j₁) (B (q - 1 + K - j₁)) (r + M))
            else
              -(if j₁ ≤ K - 1 then negConv (2 * M) (A j₁) (B (K - 1 - j₁)) (r + M)
                else -(negConv (2 * M) (A j₁) (B (K - 1 + K - j₁)) (r + M))))) := by
    dsimp only [C]
    split_ifs with hq0
    · rw [← Finset.sum_add_distrib]
    · rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  rw [hRHS]
  refine Finset.sum_congr rfl ?_
  intro j₁ hj₁
  rw [Finset.mem_range] at hj₁
  simp only [hchunk_lo, hchunk_hi]
  -- Split LHS inner sum into `r₁ ≤ r` and `r < r₁` and match each case of `j₁` vs `q`
  have hinner_split : ∀ (f : ℕ → Polynomial ℤ),
      ∑ r₁ ∈ Finset.range M, f r₁ =
        (∑ r₁ ∈ Finset.range M, if r₁ ≤ r then f r₁ else 0) +
        (∑ r₁ ∈ Finset.range M, if r < r₁ then f r₁ else 0) := by
    intro f
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro r₁ _
    by_cases h : r₁ ≤ r
    · have h' : ¬ (r < r₁) := by omega
      simp [h, h']
    · have h' : r < r₁ := by omega
      simp [h, h']
  rw [hinner_split]
  congr 1
  · -- Lower half (`r₁ ≤ r`): `j₁ * M + r₁ ≤ q * M + r ↔ j₁ ≤ q`
    by_cases hjq : j₁ ≤ q
    · simp only [hjq, ↓reduceIte]
      refine Finset.sum_congr rfl ?_
      intro r₁ hr₁; rw [Finset.mem_range] at hr₁
      by_cases hle : r₁ ≤ r
      · have hmain : j₁ * M + r₁ ≤ q * M + r := by nlinarith
        have hidx : q * M + r - (j₁ * M + r₁) = (q - j₁) * M + (r - r₁) := by
          zify [hjq, hle, hmain]; ring
        simp [hle, hmain, hidx]
      · simp [hle]
    · simp only [hjq, ↓reduceIte, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl ?_
      intro r₁ hr₁; rw [Finset.mem_range] at hr₁
      by_cases hle : r₁ ≤ r
      · have hmain : ¬ (j₁ * M + r₁ ≤ q * M + r) := by nlinarith
        have hidx : q * M + r + K * M - (j₁ * M + r₁) = (q + K - j₁) * M + (r - r₁) := by
          have h1 : j₁ ≤ q + K := by omega
          have h2 : j₁ * M + r₁ ≤ q * M + r + K * M := by nlinarith
          zify [h1, hle, h2]; ring
        simp [hle, hmain, hidx]
      · simp [hle]
  · -- Upper half (`r < r₁`): `j₁ * M + r₁ ≤ q * M + r ↔ j₁ < q`
    by_cases hq0 : 0 < q
    · simp only [hq0, ↓reduceIte]
      by_cases hjq : j₁ ≤ q - 1
      · simp only [hjq, ↓reduceIte]
        refine Finset.sum_congr rfl ?_
        intro r₁ hr₁; rw [Finset.mem_range] at hr₁
        by_cases hgt : r < r₁
        · have hmain : j₁ * M + r₁ ≤ q * M + r := by
            have : j₁ + 1 ≤ q := by omega
            nlinarith
          have hidx : q * M + r - (j₁ * M + r₁) = (q - 1 - j₁) * M + (r + M - r₁) := by
            have h1 : j₁ + 1 ≤ q := by omega
            have h2 : r₁ ≤ r + M := by omega
            zify [h1, hq0, hjq, h2, hmain]; ring
          simp [hgt, hmain, hidx]
        · simp [hgt]
      · simp only [hjq, ↓reduceIte, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl ?_
        intro r₁ hr₁; rw [Finset.mem_range] at hr₁
        by_cases hgt : r < r₁
        · have hmain : ¬ (j₁ * M + r₁ ≤ q * M + r) := by
            have : q ≤ j₁ := by omega
            nlinarith
          have hidx : q * M + r + K * M - (j₁ * M + r₁) = (q - 1 + K - j₁) * M + (r + M - r₁) := by
            have h1 : j₁ ≤ q - 1 + K := by omega
            have h2 : r₁ ≤ r + M := by omega
            have h3 : j₁ * M + r₁ ≤ q * M + r + K * M := by
              have : j₁ + 1 ≤ q + K := by omega
              nlinarith
            zify [hq0, h1, h2, h3]; ring
          simp [hgt, hmain, hidx]
        · simp [hgt]
    · have hq_zero : q = 0 := by omega
      subst hq_zero
      have hjK : j₁ ≤ K - 1 := by omega
      simp only [lt_self_iff_false, ↓reduceIte, hjK, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl ?_
      intro r₁ hr₁; rw [Finset.mem_range] at hr₁
      by_cases hgt : r < r₁
      · have hmain : ¬ (j₁ * M + r₁ ≤ r) := by nlinarith
        have hidx : r + K * M - (j₁ * M + r₁) = (K - 1 - j₁) * M + (r + M - r₁) := by
          have h2 : r₁ ≤ r + M := by omega
          have h3 : j₁ * M + r₁ ≤ r + K * M := by nlinarith
          zify [hK, hjK, h2, h3]; ring
        simp [hgt, hmain, hidx]
      · simp [hgt]

/-- **Division-Free Schönhage–Nussbaumer Negacyclic Multiplication (`CanBuild`):**
For every `k : ℕ`, given `{0} ∪ {a i | i < 2^k} ∪ {b j | j < 2^k}`, computes
`{(2 : ℤ) ^ (snScale k) * negConv (2^k) a b t | t < 2^k}` in `snCost k` constant-free gates. -/
theorem canBuild_snMul :
    ∀ (k : ℕ) (a b : ℕ → Polynomial ℤ),
      CanBuild
        ({(0 : Polynomial ℤ)} ∪ (⋃ i < 2 ^ k, {a i}) ∪ (⋃ j < 2 ^ k, {b j}))
        (snCost k)
        (⋃ t < 2 ^ k, {((2 : Polynomial ℤ) ^ snScale k) * negConv (2 ^ k) a b t})
  | k, a, b => by
      by_cases hk : k ≤ 3
      · rw [snCost, snScale]
        simp only [hk, ↓reduceDIte, pow_zero, one_mul]
        exact canBuild_negConv_schoolbook (2 ^ k) a b
      · have hk4 : 4 ≤ k := by omega
        have hsub_lt : snSub k < k := snSub_lt k hk4
        set p := k / 2
        set K := 2 ^ p
        set M := 2 ^ (k - p)
        set L := 2 ^ snSub k
        have hKM : K * M = 2 ^ k := by
          simp only [K, M, ← pow_add]; congr 1; omega
        have hL2M : L = 2 * M := by
          simp only [L, M, snSub]
          have : (k + 1) / 2 + 1 = (k - k / 2) + 1 := by omega
          rw [this, pow_succ]; ring
        have hKpos : 1 ≤ K := Nat.one_le_two_pow
        have hMpos : 1 ≤ M := Nat.one_le_two_pow
        have hL : 0 < L := by positivity
        -- `step = L / K`: since `k - p = p` or `p + 1`, `L = 2 * M = K * 2` or `K * 4`
        set step := 2 ^ (snSub k - p)
        have hKS : K * step = L := by
          simp only [K, step, L, ← pow_add]
          congr 1; unfold snSub; omega
        -- Chunk arrays `A, B` (size K, each length L = 2*M, zero-padded past M)
        let A : ℕ → ℕ → Polynomial ℤ := fun j u => if u < M then a (j * M + u) else 0
        let B : ℕ → ℕ → Polynomial ℤ := fun j u => if u < M then b (j * M + u) else 0
        -- Twist by `ζ^j = Z^(step * j)`
        let Atw : ℕ → ℕ → Polynomial ℤ := fun j => negShift L (step * j) (A j)
        let Btw : ℕ → ℕ → Polynomial ℤ := fun j => negShift L (step * j) (B j)
        -- Forward DFT with `ang = 2 * step * 1`
        let Ahat := ringDFT L K (2 * step * 1) Atw
        let Bhat := ringDFT L K (2 * step * 1) Btw
        -- Pointwise scaled negacyclic products of size `L = 2^(snSub k)`
        let Phat : ℕ → ℕ → Polynomial ℤ := fun u t =>
          ((2 : Polynomial ℤ) ^ snScale (snSub k)) * negConv L (Ahat u) (Bhat u) t
        -- Inverse DFT with `angInv = 2 * step * (K - 1)`
        let Ctw := ringDFT L K (2 * step * (K - 1)) Phat
        -- Untwist by `ζ^(-j) = Z^(step * (2*K - j))`
        let Cscaled : ℕ → ℕ → Polynomial ℤ := fun j => negShift L (step * (2 * K - j)) (Ctw j)
        -- Recombine overlapping chunks into length `2^k = K * M`
        let Out : ℕ → Polynomial ℤ := fun t =>
          let q := t / M
          let r := t % M
          Cscaled q r + (if 0 < q then Cscaled (q - 1) (r + M) else -(Cscaled (K - 1) (r + M)))
        -- Prove algebraic correctness: `Out t = 2^(snScale k) * negConv (2^k) a b t` for all `t < 2^k`
        have hOut_eq : ∀ t < 2 ^ k,
            Out t = ((2 : Polynomial ℤ) ^ snScale k) * negConv (2 ^ k) a b t := by
          intro t ht
          have hsnScale : snScale k = snScale (snSub k) + p := by
            conv_lhs => rw [snScale]
            simp [hk, p]
          -- First compute `Cscaled j u` for `j < K, u < L`
          have hCscaled : ∀ j < K, ∀ u < L,
              Cscaled j u =
                ((2 : Polynomial ℤ) ^ (snScale (snSub k) + p)) *
                  ∑ j₁ ∈ Finset.range K,
                    if j₁ ≤ j then negConv (2 * M) (A j₁) (B (j - j₁)) u
                    else -(negConv (2 * M) (A j₁) (B (j + K - j₁)) u) := by
            intro j hj u hu
            -- Factor `2^(snScale (snSub k))` out of `Ctw` and `Cscaled`
            have hPhat_eq : Phat = fun w x =>
                ((2 : Polynomial ℤ) ^ snScale (snSub k)) * negConv L (Ahat w) (Bhat w) x := rfl
            have hCtw_pull : ∀ w x,
                Ctw w x = ((2 : Polynomial ℤ) ^ snScale (snSub k)) *
                  ringDFT L K (2 * step * (K - 1)) (fun z => negConv L (Ahat z) (Bhat z)) w x := by
              intro w x
              dsimp only [Ctw, ringDFT, Phat]
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro z _
              rw [negShift_smul_linear]
            dsimp only [Cscaled]
            have hCtw_fn : Ctw j = fun x =>
                ((2 : Polynomial ℤ) ^ snScale (snSub k)) *
                  ringDFT L K (2 * step * (K - 1)) (fun z => negConv L (Ahat z) (Bhat z)) j x :=
              funext (hCtw_pull j)
            rw [hCtw_fn, negShift_smul_linear]
            -- Apply `ringDFT_convolution` to `Atw, Btw`
            have hAhat_eq : Ahat = ringDFT L K (2 * step) Atw := by
              simp [Ahat]
            have hBhat_eq : Bhat = ringDFT L K (2 * step) Btw := by
              simp [Bhat]
            have hconv_fn :
                ∀ x < L,
                  ringDFT L K (2 * step * (K - 1)) (fun z => negConv L (Ahat z) (Bhat z)) j x =
                    ((K : ℕ) : Polynomial ℤ) *
                      ∑ j₁ ∈ Finset.range K,
                        negConv L (Atw j₁) (Btw ((j + K - j₁) % K)) x := by
              intro x hx
              rw [hAhat_eq, hBhat_eq]
              exact ringDFT_convolution p step L hL hKS Atw Btw j x hj hx
            -- Apply `negShift L (step * (2*K - j))` to `hconv_fn`
            have hsh_eq :
                negShift L (step * (2 * K - j))
                    (ringDFT L K (2 * step * (K - 1)) (fun z => negConv L (Ahat z) (Bhat z)) j) u =
                  negShift L (step * (2 * K - j))
                    (fun x => ((K : ℕ) : Polynomial ℤ) *
                      ∑ j₁ ∈ Finset.range K, negConv L (Atw j₁) (Btw ((j + K - j₁) % K)) x) u :=
              negShift_congr L _ hL _ _ hconv_fn u hu
            rw [hsh_eq, negShift_smul_linear, negShift_finset_sum]
            have hKcast : ((K : ℕ) : Polynomial ℤ) = (2 : Polynomial ℤ) ^ p := by
              simp [K]
            rw [hKcast, ← mul_assoc, ← pow_add]
            congr 1
            refine Finset.sum_congr rfl ?_
            intro j₁ hj₁
            rw [Finset.mem_range] at hj₁
            dsimp only [Atw, Btw]
            have h3shift :
                negShift L (step * (2 * K - j))
                    (negConv L (negShift L (step * j₁) (A j₁))
                      (negShift L (step * ((j + K - j₁) % K)) (B ((j + K - j₁) % K)))) u =
                  negShift L (step * (2 * K - j) + step * j₁ + step * ((j + K - j₁) % K))
                    (negConv L (A j₁) (B ((j + K - j₁) % K))) u := by
              have hinner_eq : ∀ x < L,
                  negConv L (negShift L (step * j₁) (A j₁))
                    (negShift L (step * ((j + K - j₁) % K)) (B ((j + K - j₁) % K))) x =
                  negShift L (step * j₁ + step * ((j + K - j₁) % K))
                    (negConv L (A j₁) (B ((j + K - j₁) % K))) x := by
                intro x hx
                rw [negConv_negShift_left L _ hL _ _ x hx]
                rw [negShift_congr L _ hL _ _ (fun y hy => negConv_negShift_right L _ hL (A j₁) _ y hy) x hx]
                rw [← negShift_add L _ _ hL _ x hx]
              have houter := negShift_congr L (step * (2 * K - j)) hL _ _ hinner_eq u hu
              rw [houter, ← negShift_add L _ _ hL _ u hu, add_assoc]
            rw [h3shift, hL2M]
            by_cases hle : j₁ ≤ j
            · have hmod : (j + K - j₁) % K = j - j₁ := by
                rw [show j + K - j₁ = (j - j₁) + K by omega, Nat.add_mod_right,
                  Nat.mod_eq_of_lt (by omega)]
              simp only [hle, ↓reduceIte, hmod]
              have hsum_exp : step * (2 * K - j) + step * j₁ + step * (j - j₁) = 2 * L := by
                rw [← hKS]
                zify [hle, show j ≤ 2 * K by omega]; ring
              rw [← hL2M, hsum_exp, show 2 * L = 0 + 2 * L by ring, negShift_add_mul_N L 0 2 hL,
                negShift_zero L hL]
              norm_num
            · have hmod : (j + K - j₁) % K = j + K - j₁ := Nat.mod_eq_of_lt (by omega)
              simp only [hle, ↓reduceIte, hmod]
              have hsum_exp : step * (2 * K - j) + step * j₁ + step * (j + K - j₁) = 3 * L := by
                rw [← hKS]
                zify [show j₁ ≤ j + K by omega, show j ≤ 2 * K by omega]; ring
              rw [← hL2M, hsum_exp, show 3 * L = 0 + 3 * L by ring, negShift_add_mul_N L 0 3 hL,
                negShift_zero L hL]
              norm_num
          have hq : t / M < K := Nat.div_lt_of_lt_mul (by rwa [mul_comm, hKM])
          have hr : t % M < M := Nat.mod_lt t (by omega)
          have ht_eq : t = (t / M) * M + t % M := by
            have := Nat.div_add_mod t M; linarith
          rw [hsnScale]
          dsimp only [Out]
          rw [hCscaled (t / M) hq (t % M) (by omega)]
          have h2nd :
              (if 0 < t / M then Cscaled (t / M - 1) (t % M + M)
               else -(Cscaled (K - 1) (t % M + M))) =
                ((2 : Polynomial ℤ) ^ (snScale (snSub k) + p)) *
                  (if 0 < t / M then
                    ∑ j₁ ∈ Finset.range K,
                      if j₁ ≤ t / M - 1 then negConv (2 * M) (A j₁) (B (t / M - 1 - j₁)) (t % M + M)
                      else -(negConv (2 * M) (A j₁) (B (t / M - 1 + K - j₁)) (t % M + M))
                  else
                    -(∑ j₁ ∈ Finset.range K,
                      if j₁ ≤ K - 1 then negConv (2 * M) (A j₁) (B (K - 1 - j₁)) (t % M + M)
                      else -(negConv (2 * M) (A j₁) (B (K - 1 + K - j₁)) (t % M + M)))) := by
            split_ifs with hq0
            · exact hCscaled (t / M - 1) (by omega) (t % M + M) (by omega)
            · rw [hCscaled (K - 1) (by omega) (t % M + M) (by omega)]; ring
          rw [h2nd, ← mul_add]
          congr 1
          conv_rhs => rw [← hKM, ht_eq]
          exact (negConv_chunk_recombine K M hKpos hMpos a b (t / M) (t % M) hq hr).symm
        -- Now chain the `CanBuild` steps!
        set S0 : Set (Polynomial ℤ) :=
          {(0 : Polynomial ℤ)} ∪ (⋃ i < 2 ^ k, {a i}) ∪ (⋃ j < 2 ^ k, {b j})
        -- Step 1 (`K * L` gates): `Atw`
        have hAtw : CanBuild S0 (K * L) (⋃ j < K, ⋃ u < L, {Atw j u}) := by
          refine canBuild_fin_union (n := K) (d := L) (T := fun j => ⋃ u < L, {Atw j u}) ?_
          intro j hj
          refine canBuild_mono_in ?_ (canBuild_negShift L (step * j) hL (A j))
          intro x hx; rcases hx with rfl | hx'
          · left; left; rfl
          · simp only [Set.mem_iUnion, exists_prop, Set.mem_singleton_iff] at hx'
            rcases hx' with ⟨u, hu, rfl⟩
            dsimp only [A]
            split_ifs with huM
            · left; right; simp only [Set.mem_iUnion, exists_prop]
              exact ⟨j * M + u, by rw [← hKM]; nlinarith, rfl⟩
            · left; left; rfl
        -- Step 2 (`K * L` gates): `Btw`
        have hBtw : CanBuild S0 (K * L) (⋃ j < K, ⋃ u < L, {Btw j u}) := by
          refine canBuild_fin_union (n := K) (d := L) (T := fun j => ⋃ u < L, {Btw j u}) ?_
          intro j hj
          refine canBuild_mono_in ?_ (canBuild_negShift L (step * j) hL (B j))
          intro x hx; rcases hx with rfl | hx'
          · left; left; rfl
          · simp only [Set.mem_iUnion, exists_prop, Set.mem_singleton_iff] at hx'
            rcases hx' with ⟨u, hu, rfl⟩
            dsimp only [B]
            split_ifs with huM
            · right; simp only [Set.mem_iUnion, exists_prop]
              exact ⟨j * M + u, by rw [← hKM]; nlinarith, rfl⟩
            · left; left; rfl
        -- Step 3 (`2 * dftCost p L` gates): `Ahat` and `Bhat`
        have hOdd1 : Odd (1 : ℕ) := ⟨0, by omega⟩
        have hOddKm1 : Odd (K - 1) := by
          have hp1 : 1 ≤ p := by omega
          have hK2 : 2 ∣ K := dvd_pow_self 2 (by omega : p ≠ 0)
          rcases hK2 with ⟨m, hm⟩
          exact ⟨m - 1, by omega⟩
        have hAhat := canBuild_ringDFT p step 1 L hL hKS hOdd1 Atw
        have hBhat := canBuild_ringDFT p step 1 L hL hKS hOdd1 Btw
        -- Step 4 (`K * snCost (snSub k)` gates): `K` recursive calls `Phat u`
        have hPhat :
            CanBuild
              ({(0 : Polynomial ℤ)} ∪ (⋃ u < K, ⋃ t < L, {Ahat u t}) ∪
                (⋃ u < K, ⋃ t < L, {Bhat u t}))
              (K * snCost (snSub k))
              (⋃ u < K, ⋃ t < L, {Phat u t}) := by
          refine canBuild_fin_union (n := K) (d := snCost (snSub k))
            (T := fun u => ⋃ t < L, {Phat u t}) ?_
          intro u hu
          refine canBuild_mono_in ?_ (canBuild_snMul (snSub k) (Ahat u) (Bhat u))
          intro x hx; rcases hx with (rfl | hxA) | hxB
          · left; left; rfl
          · left; right; simp only [Set.mem_iUnion, exists_prop] at hxA ⊢
            rcases hxA with ⟨t, ht, hxt⟩; exact ⟨u, hu, t, ht, hxt⟩
          · right; simp only [Set.mem_iUnion, exists_prop] at hxB ⊢
            rcases hxB with ⟨t, ht, hxt⟩; exact ⟨u, hu, t, ht, hxt⟩
        -- Step 5 (`dftCost p L` gates): `Ctw`
        have hCtw := canBuild_ringDFT p step (K - 1) L hL hKS hOddKm1 Phat
        -- Step 6 (`K * L` gates): `Cscaled`
        have hCsc :
            CanBuild ({(0 : Polynomial ℤ)} ∪ ⋃ j < K, ⋃ u < L, {Ctw j u})
              (K * L) (⋃ j < K, ⋃ u < L, {Cscaled j u}) := by
          refine canBuild_fin_union (n := K) (d := L) (T := fun j => ⋃ u < L, {Cscaled j u}) ?_
          intro j hj
          refine canBuild_mono_in ?_ (canBuild_negShift L (step * (2 * K - j)) hL (Ctw j))
          intro x hx; rcases hx with rfl | hx'
          · left; rfl
          · right; simp only [Set.mem_iUnion, exists_prop] at hx' ⊢
            rcases hx' with ⟨u, hu, hxu⟩; exact ⟨j, hj, u, hu, hxu⟩
        -- Step 7 (`2 * 2^k` gates): `Out t` for `t < 2^k`
        have hOut :
            CanBuild ({(0 : Polynomial ℤ)} ∪ ⋃ j < K, ⋃ u < L, {Cscaled j u})
              (2 ^ k * 2) (⋃ t < 2 ^ k, {Out t}) := by
          refine canBuild_fin_union (n := 2 ^ k) (d := 2) (T := fun t => {Out t}) ?_
          intro t ht
          set q := t / M
          set r := t % M
          have hq : q < K := Nat.div_lt_of_lt_mul (by rwa [mul_comm, hKM])
          have hr : r < M := Nat.mod_lt t (by omega)
          by_cases hq0 : 0 < q
          · have ha := canBuild_add (Cscaled q r) (Cscaled (q - 1) (r + M))
            have hOut_eq' : Out t = Cscaled q r + Cscaled (q - 1) (r + M) := by
              change Cscaled q r + (if 0 < q then Cscaled (q - 1) (r + M) else -(Cscaled (K - 1) (r + M))) = _
              simp only [hq0, ↓reduceIte]
            refine canBuild_mono_cost (by omega : 1 ≤ 2)
              (canBuild_mono_out (T₂ := {Cscaled q r + Cscaled (q - 1) (r + M)})
                (by intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx; rw [hOut_eq']; rfl)
                (canBuild_mono_in ?_ ha))
            intro x hx; rcases hx with rfl | rfl
            · right; simp only [Set.mem_iUnion, exists_prop]; exact ⟨q, hq, r, by omega, rfl⟩
            · right; simp only [Set.mem_iUnion, exists_prop]; exact ⟨q - 1, by omega, r + M, by omega, rfl⟩
          · have hs := canBuild_sub (Cscaled q r) (Cscaled (K - 1) (r + M))
            have hOut_eq' : Out t = Cscaled q r - Cscaled (K - 1) (r + M) := by
              change Cscaled q r + (if 0 < q then Cscaled (q - 1) (r + M) else -(Cscaled (K - 1) (r + M))) = _
              simp only [hq0, ↓reduceIte, sub_eq_add_neg]
            refine canBuild_mono_cost (by omega : 1 ≤ 2)
              (canBuild_mono_out (T₂ := {Cscaled q r - Cscaled (K - 1) (r + M)})
                (by intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx; rw [hOut_eq']; rfl)
                (canBuild_mono_in ?_ hs))
            intro x hx; rcases hx with rfl | rfl
            · right; simp only [Set.mem_iUnion, exists_prop]; exact ⟨q, hq, r, by omega, rfl⟩
            · right; simp only [Set.mem_iUnion, exists_prop]; exact ⟨K - 1, by omega, r + M, by omega, rfl⟩
        -- Compose Steps 1..7
        have s12 := canBuild_trans hAtw Set.subset_union_left hBtw
        have s13 := canBuild_trans s12 (by
          intro x hx; rcases hx with rfl | hx'
          · left; left; left; rfl
          · right; left; exact hx') hAhat
        have s14 := canBuild_trans s13 (by
          intro x hx; rcases hx with rfl | hx'
          · left; left; left; rfl
          · right; left; right; exact hx') hBhat
        have s15 := canBuild_trans s14 (by
          intro x hx; rcases hx with (rfl | hxA) | hxB
          · left; left; left; rfl
          · right; left; right; exact hxA
          · right; right; exact hxB) hPhat
        have s16 := canBuild_trans s15 (by
          intro x hx; rcases hx with rfl | hx'
          · left; left; left; rfl
          · right; right; exact hx') hCtw
        have s17 := canBuild_trans s16 (by
          intro x hx; rcases hx with rfl | hx'
          · left; left; left; rfl
          · right; right; exact hx') hCsc
        have s18 := canBuild_trans s17 (by
          intro x hx; rcases hx with rfl | hx'
          · left; left; left; rfl
          · right; right; exact hx') hOut
        have hcost :
            K * L + K * L + dftCost p L + dftCost p L + K * snCost (snSub k) +
                dftCost p L + K * L + 2 ^ k * 2 = snCost k := by
          conv_rhs => rw [snCost]
          simp only [hk, ↓reduceDIte, p, K, L]
          ring
        rw [hcost] at s18
        refine canBuild_mono_out ?_ s18
        intro x hx
        simp only [Set.mem_iUnion, exists_prop, Set.mem_singleton_iff] at hx
        rcases hx with ⟨t, ht, rfl⟩
        right
        simp only [Set.mem_iUnion, exists_prop]
        exact ⟨t, ht, (hOut_eq t ht).symm⟩
termination_by k => k
decreasing_by exact snSub_lt k (by omega)

/-! ## 5. Asymptotic Bound on `snCost k` and Refutation of All Real Exponents `c < 2` -/

/-- Exact asymptotic upper bound on Schönhage–Nussbaumer gate cost:
`snCost k ≤ 200 * k * (Nat.log 2 k + 1) * 2 ^ k` for every `k ≥ 1`. -/
theorem snCost_le : ∀ k : ℕ, 1 ≤ k → snCost k ≤ 200 * k * (Nat.log 2 k + 1) * 2 ^ k := by
  -- Prove the sharper shifted invariant for all `k ≥ 1`:
  -- `snCost k ≤ (50 * (k - 3) * (Nat.log 2 (k - 3) + 1) + 48) * 2 ^ k`
  -- Check:
  --  k = 1: 3 * 2 * 2 = 12 ≤ 48 * 2 = 96
  --  k = 2: 3 * 4 * 4 = 48 ≤ 48 * 4 = 192
  --  k = 3: 3 * 8 * 8 = 192 ≤ 48 * 8 = 384
  --  k = 4: snSub 4 = 3, p = 2, K = 4, L = 8:
  --    snCost 4 = 4 * 192 + 3 * (3 * 2 * 4 * 8) + 3 * 4 * 8 + 32 = 768 + 576 + 96 + 32 = 1472
  --    RHS at k = 4: (50 * 1 * 1 + 48) * 16 = 98 * 16 = 1568 ≥ 1472!
  --  k ≥ 5: let k' = snSub k = (k + 1) / 2 + 1. Note K * 2^k' = 2^(k/2 + (k+1)/2 + 1) = 2 * 2^k,
  --    and 2 * (k' - 3) ≤ k - 3, and Nat.log 2 (k' - 3) + 1 ≤ Nat.log 2 (k - 3)!
  --    Extra work: 3 * dftCost p L + 3 * K * L + 2 * 2^k
  --      = (9 * p * 2 + 3 * 2 + 2) * 2^k = (18 * p + 8) * 2^k ≤ (9 * k + 8) * 2^k.
  --    Total / 2^k ≤ 2 * (50 * (k' - 3) * (log(k'-3) + 1) + 48) + 9 * k + 8
  --      ≤ 50 * (k - 3) * log(k - 3) + 96 + 9 * k + 8
  --      = 50 * (k - 3) * (log(k - 3) + 1) + 48 + (56 + 9 * k - 50 * (k - 3))
  --      and for k ≥ 5: 56 + 9 * k ≤ 101 ≤ 100? Wait: at k = 5: 56 + 45 = 101 > 50 * 2 = 100!
  --    Bump 50 → 60! At k = 5: 56 + 45 = 101 ≤ 60 * 2 = 120!
  --    And for all k ≥ 5: 56 + 9 * k ≤ 60 * (k - 3) ⟺ 236 ≤ 51 * k (51 * 5 = 255 ≥ 236)!
  --    And 60 * (k - 3) * (log(k-3) + 1) + 48 ≤ 200 * k * (log k + 1) for all k ≥ 1!
  have hstrong : ∀ k : ℕ, 1 ≤ k →
      snCost k ≤ (60 * (k - 3) * (Nat.log 2 (k - 3) + 1) + 48) * 2 ^ k := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
        intro hk1
        by_cases hk3 : k ≤ 3
        · rw [snCost]
          simp only [hk3, ↓reduceDIte]
          have hpow : 2 ^ k ≤ 8 := by
            calc 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by omega) hk3
              _ = 8 := by norm_num
          have h1 : 3 * 2 ^ k ≤ 60 * (k - 3) * (Nat.log 2 (k - 3) + 1) + 48 := by omega
          exact Nat.mul_le_mul_right (2 ^ k) h1
        · by_cases hk4 : k = 4
          · subst hk4
            have hval : snCost 4 = 1472 := by
              rw [snCost]; simp only [show ¬ (4 ≤ 3) by omega, ↓reduceDIte, snSub, dftCost]
              rw [snCost]; simp
            rw [hval]
            norm_num
          · have hk5 : 5 ≤ k := by omega
            have hlt : snSub k < k := snSub_lt k (by omega)
            have hsub1 : 1 ≤ snSub k := by unfold snSub; omega
            have hih := ih (snSub k) hlt hsub1
            set p := k / 2
            set K := 2 ^ p
            set L := 2 ^ snSub k
            have hKL : K * L = 2 * 2 ^ k := by
              simp only [K, L, snSub, ← pow_add]
              rw [show p + ((k + 1) / 2 + 1) = k + 1 by omega, pow_succ]
              ring
            have hdft : 3 * dftCost p L + 3 * K * L + 2 * 2 ^ k ≤ (9 * k + 8) * 2 ^ k := by
              simp only [dftCost]
              have h1 : 3 * (3 * p * K * L) + 3 * K * L + 2 * 2 ^ k =
                  (18 * p + 8) * 2 ^ k := by
                have : 3 * (3 * p * K * L) + 3 * K * L = (9 * p + 3) * (K * L) := by ring
                rw [this, hKL]; ring
              have h2 : 18 * p + 8 ≤ 9 * k + 8 := by omega
              rw [h1]
              exact Nat.mul_le_mul_right (2 ^ k) h2
            have hrec : K * snCost (snSub k) ≤
                (2 * (60 * (snSub k - 3) * (Nat.log 2 (snSub k - 3) + 1) + 48)) * 2 ^ k := by
              calc K * snCost (snSub k)
                  ≤ K * ((60 * (snSub k - 3) * (Nat.log 2 (snSub k - 3) + 1) + 48) * L) :=
                    Nat.mul_le_mul_left K hih
                _ = (60 * (snSub k - 3) * (Nat.log 2 (snSub k - 3) + 1) + 48) * (K * L) := by ring
                _ = (2 * (60 * (snSub k - 3) * (Nat.log 2 (snSub k - 3) + 1) + 48)) * 2 ^ k := by
                    rw [hKL]; ring
            have hhalf : 2 * (snSub k - 3) ≤ k - 3 := by unfold snSub; omega
            have hpos_sub : 1 ≤ snSub k - 3 := by unfold snSub; omega
            have hlog : Nat.log 2 (snSub k - 3) + 1 ≤ Nat.log 2 (k - 3) := by
              have h1 : Nat.log 2 (2 * (snSub k - 3)) = Nat.log 2 (snSub k - 3) + 1 := by
                rw [mul_comm, Nat.log_mul_base (by omega) (by omega)]
              rw [← h1]
              exact Nat.log_mono_right hhalf
            have hmain_term :
                2 * (60 * (snSub k - 3) * (Nat.log 2 (snSub k - 3) + 1)) ≤
                  60 * (k - 3) * Nat.log 2 (k - 3) := by
              calc 2 * (60 * (snSub k - 3) * (Nat.log 2 (snSub k - 3) + 1))
                  = 60 * (2 * (snSub k - 3)) * (Nat.log 2 (snSub k - 3) + 1) := by ring
                _ ≤ 60 * (k - 3) * Nat.log 2 (k - 3) := by
                    exact Nat.mul_le_mul (Nat.mul_le_mul_left 60 hhalf) hlog
            have hcoeff :
                2 * (60 * (snSub k - 3) * (Nat.log 2 (snSub k - 3) + 1) + 48) + (9 * k + 8) ≤
                  60 * (k - 3) * (Nat.log 2 (k - 3) + 1) + 48 := by
              have hlin : 56 + 9 * k ≤ 60 * (k - 3) := by omega
              have hexp : 60 * (k - 3) * (Nat.log 2 (k - 3) + 1) =
                  60 * (k - 3) * Nat.log 2 (k - 3) + 60 * (k - 3) := by ring
              omega
            conv_lhs => rw [snCost]
            simp only [hk3, ↓reduceDIte]
            calc K * snCost (snSub k) + 3 * dftCost p L + 3 * K * L + 2 * 2 ^ k
                = K * snCost (snSub k) + (3 * dftCost p L + 3 * K * L + 2 * 2 ^ k) := by ring
              _ ≤ (2 * (60 * (snSub k - 3) * (Nat.log 2 (snSub k - 3) + 1) + 48)) * 2 ^ k +
                    (9 * k + 8) * 2 ^ k := Nat.add_le_add hrec hdft
              _ = (2 * (60 * (snSub k - 3) * (Nat.log 2 (snSub k - 3) + 1) + 48) + (9 * k + 8)) * 2 ^ k := by
                  ring
              _ ≤ (60 * (k - 3) * (Nat.log 2 (k - 3) + 1) + 48) * 2 ^ k :=
                  Nat.mul_le_mul_right (2 ^ k) hcoeff
  intro k hk1
  have hs := hstrong k hk1
  have hlog : Nat.log 2 (k - 3) ≤ Nat.log 2 k := Nat.log_mono_right (Nat.sub_le k 3)
  have h1 : 60 * (k - 3) * (Nat.log 2 (k - 3) + 1) + 48 ≤ 200 * k * (Nat.log 2 k + 1) := by
    have hmul1 : 60 * (k - 3) * (Nat.log 2 (k - 3) + 1) ≤ 60 * k * (Nat.log 2 k + 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 60 (Nat.sub_le k 3)) (Nat.add_le_add_right hlog 1)
    have h48 : 48 ≤ 140 * k * (Nat.log 2 k + 1) := by
      have : 1 ≤ k * (Nat.log 2 k + 1) := Nat.mul_pos hk1 (by omega)
      nlinarith
    have : 60 * k * (Nat.log 2 k + 1) + 140 * k * (Nat.log 2 k + 1) =
        200 * k * (Nat.log 2 k + 1) := by ring
    omega
  exact hs.trans (Nat.mul_le_mul_right (2 ^ k) h1)

/-- **Unconditional Near-Quadratic Growth (`z_max(τ) = Ω(τ^2 / (log^2 τ (log log τ)^2))`):**
For every `k ≥ 2`, there exists a constant-free SLP of length `2000 * k * (Nat.log 2 k + 1) * 2 ^ k`
computing a nonzero polynomial in `ℤ[X]` with at least `2 * 4 ^ k + 1` distinct integer roots. -/
theorem tau_subquadratic_growth (k : ℕ) (hk : 2 ≤ k) :
    zMaxGe (2000 * k * (Nat.log 2 k + 1) * 2 ^ k) (2 * 4 ^ k + 1) := by
  set m := 2 ^ k
  have hm : 1 ≤ m := Nat.one_le_two_pow
  have hm2 : m * m = 4 ^ k := by
    simp only [m, ← pow_add, show k + k = 2 * k by ring, pow_mul]
    norm_num
  have h2m : 2 * m = 2 ^ (k + 1) := by simp [m, pow_succ, mul_comm]
  have hsn := canBuild_snMul (k + 1) (chirpA m) (chirpB m)
  have hSpos : (0 : ℤ) < (2 : ℤ) ^ snScale (k + 1) := by positivity
  have hstep :
      CanBuild
        ({(0 : Polynomial ℤ)} ∪ (⋃ r < m + 1, {chirpA m r}) ∪ (⋃ s < 2 * m, {chirpB m s}))
        (snCost (k + 1))
        (⋃ i < m, {Polynomial.C ((2 : ℤ) ^ snScale (k + 1)) *
          ∑ r ∈ Finset.range (m + 1), chirpA m r * chirpB m (i + m - r)}) := by
    have hin :
        ({(0 : Polynomial ℤ)} ∪ (⋃ i < 2 ^ (k + 1), {chirpA m i}) ∪
            (⋃ j < 2 ^ (k + 1), {chirpB m j})) ⊆
          ({(0 : Polynomial ℤ)} ∪ (⋃ r < m + 1, {chirpA m r}) ∪ (⋃ s < 2 * m, {chirpB m s})) := by
      intro x hx
      rcases hx with (rfl | hxA) | hxB
      · left; left; rfl
      · simp only [Set.mem_iUnion, exists_prop, Set.mem_singleton_iff] at hxA
        rcases hxA with ⟨r, _, rfl⟩
        by_cases hrm : r ≤ m
        · left; right; simp only [Set.mem_iUnion, exists_prop]; exact ⟨r, by omega, rfl⟩
        · left; left; simp [chirpA, hrm]
      · right
        simp only [Set.mem_iUnion, exists_prop, Set.mem_singleton_iff] at hxB ⊢
        rcases hxB with ⟨s, hs, rfl⟩
        exact ⟨s, by omega, rfl⟩
    refine canBuild_mono_out ?_ (canBuild_mono_in hin hsn)
    intro x hx
    simp only [Set.mem_iUnion, exists_prop, Set.mem_singleton_iff] at hx ⊢
    rcases hx with ⟨i, hi, rfl⟩
    refine ⟨i + m, by omega, ?_⟩
    rw [← h2m, negConv_chirp_eq m i hm hi]
    simp [map_pow]
  have hz := zMaxGe_of_chirp_engine hm ((2 : ℤ) ^ snScale (k + 1)) hSpos hstep
  rw [hm2] at hz
  have hle : 17 * m + snCost (k + 1) + 14 ≤ 2000 * k * (Nat.log 2 k + 1) * 2 ^ k := by
    have hsn_le := snCost_le (k + 1) (by omega)
    have hlog1 : Nat.log 2 (k + 1) ≤ Nat.log 2 k + 1 := by
      have h1 : k + 1 ≤ k * 2 := by omega
      calc Nat.log 2 (k + 1) ≤ Nat.log 2 (k * 2) := Nat.log_mono_right h1
        _ = Nat.log 2 k + 1 := Nat.log_mul_base (by omega) (by omega)
    have hkl : (k + 1) * (Nat.log 2 (k + 1) + 1) ≤ 4 * k * (Nat.log 2 k + 1) := by
      have hk2 : k + 1 ≤ 2 * k := by omega
      have hl2 : Nat.log 2 (k + 1) + 1 ≤ 2 * (Nat.log 2 k + 1) := by omega
      calc (k + 1) * (Nat.log 2 (k + 1) + 1)
          ≤ (2 * k) * (2 * (Nat.log 2 k + 1)) := Nat.mul_le_mul hk2 hl2
        _ = 4 * k * (Nat.log 2 k + 1) := by ring
    have hsn_bound : snCost (k + 1) ≤ 1600 * k * (Nat.log 2 k + 1) * 2 ^ k := by
      calc snCost (k + 1)
          ≤ 200 * (k + 1) * (Nat.log 2 (k + 1) + 1) * 2 ^ (k + 1) := hsn_le
        _ = 400 * ((k + 1) * (Nat.log 2 (k + 1) + 1)) * 2 ^ k := by rw [pow_succ]; ring
        _ ≤ 400 * (4 * k * (Nat.log 2 k + 1)) * 2 ^ k :=
            Nat.mul_le_mul_right (2 ^ k) (Nat.mul_le_mul_left 400 hkl)
        _ = 1600 * k * (Nat.log 2 k + 1) * 2 ^ k := by ring
    have hrem : 17 * m + 14 ≤ 400 * k * (Nat.log 2 k + 1) * 2 ^ k := by
      have h1 : 17 * m + 14 ≤ 31 * 2 ^ k := by omega
      have h2 : 31 ≤ 400 * k * (Nat.log 2 k + 1) := by
        have : 1 ≤ k * (Nat.log 2 k + 1) := Nat.mul_pos (by omega) (by omega)
        nlinarith
      exact h1.trans (Nat.mul_le_mul_right (2 ^ k) h2)
    have hsum : 1600 * k * (Nat.log 2 k + 1) * 2 ^ k + 400 * k * (Nat.log 2 k + 1) * 2 ^ k =
        2000 * k * (Nat.log 2 k + 1) * 2 ^ k := by ring
    omega
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
  rw [hd]
  clear hd hle
  induction d with
  | zero => simpa using hz
  | succ d ih => exact zMaxGe_succ ih

/-- **Unconditional Refutation of Every Sub-Quadratic Exponent `c < 2` in Smale's 4th Problem:**
For every real `c < 2`, there is NO real constant `a` such that every nonzero constant-free SLP
of length `τ` satisfies `(intRootCount P.evalPoly : ℝ) ≤ a * ((τ : ℝ) + 1) ^ c`. -/
theorem tau_refutes_subquadratic (c : ℝ) (hc : c < 2) :
    ¬ ∃ a : ℝ, ∀ (τ : ℕ) (P : SLP τ), P.evalPoly ≠ 0 →
      (intRootCount P.evalPoly : ℝ) ≤ a * ((τ : ℝ) + 1) ^ c := by
  rintro ⟨a, ha⟩
  by_cases hc0 : c ≤ 0
  · -- When `c ≤ 0`, `(τ + 1)^c ≤ 1`, contradicting unbounded root counts
    obtain ⟨k, hk⟩ := exists_nat_gt (max a 0)
    let k' := k + 2
    rcases tau_subquadratic_growth k' (by omega) with ⟨P, hne, hcard⟩
    have hub := ha _ P hne
    have htau_ge : (1 : ℝ) ≤ ((2000 * k' * (Nat.log 2 k' + 1) * 2 ^ k' : ℕ) : ℝ) + 1 := by
      linarith [Nat.cast_nonneg (α := ℝ) (2000 * k' * (Nat.log 2 k' + 1) * 2 ^ k')]
    have hrpow_le : (((2000 * k' * (Nat.log 2 k' + 1) * 2 ^ k' : ℕ) : ℝ) + 1) ^ c ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos htau_ge hc0
    have h4gt : (k : ℝ) < (2 * 4 ^ k' + 1 : ℕ) := by
      have h1 : k < 2 * 4 ^ k' + 1 := by
        have : k' < 2 ^ k' := Nat.lt_two_pow_self
        have : 2 ^ k' ≤ 4 ^ k' := Nat.pow_le_pow_left (by omega) k'
        omega
      exact_mod_cast h1
    have hcardR : ((2 * 4 ^ k' + 1 : ℕ) : ℝ) ≤ (intRootCount P.evalPoly : ℝ) := by exact_mod_cast hcard
    have hle_a : a * (((2000 * k' * (Nat.log 2 k' + 1) * 2 ^ k' : ℕ) : ℝ) + 1) ^ c ≤ max a 0 := by
      have hrpos : 0 ≤ (((2000 * k' * (Nat.log 2 k' + 1) * 2 ^ k' : ℕ) : ℝ) + 1) ^ c := by positivity
      calc a * (((2000 * k' * (Nat.log 2 k' + 1) * 2 ^ k' : ℕ) : ℝ) + 1) ^ c
          ≤ max a 0 * (((2000 * k' * (Nat.log 2 k' + 1) * 2 ^ k' : ℕ) : ℝ) + 1) ^ c :=
            mul_le_mul_of_nonneg_right (le_max_left a 0) hrpos
        _ ≤ max a 0 * 1 := mul_le_mul_of_nonneg_left hrpow_le (le_max_right a 0)
        _ = max a 0 := mul_one _
    linarith
  · push Not at hc0
    have hgap : 0 < 2 - c := by linarith
    obtain ⟨M0, hM0⟩ := exists_nat_gt (1 / (2 - c))
    let M := M0 + 1
    have hMpos : 1 ≤ M := by omega
    have hMgap : (1 : ℝ) ≤ (2 - c) * (M : ℝ) := by
      have h1 : 1 / (2 - c) < (M : ℝ) := by
        have : (M0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : M0 < M)
        linarith
      have h2 := (div_lt_iff₀ hgap).mp h1
      linarith
    let B : ℝ := max a 0 * ((2001 : ℝ) * ((5 * M + 1 : ℕ) : ℝ) ^ 2) ^ 2
    obtain ⟨t0, ht0⟩ := exists_nat_gt B
    let t := t0 + 2
    let k := 5 * M * t
    have hk2 : 2 ≤ k := by
      have h1 : 5 * 1 * 2 ≤ 5 * M * t :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 5 hMpos) (by omega)
      exact le_trans (by omega : 2 ≤ 5 * 1 * 2) h1
    set τ := 2000 * k * (Nat.log 2 k + 1) * 2 ^ k
    rcases tau_subquadratic_growth k hk2 with ⟨P, hne, hcard⟩
    have hub := ha τ P hne
    have htau_nat : τ + 1 ≤ 2001 * (k + 1) ^ 2 * 2 ^ k := by
      have hlog : Nat.log 2 k ≤ k := Nat.log_le_self 2 k
      have h1 : τ ≤ 2000 * (k + 1) ^ 2 * 2 ^ k := by
        have hkk : k * (Nat.log 2 k + 1) ≤ (k + 1) ^ 2 := by
          have : k * (Nat.log 2 k + 1) ≤ (k + 1) * (k + 1) :=
            Nat.mul_le_mul (by omega) (by omega)
          simpa [sq] using this
        calc τ = 2000 * (k * (Nat.log 2 k + 1)) * 2 ^ k := by ring
          _ ≤ 2000 * (k + 1) ^ 2 * 2 ^ k :=
              Nat.mul_le_mul_right (2 ^ k) (Nat.mul_le_mul_left 2000 hkk)
      have h2 : 1 ≤ (k + 1) ^ 2 * 2 ^ k := by
        have ha1 : 1 ≤ (k + 1) ^ 2 := by nlinarith
        have hb1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
        exact Nat.mul_pos ha1 hb1
      linarith
    have htau_R : ((τ : ℝ) + 1) ≤ ((2001 : ℝ) * ((k + 1 : ℕ) : ℝ) ^ 2) * (2 : ℝ) ^ k := by
      exact_mod_cast htau_nat
    have hbase_ge1 : (1 : ℝ) ≤ (2001 : ℝ) * ((k + 1 : ℕ) : ℝ) ^ 2 := by
      have h1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) ^ 2 := by
        exact_mod_cast (by nlinarith : 1 ≤ (k + 1) ^ 2)
      nlinarith
    have hrpow_bound :
        ((τ : ℝ) + 1) ^ c ≤
          ((2001 : ℝ) * ((k + 1 : ℕ) : ℝ) ^ 2) ^ 2 * (2 : ℝ) ^ (c * (k : ℝ)) := by
      have h1 : ((τ : ℝ) + 1) ^ c ≤
          (((2001 : ℝ) * ((k + 1 : ℕ) : ℝ) ^ 2) * (2 : ℝ) ^ k) ^ c :=
        Real.rpow_le_rpow (by positivity) htau_R (le_of_lt hc0)
      rw [Real.mul_rpow (by positivity) (by positivity)] at h1
      have h2 : ((2001 : ℝ) * ((k + 1 : ℕ) : ℝ) ^ 2) ^ c ≤
          ((2001 : ℝ) * ((k + 1 : ℕ) : ℝ) ^ 2) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hbase_ge1 (le_of_lt hc)
      have h2' : ((2001 : ℝ) * ((k + 1 : ℕ) : ℝ) ^ 2) ^ (2 : ℝ) =
          ((2001 : ℝ) * ((k + 1 : ℕ) : ℝ) ^ 2) ^ 2 := by norm_cast
      have h3 : ((2 : ℝ) ^ k) ^ c = (2 : ℝ) ^ (c * (k : ℝ)) := by
        rw [← Real.rpow_natCast (2 : ℝ) k, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), mul_comm]
      rw [h2'] at h2
      rw [h3] at h1
      exact h1.trans (mul_le_mul_of_nonneg_right h2 (by positivity))
    have hk_le : ((k + 1 : ℕ) : ℝ) ≤ ((5 * M + 1 : ℕ) : ℝ) * (t : ℝ) := by
      have : k + 1 ≤ (5 * M + 1) * t := by
        dsimp only [k]
        have : 1 ≤ t := by omega
        nlinarith
      exact_mod_cast this
    have hpoly_bound :
        max a 0 * ((2001 : ℝ) * ((k + 1 : ℕ) : ℝ) ^ 2) ^ 2 ≤ B * (t : ℝ) ^ 4 := by
      have hsq : ((2001 : ℝ) * ((k + 1 : ℕ) : ℝ) ^ 2) ^ 2 ≤
          ((2001 : ℝ) * (((5 * M + 1 : ℕ) : ℝ) * (t : ℝ)) ^ 2) ^ 2 := by
        gcongr
      calc max a 0 * ((2001 : ℝ) * ((k + 1 : ℕ) : ℝ) ^ 2) ^ 2
          ≤ max a 0 * ((2001 : ℝ) * (((5 * M + 1 : ℕ) : ℝ) * (t : ℝ)) ^ 2) ^ 2 :=
            mul_le_mul_of_nonneg_left hsq (le_max_right a 0)
        _ = B * (t : ℝ) ^ 4 := by dsimp only [B]; ring
    have h4eq : ((2 * 4 ^ k + 1 : ℕ) : ℝ) > (2 : ℝ) ^ (2 * k) := by
      have h1 : 2 ^ (2 * k) < 2 * 4 ^ k + 1 := by
        have hpow : 2 ^ (2 * k) = 4 ^ k := by rw [pow_mul]; norm_num
        omega
      exact_mod_cast h1
    have hcardR : ((2 * 4 ^ k + 1 : ℕ) : ℝ) ≤ (intRootCount P.evalPoly : ℝ) := by exact_mod_cast hcard
    have hLHS : (2 : ℝ) ^ ((2 : ℝ) * (k : ℝ)) < (intRootCount P.evalPoly : ℝ) := by
      have h2k : (2 : ℝ) ^ ((2 : ℝ) * (k : ℝ)) = (2 : ℝ) ^ (2 * k) := by
        rw [← Real.rpow_natCast (2 : ℝ) (2 * k)]
        congr 1; push_cast; ring
      rw [h2k]
      linarith
    have hRHS : (intRootCount P.evalPoly : ℝ) ≤ B * (t : ℝ) ^ 4 * (2 : ℝ) ^ (c * (k : ℝ)) := by
      calc (intRootCount P.evalPoly : ℝ)
          ≤ a * ((τ : ℝ) + 1) ^ c := hub
        _ ≤ max a 0 * ((τ : ℝ) + 1) ^ c :=
            mul_le_mul_of_nonneg_right (le_max_left a 0) (by positivity)
        _ ≤ max a 0 * (((2001 : ℝ) * ((k + 1 : ℕ) : ℝ) ^ 2) ^ 2 * (2 : ℝ) ^ (c * (k : ℝ))) :=
            mul_le_mul_of_nonneg_left hrpow_bound (le_max_right a 0)
        _ = (max a 0 * ((2001 : ℝ) * ((k + 1 : ℕ) : ℝ) ^ 2) ^ 2) * (2 : ℝ) ^ (c * (k : ℝ)) := by ring
        _ ≤ (B * (t : ℝ) ^ 4) * (2 : ℝ) ^ (c * (k : ℝ)) :=
            mul_le_mul_of_nonneg_right hpoly_bound (by positivity)
    -- Divide out `(2 : ℝ) ^ (c * k) > 0`: gives `(2 : ℝ) ^ ((2 - c) * k) < B * t^4`
    have h2split : (2 : ℝ) ^ ((2 : ℝ) * (k : ℝ)) =
        (2 : ℝ) ^ ((2 - c) * (k : ℝ)) * (2 : ℝ) ^ (c * (k : ℝ)) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1; ring
    have h2ck_pos : (0 : ℝ) < (2 : ℝ) ^ (c * (k : ℝ)) := by positivity
    have hdiv : (2 : ℝ) ^ ((2 - c) * (k : ℝ)) < B * (t : ℝ) ^ 4 := by
      have hlt : (2 : ℝ) ^ ((2 - c) * (k : ℝ)) * (2 : ℝ) ^ (c * (k : ℝ)) <
          (B * (t : ℝ) ^ 4) * (2 : ℝ) ^ (c * (k : ℝ)) := by
        rw [← h2split]; linarith
      exact lt_of_mul_lt_mul_right hlt (le_of_lt h2ck_pos)
    -- Meanwhile `(2 - c) * k = (2 - c) * M * (5 * t) ≥ 5 * t`, and `2^(5 * t) = 2^t * (2^t)^4 > B * t^4`!
    have hexp_ge : ((5 * t : ℕ) : ℝ) ≤ (2 - c) * (k : ℝ) := by
      have hkR : (k : ℝ) = (M : ℝ) * ((5 * t : ℕ) : ℝ) := by
        dsimp only [k]; push_cast; ring
      rw [hkR, ← mul_assoc]
      calc ((5 * t : ℕ) : ℝ) = 1 * ((5 * t : ℕ) : ℝ) := (one_mul _).symm
        _ ≤ ((2 - c) * (M : ℝ)) * ((5 * t : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_right hMgap (by positivity)
    have h2_5t : (2 : ℝ) ^ (5 * t) ≤ (2 : ℝ) ^ ((2 - c) * (k : ℝ)) := by
      rw [← Real.rpow_natCast (2 : ℝ) (5 * t)]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp_ge
    have ht_lt_2t : (t : ℝ) < (2 : ℝ) ^ t := by exact_mod_cast (Nat.lt_two_pow_self (n := t))
    have hB_lt_2t : B < (2 : ℝ) ^ t := by
      have : (t0 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : t0 < t)
      linarith
    have hB_nonneg : 0 ≤ B := by
      dsimp only [B]
      exact mul_nonneg (le_max_right a 0) (sq_nonneg _)
    have hpow4 : (t : ℝ) ^ 4 ≤ ((2 : ℝ) ^ t) ^ 4 := by gcongr
    have h2_5t_eq : (2 : ℝ) ^ (5 * t) = (2 : ℝ) ^ t * ((2 : ℝ) ^ t) ^ 4 := by
      rw [← pow_mul, ← pow_add]; congr 1; ring
    have hcontra : B * (t : ℝ) ^ 4 < (2 : ℝ) ^ (5 * t) := by
      rw [h2_5t_eq]
      calc B * (t : ℝ) ^ 4 ≤ B * ((2 : ℝ) ^ t) ^ 4 := mul_le_mul_of_nonneg_left hpow4 hB_nonneg
        _ < (2 : ℝ) ^ t * ((2 : ℝ) ^ t) ^ 4 := mul_lt_mul_of_pos_right hB_lt_2t (by positivity)
    linarith

/-! ## 6. Machine-Verified Concrete Finite Crossover (`z_max(1884) ≥ 2049 > 1884`) -/

/-- Exact middle product of length `n`:
`midProd n P Q i = ∑ r < n, P r * Q (i + n - 1 - r)` for `i < n` (reading `P` on `0 .. n-1`
and `Q` on `0 .. 2*n - 2`). -/
noncomputable def midProd (n : ℕ) (P Q : ℕ → Polynomial ℤ) (i : ℕ) : Polynomial ℤ :=
  ∑ r ∈ Finset.range n, P r * Q (i + n - 1 - r)

/-- Exact gate cost of power-of-2 Karatsuba middle product with base case `k = 2` (`n = 4`):
`midCost 2 = 28`, `midCost (k + 1) = 3 * midCost k + 7 * 2^k - 2`.
At `k = 5` (`n = 32`): `midCost 5 = 1262`. -/
def midCost : ℕ → ℕ
  | 0 => 1
  | 1 => 6
  | 2 => 28
  | k + 1 => 3 * midCost k + 7 * 2 ^ k - 2

theorem midProd_even_lo (h : ℕ) (P Q : ℕ → Polynomial ℤ) (i : ℕ) :
    let P0 := fun r => P r
    let P1 := fun r => P (r + h)
    let Psum := fun r => P0 r + P1 r
    let Qlo := fun s => Q s
    let Qmid := fun s => Q (s + h)
    let Q1 := fun s => Qlo s - Qmid s
    midProd (2 * h) P Q i = midProd h Psum Qmid i + midProd h P1 Q1 i := by
  intro P0 P1 Psum Qlo Qmid Q1
  unfold midProd
  rw [show 2 * h = h + h by ring, Finset.sum_range_add]
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro r hr
  rw [Finset.mem_range] at hr
  have h1 : i + (h + h) - 1 - r = i + h - 1 - r + h := by omega
  have h2 : i + (h + h) - 1 - (h + r) = i + h - 1 - r := by omega
  have h3 : h + r = r + h := by omega
  dsimp only [Psum, P0, P1, Qmid, Q1, Qlo]
  rw [h1, h2, h3]
  ring

theorem midProd_even_hi (h : ℕ) (P Q : ℕ → Polynomial ℤ) (i : ℕ) :
    let P0 := fun r => P r
    let P1 := fun r => P (r + h)
    let Psum := fun r => P0 r + P1 r
    let Qmid := fun s => Q (s + h)
    let Qhi := fun s => Q (s + 2 * h)
    let Q2 := fun s => Qhi s - Qmid s
    midProd (2 * h) P Q (i + h) = midProd h Psum Qmid i + midProd h P0 Q2 i := by
  intro P0 P1 Psum Qmid Qhi Q2
  unfold midProd
  rw [show 2 * h = h + h by ring, Finset.sum_range_add]
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro r hr
  rw [Finset.mem_range] at hr
  have h1 : i + h + (h + h) - 1 - r = i + h - 1 - r + 2 * h := by omega
  have h2 : i + h + (h + h) - 1 - (h + r) = i + h - 1 - r + h := by omega
  have h3 : h + r = r + h := by omega
  dsimp only [Psum, P0, P1, Qmid, Q2, Qhi]
  rw [h1, h2, h3]
  ring

/-- Helper: sum of `4` given wires `f 0 + f 1 + f 2 + f 3` in `3` gates (no `0` wire needed!). -/
theorem canBuild_sum4 (a b c d : Polynomial ℤ) :
    CanBuild ({a, b, c, d} : Set (Polynomial ℤ)) 3 {a + b + c + d} := by
  have s1 := canBuild_mono_in (S₂ := {a, b, c, d})
    (by intro x hx; rcases hx with rfl | rfl <;> simp) (canBuild_add a b)
  have s2 := canBuild_trans s1 (by intro x hx; rcases hx with rfl | rfl <;> simp)
    (canBuild_add (a + b) c)
  have s3 := canBuild_trans s2 (by intro x hx; rcases hx with rfl | rfl <;> simp)
    (canBuild_add (a + b + c) d)
  exact canBuild_mono_out (fun x hx => Or.inr hx) s3

/-- Base case `k = 2` (`n = 4`): schoolbook `4 × 4` middle product in `28 = 4 * 7` gates. -/
theorem canBuild_midProd_four (P Q : ℕ → Polynomial ℤ) :
    CanBuild ((⋃ r < 4, {P r}) ∪ (⋃ s < 7, {Q s})) 28 (⋃ i < 4, {midProd 4 P Q i}) := by
  refine canBuild_fin_union (n := 4) (d := 7) (T := fun i => {midProd 4 P Q i}) ?_
  intro i hi
  have h4m :
      CanBuild ((⋃ r < 4, {P r}) ∪ (⋃ s < 7, {Q s})) 4
        (⋃ r < 4, {P r * Q (i + 3 - r)}) := by
    simpa using canBuild_fin_union (n := 4) (d := 1)
      (S := (⋃ r < 4, {P r}) ∪ (⋃ s < 7, {Q s}))
      (T := fun r => {P r * Q (i + 3 - r)}) (by
        intro r hr
        refine canBuild_mono_in ?_ (canBuild_mul (P r) (Q (i + 3 - r)))
        intro x hx; rcases hx with rfl | rfl
        · left; simp only [Set.mem_iUnion, exists_prop]; exact ⟨r, hr, rfl⟩
        · right; simp only [Set.mem_iUnion, exists_prop]; exact ⟨i + 3 - r, by omega, rfl⟩)
  have hs := canBuild_sum4 (P 0 * Q (i + 3 - 0)) (P 1 * Q (i + 3 - 1))
    (P 2 * Q (i + 3 - 2)) (P 3 * Q (i + 3 - 3))
  have hcomb := canBuild_trans h4m (by
    intro x hx
    rcases hx with rfl | rfl | rfl | rfl <;>
    · right; simp only [Set.mem_iUnion, exists_prop]
      first | exact ⟨0, by omega, rfl⟩ | exact ⟨1, by omega, rfl⟩
            | exact ⟨2, by omega, rfl⟩ | exact ⟨3, by omega, rfl⟩) hs
  refine canBuild_mono_out ?_ hcomb
  intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx
  right; rw [Set.mem_singleton_iff]
  simp [midProd, Finset.sum_range_succ, add_assoc]

/-- **Power-of-2 Karatsuba Middle Product (`CanBuild`) for `k ≥ 2`:**
Computes `{midProd (2^k) P Q i | i < 2^k}` in `midCost k` gates (`midCost 5 = 1262`). -/
theorem canBuild_karaMid :
    ∀ (k : ℕ), 2 ≤ k →
      ∀ (P Q : ℕ → Polynomial ℤ),
        CanBuild
          ((⋃ r < 2 ^ k, {P r}) ∪ (⋃ s < 2 * 2 ^ k - 1, {Q s}))
          (midCost k)
          (⋃ i < 2 ^ k, {midProd (2 ^ k) P Q i})
  | 0, hk, _, _ => by omega
  | 1, hk, _, _ => by omega
  | 2, _, P, Q => by
      simpa [midCost] using canBuild_midProd_four P Q
  | k + 3, _, P, Q => by
      set h := 2 ^ (k + 2)
      have hh : 2 ^ (k + 3) = 2 * h := by simp [h, pow_succ, mul_comm]
      have hpos : 1 ≤ h := Nat.one_le_two_pow
      let P0 := fun r => P r
      let P1 := fun r => P (r + h)
      let Psum := fun r => P0 r + P1 r
      let Qlo := fun s => Q s
      let Qmid := fun s => Q (s + h)
      let Qhi := fun s => Q (s + 2 * h)
      let Q1 := fun s => Qlo s - Qmid s
      let Q2 := fun s => Qhi s - Qmid s
      let M0 := midProd h Psum Qmid
      let M1 := midProd h P1 Q1
      let M2 := midProd h P0 Q2
      set S0 : Set (Polynomial ℤ) :=
        (⋃ r < 2 ^ (k + 3), {P r}) ∪ (⋃ s < 2 * 2 ^ (k + 3) - 1, {Q s})
      -- Step 1 (`h` gates): Psum
      have hPsum : CanBuild S0 h (⋃ r < h, {Psum r}) := by
        simpa using canBuild_fin_union (n := h) (d := 1) (S := S0) (T := fun r => {Psum r}) (by
          intro r hr
          refine canBuild_mono_in ?_ (canBuild_add (P0 r) (P1 r))
          intro x hx; rcases hx with rfl | rfl
          · left; simp only [Set.mem_iUnion, exists_prop]; exact ⟨r, by omega, rfl⟩
          · left; simp only [Set.mem_iUnion, exists_prop]; exact ⟨r + h, by omega, rfl⟩)
      -- Step 2 (`2*h - 1` gates): Q1
      have hQ1 : CanBuild S0 (2 * h - 1) (⋃ s < 2 * h - 1, {Q1 s}) := by
        simpa using canBuild_fin_union (n := 2 * h - 1) (d := 1) (S := S0) (T := fun s => {Q1 s}) (by
          intro s hs
          refine canBuild_mono_in ?_ (canBuild_sub (Qlo s) (Qmid s))
          intro x hx; rcases hx with rfl | rfl
          · right; simp only [Set.mem_iUnion, exists_prop]; exact ⟨s, by omega, rfl⟩
          · right; simp only [Set.mem_iUnion, exists_prop]; exact ⟨s + h, by omega, rfl⟩)
      -- Step 3 (`2*h - 1` gates): Q2
      have hQ2 : CanBuild S0 (2 * h - 1) (⋃ s < 2 * h - 1, {Q2 s}) := by
        simpa using canBuild_fin_union (n := 2 * h - 1) (d := 1) (S := S0) (T := fun s => {Q2 s}) (by
          intro s hs
          refine canBuild_mono_in ?_ (canBuild_sub (Qhi s) (Qmid s))
          intro x hx; rcases hx with rfl | rfl
          · right; simp only [Set.mem_iUnion, exists_prop]; exact ⟨s + 2 * h, by omega, rfl⟩
          · right; simp only [Set.mem_iUnion, exists_prop]; exact ⟨s + h, by omega, rfl⟩)
      -- Step 4 (`3 * midCost (k + 2)` gates): M0, M1, M2
      have hM0 := canBuild_karaMid (k + 2) (by omega) Psum Qmid
      have hM1 := canBuild_karaMid (k + 2) (by omega) P1 Q1
      have hM2 := canBuild_karaMid (k + 2) (by omega) P0 Q2
      have c1 := canBuild_trans hPsum Set.subset_union_left hQ1
      have c2 := canBuild_trans c1 Set.subset_union_left hQ2
      have c3 := canBuild_trans c2 (by
        intro x hx; rcases hx with hxP | hxQ
        · right; left; left; exact hxP
        · left; right; simp only [Set.mem_iUnion, exists_prop] at hxQ ⊢
          rcases hxQ with ⟨s, hs, hxs⟩; exact ⟨s + h, by omega, hxs⟩) hM0
      have c4 := canBuild_trans c3 (by
        intro x hx; rcases hx with hxP | hxQ
        · left; left; simp only [Set.mem_iUnion, exists_prop] at hxP ⊢
          rcases hxP with ⟨r, hr, hxr⟩; exact ⟨r + h, by omega, hxr⟩
        · right; left; left; right; exact hxQ) hM1
      have c5 := canBuild_trans c4 (by
        intro x hx; rcases hx with hxP | hxQ
        · left; left; simp only [Set.mem_iUnion, exists_prop] at hxP ⊢
          rcases hxP with ⟨r, hr, hxr⟩; exact ⟨r, by omega, hxr⟩
        · right; left; left; right; exact hxQ) hM2
      -- Step 5 (`2 * h` gates): combine M0 + M1 and M0 + M2
      have hComb1 :
          CanBuild ((⋃ i < h, {M0 i}) ∪ (⋃ i < h, {M1 i})) h
            (⋃ i < h, {M0 i + M1 i}) := by
        simpa using canBuild_fin_union (n := h) (d := 1) (T := fun i => {M0 i + M1 i}) (by
          intro i hi
          refine canBuild_mono_in ?_ (canBuild_add (M0 i) (M1 i))
          intro x hx; rcases hx with rfl | rfl
          · left; simp only [Set.mem_iUnion, exists_prop]; exact ⟨i, hi, rfl⟩
          · right; simp only [Set.mem_iUnion, exists_prop]; exact ⟨i, hi, rfl⟩)
      have hComb2 :
          CanBuild ((⋃ i < h, {M0 i}) ∪ (⋃ i < h, {M2 i})) h
            (⋃ i < h, {M0 i + M2 i}) := by
        simpa using canBuild_fin_union (n := h) (d := 1) (T := fun i => {M0 i + M2 i}) (by
          intro i hi
          refine canBuild_mono_in ?_ (canBuild_add (M0 i) (M2 i))
          intro x hx; rcases hx with rfl | rfl
          · left; simp only [Set.mem_iUnion, exists_prop]; exact ⟨i, hi, rfl⟩
          · right; simp only [Set.mem_iUnion, exists_prop]; exact ⟨i, hi, rfl⟩)
      have c6 := canBuild_trans c5 (by
        intro x hx; rcases hx with hx0 | hx1
        · right; left; left; right; exact hx0
        · right; left; right; exact hx1) hComb1
      have c7 := canBuild_trans c6 (by
        intro x hx; rcases hx with hx0 | hx2
        · right; left; left; left; right; exact hx0
        · right; left; right; exact hx2) hComb2
      have hcost :
          h + (2 * h - 1) + (2 * h - 1) + midCost (k + 2) + midCost (k + 2) + midCost (k + 2) +
              h + h = midCost (k + 3) := by
        change _ = 3 * midCost (k + 2) + 7 * 2 ^ (k + 2) - 2
        omega
      rw [hcost] at c7
      refine canBuild_mono_out ?_ c7
      intro x hx
      simp only [Set.mem_iUnion, exists_prop, Set.mem_singleton_iff] at hx
      rcases hx with ⟨i, hi, rfl⟩
      by_cases hih : i < h
      · rw [hh, midProd_even_lo h P Q i]
        left; right
        simp only [Set.mem_iUnion, exists_prop]
        exact ⟨i, hih, rfl⟩
      · have hi_eq : i = (i - h) + h := by omega
        rw [hh, hi_eq, midProd_even_hi h P Q (i - h)]
        right
        simp only [Set.mem_iUnion, exists_prop]
        exact ⟨i - h, by omega, rfl⟩

/-- **Machine-Verified Concrete Finite Crossover (`z_max(1884) ≥ 2049 > 1884`):**
There exists a constant-free straight-line program of length `1884` over `ℤ[X]` computing a
nonzero polynomial with at least `2049` distinct integer roots (`2049 > 1884`, proving
strictly more distinct integer roots than gates at an explicit finite length). -/
theorem tau_crossover_1884_2049 : zMaxGe 1884 2049 := by
  -- Use m = 32 = 2^5: `chirp_middle_product` = `midProd 32 (chirpA 32) (fun s => chirpB 32 (s + 1)) i + chirpA 32 32 * chirpB 32 i`
  have hmid := canBuild_karaMid 5 (by omega) (chirpA 32) (fun s => chirpB 32 (s + 1))
  set S0 : Set (Polynomial ℤ) :=
    {(0 : Polynomial ℤ)} ∪ (⋃ r < 32 + 1, {chirpA 32 r}) ∪ (⋃ s < 2 * 32, {chirpB 32 s})
  have h1 : CanBuild S0 (midCost 5) (⋃ i < 32, {midProd 32 (chirpA 32) (fun s => chirpB 32 (s + 1)) i}) := by
    refine canBuild_mono_in ?_ hmid
    intro x hx; rcases hx with hxA | hxB
    · left; right; simp only [Set.mem_iUnion, exists_prop] at hxA ⊢
      rcases hxA with ⟨r, hr, hxr⟩; exact ⟨r, by omega, hxr⟩
    · right; simp only [Set.mem_iUnion, exists_prop] at hxB ⊢
      rcases hxB with ⟨s, hs, hxs⟩; exact ⟨s + 1, by omega, hxs⟩
  -- Add the `r = 32` term `chirpA 32 32 * chirpB 32 i` (`2 * 32 = 64` gates)
  have h2 :
      CanBuild
        (S0 ∪ ⋃ i < 32, {midProd 32 (chirpA 32) (fun s => chirpB 32 (s + 1)) i})
        (32 * 2)
        (⋃ i < 32, {Polynomial.C (1 : ℤ) *
          ∑ r ∈ Finset.range (32 + 1), chirpA 32 r * chirpB 32 (i + 32 - r)}) := by
    refine canBuild_fin_union (n := 32) (d := 2)
      (T := fun i => {Polynomial.C (1 : ℤ) *
        ∑ r ∈ Finset.range (32 + 1), chirpA 32 r * chirpB 32 (i + 32 - r)}) ?_
    intro i hi
    have hm := canBuild_mul (chirpA 32 32) (chirpB 32 i)
    have ha := canBuild_add (midProd 32 (chirpA 32) (fun s => chirpB 32 (s + 1)) i)
      (chirpA 32 32 * chirpB 32 i)
    have hma := canBuild_trans
      (canBuild_mono_in (S₂ := {midProd 32 (chirpA 32) (fun s => chirpB 32 (s + 1)) i,
        chirpA 32 32, chirpB 32 i}) (by intro x hx; rcases hx with rfl | rfl <;> simp) hm)
      (by intro x hx; rcases hx with rfl | rfl <;> simp) ha
    have heq :
        midProd 32 (chirpA 32) (fun s => chirpB 32 (s + 1)) i + chirpA 32 32 * chirpB 32 i =
          Polynomial.C (1 : ℤ) *
            ∑ r ∈ Finset.range (32 + 1), chirpA 32 r * chirpB 32 (i + 32 - r) := by
      rw [map_one, one_mul, Finset.sum_range_succ, show i + 32 - 32 = i by omega]
      have hsum : midProd 32 (chirpA 32) (fun s => chirpB 32 (s + 1)) i =
          ∑ r ∈ Finset.range 32, chirpA 32 r * chirpB 32 (i + 32 - r) := by
        unfold midProd
        refine Finset.sum_congr rfl ?_
        intro r hr
        rw [Finset.mem_range] at hr
        have hidx : i + 32 - 1 - r + 1 = i + 32 - r := by omega
        dsimp only
        rw [hidx]
      rw [hsum]
    refine canBuild_mono_out
      (T₂ := {chirpA 32 32 * chirpB 32 i} ∪
        {midProd 32 (chirpA 32) (fun s => chirpB 32 (s + 1)) i + chirpA 32 32 * chirpB 32 i})
      (by intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx; right; rw [Set.mem_singleton_iff, heq])
      (canBuild_mono_in ?_ hma)
    intro x hx
    rcases hx with rfl | rfl | rfl
    · right; simp only [Set.mem_iUnion, exists_prop]; exact ⟨i, hi, rfl⟩
    · left; left; right; simp only [Set.mem_iUnion, exists_prop]; exact ⟨32, by omega, rfl⟩
    · left; right; simp only [Set.mem_iUnion, exists_prop]; exact ⟨i, by omega, rfl⟩
  have hstep := canBuild_mono_out Set.subset_union_right (canBuild_seq h1 h2)
  have hz := zMaxGe_of_chirp_engine (m := 32) (by omega) 1 (by omega) hstep
  have hcost : 17 * 32 + (midCost 5 + 32 * 2) + 14 = 1884 := by decide
  have hroots : 2 * (32 * 32) + 1 = 2049 := by decide
  rwa [hcost, hroots] at hz

/-- Existential witness that constant-free SLPs over `ℤ[X]` strictly beat `z_max(τ) ≤ τ`. -/
theorem tau_exists_roots_gt_gates : ∃ τ r : ℕ, τ < r ∧ zMaxGe τ r :=
  ⟨1884, 2049, by omega, tau_crossover_1884_2049⟩

end Research.PvsNP.Tau

end