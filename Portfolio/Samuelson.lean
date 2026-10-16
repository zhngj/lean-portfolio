import Mathlib

/-!
# Samuelson's inequality

For a finite sample `x₁, …, xₙ` with mean `m` and (population) variance
`s² = (1/n) ∑ (xᵢ - m)²`, no observation can lie more than `√(n-1)` standard
deviations away from the mean:

  `(xⱼ - m)² ≤ (n - 1) · s²`,   equivalently   `n (xⱼ - m)² ≤ (n - 1) ∑ᵢ (xᵢ - m)²`.

Proof.  Put `dᵢ = xᵢ - m`, so `∑ dᵢ = 0` and hence `∑_{i ≠ j} dᵢ = -dⱼ`.
Cauchy–Schwarz over the `n - 1` indices `i ≠ j` gives
`dⱼ² = (∑_{i ≠ j} dᵢ)² ≤ (n - 1) ∑_{i ≠ j} dᵢ² = (n - 1)(∑ᵢ dᵢ² - dⱼ²)`,
which rearranges to the claim.
-/

namespace Portfolio

open Finset

/-- The sample mean of `x : Fin n → ℝ`. -/
noncomputable def mean {n : ℕ} (x : Fin n → ℝ) : ℝ := (∑ i, x i) / n

/-- The deviations from the mean sum to zero (for a nonempty sample). -/
theorem sum_sub_mean_eq_zero {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) :
    ∑ i, (x i - mean x) = 0 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mean]
  field_simp
  ring

/-- **Samuelson's inequality.**  For every sample point `x j`,
`n (x j - mean x)² ≤ (n - 1) ∑ i, (x i - mean x)²`. -/
theorem samuelson_inequality {n : ℕ} (x : Fin n → ℝ) (j : Fin n) :
    (n : ℝ) * (x j - mean x) ^ 2 ≤ ((n : ℝ) - 1) * ∑ i, (x i - mean x) ^ 2 := by
  have hn : 0 < n := Fin.pos j
  set d : Fin n → ℝ := fun i => x i - mean x with hd
  have hsum : ∑ i, d i = 0 := sum_sub_mean_eq_zero hn x
  -- Split off the index `j`.
  have hsplit : d j + ∑ i ∈ univ.erase j, d i = ∑ i, d i := add_sum_erase univ d (mem_univ j)
  have hsq : d j ^ 2 + ∑ i ∈ univ.erase j, d i ^ 2 = ∑ i, d i ^ 2 :=
    add_sum_erase univ (fun i => d i ^ 2) (mem_univ j)
  -- Cauchy–Schwarz on the remaining `n - 1` indices.
  have hcs : (∑ i ∈ univ.erase j, d i) ^ 2 ≤
      ((univ.erase j).card : ℝ) * ∑ i ∈ univ.erase j, d i ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have hcard : ((univ.erase j).card : ℝ) = (n : ℝ) - 1 := by
    rw [card_erase_of_mem (mem_univ j), card_univ, Fintype.card_fin, Nat.cast_sub hn]
    simp
  have hrest : ∑ i ∈ univ.erase j, d i = -d j := by linarith
  rw [hcard, hrest, neg_sq] at hcs
  -- Everything is now linear in the monomials `d j ^ 2`, `∑ d i ^ 2`, `n * ∑ d i ^ 2`, ...
  have hS : ∑ i ∈ univ.erase j, d i ^ 2 = ∑ i, d i ^ 2 - d j ^ 2 := by linarith
  rw [hS] at hcs
  nlinarith [hcs]

end Portfolio
