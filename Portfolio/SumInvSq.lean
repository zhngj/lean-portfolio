import Mathlib

/-!
# Partial sums of `1/k²` are bounded by `2 - 1/n`

For every `n ≥ 1`,

  `1/1² + 1/2² + ⋯ + 1/n² ≤ 2 - 1/n`,

and consequently every partial sum of the series `∑ 1/k²` is below `2`.
The proof is the classical telescoping argument: for `m ≥ 1`,
`1/(m+1)² < 1/(m(m+1)) = 1/m - 1/(m+1)`.
-/

namespace Portfolio

open Finset

/-- The telescoping estimate `1/(m+1)² ≤ 1/m - 1/(m+1)` for `m ≥ 1`. -/
theorem one_div_succ_sq_le_telescope (m : ℕ) (hm : 1 ≤ m) :
    (1 : ℚ) / ((m : ℚ) + 1) ^ 2 ≤ 1 / (m : ℚ) - 1 / ((m : ℚ) + 1) := by
  have hm0 : (0 : ℚ) < m := by exact_mod_cast hm
  have hm1 : (0 : ℚ) < (m : ℚ) + 1 := by linarith
  have hsub : 1 / (m : ℚ) - 1 / ((m : ℚ) + 1) = 1 / ((m : ℚ) * ((m : ℚ) + 1)) := by
    field_simp
    ring
  rw [hsub]
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

/-- For `n ≥ 1`, `∑_{k=1}^{n} 1/k² ≤ 2 - 1/n`. -/
theorem sum_one_div_sq_le (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Icc 1 n, (1 : ℚ) / (k : ℚ) ^ 2 ≤ 2 - 1 / (n : ℚ) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    rw [sum_Icc_succ_top (by omega)]
    have key := one_div_succ_sq_le_telescope m hm
    push_cast
    linarith

/-- Every partial sum of `∑ 1/k²` is strictly below `2`. -/
theorem sum_one_div_sq_lt_two (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Icc 1 n, (1 : ℚ) / (k : ℚ) ^ 2 < 2 := by
  have h := sum_one_div_sq_le n hn
  have hn0 : (0 : ℚ) < 1 / (n : ℚ) := by
    have : (0 : ℚ) < n := by exact_mod_cast hn
    positivity
  linarith

end Portfolio
