import Mathlib

/-!
# The Hurwitz equation `x² + y² + z² = k·x·y·z`

If positive integers `x, y, z` satisfy `x² + y² + z² = k x y z`, then `k = 1` or `k = 3`
(Hurwitz, 1907).  Both values occur: `(1, 1, 1)` solves the Markov equation (`k = 3`)
and `(3, 3, 3)` solves the case `k = 1`.

The proof is *Vieta jumping*.  Order the solution so that `x ≤ y ≤ z` and view the equation
as a quadratic in `z`: its other root `z' = k x y - z = (x² + y²)/z` is again a positive
integer, so `(x, y, z')` is another positive solution.

* If `z' < z` the new solution has a smaller sum, and we conclude by strong induction.
* If `z ≤ z'` then `z² ≤ z z' = x² + y² ≤ 2 y²`, and the equation forces `k x ≤ 3`
  (otherwise `4 y z ≤ k x y z = x² + y² + z² ≤ 4 y² ≤ 4 y z` with equality impossible).
  Then `k ≤ 3`; `k = 0` is absurd, and `k = 2` forces `x = 1` and `1 + y² + z² = 2 y z`,
  which contradicts `y² + z² ≥ 2 y z`.
-/

namespace Portfolio

/-- Strong induction on the sum `x + y + z`; the statement is symmetric in `x, y, z`,
so inside the induction we may assume `x ≤ y ≤ z`. -/
theorem hurwitz_aux (k : ℕ) : ∀ s : ℕ, ∀ x y z : ℕ, x + y + z = s →
    0 < x → 0 < y → 0 < z → x ^ 2 + y ^ 2 + z ^ 2 = k * x * y * z → k = 1 ∨ k = 3 := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
  -- The ordered case.
  have sorted : ∀ x y z : ℕ, x + y + z = s → 0 < x → 0 < y → 0 < z → x ≤ y → y ≤ z →
      x ^ 2 + y ^ 2 + z ^ 2 = k * x * y * z → k = 1 ∨ k = 3 := by
    intro x y z hs hx hy hz hxy hyz h
    -- The other root of the quadratic in `z`.
    have hkxy : z < k * x * y := by
      have h1 : z * z < k * x * y * z := by nlinarith [pow_pos hx 2, pow_pos hy 2]
      exact Nat.lt_of_mul_lt_mul_right h1
    set z' := k * x * y - z with hz'
    have hz'z : z' + z = k * x * y := by rw [hz']; exact Nat.sub_add_cancel hkxy.le
    have hzz' : z * z' = x ^ 2 + y ^ 2 := by
      have h2 : z * z' + z * z = z * (k * x * y) := by rw [← hz'z]; ring
      nlinarith [h, h2]
    have hz'pos : 0 < z' := by
      rcases Nat.eq_zero_or_pos z' with h0 | h0
      · rw [h0, mul_zero] at hzz'
        nlinarith [pow_pos hx 2, pow_pos hy 2]
      · exact h0
    rcases lt_or_ge z' z with hlt | hle
    · -- Descent: `(x, y, z')` is a smaller positive solution.
      have h' : x ^ 2 + y ^ 2 + z' ^ 2 = k * x * y * z' := by
        have h3 : k * x * y * z' = z' * z' + z * z' := by rw [← hz'z]; ring
        nlinarith [hzz', h3]
      exact ih (x + y + z') (by omega) x y z' rfl hx hy hz'pos h'
    · -- Base case: `z ≤ z'`, so `z² ≤ x² + y²`.
      have hz2 : z ^ 2 ≤ x ^ 2 + y ^ 2 := by
        have := Nat.mul_le_mul_left z hle
        rw [hzz'] at this
        simpa [sq] using this
      have hx2 : x ^ 2 ≤ y ^ 2 := Nat.pow_le_pow_left hxy 2
      have hkx : k * x ≤ 3 := by
        by_contra hcon
        have hcon4 : 4 ≤ k * x := by omega
        have e1 : 4 * (y * z) ≤ k * x * (y * z) := Nat.mul_le_mul_right _ hcon4
        have e2 : k * x * (y * z) = x ^ 2 + y ^ 2 + z ^ 2 := by rw [h]; ring
        have e3 : y * y ≤ y * z := Nat.mul_le_mul_left y hyz
        have e4 : y * z ≤ y * y := by nlinarith [e1, e2, hz2, hx2, e3]
        have hzy : z = y := le_antisymm (Nat.le_of_mul_le_mul_left e4 hy) hyz
        subst hzy
        nlinarith [e1, e2, hx2, Nat.mul_pos hy hy]
      have hk0 : k ≠ 0 := by
        rintro rfl
        nlinarith [pow_pos hx 2, pow_pos hy 2, pow_pos hz 2]
      have hk2 : k ≠ 2 := by
        rintro rfl
        have hx1 : x = 1 := by omega
        subst hx1
        have hZ : ((1 : ℕ) : ℤ) ^ 2 + (y : ℤ) ^ 2 + (z : ℤ) ^ 2 = 2 * 1 * y * z := by
          exact_mod_cast h
        nlinarith [sq_nonneg ((y : ℤ) - z)]
      have hk3 : k ≤ 3 := by
        calc k = k * 1 := (mul_one k).symm
          _ ≤ k * x := Nat.mul_le_mul_left k hx
          _ ≤ 3 := hkx
      omega
  -- Reduce the general case to the ordered one.
  intro x y z hs hx hy hz h
  rcases le_total x y with hxy | hxy <;> rcases le_total y z with hyz | hyz <;>
    rcases le_total x z with hxz | hxz
  all_goals first
    | exact sorted x y z (by omega) hx hy hz (by omega) (by omega) (by linarith [h])
    | exact sorted x z y (by omega) hx hz hy (by omega) (by omega)
        (by linarith [h, show k * x * y * z = k * x * z * y by ring])
    | exact sorted y x z (by omega) hy hx hz (by omega) (by omega)
        (by linarith [h, show k * x * y * z = k * y * x * z by ring])
    | exact sorted y z x (by omega) hy hz hx (by omega) (by omega)
        (by linarith [h, show k * x * y * z = k * y * z * x by ring])
    | exact sorted z x y (by omega) hz hx hy (by omega) (by omega)
        (by linarith [h, show k * x * y * z = k * z * x * y by ring])
    | exact sorted z y x (by omega) hz hy hx (by omega) (by omega)
        (by linarith [h, show k * x * y * z = k * z * y * x by ring])

/-- **Hurwitz's theorem** for three variables: a positive solution of
`x² + y² + z² = k x y z` forces `k = 1` or `k = 3`. -/
theorem hurwitz_k_eq_one_or_three (k x y z : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x ^ 2 + y ^ 2 + z ^ 2 = k * x * y * z) : k = 1 ∨ k = 3 :=
  hurwitz_aux k (x + y + z) x y z rfl hx hy hz h

/-- Both values occur: `(1, 1, 1)` is a Markov triple (`k = 3`). -/
theorem markov_one_one_one : 1 ^ 2 + 1 ^ 2 + 1 ^ 2 = 3 * 1 * 1 * 1 := by norm_num

/-- Both values occur: `(3, 3, 3)` solves the case `k = 1`. -/
theorem hurwitz_three_three_three : 3 ^ 2 + 3 ^ 2 + 3 ^ 2 = 1 * 3 * 3 * 3 := by norm_num

end Portfolio
