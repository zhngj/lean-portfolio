import Mathlib

/-!
# Lattice points under a hyperbola and the divisor function

Let `d(k)` be the number of positive divisors of `k`.  Counting the lattice points
`(a, b)` with `1 ≤ a, b ≤ n` and `a·b ≤ n` in two ways gives

  `#{(a, b) : a b ≤ n} = ∑_{k=1}^{n} d(k) = ∑_{a=1}^{n} ⌊n / a⌋`.

* Grouping the points by the value `k = a·b` gives the divisor sum
  (each `k` contributes its `d(k)` factorisations `k = a·b`).
* Grouping them by the column `a` gives `⌊n/a⌋` points in column `a`.

This is the first step of Dirichlet's hyperbola method for the average order of `d`.
-/

namespace Portfolio

open Finset

/-- The lattice points `(a, b)` with `1 ≤ a, b ≤ n` and `a * b ≤ n`. -/
def hyperbolaPoints (n : ℕ) : Finset (ℕ × ℕ) :=
  (Icc 1 n ×ˢ Icc 1 n).filter fun p => p.1 * p.2 ≤ n

theorem mem_hyperbolaPoints {n : ℕ} {p : ℕ × ℕ} :
    p ∈ hyperbolaPoints n ↔ (1 ≤ p.1 ∧ p.1 ≤ n) ∧ (1 ≤ p.2 ∧ p.2 ≤ n) ∧ p.1 * p.2 ≤ n := by
  simp [hyperbolaPoints, and_assoc]

/-- The points with product exactly `k` (for `1 ≤ k ≤ n`) are the factorisations of `k`. -/
theorem filter_prod_eq_divisorsAntidiagonal {n k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    (hyperbolaPoints n).filter (fun p => p.1 * p.2 = k) = Nat.divisorsAntidiagonal k := by
  ext ⟨a, b⟩
  simp only [mem_filter, mem_hyperbolaPoints, Nat.mem_divisorsAntidiagonal]
  constructor
  · rintro ⟨⟨_, _, _⟩, hab⟩
    exact ⟨hab, by omega⟩
  · rintro ⟨hab, -⟩
    have ha : 1 ≤ a := by
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · simp at hab; omega
      · exact ha
    have hb : 1 ≤ b := by
      rcases Nat.eq_zero_or_pos b with rfl | hb
      · simp at hab; omega
      · exact hb
    refine ⟨⟨⟨ha, ?_⟩, ⟨hb, ?_⟩, by omega⟩, hab⟩
    · calc a = a * 1 := (mul_one a).symm
        _ ≤ a * b := Nat.mul_le_mul_left a hb
        _ ≤ n := by omega
    · calc b = 1 * b := (one_mul b).symm
        _ ≤ a * b := Nat.mul_le_mul_right b ha
        _ ≤ n := by omega

/-- Counting by the value of the product: `#{(a,b) : a b ≤ n} = ∑_{k=1}^{n} d(k)`. -/
theorem card_hyperbolaPoints_eq_sum_divisors (n : ℕ) :
    (hyperbolaPoints n).card = ∑ k ∈ Icc 1 n, (Nat.divisors k).card := by
  rw [card_eq_sum_card_fiberwise (f := fun p : ℕ × ℕ => p.1 * p.2) (t := Icc 1 n)]
  · refine sum_congr rfl fun k hk => ?_
    rw [mem_Icc] at hk
    rw [filter_prod_eq_divisorsAntidiagonal hk.1 hk.2, ← Nat.map_div_right_divisors, card_map]
  · intro p hp
    rw [mem_coe, mem_hyperbolaPoints] at hp
    rw [mem_coe, mem_Icc]
    exact ⟨Nat.mul_pos hp.1.1 hp.2.1.1, hp.2.2⟩

/-- The points in column `a` are `(a, b)` with `1 ≤ b ≤ ⌊n / a⌋`. -/
theorem card_filter_fst_eq {n a : ℕ} (ha1 : 1 ≤ a) (han : a ≤ n) :
    ((hyperbolaPoints n).filter (fun p => p.1 = a)).card = n / a := by
  have ha0 : 0 < a := ha1
  have himage : (hyperbolaPoints n).filter (fun p => p.1 = a) =
      (Icc 1 (n / a)).image (Prod.mk a) := by
    ext ⟨c, b⟩
    simp only [mem_filter, mem_hyperbolaPoints, mem_image, mem_Icc, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨_, ⟨hb1, _⟩, hab⟩, rfl⟩
      refine ⟨b, ⟨hb1, (Nat.le_div_iff_mul_le ha0).2 ?_⟩, rfl, rfl⟩
      linarith [hab]
    · rintro ⟨b', ⟨hb1, hb2⟩, rfl, rfl⟩
      have hab : a * b' ≤ n := by
        have := (Nat.le_div_iff_mul_le ha0).1 hb2
        linarith
      refine ⟨⟨⟨ha1, han⟩, ⟨hb1, ?_⟩, hab⟩, rfl⟩
      calc b' = 1 * b' := (one_mul b').symm
        _ ≤ a * b' := Nat.mul_le_mul_right b' ha1
        _ ≤ n := hab
  rw [himage, card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2), Nat.card_Icc]
  simp

/-- Counting by columns: `#{(a,b) : a b ≤ n} = ∑_{a=1}^{n} ⌊n / a⌋`. -/
theorem card_hyperbolaPoints_eq_sum_div (n : ℕ) :
    (hyperbolaPoints n).card = ∑ a ∈ Icc 1 n, n / a := by
  rw [card_eq_sum_card_fiberwise (f := fun p : ℕ × ℕ => p.1) (t := Icc 1 n)]
  · refine sum_congr rfl fun a ha => ?_
    rw [mem_Icc] at ha
    exact card_filter_fst_eq ha.1 ha.2
  · intro p hp
    rw [mem_coe, mem_hyperbolaPoints] at hp
    rw [mem_coe, mem_Icc]
    exact hp.1

/-- **Dirichlet's identity**: `∑_{k=1}^{n} d(k) = ∑_{a=1}^{n} ⌊n / a⌋`. -/
theorem sum_card_divisors_eq_sum_div (n : ℕ) :
    ∑ k ∈ Icc 1 n, (Nat.divisors k).card = ∑ a ∈ Icc 1 n, n / a := by
  rw [← card_hyperbolaPoints_eq_sum_divisors, card_hyperbolaPoints_eq_sum_div]

end Portfolio
