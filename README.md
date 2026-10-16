# lean-portfolio

Self-contained, kernel-checked formalizations in **Lean 4** with **Mathlib**, written as
practice in writing complete proofs against a pinned library version.

| | |
|---|---|
| Lean | `leanprover/lean4:v4.33.0-rc1` (see `lean-toolchain`) |
| Mathlib | commit `9944fe2973b8dc0b86949101ed98232c07cd54a0` (pinned in `lakefile.lean`) |
| Status | every theorem is proved in full: no `sorry`, no extra axioms |

## Theorems

| File | Main result | Informal statement |
|---|---|---|
| `Portfolio/Hurwitz.lean` | `hurwitz_k_eq_one_or_three` | If positive integers satisfy `x² + y² + z² = k·x·y·z`, then `k = 1` or `k = 3` (Hurwitz, 1907). Proved by Vieta jumping with strong induction on `x + y + z`; the witnesses `(1,1,1)` and `(3,3,3)` show both values occur. |
| `Portfolio/Samuelson.lean` | `samuelson_inequality` | For a finite sample with mean `m`, every point satisfies `n·(xⱼ − m)² ≤ (n − 1)·∑ᵢ (xᵢ − m)²`, i.e. no observation lies more than `√(n−1)` standard deviations from the mean. Proved from Cauchy–Schwarz over the other `n − 1` points. |
| `Portfolio/DivisorSum.lean` | `card_hyperbolaPoints_eq_sum_divisors`, `card_hyperbolaPoints_eq_sum_div`, `sum_card_divisors_eq_sum_div` | Counting lattice points under the hyperbola `a·b ≤ n` two ways: `#{(a,b) : a b ≤ n} = ∑_{k≤n} d(k) = ∑_{a≤n} ⌊n/a⌋` (the first step of Dirichlet's hyperbola method). |
| `Portfolio/SumInvSq.lean` | `sum_one_div_sq_le`, `sum_one_div_sq_lt_two` | `∑_{k=1}^{n} 1/k² ≤ 2 − 1/n` for `n ≥ 1`, hence every partial sum of `∑ 1/k²` is below `2`. Telescoping bound `1/(m+1)² ≤ 1/m − 1/(m+1)`. |

## Building

```bash
lake exe cache get   # download the prebuilt Mathlib oleans for the pinned commit
lake build
```

`lake build` compiles `Portfolio.lean`, which imports the four modules above.

## Axiom check

Each main theorem depends only on the three standard axioms of Lean's core
(`propext`, `Classical.choice`, `Quot.sound`), as reported by `#print axioms`:

```
'Portfolio.hurwitz_k_eq_one_or_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'Portfolio.samuelson_inequality' depends on axioms: [propext, Classical.choice, Quot.sound]
'Portfolio.card_hyperbolaPoints_eq_sum_divisors' depends on axioms: [propext, Classical.choice, Quot.sound]
'Portfolio.card_hyperbolaPoints_eq_sum_div' depends on axioms: [propext, Classical.choice, Quot.sound]
'Portfolio.sum_card_divisors_eq_sum_div' depends on axioms: [propext, Classical.choice, Quot.sound]
'Portfolio.sum_one_div_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Portfolio.sum_one_div_sq_lt_two' depends on axioms: [propext, Classical.choice, Quot.sound]
```

To reproduce after `lake build`: `lake env lean Axioms.lean`.
