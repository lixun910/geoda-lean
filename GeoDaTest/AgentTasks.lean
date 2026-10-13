/-
Copyright (c) 2026 GeoDa-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import GeoDaTest.Smoke

/-!
# The agent-loop benchmark: the refuted conjecture

The third benchmark task recorded in `docs/agent-tasks.md` is a conjecture that is
**false**. It is here, in the test suite, because the correct outcome of that task is not
a proof — it is a *refutation*, and the agent loop must report it as such rather than
producing something that type-checks for the wrong reason, or quietly weakening the
statement until it becomes true.

The conjecture: *every* nonnegative weights matrix gives an invertible spatial multiplier
for `|ρ| < 1`. It is a natural over-generalization of
`GeoDa.isUnit_one_sub_smul_of_rowSubstochastic`, and it is wrong, because nonnegativity
alone imposes no bound on the row sums: `2 • 1` has rows summing to `2`, and at `ρ = 1/2`
the multiplier is `1 - (1/2)·2·1 = 0`.

`GeoDaTest.wtwo_not_isUnit` is the counterexample itself. The theorem below turns it into
the *refutation of the universal statement*, so that "this conjecture is false" is a
checked fact rather than a remark in a log file.
-/

open scoped Matrix

namespace GeoDaTest

open GeoDa

/-- **Nonnegativity alone does not make the multiplier invertible.**

The universal statement `Nonneg W → |ρ| < 1 → IsUnit (1 - ρ • W)` is false. The
counterexample is `Wtwo = 2 • 1` at `ρ = 1/2`, where the multiplier is `0`; see
`wtwo_not_isUnit`. The hypothesis that is missing is `RowSubstochastic`, and that is
exactly what `isUnit_one_sub_smul_of_rowSubstochastic` assumes. -/
theorem nonneg_alone_is_not_enough :
    ¬ (∀ (n : ℕ) (W : WMat n) (ρ : ℝ), Nonneg W → |ρ| < 1 → IsUnit (1 - ρ • W)) := by
  intro h
  exact wtwo_not_isUnit (h 2 Wtwo (1 / 2) wtwo_nonneg (by norm_num))

/-- Nor does replacing nonnegativity by row-substochasticity alone work: that conjecture
fails on `Wneg = !![2, -1; 0, 0]`, whose rows sum to `1` and `0` but which has a negative
entry. Both hypotheses of `isUnit_one_sub_smul_of_rowSubstochastic` are needed, and
`GeoDaTest.wneg_not_isUnit` is the witness. -/
theorem rowSubstochastic_alone_is_not_enough :
    ¬ (∀ (n : ℕ) (W : WMat n) (ρ : ℝ), RowSubstochastic W → |ρ| < 1 → IsUnit (1 - ρ • W)) := by
  intro h
  exact wneg_not_isUnit (h 2 Wneg (1 / 2) wneg_rowSubstochastic (by norm_num))

/-! ### Task B's theorem, on a concrete column-substochastic matrix -/

/-- The column-substochastic hypothesis is satisfied by the transpose of the island
matrix — column `1` sums to `1`, column `0` is zero — so the transposed multiplier is a
unit for `|ρ| < 1`, by `isUnit_one_sub_smul_transpose_of_colSubstochastic`. -/
example : ColSubstochastic Wisland := by
  intro j
  fin_cases j <;> norm_num [colSum, Wisland, Fin.sum_univ_two]

example (ρ : ℝ) (hρ : |ρ| < 1) : IsUnit (1 - ρ • Wislandᵀ) :=
  isUnit_one_sub_smul_transpose_of_colSubstochastic Wisland wisland_nonneg
    (by intro j; fin_cases j <;> norm_num [colSum, Wisland, Fin.sum_univ_two]) ρ hρ

end GeoDaTest
