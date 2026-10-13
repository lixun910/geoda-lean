/-
Copyright (c) 2026 GeoDa-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import GeoDa.Weights
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Spatial weights: predicates, row normalization and islands

`GeoDa.Weights` lets `W` be an *arbitrary* real matrix. In applications a spatial
weights matrix is not arbitrary: its entries are expected to be nonnegative, and
very often each row is standardized to sum to one. This file introduces those
assumptions as **explicit predicates** rather than as background conventions, and
proves how they interact with row sums and with row normalization.

Two conventions that this file deliberately does *not* build in:

* **Symmetry** is nowhere assumed. None of the results below requires it.
* **A zero diagonal** is kept separate from row standardization. A zero diagonal
  is a modelling choice (a region not being its own neighbour), and it is neither
  implied by nor implies row standardization: the identity matrix is
  row-stochastic with a nonzero diagonal (`GeoDa.not_zeroDiag_one`), while
  `!![0, 1; 0, 0]` has a zero diagonal but is not row-stochastic.

The other point of care is **islands** — regions with no neighbours, i.e. zero
rows. Normalization is a total function: `ℝ`'s inverse is totalized by
`(0 : ℝ)⁻¹ = 0`, so a zero row is carried to a zero row instead of triggering an
undefined division by zero, and `GeoDa.island_normalize` records that islands
survive normalization. Consequently the normalized matrix is always
row-substochastic (`GeoDa.rowSubstochastic_normalize`) and is row-stochastic
exactly when the original matrix has no island
(`GeoDa.rowStochastic_normalize_iff`).

## Main definitions

* `GeoDa.rowSum` : the sum of the entries of a row.
* `GeoDa.Nonneg` : entry-wise nonnegativity.
* `GeoDa.RowStochastic`, `GeoDa.RowSubstochastic` : row sums equal to, resp. at
  most, one.
* `GeoDa.Island` : a zero row (a region with no neighbours).
* `GeoDa.ZeroDiag` : a zero diagonal.
* `GeoDa.normalize` : row normalization, which maps islands to islands.

## Main results

* `GeoDa.mulVec_one_apply` : `(W *ᵥ 1) i = ∑ j, W i j`.
* `GeoDa.rowStochastic_iff_mulVec_one` : `W *ᵥ 1 = 1` exactly for
  row-stochastic `W`.
* `GeoDa.island_iff_rowSum_eq_zero` : for nonnegative `W`, a row is an island
  exactly when its sum vanishes.
* `GeoDa.not_rowStochastic_of_island` : row-stochastic weights have no islands.
* `GeoDa.rowStochastic_normalize_iff`, `GeoDa.rowStochastic_normalize_iff_pos` :
  for nonnegative `W`, normalization is row-stochastic exactly when there is no
  island, equivalently when every row sum is positive.

Nothing here claims anything about estimators, identifiability or probability
distributions; these are statements about the weights matrix alone.
-/

open scoped Matrix
open Matrix

namespace GeoDa

variable {n : ℕ}

/-! ### Row sums -/

/-- The sum of the entries of row `i` of a weights matrix. -/
def rowSum (W : WMat n) (i : Fin n) : ℝ := ∑ j, W i j

/-- **Row-sum identity:** applying `W` to the constant vector `1` sums each row,
`(W *ᵥ 1) i = ∑ j, W i j`. -/
theorem mulVec_one_apply (W : WMat n) (i : Fin n) :
    (W *ᵥ (1 : Vec n)) i = rowSum W i := by
  rw [Matrix.mulVec_apply_eq_sum]
  simp only [Pi.one_apply, mul_one, rowSum]

/-! ### Predicates -/

/-- **Nonnegative weights:** every entry is `≥ 0`. This is the standard
assumption on a spatial weights matrix. It is *not* assumed by the definitions in
this file — only by the theorems that need it. -/
def Nonneg (W : WMat n) : Prop := ∀ i j, 0 ≤ W i j

/-- **Row standardization (row stochasticity):** every row sums to `1`. A region
therefore distributes unit total weight across its neighbours. -/
def RowStochastic (W : WMat n) : Prop := ∀ i, rowSum W i = 1

/-- **Row substochasticity:** every row sums to at most `1`. This is strictly
weaker than row standardization, and is what normalization yields when the
weights have islands (`GeoDa.rowSubstochastic_normalize`). -/
def RowSubstochastic (W : WMat n) : Prop := ∀ i, rowSum W i ≤ 1

/-- **Island** — a region with no neighbours, i.e. a zero row of `W`.

Stated pointwise, so it needs no nonnegativity assumption to be meaningful. Under
`Nonneg` it coincides with the vanishing of the row sum
(`GeoDa.island_iff_rowSum_eq_zero`). -/
def Island (W : WMat n) (i : Fin n) : Prop := ∀ j, W i j = 0

/-- **Zero diagonal:** no region is its own neighbour. This is independent of row
standardization: it is not implied by it (`GeoDa.not_zeroDiag_one`) and does not
imply it (`GeoDaTest.Wnotdiag`). -/
def ZeroDiag (W : WMat n) : Prop := ∀ i, W i i = 0

/-! ### Consequences of the predicates -/

/-- Row sums of a nonnegative matrix are nonnegative. -/
theorem rowSum_nonneg (W : WMat n) (hW : Nonneg W) (i : Fin n) : 0 ≤ rowSum W i := by
  simp only [rowSum]
  exact Finset.sum_nonneg fun j _ => hW i j

/-- Row stochasticity implies row substochasticity. -/
theorem rowSubstochastic_of_rowStochastic (W : WMat n) (h : RowStochastic W) :
    RowSubstochastic W :=
  fun i => le_of_eq (h i)

/-- **`W` is row-stochastic exactly when `W *ᵥ 1 = 1`.** -/
theorem rowStochastic_iff_mulVec_one (W : WMat n) :
    RowStochastic W ↔ W *ᵥ (1 : Vec n) = 1 := by
  constructor
  · intro h
    funext i
    rw [mulVec_one_apply, h i]
    rfl
  · intro h i
    have := congrFun h i
    rw [mulVec_one_apply] at this
    exact this

/-- An island row has vanishing row sum. -/
theorem rowSum_eq_zero_of_island (W : WMat n) {i : Fin n} (h : Island W i) :
    rowSum W i = 0 := by
  simp only [rowSum]
  exact Finset.sum_eq_zero fun j _ => h j

/-- **Islands are exactly the vanishing row sums**, for nonnegative weights.

Without nonnegativity this fails: `!![1, -1; 0, 0]` has a vanishing first row sum
without being a zero row. -/
theorem island_iff_rowSum_eq_zero (W : WMat n) (hW : Nonneg W) (i : Fin n) :
    Island W i ↔ rowSum W i = 0 := by
  refine ⟨rowSum_eq_zero_of_island W, fun h j => ?_⟩
  have hle : W i j ≤ rowSum W i := by
    simp only [rowSum]
    exact Finset.single_le_sum (fun b _ => hW i b) (Finset.mem_univ j)
  rw [h] at hle
  exact le_antisymm hle (hW i j)

/-- **Row-stochastic weights have no islands:** a nonempty row cannot both sum to
`1` and vanish. -/
theorem not_rowStochastic_of_island (W : WMat n) {i : Fin n} (h : Island W i) :
    ¬ RowStochastic W := by
  intro hR
  have h0 : rowSum W i = 0 := rowSum_eq_zero_of_island W h
  have h1 : rowSum W i = 1 := hR i
  exact zero_ne_one (h0 ▸ h1)

/-- Row-stochastic weights have no islands, restated in the direction used by
consumers of `RowStochastic`. -/
theorem not_island_of_rowStochastic (W : WMat n) (h : RowStochastic W) (i : Fin n) :
    ¬ Island W i :=
  fun hi => not_rowStochastic_of_island W hi h

/-- The identity matrix is row-stochastic. Together with
`GeoDa.not_zeroDiag_one` this is the statement that **row standardization does
not force a zero diagonal**. -/
theorem rowStochastic_one : RowStochastic (1 : WMat n) :=
  (rowStochastic_iff_mulVec_one (1 : WMat n)).mpr (one_mulVec (1 : Vec n))

/-- The identity matrix is nonnegative. -/
theorem nonneg_one : Nonneg (1 : WMat n) := by
  intro i j
  rw [Matrix.one_apply]
  split_ifs <;> norm_num

/-- The identity matrix is not zero-diagonal, as soon as there is a region. -/
theorem not_zeroDiag_one (i : Fin n) : ¬ ZeroDiag (1 : WMat n) := by
  intro h
  have hi : (1 : WMat n) i i = 0 := h i
  rw [Matrix.one_apply] at hi
  simp at hi

/-! ### Row normalization -/

/-- **Row normalization:** divide each entry of row `i` by the row sum `∑ j, W i j`.

Islands are handled by the totalized inverse rather than by a side condition:
`(0 : ℝ)⁻¹ = 0`, so a zero row is mapped to a zero row rather than producing an
undefined division by zero. Thus `normalize` is a total function and
`GeoDa.island_normalize` shows islands are preserved. -/
noncomputable def normalize (W : WMat n) : WMat n := fun i j => (rowSum W i)⁻¹ * W i j

/-- Row sums of the normalized matrix. -/
theorem rowSum_normalize (W : WMat n) (i : Fin n) :
    rowSum (normalize W) i = (rowSum W i)⁻¹ * rowSum W i := by
  simp only [rowSum, normalize, Finset.mul_sum]

/-- **Normalization of a row with nonvanishing sum** has row sum `1`. -/
theorem rowStochastic_normalize_of_ne_zero (W : WMat n) {i : Fin n}
    (h : rowSum W i ≠ 0) : rowSum (normalize W) i = 1 := by
  rw [rowSum_normalize, inv_mul_cancel₀ h]

/-- **Islands survive normalization.** -/
theorem island_normalize (W : WMat n) {i : Fin n} (h : Island W i) :
    Island (normalize W) i := by
  intro j
  simp only [normalize, h j, mul_zero]

/-- **Normalization preserves nonnegativity.** -/
theorem nonneg_normalize (W : WMat n) (hW : Nonneg W) : Nonneg (normalize W) := by
  intro i j
  simp only [normalize]
  exact mul_nonneg (inv_nonneg.mpr (rowSum_nonneg W hW i)) (hW i j)

/-- **Normalization preserves a zero diagonal.** -/
theorem zeroDiag_normalize (W : WMat n) (h : ZeroDiag W) : ZeroDiag (normalize W) := by
  intro i
  simp only [normalize, h i, mul_zero]

/-- **Normalization is always row-substochastic**, for every `W`: a row sum of
`(∑ j, W i j)⁻¹ * ∑ j, W i j` is `1` when the row sum does not vanish and `0` for
an island. No nonnegativity hypothesis is needed. -/
theorem rowSubstochastic_normalize (W : WMat n) : RowSubstochastic (normalize W) := by
  intro i
  rw [rowSum_normalize]
  by_cases h : rowSum W i = 0
  · rw [h, inv_zero, zero_mul]
    exact zero_le_one
  · rw [inv_mul_cancel₀ h]

/-- **Row-stochastic normalization.** For nonnegative `W`, the normalized matrix
is row-stochastic exactly when `W` has no island. -/
theorem rowStochastic_normalize_iff (W : WMat n) (hW : Nonneg W) :
    RowStochastic (normalize W) ↔ ∀ i, ¬ Island W i := by
  constructor
  · intro h i hi
    have hz : rowSum W i = 0 := rowSum_eq_zero_of_island W hi
    have h1 : rowSum (normalize W) i = 1 := h i
    rw [rowSum_normalize, hz, inv_zero, zero_mul] at h1
    exact zero_ne_one h1
  · intro h i
    exact rowStochastic_normalize_of_ne_zero W fun hz => h i ((island_iff_rowSum_eq_zero W hW i).mpr hz)

/-- **Row-stochastic normalization, positive-row-sum form:** for nonnegative `W`,
the normalized matrix is row-stochastic exactly when every row sum is positive.
This is the form in which "normalize rows with positive sums" is usually stated. -/
theorem rowStochastic_normalize_iff_pos (W : WMat n) (hW : Nonneg W) :
    RowStochastic (normalize W) ↔ ∀ i, 0 < rowSum W i := by
  rw [rowStochastic_normalize_iff W hW]
  constructor
  · intro h i
    exact lt_of_le_of_ne' (rowSum_nonneg W hW i)
      fun hz => h i ((island_iff_rowSum_eq_zero W hW i).mpr hz)
  · intro h i hi
    exact absurd (rowSum_eq_zero_of_island W hi ▸ h i) (lt_irrefl 0)

end GeoDa
