/-
Copyright (c) 2026 GeoDa-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import GeoDa.SpatialWeights
import GeoDa.ReducedForm
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Invertibility of the spatial multiplier `1 - ρW`

Every reduced form in this repository — `GeoDa.Weights`, `GeoDa.Design`,
`GeoDa.ReducedForm` — carries an invertibility hypothesis on `1 - ρW` and
`1 - λW`, taken as `IsUnit` or as a nonvanishing determinant. Those are *stated*,
never derived, so they say nothing about which weights actually satisfy them.
This file derives the hypothesis from the weights themselves.

The argument is the classical one. For a **nonnegative row-substochastic** matrix
`W` — every entry `≥ 0`, every row summing to at most `1`, islands included —
applying `W` to a vector cannot increase its `ℓ∞` norm:

```
‖W *ᵥ v‖ ≤ ‖v‖
```

because row `i` contributes `∑ j, W i j * ‖v j‖ ≤ (∑ j, W i j) * ‖v‖ ≤ ‖v‖`. Hence
`‖ρ • W‖ ≤ |ρ| · 1 < 1` whenever `|ρ| < 1`, and `1 - ρW` is a spatial multiplier in
the Neumann sense. Rather than invoking a general Neumann-series criterion, the
proof below is finite-dimensional and elementary: `1 - ρW` is shown to be
*injective*, and injective endomorphisms of a finite-dimensional space are units.
Concretely, `(1 - ρW)v = 0` gives `v = ρ • (Wv)`, hence `‖v‖ ≤ |ρ| ‖v‖`, which
forces `‖v‖ = 0` since `|ρ| < 1`.

## Main results

* `GeoDa.abs_mulVec_apply_le_norm` : `|(W *ᵥ v) i| ≤ ‖v‖`.
* `GeoDa.norm_mulVec_le` : **`W` is an `ℓ∞` contraction**, `‖W *ᵥ v‖ ≤ ‖v‖`.
* `GeoDa.mulVec_injective_one_sub_smul` : for `|ρ| < 1`, `1 - ρW` is injective.
* `GeoDa.isUnit_one_sub_smul_of_rowSubstochastic` : **`|ρ| < 1` gives
  `IsUnit (1 - ρ • W)`**, with the weights assumptions explicit. The same
  statement is used unchanged for the spatial-error parameter `λ`; there is
  nothing specific to `ρ` in the proof.
* `GeoDa.isUnit_one_sub_smul_of_rowStochastic` : the row-stochastic special case.
* `GeoDa.sarMat_iff_reducedForm_of_rowSubstochastic`,
  `GeoDa.semMat_iff_reducedForm_of_rowSubstochastic` : the SAR and SEM reduced
  forms with `IsUnit` replaced throughout by the weights hypotheses and
  `|ρ| < 1`. These are the "bridge" to the existing reduced-form theorems.

## What is (and is not) claimed

* The hypotheses are **not** decorative, and the tests in `GeoDaTest/Smoke.lean`
  show both are needed: `2 • 1` is nonnegative with row sums `2`, and
  `1 - (1/2) • (2 • 1) = 0` is not invertible; and `!![2, -1; 0, 0]` is
  row-substochastic with a negative entry, and `1 - (1/2) • …` is singular. So
  neither nonnegativity nor row-substochasticity can be dropped.
* This is a statement about the *weights matrix*. It is not a claim about
  estimators, identifiability or asymptotics, and it is not novel: the
  contraction estimate is textbook.
* No regularity of `W` beyond nonnegativity and row-substochasticity is assumed —
  in particular **not symmetry, and not a zero diagonal**, and islands are
  allowed.
-/

open scoped Matrix
open Matrix

namespace GeoDa

variable {n : ℕ}

/-! ### `W` is an `ℓ∞` contraction -/

/-- **Coordinate bound.** For nonnegative row-substochastic weights, every entry
of `W *ᵥ v` is bounded by the `ℓ∞` norm of `v`. -/
theorem abs_mulVec_apply_le_norm (W : WMat n) (hW : Nonneg W) (h1 : RowSubstochastic W)
    (v : Vec n) (i : Fin n) : |(W *ᵥ v) i| ≤ ‖v‖ := by
  rw [Matrix.mulVec_apply_eq_sum]
  calc |∑ j, W i j * v j|
      ≤ ∑ j, |W i j * v j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, W i j * |v j| := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [abs_mul, abs_of_nonneg (hW i j)]
    _ ≤ ∑ j, W i j * ‖v‖ :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (norm_le_pi_norm v j) (hW i j)
    _ = (∑ j, W i j) * ‖v‖ := (Finset.sum_mul _ _ _).symm
    _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right (by simpa only [rowSum] using h1 i) (norm_nonneg v)
    _ = ‖v‖ := one_mul _

/-- **`W` is a contraction for the `ℓ∞` norm of vectors.** This is the row-sum
estimate `‖W‖∞ ≤ 1` of the spatial-weights literature, stated on vectors so that
no matrix norm is needed. -/
theorem norm_mulVec_le (W : WMat n) (hW : Nonneg W) (h1 : RowSubstochastic W) (v : Vec n) :
    ‖W *ᵥ v‖ ≤ ‖v‖ := by
  rcases isEmpty_or_nonempty (Fin n) with h | h
  · have hv : v = 0 := funext fun i => (h.false i).elim
    rw [hv, Matrix.mulVec_zero]
  · exact (pi_norm_le_iff_of_nonempty (W *ᵥ v)).mpr fun i =>
      by simpa only [Real.norm_eq_abs] using abs_mulVec_apply_le_norm W hW h1 v i

/-! ### Invertibility of the spatial multiplier -/

/-- **`1 - ρW` is injective for `|ρ| < 1`.** If `(1 - ρW) v = 0` then
`v = ρ • (W v)`, so `‖v‖ ≤ |ρ| ‖v‖`, which forces `‖v‖ = 0`. -/
theorem mulVec_injective_one_sub_smul (W : WMat n) (hW : Nonneg W) (h1 : RowSubstochastic W)
    (ρ : ℝ) (hρ : |ρ| < 1) : Function.Injective ((1 - ρ • W).mulVec) := by
  intro u v huv
  have hz : (1 - ρ • W) *ᵥ (u - v) = 0 := by rw [mulVec_sub, huv, sub_self]
  have hw : u - v = ρ • (W *ᵥ (u - v)) := by
    have h := hz
    rw [one_sub_smul_mulVec, sub_eq_zero] at h
    exact h
  have hM : ‖u - v‖ ≤ |ρ| * ‖u - v‖ := by
    calc ‖u - v‖ = ‖ρ • (W *ᵥ (u - v))‖ := congrArg norm hw
      _ = |ρ| * ‖W *ᵥ (u - v)‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ |ρ| * ‖u - v‖ := mul_le_mul_of_nonneg_left (norm_mulVec_le W hW h1 _) (abs_nonneg ρ)
  have hnorm : ‖u - v‖ = 0 := by
    by_contra hne
    have hpos : 0 < ‖u - v‖ := lt_of_le_of_ne' (norm_nonneg _) hne
    have hlt : ‖u - v‖ < ‖u - v‖ :=
      calc ‖u - v‖ ≤ |ρ| * ‖u - v‖ := hM
        _ < 1 * ‖u - v‖ := mul_lt_mul_of_pos_right hρ hpos
        _ = ‖u - v‖ := one_mul _
    exact lt_irrefl _ hlt
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- **The spatial multiplier under concrete weights assumptions.** For nonnegative
row-substochastic `W` and `|ρ| < 1`, the multiplier `1 - ρW` is invertible. No
`IsUnit` hypothesis is assumed: it is derived.

The proof is unchanged if `ρ` is read as the spatial-error parameter `λ`; there is
nothing `ρ`-specific about it. -/
theorem isUnit_one_sub_smul_of_rowSubstochastic (W : WMat n) (hW : Nonneg W)
    (h1 : RowSubstochastic W) (ρ : ℝ) (hρ : |ρ| < 1) : IsUnit (1 - ρ • W) :=
  (Matrix.mulVec_injective_iff_isUnit).mp (mulVec_injective_one_sub_smul W hW h1 ρ hρ)

/-- Row-stochastic weights are row-substochastic, so the multiplier is invertible
there too. -/
theorem isUnit_one_sub_smul_of_rowStochastic (W : WMat n) (hW : Nonneg W)
    (h1 : RowStochastic W) (ρ : ℝ) (hρ : |ρ| < 1) : IsUnit (1 - ρ • W) :=
  isUnit_one_sub_smul_of_rowSubstochastic W hW (rowSubstochastic_of_rowStochastic W h1) ρ hρ

/-! ### Bridges to the reduced-form theorems -/

/-- **SAR reduced form under weights assumptions.** With nonnegative
row-substochastic `W` and `|ρ| < 1`, `1 - ρW` is invertible and the SAR equation
holds exactly when `y = (1 - ρW)⁻¹ (Xβ + ε)`. The invertibility hypothesis of
`GeoDa.sarMat_iff_reducedForm` is discharged, not assumed. -/
theorem sarMat_iff_reducedForm_of_rowSubstochastic (W : WMat n) (hW : Nonneg W)
    (h1 : RowSubstochastic W) (ρ : ℝ) (hρ : |ρ| < 1) (y xb ε : Vec n) :
    SARMat W y xb ε ρ ↔ y = ((1 - ρ • W)⁻¹ : WMat n) *ᵥ (xb + ε) := by
  have hdet : IsUnit (1 - ρ • W).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_one_sub_smul_of_rowSubstochastic W hW h1 ρ hρ)
  rw [sarMat_iff_mulVec]
  exact mulVec_eq_iff (nonsing_inv_mul _ hdet) (mul_nonsing_inv _ hdet) y (xb + ε)

/-- **SEM reduced form under weights assumptions.** With nonnegative
row-substochastic `W` and `|λ| < 1`, `1 - λW` is invertible and the SEM equation
holds exactly when `u = (1 - λW)⁻¹ ε` and `y = Xβ + (1 - λW)⁻¹ ε`. -/
theorem semMat_iff_reducedForm_of_rowSubstochastic (W : WMat n) (hW : Nonneg W)
    (h1 : RowSubstochastic W) (lam : ℝ) (hlam : |lam| < 1) (y xb u ε : Vec n) :
    SEMMat W y xb u ε lam ↔
      (u = ((1 - lam • W)⁻¹ : WMat n) *ᵥ ε ∧ y = xb + ((1 - lam • W)⁻¹ : WMat n) *ᵥ ε) := by
  have hdet : IsUnit (1 - lam • W).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp
      (isUnit_one_sub_smul_of_rowSubstochastic W hW h1 lam hlam)
  have hL : ((1 - lam • W)⁻¹ : WMat n) * (1 - lam • W) = 1 := nonsing_inv_mul _ hdet
  have hR : (1 - lam • W) * ((1 - lam • W)⁻¹ : WMat n) = 1 := mul_nonsing_inv _ hdet
  rw [semMat_iff_mulVec]
  constructor
  · rintro ⟨hu, hy⟩
    have hu' : u = ((1 - lam • W)⁻¹ : WMat n) *ᵥ ε := mulVec_eq_of_mulVec_eq hL hu
    exact ⟨hu', by rw [hy, hu']⟩
  · rintro ⟨hu, hy⟩
    exact ⟨mulVec_eq_of_eq_mulVec hR hu, by rw [hy, ← hu]⟩

/-! ### Column-substochastic weights, and the transposed multiplier

`GeoDa.RowSubstochastic` is the hypothesis that makes `W` an `ℓ∞` contraction and so
makes `1 - ρW` invertible. The dual normalization — **column** sums at most one, as in a
column-standardized weights matrix — is a different condition, and it does not make `W`
itself an `ℓ∞` contraction. What it makes an `ℓ∞` contraction is `Wᵀ`.
Both multipliers are invertible, since transposition preserves invertibility.

The transposed multiplier is not an ornamental case: it is the one that appears on the
right of `Cov(Aξ) = A Cov(ξ) Aᵀ` in `GeoDa.RandomVector`. So it is worth having, and it
comes out of the row-substochastic theorem by transposition rather than by repeating the
`ℓ∞` estimate for columns. -/

/-- The sum of the entries of column `j`. -/
def colSum (W : WMat n) (j : Fin n) : ℝ := ∑ i, W i j

/-- **Column substochasticity:** every column sums to at most `1`. -/
def ColSubstochastic (W : WMat n) : Prop := ∀ j, colSum W j ≤ 1

/-- The row sums of the transpose are the column sums of the original. -/
theorem rowSum_transpose (W : WMat n) (j : Fin n) : rowSum Wᵀ j = colSum W j := rfl

/-- **The transposed multiplier is invertible.** For nonnegative column-substochastic
`W` and `|ρ| < 1`, `1 - ρ • Wᵀ` is a unit.

Proved by transposition: `Wᵀ` is nonnegative and row-substochastic, so
`isUnit_one_sub_smul_of_rowSubstochastic` applies to it unchanged. Repeating the `ℓ∞`
estimate here would prove the same theorem twice. -/
theorem isUnit_one_sub_smul_transpose_of_colSubstochastic (W : WMat n) (hW : Nonneg W)
    (h1 : ColSubstochastic W) (ρ : ℝ) (hρ : |ρ| < 1) : IsUnit (1 - ρ • Wᵀ) :=
  isUnit_one_sub_smul_of_rowSubstochastic Wᵀ (fun i j => hW j i) (fun i => h1 i) ρ hρ

/-- The original multiplier is also invertible under nonnegative column bounds.
This does not assert that `W` is an infinity-norm contraction. -/
theorem isUnit_one_sub_smul_of_colSubstochastic (W : WMat n) (hW : Nonneg W)
    (h1 : ColSubstochastic W) (ρ : ℝ) (hρ : |ρ| < 1) : IsUnit (1 - ρ • W) := by
  have ht : IsUnit ((1 - ρ • W)ᵀ) := by
    simpa only [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul] using
      isUnit_one_sub_smul_transpose_of_colSubstochastic W hW h1 ρ hρ
  have hd := (Matrix.isUnit_iff_isUnit_det _).mp ht
  rw [Matrix.det_transpose] at hd
  exact (Matrix.isUnit_iff_isUnit_det _).mpr hd

end GeoDa
