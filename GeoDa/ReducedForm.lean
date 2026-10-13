/-
Copyright (c) 2026 GeoDa-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import GeoDa.Design
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Abel

/-!
# The full GNS reduced form

`GeoDa.Design` restates the four model equations with `Xβ := X *ᵥ β` and
`WXθ := (W * X) *ᵥ θ`, and proves the SAR and SEM reduced forms *separately*.
`GeoDa.Weights` does the same for the matrix-valued SAR and SEM.

This file eliminates **both** latent quantities of the general nesting spatial
model at once. Write

```
A = 1 - ρW        B = 1 - λW
```

and suppose `A` and `B` are invertible. Then the GNS system

```
y = ρWy + Xβ + WXθ + u        u = λWu + ε
```

is **equivalent** to the reduced form

```
u = B⁻¹ ε
y = A⁻¹ (Xβ + WXθ + B⁻¹ ε)
```

Preserving *both* equations is the point: the `u` component is not discarded on
the way to `y`, and the theorem is an `↔`, so it also says that any pair `(u, y)`
satisfying the reduced form satisfies the structural GNS system — which is what
makes it legitimate to use the reduced form as *the* model.

Three forms of the invertibility hypothesis are provided, and they are all the
same theorem:

* `gnsDes_iff_reducedForm_of_inverse` takes explicit two-sided inverses `A` and
  `B`. This is the workhorse: it needs no `IsUnit` bookkeeping, and it makes the
  determinant version below a purely algebraic corollary.
* `gnsDes_iff_reducedForm` takes `IsUnit (1 - ρ • W)` and `IsUnit (1 - λ • W)`,
  matching the convention already used in `GeoDa.Weights`.
* `gnsDes_iff_reducedForm_of_det_ne_zero` takes `det (1 - ρ • W) ≠ 0` and
  `det (1 - λ • W) ≠ 0`, via `isUnit_iff_det_ne_zero`. This is the hypothesis an
  implementation actually checks.

The specialisation to SDM (`λ = 0`, so `B = 1` and `u = ε`) is given as
`sdmDes_iff_reducedForm`; the design-matrix SAR and SEM reduced forms are already
in `GeoDa.Design`.

What is (and is not) claimed:

* As everywhere in this project, these are statements about model *equations*.
  Nothing here establishes identifiability, estimator consistency, asymptotic
  distribution theory or numerical correctness.
* The invertibility hypothesis is *stated*, not derived. Showing that `1 - ρW`
  is in fact invertible for `|ρ| < 1` under a row-standardization hypothesis is a
  different (and open) problem — see the "Next steps" in `README.md`.
* No regularity of `W` (row standardization, symmetry, nonnegativity) and no
  regularity of `X` (full rank, centring, an intercept) is assumed.
-/

open scoped Matrix
open Matrix

namespace GeoDa

variable {n k : ℕ}

/-! ### Two elementary reductions -/

/-- The linear system `(1 - cW) *ᵥ v = w` is the structural equation
`v = c • (W *ᵥ v) + w`. This is the step that turns a model equation into a
matrix equation, and hence into a reduced form. -/
theorem one_sub_smul_mulVec_eq_iff (W : WMat n) (c : ℝ) (v w : Vec n) :
    (1 - c • W) *ᵥ v = w ↔ v = c • (W *ᵥ v) + w := by
  rw [one_sub_smul_mulVec, sub_eq_iff_eq_add]
  constructor
  · intro h
    calc v = w + c • (W *ᵥ v) := h
      _ = c • (W *ᵥ v) + w := add_comm _ _
  · intro h
    calc v = c • (W *ᵥ v) + w := h
      _ = w + c • (W *ᵥ v) := add_comm _ _

/-- **Left inverse solves the system.** If `A * M = 1`, then any solution of
`M *ᵥ v = w` is `A *ᵥ w`, so the solution is unique. -/
theorem mulVec_eq_of_mulVec_eq {M A : WMat n} (h : A * M = 1) {v w : Vec n}
    (hmv : M *ᵥ v = w) : v = A *ᵥ w := by
  have h1 : A *ᵥ (M *ᵥ v) = A *ᵥ w := by rw [hmv]
  rwa [mulVec_mulVec, h, one_mulVec] at h1

/-- **Right inverse checks the solution.** If `M * A = 1`, then `A *ᵥ w` does
solve `M *ᵥ v = w`. -/
theorem mulVec_eq_of_eq_mulVec {M A : WMat n} (h : M * A = 1) {v w : Vec n}
    (hv : v = A *ᵥ w) : M *ᵥ v = w := by
  rw [hv, mulVec_mulVec, h, one_mulVec]

/-- **Invertible system.** With `A` a two-sided inverse of `M`, the system
`M *ᵥ v = w` has the unique solution `v = A *ᵥ w`. -/
theorem mulVec_eq_iff {M A : WMat n} (hL : A * M = 1) (hR : M * A = 1) (v w : Vec n) :
    M *ᵥ v = w ↔ v = A *ᵥ w :=
  ⟨mulVec_eq_of_mulVec_eq hL, mulVec_eq_of_eq_mulVec hR⟩

/-! ### GNS as a linear system -/

/-- **The GNS system as a pair of linear systems.** GNS holds exactly when
`(1 - ρW) y = Xβ + WXθ + u` and `(1 - λW) u = ε`. Both equations are kept. -/
theorem gnsDes_iff_mulVec (W : WMat n) (X : DMat n k) (y : Vec n) (β θ : Vec k)
    (u ε : Vec n) (ρ lam : ℝ) :
    GNSDes W X y β θ u ε ρ lam ↔
      ((1 - ρ • W) *ᵥ y = X *ᵥ β + (W * X) *ᵥ θ + u ∧ (1 - lam • W) *ᵥ u = ε) := by
  unfold GNSDes
  constructor
  · rintro ⟨hy, hu⟩
    exact ⟨(one_sub_smul_mulVec_eq_iff W ρ y _).mpr (by
             calc y = ρ • (W *ᵥ y) + X *ᵥ β + (W * X) *ᵥ θ + u := hy
               _ = ρ • (W *ᵥ y) + (X *ᵥ β + (W * X) *ᵥ θ + u) := by abel),
           (one_sub_smul_mulVec_eq_iff W lam u ε).mpr hu⟩
  · rintro ⟨hy, hu⟩
    refine ⟨?_, (one_sub_smul_mulVec_eq_iff W lam u ε).mp hu⟩
    have := (one_sub_smul_mulVec_eq_iff W ρ y (X *ᵥ β + (W * X) *ᵥ θ + u)).mp hy
    calc y = ρ • (W *ᵥ y) + (X *ᵥ β + (W * X) *ᵥ θ + u) := this
      _ = ρ • (W *ᵥ y) + X *ᵥ β + (W * X) *ᵥ θ + u := by abel

/-! ### The full reduced form -/

/-- **Full GNS reduced form, explicit-inverse form.** If `A` and `B` are
two-sided inverses of `1 - ρW` and `1 - λW`, then the GNS system holds exactly
when the latent disturbance and the outcome are given by the reduced form
`u = Bε` and `y = A(Xβ + WXθ + Bε)` — with `A` and `B` the inverses, so that
writing `A = (1 - ρW)⁻¹` and `B = (1 - λW)⁻¹` gives the usual statement.

Taking the inverses as hypotheses rather than as `IsUnit` data is what makes the
determinant version below immediate. -/
theorem gnsDes_iff_reducedForm_of_inverse (W : WMat n) (X : DMat n k) (y : Vec n)
    (β θ : Vec k) (u ε : Vec n) (ρ lam : ℝ) (A B : WMat n)
    (hAL : A * (1 - ρ • W) = 1) (hAR : (1 - ρ • W) * A = 1)
    (hBL : B * (1 - lam • W) = 1) (hBR : (1 - lam • W) * B = 1) :
    GNSDes W X y β θ u ε ρ lam ↔
      (u = B *ᵥ ε ∧ y = A *ᵥ (X *ᵥ β + (W * X) *ᵥ θ + B *ᵥ ε)) := by
  rw [gnsDes_iff_mulVec]
  constructor
  · rintro ⟨hy, hu⟩
    have hu' : u = B *ᵥ ε := mulVec_eq_of_mulVec_eq hBL hu
    refine ⟨hu', ?_⟩
    rw [hu'] at hy
    exact mulVec_eq_of_mulVec_eq hAL hy
  · rintro ⟨hu, hy⟩
    exact ⟨mulVec_eq_of_eq_mulVec hAR (by rw [hy, ← hu]),
           mulVec_eq_of_eq_mulVec hBR hu⟩

/-- **Forward direction.** If the GNS system holds and `A`, `B` invert
`1 - ρW`, `1 - λW`, then `u` and `y` are given by the reduced form. Kept as a
separate name because the issue that prompted this file asks for the two
implications explicitly; it is the `mp` half of `gnsDes_iff_reducedForm`. -/
theorem gnsDes_reducedForm (W : WMat n) (X : DMat n k) (y : Vec n) (β θ : Vec k)
    (u ε : Vec n) (ρ lam : ℝ) {A B : WMat n}
    (hAL : A * (1 - ρ • W) = 1) (hAR : (1 - ρ • W) * A = 1)
    (hBL : B * (1 - lam • W) = 1) (hBR : (1 - lam • W) * B = 1)
    (h : GNSDes W X y β θ u ε ρ lam) :
    u = B *ᵥ ε ∧ y = A *ᵥ (X *ᵥ β + (W * X) *ᵥ θ + B *ᵥ ε) :=
  (gnsDes_iff_reducedForm_of_inverse W X y β θ u ε ρ lam A B hAL hAR hBL hBR).mp h

/-- **Reverse direction.** Conversely, any `(u, y)` satisfying the reduced form
satisfies the structural GNS system. This is the direction that is *not* merely
"solve the equation": it says the reduced form has not thrown any solution away
or added any. -/
theorem reducedForm_gnsDes (W : WMat n) (X : DMat n k) (y : Vec n) (β θ : Vec k)
    (u ε : Vec n) (ρ lam : ℝ) {A B : WMat n}
    (hAL : A * (1 - ρ • W) = 1) (hAR : (1 - ρ • W) * A = 1)
    (hBL : B * (1 - lam • W) = 1) (hBR : (1 - lam • W) * B = 1)
    (h : u = B *ᵥ ε ∧ y = A *ᵥ (X *ᵥ β + (W * X) *ᵥ θ + B *ᵥ ε)) :
    GNSDes W X y β θ u ε ρ lam :=
  (gnsDes_iff_reducedForm_of_inverse W X y β θ u ε ρ lam A B hAL hAR hBL hBR).mpr h

/-- **Full GNS reduced form.** `IsUnit` form, matching the convention of
`GeoDa.Weights`: with `1 - ρW` and `1 - λW` invertible, GNS holds exactly when
`u = B⁻¹ ε` and `y = A⁻¹ (Xβ + WXθ + B⁻¹ ε)`, where the inverses are the unit
inverses of the `IsUnit` proofs. -/
theorem gnsDes_iff_reducedForm (W : WMat n) (X : DMat n k) (y : Vec n) (β θ : Vec k)
    (u ε : Vec n) (ρ lam : ℝ) (hA : IsUnit (1 - ρ • W)) (hB : IsUnit (1 - lam • W)) :
    GNSDes W X y β θ u ε ρ lam ↔
      (u = (↑(hB.unit⁻¹) : WMat n) *ᵥ ε ∧
       y = (↑(hA.unit⁻¹) : WMat n) *ᵥ
             (X *ᵥ β + (W * X) *ᵥ θ + (↑(hB.unit⁻¹) : WMat n) *ᵥ ε)) :=
  gnsDes_iff_reducedForm_of_inverse W X y β θ u ε ρ lam
    (↑(hA.unit⁻¹) : WMat n) (↑(hB.unit⁻¹) : WMat n)
    (by simpa only [hA.unit_spec] using Units.inv_mul hA.unit)
    (by simpa only [hA.unit_spec] using Units.mul_inv hA.unit)
    (by simpa only [hB.unit_spec] using Units.inv_mul hB.unit)
    (by simpa only [hB.unit_spec] using Units.mul_inv hB.unit)

/-! ### Determinant form of the hypothesis -/

/-- `IsUnit` for a square real matrix is exactly nonvanishing of the
determinant. This is the bridge from the `IsUnit` hypotheses used above to the
hypothesis `det ≠ 0` that an implementation actually tests. -/
theorem isUnit_iff_det_ne_zero (M : WMat n) : IsUnit M ↔ M.det ≠ 0 :=
  (Matrix.isUnit_iff_isUnit_det M).trans isUnit_iff_ne_zero

/-- **Full GNS reduced form, determinant form.** The same theorem as
`gnsDes_iff_reducedForm`, with the invertibility hypothesis written as
`det ≠ 0` and the inverses written with `⁻¹`. -/
theorem gnsDes_iff_reducedForm_of_det_ne_zero (W : WMat n) (X : DMat n k) (y : Vec n)
    (β θ : Vec k) (u ε : Vec n) (ρ lam : ℝ)
    (hA : (1 - ρ • W).det ≠ 0) (hB : (1 - lam • W).det ≠ 0) :
    GNSDes W X y β θ u ε ρ lam ↔
      (u = ((1 - lam • W)⁻¹ : WMat n) *ᵥ ε ∧
       y = ((1 - ρ • W)⁻¹ : WMat n) *ᵥ
             (X *ᵥ β + (W * X) *ᵥ θ + ((1 - lam • W)⁻¹ : WMat n) *ᵥ ε)) :=
  gnsDes_iff_reducedForm_of_inverse W X y β θ u ε ρ lam _ _
    (nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hA))
    (mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hA))
    (nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hB))
    (mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hB))

/-! ### The SDM restriction -/

/-- **The SDM system as a linear system.** SDM holds exactly when
`(1 - ρW) y = Xβ + WXθ + ε`. (`GeoDa.Design` has the SAR and SEM versions.) -/
theorem sdmDes_iff_mulVec (W : WMat n) (X : DMat n k) (y ε : Vec n) (β θ : Vec k)
    (ρ : ℝ) :
    SDMDes W X y β θ ε ρ ↔ (1 - ρ • W) *ᵥ y = X *ᵥ β + (W * X) *ᵥ θ + ε := by
  unfold SDMDes
  rw [one_sub_smul_mulVec, sub_eq_iff_eq_add]
  constructor
  · intro h
    calc y = ρ • (W *ᵥ y) + X *ᵥ β + (W * X) *ᵥ θ + ε := h
      _ = X *ᵥ β + (W * X) *ᵥ θ + ε + ρ • (W *ᵥ y) := by abel
  · intro h
    calc y = X *ᵥ β + (W * X) *ᵥ θ + ε + ρ • (W *ᵥ y) := h
      _ = ρ • (W *ᵥ y) + X *ᵥ β + (W * X) *ᵥ θ + ε := by abel

/-- **SDM reduced form.** SDM is GNS with `λ = 0`, for which `B = 1 - 0 • W = 1`
and hence `u = ε`: the reduced form collapses to
`y = (1 - ρW)⁻¹ (Xβ + WXθ + ε)`. This is the `λ = 0` restriction of
`gnsDes_iff_reducedForm`. -/
theorem sdmDes_iff_reducedForm (W : WMat n) (X : DMat n k) (y ε : Vec n) (β θ : Vec k)
    (ρ : ℝ) (hA : IsUnit (1 - ρ • W)) :
    SDMDes W X y β θ ε ρ ↔
      y = (↑(hA.unit⁻¹) : WMat n) *ᵥ (X *ᵥ β + (W * X) *ᵥ θ + ε) := by
  rw [sdmDes_iff_mulVec]
  exact mulVec_eq_iff
    (by simpa only [hA.unit_spec] using Units.inv_mul hA.unit)
    (by simpa only [hA.unit_spec] using Units.mul_inv hA.unit) y _

end GeoDa
