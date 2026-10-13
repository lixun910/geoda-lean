/-
Copyright (c) 2026 GeoDa-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import GeoDa.Weights

/-!
# GNS nesting with the regressors formed from a design matrix

`GeoDa.GNS` and `GeoDa.Weights` take `Xβ` and `WXθ` as *supplied vectors*: the
arguments `xb` and `wxθ` are named after the terms `Xβ` and `WXθ`, but nothing in
those files multiplies a design matrix by a parameter vector to produce them.
This file closes that gap.

A design matrix `X : Matrix (Fin n) (Fin k) ℝ` with a parameter vector
`β : Fin k → ℝ` and a lagged-regressor coefficient vector `θ : Fin k → ℝ` is
introduced, and the four model equations are restated with

* `Xβ` formed as `X *ᵥ β`, and
* `WXθ` formed as `(W * X) *ᵥ θ`.

Everything else — the weights matrix `W`, the outcome `y`, the latent disturbance
`u`, the innovation `ε` and the coefficients `ρ`, `λ` — is as in `GeoDa.Weights`.

What is (and is not) claimed:

* As in the rest of the project, these are statements about model *equations*,
  not about estimators, probability distributions, identifiability or consistency.
* `X` is an arbitrary real matrix and `W` an arbitrary real square matrix: no
  regularity of the design (full rank, centring, an intercept column) and no
  regularity of the weights (row standardization, symmetry, non-negativity) is
  assumed.
* Nothing here is claimed to be novel. The point of the file is that `Xβ` and
  `WXθ` are now *products* rather than free variables, which is what a numerical
  implementation such as PySAL's `spreg` actually computes.

## Main definitions

* `GeoDa.DMat` : the type of `n × k` real design matrices.
* `GeoDa.GNSDes`, `GeoDa.SARDes`, `GeoDa.SEMDes`, `GeoDa.SDMDes` : the model
  equations with `Xβ` and `WXθ` formed by matrix multiplication.

## Main results

* `GeoDa.design_wxθ_eq` : `W *ᵥ (X *ᵥ θ) = (W * X) *ᵥ θ`, so the definition of the
  lagged-regressor term is the expected one.
* `GeoDa.gnsDes_iff_gnsMat` (and the `sar`/`sem`/`sdm` siblings): each design-matrix
  equation is the corresponding `GeoDa.Weights` equation with `xb := X *ᵥ β` and
  `wxθ := (W * X) *ᵥ θ`.
* `GeoDa.gnsDes_iff_sarDes`, `GeoDa.gnsDes_iff_semDes`, `GeoDa.gnsDes_iff_sdmDes` :
  GNS nests each of the three special cases exactly when the corresponding
  coefficients vanish.
* `GeoDa.sarDes_iff_mulVec`, `GeoDa.semDes_iff_mulVec` : the structural equations as
  linear systems.
* `GeoDa.sarDes_iff_reducedForm`, `GeoDa.semDes_iff_reducedForm` : the reduced forms
  under invertibility of `1 - ρW` resp. `1 - λW`.
* `GeoDa.semDes_reducedForm_eq_sarDes_reducedForm_of_filtered` : the SEM/SAR
  equivalence with spatially filtered regressors.
-/

open scoped Matrix
open Matrix

namespace GeoDa

variable {n k : ℕ}

/-- An `n × k` real design matrix. -/
abbrev DMat (n k : ℕ) := Matrix (Fin n) (Fin k) ℝ

/-- The **general nesting spatial** model with the regressors formed from a design
matrix: `y = ρWy + Xβ + WXθ + u`, `u = λWu + ε`, where `Xβ := X *ᵥ β` and
`WXθ := (W * X) *ᵥ θ`. -/
def GNSDes (W : WMat n) (X : DMat n k) (y : Vec n) (β : Vec k) (θ : Vec k)
    (u ε : Vec n) (ρ lam : ℝ) : Prop :=
  y = ρ • (W *ᵥ y) + X *ᵥ β + (W * X) *ᵥ θ + u ∧ u = lam • (W *ᵥ u) + ε

/-- The **spatial autoregressive** model with a design matrix:
`y = ρWy + Xβ + ε`. -/
def SARDes (W : WMat n) (X : DMat n k) (y : Vec n) (β : Vec k) (ε : Vec n) (ρ : ℝ) : Prop :=
  y = ρ • (W *ᵥ y) + X *ᵥ β + ε

/-- The **spatial error** model with a design matrix, latent disturbance explicit:
`y = Xβ + u`, `u = λWu + ε`. -/
def SEMDes (W : WMat n) (X : DMat n k) (y : Vec n) (β : Vec k) (u ε : Vec n)
    (lam : ℝ) : Prop :=
  y = X *ᵥ β + u ∧ u = lam • (W *ᵥ u) + ε

/-- The **spatial Durbin** model with a design matrix:
`y = ρWy + Xβ + WXθ + ε`. -/
def SDMDes (W : WMat n) (X : DMat n k) (y : Vec n) (β θ : Vec k) (ε : Vec n)
    (ρ : ℝ) : Prop :=
  y = ρ • (W *ᵥ y) + X *ᵥ β + (W * X) *ᵥ θ + ε

/-! ### The lagged-regressor term -/

/-- The lagged-regressor term `WXθ` written as `W *ᵥ (X *ᵥ θ)` — `W` applied to the
fitted values `Xθ` — is the product `(W * X) *ᵥ θ` used in the definitions above. -/
theorem design_wxθ_eq (W : WMat n) (X : DMat n k) (θ : Vec k) :
    W *ᵥ (X *ᵥ θ) = (W * X) *ᵥ θ :=
  mulVec_mulVec θ W X

/-! ### The design-matrix equations are the `GeoDa.Weights` equations -/

/-- `GNSDes` is `GNSMat` with `xb := X *ᵥ β` and `wxθ := (W * X) *ᵥ θ`. -/
theorem gnsDes_iff_gnsMat (W : WMat n) (X : DMat n k) (y u ε : Vec n) (β θ : Vec k)
    (ρ lam : ℝ) :
    GNSDes W X y β θ u ε ρ lam ↔ GNSMat W y (X *ᵥ β) ((W * X) *ᵥ θ) u ε ρ lam :=
  Iff.rfl

/-- `SARDes` is `SARMat` with `xb := X *ᵥ β`. -/
theorem sarDes_iff_sarMat (W : WMat n) (X : DMat n k) (y ε : Vec n) (β : Vec k) (ρ : ℝ) :
    SARDes W X y β ε ρ ↔ SARMat W y (X *ᵥ β) ε ρ :=
  Iff.rfl

/-- `SEMDes` is `SEMMat` with `xb := X *ᵥ β`. -/
theorem semDes_iff_semMat (W : WMat n) (X : DMat n k) (y u ε : Vec n) (β : Vec k) (lam : ℝ) :
    SEMDes W X y β u ε lam ↔ SEMMat W y (X *ᵥ β) u ε lam :=
  Iff.rfl

/-- `SDMDes` is `SDMMat` with `xb := X *ᵥ β` and `wxθ := (W * X) *ᵥ θ`. -/
theorem sdmDes_iff_sdmMat (W : WMat n) (X : DMat n k) (y ε : Vec n) (β θ : Vec k) (ρ : ℝ) :
    SDMDes W X y β θ ε ρ ↔ SDMMat W y (X *ᵥ β) ((W * X) *ᵥ θ) ε ρ :=
  Iff.rfl

/-! ### Nesting -/

/-- GNS with `λ = 0` and `θ = 0` is SAR (with a design matrix), together with the
identity `u = ε` that reconciles the two latent-disturbance conventions. -/
theorem gnsDes_iff_sarDes (W : WMat n) (X : DMat n k) (y u ε : Vec n) (β : Vec k) (ρ : ℝ) :
    GNSDes W X y β 0 u ε ρ 0 ↔ (SARDes W X y β ε ρ ∧ u = ε) := by
  have hwx : (W * X) *ᵥ (0 : Vec k) = (0 : Vec n) := mulVec_zero _
  unfold GNSDes SARDes
  rw [hwx]
  constructor
  · rintro ⟨h, hu⟩
    refine ⟨?_, ?_⟩
    · calc y = ρ • (W *ᵥ y) + X *ᵥ β + 0 + u := h
        _ = ρ • (W *ᵥ y) + X *ᵥ β + ε := by rw [hu]; simp only [zero_smul]; abel
    · rw [hu]; simp only [zero_smul]; abel
  · rintro ⟨h, hu⟩
    refine ⟨?_, ?_⟩
    · calc y = ρ • (W *ᵥ y) + X *ᵥ β + ε := h
        _ = ρ • (W *ᵥ y) + X *ᵥ β + 0 + u := by rw [hu]; abel
    · rw [hu]; simp only [zero_smul]; abel

/-- GNS with `ρ = 0` and `θ = 0` is SEM (with a design matrix). -/
theorem gnsDes_iff_semDes (W : WMat n) (X : DMat n k) (y u ε : Vec n) (β : Vec k) (lam : ℝ) :
    GNSDes W X y β 0 u ε 0 lam ↔ SEMDes W X y β u ε lam := by
  have hwx : (W * X) *ᵥ (0 : Vec k) = (0 : Vec n) := mulVec_zero _
  unfold GNSDes SEMDes
  rw [hwx]
  constructor
  · rintro ⟨h, hu⟩
    refine ⟨?_, hu⟩
    · calc y = (0 : ℝ) • (W *ᵥ y) + X *ᵥ β + 0 + u := h
        _ = X *ᵥ β + u := by simp only [zero_smul]; abel
  · rintro ⟨h, hu⟩
    refine ⟨?_, hu⟩
    · have key : (0 : ℝ) • (W *ᵥ y) + X *ᵥ β + 0 + u = X *ᵥ β + u := by
        simp only [zero_smul]; abel
      exact h.trans key.symm

/-- GNS with `λ = 0` is SDM (with a design matrix), together with `u = ε`. -/
theorem gnsDes_iff_sdmDes (W : WMat n) (X : DMat n k) (y u ε : Vec n) (β θ : Vec k) (ρ : ℝ) :
    GNSDes W X y β θ u ε ρ 0 ↔ (SDMDes W X y β θ ε ρ ∧ u = ε) := by
  unfold GNSDes SDMDes
  constructor
  · rintro ⟨h, hu⟩
    refine ⟨?_, ?_⟩
    · calc y = ρ • (W *ᵥ y) + X *ᵥ β + (W * X) *ᵥ θ + u := h
        _ = ρ • (W *ᵥ y) + X *ᵥ β + (W * X) *ᵥ θ + ε := by
              rw [hu]; simp only [zero_smul]; abel
    · rw [hu]; simp only [zero_smul]; abel
  · rintro ⟨h, hu⟩
    refine ⟨?_, ?_⟩
    · calc y = ρ • (W *ᵥ y) + X *ᵥ β + (W * X) *ᵥ θ + ε := h
        _ = ρ • (W *ᵥ y) + X *ᵥ β + (W * X) *ᵥ θ + u := by rw [hu]
    · rw [hu]; simp only [zero_smul]; abel

/-! ### Structural equation versus linear system -/

/-- The SAR design-matrix equation is equivalent to the linear system
`(1 - ρW) y = Xβ + ε`. -/
theorem sarDes_iff_mulVec (W : WMat n) (X : DMat n k) (y ε : Vec n) (β : Vec k) (ρ : ℝ) :
    SARDes W X y β ε ρ ↔ (1 - ρ • W) *ᵥ y = X *ᵥ β + ε :=
  sarMat_iff_mulVec W y (X *ᵥ β) ε ρ

/-- The SEM design-matrix equation is equivalent to the linear system
`(1 - λW) u = ε` together with `y = Xβ + u`. -/
theorem semDes_iff_mulVec (W : WMat n) (X : DMat n k) (y u ε : Vec n) (β : Vec k) (lam : ℝ) :
    SEMDes W X y β u ε lam ↔ ((1 - lam • W) *ᵥ u = ε ∧ y = X *ᵥ β + u) :=
  semMat_iff_mulVec W y (X *ᵥ β) u ε lam

/-! ### Reduced forms under invertibility -/

/-- **SAR reduced form, design-matrix version.** If `1 - ρW` is invertible then the
SAR equation with regressors `Xβ` holds exactly when `y = (1 - ρW)⁻¹ (Xβ + ε)`. -/
theorem sarDes_iff_reducedForm (W : WMat n) (X : DMat n k) (y ε : Vec n) (β : Vec k)
    (ρ : ℝ) (h : IsUnit (1 - ρ • W)) :
    SARDes W X y β ε ρ ↔ y = (↑(h.unit⁻¹) : WMat n) *ᵥ (X *ᵥ β + ε) :=
  sarMat_iff_reducedForm W y (X *ᵥ β) ε ρ h

/-- **SEM reduced form, design-matrix version.** If `1 - λW` is invertible then the
SEM equation with regressors `Xβ` holds exactly when `u = (1 - λW)⁻¹ ε` and
`y = Xβ + (1 - λW)⁻¹ ε`. -/
theorem semDes_iff_reducedForm (W : WMat n) (X : DMat n k) (y u ε : Vec n) (β : Vec k)
    (lam : ℝ) (h : IsUnit (1 - lam • W)) :
    SEMDes W X y β u ε lam ↔
      (u = (↑(h.unit⁻¹) : WMat n) *ᵥ ε ∧ y = X *ᵥ β + (↑(h.unit⁻¹) : WMat n) *ᵥ ε) :=
  semMat_iff_reducedForm W y (X *ᵥ β) u ε lam h

/-! ### SAR versus SEM -/

/-- **Observational equivalence with filtered regressors, design-matrix version.**
With `B = (1 - λW)⁻¹`, the SEM reduced form with regressors `Xβ` equals the SAR
reduced form whose regressors have been spatially filtered to `(1 - λW)Xβ`. -/
theorem semDes_reducedForm_eq_sarDes_reducedForm_of_filtered
    (W : WMat n) (X : DMat n k) (β : Vec k) (ε : Vec n) (lam : ℝ)
    (h : IsUnit (1 - lam • W)) :
    X *ᵥ β + (↑(h.unit⁻¹) : WMat n) *ᵥ ε
      = (↑(h.unit⁻¹) : WMat n) *ᵥ ((1 - lam • W) *ᵥ (X *ᵥ β) + ε) :=
  sem_reducedForm_eq_sar_reducedForm_of_filtered W (X *ᵥ β) ε lam h

end GeoDa
