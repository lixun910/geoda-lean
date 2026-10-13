/-
Copyright (c) 2026 GeoDa-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import GeoDa.Multiplier
import GeoDa.Nesting
import GeoDa.RandomVector
import GeoDa.ReducedForm

/-!
# The spatial Durbin error model (SDEM)

```
y = Xβ + WXθ + u        u = λWu + ε
```

a spatial lag of the *regressors* together with a spatially autocorrelated disturbance,
and no lag of `y`. It is the model of LeSage and Pace's *Introduction to Spatial
Econometrics* (2009); LeSage (2014) singles it out, with the SDM, as one of the two
specifications he thinks applied work should consider, and Halleck Vega and Elhorst (2015)
place it in the SLX/SDEM/SDM/GNS group whose spillovers are *flexible* across regressors —
as against SAR and SEM, whose spillovers are proportional to the direct effect or zero by
construction.

**This file is the benchmark model of the P4.2 research pilot.** It is a *reproduction*: the
model, its nesting relations and its reduced form are published results, and the point of
formalizing them here is that there is a reference to be wrong against. See
`docs/research-note-sdem.md` for the prior art, the fidelity check against the published
statements, and the record of what this took.

## Why it is a good benchmark

* It is **expressible in what is already here** — `GNSDes W X y β θ u ε 0 lam` — so the task
  is naming, nesting and a reduced form rather than new algebra. It reuses `GeoDa.SLXDes`
  and `GeoDa.SEMDes` and proves things *about* them.
* It has **published nesting claims to check against**: SDEM with `λ = 0` is SLX, and SDEM
  with `θ = 0` is SEM. Both are stated by LeSage (2014) and both are proved below, which is
  the closest this pilot gets to a semantic-fidelity check.
* It has a **reference implementation**: `spreg.dgp.dgp_slxerror` in PySAL computes exactly
  this DGP, so the numerical cross-check in `validation/test_sdem.py` compares against
  somebody else's code rather than only against ours.

## Main results

* `GeoDa.gnsDes_iff_sdemDes` : GNS with `ρ = 0` is SDEM.
* `GeoDa.sdemDes_iff_slx_and_error` : SDEM *is* SLX with a spatial error — definitionally.
* `GeoDa.sdemDes_iff_slxDes_of_lam_zero`, `GeoDa.sdemDes_iff_semDes_of_theta_zero` : the two
  published nestings.
* `GeoDa.sdemDes_iff_reducedForm` and `..._of_rowSubstochastic` : the reduced form
  `y = Xβ + WXθ + (1 - λW)⁻¹ε`.
* `GeoDa.sdem_moments` : the mean and covariance, from `GeoDa.sem_moments`.

As everywhere in this repository, these are statements about model *equations*. Nothing
here identifies a parameter, validates an estimator, or says anything about inference.
-/

open scoped Matrix
open Matrix

namespace GeoDa

variable {n k : ℕ}

/-- The **spatial Durbin error model**: `y = Xβ + WXθ + u`, `u = λWu + ε`.

The lagged-regressor term is `(W * X) *ᵥ θ`, as everywhere else here. Unlike SDM there is no
`ρWy` term, and unlike SLX the disturbance is spatially autocorrelated. -/
def SDEMDes (W : WMat n) (X : DMat n k) (y : Vec n) (β θ : Vec k) (u ε : Vec n)
    (lam : ℝ) : Prop :=
  y = X *ᵥ β + (W * X) *ᵥ θ + u ∧ u = lam • (W *ᵥ u) + ε

/-! ### Nesting -/

/-- **GNS with `ρ = 0` is SDEM.** Switching off only the lag of the dependent variable leaves
the lagged regressors and the spatial error, which is SDEM exactly. -/
theorem gnsDes_iff_sdemDes (W : WMat n) (X : DMat n k) (y u ε : Vec n) (β θ : Vec k)
    (lam : ℝ) :
    GNSDes W X y β θ u ε 0 lam ↔ SDEMDes W X y β θ u ε lam := by
  unfold GNSDes SDEMDes
  constructor
  · rintro ⟨h, hu⟩
    refine ⟨?_, hu⟩
    · calc y = (0 : ℝ) • (W *ᵥ y) + X *ᵥ β + (W * X) *ᵥ θ + u := h
        _ = X *ᵥ β + (W * X) *ᵥ θ + u := by simp only [zero_smul]; abel
  · rintro ⟨h, hu⟩
    refine ⟨?_, hu⟩
    · have key : (0 : ℝ) • (W *ᵥ y) + X *ᵥ β + (W * X) *ᵥ θ + u
          = X *ᵥ β + (W * X) *ᵥ θ + u := by
        simp only [zero_smul]; abel
      exact h.trans key.symm

/-- **SDEM is SLX with a spatial error** — and this one is definitional, `Iff.rfl`: the
`y`-equation of SDEM is literally `SLXDes` with the disturbance left named `u`.
LeSage (2014) puts it as "SDEM subsumes SLX"; here the two differ by one equation. -/
theorem sdemDes_iff_slx_and_error (W : WMat n) (X : DMat n k) (y u ε : Vec n) (β θ : Vec k)
    (lam : ℝ) :
    SDEMDes W X y β θ u ε lam ↔ (SLXDes W X y β θ u ∧ u = lam • (W *ᵥ u) + ε) :=
  Iff.rfl

/-- **SDEM with `λ = 0` is SLX.** With no autocorrelation in the disturbance, `u = ε` and
what remains is the regressors and their spatial lag. -/
theorem sdemDes_iff_slxDes_of_lam_zero (W : WMat n) (X : DMat n k) (y u ε : Vec n)
    (β θ : Vec k) :
    SDEMDes W X y β θ u ε 0 ↔ (SLXDes W X y β θ ε ∧ u = ε) := by
  unfold SDEMDes
  constructor
  · rintro ⟨h, hu⟩
    refine ⟨?_, ?_⟩
    · calc y = X *ᵥ β + (W * X) *ᵥ θ + u := h
        _ = X *ᵥ β + (W * X) *ᵥ θ + ε := by rw [hu]; simp only [zero_smul]; abel
    · rw [hu]; simp only [zero_smul]; abel
  · rintro ⟨h, hu⟩
    refine ⟨?_, ?_⟩
    · calc y = X *ᵥ β + (W * X) *ᵥ θ + ε := h
        _ = X *ᵥ β + (W * X) *ᵥ θ + u := by rw [hu]
    · rw [hu]; simp only [zero_smul]; abel

/-- **SDEM with `θ = 0` is SEM.** Dropping the lagged regressors leaves the spatial error
model. -/
theorem sdemDes_iff_semDes_of_theta_zero (W : WMat n) (X : DMat n k) (y u ε : Vec n) (β : Vec k)
    (lam : ℝ) :
    SDEMDes W X y β 0 u ε lam ↔ SEMDes W X y β u ε lam := by
  unfold SDEMDes SEMDes
  constructor
  · rintro ⟨h, hu⟩
    refine ⟨?_, hu⟩
    · calc y = X *ᵥ β + (W * X) *ᵥ (0 : Vec k) + u := h
        _ = X *ᵥ β + u := by rw [Matrix.mulVec_zero]; abel
  · rintro ⟨h, hu⟩
    refine ⟨?_, hu⟩
    · calc y = X *ᵥ β + u := h
        _ = X *ᵥ β + (W * X) *ᵥ (0 : Vec k) + u := by rw [Matrix.mulVec_zero]; abel

/-! ### Linear system and reduced form -/

/-- The SDEM equations as a linear system. -/
theorem sdemDes_iff_mulVec (W : WMat n) (X : DMat n k) (y u ε : Vec n) (β θ : Vec k)
    (lam : ℝ) :
    SDEMDes W X y β θ u ε lam ↔
      ((1 - lam • W) *ᵥ u = ε ∧ y = X *ᵥ β + (W * X) *ᵥ θ + u) := by
  unfold SDEMDes
  have key : ((1 - lam • W) *ᵥ u = ε) ↔ (u = lam • (W *ᵥ u) + ε) := by
    rw [one_sub_smul_mulVec]
    constructor
    · intro h
      calc u = (u - lam • (W *ᵥ u)) + lam • (W *ᵥ u) := by abel
        _ = ε + lam • (W *ᵥ u) := congrArg (fun z => z + lam • (W *ᵥ u)) h
        _ = lam • (W *ᵥ u) + ε := add_comm _ _
    · intro h
      calc u - lam • (W *ᵥ u) = (lam • (W *ᵥ u) + ε) - lam • (W *ᵥ u) :=
            congrArg (fun z => z - lam • (W *ᵥ u)) h
        _ = ε := by abel
  constructor
  · rintro ⟨hy, hu⟩; exact ⟨key.mpr hu, hy⟩
  · rintro ⟨hu, hy⟩; exact ⟨hy, key.mp hu⟩

/-- **Reduced form of SDEM.** With `1 - λW` invertible, SDEM holds exactly when
`u = (1 - λW)⁻¹ ε` and `y = Xβ + WXθ + (1 - λW)⁻¹ ε`.

This is the published reduced form: LeSage (2014) writes the disturbance as
`u = (I - λW)⁻¹ε = (I + λW + λ²W² + ⋯)ε` and notes that this is what makes the error process
*global* even though the spillovers in `WX` are local. -/
theorem sdemDes_iff_reducedForm (W : WMat n) (X : DMat n k) (y u ε : Vec n) (β θ : Vec k)
    (lam : ℝ) (h : IsUnit (1 - lam • W)) :
    SDEMDes W X y β θ u ε lam ↔
      (u = (↑(h.unit⁻¹) : WMat n) *ᵥ ε ∧
        y = X *ᵥ β + (W * X) *ᵥ θ + (↑(h.unit⁻¹) : WMat n) *ᵥ ε) := by
  have hL : (↑(h.unit⁻¹) : WMat n) * (1 - lam • W) = 1 := by
    simpa only [h.unit_spec] using Units.inv_mul h.unit
  have hR : (1 - lam • W) * (↑(h.unit⁻¹) : WMat n) = 1 := by
    simpa only [h.unit_spec] using Units.mul_inv h.unit
  rw [sdemDes_iff_mulVec]
  constructor
  · rintro ⟨hu, hy⟩
    have hu' : u = (↑(h.unit⁻¹) : WMat n) *ᵥ ε := by
      have h1 : (↑(h.unit⁻¹) : WMat n) *ᵥ ((1 - lam • W) *ᵥ u)
          = (↑(h.unit⁻¹) : WMat n) *ᵥ ε := by rw [hu]
      rwa [mulVec_mulVec, hL, one_mulVec] at h1
    exact ⟨hu', by rw [hy, hu']⟩
  · rintro ⟨hu, hy⟩
    have hu' : (1 - lam • W) *ᵥ u = ε := by
      rw [hu, mulVec_mulVec, hR, one_mulVec]
    exact ⟨hu', by rw [hy, hu]⟩

/-- **The reduced form, with the invertibility hypothesis derived from the weights.** For
nonnegative row-substochastic `W` and `|λ| < 1`, `1 - λW` is invertible by
`GeoDa.isUnit_one_sub_smul_of_rowSubstochastic`, and no `IsUnit` is assumed. -/
theorem sdemDes_iff_reducedForm_of_rowSubstochastic (W : WMat n) (X : DMat n k) (y u ε : Vec n)
    (β θ : Vec k) (lam : ℝ) (hW : Nonneg W) (h1 : RowSubstochastic W) (hlam : |lam| < 1) :
    SDEMDes W X y β θ u ε lam ↔
      (u = ((1 - lam • W)⁻¹ : WMat n) *ᵥ ε ∧
        y = X *ᵥ β + (W * X) *ᵥ θ + ((1 - lam • W)⁻¹ : WMat n) *ᵥ ε) := by
  have hdet : IsUnit (1 - lam • W).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp
      (isUnit_one_sub_smul_of_rowSubstochastic W hW h1 lam hlam)
  rw [sdemDes_iff_mulVec]
  constructor
  · rintro ⟨hu, hy⟩
    have hu' : u = ((1 - lam • W)⁻¹ : WMat n) *ᵥ ε :=
      mulVec_eq_of_mulVec_eq (nonsing_inv_mul _ hdet) hu
    exact ⟨hu', by rw [hy, hu']⟩
  · rintro ⟨hu, hy⟩
    exact ⟨mulVec_eq_of_eq_mulVec (mul_nonsing_inv _ hdet) hu, by rw [hy, hu]⟩

/-! ### Moments -/

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **SDEM moments.** With `u = Bε` for an inverse `B` of `1 - λW`, the disturbance is mean
zero with covariance `σ² B Bᵀ`, and the outcome has mean `Xβ + WXθ` and the *same* covariance
— the regressors shift the mean and contribute nothing to the variance.

This is `GeoDa.sem_moments` with `Xβ + WXθ` in place of `Xβ`; the derivation is not repeated. -/
theorem sdem_moments {ε : Ω → Vec n} {σ2 : ℝ} (hε : IsWhiteNoise μ ε σ2) (B : WMat n)
    (xb wxg : Vec n) :
    rvExp μ (fun ω => xb + wxg + B *ᵥ ε ω) = xb + wxg ∧
      rvCov μ (fun ω => xb + wxg + B *ᵥ ε ω) = σ2 • (B * Bᵀ) := by
  have hfun : (fun ω => xb + wxg + B *ᵥ ε ω) = fun ω => (xb + wxg) + B *ᵥ ε ω := by
    funext ω; abel
  rw [hfun]
  exact (sem_moments hε B (xb + wxg)).2.2

end GeoDa
