/-
Copyright (c) 2026 GeoDa-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import GeoDa.GNS
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Abel

/-!
# GNS nesting with a concrete spatial weights matrix

`GeoDa.GNS` works with an abstract linear operator. Here `W` is a concrete
`n × n` real matrix acting on vectors by `Matrix.mulVec`, so that `WXθ` can
eventually be instantiated by an actual matrix product.

We prove

* the nesting results of `GeoDa.GNS` again in the matrix setting;
* that the SAR and SEM structural equations are each *equivalent to a linear
  system* `(1 - ρW) y = Xβ + ε` resp. `(1 - λW) u = ε`;
* the **reduced forms**: when `1 - ρW` (resp. `1 - λW`) is invertible, the linear
  system has the unique solution `y = (1 - ρW)⁻¹ (Xβ + ε)`;
* an **observational-equivalence** statement: with `B` the inverse of `1 - λW`,
  the SEM reduced form `Xβ + Bε` equals the SAR reduced form `B((1 - λW)Xβ + ε)`
  — that is, a SEM is a SAR with spatially filtered regressors;
* the **non-equivalence** statement: the SAR and SEM reduced forms agree for all
  `(Xβ, ε)` exactly when the inverse matrix is the identity.

The invertibility hypothesis is taken as `IsUnit` in the matrix ring, which for
square matrices over `ℝ` is equivalent to nonsingularity (`Matrix.isUnit_iff_isUnit_det`).
-/

open scoped Matrix
open Matrix

namespace GeoDa

variable {n : ℕ}

/-- A concrete `n × n` real spatial weights matrix. -/
abbrev WMat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- The GNS model with a concrete weights matrix: `y = ρWy + Xβ + WXθ + u`,
`u = λWu + ε`. -/
def GNSMat (W : WMat n) (y xb wxθ u ε : Vec n) (ρ lam : ℝ) : Prop :=
  y = ρ • (W *ᵥ y) + xb + wxθ + u ∧ u = lam • (W *ᵥ u) + ε

/-- The SAR model with a concrete weights matrix. -/
def SARMat (W : WMat n) (y xb ε : Vec n) (ρ : ℝ) : Prop :=
  y = ρ • (W *ᵥ y) + xb + ε

/-- The SEM model with a concrete weights matrix. -/
def SEMMat (W : WMat n) (y xb u ε : Vec n) (lam : ℝ) : Prop :=
  y = xb + u ∧ u = lam • (W *ᵥ u) + ε

/-- The SDM model with a concrete weights matrix. -/
def SDMMat (W : WMat n) (y xb wxθ ε : Vec n) (ρ : ℝ) : Prop :=
  y = ρ • (W *ᵥ y) + xb + wxθ + ε

/-! ### Nesting -/

/-- GNS with `λ = 0` and `θ = 0` is SAR together with `u = ε`. -/
theorem gnsMat_iff_sarMat (W : WMat n) (y xb u ε : Vec n) (ρ : ℝ) :
    GNSMat W y xb 0 u ε ρ 0 ↔ (SARMat W y xb ε ρ ∧ u = ε) := by
  unfold GNSMat SARMat
  constructor
  · rintro ⟨h, hu⟩
    refine ⟨?_, ?_⟩
    · calc y = ρ • (W *ᵥ y) + xb + 0 + u := h
        _ = ρ • (W *ᵥ y) + xb + ε := by rw [hu]; simp only [zero_smul]; abel
    · rw [hu]; simp only [zero_smul]; abel
  · rintro ⟨h, hu⟩
    refine ⟨?_, ?_⟩
    · calc y = ρ • (W *ᵥ y) + xb + ε := h
        _ = ρ • (W *ᵥ y) + xb + 0 + u := by rw [hu]; abel
    · rw [hu]; simp only [zero_smul]; abel

/-- GNS with `ρ = 0` and `θ = 0` is SEM. -/
theorem gnsMat_iff_semMat (W : WMat n) (y xb u ε : Vec n) (lam : ℝ) :
    GNSMat W y xb 0 u ε 0 lam ↔ SEMMat W y xb u ε lam := by
  unfold GNSMat SEMMat
  constructor
  · rintro ⟨h, hu⟩
    refine ⟨?_, hu⟩
    · calc y = (0 : ℝ) • (W *ᵥ y) + xb + 0 + u := h
        _ = xb + u := by simp only [zero_smul]; abel
  · rintro ⟨h, hu⟩
    refine ⟨?_, hu⟩
    · have key : (0 : ℝ) • (W *ᵥ y) + xb + 0 + u = xb + u := by
        simp only [zero_smul]; abel
      exact h.trans key.symm

/-- GNS with `λ = 0` is SDM together with `u = ε`. -/
theorem gnsMat_iff_sdmMat (W : WMat n) (y xb wxθ u ε : Vec n) (ρ : ℝ) :
    GNSMat W y xb wxθ u ε ρ 0 ↔ (SDMMat W y xb wxθ ε ρ ∧ u = ε) := by
  unfold GNSMat SDMMat
  constructor
  · rintro ⟨h, hu⟩
    refine ⟨?_, ?_⟩
    · calc y = ρ • (W *ᵥ y) + xb + wxθ + u := h
        _ = ρ • (W *ᵥ y) + xb + wxθ + ε := by rw [hu]; simp only [zero_smul]; abel
    · rw [hu]; simp only [zero_smul]; abel
  · rintro ⟨h, hu⟩
    refine ⟨?_, ?_⟩
    · calc y = ρ • (W *ᵥ y) + xb + wxθ + ε := h
        _ = ρ • (W *ᵥ y) + xb + wxθ + u := by rw [hu]
    · rw [hu]; simp only [zero_smul]; abel

/-! ### Structural equation versus linear system -/

/-- `(1 - c • W) *ᵥ v = v - c • (W *ᵥ v)`. -/
theorem one_sub_smul_mulVec (W : WMat n) (c : ℝ) (v : Vec n) :
    (1 - c • W) *ᵥ v = v - c • (W *ᵥ v) := by
  rw [sub_mulVec, one_mulVec, smul_mulVec]

/-- The SAR structural equation is equivalent to the linear system `(1 - ρW)y = Xβ + ε`. -/
theorem sarMat_iff_mulVec (W : WMat n) (y xb ε : Vec n) (ρ : ℝ) :
    SARMat W y xb ε ρ ↔ (1 - ρ • W) *ᵥ y = xb + ε := by
  rw [SARMat, one_sub_smul_mulVec, sub_eq_iff_eq_add]
  constructor
  · intro h
    calc y = ρ • (W *ᵥ y) + xb + ε := h
      _ = (xb + ε) + ρ • (W *ᵥ y) := by abel
  · intro h
    calc y = (xb + ε) + ρ • (W *ᵥ y) := h
      _ = ρ • (W *ᵥ y) + xb + ε := by abel

/-- The SEM structural equation is equivalent to the linear system `(1 - λW)u = ε`
together with `y = Xβ + u`. -/
theorem semMat_iff_mulVec (W : WMat n) (y xb u ε : Vec n) (lam : ℝ) :
    SEMMat W y xb u ε lam ↔ ((1 - lam • W) *ᵥ u = ε ∧ y = xb + u) := by
  have key : (u = lam • (W *ᵥ u) + ε) ↔ ((1 - lam • W) *ᵥ u = ε) := by
    rw [one_sub_smul_mulVec, sub_eq_iff_eq_add]
    constructor
    · intro h
      calc u = lam • (W *ᵥ u) + ε := h
        _ = ε + lam • (W *ᵥ u) := by abel
    · intro h
      calc u = ε + lam • (W *ᵥ u) := h
        _ = lam • (W *ᵥ u) + ε := by abel
  rw [SEMMat]
  constructor
  · rintro ⟨hy, hu⟩; exact ⟨key.mp hu, hy⟩
  · rintro ⟨hu, hy⟩; exact ⟨hy, key.mpr hu⟩

/-! ### Reduced forms under invertibility -/

/-- **SAR reduced form.** If `1 - ρW` is invertible then the SAR structural
equation holds exactly when `y` is the solution of the reduced form
`y = (1 - ρW)⁻¹ (Xβ + ε)`. -/
theorem sarMat_iff_reducedForm (W : WMat n) (y xb ε : Vec n) (ρ : ℝ)
    (h : IsUnit (1 - ρ • W)) :
    SARMat W y xb ε ρ ↔ y = (↑(h.unit⁻¹) : WMat n) *ᵥ (xb + ε) := by
  have hB : (↑(h.unit⁻¹) : WMat n) * (1 - ρ • W) = 1 := by
    simpa only [h.unit_spec] using Units.inv_mul h.unit
  have hB' : (1 - ρ • W) * (↑(h.unit⁻¹) : WMat n) = 1 := by
    simpa only [h.unit_spec] using Units.mul_inv h.unit
  rw [sarMat_iff_mulVec]
  constructor
  · intro hmv
    have h1 : (↑(h.unit⁻¹) : WMat n) *ᵥ ((1 - ρ • W) *ᵥ y)
        = (↑(h.unit⁻¹) : WMat n) *ᵥ (xb + ε) := by rw [hmv]
    rw [mulVec_mulVec, hB, one_mulVec] at h1
    exact h1
  · intro hy
    have h1 : (1 - ρ • W) *ᵥ y
        = (1 - ρ • W) *ᵥ ((↑(h.unit⁻¹) : WMat n) *ᵥ (xb + ε)) := by rw [hy]
    rw [mulVec_mulVec, hB', one_mulVec] at h1
    exact h1

/-- **SEM reduced form.** If `1 - λW` is invertible then the SEM structural
equation holds exactly when `u` and `y` are given by the reduced form: the
disturbance is `u = (1 - λW)⁻¹ ε` and the outcome is `y = Xβ + (1 - λW)⁻¹ ε`. -/
theorem semMat_iff_reducedForm (W : WMat n) (y xb u ε : Vec n) (lam : ℝ)
    (h : IsUnit (1 - lam • W)) :
    SEMMat W y xb u ε lam ↔
      (u = (↑(h.unit⁻¹) : WMat n) *ᵥ ε ∧ y = xb + (↑(h.unit⁻¹) : WMat n) *ᵥ ε) := by
  have hB : (↑(h.unit⁻¹) : WMat n) * (1 - lam • W) = 1 := by
    simpa only [h.unit_spec] using Units.inv_mul h.unit
  have hB' : (1 - lam • W) * (↑(h.unit⁻¹) : WMat n) = 1 := by
    simpa only [h.unit_spec] using Units.mul_inv h.unit
  rw [semMat_iff_mulVec]
  constructor
  · rintro ⟨hu, hy⟩
    have h1 : (↑(h.unit⁻¹) : WMat n) *ᵥ ((1 - lam • W) *ᵥ u)
        = (↑(h.unit⁻¹) : WMat n) *ᵥ ε := by rw [hu]
    rw [mulVec_mulVec, hB, one_mulVec] at h1
    exact ⟨h1, by rw [hy, h1]⟩
  · rintro ⟨hu, hy⟩
    have h1 : (1 - lam • W) *ᵥ u
        = (1 - lam • W) *ᵥ ((↑(h.unit⁻¹) : WMat n) *ᵥ ε) := by rw [hu]
    rw [mulVec_mulVec, hB', one_mulVec] at h1
    exact ⟨h1, by rw [hy, hu]⟩

/-! ### SAR versus SEM -/

/-- **Observational equivalence with filtered regressors.** With `B = (1 - λW)⁻¹`,
the SEM reduced form with regressors `Xβ` equals the SAR reduced form whose
regressors have been spatially filtered to `(1 - λW)Xβ`. -/
theorem sem_reducedForm_eq_sar_reducedForm_of_filtered (W : WMat n) (xb ε : Vec n)
    (lam : ℝ) (h : IsUnit (1 - lam • W)) :
    xb + (↑(h.unit⁻¹) : WMat n) *ᵥ ε
      = (↑(h.unit⁻¹) : WMat n) *ᵥ ((1 - lam • W) *ᵥ xb + ε) := by
  have hB : (↑(h.unit⁻¹) : WMat n) * (1 - lam • W) = 1 := by
    simpa only [h.unit_spec] using Units.inv_mul h.unit
  rw [mulVec_add, mulVec_mulVec, hB, one_mulVec]

/-- **Non-equivalence.** The SAR reduced form with coefficient `ρ` and the SEM
reduced form with coefficient `λ` agree as functions of `(Xβ, ε)` exactly when
both inverse matrices are the identity. -/
theorem reducedForm_eq_iff_inverse_eq_one (W : WMat n) (ρ lam : ℝ)
    (hρ : IsUnit (1 - ρ • W)) (hlam : IsUnit (1 - lam • W)) :
    (∀ xb ε : Vec n, (↑(hρ.unit⁻¹) : WMat n) *ᵥ (xb + ε)
        = xb + (↑(hlam.unit⁻¹) : WMat n) *ᵥ ε) ↔
      ((↑(hρ.unit⁻¹) : WMat n) = 1 ∧ (↑(hlam.unit⁻¹) : WMat n) = 1) := by
  constructor
  · intro h
    have hzero : ∀ xb : Vec n, (↑(hρ.unit⁻¹) : WMat n) *ᵥ xb = xb := by
      intro xb
      have hx := h xb 0
      simpa only [add_zero, mulVec_zero] using hx
    have hρ1 : (↑(hρ.unit⁻¹) : WMat n) = 1 := by
      have key : (mulVec (↑(hρ.unit⁻¹) : WMat n) : Vec n → Vec n) = mulVec (1 : WMat n) := by
        funext xb
        simpa [one_mulVec] using hzero xb
      exact mulVec_injective key
    refine ⟨hρ1, ?_⟩
    have hone : ∀ ε : Vec n, (↑(hlam.unit⁻¹) : WMat n) *ᵥ ε = ε := by
      intro ε
      have hε := h 0 ε
      simpa [hρ1] using hε.symm
    have key : (mulVec (↑(hlam.unit⁻¹) : WMat n) : Vec n → Vec n) = mulVec (1 : WMat n) := by
      funext ε
      simpa [one_mulVec] using hone ε
    exact mulVec_injective key
  · rintro ⟨h1, h2⟩ xb ε
    rw [h1, h2, one_mulVec, one_mulVec]

end GeoDa
