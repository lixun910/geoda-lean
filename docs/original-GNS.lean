import Mathlib

/-!
# GNS and nested spatial econometric models

This is a first formalization of *model equations*, not estimators or
probability distributions. `W` is an abstract linear spatial lag operator.
The term `wxθ` stands for the spatially lagged regressors WXθ.
-/

namespace GeoDa

variable {n : ℕ}
abbrev Vec (n : ℕ) := Fin n → ℝ

/-- General nesting spatial model, with an explicit latent disturbance `u`. -/
def GNS (W : Vec n →ₗ[ℝ] Vec n) (y xb wxθ u ε : Vec n)
    (ρ λ : ℝ) : Prop :=
  y = ρ • W y + xb + wxθ + u ∧
  u = λ • W u + ε

/-- Spatial autoregressive (spatial lag) model. -/
def SAR (W : Vec n →ₗ[ℝ] Vec n) (y xb ε : Vec n)
    (ρ : ℝ) : Prop :=
  y = ρ • W y + xb + ε

/-- Spatial error model with explicit latent disturbance. -/
def SEM (W : Vec n →ₗ[ℝ] Vec n) (y xb u ε : Vec n)
    (λ : ℝ) : Prop :=
  y = xb + u ∧ u = λ • W u + ε

/-- Spatial Durbin model, where `wxθ` denotes WXθ. -/
def SDM (W : Vec n →ₗ[ℝ] Vec n) (y xb wxθ ε : Vec n)
    (ρ : ℝ) : Prop :=
  y = ρ • W y + xb + wxθ + ε

/-- GNS with zero spatial-error and lagged-X effects reduces to SAR. -/
theorem gns_iff_sar (W : Vec n →ₗ[ℝ] Vec n)
    (y xb u ε : Vec n) (ρ : ℝ) :
    GNS W y xb 0 u ε ρ 0 ↔ (SAR W y xb ε ρ ∧ u = ε) := by
  simp [GNS, SAR]

/-- GNS with zero endogenous spatial lag and lagged-X effects is SEM. -/
theorem gns_iff_sem (W : Vec n →ₗ[ℝ] Vec n)
    (y xb u ε : Vec n) (λ : ℝ) :
    GNS W y xb 0 u ε 0 λ ↔ SEM W y xb u ε λ := by
  simp [GNS, SEM]

/-- GNS with zero spatial-error coefficient reduces to SDM. -/
theorem gns_iff_sdm (W : Vec n →ₗ[ℝ] Vec n)
    (y xb wxθ u ε : Vec n) (ρ : ℝ) :
    GNS W y xb wxθ u ε ρ 0 ↔ (SDM W y xb wxθ ε ρ ∧ u = ε) := by
  simp [GNS, SDM]

end GeoDa
