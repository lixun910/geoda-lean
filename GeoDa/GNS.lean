/-
Copyright (c) 2026 GeoDa-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Abel

/-!
# GNS and nested spatial econometric models

This file formalizes the *model equations* of the general nesting spatial (GNS)
model and its three classical nested special cases, in the abstract setting where
the spatial lag operator `W` is an arbitrary `ℝ`-linear endomorphism of `Fin n → ℝ`.

What is (and is not) claimed:

* These are statements about model *equations*, not about estimators, probability
  distributions, identifiability, or consistency.
* `W` here is an abstract linear operator. See `GeoDa.Weights` for the concrete
  matrix-valued version.
* `xb` denotes `Xβ` and `wxθ` denotes `WXθ`; both are supplied vectors, not yet
  constructed by matrix multiplication.

## Main definitions

* `GeoDa.Vec` : the type of `n`-vectors of reals.
* `GeoDa.GNS`, `GeoDa.SAR`, `GeoDa.SEM`, `GeoDa.SDM` : the model equations.

## Main results

* `GeoDa.gns_iff_sar`, `GeoDa.gns_iff_sem`, `GeoDa.gns_iff_sdm` : GNS nests each
  of the three special cases exactly when the corresponding coefficients vanish.
-/

namespace GeoDa

variable {n : ℕ}

/-- An `n`-vector of real numbers. -/
abbrev Vec (n : ℕ) := Fin n → ℝ

/-- The **general nesting spatial** model: a spatial lag of the dependent variable,
spatially lagged regressors, and a spatially autocorrelated disturbance.

`y = ρWy + Xβ + WXθ + u`, `u = λWu + ε`. -/
def GNS (W : Vec n →ₗ[ℝ] Vec n) (y xb wxθ u ε : Vec n) (ρ lam : ℝ) : Prop :=
  y = ρ • W y + xb + wxθ + u ∧ u = lam • W u + ε

/-- The **spatial autoregressive** (spatial lag) model: `y = ρWy + Xβ + ε`. -/
def SAR (W : Vec n →ₗ[ℝ] Vec n) (y xb ε : Vec n) (ρ : ℝ) : Prop :=
  y = ρ • W y + xb + ε

/-- The **spatial error** model, with the latent disturbance `u` made explicit:
`y = Xβ + u`, `u = λWu + ε`. -/
def SEM (W : Vec n →ₗ[ℝ] Vec n) (y xb u ε : Vec n) (lam : ℝ) : Prop :=
  y = xb + u ∧ u = lam • W u + ε

/-- The **spatial Durbin** model: `y = ρWy + Xβ + WXθ + ε`. -/
def SDM (W : Vec n →ₗ[ℝ] Vec n) (y xb wxθ ε : Vec n) (ρ : ℝ) : Prop :=
  y = ρ • W y + xb + wxθ + ε

/-- GNS with vanishing spatial-error coefficient (`λ = 0`) and vanishing lagged-X
coefficient (`θ = 0`) is exactly SAR, together with the identity `u = ε` that
makes the two latent disturbance conventions agree. -/
theorem gns_iff_sar (W : Vec n →ₗ[ℝ] Vec n) (y xb u ε : Vec n) (ρ : ℝ) :
    GNS W y xb 0 u ε ρ 0 ↔ (SAR W y xb ε ρ ∧ u = ε) := by
  unfold GNS SAR
  constructor
  · rintro ⟨h, hu⟩
    refine ⟨?_, ?_⟩
    · calc y = ρ • W y + xb + 0 + u := h
        _ = ρ • W y + xb + ε := by rw [hu]; simp only [zero_smul]; abel
    · rw [hu]; simp only [zero_smul]; abel
  · rintro ⟨h, hu⟩
    refine ⟨?_, ?_⟩
    · calc y = ρ • W y + xb + ε := h
        _ = ρ • W y + xb + 0 + u := by rw [hu]; abel
    · rw [hu]; simp only [zero_smul]; abel

/-- GNS with vanishing spatial-lag coefficient (`ρ = 0`) and vanishing lagged-X
coefficient (`θ = 0`) is exactly SEM. -/
theorem gns_iff_sem (W : Vec n →ₗ[ℝ] Vec n) (y xb u ε : Vec n) (lam : ℝ) :
    GNS W y xb 0 u ε 0 lam ↔ SEM W y xb u ε lam := by
  unfold GNS SEM
  constructor
  · rintro ⟨h, hu⟩
    refine ⟨?_, hu⟩
    · calc y = 0 • W y + xb + 0 + u := h
        _ = xb + u := by simp only [zero_smul]; abel
  · rintro ⟨h, hu⟩
    refine ⟨?_, hu⟩
    · have key : (0 : ℝ) • W y + xb + 0 + u = xb + u := by
        simp only [zero_smul]; abel
      exact h.trans key.symm

/-- GNS with vanishing spatial-error coefficient (`λ = 0`) is exactly SDM, together
with the identity `u = ε`. -/
theorem gns_iff_sdm (W : Vec n →ₗ[ℝ] Vec n) (y xb wxθ u ε : Vec n) (ρ : ℝ) :
    GNS W y xb wxθ u ε ρ 0 ↔ (SDM W y xb wxθ ε ρ ∧ u = ε) := by
  unfold GNS SDM
  constructor
  · rintro ⟨h, hu⟩
    refine ⟨?_, ?_⟩
    · calc y = ρ • W y + xb + wxθ + u := h
        _ = ρ • W y + xb + wxθ + ε := by rw [hu]; simp only [zero_smul]; abel
    · rw [hu]; simp only [zero_smul]; abel
  · rintro ⟨h, hu⟩
    refine ⟨?_, ?_⟩
    · calc y = ρ • W y + xb + wxθ + ε := h
        _ = ρ • W y + xb + wxθ + u := by rw [hu]
    · rw [hu]; simp only [zero_smul]; abel

end GeoDa
