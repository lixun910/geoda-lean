/-
Copyright (c) 2026 GeoDa-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import GeoDa.Design
import Mathlib.Tactic.Abel

/-!
# SLX, and where it sits in the nesting

The four models of `GeoDa.Design` — GNS, SAR, SEM and SDM — are the ones the spatial
econometrics literature names. **SLX** (*spatial lag of X*) is the fifth that belongs
with them, and the repository did not have it: `y = Xβ + WXθ + ε`, a spatial lag of the
regressors with no lag of the dependent variable and no spatial error.

It is included here for two reasons. It is a model in its own right, used when the
dependence is believed to run through the regressors rather than the outcome. And it is
where the GNS nesting bottoms out: GNS with *both* the lag coefficient `ρ` and the error
coefficient `λ` switched off is SLX, and the theorem below says so exactly.

This file was added as the first of the agent-loop benchmark tasks recorded in
`docs/agent-tasks.md`: a *new nested model relation*, stated and proved from scratch.
As everywhere else in this repository, it is a statement about model *equations*.

## Main definitions

* `GeoDa.SLXDes` : the SLX model equation.

## Main results

* `GeoDa.gnsDes_iff_slxDes` : GNS with `ρ = 0` and `λ = 0` is SLX exactly, together
  with the identity `u = ε` that reconciles the two disturbance conventions.
-/

open scoped Matrix
open Matrix

namespace GeoDa

variable {n k : ℕ}

/-- The **spatial lag of X** (SLX) model: `y = Xβ + WXθ + ε`, with the regressors and
their spatial lag, and no spatial dependence in the outcome or the error.

The lagged-regressor term is `(W * X) *ᵥ θ`, as everywhere else in this repository. -/
def SLXDes (W : WMat n) (X : DMat n k) (y : Vec n) (β : Vec k) (θ : Vec k) (ε : Vec n) : Prop :=
  y = X *ᵥ β + (W * X) *ᵥ θ + ε

/-- **GNS with `ρ = 0` and `λ = 0` is SLX**, together with `u = ε`.

Both coefficients vanish, so the outcome carries neither a spatial lag nor a spatially
autocorrelated disturbance; what is left is the regressors, their spatial lag, and the
innovation. As with SAR and SDM, the equivalence has to carry `u = ε` explicitly,
because GNS keeps a latent disturbance that SLX absorbs. -/
theorem gnsDes_iff_slxDes (W : WMat n) (X : DMat n k) (y u ε : Vec n) (β θ : Vec k) :
    GNSDes W X y β θ u ε 0 0 ↔ (SLXDes W X y β θ ε ∧ u = ε) := by
  unfold GNSDes SLXDes
  constructor
  · rintro ⟨h, hu⟩
    refine ⟨?_, ?_⟩
    · calc y = (0 : ℝ) • (W *ᵥ y) + X *ᵥ β + (W * X) *ᵥ θ + u := h
        _ = X *ᵥ β + (W * X) *ᵥ θ + ε := by rw [hu]; simp only [zero_smul]; abel
    · rw [hu]; simp only [zero_smul]; abel
  · rintro ⟨h, hu⟩
    refine ⟨?_, ?_⟩
    · calc y = X *ᵥ β + (W * X) *ᵥ θ + ε := h
        _ = (0 : ℝ) • (W *ᵥ y) + X *ᵥ β + (W * X) *ᵥ θ + u := by
              rw [hu]; simp only [zero_smul]; abel
    · rw [hu]; simp only [zero_smul]; abel

end GeoDa
