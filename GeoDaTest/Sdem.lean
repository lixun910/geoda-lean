/-
Copyright (c) 2026 GeoDa-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import GeoDaTest.Smoke

/-!
# Tests for the SDEM benchmark model

Signature pins, the two published nestings instantiated at `n = 2`, and — as the P4.2
protocol asks — the model re-declared with the `spatial_model` DSL and proved **equal to the
hand-written one by `rfl`**.
-/

open scoped Matrix

namespace GeoDaTest

open GeoDa

/-! ### Signature pins -/

#check @GeoDa.SDEMDes
#check @GeoDa.gnsDes_iff_sdemDes
#check @GeoDa.sdemDes_iff_slx_and_error
#check @GeoDa.sdemDes_iff_slxDes_of_lam_zero
#check @GeoDa.sdemDes_iff_semDes_of_theta_zero
#check @GeoDa.sdemDes_iff_mulVec
#check @GeoDa.sdemDes_iff_reducedForm
#check @GeoDa.sdemDes_iff_reducedForm_of_rowSubstochastic
#check @GeoDa.sdem_moments

/-! ### The published nestings, at `n = 2`

LeSage (2014) states that SDEM subsumes SLX when `λ = 0` and SEM when `θ = 0`. Both are
proved in `GeoDa/Sdem.lean` in general; these are the two-region instances. -/

example (y u ε : Vec 2) (β θ : Vec 1) :
    SDEMDes Wswap X2 y β θ u ε 0 ↔ (SLXDes Wswap X2 y β θ ε ∧ u = ε) :=
  sdemDes_iff_slxDes_of_lam_zero Wswap X2 y u ε β θ

example (y u ε : Vec 2) (β : Vec 1) (lam : ℝ) :
    SDEMDes Wswap X2 y β 0 u ε lam ↔ SEMDes Wswap X2 y β u ε lam :=
  sdemDes_iff_semDes_of_theta_zero Wswap X2 y u ε β lam

/-- SDEM is SLX with a spatial error — and here that is `Iff.rfl`, not an argument. -/
example (y u ε : Vec 2) (β θ : Vec 1) (lam : ℝ) :
    SDEMDes Wswap X2 y β θ u ε lam ↔ (SLXDes Wswap X2 y β θ u ∧ u = lam • (Wswap *ᵥ u) + ε) :=
  sdemDes_iff_slx_and_error Wswap X2 y u ε β θ lam

/-! ### The reduced form, with the hypothesis derived from the weights -/

example (y u ε : Vec 2) (β θ : Vec 1) :
    SDEMDes Wswap X2 y β θ u ε (1/2) ↔
      (u = ((1 - (1/2 : ℝ) • Wswap)⁻¹ : WMat 2) *ᵥ ε ∧
        y = X2 *ᵥ β + (Wswap * X2) *ᵥ θ + ((1 - (1/2 : ℝ) • Wswap)⁻¹ : WMat 2) *ᵥ ε) :=
  sdemDes_iff_reducedForm_of_rowSubstochastic Wswap X2 y u ε β θ (1/2)
    wswap_nonneg (rowSubstochastic_of_rowStochastic Wswap wswap_rowStochastic) (by norm_num)

/-! ### The model, re-declared with the DSL

Phase B of the P4.2 protocol asks for a typed model specification, and `spatial_model` is
how this repository writes one. The generated `def` is then proved equal to the hand-written
`SDEMDes` by `rfl` — the same function up to definitional equality, not merely a proposition
that happens to agree. -/

spatial_model SdemViaDsl {n k : ℕ} (W : WMat n) (X : DMat n k) (y : Vec n) (β θ : Vec k)
    (u ε : Vec n) (lam : ℝ) :
  y = X *ᵥ β + (W * X) *ᵥ θ + u ∧ u = lam • (W *ᵥ u) + ε

theorem sdemViaDsl_eq_SDEMDes : @SdemViaDsl = @SDEMDes := rfl

end GeoDaTest
