/-
Copyright (c) 2026 GeoDa-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import GeoDaTest.Smoke

/-!
# Tests for the heterogeneous-`ρ` model

Signature pins, and then the two directions of the identifiability result on concrete
weights matrices. The negative half is the one worth having: an island's parameter is not
identified, and that is shown here on `Wisland`, whose row `0` is all zeros.
-/

open scoped Matrix

namespace GeoDaTest

open GeoDa

/-! ### Signature pins -/

#check @GeoDa.diagMul
#check @GeoDa.HeteroSARDes
#check @GeoDa.diagMul_mulVec
#check @GeoDa.rowSum_diagMul
#check @GeoDa.abs_mulVec_diagMul_apply_le
#check @GeoDa.norm_mulVec_diagMul_le
#check @GeoDa.isUnit_one_sub_diagMul_of_rowSubstochastic
#check @GeoDa.heteroSARDes_iff_mulVec
#check @GeoDa.heteroSARDes_iff_reducedForm
#check @GeoDa.diagMul_update_island
#check @GeoDa.diagMul_injective_of_no_island
#check @GeoDa.diagMul_eq_of_reducedForm_eq
#check @GeoDa.heteroSAR_parameter_identified
#check @GeoDa.heteroSARDes_island_invariant
#check @GeoDa.heteroSAR_reducedForm_island_invariant

/-! ### Existence and uniqueness, on the island matrix

`Wisland` is nonnegative and row-substochastic, so the heterogeneous model with any
parameters bounded by `c < 1` has exactly one solution. Islands are *not* a problem for
existence — they are a problem for identification, below. -/

example (ρ : Vec 2) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) (hc : ∀ i, |ρ i| ≤ c) :
    IsUnit (1 - diagMul ρ Wisland) :=
  isUnit_one_sub_diagMul_of_rowSubstochastic Wisland wisland_nonneg
    wisland_rowSubstochastic ρ c hc0 hc1 hc

/-- The reduced form, on the same instance. -/
example (ρ y : Vec 2) (β : Vec 1) (ε : Vec 2) (h : IsUnit (1 - diagMul ρ Wisland)) :
    HeteroSARDes Wisland X2 ρ y β ε ↔
      y = ((1 - diagMul ρ Wisland)⁻¹ : WMat 2) *ᵥ (X2 *ᵥ β + ε) :=
  heteroSARDes_iff_reducedForm Wisland X2 ρ y β ε h

/-! ### Non-identification at an island

Row `0` of `Wisland` is all zeros (`wisland_island`), so `ρ 0` multiplies a zero row.
Changing it changes nothing: the two models have the same solutions, and the two reduced
forms are the same matrix applied to the same vector. -/

example (ρ : Vec 2) (a : ℝ) (y : Vec 2) (β : Vec 1) (ε : Vec 2) :
    HeteroSARDes Wisland X2 (Function.update ρ 0 a) y β ε
      ↔ HeteroSARDes Wisland X2 ρ y β ε :=
  heteroSARDes_island_invariant Wisland X2 wisland_island ρ a y β ε

example (ρ : Vec 2) (a : ℝ) (xb ε : Vec 2) :
    ((1 - diagMul (Function.update ρ 0 a) Wisland)⁻¹ : WMat 2) *ᵥ (xb + ε)
      = ((1 - diagMul ρ Wisland)⁻¹ : WMat 2) *ᵥ (xb + ε) :=
  heteroSAR_reducedForm_island_invariant Wisland wisland_island ρ a xb ε

/-- And explicitly: `ρ = ![1/4, 1/2]` and `ρ = ![3/4, 1/2]` — different parameters, row `0`
being the island — give the same multiplier. -/
theorem wisland_two_rho_same_multiplier :
    diagMul ![3/4, 1/2] Wisland = diagMul ![1/4, 1/2] Wisland := by
  have hupd : Function.update (![1/4, 1/2] : Vec 2) 0 (3/4) = ![3/4, 1/2] := by
    funext i
    fin_cases i <;> simp [Function.update_apply]
  rw [← hupd]
  exact diagMul_update_island Wisland wisland_island ![1/4, 1/2] (3/4)

/-! ### Identification away from islands

`Wswap` has no zero row, so `ρ ↦ diag(ρ) Wswap` is injective, and by
`heteroSAR_parameter_identified` the reduced form determines `ρ`. -/

theorem wswap_no_island (i : Fin 2) : ¬ Island Wswap i := by
  intro h
  fin_cases i
  · have h1 := h 1
    norm_num [Wswap] at h1
  · have h0 := h 0
    norm_num [Wswap] at h0

example : Function.Injective (fun ρ : Vec 2 => diagMul ρ Wswap) :=
  diagMul_injective_of_no_island Wswap wswap_no_island

end GeoDaTest
