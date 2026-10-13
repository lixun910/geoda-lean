/-
Copyright (c) 2026 GeoDa-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import GeoDa
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Smoke tests

Compile-time tests for `GeoDa`. These are ordinary Lean declarations: if any of
them stops elaborating, `lake build` fails, so CI catches regressions.

* signature pins, so that a change in a theorem statement is caught;
* the nesting theorems instantiated at `n = 2` with an explicit weights matrix;
* numerical checks of the invertibility hypothesis of the reduced-form theorems.
-/

open scoped Matrix

namespace GeoDaTest

open GeoDa

/-! ### Signature pins -/

#check @GeoDa.gns_iff_sar
#check @GeoDa.gns_iff_sem
#check @GeoDa.gns_iff_sdm
#check @GeoDa.gnsMat_iff_sarMat
#check @GeoDa.gnsMat_iff_semMat
#check @GeoDa.gnsMat_iff_sdmMat
#check @GeoDa.sarMat_iff_mulVec
#check @GeoDa.semMat_iff_mulVec
#check @GeoDa.sarMat_iff_reducedForm
#check @GeoDa.semMat_iff_reducedForm
#check @GeoDa.sem_reducedForm_eq_sar_reducedForm_of_filtered
#check @GeoDa.reducedForm_eq_iff_inverse_eq_one

-- GeoDa.Design: the regressors formed from a design matrix
#check @GeoDa.design_wxθ_eq
#check @GeoDa.gnsDes_iff_gnsMat
#check @GeoDa.sarDes_iff_sarMat
#check @GeoDa.semDes_iff_semMat
#check @GeoDa.sdmDes_iff_sdmMat
#check @GeoDa.gnsDes_iff_sarDes
#check @GeoDa.gnsDes_iff_semDes
#check @GeoDa.gnsDes_iff_sdmDes
#check @GeoDa.sarDes_iff_mulVec
#check @GeoDa.semDes_iff_mulVec
#check @GeoDa.sarDes_iff_reducedForm
#check @GeoDa.semDes_iff_reducedForm
#check @GeoDa.semDes_reducedForm_eq_sarDes_reducedForm_of_filtered

/-! ### The full GNS reduced form: signature pins -/

#check @GeoDa.one_sub_smul_mulVec_eq_iff
#check @GeoDa.mulVec_eq_of_mulVec_eq
#check @GeoDa.mulVec_eq_of_eq_mulVec
#check @GeoDa.mulVec_eq_iff
#check @GeoDa.gnsDes_iff_mulVec
#check @GeoDa.gnsDes_iff_reducedForm_of_inverse
#check @GeoDa.gnsDes_reducedForm
#check @GeoDa.reducedForm_gnsDes
#check @GeoDa.gnsDes_iff_reducedForm
#check @GeoDa.isUnit_iff_det_ne_zero
#check @GeoDa.gnsDes_iff_reducedForm_of_det_ne_zero
#check @GeoDa.sdmDes_iff_mulVec
#check @GeoDa.sdmDes_iff_reducedForm

/-! ### Invertibility of the spatial multiplier: signature pins -/

#check @GeoDa.abs_mulVec_apply_le_norm
#check @GeoDa.norm_mulVec_le
#check @GeoDa.mulVec_injective_one_sub_smul
#check @GeoDa.isUnit_one_sub_smul_of_rowSubstochastic
#check @GeoDa.isUnit_one_sub_smul_of_rowStochastic
#check @GeoDa.sarMat_iff_reducedForm_of_rowSubstochastic
#check @GeoDa.semMat_iff_reducedForm_of_rowSubstochastic

/-! ### Spatial weights: signature pins -/

#check @GeoDa.mulVec_one_apply
#check @GeoDa.rowStochastic_iff_mulVec_one
#check @GeoDa.rowSum_nonneg
#check @GeoDa.rowSubstochastic_of_rowStochastic
#check @GeoDa.rowSum_eq_zero_of_island
#check @GeoDa.island_iff_rowSum_eq_zero
#check @GeoDa.not_rowStochastic_of_island
#check @GeoDa.rowStochastic_one
#check @GeoDa.nonneg_one
#check @GeoDa.not_zeroDiag_one
#check @GeoDa.rowSum_normalize
#check @GeoDa.rowStochastic_normalize_of_ne_zero
#check @GeoDa.island_normalize
#check @GeoDa.nonneg_normalize
#check @GeoDa.zeroDiag_normalize
#check @GeoDa.rowSubstochastic_normalize
#check @GeoDa.rowStochastic_normalize_iff
#check @GeoDa.rowStochastic_normalize_iff_pos

/-! ### Explicit data -/

/-- The symmetric two-region "swap" weights matrix. -/
def Wswap : WMat 2 := !![0, 1; 1, 0]

/-- The two-sided inverse of `1 - (1/2) • Wswap`:
`(1 - 1/4)⁻¹ • [[1, 1/2], [1/2, 1]] = [[4/3, 2/3], [2/3, 4/3]]`. -/
noncomputable def WswapInv : WMat 2 := !![4/3, 2/3; 2/3, 4/3]

/-- Numerical check: `WswapInv` really is a two-sided inverse of `1 - (1/2)•Wswap`. -/
theorem wswapInv_spec :
    WswapInv * (1 - (1/2 : ℝ) • Wswap) = 1 ∧
      (1 - (1/2 : ℝ) • Wswap) * WswapInv = 1 := by
  constructor <;>
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Wswap, WswapInv, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

/-- The nesting theorem at `n = 2`, with an explicit weights matrix. -/
example (y xb u ε : Vec 2) (ρ : ℝ) :
    GNSMat Wswap y xb 0 u ε ρ 0 ↔ (SARMat Wswap y xb ε ρ ∧ u = ε) :=
  gnsMat_iff_sarMat Wswap y xb u ε ρ

/-- The reduced-form theorem at `n = 2`, with an explicit weights matrix. -/
example (y xb ε : Vec 2) (h : IsUnit (1 - (1/2 : ℝ) • Wswap)) :
    SARMat Wswap y xb ε (1/2) ↔ y = ↑(h.unit⁻¹) *ᵥ (xb + ε) :=
  sarMat_iff_reducedForm Wswap y xb ε (1/2) h

/-! ### A design matrix over the same two-region model -/

/-- A one-column design matrix for the two-region model. -/
def X2 : DMat 2 1 := !![1; 2]

/-- Numerical check: `Wswap * X2 = ![2, 1]ᵀ`, i.e. the lag of the fitted values
swaps the two regions. -/
theorem wswap_mul_X2 : Wswap * X2 = !![2; 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Wswap, X2, Matrix.mul_apply, Fin.sum_univ_two]

/-- The `Xβ`-from-design-matrix bridge at `n = 2`, `k = 1`: the design-matrix GNS
equation is the `GeoDa.Weights` equation with `xb := X2 *ᵥ β` and
`wxθ := (Wswap * X2) *ᵥ θ`. -/
example (y u ε : Vec 2) (β θ : Vec 1) (ρ lam : ℝ) :
    GNSDes Wswap X2 y β θ u ε ρ lam
      ↔ GNSMat Wswap y (X2 *ᵥ β) ((Wswap * X2) *ᵥ θ) u ε ρ lam :=
  gnsDes_iff_gnsMat Wswap X2 y u ε β θ ρ lam

/-- The nesting theorem at `n = 2`, `k = 1`, with an explicit design matrix. -/
example (y u ε : Vec 2) (β : Vec 1) (ρ : ℝ) :
    GNSDes Wswap X2 y β 0 u ε ρ 0 ↔ (SARDes Wswap X2 y β ε ρ ∧ u = ε) :=
  gnsDes_iff_sarDes Wswap X2 y u ε β ρ

/-- The design-matrix SAR reduced-form theorem at `n = 2`, `k = 1`. -/
example (y ε : Vec 2) (β : Vec 1) (h : IsUnit (1 - (1/2 : ℝ) • Wswap)) :
    SARDes Wswap X2 y β ε (1/2) ↔ y = ↑(h.unit⁻¹) *ᵥ (X2 *ᵥ β + ε) :=
  sarDes_iff_reducedForm Wswap X2 y ε β (1/2) h

/-! ### A degenerate one-region model, computed by `norm_num` -/

/-- With one region and `W = 1`, the SAR operator is `1 - (1/2) • 1 = (1/2) • 1`. -/
example : (1 - (1/2 : ℝ) • (1 : WMat 1)) = (1/2 : ℝ) • (1 : WMat 1) := by
  ext i j
  fin_cases i
  fin_cases j
  norm_num [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]

/-! ### The full GNS reduced form over the two-region model -/

/-- **Explicit-inverse GNS reduced form at `n = 2`, `k = 1`.** With `W = Wswap`
and `ρ = λ = 1/2`, both `1 - ρW` and `1 - λW` are `1 - (1/2)•Wswap`, whose
two-sided inverse is `WswapInv` (`wswapInv_spec`). -/
example (y u ε : Vec 2) (β θ : Vec 1) :
    GNSDes Wswap X2 y β θ u ε (1/2) (1/2) ↔
      (u = WswapInv *ᵥ ε ∧
       y = WswapInv *ᵥ (X2 *ᵥ β + (Wswap * X2) *ᵥ θ + WswapInv *ᵥ ε)) :=
  gnsDes_iff_reducedForm_of_inverse Wswap X2 y β θ u ε (1/2) (1/2)
    WswapInv WswapInv wswapInv_spec.1 wswapInv_spec.2 wswapInv_spec.1 wswapInv_spec.2

/-- The `IsUnit` form of the same theorem, at `n = 2`, `k = 1`. -/
example (y u ε : Vec 2) (β θ : Vec 1) (h : IsUnit (1 - (1/2 : ℝ) • Wswap)) :
    GNSDes Wswap X2 y β θ u ε (1/2) (1/2) ↔
      (u = ↑(h.unit⁻¹) *ᵥ ε ∧
       y = ↑(h.unit⁻¹) *ᵥ (X2 *ᵥ β + (Wswap * X2) *ᵥ θ + ↑(h.unit⁻¹) *ᵥ ε)) :=
  gnsDes_iff_reducedForm Wswap X2 y β θ u ε (1/2) (1/2) h h

/-- The two equations of the reduced form, computed by `norm_num`: with
`β = ![3]`, `θ = ![-1]`, `ε = ![1, 1]` the disturbance is `u = ![2, 2]` and the
outcome is `y = ![26/3, 34/3]`. -/
theorem wswap_gns_reducedForm_values :
    WswapInv *ᵥ (![1, 1] : Vec 2) = ![2, 2] ∧
      WswapInv *ᵥ (X2 *ᵥ (![3] : Vec 1) + (Wswap * X2) *ᵥ (![-1] : Vec 1)
        + WswapInv *ᵥ (![1, 1] : Vec 2)) = ![26/3, 34/3] := by
  rw [wswap_mul_X2]
  refine ⟨?_, ?_⟩ <;>
    · ext i
      fin_cases i <;>
        rw [Matrix.mulVec_apply_eq_sum] <;>
        simp [WswapInv, X2, Fin.sum_univ_two, Matrix.mulVec_apply_eq_sum] <;>
        norm_num

/-- The determinant hypothesis of `gnsDes_iff_reducedForm_of_det_ne_zero`: here
`det (1 - (1/2)•Wswap) = 3/4`. -/
theorem wswap_det_ne_zero : (1 - (1/2 : ℝ) • Wswap).det ≠ 0 := by
  rw [Matrix.det_fin_two]
  simp [Wswap, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
  norm_num

/-- The determinant form of the full GNS reduced form, at `n = 2`, `k = 1`. -/
example (y u ε : Vec 2) (β θ : Vec 1) :
    GNSDes Wswap X2 y β θ u ε (1/2) (1/2) ↔
      (u = ((1 - (1/2 : ℝ) • Wswap)⁻¹ : WMat 2) *ᵥ ε ∧
       y = ((1 - (1/2 : ℝ) • Wswap)⁻¹ : WMat 2) *ᵥ
             (X2 *ᵥ β + (Wswap * X2) *ᵥ θ
               + ((1 - (1/2 : ℝ) • Wswap)⁻¹ : WMat 2) *ᵥ ε)) :=
  gnsDes_iff_reducedForm_of_det_ne_zero Wswap X2 y β θ u ε (1/2) (1/2)
    wswap_det_ne_zero wswap_det_ne_zero

/-- The `λ = 0` restriction: the SDM reduced form, at `n = 2`, `k = 1`. -/
example (y ε : Vec 2) (β θ : Vec 1) (h : IsUnit (1 - (1/2 : ℝ) • Wswap)) :
    SDMDes Wswap X2 y β θ ε (1/2) ↔
      y = ↑(h.unit⁻¹) *ᵥ (X2 *ᵥ β + (Wswap * X2) *ᵥ θ + ε) :=
  sdmDes_iff_reducedForm Wswap X2 y ε β θ (1/2) h

/-! ### Spatial weights: an island (§ "positive-row and island cases tested
independently") -/

/-- A 2×2 **island** example: region `0` has no neighbours, region `1` points at
region `0` and already carries unit weight. -/
def Wisland : WMat 2 := !![0, 0; 1, 0]

theorem wisland_nonneg : Nonneg Wisland := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [Wisland]

theorem wisland_zeroDiag : ZeroDiag Wisland := by
  intro i
  fin_cases i <;> norm_num [Wisland]

theorem wisland_island : Island Wisland 0 := by
  intro j
  fin_cases j <;> norm_num [Wisland]

theorem wisland_not_island_one : ¬ Island Wisland 1 := by
  intro h
  have := h 0
  norm_num [Wisland] at this

theorem wisland_rowSubstochastic : RowSubstochastic Wisland := by
  intro i
  fin_cases i <;> norm_num [Wisland, rowSum, Fin.sum_univ_two]

/-- The island makes the weights non-stochastic: row `0` sums to `0`, not `1`. -/
theorem wisland_not_rowStochastic : ¬ RowStochastic Wisland :=
  not_rowStochastic_of_island Wisland wisland_island

/-- Normalizing weights that contain an island changes nothing: the zero row is
carried to a zero row rather than dividing by zero. -/
theorem normalize_wisland : GeoDa.normalize Wisland = Wisland := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Wisland, GeoDa.normalize, rowSum, Fin.sum_univ_two]

/-- Consequently the normalized matrix is still not row-stochastic. -/
example : ¬ RowStochastic (GeoDa.normalize Wisland) := by
  rw [rowStochastic_normalize_iff Wisland wisland_nonneg]
  exact fun h => h 0 wisland_island

/-! ### Spatial weights: positive rows -/

/-- The symmetric two-region swap matrix `Wswap` is row-stochastic (defined
above under "explicit data"). -/
theorem wswap_rowStochastic : RowStochastic Wswap := by
  intro i
  fin_cases i <;> norm_num [Wswap, rowSum, Fin.sum_univ_two]

theorem wswap_nonneg : Nonneg Wswap := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [Wswap]

theorem wswap_zeroDiag : ZeroDiag Wswap := by
  intro i
  fin_cases i <;> norm_num [Wswap]

/-- The row-sum identity, realized as a matrix–vector product. -/
example : Wswap *ᵥ (1 : Vec 2) = 1 :=
  (rowStochastic_iff_mulVec_one Wswap).mp wswap_rowStochastic

/-- Normalizing already row-stochastic weights is the identity. -/
theorem normalize_wswap : GeoDa.normalize Wswap = Wswap := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Wswap, GeoDa.normalize, rowSum, Fin.sum_univ_two]

/-- Nonnegative weights whose rows are *not* normalized: rows sum to `3` and `7`. -/
def Wpos : WMat 2 := !![1, 2; 3, 4]

theorem wpos_nonneg : Nonneg Wpos := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [Wpos]

/-- Normalization turns positive rows into unit rows. -/
theorem wpos_normalize_rowStochastic : RowStochastic (GeoDa.normalize Wpos) :=
  (rowStochastic_normalize_iff_pos Wpos wpos_nonneg).mpr
    (by intro i; fin_cases i <;> norm_num [Wpos, rowSum, Fin.sum_univ_two])

/-- The normalized positive-row matrix in explicit form: rows `[1/3, 2/3]` and
`[3/7, 4/7]`. -/
theorem normalize_wpos : GeoDa.normalize Wpos = !![1/3, 2/3; 3/7, 4/7] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Wpos, GeoDa.normalize, rowSum, Fin.sum_univ_two]

/-! ### Independence of row standardization and a zero diagonal -/

/-- Row standardization does **not** imply a zero diagonal: the identity is
row-stochastic with diagonal `1`. -/
example : RowStochastic (1 : WMat 2) ∧ ¬ ZeroDiag (1 : WMat 2) :=
  ⟨rowStochastic_one, not_zeroDiag_one 0⟩

/-- A zero diagonal does **not** imply row standardization: region `1` has no
neighbours at all here, even though no region is its own neighbour. -/
def Wnotdiag : WMat 2 := !![0, 1; 0, 0]

theorem wnotdiag_zeroDiag : ZeroDiag Wnotdiag := by
  intro i
  fin_cases i <;> norm_num [Wnotdiag]

theorem wnotdiag_not_rowStochastic : ¬ RowStochastic Wnotdiag := by
  intro h
  have h1 := h 1
  norm_num [Wnotdiag, rowSum, Fin.sum_univ_two] at h1

/-- `ZeroDiag` and `RowStochastic` are therefore logically independent, and
neither is assumed by the other anywhere in the development. -/
example : ZeroDiag Wnotdiag ∧ ¬ RowStochastic Wnotdiag :=
  ⟨wnotdiag_zeroDiag, wnotdiag_not_rowStochastic⟩

/-! ### Invertibility of the spatial multiplier `1 - ρW` -/

/-- Row-stochastic nonnegative weights: `1 - ρW` is a unit for `|ρ| < 1`, with no
`IsUnit` hypothesis anywhere. -/
example (ρ : ℝ) (hρ : |ρ| < 1) : IsUnit (1 - ρ • Wswap) :=
  isUnit_one_sub_smul_of_rowStochastic Wswap wswap_nonneg wswap_rowStochastic ρ hρ

/-- **Island weights.** A zero row is allowed: row-substochasticity is enough, and
`Wisland` has row sums `0` and `1`. -/
example (ρ : ℝ) (hρ : |ρ| < 1) : IsUnit (1 - ρ • Wisland) :=
  isUnit_one_sub_smul_of_rowSubstochastic Wisland wisland_nonneg wisland_rowSubstochastic ρ hρ

/-- The SAR reduced form at `n = 2` with the invertibility hypothesis *derived*
from the weights rather than assumed. -/
example (y xb ε : Vec 2) :
    SARMat Wswap y xb ε (1/2) ↔ y = ((1 - (1/2 : ℝ) • Wswap)⁻¹ : WMat 2) *ᵥ (xb + ε) :=
  sarMat_iff_reducedForm_of_rowSubstochastic Wswap wswap_nonneg
    (rowSubstochastic_of_rowStochastic Wswap wswap_rowStochastic)
    (1/2) (by norm_num) y xb ε

/-- **Counterexample 1 — nonnegativity alone is not enough.** `2 • 1` is
nonnegative, but its rows sum to `2`, and at `ρ = 1/2` the multiplier is
`1 - (1/2)·2·1 = 0`. -/
def Wtwo : WMat 2 := (2 : ℝ) • (1 : WMat 2)

theorem wtwo_nonneg : Nonneg Wtwo := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Wtwo, Matrix.smul_apply, Matrix.one_apply]

theorem wtwo_not_rowSubstochastic : ¬ RowSubstochastic Wtwo := by
  intro h
  have h0 := h 0
  norm_num [Wtwo, rowSum, Fin.sum_univ_two, Matrix.smul_apply, Matrix.one_apply] at h0

theorem wtwo_not_isUnit : ¬ IsUnit (1 - (1/2 : ℝ) • Wtwo) := by
  have h : (1 - (1/2 : ℝ) • Wtwo : WMat 2) = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Wtwo, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
  rw [h]
  exact not_isUnit_zero

/-- **Counterexample 2 — row-substochasticity alone is not enough either.**
`!![2, -1; 0, 0]` has row sums `1` and `0`, but a negative entry, and at
`ρ = 1/2` the multiplier is the singular `!![0, 1/2; 0, 1]`. -/
def Wneg : WMat 2 := !![2, -1; 0, 0]

theorem wneg_rowSubstochastic : RowSubstochastic Wneg := by
  intro i
  fin_cases i <;> norm_num [Wneg, rowSum, Fin.sum_univ_two]

theorem wneg_not_nonneg : ¬ Nonneg Wneg := by
  intro h
  have h01 := h 0 1
  norm_num [Wneg] at h01

theorem wneg_multiplier : (1 - (1/2 : ℝ) • Wneg : WMat 2) = !![0, 1/2; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Wneg, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]

theorem wneg_det_zero : (1 - (1/2 : ℝ) • Wneg).det = 0 := by
  rw [wneg_multiplier, Matrix.det_fin_two]
  norm_num

theorem wneg_not_isUnit : ¬ IsUnit (1 - (1/2 : ℝ) • Wneg) := by
  rw [Matrix.isUnit_iff_isUnit_det, wneg_det_zero]
  exact not_isUnit_zero

end GeoDaTest
