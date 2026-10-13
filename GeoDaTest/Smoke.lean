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
theorem normalize_wisland : normalize Wisland = Wisland := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Wisland, normalize, rowSum, Fin.sum_univ_two]

/-- Consequently the normalized matrix is still not row-stochastic. -/
example : ¬ RowStochastic (normalize Wisland) := by
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
theorem normalize_wswap : normalize Wswap = Wswap := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Wswap, normalize, rowSum, Fin.sum_univ_two]

/-- Nonnegative weights whose rows are *not* normalized: rows sum to `3` and `7`. -/
def Wpos : WMat 2 := !![1, 2; 3, 4]

theorem wpos_nonneg : Nonneg Wpos := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [Wpos]

/-- Normalization turns positive rows into unit rows. -/
theorem wpos_normalize_rowStochastic : RowStochastic (normalize Wpos) :=
  (rowStochastic_normalize_iff_pos Wpos wpos_nonneg).mpr
    (by intro i; fin_cases i <;> norm_num [Wpos, rowSum, Fin.sum_univ_two])

/-- The normalized positive-row matrix in explicit form: rows `[1/3, 2/3]` and
`[3/7, 4/7]`. -/
theorem normalize_wpos : normalize Wpos = !![1/3, 2/3; 3/7, 4/7] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Wpos, normalize, rowSum, Fin.sum_univ_two]

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

end GeoDaTest
