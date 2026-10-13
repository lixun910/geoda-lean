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

/-! ### A degenerate one-region model, computed by `norm_num` -/

/-- With one region and `W = 1`, the SAR operator is `1 - (1/2) • 1 = (1/2) • 1`. -/
example : (1 - (1/2 : ℝ) • (1 : WMat 1)) = (1/2 : ℝ) • (1 : WMat 1) := by
  ext i j
  fin_cases i
  fin_cases j
  norm_num [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]

end GeoDaTest
