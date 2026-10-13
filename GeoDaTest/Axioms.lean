/-
Copyright (c) 2026 GeoDa-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import GeoDa

/-!
# Axiom audit

`scripts/verify.sh` runs this file and checks that the axiom list of every main
theorem is the standard Lean/Mathlib trio and contains neither `sorryAx` nor any
user-introduced axiom.
-/

#print axioms GeoDa.gns_iff_sar
#print axioms GeoDa.gns_iff_sem
#print axioms GeoDa.gns_iff_sdm
#print axioms GeoDa.gnsMat_iff_sarMat
#print axioms GeoDa.gnsMat_iff_semMat
#print axioms GeoDa.gnsMat_iff_sdmMat
#print axioms GeoDa.sarMat_iff_mulVec
#print axioms GeoDa.semMat_iff_mulVec
#print axioms GeoDa.sarMat_iff_reducedForm
#print axioms GeoDa.semMat_iff_reducedForm
#print axioms GeoDa.sem_reducedForm_eq_sar_reducedForm_of_filtered
#print axioms GeoDa.reducedForm_eq_iff_inverse_eq_one

-- GeoDa.Design: the regressors formed from a design matrix
#print axioms GeoDa.design_wxθ_eq
#print axioms GeoDa.gnsDes_iff_gnsMat
#print axioms GeoDa.sarDes_iff_sarMat
#print axioms GeoDa.semDes_iff_semMat
#print axioms GeoDa.sdmDes_iff_sdmMat
#print axioms GeoDa.gnsDes_iff_sarDes
#print axioms GeoDa.gnsDes_iff_semDes
#print axioms GeoDa.gnsDes_iff_sdmDes
#print axioms GeoDa.sarDes_iff_mulVec
#print axioms GeoDa.semDes_iff_mulVec
#print axioms GeoDa.sarDes_iff_reducedForm
#print axioms GeoDa.semDes_iff_reducedForm
#print axioms GeoDa.semDes_reducedForm_eq_sarDes_reducedForm_of_filtered

-- GeoDa.ReducedForm: the full GNS reduced form
#print axioms GeoDa.one_sub_smul_mulVec_eq_iff
#print axioms GeoDa.mulVec_eq_of_mulVec_eq
#print axioms GeoDa.mulVec_eq_of_eq_mulVec
#print axioms GeoDa.mulVec_eq_iff
#print axioms GeoDa.gnsDes_iff_mulVec
#print axioms GeoDa.gnsDes_iff_reducedForm_of_inverse
#print axioms GeoDa.gnsDes_reducedForm
#print axioms GeoDa.reducedForm_gnsDes
#print axioms GeoDa.gnsDes_iff_reducedForm
#print axioms GeoDa.isUnit_iff_det_ne_zero
#print axioms GeoDa.gnsDes_iff_reducedForm_of_det_ne_zero
#print axioms GeoDa.sdmDes_iff_mulVec
#print axioms GeoDa.sdmDes_iff_reducedForm

-- GeoDa.SpatialWeights: weights predicates, row normalization, islands
#print axioms GeoDa.mulVec_one_apply
#print axioms GeoDa.rowStochastic_iff_mulVec_one
#print axioms GeoDa.rowSum_nonneg
#print axioms GeoDa.rowSubstochastic_of_rowStochastic
#print axioms GeoDa.rowSum_eq_zero_of_island
#print axioms GeoDa.island_iff_rowSum_eq_zero
#print axioms GeoDa.not_rowStochastic_of_island
#print axioms GeoDa.rowStochastic_one
#print axioms GeoDa.nonneg_one
#print axioms GeoDa.not_zeroDiag_one
#print axioms GeoDa.rowSum_normalize
#print axioms GeoDa.rowStochastic_normalize_of_ne_zero
#print axioms GeoDa.island_normalize
#print axioms GeoDa.nonneg_normalize
#print axioms GeoDa.zeroDiag_normalize
#print axioms GeoDa.rowSubstochastic_normalize
#print axioms GeoDa.rowStochastic_normalize_iff
#print axioms GeoDa.rowStochastic_normalize_iff_pos
