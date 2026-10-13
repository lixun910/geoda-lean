/-
Copyright (c) 2026 GeoDa-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import GeoDa
import GeoDaTest.AgentTasks
import GeoDaTest.HeteroRho
import GeoDaTest.Sdem
import GeoDaTest.DSL

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

-- GeoDa.Multiplier: invertibility of 1 - ρW under weights assumptions
#print axioms GeoDa.abs_mulVec_apply_le_norm
#print axioms GeoDa.norm_mulVec_le
#print axioms GeoDa.mulVec_injective_one_sub_smul
#print axioms GeoDa.isUnit_one_sub_smul_of_rowSubstochastic
#print axioms GeoDa.isUnit_one_sub_smul_of_rowStochastic
#print axioms GeoDa.sarMat_iff_reducedForm_of_rowSubstochastic
#print axioms GeoDa.semMat_iff_reducedForm_of_rowSubstochastic

-- GeoDa.RandomVector: expectation, covariance and the model moments
#print axioms GeoDa.rvExp_const
#print axioms GeoDa.integrable_mulVec
#print axioms GeoDa.rvExp_mulVec
#print axioms GeoDa.rvExp_affine
#print axioms GeoDa.rvCenter_mulVec
#print axioms GeoDa.integrable_center_mul
#print axioms GeoDa.integral_double_sum_mul
#print axioms GeoDa.sum_sum_mul_mul_eq
#print axioms GeoDa.rvCov_mulVec
#print axioms GeoDa.rvCenter_affine
#print axioms GeoDa.rvCov_affine
#print axioms GeoDa.HasMoments.mulVec
#print axioms GeoDa.HasMoments.add_const
#print axioms GeoDa.HasMoments.mulVec_add
#print axioms GeoDa.affine_moments
#print axioms GeoDa.linear_moments
#print axioms GeoDa.sar_moments
#print axioms GeoDa.sem_moments
#print axioms GeoDa.gns_moments

-- GeoDaTest.DSL: the `spatial_model` DSL agrees with the hand-written specifications
#print axioms GeoDaTest.mySAR_eq_SARDes
#print axioms GeoDaTest.mySDM_eq_SDMDes
#print axioms GeoDaTest.mySEM_eq_SEMDes
#print axioms GeoDaTest.myGNS_eq_GNSDes
#print axioms GeoDaTest.mySLX_iff

-- GeoDa.Nesting and GeoDa.Multiplier: SLX, and the transposed multiplier
#print axioms GeoDa.gnsDes_iff_slxDes
#print axioms GeoDa.rowSum_transpose
#print axioms GeoDa.isUnit_one_sub_smul_transpose_of_colSubstochastic

-- GeoDaTest.AgentTasks: the refuted conjectures of the agent-loop benchmark
#print axioms GeoDaTest.nonneg_alone_is_not_enough
#print axioms GeoDaTest.rowSubstochastic_alone_is_not_enough

-- GeoDa.HeteroRho: the heterogeneous-rho model, its reduced form and its identifiability
#print axioms GeoDa.diagMul_mulVec
#print axioms GeoDa.rowSum_diagMul
#print axioms GeoDa.abs_mulVec_diagMul_apply_le
#print axioms GeoDa.norm_mulVec_diagMul_le
#print axioms GeoDa.isUnit_one_sub_diagMul_of_rowSubstochastic
#print axioms GeoDa.heteroSARDes_iff_mulVec
#print axioms GeoDa.heteroSARDes_iff_reducedForm
#print axioms GeoDa.diagMul_update_island
#print axioms GeoDa.diagMul_injective_of_no_island
#print axioms GeoDa.diagMul_eq_of_reducedForm_eq
#print axioms GeoDa.heteroSAR_parameter_identified
#print axioms GeoDa.heteroSARDes_island_invariant
#print axioms GeoDa.heteroSAR_reducedForm_island_invariant
#print axioms GeoDaTest.wisland_two_rho_same_multiplier

-- GeoDa.Sdem: the P4.2 benchmark model, its nestings and its reduced form
#print axioms GeoDa.gnsDes_iff_sdemDes
#print axioms GeoDa.sdemDes_iff_slx_and_error
#print axioms GeoDa.sdemDes_iff_slxDes_of_lam_zero
#print axioms GeoDa.sdemDes_iff_semDes_of_theta_zero
#print axioms GeoDa.sdemDes_iff_mulVec
#print axioms GeoDa.sdemDes_iff_reducedForm
#print axioms GeoDa.sdemDes_iff_reducedForm_of_rowSubstochastic
#print axioms GeoDa.sdem_moments
#print axioms GeoDaTest.sdemViaDsl_eq_SDEMDes

-- Paper 1 semantic-review additions
#print axioms GeoDa.isUnit_one_sub_smul_of_colSubstochastic
#print axioms GeoDa.gnsDes_moments_of_rowSubstochastic
