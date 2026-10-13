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
