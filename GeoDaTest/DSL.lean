/-
Copyright (c) 2026 GeoDa-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import GeoDa

/-!
# Tests for the `spatial_model` DSL

**Positive tests.** Models declared with `spatial_model` from the equation alone are
proved **definitionally equal** to the hand-written specifications in `GeoDa.Design`,
by `rfl`. That is the "equivalent to manually defined specifications" acceptance
criterion in its strongest form: not that the two agree as propositions, but that the
generated definitions *are* the manual ones, up to definitional equality. A model with
no counterpart in the repository is declared too, to show what the DSL is for.

**Negative tests.** `#guard_msgs` pins the exact message for each rejection, so the
test fails if the rejection stops happening, or stops being specific.
-/

open scoped Matrix

namespace GeoDaTest

open GeoDa

/-! ### The four models of `GeoDa.Design`, re-derived from the equation alone -/

-- SAR, declared by its equation.
spatial_model MySAR {n k : ℕ} (W : WMat n) (X : DMat n k) (y : Vec n) (β : Vec k)
    (ε : Vec n) (ρ : ℝ) : y = ρ • (W *ᵥ y) + X *ᵥ β + ε

/-- The generated SAR *is* `GeoDa.SARDes`. `rfl`, not a proof script: the two bodies
are definitionally equal, and so are the binder lists. -/
theorem mySAR_eq_SARDes : @MySAR = @SARDes := rfl

-- SDM, declared by its equation.
spatial_model MySDM {n k : ℕ} (W : WMat n) (X : DMat n k) (y : Vec n) (β : Vec k)
    (θ : Vec k) (ε : Vec n) (ρ : ℝ) : y = ρ • (W *ᵥ y) + X *ᵥ β + (W * X) *ᵥ θ + ε

theorem mySDM_eq_SDMDes : @MySDM = @SDMDes := rfl

-- SEM, declared by its *pair* of equations. The body of a `spatial_model` is one
-- `Prop`, so a two-equation model is written with `∧` — which is how `SEMDes` is
-- written too.
spatial_model MySEM {n k : ℕ} (W : WMat n) (X : DMat n k) (y : Vec n) (β : Vec k)
    (u : Vec n) (ε : Vec n) (lam : ℝ) : y = X *ᵥ β + u ∧ u = lam • (W *ᵥ u) + ε

theorem mySEM_eq_SEMDes : @MySEM = @SEMDes := rfl

-- GNS, declared by its pair of equations. Note `lam`, not `λ`: `λ` is Lean's lambda
-- token and can never be an identifier — one of the gotchas recorded in `CLAUDE.md`.
spatial_model MyGNS {n k : ℕ} (W : WMat n) (X : DMat n k) (y : Vec n) (β : Vec k)
    (θ : Vec k) (u : Vec n) (ε : Vec n) (ρ : ℝ) (lam : ℝ) :
  y = ρ • (W *ᵥ y) + X *ᵥ β + (W * X) *ᵥ θ + u ∧ u = lam • (W *ᵥ u) + ε

theorem myGNS_eq_GNSDes : @MyGNS = @GNSDes := rfl

/-- Consequently the DSL is transparent: a theorem about `GNSDes` applies to `MyGNS`
with no conversion at all. -/
example (W : WMat n) (X : DMat n k) (y : Vec n) (β : Vec k) (θ : Vec k) (u : Vec n)
    (ε : Vec n) (ρ lam : ℝ) : GNSDes W X y β θ u ε ρ lam ↔ MyGNS W X y β θ u ε ρ lam :=
  Iff.rfl

/-! ### A model that does not exist in this repository

The point of the DSL is that a *new* model costs one equation and no boilerplate. SLX
— `y = Xβ + WXθ + ε`, a spatial lag of the regressors with no lag of `y` and no spatial
error — has no counterpart in `GeoDa`, and defining it here touches no existing file. -/

spatial_model MySLX {n k : ℕ} (W : WMat n) (X : DMat n k) (y : Vec n) (β : Vec k)
    (θ : Vec k) (ε : Vec n) : y = X *ᵥ β + (W * X) *ᵥ θ + ε

/-- And it is immediately usable: SLX holds exactly when `y` equals the augmented
design times its coefficients. -/
theorem mySLX_iff (W : WMat n) (X : DMat n k) (y : Vec n) (β : Vec k) (θ : Vec k)
    (ε : Vec n) : MySLX W X y β θ ε ↔ y = X *ᵥ β + (W * X) *ᵥ θ + ε :=
  Iff.rfl

/-! ### Negative tests

Each of these must be *rejected*, and rejected with the message asserted here.
`#guard_msgs` compares the docstring against what the command actually emitted, so a
rejection that quietly stopped happening — or stopped being specific — fails the build.
-/

/-- error: spatial_model: the slot X has row dimension n, but W fixes the row dimension to m; every vector and matrix slot of a spatial model must have the same row dimension -/
#guard_msgs in
spatial_model BadDims {n m k : ℕ} (W : WMat m) (X : DMat n k) (y : Vec n) (β : Vec k)
    (ε : Vec n) : y = X *ᵥ β + ε

/-- error: spatial_model: the vector slot v has dimension j, which is neither the row dimension n nor the coefficient dimension k -/
#guard_msgs in
spatial_model BadVecDim {n k j : ℕ} (W : WMat n) (X : DMat n k) (y : Vec n) (β : Vec k)
    (ε : Vec n) (v : Vec j) : y = X *ᵥ β + ε

/-- error: Unknown identifier `ρ` -/
#guard_msgs in
spatial_model BadUndeclared {n k : ℕ} (W : WMat n) (X : DMat n k) (y : Vec n)
    (β : Vec k) (ε : Vec n) : y = ρ • (W *ᵥ y) + X *ᵥ β + ε

/-- error: Type mismatch
  y
has type
  Vec n
but is expected to have type
  ℝ -/
#guard_msgs in
spatial_model BadType {n : ℕ} (y : Vec n) (ρ : ℝ) : ρ = y

end GeoDaTest
