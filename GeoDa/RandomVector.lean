/-
Copyright (c) 2026 GeoDa-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import GeoDa.SpatialWeights
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Random vectors: expectation and covariance

Everything before this file is deterministic. `GeoDa.GNS` and its relatives are
statements about *model equations* — they say nothing about probability
distributions, and their docstrings say so. This file starts the probability
layer, keeping the two strictly apart:

* `Ω` is a measurable space with a probability measure `μ`;
* a **random vector** is an ordinary function `ξ : Ω → Vec n`, i.e. `Ω → Fin n → ℝ`;
* `X`, `W`, `β`, `θ`, `ρ`, `λ` stay **deterministic** — they are the same objects
  as everywhere else in the repository and never become random;
* only `ε`, and the `u` and `y` built from it, are random.

Expectation is defined **coordinatewise**,
`(rvExp μ ξ) i = ∫ ω, ξ ω i ∂μ`, and covariance likewise,
`(rvCov μ ξ) i j = ∫ ω, (ξ ω i - Eξ i) * (ξ ω j - Eξ j) ∂μ`.
Defining them coordinatewise is what keeps this file elementary: every integral
below is a real-valued Lebesgue integral, so no Bochner integral in a normed
space, no `ContinuousLinearMap` commutation lemma and no matrix norm is
involved. For a finite index type the coordinatewise expectation *is* the
Bochner integral, but nothing here needs that fact.

## Integrability is assumed, never implied

The hypotheses are stated, not smuggled in. `rvExp_mulVec` assumes each
coordinate of `ξ` is integrable; `rvCov_mulVec` assumes in addition that each
product of two coordinates is integrable. Nothing is claimed about a random
vector whose moments do not exist, and no measurability hypothesis is hidden
behind `integral_add` etc. — `Integrable` carries it.

## Main definitions

* `GeoDa.rvExp` : the expectation of a random vector.
* `GeoDa.rvCenter` : the centered random vector `ξ - Eξ`.
* `GeoDa.rvCov` : the covariance matrix, `Cov(ξ) i j = E[(ξ i - Eξ i)(ξ j - Eξ j)]`.

## Main results

* `GeoDa.rvExp_mulVec` : `E[Aξ] = A E[ξ]`.
* `GeoDa.rvExp_affine` : `E[Aξ + b] = A E[ξ] + b`.
* `GeoDa.rvCenter_mulVec` : centering commutes with `A`, `(Aξ) - E[Aξ] = A(ξ - Eξ)`.
* `GeoDa.rvCov_mulVec` : **`Cov(Aξ) = A Cov(ξ) Aᵀ`**.
* `GeoDa.rvCov_affine` : `Cov(Aξ + b) = A Cov(ξ) Aᵀ` — adding a constant changes
  nothing.

Note the transpose convention: the index that is summed is the *middle* one,
`(A Cov(ξ) Aᵀ) i j = ∑ k ∑ l, A i k Cov(ξ) k l A j l`, which is the usual
`A Cov(ξ) Aᵀ` of the spatial-econometrics literature.

What is **not** here: any distributional assumption. A mean-zero variance-`σ²`
innovation is specified by its first two moments alone, and no Gaussianity is
claimed or used. The multivariate normal innovation, and a likelihood built on
it, are a separate and strictly stronger claim.
-/

open scoped Matrix
open Matrix MeasureTheory

namespace GeoDa

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Expectation -/

/-- **Expectation of a random vector**, defined coordinatewise. -/
noncomputable def rvExp (μ : Measure Ω) (ξ : Ω → Vec n) : Vec n := fun i => ∫ ω, ξ ω i ∂μ

/-- The **centered** random vector `ξ - Eξ`. -/
noncomputable def rvCenter (μ : Measure Ω) (ξ : Ω → Vec n) : Ω → Vec n :=
  fun ω i => ξ ω i - rvExp μ ξ i

/-- **Covariance matrix**: `Cov(ξ) i j = E[(ξ i - Eξ i) * (ξ j - Eξ j)]`. -/
noncomputable def rvCov (μ : Measure Ω) (ξ : Ω → Vec n) : WMat n :=
  fun i j => ∫ ω, rvCenter μ ξ ω i * rvCenter μ ξ ω j ∂μ

variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A constant is integrable on a probability space, and its expectation is the
constant. -/
theorem rvExp_const (b : Vec n) : rvExp μ (fun _ : Ω => b) = b := by
  have hμ : μ.real Set.univ = 1 := by
    rw [measureReal_def, measure_univ, ENNReal.toReal_one]
  funext i
  show (∫ _ : Ω, b i ∂μ) = b i
  rw [integral_const, hμ, one_smul]

omit [IsProbabilityMeasure μ] in
/-- `A *ᵥ ξ` is integrable coordinatewise when `ξ` is. -/
theorem integrable_mulVec (ξ : Ω → Vec n) (A : WMat n)
    (hξ : ∀ i, Integrable (fun ω => ξ ω i) μ) (i : Fin n) :
    Integrable (fun ω => (A *ᵥ ξ ω) i) μ := by
  have hfun : (fun ω => (A *ᵥ ξ ω) i) = fun ω => ∑ j, A i j * ξ ω j := by
    funext ω
    rw [Matrix.mulVec_apply_eq_sum]
  rw [hfun]
  exact integrable_finsetSum Finset.univ (fun j _ => (hξ j).const_mul (A i j))

omit [IsProbabilityMeasure μ] in
/-- **Expectation is linear through a matrix**: `E[Aξ] = A E[ξ]`, provided each
coordinate of `ξ` is integrable. -/
theorem rvExp_mulVec (ξ : Ω → Vec n) (A : WMat n)
    (hξ : ∀ i, Integrable (fun ω => ξ ω i) μ) :
    rvExp μ (fun ω => A *ᵥ ξ ω) = A *ᵥ rvExp μ ξ := by
  funext i
  show (∫ ω, (A *ᵥ ξ ω) i ∂μ) = (A *ᵥ rvExp μ ξ) i
  have h1 : (∫ ω, (A *ᵥ ξ ω) i ∂μ) = ∫ ω, ∑ j, A i j * ξ ω j ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω => Matrix.mulVec_apply_eq_sum A (ξ ω) i)
  rw [h1, integral_finsetSum Finset.univ (fun j _ => (hξ j).const_mul (A i j)),
    Matrix.mulVec_apply_eq_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact integral_const_mul (A i j) (fun ω => ξ ω j)

/-- **Expectation of an affine function.** `E[Aξ + b] = A E[ξ] + b`. -/
theorem rvExp_affine (ξ : Ω → Vec n) (A : WMat n) (b : Vec n)
    (hξ : ∀ i, Integrable (fun ω => ξ ω i) μ) :
    rvExp μ (fun ω => A *ᵥ ξ ω + b) = A *ᵥ rvExp μ ξ + b := by
  have hsplit : rvExp μ (fun ω => A *ᵥ ξ ω + b)
      = rvExp μ (fun ω => A *ᵥ ξ ω) + rvExp μ (fun _ : Ω => b) := by
    funext i
    show (∫ ω, (A *ᵥ ξ ω + b) i ∂μ) = (∫ ω, (A *ᵥ ξ ω) i ∂μ) + (∫ ω, b i ∂μ)
    have h1 : (∫ ω, (A *ᵥ ξ ω + b) i ∂μ) = ∫ ω, ((A *ᵥ ξ ω) i + b i) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω => rfl)
    rw [h1, integral_add (integrable_mulVec ξ A hξ i) (integrable_const (b i))]
  rw [hsplit, rvExp_mulVec ξ A hξ, rvExp_const]

/-! ### Covariance -/

omit [IsProbabilityMeasure μ] in
/-- **Centering commutes with a linear map**: `(Aξ) - E[Aξ] = A (ξ - Eξ)`. -/
theorem rvCenter_mulVec (ξ : Ω → Vec n) (A : WMat n)
    (hξ : ∀ i, Integrable (fun ω => ξ ω i) μ) :
    rvCenter μ (fun ω => A *ᵥ ξ ω)
      = fun ω i => ∑ j, A i j * rvCenter μ ξ ω j := by
  funext ω i
  show (A *ᵥ ξ ω) i - rvExp μ (fun ω => A *ᵥ ξ ω) i
      = ∑ j, A i j * (ξ ω j - rvExp μ ξ j)
  rw [congrFun (rvExp_mulVec ξ A hξ) i, Matrix.mulVec_apply_eq_sum, Matrix.mulVec_apply_eq_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Products of centered coordinates are integrable, given the first and second
moments of `ξ`. -/
theorem integrable_center_mul (ξ : Ω → Vec n) (hξ : ∀ i, Integrable (fun ω => ξ ω i) μ)
    (hξ2 : ∀ i j, Integrable (fun ω => ξ ω i * ξ ω j) μ) (j l : Fin n) :
    Integrable (fun ω => rvCenter μ ξ ω j * rvCenter μ ξ ω l) μ := by
  have hfun : (fun ω => rvCenter μ ξ ω j * rvCenter μ ξ ω l)
      = fun ω => ξ ω j * ξ ω l - rvExp μ ξ l * ξ ω j - rvExp μ ξ j * ξ ω l
          + rvExp μ ξ j * rvExp μ ξ l := by
    funext ω
    simp only [rvCenter]
    ring
  rw [hfun]
  exact (((hξ2 j l).sub ((hξ j).const_mul _)).sub ((hξ l).const_mul _)).add (integrable_const _)

/-- **Integrating a product of two linear combinations.** For random vectors whose
coordinates have first and second moments,
`∫ (∑ j, A i j ξc j) * (∑ l, B k l ξc l) = ∑ j ∑ l, A i j B k l Cov(ξ) j l`,
where `ξc` is the centered `ξ`. -/
theorem integral_double_sum_mul (ξ : Ω → Vec n) (A B : WMat n)
    (hξ : ∀ i, Integrable (fun ω => ξ ω i) μ)
    (hξ2 : ∀ i j, Integrable (fun ω => ξ ω i * ξ ω j) μ) (i k : Fin n) :
    (∫ ω, (∑ j, A i j * rvCenter μ ξ ω j) * (∑ l, B k l * rvCenter μ ξ ω l) ∂μ)
      = ∑ j, ∑ l, A i j * B k l * rvCov μ ξ j l := by
  have hmul : ∀ ω, (∑ j, A i j * rvCenter μ ξ ω j) * (∑ l, B k l * rvCenter μ ξ ω l)
      = ∑ j, ∑ l, (A i j * B k l) * (rvCenter μ ξ ω j * rvCenter μ ξ ω l) := by
    intro ω
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hmul),
    integral_finsetSum Finset.univ (fun j _ => integrable_finsetSum Finset.univ
      (fun l _ => (integrable_center_mul ξ hξ hξ2 j l).const_mul _))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum Finset.univ
    (fun l _ => (integrable_center_mul ξ hξ hξ2 j l).const_mul (A i j * B k l))]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [integral_const_mul]
  rfl

/-- The double sum `∑ j ∑ l, A i j * A k l * C j l` is the matrix product
`(A * C * Aᵀ) i k`. -/
theorem sum_sum_mul_mul_eq (A C : WMat n) (i k : Fin n) :
    (∑ j, ∑ l, A i j * A k l * C j l) = (A * C * Aᵀ) i k := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

/-- **Covariance under a linear map: `Cov(Aξ) = A Cov(ξ) Aᵀ`.**

The transpose convention matters here: the summed index is the middle one, so
`(A Cov(ξ) Aᵀ) i k = ∑ j ∑ l, A i j Cov(ξ) j l A k l`. No symmetry of `Cov(ξ)` is
used or needed. -/
theorem rvCov_mulVec (ξ : Ω → Vec n) (A : WMat n)
    (hξ : ∀ i, Integrable (fun ω => ξ ω i) μ)
    (hξ2 : ∀ i j, Integrable (fun ω => ξ ω i * ξ ω j) μ) :
    rvCov μ (fun ω => A *ᵥ ξ ω) = A * rvCov μ ξ * Aᵀ := by
  have hcw : rvCov μ (fun ω => A *ᵥ ξ ω)
      = fun i k => ∫ ω, (∑ j, A i j * rvCenter μ ξ ω j)
          * (∑ l, A k l * rvCenter μ ξ ω l) ∂μ := by
    funext i k
    show (∫ ω, rvCenter μ (fun ω => A *ᵥ ξ ω) ω i
        * rvCenter μ (fun ω => A *ᵥ ξ ω) ω k ∂μ)
      = ∫ ω, (∑ j, A i j * rvCenter μ ξ ω j) * (∑ l, A k l * rvCenter μ ξ ω l) ∂μ
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by
      show rvCenter μ (fun ω => A *ᵥ ξ ω) ω i * rvCenter μ (fun ω => A *ᵥ ξ ω) ω k
        = (∑ j, A i j * rvCenter μ ξ ω j) * (∑ l, A k l * rvCenter μ ξ ω l)
      rw [congrFun (congrFun (rvCenter_mulVec ξ A hξ) ω) i,
        congrFun (congrFun (rvCenter_mulVec ξ A hξ) ω) k])
  rw [hcw]
  funext i k
  rw [integral_double_sum_mul ξ A A hξ hξ2 i k]
  exact sum_sum_mul_mul_eq A (rvCov μ ξ) i k

/-- **Centering commutes with an affine map**: `(Aξ + b) - E[Aξ + b] = A(ξ - Eξ)`;
the constant cancels. -/
theorem rvCenter_affine (ξ : Ω → Vec n) (A : WMat n) (b : Vec n)
    (hξ : ∀ i, Integrable (fun ω => ξ ω i) μ) :
    rvCenter μ (fun ω => A *ᵥ ξ ω + b) = rvCenter μ (fun ω => A *ᵥ ξ ω) := by
  funext ω i
  show (A *ᵥ ξ ω + b) i - rvExp μ (fun ω => A *ᵥ ξ ω + b) i
      = (A *ᵥ ξ ω) i - rvExp μ (fun ω => A *ᵥ ξ ω) i
  rw [congrFun (rvExp_affine ξ A b hξ) i, congrFun (rvExp_mulVec ξ A hξ) i]
  show (A *ᵥ ξ ω + b) i - ((A *ᵥ rvExp μ ξ) i + b i)
      = (A *ᵥ ξ ω) i - (A *ᵥ rvExp μ ξ) i
  simp only [Pi.add_apply]
  ring

/-- **Covariance ignores the constant: `Cov(Aξ + b) = A Cov(ξ) Aᵀ`.** -/
theorem rvCov_affine (ξ : Ω → Vec n) (A : WMat n) (b : Vec n)
    (hξ : ∀ i, Integrable (fun ω => ξ ω i) μ)
    (hξ2 : ∀ i j, Integrable (fun ω => ξ ω i * ξ ω j) μ) :
    rvCov μ (fun ω => A *ᵥ ξ ω + b) = A * rvCov μ ξ * Aᵀ := by
  have hcov : rvCov μ (fun ω => A *ᵥ ξ ω + b) = rvCov μ (fun ω => A *ᵥ ξ ω) := by
    unfold rvCov
    funext i k
    rw [rvCenter_affine ξ A b hξ]
  rw [hcov, rvCov_mulVec ξ A hξ hξ2]

/-! ### Moments of the spatial models -/

/-- `HasMoments μ ξ`: every coordinate of `ξ` is integrable, and so is every
product of two coordinates. This is exactly what `rvExp` and `rvCov` need, stated
once so that the model theorems below do not each carry `2n²` hypotheses. -/
def HasMoments (μ : Measure Ω) (ξ : Ω → Vec n) : Prop :=
  (∀ i, Integrable (fun ω => ξ ω i) μ) ∧ (∀ i j, Integrable (fun ω => ξ ω i * ξ ω j) μ)

omit [IsProbabilityMeasure μ] in
/-- A linear image `Aξ` has moments when `ξ` does. -/
theorem HasMoments.mulVec {ξ : Ω → Vec n} (h : HasMoments μ ξ) (A : WMat n) :
    HasMoments μ (fun ω => A *ᵥ ξ ω) := by
  refine ⟨fun i => integrable_mulVec ξ A h.1 i, fun i j => ?_⟩
  have hfun : (fun ω => (A *ᵥ ξ ω) i * (A *ᵥ ξ ω) j)
      = fun ω => ∑ k, ∑ l, (A i k * A j l) * (ξ ω k * ξ ω l) := by
    funext ω
    rw [Matrix.mulVec_apply_eq_sum, Matrix.mulVec_apply_eq_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [hfun]
  exact integrable_finsetSum Finset.univ fun k _ =>
    integrable_finsetSum Finset.univ fun l _ => (h.2 k l).const_mul (A i k * A j l)

/-- A translated vector has moments when the vector does. -/
theorem HasMoments.add_const {ξ : Ω → Vec n} (h : HasMoments μ ξ) (b : Vec n) :
    HasMoments μ (fun ω => ξ ω + b) := by
  refine ⟨fun i => ?_, fun i j => ?_⟩
  · have hfun : (fun ω => (ξ ω + b) i) = fun ω => ξ ω i + b i := by
      funext ω; rw [Pi.add_apply]
    rw [hfun]
    exact (h.1 i).add (integrable_const _)
  · have hfun : (fun ω => (ξ ω + b) i * (ξ ω + b) j)
        = fun ω => ξ ω i * ξ ω j + b j * ξ ω i + b i * ξ ω j + b i * b j := by
      funext ω
      simp only [Pi.add_apply]
      ring
    rw [hfun]
    exact (((h.2 i j).add ((h.1 i).const_mul _)).add ((h.1 j).const_mul _)).add
      (integrable_const _)

/-- `Aξ + b` has moments when `ξ` does. -/
theorem HasMoments.mulVec_add {ξ : Ω → Vec n} (h : HasMoments μ ξ) (A : WMat n) (b : Vec n) :
    HasMoments μ (fun ω => A *ᵥ ξ ω + b) :=
  (h.mulVec A).add_const b

/-- **White noise: mean-zero innovation with covariance `σ² I`.** This is the
entire content of "`ε` has mean `0` and covariance `σ² I`" — a first-moment and a
second-moment condition, and nothing more. No distributional shape is assumed, and
in particular **not** Gaussianity; the multivariate normal innovation would be a
strictly stronger, and separate, hypothesis. -/
def IsWhiteNoise (μ : Measure Ω) (ε : Ω → Vec n) (σ2 : ℝ) : Prop :=
  HasMoments μ ε ∧ rvExp μ ε = 0 ∧ rvCov μ ε = σ2 • (1 : WMat n)

/-- **Moments of an affine function of white noise.** `E[Aε + c] = c` and
`Cov(Aε + c) = σ² A Aᵀ`. The deterministic part `c` cancels from the covariance
entirely: this is why the regression term `Xβ` never appears in `Cov(ŷ)`. -/
theorem affine_moments {ε : Ω → Vec n} {σ2 : ℝ} (hε : IsWhiteNoise μ ε σ2)
    (A : WMat n) (c : Vec n) :
    rvExp μ (fun ω => A *ᵥ ε ω + c) = c ∧
      rvCov μ (fun ω => A *ᵥ ε ω + c) = σ2 • (A * Aᵀ) := by
  obtain ⟨hm, hmean, hvar⟩ := hε
  constructor
  · rw [rvExp_affine ε A c hm.1, hmean, mulVec_zero, zero_add]
  · rw [rvCov_affine ε A c hm.1 hm.2, hvar, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

/-- **SAR moments.** With `y = (1 - ρW)⁻¹ (Xβ + ε)` — the SAR reduced form of
`GeoDa.Design` and `GeoDa.Weights` — and `ε` white noise of variance `σ²`, the
outcome has mean `(1 - ρW)⁻¹ Xβ` and covariance `σ² A Aᵀ` with `A = (1 - ρW)⁻¹`.

Note that the lag is what puts `A` on *both* sides of the covariance. -/
theorem sar_moments {ε : Ω → Vec n} {σ2 : ℝ} (hε : IsWhiteNoise μ ε σ2)
    (A : WMat n) (xb : Vec n) :
    rvExp μ (fun ω => A *ᵥ (xb + ε ω)) = A *ᵥ xb ∧
      rvCov μ (fun ω => A *ᵥ (xb + ε ω)) = σ2 • (A * Aᵀ) := by
  have hfun : (fun ω => A *ᵥ (xb + ε ω)) = fun ω => A *ᵥ ε ω + A *ᵥ xb := by
    funext ω; rw [Matrix.mulVec_add, add_comm]
  rw [hfun]
  exact affine_moments hε A (A *ᵥ xb)

/-- **Moments of a linear function of white noise**, the `c = 0` case of
`affine_moments`. -/
theorem linear_moments {ε : Ω → Vec n} {σ2 : ℝ} (hε : IsWhiteNoise μ ε σ2) (A : WMat n) :
    rvExp μ (fun ω => A *ᵥ ε ω) = 0 ∧ rvCov μ (fun ω => A *ᵥ ε ω) = σ2 • (A * Aᵀ) := by
  have h := affine_moments hε A 0
  exact ⟨by simpa using h.1, by simpa using h.2⟩

/-- **SEM moments.** With `u = (1 - λW)⁻¹ ε` and `y = Xβ + u`, the latent
disturbance is mean zero with covariance `σ² B Bᵀ` for `B = (1 - λW)⁻¹`, and the
outcome has the *same* covariance: `Cov(y) = Cov(u)`, the regressors contributing
nothing. -/
theorem sem_moments {ε : Ω → Vec n} {σ2 : ℝ} (hε : IsWhiteNoise μ ε σ2)
    (B : WMat n) (xb : Vec n) :
    rvExp μ (fun ω => B *ᵥ ε ω) = 0 ∧
      rvCov μ (fun ω => B *ᵥ ε ω) = σ2 • (B * Bᵀ) ∧
      rvExp μ (fun ω => xb + B *ᵥ ε ω) = xb ∧
      rvCov μ (fun ω => xb + B *ᵥ ε ω) = σ2 • (B * Bᵀ) := by
  have hzero := linear_moments hε B
  have hxb := affine_moments (ε := ε) hε B xb
  have hfun : (fun ω => xb + B *ᵥ ε ω) = fun ω => B *ᵥ ε ω + xb := by
    funext ω; rw [add_comm]
  exact ⟨hzero.1, hzero.2, by rw [hfun]; exact hxb.1, by rw [hfun]; exact hxb.2⟩

/-- **GNS moments.** With `u = Bε` and `y = A(γ + Bε)`, where `γ := Xβ + WXθ` is
the deterministic part and `A = (1 - ρW)⁻¹`, `B = (1 - λW)⁻¹` — the full GNS reduced
form of `GeoDa.ReducedForm` — the disturbance is mean zero with covariance
`σ² B Bᵀ`, and the outcome has mean `Aγ` and covariance `σ² (AB)(AB)ᵀ`.

The nesting shows up in the covariance: the spatial-error multiplier `B` enters
on both sides, and the lag multiplier `A` is applied on top. -/
theorem gns_moments {ε : Ω → Vec n} {σ2 : ℝ} (hε : IsWhiteNoise μ ε σ2)
    (A B : WMat n) (γ : Vec n) :
    rvExp μ (fun ω => B *ᵥ ε ω) = 0 ∧
      rvCov μ (fun ω => B *ᵥ ε ω) = σ2 • (B * Bᵀ) ∧
      rvExp μ (fun ω => A *ᵥ (γ + B *ᵥ ε ω)) = A *ᵥ γ ∧
      rvCov μ (fun ω => A *ᵥ (γ + B *ᵥ ε ω)) = σ2 • ((A * B) * (A * B)ᵀ) := by
  have hzero := linear_moments hε B
  have hAB : (fun ω => A *ᵥ (γ + B *ᵥ ε ω)) = fun ω => (A * B) *ᵥ ε ω + A *ᵥ γ := by
    funext ω
    rw [Matrix.mulVec_add, mulVec_mulVec, add_comm]
  have hall := affine_moments (ε := ε) hε (A * B) (A *ᵥ γ)
  exact ⟨hzero.1, hzero.2, by rw [hAB]; exact hall.1, by rw [hAB]; exact hall.2⟩

end GeoDa
