import GeoDa.Multiplier
import GeoDa.RandomVector

/-! # Structural GNS equations imply moments

A pointwise structural hypothesis connects the existing algebra and probability
layers. This theorem does not assume or prove Gaussianity or statistical identification.
-/

open scoped Matrix
open Matrix MeasureTheory

namespace GeoDa

/-- GNS moments from structural equations and explicit weights bounds.
The structural equations hold at every sample point, not merely almost everywhere. -/
theorem gnsDes_moments_of_rowSubstochastic
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (W : WMat n) (X : DMat n k) (β θ : Vec k)
    (ρ lam : ℝ) (hW : Nonneg W) (h1 : RowSubstochastic W)
    (hρ : |ρ| < 1) (hlam : |lam| < 1)
    (y u ε : Ω → Vec n) (σ2 : ℝ) (hε : IsWhiteNoise μ ε σ2)
    (hmodel : ∀ ω, GNSDes W X (y ω) β θ (u ω) (ε ω) ρ lam) :
    let A : WMat n := (1 - ρ • W)⁻¹
    let B : WMat n := (1 - lam • W)⁻¹
    rvExp μ u = 0 ∧ rvCov μ u = σ2 • (B * Bᵀ) ∧
    rvExp μ y = A *ᵥ (X *ᵥ β + (W * X) *ᵥ θ) ∧
    rvCov μ y = σ2 • ((A * B) * (A * B)ᵀ) := by
  have hA := (isUnit_iff_det_ne_zero (1 - ρ • W)).mp
    (isUnit_one_sub_smul_of_rowSubstochastic W hW h1 ρ hρ)
  have hB := (isUnit_iff_det_ne_zero (1 - lam • W)).mp
    (isUnit_one_sub_smul_of_rowSubstochastic W hW h1 lam hlam)
  have hred := fun ω => (gnsDes_iff_reducedForm_of_det_ne_zero
    W X (y ω) β θ (u ω) (ε ω) ρ lam hA hB).mp (hmodel ω)
  have hu : u = fun ω => ((1 - lam • W)⁻¹ : WMat n) *ᵥ ε ω :=
    funext fun ω => (hred ω).1
  have hy : y = fun ω => ((1 - ρ • W)⁻¹ : WMat n) *ᵥ
      (X *ᵥ β + (W * X) *ᵥ θ + ((1 - lam • W)⁻¹ : WMat n) *ᵥ ε ω) :=
    funext fun ω => (hred ω).2
  dsimp only
  rw [hu, hy]
  exact gns_moments hε _ _ _

end GeoDa
