import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProductThroatHolonomyGraphInverseLocalBound4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProductThroatHolonomyGraphSecondDerivative4D
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars

/-!
# C1 inverse common-graph family

Complex `C¹` regularity of inversion is restricted to the real scalar field
and composed with the real-holonomy common-graph family.
-/

namespace JanusFormal
namespace P0EFTJanusProductThroatHolonomyGraphInverseC1_4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProductThroatHeatOperator4D
open P0EFTJanusProductThroatUnboundedDiracFredholm4D
open P0EFTJanusProductThroatHolonomyGraphFamily4D
open P0EFTJanusProductThroatHolonomyGraphSecondDerivative4D
open P0EFTJanusProductThroatHolonomyGraphRealFredholmFamily4D
open P0EFTJanusProductThroatHolonomyGraphInverseRegularity4D
open scoped Topology

instance productThroatInverseDerivativeRealNormedAddCommGroup
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist) :
    NormedAddCommGroup
      ((ProductThroatCommonGraphDomain data fold reference →L[Complex]
          ProductThroatHeatHilbert data) →L[ℝ]
        (ProductThroatHeatHilbert data →L[Complex]
          ProductThroatCommonGraphDomain data fold reference)) :=
  ContinuousLinearMap.toNormedAddCommGroup
    (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := ProductThroatCommonGraphDomain data fold reference →L[Complex]
      ProductThroatHeatHilbert data)
    (F := ProductThroatHeatHilbert data →L[Complex]
      ProductThroatCommonGraphDomain data fold reference)
    (σ₁₂ := RingHom.id ℝ)

theorem continuousLinearMap_inverse_contDiffAt_real
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist)
    (equiv : ProductThroatCommonGraphDomain data fold reference ≃L[Complex]
      ProductThroatHeatHilbert data) :
    ContDiffAt ℝ 1
      (ContinuousLinearMap.inverse :
        (ProductThroatCommonGraphDomain data fold reference →L[Complex]
          ProductThroatHeatHilbert data) →
        (ProductThroatHeatHilbert data →L[Complex]
          ProductThroatCommonGraphDomain data fold reference))
      (equiv : ProductThroatCommonGraphDomain data fold reference →L[Complex]
        ProductThroatHeatHilbert data) := by
  have hComplex : ContDiffAt Complex 1 ContinuousLinearMap.inverse
      (equiv : ProductThroatCommonGraphDomain data fold reference →L[Complex]
        ProductThroatHeatHilbert data) :=
    contDiffAt_map_inverse equiv
  rcases contDiffAt_one_iff.mp hComplex with
    ⟨derivative, neighborhood, hNeighborhood, hDerivativeContinuous,
      hHasDerivative⟩
  rw [contDiffAt_one_iff]
  refine ⟨fun operator => (derivative operator).restrictScalars ℝ,
    neighborhood, hNeighborhood, ?_, ?_⟩
  · exact (ContinuousLinearMap.continuous_restrictScalars ℝ).comp_continuousOn
      hDerivativeContinuous
  · intro operator hOperator
    exact (hHasDerivative operator hOperator).restrictScalars ℝ

/-- The same inverse family in the canonical complex operator type, viewed over `ℝ`. -/
def productThroatCommonGraphDiracInverseCanonical
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist)
    (holonomy : ℝ) :
    ProductThroatHeatHilbert data →L[Complex]
      ProductThroatCommonGraphDomain data fold reference :=
  ContinuousLinearMap.inverse
    (productThroatCommonGraphDiracCLM data fold reference holonomy)

theorem productThroatCommonGraphDiracInverseCanonical_eq_restricted
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist)
    (holonomy : ℝ) :
    productThroatCommonGraphDiracInverseCanonical data fold reference holonomy =
      productThroatCommonGraphDiracInverseCLM data fold reference holonomy :=
  rfl

theorem productThroatCommonGraphDiracInverseCanonical_contDiff_one
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist) :
    ContDiff ℝ 1
      (productThroatCommonGraphDiracInverseCanonical data fold reference) := by
  rw [contDiff_iff_contDiffAt]
  intro holonomy
  have hInverse := continuousLinearMap_inverse_contDiffAt_real
    data fold reference
      (productThroatCommonGraphDiracContinuousLinearEquiv_real
        data fold reference holonomy)
  have hFamily : ContDiffAt ℝ 1
      (productThroatCommonGraphDiracReal data fold reference) holonomy :=
    (productThroatCommonGraphDirac_contDiff_one
      data fold reference).contDiffAt
  change ContDiffAt ℝ 1
    (fun parameter => ContinuousLinearMap.inverse
      (productThroatCommonGraphDiracCLM data fold reference parameter)) holonomy
  exact hInverse.comp holonomy hFamily

/-- Complex smoothness of inversion restricted to the real scalar field at
order three. -/
theorem continuousLinearMap_inverse_contDiffAt_real_three
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist)
    (equiv : ProductThroatCommonGraphDomain data fold reference ≃L[Complex]
      ProductThroatHeatHilbert data) :
    ContDiffAt ℝ 3
      (ContinuousLinearMap.inverse :
        (ProductThroatCommonGraphDomain data fold reference →L[Complex]
          ProductThroatHeatHilbert data) →
        (ProductThroatHeatHilbert data →L[Complex]
          ProductThroatCommonGraphDomain data fold reference))
      (equiv : ProductThroatCommonGraphDomain data fold reference →L[Complex]
        ProductThroatHeatHilbert data) := by
  have hComplex : ContDiffAt Complex 3 ContinuousLinearMap.inverse
      (equiv : ProductThroatCommonGraphDomain data fold reference →L[Complex]
        ProductThroatHeatHilbert data) :=
    contDiffAt_map_inverse equiv
  exact hComplex.restrict_scalars ℝ

theorem productThroatCommonGraphDiracInverseCanonical_contDiff_three
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist) :
    ContDiff ℝ 3
      (productThroatCommonGraphDiracInverseCanonical data fold reference) := by
  rw [contDiff_iff_contDiffAt]
  intro holonomy
  have hInverse := continuousLinearMap_inverse_contDiffAt_real_three
    data fold reference
      (productThroatCommonGraphDiracContinuousLinearEquiv_real
        data fold reference holonomy)
  have hFamily : ContDiffAt ℝ 3
      (productThroatCommonGraphDiracReal data fold reference) holonomy :=
    (productThroatCommonGraphDirac_contDiff_three
      data fold reference).contDiffAt
  change ContDiffAt ℝ 3
    (fun parameter => ContinuousLinearMap.inverse
      (productThroatCommonGraphDiracCLM data fold reference parameter)) holonomy
  exact hInverse.comp holonomy hFamily

/-- Inversion is smooth to every order over `ℝ` at every complex-linear
equivalence. -/
theorem continuousLinearMap_inverse_contDiffAt_real_top
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist)
    (equiv : ProductThroatCommonGraphDomain data fold reference ≃L[Complex]
      ProductThroatHeatHilbert data) :
    ContDiffAt ℝ (⊤ : WithTop ℕ∞)
      (ContinuousLinearMap.inverse :
        (ProductThroatCommonGraphDomain data fold reference →L[Complex]
          ProductThroatHeatHilbert data) →
        (ProductThroatHeatHilbert data →L[Complex]
          ProductThroatCommonGraphDomain data fold reference))
      (equiv : ProductThroatCommonGraphDomain data fold reference →L[Complex]
        ProductThroatHeatHilbert data) := by
  have hComplex : ContDiffAt Complex (⊤ : WithTop ℕ∞)
      ContinuousLinearMap.inverse
      (equiv : ProductThroatCommonGraphDomain data fold reference →L[Complex]
        ProductThroatHeatHilbert data) :=
    contDiffAt_map_inverse equiv
  exact hComplex.restrict_scalars ℝ

/-- Any `C∞` upgrade of the direct common-graph family automatically upgrades
its canonical inverse to `C∞`; no order-by-order inverse calculation remains. -/
theorem productThroatCommonGraphDiracInverseCanonical_contDiff_top
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist)
    (hForward : ContDiff ℝ (⊤ : WithTop ℕ∞)
      (productThroatCommonGraphDiracReal data fold reference)) :
    ContDiff ℝ (⊤ : WithTop ℕ∞)
      (productThroatCommonGraphDiracInverseCanonical data fold reference) := by
  rw [contDiff_iff_contDiffAt]
  intro holonomy
  have hInverse := continuousLinearMap_inverse_contDiffAt_real_top
    data fold reference
      (productThroatCommonGraphDiracContinuousLinearEquiv_real
        data fold reference holonomy)
  change ContDiffAt ℝ (⊤ : WithTop ℕ∞)
    (fun parameter => ContinuousLinearMap.inverse
      (productThroatCommonGraphDiracCLM data fold reference parameter)) holonomy
  exact hInverse.comp holonomy hForward.contDiffAt

end


end P0EFTJanusProductThroatHolonomyGraphInverseC1_4D
end JanusFormal
