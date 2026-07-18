import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProductThroatHolonomyGraphRealFredholmFamily4D
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Regularity of the inverse common-graph family

Every real-holonomy graph fiber is a complex Banach-space isomorphism.  The
inverse-map regularity theorem therefore gives a continuous inverse family in
operator norm.  The parameter and the operator spaces are viewed over `ℝ`.
-/

namespace JanusFormal
namespace P0EFTJanusProductThroatHolonomyGraphInverseRegularity4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProductThroatHeatOperator4D
open P0EFTJanusProductThroatUnboundedDiracFredholm4D
open P0EFTJanusProductThroatHolonomyGraphFamily4D
open P0EFTJanusProductThroatHolonomyGraphRealFredholmFamily4D
open scoped Topology

/-- The inverse complex operators, with their canonical real normed structure. -/
def ProductThroatCommonGraphInverseOperatorReal
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist) :=
  RestrictScalars ℝ Complex
    (ProductThroatHeatHilbert data →L[Complex]
      ProductThroatCommonGraphDomain data fold reference)

instance productThroatCommonGraphInverseOperatorRealNormedAddCommGroup
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist) :
    NormedAddCommGroup
      (ProductThroatCommonGraphInverseOperatorReal data fold reference) := by
  unfold ProductThroatCommonGraphInverseOperatorReal
  infer_instance

instance productThroatCommonGraphInverseOperatorRealModule
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist) :
    Module ℝ (ProductThroatCommonGraphInverseOperatorReal data fold reference) :=
  RestrictScalars.module ℝ Complex
    (ProductThroatHeatHilbert data →L[Complex]
      ProductThroatCommonGraphDomain data fold reference)

instance productThroatCommonGraphInverseOperatorRealNormedSpace
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist) :
    NormedSpace ℝ
      (ProductThroatCommonGraphInverseOperatorReal data fold reference) :=
  RestrictScalars.normedSpace ℝ Complex
    (ProductThroatHeatHilbert data →L[Complex]
      ProductThroatCommonGraphDomain data fold reference)

/-- The inverse of the common-graph Dirac fiber. -/
def productThroatCommonGraphDiracInverseCLM
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist)
    (holonomy : ℝ) :
    ProductThroatCommonGraphInverseOperatorReal data fold reference :=
  ContinuousLinearMap.inverse
    (productThroatCommonGraphDiracCLM data fold reference holonomy)

theorem productThroatCommonGraphDiracInverse_eq_equiv_symm
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist)
    (holonomy : ℝ) :
    productThroatCommonGraphDiracInverseCLM data fold reference holonomy =
      ((productThroatCommonGraphDiracContinuousLinearEquiv_real
        data fold reference holonomy).symm :
        ProductThroatHeatHilbert data →L[Complex]
          ProductThroatCommonGraphDomain data fold reference) := by
  change ContinuousLinearMap.inverse
      (productThroatCommonGraphDiracCLM data fold reference holonomy) =
    ((productThroatCommonGraphDiracContinuousLinearEquiv_real
      data fold reference holonomy).symm :
      ProductThroatHeatHilbert data →L[Complex]
        ProductThroatCommonGraphDomain data fold reference)
  exact ContinuousLinearMap.inverse_equiv
    (productThroatCommonGraphDiracContinuousLinearEquiv_real
      data fold reference holonomy)

theorem productThroatCommonGraphDiracInverse_continuousAt
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist)
    (holonomy : ℝ) :
    ContinuousAt
      (productThroatCommonGraphDiracInverseCLM data fold reference) holonomy := by
  have hInverse : ContinuousAt ContinuousLinearMap.inverse
      (productThroatCommonGraphDiracCLM data fold reference holonomy) :=
    (contDiffAt_map_inverse
      (productThroatCommonGraphDiracContinuousLinearEquiv_real
        data fold reference holonomy) :
      ContDiffAt Complex 1 ContinuousLinearMap.inverse
        (productThroatCommonGraphDiracCLM
          data fold reference holonomy)).continuousAt
  have hFamily : ContinuousAt
      (productThroatCommonGraphDiracReal data fold reference) holonomy :=
    (productThroatCommonGraphDirac_contDiff_one
      data fold reference).continuous.continuousAt
  exact hInverse.comp hFamily

theorem productThroatCommonGraphDiracInverse_continuous
    (data : ProductThroatSpectralData) (fold : Fold) (reference : CircleTwist) :
    Continuous (productThroatCommonGraphDiracInverseCLM data fold reference) := by
  rw [continuous_iff_continuousAt]
  exact productThroatCommonGraphDiracInverse_continuousAt data fold reference

end

end P0EFTJanusProductThroatHolonomyGraphInverseRegularity4D
end JanusFormal
