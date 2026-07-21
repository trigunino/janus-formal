import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonMatterRobinLLActionVariation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatterRobinLLActionReconstruction4D

/-!
# Actual Helmholtz symmetry on enriched common directions

This transports the proved symmetry of the genuine matter + Robin + LL
second variation to the enriched common Program-P direction type used by the
same action and Euler derivative.  It does not add the metric, gauge, ghost,
or auxiliary action sectors.
-/

namespace JanusFormal
namespace P0EFTJanusCommonMatterRobinLLActualHelmholtz4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D
open P0EFTJanusMappingTorusScalarRobinJunctionBalance4D
open P0EFTJanusMappingTorusScalarRobinJunctionHessian4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLHessian4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusCommonMatterActionVariation4D
open P0EFTJanusMatterRobinLLActualActionEulerHessian4D
open P0EFTJanusCommonMatterRobinLLActionVariation4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance effectiveThroatMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance effectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

/-- Helmholtz symmetry of the actual Hessian of the same assembled action,
after transport to the faithful enriched common directions. -/
theorem commonMatterRobinLLHessian_symmetric
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    (fields : IndependentFields period hPeriod)
    (first second : MatterRobinLLEnrichedDirections period hPeriod) :
    commonMatterRobinLLHessian period hPeriod matterData kPlus kMinus
        robinMeasure frame llMeasure fields first second =
      commonMatterRobinLLHessian period hPeriod matterData kPlus kMinus
        robinMeasure frame llMeasure fields second first := by
  unfold commonMatterRobinLLHessian
  exact matterRobinLLHessian_symmetric period hPeriod matterData kPlus kMinus
    robinMeasure frame llMeasure
    (matterVariationComponentFamily period hPeriod first.common.matter)
    (matterVariationComponentFamily period hPeriod second.common.matter)
    first.robin second.robin fields first.common.ll second.common.ll

/-- Consequently the two genuine Euler linearizations supplied by the common
variation bridge have equal real derivatives when their directions are
exchanged. -/
theorem commonMatterRobinLLEuler_mixed_derivatives_commute
    (matterData : MatterMultipletActionData period hPeriod)
    (kPlus kMinus : Real)
    (bulkPlus bulkMinus : SmoothQuotientField period hPeriod Real)
    (robinMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure robinMeasure]
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (llMeasure : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure llMeasure]
    (fields : IndependentFields period hPeriod)
    (junction : SmoothThroatField period hPeriod Real)
    (first second : MatterRobinLLEnrichedDirections period hPeriod) :
    HasDerivAt
        (fun epsilon : Real => matterRobinLLEuler period hPeriod matterData
          kPlus kMinus bulkPlus bulkMinus robinMeasure frame llMeasure
          (matterMultipletAffineCurve period hPeriod
            (independentMatterComponentFamily period hPeriod fields)
            (matterVariationComponentFamily period hPeriod first.common.matter)
            epsilon)
          (matterVariationComponentFamily period hPeriod second.common.matter)
          (junctionAffineCurve period hPeriod junction first.robin epsilon)
          second.robin
          (differentialLLFluxCurve period hPeriod fields first.common.ll epsilon)
          second.common.ll)
        (commonMatterRobinLLHessian period hPeriod matterData kPlus kMinus
          robinMeasure frame llMeasure fields second first) 0 := by
  rw [← commonMatterRobinLLHessian_symmetric period hPeriod matterData kPlus
    kMinus robinMeasure frame llMeasure fields first second]
  exact commonMatterRobinLLEuler_hasDerivAt period hPeriod matterData kPlus
    kMinus bulkPlus bulkMinus robinMeasure frame llMeasure fields junction
    first second

end

end P0EFTJanusCommonMatterRobinLLActualHelmholtz4D
end JanusFormal
