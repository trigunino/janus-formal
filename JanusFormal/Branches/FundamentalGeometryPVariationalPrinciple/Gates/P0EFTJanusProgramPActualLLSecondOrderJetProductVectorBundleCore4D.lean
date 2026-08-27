import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualSecondOrderJetSmoothCoreSectionCoordinates4D

namespace JanusFormal
namespace P0EFTJanusProgramPActualLLSecondOrderJetProductVectorBundleCore4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPActualThroatConstantFiberSecondOrderJetSmoothVectorBundleCore4D
open P0EFTJanusProgramPActualSecondOrderJetSmoothCoreSectionCoordinates4D
open P0EFTJanusPhysicalSecondJetProductVectorBundleCore
open P0EFTJanusPhysicalSecondJetSmoothVectorBundleCore
open P0EFTJanusPhysicalSecondJetSmoothSectionAssembly

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

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

abbrev ActualLLSecondOrderJetFiber :=
  (ActualThroatConstantFiberSecondOrderJet LLMetricFiber ×
      ActualThroatConstantFiberSecondOrderJet Real) ×
    ActualThroatConstantFiberSecondOrderJet LLFieldFiber

abbrev ActualLLSecondOrderJetBundleIndex :=
  (ActualThroatConstantFiberSecondOrderJetBundleIndex period hPeriod ×
      ActualThroatConstantFiberSecondOrderJetBundleIndex period hPeriod) ×
    ActualThroatConstantFiberSecondOrderJetBundleIndex period hPeriod

def actualLLSecondOrderJetProductVectorBundleCore :
    VectorBundleCore Real (EffectiveThroat period hPeriod)
      ActualLLSecondOrderJetFiber
      (ActualLLSecondOrderJetBundleIndex period hPeriod) :=
  vectorBundleCoreProd
    (vectorBundleCoreProd
      (actualThroatConstantFiberSecondOrderJetSmoothVectorBundleCore
        period hPeriod (Fiber := LLMetricFiber))
      (actualThroatConstantFiberSecondOrderJetSmoothVectorBundleCore
        period hPeriod (Fiber := Real)))
    (actualThroatConstantFiberSecondOrderJetSmoothVectorBundleCore
      period hPeriod (Fiber := LLFieldFiber))

theorem actualLLSecondOrderJetProductVectorBundleCore_isContMDiff :
    (actualLLSecondOrderJetProductVectorBundleCore period hPeriod).IsContMDiff
      throatCoverModelWithCorners ∞ := by
  letI :
      (actualThroatConstantFiberSecondOrderJetSmoothVectorBundleCore
        period hPeriod (Fiber := LLMetricFiber)).IsContMDiff
          throatCoverModelWithCorners ∞ :=
    actualThroatConstantFiberSecondOrderJetSmoothVectorBundleCore_isContMDiff
      period hPeriod (Fiber := LLMetricFiber)
  letI :
      (actualThroatConstantFiberSecondOrderJetSmoothVectorBundleCore
        period hPeriod (Fiber := Real)).IsContMDiff
          throatCoverModelWithCorners ∞ :=
    actualThroatConstantFiberSecondOrderJetSmoothVectorBundleCore_isContMDiff
      period hPeriod (Fiber := Real)
  letI :
      (actualThroatConstantFiberSecondOrderJetSmoothVectorBundleCore
        period hPeriod (Fiber := LLFieldFiber)).IsContMDiff
          throatCoverModelWithCorners ∞ :=
    actualThroatConstantFiberSecondOrderJetSmoothVectorBundleCore_isContMDiff
      period hPeriod (Fiber := LLFieldFiber)
  letI :
      (vectorBundleCoreProd
        (actualThroatConstantFiberSecondOrderJetSmoothVectorBundleCore
          period hPeriod (Fiber := LLMetricFiber))
        (actualThroatConstantFiberSecondOrderJetSmoothVectorBundleCore
          period hPeriod (Fiber := Real))).IsContMDiff
            throatCoverModelWithCorners ∞ :=
    vectorBundleCoreProd_isContMDiff throatCoverModelWithCorners
      (actualThroatConstantFiberSecondOrderJetSmoothVectorBundleCore
        period hPeriod (Fiber := LLMetricFiber))
      (actualThroatConstantFiberSecondOrderJetSmoothVectorBundleCore
        period hPeriod (Fiber := Real))
  exact vectorBundleCoreProd_isContMDiff throatCoverModelWithCorners
    (vectorBundleCoreProd
      (actualThroatConstantFiberSecondOrderJetSmoothVectorBundleCore
        period hPeriod (Fiber := LLMetricFiber))
      (actualThroatConstantFiberSecondOrderJetSmoothVectorBundleCore
        period hPeriod (Fiber := Real)))
    (actualThroatConstantFiberSecondOrderJetSmoothVectorBundleCore
      period hPeriod (Fiber := LLFieldFiber))

def globalFieldConfigurationLLSecondOrderJetProductSmoothCoreSectionCoordinates
    (configuration : GlobalFieldConfiguration period hPeriod) :
    SmoothCoreSectionCoordinates throatCoverModelWithCorners
      (actualLLSecondOrderJetProductVectorBundleCore period hPeriod) :=
  smoothCoreSectionCoordinatesProd throatCoverModelWithCorners
    (smoothCoreSectionCoordinatesProd throatCoverModelWithCorners
      (globalFieldConfigurationLLAuxMetricSecondOrderJetSmoothCoreSectionCoordinates
        period hPeriod configuration)
      (globalFieldConfigurationLLMeasureSecondOrderJetSmoothCoreSectionCoordinates
        period hPeriod configuration))
    (globalFieldConfigurationLLFieldSecondOrderJetSmoothCoreSectionCoordinates
      period hPeriod configuration)

end
end P0EFTJanusProgramPActualLLSecondOrderJetProductVectorBundleCore4D
end JanusFormal
