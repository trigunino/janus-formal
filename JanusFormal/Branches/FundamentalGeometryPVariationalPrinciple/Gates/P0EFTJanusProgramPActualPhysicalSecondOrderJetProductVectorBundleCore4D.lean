import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualLLSecondOrderJetProductVectorBundleCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeSecondOrderJetSmoothVectorBundleCore4D

namespace JanusFormal
namespace P0EFTJanusProgramPActualPhysicalSecondOrderJetProductVectorBundleCore4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPActualThroatAbelianPotentialChartwiseSecondOrderJetExtraction4D
open P0EFTJanusProgramPGlobalMetricChartwiseSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetBundleAtlasData4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetVectorBundleCore4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetSmoothVectorBundleCore4D
open P0EFTJanusProgramPActualThroatMetricSecondOrderJetBundleAtlasData4D
open P0EFTJanusProgramPActualThroatMetricSecondOrderJetVectorBundleCore4D
open P0EFTJanusProgramPActualThroatMetricSecondOrderJetSmoothVectorBundleCore4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderJetBundleAtlasData4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderJetVectorBundleCore4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderJetSmoothVectorBundleCore4D
open P0EFTJanusProgramPActualSecondOrderJetSmoothCoreSectionCoordinates4D
open P0EFTJanusProgramPActualLLSecondOrderJetProductVectorBundleCore4D
open P0EFTJanusPhysicalSecondJetCommonRefinedAtlas
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

variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*}
variable [Fintype NonNullFace] [Fintype NullFace]

abbrev ActualGaugeSecondOrderJetFiber :=
  FramedSecondOrderJet ThroatCoverCoordinates
    (FramedCovector ThroatCoverCoordinates)

abbrev ActualGaugeSecondOrderJetProductFiber :=
  (ActualGaugeSecondOrderJetFiber × ActualGaugeSecondOrderJetFiber) ×
    (ActualGaugeSecondOrderJetFiber × ActualGaugeSecondOrderJetFiber)

abbrev ActualGaugeSecondOrderJetProductBundleIndex :=
  (ThroatGaugeSecondOrderJetBundleIndex period hPeriod ×
      ThroatGaugeSecondOrderJetBundleIndex period hPeriod) ×
    (ThroatGaugeSecondOrderJetBundleIndex period hPeriod ×
      ThroatGaugeSecondOrderJetBundleIndex period hPeriod)

def actualGaugeSecondOrderJetProductVectorBundleCore :
    VectorBundleCore Real (EffectiveThroat period hPeriod)
      ActualGaugeSecondOrderJetProductFiber
      (ActualGaugeSecondOrderJetProductBundleIndex period hPeriod) :=
  vectorBundleCoreProd
    (vectorBundleCoreProd
      (throatGaugeSecondOrderJetVectorBundleCore period hPeriod)
      (throatGaugeSecondOrderJetVectorBundleCore period hPeriod))
    (vectorBundleCoreProd
      (throatGaugeSecondOrderJetVectorBundleCore period hPeriod)
      (throatGaugeSecondOrderJetVectorBundleCore period hPeriod))

theorem actualGaugeSecondOrderJetProductVectorBundleCore_isContMDiff :
    (actualGaugeSecondOrderJetProductVectorBundleCore period hPeriod).IsContMDiff
      throatCoverModelWithCorners ∞ := by
  letI :
      (throatGaugeSecondOrderJetVectorBundleCore period hPeriod).IsContMDiff
        throatCoverModelWithCorners ∞ :=
    throatGaugeSecondOrderJetVectorBundleCore_isContMDiff period hPeriod
  letI :
      (vectorBundleCoreProd
        (throatGaugeSecondOrderJetVectorBundleCore period hPeriod)
        (throatGaugeSecondOrderJetVectorBundleCore period hPeriod)).IsContMDiff
          throatCoverModelWithCorners ∞ :=
    vectorBundleCoreProd_isContMDiff throatCoverModelWithCorners
      (throatGaugeSecondOrderJetVectorBundleCore period hPeriod)
      (throatGaugeSecondOrderJetVectorBundleCore period hPeriod)
  exact vectorBundleCoreProd_isContMDiff throatCoverModelWithCorners
    (vectorBundleCoreProd
      (throatGaugeSecondOrderJetVectorBundleCore period hPeriod)
      (throatGaugeSecondOrderJetVectorBundleCore period hPeriod))
    (vectorBundleCoreProd
      (throatGaugeSecondOrderJetVectorBundleCore period hPeriod)
      (throatGaugeSecondOrderJetVectorBundleCore period hPeriod))

def globalCandidateAActualGaugeSecondOrderJetProductSmoothCoreSectionCoordinates
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace) :
    SmoothCoreSectionCoordinates throatCoverModelWithCorners
      (actualGaugeSecondOrderJetProductVectorBundleCore period hPeriod) :=
  smoothCoreSectionCoordinatesProd throatCoverModelWithCorners
    (smoothCoreSectionCoordinatesProd throatCoverModelWithCorners
      (actualThroatGaugeSecondOrderJetSmoothCoreSectionCoordinates
        period hPeriod
        (globalCandidateAThroatPotentialBySector period hPeriod data .plus) 0)
      (actualThroatGaugeSecondOrderJetSmoothCoreSectionCoordinates
        period hPeriod
        (globalCandidateAThroatPotentialBySector period hPeriod data .plus) 1))
    (smoothCoreSectionCoordinatesProd throatCoverModelWithCorners
      (actualThroatGaugeSecondOrderJetSmoothCoreSectionCoordinates
        period hPeriod
        (globalCandidateAThroatPotentialBySector period hPeriod data .minus) 0)
      (actualThroatGaugeSecondOrderJetSmoothCoreSectionCoordinates
        period hPeriod
        (globalCandidateAThroatPotentialBySector period hPeriod data .minus) 1))

abbrev ActualMetricSecondOrderJetFiber :=
  FramedSecondOrderJet ThroatCoverCoordinates
    (FramedCovariantTwoTensor ThroatCoverCoordinates)

abbrev ActualMetricSecondOrderJetProductFiber :=
  ActualMetricSecondOrderJetFiber × ActualMetricSecondOrderJetFiber

abbrev ActualMetricSecondOrderJetProductBundleIndex :=
  ThroatMetricSecondOrderJetBundleIndex period hPeriod ×
    ThroatMetricSecondOrderJetBundleIndex period hPeriod

def actualMetricSecondOrderJetProductVectorBundleCore :
    VectorBundleCore Real (EffectiveThroat period hPeriod)
      ActualMetricSecondOrderJetProductFiber
      (ActualMetricSecondOrderJetProductBundleIndex period hPeriod) :=
  vectorBundleCoreProd
    (throatMetricSecondOrderJetVectorBundleCore period hPeriod)
    (throatMetricSecondOrderJetVectorBundleCore period hPeriod)

theorem actualMetricSecondOrderJetProductVectorBundleCore_isContMDiff :
    (actualMetricSecondOrderJetProductVectorBundleCore period hPeriod).IsContMDiff
      throatCoverModelWithCorners ∞ := by
  letI :
      (throatMetricSecondOrderJetVectorBundleCore period hPeriod).IsContMDiff
        throatCoverModelWithCorners ∞ :=
    throatMetricSecondOrderJetVectorBundleCore_isContMDiff period hPeriod
  exact vectorBundleCoreProd_isContMDiff throatCoverModelWithCorners
    (throatMetricSecondOrderJetVectorBundleCore period hPeriod)
    (throatMetricSecondOrderJetVectorBundleCore period hPeriod)

def globalGaugeFixedActualMetricSecondOrderJetProductSmoothCoreSectionCoordinates
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) :
    SmoothCoreSectionCoordinates throatCoverModelWithCorners
      (actualMetricSecondOrderJetProductVectorBundleCore period hPeriod) :=
  smoothCoreSectionCoordinatesProd throatCoverModelWithCorners
    (actualThroatMetricSecondOrderJetSmoothCoreSectionCoordinates
      period hPeriod
      (globalGaugeFixedInducedMetricBySector period hPeriod configuration .plus))
    (actualThroatMetricSecondOrderJetSmoothCoreSectionCoordinates
      period hPeriod
      (globalGaugeFixedInducedMetricBySector period hPeriod configuration .minus))

abbrev ActualSpinCSecondOrderJetFiber :=
  FramedSecondOrderJet ThroatCoverCoordinates D9DoubledMatterFiber

abbrev ActualSpinCSecondOrderJetProductFiber :=
  ActualSpinCSecondOrderJetFiber × ActualSpinCSecondOrderJetFiber

abbrev ActualSpinCSecondOrderJetProductBundleIndex :=
  ThroatSpinCSecondOrderJetBundleIndex period hPeriod ×
    ThroatSpinCSecondOrderJetBundleIndex period hPeriod

def actualSpinCSecondOrderJetProductVectorBundleCore
    (choice : NormalRootChoice) :
    VectorBundleCore Real (EffectiveThroat period hPeriod)
      ActualSpinCSecondOrderJetProductFiber
      (ActualSpinCSecondOrderJetProductBundleIndex period hPeriod) :=
  vectorBundleCoreProd
    (throatSpinCSecondOrderJetVectorBundleCore period hPeriod choice)
    (throatSpinCSecondOrderJetVectorBundleCore period hPeriod choice)

theorem actualSpinCSecondOrderJetProductVectorBundleCore_isContMDiff
    (choice : NormalRootChoice) :
    (actualSpinCSecondOrderJetProductVectorBundleCore
      period hPeriod choice).IsContMDiff throatCoverModelWithCorners ∞ := by
  letI :
      (throatSpinCSecondOrderJetVectorBundleCore
        period hPeriod choice).IsContMDiff throatCoverModelWithCorners ∞ :=
    throatSpinCSecondOrderJetVectorBundleCore_isContMDiff
      period hPeriod choice
  exact vectorBundleCoreProd_isContMDiff throatCoverModelWithCorners
    (throatSpinCSecondOrderJetVectorBundleCore period hPeriod choice)
    (throatSpinCSecondOrderJetVectorBundleCore period hPeriod choice)

def globalGaugeFixedActualSpinCSecondOrderJetProductSmoothCoreSectionCoordinates
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) :
    SmoothCoreSectionCoordinates throatCoverModelWithCorners
      (actualSpinCSecondOrderJetProductVectorBundleCore
        period hPeriod .positiveQuarter) :=
  smoothCoreSectionCoordinatesProd throatCoverModelWithCorners
    (actualThroatSpinCSecondOrderJetSmoothCoreSectionCoordinates
      period hPeriod .positiveQuarter
      (configuration.physical.spinCMatter .plus))
    (actualThroatSpinCSecondOrderJetSmoothCoreSectionCoordinates
      period hPeriod .positiveQuarter
      (configuration.physical.spinCMatter .minus))

abbrev ActualPhysicalSecondOrderJetProductFiber :=
  PhysicalSecondJetFiber
    (GaugeFiber := ActualGaugeSecondOrderJetProductFiber)
    (LLFiber := ActualLLSecondOrderJetFiber)
    (MetricFiber := ActualMetricSecondOrderJetProductFiber)
    (SpinCFiber := ActualSpinCSecondOrderJetProductFiber)

abbrev ActualPhysicalSecondOrderJetProductBundleIndex :=
  PhysicalCommonChart
    (ActualGaugeSecondOrderJetProductBundleIndex period hPeriod)
    (ActualLLSecondOrderJetBundleIndex period hPeriod)
    (ActualMetricSecondOrderJetProductBundleIndex period hPeriod)
    (ActualSpinCSecondOrderJetProductBundleIndex period hPeriod)

def actualPhysicalSecondOrderJetProductVectorBundleCore
    (choice : NormalRootChoice) :
    VectorBundleCore Real (EffectiveThroat period hPeriod)
      ActualPhysicalSecondOrderJetProductFiber
      (ActualPhysicalSecondOrderJetProductBundleIndex period hPeriod) :=
  physicalSecondJetVectorBundleCore
    (actualGaugeSecondOrderJetProductVectorBundleCore period hPeriod)
    (actualLLSecondOrderJetProductVectorBundleCore period hPeriod)
    (actualMetricSecondOrderJetProductVectorBundleCore period hPeriod)
    (actualSpinCSecondOrderJetProductVectorBundleCore period hPeriod choice)

theorem actualPhysicalSecondOrderJetProductVectorBundleCore_isContMDiff
    (choice : NormalRootChoice) :
    (actualPhysicalSecondOrderJetProductVectorBundleCore
      period hPeriod choice).IsContMDiff throatCoverModelWithCorners ∞ := by
  letI :
      (actualGaugeSecondOrderJetProductVectorBundleCore
        period hPeriod).IsContMDiff throatCoverModelWithCorners ∞ :=
    actualGaugeSecondOrderJetProductVectorBundleCore_isContMDiff
      period hPeriod
  letI :
      (actualLLSecondOrderJetProductVectorBundleCore
        period hPeriod).IsContMDiff throatCoverModelWithCorners ∞ :=
    actualLLSecondOrderJetProductVectorBundleCore_isContMDiff period hPeriod
  letI :
      (actualMetricSecondOrderJetProductVectorBundleCore
        period hPeriod).IsContMDiff throatCoverModelWithCorners ∞ :=
    actualMetricSecondOrderJetProductVectorBundleCore_isContMDiff
      period hPeriod
  letI :
      (actualSpinCSecondOrderJetProductVectorBundleCore
        period hPeriod choice).IsContMDiff throatCoverModelWithCorners ∞ :=
    actualSpinCSecondOrderJetProductVectorBundleCore_isContMDiff
      period hPeriod choice
  exact physicalSecondJetVectorBundleCore_isContMDiff throatCoverModelWithCorners
    (actualGaugeSecondOrderJetProductVectorBundleCore period hPeriod)
    (actualLLSecondOrderJetProductVectorBundleCore period hPeriod)
    (actualMetricSecondOrderJetProductVectorBundleCore period hPeriod)
    (actualSpinCSecondOrderJetProductVectorBundleCore period hPeriod choice)

def globalCandidateAActualPhysicalSecondOrderJetSmoothCoreSectionCoordinates
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace) :
    SmoothCoreSectionCoordinates throatCoverModelWithCorners
      (actualPhysicalSecondOrderJetProductVectorBundleCore
        period hPeriod .positiveQuarter) :=
  physicalSecondJetSmoothCoreSectionCoordinates throatCoverModelWithCorners
    (actualGaugeSecondOrderJetProductVectorBundleCore period hPeriod)
    (actualLLSecondOrderJetProductVectorBundleCore period hPeriod)
    (actualMetricSecondOrderJetProductVectorBundleCore period hPeriod)
    (actualSpinCSecondOrderJetProductVectorBundleCore
      period hPeriod .positiveQuarter)
    (globalCandidateAActualGaugeSecondOrderJetProductSmoothCoreSectionCoordinates
      period hPeriod data)
    (globalFieldConfigurationLLSecondOrderJetProductSmoothCoreSectionCoordinates
      period hPeriod configuration.physical)
    (globalGaugeFixedActualMetricSecondOrderJetProductSmoothCoreSectionCoordinates
      period hPeriod configuration)
    (globalGaugeFixedActualSpinCSecondOrderJetProductSmoothCoreSectionCoordinates
      period hPeriod configuration)

end
end P0EFTJanusProgramPActualPhysicalSecondOrderJetProductVectorBundleCore4D
end JanusFormal
