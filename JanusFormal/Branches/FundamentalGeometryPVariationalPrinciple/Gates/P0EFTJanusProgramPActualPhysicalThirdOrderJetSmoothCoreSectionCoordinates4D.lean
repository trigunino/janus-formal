import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualPhysicalThirdOrderJetProductVectorBundleCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeThirdOrderJetSmoothVectorBundleSection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatMetricThirdOrderJetSmoothVectorBundleSection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCThirdOrderJetSmoothVectorBundleSection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualLLThirdOrderJetSmoothVectorBundleSections4D
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusPhysicalSecondJetSmoothSectionAssembly

/-!
# Smooth coordinates of the actual physical third-jet section

The eleven gauge, LL, metric and SpinC third jets are assembled in the
physical product core of Gate 1005.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualPhysicalThirdOrderJetSmoothCoreSectionCoordinates4D

set_option autoImplicit false

noncomputable section

open Bundle
open scoped Manifold ContDiff RealInnerProductSpace Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPActualThroatAbelianPotentialChartwiseSecondOrderJetExtraction4D
open P0EFTJanusProgramPGlobalMetricChartwiseSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatGaugeThirdOrderJetLocalSectionSmoothness4D
open P0EFTJanusProgramPActualThroatGaugeThirdOrderJetVectorBundleCore4D
open P0EFTJanusProgramPActualThroatGaugeThirdOrderJetSmoothVectorBundleSection4D
open P0EFTJanusProgramPActualThroatMetricThirdOrderJetLocalSectionSmoothness4D
open P0EFTJanusProgramPActualThroatMetricThirdOrderJetVectorBundleCore4D
open P0EFTJanusProgramPActualThroatMetricThirdOrderJetSmoothVectorBundleSection4D
open P0EFTJanusProgramPActualThroatSpinCThirdOrderJetLocalSectionSmoothness4D
open P0EFTJanusProgramPActualThroatSpinCThirdOrderJetVectorBundleCore4D
open P0EFTJanusProgramPActualThroatSpinCThirdOrderJetSmoothVectorBundleSection4D
open P0EFTJanusProgramPActualLLThirdOrderJetProductVectorBundleCore4D
open P0EFTJanusProgramPActualLLThirdOrderJetSmoothVectorBundleSections4D
open P0EFTJanusProgramPActualPhysicalThirdOrderJetProductVectorBundleCore4D
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

/-! ## Component coordinate packages -/

def actualThroatGaugeThirdOrderJetSmoothCoreSectionCoordinates
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2) :
    SmoothCoreSectionCoordinates throatCoverModelWithCorners
      (throatGaugeThirdOrderJetVectorBundleCore period hPeriod) :=
  smoothCoreSectionCoordinatesOfLocalRepresentatives
    throatCoverModelWithCorners
    (throatGaugeThirdOrderJetVectorBundleCore period hPeriod)
    (actualThroatGaugeThirdOrderJetLocalRepresentative
      period hPeriod potential component)
    (actualThroatGaugeThirdOrderJetLocalRepresentative_compatible
      period hPeriod potential component)
    (actualThroatGaugeThirdOrderJetLocalRepresentative_contMDiffOn
      period hPeriod potential component)

def actualThroatMetricThirdOrderJetSmoothCoreSectionCoordinates
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod) :
    SmoothCoreSectionCoordinates throatCoverModelWithCorners
      (throatMetricThirdOrderJetVectorBundleCore period hPeriod) :=
  smoothCoreSectionCoordinatesOfLocalRepresentatives
    throatCoverModelWithCorners
    (throatMetricThirdOrderJetVectorBundleCore period hPeriod)
    (actualThroatMetricThirdOrderJetLocalRepresentative period hPeriod tensor)
    (actualThroatMetricThirdOrderJetLocalRepresentative_compatible
      period hPeriod tensor)
    (actualThroatMetricThirdOrderJetLocalRepresentative_contMDiffOn
      period hPeriod tensor)

def actualThroatSpinCThirdOrderJetSmoothCoreSectionCoordinates
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice) :
    SmoothCoreSectionCoordinates throatCoverModelWithCorners
      (throatSpinCThirdOrderJetVectorBundleCore period hPeriod choice) :=
  smoothCoreSectionCoordinatesOfLocalRepresentatives
    throatCoverModelWithCorners
    (throatSpinCThirdOrderJetVectorBundleCore period hPeriod choice)
    (actualThroatSpinCThirdOrderJetLocalRepresentative
      period hPeriod choice state)
    (actualThroatSpinCThirdOrderJetLocalRepresentative_compatible
      period hPeriod choice state)
    (actualThroatSpinCThirdOrderJetLocalRepresentative_contMDiffOn
      period hPeriod choice state)

/-! ## Sector products -/

def globalCandidateAActualGaugeThirdOrderJetProductSmoothCoreSectionCoordinates
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace) :
    SmoothCoreSectionCoordinates throatCoverModelWithCorners
      (actualGaugeThirdOrderJetProductVectorBundleCore period hPeriod) :=
  smoothCoreSectionCoordinatesProd throatCoverModelWithCorners
    (smoothCoreSectionCoordinatesProd throatCoverModelWithCorners
      (actualThroatGaugeThirdOrderJetSmoothCoreSectionCoordinates
        period hPeriod
        (globalCandidateAThroatPotentialBySector period hPeriod data .plus) 0)
      (actualThroatGaugeThirdOrderJetSmoothCoreSectionCoordinates
        period hPeriod
        (globalCandidateAThroatPotentialBySector period hPeriod data .plus) 1))
    (smoothCoreSectionCoordinatesProd throatCoverModelWithCorners
      (actualThroatGaugeThirdOrderJetSmoothCoreSectionCoordinates
        period hPeriod
        (globalCandidateAThroatPotentialBySector period hPeriod data .minus) 0)
      (actualThroatGaugeThirdOrderJetSmoothCoreSectionCoordinates
        period hPeriod
        (globalCandidateAThroatPotentialBySector period hPeriod data .minus) 1))

def globalGaugeFixedActualMetricThirdOrderJetProductSmoothCoreSectionCoordinates
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) :
    SmoothCoreSectionCoordinates throatCoverModelWithCorners
      (actualMetricThirdOrderJetProductVectorBundleCore period hPeriod) :=
  smoothCoreSectionCoordinatesProd throatCoverModelWithCorners
    (actualThroatMetricThirdOrderJetSmoothCoreSectionCoordinates
      period hPeriod
      (globalGaugeFixedInducedMetricBySector period hPeriod configuration .plus))
    (actualThroatMetricThirdOrderJetSmoothCoreSectionCoordinates
      period hPeriod
      (globalGaugeFixedInducedMetricBySector period hPeriod configuration .minus))

def globalGaugeFixedActualSpinCThirdOrderJetProductSmoothCoreSectionCoordinates
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) :
    SmoothCoreSectionCoordinates throatCoverModelWithCorners
      (actualSpinCThirdOrderJetProductVectorBundleCore
        period hPeriod .positiveQuarter) :=
  smoothCoreSectionCoordinatesProd throatCoverModelWithCorners
    (actualThroatSpinCThirdOrderJetSmoothCoreSectionCoordinates
      period hPeriod .positiveQuarter
      (configuration.physical.spinCMatter .plus))
    (actualThroatSpinCThirdOrderJetSmoothCoreSectionCoordinates
      period hPeriod .positiveQuarter
      (configuration.physical.spinCMatter .minus))

/-! ## Complete physical section -/

def globalCandidateAActualPhysicalThirdOrderJetSmoothCoreSectionCoordinates
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace) :
    SmoothCoreSectionCoordinates throatCoverModelWithCorners
      (actualPhysicalThirdOrderJetProductVectorBundleCore
        period hPeriod .positiveQuarter) :=
  physicalSecondJetSmoothCoreSectionCoordinates throatCoverModelWithCorners
    (actualGaugeThirdOrderJetProductVectorBundleCore period hPeriod)
    (actualLLThirdOrderJetProductVectorBundleCore period hPeriod)
    (actualMetricThirdOrderJetProductVectorBundleCore period hPeriod)
    (actualSpinCThirdOrderJetProductVectorBundleCore
      period hPeriod .positiveQuarter)
    (globalCandidateAActualGaugeThirdOrderJetProductSmoothCoreSectionCoordinates
      period hPeriod data)
    (globalGaugeFixedFieldConfigurationLLThirdOrderJetProductSmoothCoreSectionCoordinates
      period hPeriod configuration)
    (globalGaugeFixedActualMetricThirdOrderJetProductSmoothCoreSectionCoordinates
      period hPeriod configuration)
    (globalGaugeFixedActualSpinCThirdOrderJetProductSmoothCoreSectionCoordinates
      period hPeriod configuration)

abbrev ActualPhysicalThirdOrderJetProductBundleTotalSpace :=
  Bundle.TotalSpace ActualPhysicalThirdOrderJetProductFiber
    (actualPhysicalThirdOrderJetProductVectorBundleCore
      period hPeriod .positiveQuarter).Fiber

def globalCandidateAActualPhysicalThirdOrderJetVectorBundleSection
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace) :
    EffectiveThroat period hPeriod →
      ActualPhysicalThirdOrderJetProductBundleTotalSpace period hPeriod :=
  physicalSecondJetBundleSection throatCoverModelWithCorners
    (actualGaugeThirdOrderJetProductVectorBundleCore period hPeriod)
    (actualLLThirdOrderJetProductVectorBundleCore period hPeriod)
    (actualMetricThirdOrderJetProductVectorBundleCore period hPeriod)
    (actualSpinCThirdOrderJetProductVectorBundleCore
      period hPeriod .positiveQuarter)
    (globalCandidateAActualGaugeThirdOrderJetProductSmoothCoreSectionCoordinates
      period hPeriod data)
    (globalGaugeFixedFieldConfigurationLLThirdOrderJetProductSmoothCoreSectionCoordinates
      period hPeriod configuration)
    (globalGaugeFixedActualMetricThirdOrderJetProductSmoothCoreSectionCoordinates
      period hPeriod configuration)
    (globalGaugeFixedActualSpinCThirdOrderJetProductSmoothCoreSectionCoordinates
      period hPeriod configuration)

theorem globalCandidateAActualPhysicalThirdOrderJetVectorBundleSection_localTriv
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (chart : ActualPhysicalThirdOrderJetProductBundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      (actualPhysicalThirdOrderJetProductVectorBundleCore
        period hPeriod .positiveQuarter).baseSet chart) :
    (((actualPhysicalThirdOrderJetProductVectorBundleCore
        period hPeriod .positiveQuarter).localTriv chart)
      (globalCandidateAActualPhysicalThirdOrderJetVectorBundleSection
        period hPeriod data current)).2 =
      (globalCandidateAActualPhysicalThirdOrderJetSmoothCoreSectionCoordinates
        period hPeriod data).extractor chart current := by
  exact physicalSecondJetBundleSection_localTriv throatCoverModelWithCorners
    (actualGaugeThirdOrderJetProductVectorBundleCore period hPeriod)
    (actualLLThirdOrderJetProductVectorBundleCore period hPeriod)
    (actualMetricThirdOrderJetProductVectorBundleCore period hPeriod)
    (actualSpinCThirdOrderJetProductVectorBundleCore
      period hPeriod .positiveQuarter)
    (globalCandidateAActualGaugeThirdOrderJetProductSmoothCoreSectionCoordinates
      period hPeriod data)
    (globalGaugeFixedFieldConfigurationLLThirdOrderJetProductSmoothCoreSectionCoordinates
      period hPeriod configuration)
    (globalGaugeFixedActualMetricThirdOrderJetProductSmoothCoreSectionCoordinates
      period hPeriod configuration)
    (globalGaugeFixedActualSpinCThirdOrderJetProductSmoothCoreSectionCoordinates
      period hPeriod configuration)
    chart current hCurrent

theorem globalCandidateAActualPhysicalThirdOrderJetVectorBundleSection_contMDiff
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace) :
    ContMDiff throatCoverModelWithCorners
      (throatCoverModelWithCorners.prod
        (modelWithCornersSelf Real ActualPhysicalThirdOrderJetProductFiber)) ∞
      (globalCandidateAActualPhysicalThirdOrderJetVectorBundleSection
        period hPeriod data) := by
  letI :
      (actualGaugeThirdOrderJetProductVectorBundleCore
        period hPeriod).IsContMDiff throatCoverModelWithCorners ∞ :=
    actualGaugeThirdOrderJetProductVectorBundleCore_isContMDiff
      period hPeriod
  letI :
      (actualLLThirdOrderJetProductVectorBundleCore
        period hPeriod).IsContMDiff throatCoverModelWithCorners ∞ :=
    actualLLThirdOrderJetProductVectorBundleCore_isContMDiff
      period hPeriod
  letI :
      (actualMetricThirdOrderJetProductVectorBundleCore
        period hPeriod).IsContMDiff throatCoverModelWithCorners ∞ :=
    actualMetricThirdOrderJetProductVectorBundleCore_isContMDiff
      period hPeriod
  letI :
      (actualSpinCThirdOrderJetProductVectorBundleCore
        period hPeriod .positiveQuarter).IsContMDiff
          throatCoverModelWithCorners ∞ :=
    actualSpinCThirdOrderJetProductVectorBundleCore_isContMDiff
      period hPeriod .positiveQuarter
  exact physicalSecondJetBundleSection_contMDiff throatCoverModelWithCorners
    (actualGaugeThirdOrderJetProductVectorBundleCore period hPeriod)
    (actualLLThirdOrderJetProductVectorBundleCore period hPeriod)
    (actualMetricThirdOrderJetProductVectorBundleCore period hPeriod)
    (actualSpinCThirdOrderJetProductVectorBundleCore
      period hPeriod .positiveQuarter)
    (globalCandidateAActualGaugeThirdOrderJetProductSmoothCoreSectionCoordinates
      period hPeriod data)
    (globalGaugeFixedFieldConfigurationLLThirdOrderJetProductSmoothCoreSectionCoordinates
      period hPeriod configuration)
    (globalGaugeFixedActualMetricThirdOrderJetProductSmoothCoreSectionCoordinates
      period hPeriod configuration)
    (globalGaugeFixedActualSpinCThirdOrderJetProductSmoothCoreSectionCoordinates
      period hPeriod configuration)

end
end P0EFTJanusProgramPActualPhysicalThirdOrderJetSmoothCoreSectionCoordinates4D
end JanusFormal
