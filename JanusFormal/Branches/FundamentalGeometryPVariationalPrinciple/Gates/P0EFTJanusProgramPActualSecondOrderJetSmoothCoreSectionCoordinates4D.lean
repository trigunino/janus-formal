import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusPhysicalSecondJetSmoothSectionAssembly
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeSecondOrderJetLocalSectionSmoothness4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatMetricSecondOrderJetSmoothVectorBundleSection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCSecondOrderJetSmoothVectorBundleSection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualLLSecondOrderJetSmoothVectorBundleSections4D

namespace JanusFormal
namespace P0EFTJanusProgramPActualSecondOrderJetSmoothCoreSectionCoordinates4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPActualThroatAbelianPotentialChartwiseSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetVectorBundleCore4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetLocalSectionSmoothness4D
open P0EFTJanusProgramPActualThroatMetricSecondOrderJetVectorBundleCore4D
open P0EFTJanusProgramPActualThroatMetricSecondOrderJetLocalSectionSmoothness4D
open P0EFTJanusProgramPActualThroatMetricSecondOrderJetSmoothVectorBundleSection4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderJetVectorBundleCore4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderJetLocalSectionSmoothness4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderJetSmoothVectorBundleSection4D
open P0EFTJanusProgramPActualThroatSmoothFieldSecondOrderJetOverlap4D
open P0EFTJanusProgramPActualThroatConstantFiberSecondOrderJetSmoothVectorBundleCore4D
open P0EFTJanusProgramPActualLLSecondOrderJetSmoothVectorBundleSections4D
open P0EFTJanusPhysicalSecondJetSmoothSectionAssembly

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

def actualThroatGaugeSecondOrderJetSmoothCoreSectionCoordinates
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2) :=
  smoothCoreSectionCoordinatesOfLocalRepresentatives
    throatCoverModelWithCorners
    (throatGaugeSecondOrderJetVectorBundleCore period hPeriod)
    (actualThroatGaugeSecondOrderJetLocalRepresentative
      period hPeriod potential component)
    (actualThroatGaugeSecondOrderJetLocalRepresentative_coordChange
      period hPeriod potential component)
    (actualThroatGaugeSecondOrderJetLocalRepresentative_contMDiffOn
      period hPeriod potential component)

def actualThroatMetricSecondOrderJetSmoothCoreSectionCoordinates
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod) :=
  smoothCoreSectionCoordinatesOfLocalRepresentatives
    throatCoverModelWithCorners
    (throatMetricSecondOrderJetVectorBundleCore period hPeriod)
    (actualThroatMetricSecondOrderJetLocalRepresentative period hPeriod tensor)
    (actualThroatMetricSecondOrderJetLocalRepresentative_compatible
      period hPeriod tensor)
    (actualThroatMetricSecondOrderJetLocalRepresentative_contMDiffOn
      period hPeriod tensor)

def actualThroatSpinCSecondOrderJetSmoothCoreSectionCoordinates
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice) :=
  smoothCoreSectionCoordinatesOfLocalRepresentatives
    throatCoverModelWithCorners
    (throatSpinCSecondOrderJetVectorBundleCore period hPeriod choice)
    (actualThroatSpinCSecondOrderJetLocalRepresentative
      period hPeriod choice state)
    (actualThroatSpinCSecondOrderJetLocalRepresentative_compatible
      period hPeriod choice state)
    (actualThroatSpinCSecondOrderJetLocalRepresentative_contMDiffOn
      period hPeriod choice state)

universe u

def actualThroatSmoothFieldSecondOrderJetSmoothCoreSectionCoordinates
    {Fiber : Type u}
    [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    [FiniteDimensional Real Fiber]
    (field : SmoothThroatField period hPeriod Fiber) :=
  smoothCoreSectionCoordinatesOfLocalRepresentatives
    throatCoverModelWithCorners
    (actualThroatConstantFiberSecondOrderJetSmoothVectorBundleCore
      period hPeriod (Fiber := Fiber))
    (throatSmoothFieldSecondOrderJetLocalRepresentative
      period hPeriod field)
    (throatSmoothFieldSecondOrderJetLocalRepresentative_compatible
      period hPeriod field)
    (throatSmoothFieldSecondOrderJetLocalRepresentative_contMDiffOn
      period hPeriod field)

def globalFieldConfigurationLLAuxMetricSecondOrderJetSmoothCoreSectionCoordinates
    (configuration : GlobalFieldConfiguration period hPeriod) :=
  actualThroatSmoothFieldSecondOrderJetSmoothCoreSectionCoordinates
    period hPeriod configuration.coefficientFields.llAuxMetric

def globalFieldConfigurationLLMeasureSecondOrderJetSmoothCoreSectionCoordinates
    (configuration : GlobalFieldConfiguration period hPeriod) :=
  actualThroatSmoothFieldSecondOrderJetSmoothCoreSectionCoordinates
    period hPeriod configuration.coefficientFields.llMeasure

def globalFieldConfigurationLLFieldSecondOrderJetSmoothCoreSectionCoordinates
    (configuration : GlobalFieldConfiguration period hPeriod) :=
  actualThroatSmoothFieldSecondOrderJetSmoothCoreSectionCoordinates
    period hPeriod configuration.coefficientFields.llField

end
end P0EFTJanusProgramPActualSecondOrderJetSmoothCoreSectionCoordinates4D
end JanusFormal
