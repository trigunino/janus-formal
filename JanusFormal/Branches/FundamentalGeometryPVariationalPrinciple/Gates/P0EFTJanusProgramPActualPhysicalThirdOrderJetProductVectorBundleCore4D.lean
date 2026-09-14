import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualLLThirdOrderJetProductVectorBundleCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeThirdOrderJetSmoothVectorBundleCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatMetricThirdOrderJetSmoothVectorBundleCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCThirdOrderJetSmoothVectorBundleCore4D

/-!
# Actual physical third-order jet product vector-bundle core

The gauge, LL, metric and SpinC third-jet cores assemble through the existing
generic physical product construction.  This gate contains no extraction or
section data.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualPhysicalThirdOrderJetProductVectorBundleCore4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPFramedThirdOrderJetConstantFiberBaseChange4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetBundleAtlasData4D
open P0EFTJanusProgramPActualThroatGaugeThirdOrderJetVectorBundleCore4D
open P0EFTJanusProgramPActualThroatGaugeThirdOrderJetSmoothVectorBundleCore4D
open P0EFTJanusProgramPActualThroatMetricSecondOrderJetBundleAtlasData4D
open P0EFTJanusProgramPActualThroatMetricThirdOrderJetVectorBundleCore4D
open P0EFTJanusProgramPActualThroatMetricThirdOrderJetSmoothVectorBundleCore4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderJetBundleAtlasData4D
open P0EFTJanusProgramPActualThroatSpinCThirdOrderJetVectorBundleCore4D
open P0EFTJanusProgramPActualThroatSpinCThirdOrderJetSmoothVectorBundleCore4D
open P0EFTJanusProgramPActualLLThirdOrderJetProductCoordChange4D
open P0EFTJanusProgramPActualLLThirdOrderJetProductVectorBundleCore4D
open P0EFTJanusPhysicalSecondJetCommonRefinedAtlas
open P0EFTJanusPhysicalSecondJetProductVectorBundleCore
open P0EFTJanusPhysicalSecondJetSmoothVectorBundleCore

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

abbrev ActualGaugeThirdOrderJetFiber :=
  FramedThirdOrderJet ThroatCoverCoordinates
    (FramedCovector ThroatCoverCoordinates)

abbrev ActualGaugeThirdOrderJetProductFiber :=
  (ActualGaugeThirdOrderJetFiber × ActualGaugeThirdOrderJetFiber) ×
    (ActualGaugeThirdOrderJetFiber × ActualGaugeThirdOrderJetFiber)

abbrev ActualGaugeThirdOrderJetProductBundleIndex :=
  (ThroatGaugeSecondOrderJetBundleIndex period hPeriod ×
      ThroatGaugeSecondOrderJetBundleIndex period hPeriod) ×
    (ThroatGaugeSecondOrderJetBundleIndex period hPeriod ×
      ThroatGaugeSecondOrderJetBundleIndex period hPeriod)

/-- Product core of the four physical gauge third jets. -/
def actualGaugeThirdOrderJetProductVectorBundleCore :
    VectorBundleCore Real (EffectiveThroat period hPeriod)
      ActualGaugeThirdOrderJetProductFiber
      (ActualGaugeThirdOrderJetProductBundleIndex period hPeriod) :=
  vectorBundleCoreProd
    (vectorBundleCoreProd
      (throatGaugeThirdOrderJetVectorBundleCore period hPeriod)
      (throatGaugeThirdOrderJetVectorBundleCore period hPeriod))
    (vectorBundleCoreProd
      (throatGaugeThirdOrderJetVectorBundleCore period hPeriod)
      (throatGaugeThirdOrderJetVectorBundleCore period hPeriod))

theorem actualGaugeThirdOrderJetProductVectorBundleCore_isContMDiff :
    (actualGaugeThirdOrderJetProductVectorBundleCore period hPeriod).IsContMDiff
      throatCoverModelWithCorners ∞ := by
  letI :
      (throatGaugeThirdOrderJetVectorBundleCore period hPeriod).IsContMDiff
        throatCoverModelWithCorners ∞ :=
    throatGaugeThirdOrderJetVectorBundleCore_isContMDiff period hPeriod
  letI :
      (vectorBundleCoreProd
        (throatGaugeThirdOrderJetVectorBundleCore period hPeriod)
        (throatGaugeThirdOrderJetVectorBundleCore period hPeriod)).IsContMDiff
          throatCoverModelWithCorners ∞ :=
    vectorBundleCoreProd_isContMDiff throatCoverModelWithCorners
      (throatGaugeThirdOrderJetVectorBundleCore period hPeriod)
      (throatGaugeThirdOrderJetVectorBundleCore period hPeriod)
  exact vectorBundleCoreProd_isContMDiff throatCoverModelWithCorners
    (vectorBundleCoreProd
      (throatGaugeThirdOrderJetVectorBundleCore period hPeriod)
      (throatGaugeThirdOrderJetVectorBundleCore period hPeriod))
    (vectorBundleCoreProd
      (throatGaugeThirdOrderJetVectorBundleCore period hPeriod)
      (throatGaugeThirdOrderJetVectorBundleCore period hPeriod))

abbrev ActualMetricThirdOrderJetFiber :=
  FramedThirdOrderJet ThroatCoverCoordinates
    (FramedCovariantTwoTensor ThroatCoverCoordinates)

abbrev ActualMetricThirdOrderJetProductFiber :=
  ActualMetricThirdOrderJetFiber × ActualMetricThirdOrderJetFiber

abbrev ActualMetricThirdOrderJetProductBundleIndex :=
  ThroatMetricSecondOrderJetBundleIndex period hPeriod ×
    ThroatMetricSecondOrderJetBundleIndex period hPeriod

/-- Product core of the two physical metric third jets. -/
def actualMetricThirdOrderJetProductVectorBundleCore :
    VectorBundleCore Real (EffectiveThroat period hPeriod)
      ActualMetricThirdOrderJetProductFiber
      (ActualMetricThirdOrderJetProductBundleIndex period hPeriod) :=
  vectorBundleCoreProd
    (throatMetricThirdOrderJetVectorBundleCore period hPeriod)
    (throatMetricThirdOrderJetVectorBundleCore period hPeriod)

theorem actualMetricThirdOrderJetProductVectorBundleCore_isContMDiff :
    (actualMetricThirdOrderJetProductVectorBundleCore period hPeriod).IsContMDiff
      throatCoverModelWithCorners ∞ := by
  letI :
      (throatMetricThirdOrderJetVectorBundleCore period hPeriod).IsContMDiff
        throatCoverModelWithCorners ∞ :=
    throatMetricThirdOrderJetVectorBundleCore_isContMDiff period hPeriod
  exact vectorBundleCoreProd_isContMDiff throatCoverModelWithCorners
    (throatMetricThirdOrderJetVectorBundleCore period hPeriod)
    (throatMetricThirdOrderJetVectorBundleCore period hPeriod)

abbrev ActualSpinCThirdOrderJetFiber :=
  FramedThirdOrderJet ThroatCoverCoordinates D9DoubledMatterFiber

abbrev ActualSpinCThirdOrderJetProductFiber :=
  ActualSpinCThirdOrderJetFiber × ActualSpinCThirdOrderJetFiber

abbrev ActualSpinCThirdOrderJetProductBundleIndex :=
  ThroatSpinCSecondOrderJetBundleIndex period hPeriod ×
    ThroatSpinCSecondOrderJetBundleIndex period hPeriod

/-- Product core of the two physical SpinC third jets. -/
def actualSpinCThirdOrderJetProductVectorBundleCore
    (choice : NormalRootChoice) :
    VectorBundleCore Real (EffectiveThroat period hPeriod)
      ActualSpinCThirdOrderJetProductFiber
      (ActualSpinCThirdOrderJetProductBundleIndex period hPeriod) :=
  vectorBundleCoreProd
    (throatSpinCThirdOrderJetVectorBundleCore period hPeriod choice)
    (throatSpinCThirdOrderJetVectorBundleCore period hPeriod choice)

theorem actualSpinCThirdOrderJetProductVectorBundleCore_isContMDiff
    (choice : NormalRootChoice) :
    (actualSpinCThirdOrderJetProductVectorBundleCore
      period hPeriod choice).IsContMDiff throatCoverModelWithCorners ∞ := by
  letI :
      (throatSpinCThirdOrderJetVectorBundleCore
        period hPeriod choice).IsContMDiff throatCoverModelWithCorners ∞ :=
    throatSpinCThirdOrderJetVectorBundleCore_isContMDiff
      period hPeriod choice
  exact vectorBundleCoreProd_isContMDiff throatCoverModelWithCorners
    (throatSpinCThirdOrderJetVectorBundleCore period hPeriod choice)
    (throatSpinCThirdOrderJetVectorBundleCore period hPeriod choice)

abbrev ActualPhysicalThirdOrderJetProductFiber :=
  PhysicalSecondJetFiber
    (GaugeFiber := ActualGaugeThirdOrderJetProductFiber)
    (LLFiber := ActualLLThirdOrderJetFiber)
    (MetricFiber := ActualMetricThirdOrderJetProductFiber)
    (SpinCFiber := ActualSpinCThirdOrderJetProductFiber)

abbrev ActualPhysicalThirdOrderJetProductBundleIndex :=
  PhysicalCommonChart
    (ActualGaugeThirdOrderJetProductBundleIndex period hPeriod)
    (ActualLLThirdOrderJetBundleIndex period hPeriod)
    (ActualMetricThirdOrderJetProductBundleIndex period hPeriod)
    (ActualSpinCThirdOrderJetProductBundleIndex period hPeriod)

/-- Product core of all eleven physical third-jet components. -/
def actualPhysicalThirdOrderJetProductVectorBundleCore
    (choice : NormalRootChoice) :
    VectorBundleCore Real (EffectiveThroat period hPeriod)
      ActualPhysicalThirdOrderJetProductFiber
      (ActualPhysicalThirdOrderJetProductBundleIndex period hPeriod) :=
  physicalSecondJetVectorBundleCore
    (actualGaugeThirdOrderJetProductVectorBundleCore period hPeriod)
    (actualLLThirdOrderJetProductVectorBundleCore period hPeriod)
    (actualMetricThirdOrderJetProductVectorBundleCore period hPeriod)
    (actualSpinCThirdOrderJetProductVectorBundleCore period hPeriod choice)

/-- The complete physical third-jet product core has smooth transitions. -/
theorem actualPhysicalThirdOrderJetProductVectorBundleCore_isContMDiff
    (choice : NormalRootChoice) :
    (actualPhysicalThirdOrderJetProductVectorBundleCore
      period hPeriod choice).IsContMDiff throatCoverModelWithCorners ∞ := by
  letI :
      (actualGaugeThirdOrderJetProductVectorBundleCore
        period hPeriod).IsContMDiff throatCoverModelWithCorners ∞ :=
    actualGaugeThirdOrderJetProductVectorBundleCore_isContMDiff
      period hPeriod
  letI :
      (actualLLThirdOrderJetProductVectorBundleCore
        period hPeriod).IsContMDiff throatCoverModelWithCorners ∞ :=
    actualLLThirdOrderJetProductVectorBundleCore_isContMDiff period hPeriod
  letI :
      (actualMetricThirdOrderJetProductVectorBundleCore
        period hPeriod).IsContMDiff throatCoverModelWithCorners ∞ :=
    actualMetricThirdOrderJetProductVectorBundleCore_isContMDiff
      period hPeriod
  letI :
      (actualSpinCThirdOrderJetProductVectorBundleCore
        period hPeriod choice).IsContMDiff throatCoverModelWithCorners ∞ :=
    actualSpinCThirdOrderJetProductVectorBundleCore_isContMDiff
      period hPeriod choice
  exact physicalSecondJetVectorBundleCore_isContMDiff throatCoverModelWithCorners
    (actualGaugeThirdOrderJetProductVectorBundleCore period hPeriod)
    (actualLLThirdOrderJetProductVectorBundleCore period hPeriod)
    (actualMetricThirdOrderJetProductVectorBundleCore period hPeriod)
    (actualSpinCThirdOrderJetProductVectorBundleCore period hPeriod choice)

end
end P0EFTJanusProgramPActualPhysicalThirdOrderJetProductVectorBundleCore4D
end JanusFormal
