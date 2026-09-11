import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatMetricThirdOrderJetBundleCoordChangeContinuity4D

/-!
# Vector-bundle core for actual throat metric third jets

The metric frame/chart atlas and its continuous third-order coordinate
changes assemble into a topological `VectorBundleCore`.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatMetricThirdOrderJetVectorBundleCore4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPFramedThirdOrderJetConstantFiberBaseChange4D
open P0EFTJanusProgramPActualThroatCovariantTwoTensorSecondOrderFrameOverlap4D
open P0EFTJanusProgramPActualThroatMetricSecondOrderJetBundleAtlasData4D
open P0EFTJanusProgramPActualThroatMetricThirdOrderJetContinuousLinearCoordChange4D
open P0EFTJanusProgramPActualThroatMetricThirdOrderJetBundleCoordChangeContinuity4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev TensorModel :=
  FramedCovariantTwoTensor ThroatCoverCoordinates

attribute [local instance]
  P0EFTJanusProgramPActualThroatCovariantTwoTensorSecondOrderFrameOverlap4D.tensorModelNormedAddCommGroup
  P0EFTJanusProgramPActualThroatCovariantTwoTensorSecondOrderFrameOverlap4D.tensorModelNormedSpace

private abbrev MetricThirdJet :=
  FramedThirdOrderJet ThroatCoverCoordinates TensorModel

private abbrev BundleIndex :=
  ThroatMetricSecondOrderJetBundleIndex period hPeriod

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- Topological vector-bundle gluing data for actual throat metric third
jets. -/
def throatMetricThirdOrderJetVectorBundleCore :
    VectorBundleCore Real (EffectiveThroat period hPeriod) MetricThirdJet
      (BundleIndex period hPeriod) where
  baseSet := throatMetricSecondOrderJetBundleBaseSet period hPeriod
  isOpen_baseSet :=
    throatMetricSecondOrderJetBundleBaseSet_isOpen period hPeriod
  indexAt := throatMetricSecondOrderJetBundleIndexAt period hPeriod
  mem_baseSet_at :=
    mem_throatMetricSecondOrderJetBundleBaseSet_indexAt period hPeriod
  coordChange :=
    throatMetricThirdOrderJetBundleContinuousCoordChange period hPeriod
  coordChange_self index current hCurrent jet := by
    rw [throatMetricThirdOrderJetBundleContinuousCoordChange_self
      period hPeriod index current hCurrent]
    rfl
  continuousOn_coordChange :=
    throatMetricThirdOrderJetBundleContinuousCoordChange_continuousOn
      period hPeriod
  coordChange_comp first middle last current hCurrent jet := by
    have hComp :=
      throatMetricThirdOrderJetBundleContinuousCoordChange_comp period hPeriod
        first middle last current hCurrent
    exact congrArg
      (fun change : MetricThirdJet →L[Real] MetricThirdJet ↦ change jet) hComp

@[simp]
theorem throatMetricThirdOrderJetVectorBundleCore_baseSet
    (index : BundleIndex period hPeriod) :
    (throatMetricThirdOrderJetVectorBundleCore period hPeriod).baseSet index =
      throatMetricSecondOrderJetBundleBaseSet period hPeriod index :=
  rfl

@[simp]
theorem throatMetricThirdOrderJetVectorBundleCore_coordChange
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod) :
    (throatMetricThirdOrderJetVectorBundleCore period hPeriod).coordChange
        first second current =
      throatMetricThirdOrderJetBundleContinuousCoordChange period hPeriod
        first second current :=
  rfl

end
end P0EFTJanusProgramPActualThroatMetricThirdOrderJetVectorBundleCore4D
end JanusFormal
