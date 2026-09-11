import Mathlib.Geometry.Manifold.VectorBundle.Basic
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatMetricThirdOrderJetVectorBundleCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatMetricThirdOrderJetBundleCoordChangeSmoothness4D

/-!
# Smooth vector-bundle core for actual throat metric third jets

The smooth overlap theorem upgrades the metric third-jet topological core to
a `C∞` vector bundle.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatMetricThirdOrderJetSmoothVectorBundleCore4D

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
open P0EFTJanusProgramPActualThroatMetricThirdOrderJetBundleCoordChangeSmoothness4D
open P0EFTJanusProgramPActualThroatMetricThirdOrderJetVectorBundleCore4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev TensorModel :=
  FramedCovariantTwoTensor ThroatCoverCoordinates

local instance tensorModelNormedAddCommGroup :
    NormedAddCommGroup TensorModel :=
  P0EFTJanusProgramPActualThroatCovariantTwoTensorSecondOrderFrameOverlap4D.tensorModelNormedAddCommGroup

local instance tensorModelNormedSpace : NormedSpace Real TensorModel :=
  P0EFTJanusProgramPActualThroatCovariantTwoTensorSecondOrderFrameOverlap4D.tensorModelNormedSpace

private abbrev MetricThirdJet :=
  FramedThirdOrderJet ThroatCoverCoordinates TensorModel

/-- The associated fiber family of the metric third-jet vector-bundle core. -/
abbrev ThroatMetricThirdOrderJetBundleFiber :=
  (throatMetricThirdOrderJetVectorBundleCore period hPeriod).Fiber

/-- The metric third-jet vector-bundle core has smooth coordinate changes. -/
theorem throatMetricThirdOrderJetVectorBundleCore_isContMDiff :
    letI : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
      P0EFTJanusProgramPActualThroatMetricThirdOrderJetBundleCoordChangeSmoothness4D.effectiveThroatChartedSpace
        period hPeriod
    (throatMetricThirdOrderJetVectorBundleCore period hPeriod).IsContMDiff
      throatCoverModelWithCorners ∞ := by
  letI : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
    P0EFTJanusProgramPActualThroatMetricThirdOrderJetBundleCoordChangeSmoothness4D.effectiveThroatChartedSpace
      period hPeriod
  constructor
  intro first second
  convert
    throatMetricThirdOrderJetBundleContinuousCoordChange_contMDiffOn
      period hPeriod first second using 1 <;> rfl

/-- The metric third-jet fiber family is a smooth vector bundle. -/
theorem throatMetricThirdOrderJetBundleFiber_isContMDiffVectorBundle :
    letI : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
      P0EFTJanusProgramPActualThroatMetricThirdOrderJetBundleCoordChangeSmoothness4D.effectiveThroatChartedSpace
        period hPeriod
    letI :
        (throatMetricThirdOrderJetVectorBundleCore period hPeriod).IsContMDiff
          throatCoverModelWithCorners ∞ :=
      throatMetricThirdOrderJetVectorBundleCore_isContMDiff period hPeriod
    ContMDiffVectorBundle ∞ MetricThirdJet
      (ThroatMetricThirdOrderJetBundleFiber period hPeriod)
      throatCoverModelWithCorners := by
  letI : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
    P0EFTJanusProgramPActualThroatMetricThirdOrderJetBundleCoordChangeSmoothness4D.effectiveThroatChartedSpace
      period hPeriod
  letI :
      (throatMetricThirdOrderJetVectorBundleCore period hPeriod).IsContMDiff
        throatCoverModelWithCorners ∞ :=
    throatMetricThirdOrderJetVectorBundleCore_isContMDiff period hPeriod
  infer_instance

end
end P0EFTJanusProgramPActualThroatMetricThirdOrderJetSmoothVectorBundleCore4D
end JanusFormal
