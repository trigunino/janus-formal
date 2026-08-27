import Mathlib.Geometry.Manifold.VectorBundle.Basic
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatMetricSecondOrderJetVectorBundleCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatMetricSecondOrderJetBundleCoordChangeSmoothness4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFrameChartPairSecondJetVectorBundleCore4D

/-!
# Smooth vector-bundle core for actual throat metric second jets

The smooth overlap theorem upgrades the metric second-jet core to a `C∞`
vector bundle.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatMetricSecondOrderJetSmoothVectorBundleCore4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPActualThroatMetricSecondOrderJetSemidirectTransport4D
open P0EFTJanusProgramPActualThroatMetricSecondOrderJetBundleAtlasData4D
open P0EFTJanusProgramPActualThroatMetricSecondOrderJetBundleCoordChange4D
open P0EFTJanusProgramPActualThroatMetricSecondOrderJetBundleCoordChangeSmoothness4D
open P0EFTJanusProgramPActualThroatMetricSecondOrderJetVectorBundleCore4D
open P0EFTJanusProgramPFrameChartPairSecondJetVectorBundleCore4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev TensorModel :=
  FramedCovariantTwoTensor ThroatCoverCoordinates

private abbrev MetricJet :=
  FramedSecondOrderJet ThroatCoverCoordinates TensorModel

local instance tensorModelNormedAddCommGroup :
    NormedAddCommGroup TensorModel :=
  P0EFTJanusProgramPActualThroatMetricSecondOrderJetSemidirectTransport4D.tensorModelNormedAddCommGroup

local instance tensorModelNormedSpace : NormedSpace Real TensorModel :=
  P0EFTJanusProgramPActualThroatMetricSecondOrderJetSemidirectTransport4D.tensorModelNormedSpace

/-- The associated fiber family of the metric second-jet core. -/
abbrev ThroatMetricSecondOrderJetBundleFiber :=
  (throatMetricSecondOrderJetVectorBundleCore period hPeriod).Fiber

/-- The metric second-jet vector-bundle core has smooth coordinate changes. -/
theorem throatMetricSecondOrderJetVectorBundleCore_isContMDiff :
    letI : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
      P0EFTJanusProgramPActualThroatMetricSecondOrderJetBundleCoordChangeSmoothness4D.effectiveThroatChartedSpace
        period hPeriod
    (throatMetricSecondOrderJetVectorBundleCore period hPeriod).IsContMDiff
      throatCoverModelWithCorners ∞ := by
  letI : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
    P0EFTJanusProgramPActualThroatMetricSecondOrderJetBundleCoordChangeSmoothness4D.effectiveThroatChartedSpace
      period hPeriod
  simpa only [throatMetricSecondOrderJetVectorBundleCore] using
    (frameChartPairSecondJetVectorBundleCore_isContMDiff
      throatCoverModelWithCorners ∞
      (throatMetricSecondOrderJetBundleBaseSet period hPeriod)
      (throatMetricSecondOrderJetBundleBaseSet_isOpen period hPeriod)
      (throatMetricSecondOrderJetBundleIndexAt period hPeriod)
      (mem_throatMetricSecondOrderJetBundleBaseSet_indexAt period hPeriod)
      (throatMetricSecondOrderJetBundleCoordChange period hPeriod)
      (throatMetricSecondOrderJetBundleCoordChange_self period hPeriod)
      (throatMetricSecondOrderJetBundleCoordChange_continuousOn period hPeriod)
      (throatMetricSecondOrderJetBundleCoordChange_comp period hPeriod)
      (throatMetricSecondOrderJetBundleCoordChange_contMDiffOn
        period hPeriod))

/-- The metric second-jet fiber family is a smooth vector bundle. -/
theorem throatMetricSecondOrderJetBundleFiber_isContMDiffVectorBundle :
    letI : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
      P0EFTJanusProgramPActualThroatMetricSecondOrderJetBundleCoordChangeSmoothness4D.effectiveThroatChartedSpace
        period hPeriod
    letI :
        (throatMetricSecondOrderJetVectorBundleCore period hPeriod).IsContMDiff
          throatCoverModelWithCorners ∞ :=
      throatMetricSecondOrderJetVectorBundleCore_isContMDiff period hPeriod
    ContMDiffVectorBundle ∞ MetricJet
      (ThroatMetricSecondOrderJetBundleFiber period hPeriod)
      throatCoverModelWithCorners := by
  letI : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
    P0EFTJanusProgramPActualThroatMetricSecondOrderJetBundleCoordChangeSmoothness4D.effectiveThroatChartedSpace
      period hPeriod
  letI :
      (throatMetricSecondOrderJetVectorBundleCore period hPeriod).IsContMDiff
        throatCoverModelWithCorners ∞ :=
    throatMetricSecondOrderJetVectorBundleCore_isContMDiff period hPeriod
  infer_instance

end
end P0EFTJanusProgramPActualThroatMetricSecondOrderJetSmoothVectorBundleCore4D
end JanusFormal
