import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatMetricSecondOrderJetBundleCoordChange4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFrameChartPairSecondJetVectorBundleCore4D

/-!
# Vector-bundle core for actual throat metric second jets

The metric frame/chart atlas and its continuous semidirect coordinate changes
assemble into a topological `VectorBundleCore` through the generic
frame/chart-pair constructor.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatMetricSecondOrderJetVectorBundleCore4D

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

private abbrev BundleIndex :=
  ThroatMetricSecondOrderJetBundleIndex period hPeriod

local instance tensorModelNormedAddCommGroup :
    NormedAddCommGroup TensorModel :=
  P0EFTJanusProgramPActualThroatMetricSecondOrderJetSemidirectTransport4D.tensorModelNormedAddCommGroup

local instance tensorModelNormedSpace : NormedSpace Real TensorModel :=
  P0EFTJanusProgramPActualThroatMetricSecondOrderJetSemidirectTransport4D.tensorModelNormedSpace

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- Topological vector-bundle gluing data for actual throat metric second
jets. -/
def throatMetricSecondOrderJetVectorBundleCore :
    VectorBundleCore Real (EffectiveThroat period hPeriod) MetricJet
      (BundleIndex period hPeriod) :=
  frameChartPairSecondJetVectorBundleCore
    (throatMetricSecondOrderJetBundleBaseSet period hPeriod)
    (throatMetricSecondOrderJetBundleBaseSet_isOpen period hPeriod)
    (throatMetricSecondOrderJetBundleIndexAt period hPeriod)
    (mem_throatMetricSecondOrderJetBundleBaseSet_indexAt period hPeriod)
    (throatMetricSecondOrderJetBundleCoordChange period hPeriod)
    (throatMetricSecondOrderJetBundleCoordChange_self period hPeriod)
    (throatMetricSecondOrderJetBundleCoordChange_continuousOn period hPeriod)
    (throatMetricSecondOrderJetBundleCoordChange_comp period hPeriod)

@[simp]
theorem throatMetricSecondOrderJetVectorBundleCore_baseSet
    (index : BundleIndex period hPeriod) :
    (throatMetricSecondOrderJetVectorBundleCore period hPeriod).baseSet index =
      throatMetricSecondOrderJetBundleBaseSet period hPeriod index :=
  rfl

@[simp]
theorem throatMetricSecondOrderJetVectorBundleCore_coordChange
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod) :
    (throatMetricSecondOrderJetVectorBundleCore period hPeriod).coordChange
        first second current =
      throatMetricSecondOrderJetBundleCoordChange period hPeriod
        first second current :=
  rfl

end
end P0EFTJanusProgramPActualThroatMetricSecondOrderJetVectorBundleCore4D
end JanusFormal
