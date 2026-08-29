import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatMetricSecondOrderJetSemidirectTransport4D

/-!
# Open atlas data for actual throat metric second jets

The atlas is indexed by a tangent-frame anchor and an extended-chart anchor.
This gate records the open cover, a raw zero metric jet and the conversion of
an atlas index valid at a point into the pointwise frame/chart type used by
the metric semidirect transport.  No setoid or bundle descent is introduced.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatMetricSecondOrderJetBundleAtlasData4D

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff RealInnerProductSpace Topology
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPActualThroatMetricSecondOrderJetSemidirectTransport4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev TensorModel :=
  FramedCovariantTwoTensor ThroatCoverCoordinates

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

/-! ## Open cover -/

/-- A metric second-jet patch is indexed by a tangent frame and base chart. -/
abbrev ThroatMetricSecondOrderJetBundleIndex :=
  EffectiveThroat period hPeriod × EffectiveThroat period hPeriod

/-- Common validity domain of the selected tangent frame and base chart. -/
def throatMetricSecondOrderJetBundleBaseSet
    (index : ThroatMetricSecondOrderJetBundleIndex period hPeriod) :
    Set (EffectiveThroat period hPeriod) :=
  (trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) index.1).baseSet ∩
    (extChartAt throatCoverModelWithCorners index.2).source

theorem throatMetricSecondOrderJetBundleBaseSet_isOpen
    (index : ThroatMetricSecondOrderJetBundleIndex period hPeriod) :
    IsOpen (throatMetricSecondOrderJetBundleBaseSet period hPeriod index) :=
  (trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) index.1).open_baseSet.inter
    (isOpen_extChartAt_source index.2)

/-- The diagonal frame/chart index centered at the current point. -/
def throatMetricSecondOrderJetBundleIndexAt
    (current : EffectiveThroat period hPeriod) :
    ThroatMetricSecondOrderJetBundleIndex period hPeriod :=
  (current, current)

theorem mem_throatMetricSecondOrderJetBundleBaseSet_indexAt
    (current : EffectiveThroat period hPeriod) :
    current ∈ throatMetricSecondOrderJetBundleBaseSet period hPeriod
      (throatMetricSecondOrderJetBundleIndexAt period hPeriod current) :=
  ⟨FiberBundle.mem_baseSet_trivializationAt' current,
    mem_extChartAt_source current⟩

theorem exists_mem_throatMetricSecondOrderJetBundleBaseSet
    (current : EffectiveThroat period hPeriod) :
    ∃ index : ThroatMetricSecondOrderJetBundleIndex period hPeriod,
      current ∈ throatMetricSecondOrderJetBundleBaseSet period hPeriod index :=
  ⟨throatMetricSecondOrderJetBundleIndexAt period hPeriod current,
    mem_throatMetricSecondOrderJetBundleBaseSet_indexAt period hPeriod current⟩

theorem iUnion_throatMetricSecondOrderJetBundleBaseSet :
    (⋃ index : ThroatMetricSecondOrderJetBundleIndex period hPeriod,
      throatMetricSecondOrderJetBundleBaseSet period hPeriod index) =
        Set.univ := by
  apply Set.eq_univ_of_forall
  intro current
  exact Set.mem_iUnion.mpr
    (exists_mem_throatMetricSecondOrderJetBundleBaseSet
      period hPeriod current)

/-! ## Pointwise frame/chart data and zero jet -/

/-- Convert an atlas index valid at `current` into the pointwise frame/chart
type consumed by metric semidirect transport. -/
def throatMetricSecondOrderJetFrameChartAt
    (index : ThroatMetricSecondOrderJetBundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatMetricSecondOrderJetBundleBaseSet period hPeriod index) :
    ThroatMetricSecondOrderJetFrameChartAt period hPeriod current where
  frameAnchor := index.1
  chartAnchor := index.2
  frame_mem := hCurrent.1
  chart_mem := hCurrent.2

@[simp]
theorem throatMetricSecondOrderJetFrameChartAt_frameAnchor
    (index : ThroatMetricSecondOrderJetBundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatMetricSecondOrderJetBundleBaseSet period hPeriod index) :
    (throatMetricSecondOrderJetFrameChartAt period hPeriod
      index current hCurrent).frameAnchor = index.1 :=
  rfl

@[simp]
theorem throatMetricSecondOrderJetFrameChartAt_chartAnchor
    (index : ThroatMetricSecondOrderJetBundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatMetricSecondOrderJetBundleBaseSet period hPeriod index) :
    (throatMetricSecondOrderJetFrameChartAt period hPeriod
      index current hCurrent).chartAnchor = index.2 :=
  rfl

/-- Distinguished zero element of the raw framed metric second-jet carrier. -/
def zeroThroatMetricFramedSecondOrderJet :
    FramedSecondOrderJet ThroatCoverCoordinates TensorModel where
  value := 0
  firstDerivative := 0
  secondDerivative := 0
  secondDerivative_symmetric := by
    intro first second
    rfl

end
end P0EFTJanusProgramPActualThroatMetricSecondOrderJetBundleAtlasData4D
end JanusFormal
