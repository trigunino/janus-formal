import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCArbitraryTrivializationChartSecondOrderJetExtraction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCSecondOrderJetSemidirectTransport4D

/-!
# Open atlas data for actual throat SpinC second jets

The atlas is indexed by a primitive SpinC trivialization and an independently
selected extended base chart.  This gate records only the open cover,
pointwise valid trivialization/chart data and the zero raw SpinC second jet.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatSpinCSecondOrderJetBundleAtlasData4D

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPActualThroatSpinCArbitraryTrivializationChartSecondOrderJetExtraction4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatBase := MappingTorus (ThroatData period hPeriod)

local instance throatBaseChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance throatBaseIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (ThroatBase period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-! ## Open cover -/

/-- A SpinC second-jet patch is indexed by a primitive SpinC
trivialization and an extended base chart. -/
abbrev ThroatSpinCSecondOrderJetBundleIndex :=
  D9PrimitiveSpinCIndex period hPeriod × ThroatBase period hPeriod

/-- Common validity domain of the selected SpinC trivialization and base
chart. -/
def throatSpinCSecondOrderJetBundleBaseSet
    (index : ThroatSpinCSecondOrderJetBundleIndex period hPeriod) :
    Set (ThroatBase period hPeriod) :=
  d9PrimitiveSpinCBaseSet period hPeriod index.1 ∩
    (extChartAt throatCoverModelWithCorners index.2).source

theorem throatSpinCSecondOrderJetBundleBaseSet_isOpen
    (index : ThroatSpinCSecondOrderJetBundleIndex period hPeriod) :
    IsOpen (throatSpinCSecondOrderJetBundleBaseSet
      period hPeriod index) :=
  (d9PrimitiveSpinCBaseSet_isOpen period hPeriod index.1).inter
    (isOpen_extChartAt_source index.2)

/-- Preferred SpinC trivialization supplied by the canonical core, paired
with the extended chart centered at the current point. -/
def throatSpinCSecondOrderJetBundleIndexAt
    (current : ThroatBase period hPeriod) :
    ThroatSpinCSecondOrderJetBundleIndex period hPeriod :=
  ((d9PrimitiveSpinCVectorBundleCore period hPeriod .positiveQuarter).indexAt
      current,
    current)

theorem mem_throatSpinCSecondOrderJetBundleBaseSet_indexAt
    (current : ThroatBase period hPeriod) :
    current ∈ throatSpinCSecondOrderJetBundleBaseSet period hPeriod
      (throatSpinCSecondOrderJetBundleIndexAt period hPeriod current) :=
  ⟨(d9PrimitiveSpinCVectorBundleCore period hPeriod .positiveQuarter)
      |>.mem_baseSet_at current,
    mem_extChartAt_source current⟩

theorem exists_mem_throatSpinCSecondOrderJetBundleBaseSet
    (current : ThroatBase period hPeriod) :
    ∃ index : ThroatSpinCSecondOrderJetBundleIndex period hPeriod,
      current ∈ throatSpinCSecondOrderJetBundleBaseSet
        period hPeriod index :=
  ⟨throatSpinCSecondOrderJetBundleIndexAt period hPeriod current,
    mem_throatSpinCSecondOrderJetBundleBaseSet_indexAt
      period hPeriod current⟩

theorem iUnion_throatSpinCSecondOrderJetBundleBaseSet :
    (⋃ index : ThroatSpinCSecondOrderJetBundleIndex period hPeriod,
      throatSpinCSecondOrderJetBundleBaseSet period hPeriod index) =
        Set.univ := by
  apply Set.eq_univ_of_forall
  intro current
  exact Set.mem_iUnion.mpr
    (exists_mem_throatSpinCSecondOrderJetBundleBaseSet
      period hPeriod current)

/-! ## Pointwise data and zero jet -/

/-- A SpinC trivialization and base chart both valid at one throat point. -/
structure ThroatSpinCSecondOrderJetTrivializationChartAt
    (current : ThroatBase period hPeriod) where
  spinIndex : D9PrimitiveSpinCIndex period hPeriod
  chartAnchor : ThroatBase period hPeriod
  spin_mem : current ∈
    d9PrimitiveSpinCBaseSet period hPeriod spinIndex
  chart_mem : current ∈
    (extChartAt throatCoverModelWithCorners chartAnchor).source

/-- Convert a valid atlas index into the pointwise data consumed by future
SpinC semidirect transports. -/
def throatSpinCSecondOrderJetTrivializationChartAt
    (index : ThroatSpinCSecondOrderJetBundleIndex period hPeriod)
    (current : ThroatBase period hPeriod)
    (hCurrent : current ∈
      throatSpinCSecondOrderJetBundleBaseSet period hPeriod index) :
    ThroatSpinCSecondOrderJetTrivializationChartAt
      period hPeriod current where
  spinIndex := index.1
  chartAnchor := index.2
  spin_mem := hCurrent.1
  chart_mem := hCurrent.2

@[simp]
theorem throatSpinCSecondOrderJetTrivializationChartAt_spinIndex
    (index : ThroatSpinCSecondOrderJetBundleIndex period hPeriod)
    (current : ThroatBase period hPeriod)
    (hCurrent : current ∈
      throatSpinCSecondOrderJetBundleBaseSet period hPeriod index) :
    (throatSpinCSecondOrderJetTrivializationChartAt period hPeriod
      index current hCurrent).spinIndex = index.1 :=
  rfl

@[simp]
theorem throatSpinCSecondOrderJetTrivializationChartAt_chartAnchor
    (index : ThroatSpinCSecondOrderJetBundleIndex period hPeriod)
    (current : ThroatBase period hPeriod)
    (hCurrent : current ∈
      throatSpinCSecondOrderJetBundleBaseSet period hPeriod index) :
    (throatSpinCSecondOrderJetTrivializationChartAt period hPeriod
      index current hCurrent).chartAnchor = index.2 :=
  rfl

/-- Convert a valid atlas index directly into the pointwise record consumed
by the SpinC semidirect transport. -/
def throatSpinCSecondOrderJetSemidirectTrivializationChartAt
    (index : ThroatSpinCSecondOrderJetBundleIndex period hPeriod)
    (current : ThroatBase period hPeriod)
    (hCurrent : current ∈
      throatSpinCSecondOrderJetBundleBaseSet period hPeriod index) :
    P0EFTJanusProgramPActualThroatSpinCSecondOrderJetSemidirectTransport4D.ThroatSpinCSecondOrderJetTrivializationChartAt
      period hPeriod current where
  trivializationIndex := index.1
  chartAnchor := index.2
  trivialization_mem := hCurrent.1
  chart_mem := hCurrent.2

@[simp]
theorem throatSpinCSecondOrderJetSemidirectTrivializationChartAt_trivializationIndex
    (index : ThroatSpinCSecondOrderJetBundleIndex period hPeriod)
    (current : ThroatBase period hPeriod)
    (hCurrent : current ∈
      throatSpinCSecondOrderJetBundleBaseSet period hPeriod index) :
    (throatSpinCSecondOrderJetSemidirectTrivializationChartAt period hPeriod
      index current hCurrent).trivializationIndex = index.1 :=
  rfl

@[simp]
theorem throatSpinCSecondOrderJetSemidirectTrivializationChartAt_chartAnchor
    (index : ThroatSpinCSecondOrderJetBundleIndex period hPeriod)
    (current : ThroatBase period hPeriod)
    (hCurrent : current ∈
      throatSpinCSecondOrderJetBundleBaseSet period hPeriod index) :
    (throatSpinCSecondOrderJetSemidirectTrivializationChartAt period hPeriod
      index current hCurrent).chartAnchor = index.2 :=
  rfl

/-- Distinguished zero element of the raw framed SpinC second-jet carrier. -/
def zeroThroatSpinCFramedSecondOrderJet :
    FramedSecondOrderJet ThroatCoverCoordinates D9DoubledMatterFiber where
  value := 0
  firstDerivative := 0
  secondDerivative := 0
  secondDerivative_symmetric := by
    intro first second
    rfl

end
end P0EFTJanusProgramPActualThroatSpinCSecondOrderJetBundleAtlasData4D
end JanusFormal
