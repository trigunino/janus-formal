import Mathlib.Analysis.Normed.Module.RCLike.Real
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPresentationSetoid4D

/-!
# Open atlas data for throat gauge second jets

This gate records only an open cover indexed by a tangent-frame anchor and a
base-chart anchor, together with a zero-jet presentation on each valid patch.
It does not construct a fiber bundle or assert continuity of transition maps.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatGaugeSecondOrderJetBundleAtlasData4D

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
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPresentationSetoid4D

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

/-! ## Open cover -/

/-- A patch is indexed by its tangent-frame anchor and base-chart anchor. -/
abbrev ThroatGaugeSecondOrderJetBundleIndex :=
  EffectiveThroat period hPeriod × EffectiveThroat period hPeriod

/-- Common validity domain of the selected tangent frame and base chart. -/
def throatGaugeSecondOrderJetBundleBaseSet
    (index : ThroatGaugeSecondOrderJetBundleIndex period hPeriod) :
    Set (EffectiveThroat period hPeriod) :=
  (trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) index.1).baseSet ∩
    (extChartAt throatCoverModelWithCorners index.2).source

theorem throatGaugeSecondOrderJetBundleBaseSet_isOpen
    (index : ThroatGaugeSecondOrderJetBundleIndex period hPeriod) :
    IsOpen (throatGaugeSecondOrderJetBundleBaseSet period hPeriod index) :=
  (trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) index.1).open_baseSet.inter
    (isOpen_extChartAt_source index.2)

/-- The frame and chart both centered at the current point. -/
def throatGaugeSecondOrderJetBundleIndexAt
    (current : EffectiveThroat period hPeriod) :
    ThroatGaugeSecondOrderJetBundleIndex period hPeriod :=
  (current, current)

theorem mem_throatGaugeSecondOrderJetBundleBaseSet_indexAt
    (current : EffectiveThroat period hPeriod) :
    current ∈ throatGaugeSecondOrderJetBundleBaseSet period hPeriod
      (throatGaugeSecondOrderJetBundleIndexAt period hPeriod current) :=
  ⟨FiberBundle.mem_baseSet_trivializationAt' current,
    mem_extChartAt_source current⟩

theorem exists_mem_throatGaugeSecondOrderJetBundleBaseSet
    (current : EffectiveThroat period hPeriod) :
    ∃ index : ThroatGaugeSecondOrderJetBundleIndex period hPeriod,
      current ∈ throatGaugeSecondOrderJetBundleBaseSet period hPeriod index :=
  ⟨throatGaugeSecondOrderJetBundleIndexAt period hPeriod current,
    mem_throatGaugeSecondOrderJetBundleBaseSet_indexAt period hPeriod current⟩

theorem iUnion_throatGaugeSecondOrderJetBundleBaseSet :
    (⋃ index : ThroatGaugeSecondOrderJetBundleIndex period hPeriod,
      throatGaugeSecondOrderJetBundleBaseSet period hPeriod index) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro current
  exact Set.mem_iUnion.mpr
    (exists_mem_throatGaugeSecondOrderJetBundleBaseSet
      period hPeriod current)

/-! ## A zero-jet local template -/

/-- The distinguished zero element of the raw framed second-jet carrier. -/
def zeroThroatGaugeFramedSecondOrderJet :
    FramedSecondOrderJet ThroatCoverCoordinates
      (FramedCovector ThroatCoverCoordinates) where
  value := 0
  firstDerivative := 0
  secondDerivative := 0
  secondDerivative_symmetric := by
    intro first second
    rfl

/-- A zero-jet presentation attached to any point of an atlas patch. -/
def zeroThroatGaugeSecondOrderJetPresentationAt
    (index : ThroatGaugeSecondOrderJetBundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatGaugeSecondOrderJetBundleBaseSet period hPeriod index) :
    ThroatGaugeSecondOrderJetPresentationAt period hPeriod current where
  frameAnchor := index.1
  chartAnchor := index.2
  frame_mem := hCurrent.1
  chart_mem := hCurrent.2
  jet := zeroThroatGaugeFramedSecondOrderJet

end
end P0EFTJanusProgramPActualThroatGaugeSecondOrderJetBundleAtlasData4D
end JanusFormal
