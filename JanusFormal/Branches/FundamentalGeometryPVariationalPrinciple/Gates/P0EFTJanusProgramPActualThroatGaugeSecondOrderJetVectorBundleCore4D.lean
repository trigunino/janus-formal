import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeSecondOrderJetBundleCoordChange4D

/-!
# Vector-bundle core for actual throat gauge second jets

The open frame/chart atlas and its continuous semidirect coordinate changes
assemble into a genuine topological `VectorBundleCore`.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatGaugeSecondOrderJetVectorBundleCore4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetBundleAtlasData4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetBundleCoordChange4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev GaugeJet :=
  FramedSecondOrderJet ThroatCoverCoordinates
    (FramedCovector ThroatCoverCoordinates)

private abbrev BundleIndex :=
  ThroatGaugeSecondOrderJetBundleIndex period hPeriod

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- Topological vector-bundle gluing data for actual throat gauge second jets. -/
def throatGaugeSecondOrderJetVectorBundleCore :
    VectorBundleCore Real (EffectiveThroat period hPeriod) GaugeJet
      (BundleIndex period hPeriod) where
  baseSet := throatGaugeSecondOrderJetBundleBaseSet period hPeriod
  isOpen_baseSet :=
    throatGaugeSecondOrderJetBundleBaseSet_isOpen period hPeriod
  indexAt := throatGaugeSecondOrderJetBundleIndexAt period hPeriod
  mem_baseSet_at :=
    mem_throatGaugeSecondOrderJetBundleBaseSet_indexAt period hPeriod
  coordChange := throatGaugeSecondOrderJetBundleCoordChange period hPeriod
  coordChange_self index current hCurrent jet := by
    rw [throatGaugeSecondOrderJetBundleCoordChange_self period hPeriod
      index current hCurrent]
    rfl
  continuousOn_coordChange :=
    throatGaugeSecondOrderJetBundleCoordChange_continuousOn period hPeriod
  coordChange_comp first middle last current hCurrent jet := by
    have hComp := throatGaugeSecondOrderJetBundleCoordChange_comp period hPeriod
      first middle last current hCurrent
    exact congrArg (fun change : GaugeJet →L[Real] GaugeJet ↦ change jet) hComp

@[simp]
theorem throatGaugeSecondOrderJetVectorBundleCore_baseSet
    (index : BundleIndex period hPeriod) :
    (throatGaugeSecondOrderJetVectorBundleCore period hPeriod).baseSet index =
      throatGaugeSecondOrderJetBundleBaseSet period hPeriod index :=
  rfl

@[simp]
theorem throatGaugeSecondOrderJetVectorBundleCore_coordChange
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod) :
    (throatGaugeSecondOrderJetVectorBundleCore period hPeriod).coordChange
        first second current =
      throatGaugeSecondOrderJetBundleCoordChange period hPeriod
        first second current :=
  rfl

end
end P0EFTJanusProgramPActualThroatGaugeSecondOrderJetVectorBundleCore4D
end JanusFormal
