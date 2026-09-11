import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeThirdOrderJetBundleCoordChangeContinuity4D

/-!
# Vector-bundle core for actual throat gauge third jets

The open frame/chart atlas and its continuous semidirect coordinate changes
assemble into a topological `VectorBundleCore`.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatGaugeThirdOrderJetVectorBundleCore4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPFramedThirdOrderJetConstantFiberBaseChange4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetBundleAtlasData4D
open P0EFTJanusProgramPActualThroatGaugeThirdOrderJetContinuousLinearCoordChange4D
open P0EFTJanusProgramPActualThroatGaugeThirdOrderJetBundleCoordChangeContinuity4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev GaugeThirdJet :=
  FramedThirdOrderJet ThroatCoverCoordinates
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

/-- Topological vector-bundle gluing data for actual throat gauge third jets. -/
def throatGaugeThirdOrderJetVectorBundleCore :
    VectorBundleCore Real (EffectiveThroat period hPeriod) GaugeThirdJet
      (BundleIndex period hPeriod) where
  baseSet := throatGaugeSecondOrderJetBundleBaseSet period hPeriod
  isOpen_baseSet :=
    throatGaugeSecondOrderJetBundleBaseSet_isOpen period hPeriod
  indexAt := throatGaugeSecondOrderJetBundleIndexAt period hPeriod
  mem_baseSet_at :=
    mem_throatGaugeSecondOrderJetBundleBaseSet_indexAt period hPeriod
  coordChange :=
    throatGaugeThirdOrderJetBundleContinuousCoordChange period hPeriod
  coordChange_self index current hCurrent jet := by
    rw [throatGaugeThirdOrderJetBundleContinuousCoordChange_self period hPeriod
      index current hCurrent]
    rfl
  continuousOn_coordChange :=
    throatGaugeThirdOrderJetBundleContinuousCoordChange_continuousOn
      period hPeriod
  coordChange_comp first middle last current hCurrent jet := by
    have hComp :=
      throatGaugeThirdOrderJetBundleContinuousCoordChange_comp period hPeriod
        first middle last current hCurrent
    exact congrArg (fun change : GaugeThirdJet →L[Real] GaugeThirdJet ↦ change jet) hComp

@[simp]
theorem throatGaugeThirdOrderJetVectorBundleCore_baseSet
    (index : BundleIndex period hPeriod) :
    (throatGaugeThirdOrderJetVectorBundleCore period hPeriod).baseSet index =
      throatGaugeSecondOrderJetBundleBaseSet period hPeriod index :=
  rfl

@[simp]
theorem throatGaugeThirdOrderJetVectorBundleCore_coordChange
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod) :
    (throatGaugeThirdOrderJetVectorBundleCore period hPeriod).coordChange
        first second current =
      throatGaugeThirdOrderJetBundleContinuousCoordChange period hPeriod
        first second current :=
  rfl

end
end P0EFTJanusProgramPActualThroatGaugeThirdOrderJetVectorBundleCore4D
end JanusFormal
