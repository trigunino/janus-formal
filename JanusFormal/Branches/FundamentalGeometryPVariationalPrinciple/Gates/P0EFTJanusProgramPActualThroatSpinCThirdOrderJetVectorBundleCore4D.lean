import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCThirdOrderJetBundleCoordChangeContinuity4D

/-!
# Vector-bundle core for actual throat SpinC third jets

The SpinC trivialization/chart atlas and its continuous third-order coordinate
changes assemble into a topological `VectorBundleCore`.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatSpinCThirdOrderJetVectorBundleCore4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPFramedThirdOrderJetConstantFiberBaseChange4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderJetBundleAtlasData4D
open P0EFTJanusProgramPActualThroatSpinCThirdOrderJetContinuousLinearCoordChange4D
open P0EFTJanusProgramPActualThroatSpinCThirdOrderJetBundleCoordChangeContinuity4D

variable (period : Real) (hPeriod : period ≠ 0)
variable (choice : NormalRootChoice)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev SpinCThirdJet :=
  FramedThirdOrderJet ThroatCoverCoordinates D9DoubledMatterFiber

private abbrev BundleIndex :=
  ThroatSpinCSecondOrderJetBundleIndex period hPeriod

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- Topological vector-bundle gluing data for actual throat SpinC third
jets. -/
def throatSpinCThirdOrderJetVectorBundleCore :
    VectorBundleCore Real (EffectiveThroat period hPeriod) SpinCThirdJet
      (BundleIndex period hPeriod) where
  baseSet := throatSpinCSecondOrderJetBundleBaseSet period hPeriod
  isOpen_baseSet :=
    throatSpinCSecondOrderJetBundleBaseSet_isOpen period hPeriod
  indexAt := throatSpinCSecondOrderJetBundleIndexAt period hPeriod
  mem_baseSet_at :=
    mem_throatSpinCSecondOrderJetBundleBaseSet_indexAt period hPeriod
  coordChange :=
    throatSpinCThirdOrderJetBundleContinuousCoordChange period hPeriod choice
  coordChange_self index current hCurrent jet := by
    rw [throatSpinCThirdOrderJetBundleContinuousCoordChange_self
      period hPeriod choice index current hCurrent]
    rfl
  continuousOn_coordChange :=
    throatSpinCThirdOrderJetBundleContinuousCoordChange_continuousOn
      period hPeriod choice
  coordChange_comp first middle last current hCurrent jet := by
    have hComp :=
      throatSpinCThirdOrderJetBundleContinuousCoordChange_comp period hPeriod
        choice first middle last current hCurrent
    exact congrArg
      (fun change : SpinCThirdJet →L[Real] SpinCThirdJet ↦ change jet) hComp

@[simp]
theorem throatSpinCThirdOrderJetVectorBundleCore_baseSet
    (index : BundleIndex period hPeriod) :
    (throatSpinCThirdOrderJetVectorBundleCore period hPeriod choice).baseSet
        index =
      throatSpinCSecondOrderJetBundleBaseSet period hPeriod index :=
  rfl

@[simp]
theorem throatSpinCThirdOrderJetVectorBundleCore_coordChange
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod) :
    (throatSpinCThirdOrderJetVectorBundleCore period hPeriod choice).coordChange
        first second current =
      throatSpinCThirdOrderJetBundleContinuousCoordChange period hPeriod choice
        first second current :=
  rfl

end
end P0EFTJanusProgramPActualThroatSpinCThirdOrderJetVectorBundleCore4D
end JanusFormal
