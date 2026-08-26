import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCSecondOrderJetBundleCoordChange4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFrameChartPairSecondJetVectorBundleCore4D

/-!
# Vector-bundle core for actual throat SpinC second jets

The SpinC trivialization/chart atlas and its continuous semidirect coordinate
changes assemble into a topological `VectorBundleCore` through the generic
frame/chart-pair constructor.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatSpinCSecondOrderJetVectorBundleCore4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderJetBundleAtlasData4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderJetBundleCoordChange4D
open P0EFTJanusProgramPFrameChartPairSecondJetVectorBundleCore4D

variable (period : Real) (hPeriod : period ≠ 0)
variable (choice : NormalRootChoice)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev SpinCJet :=
  FramedSecondOrderJet ThroatCoverCoordinates D9DoubledMatterFiber

private abbrev BundleIndex :=
  ThroatSpinCSecondOrderJetBundleIndex period hPeriod

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- Topological vector-bundle gluing data for actual throat SpinC second
jets. -/
def throatSpinCSecondOrderJetVectorBundleCore :
    VectorBundleCore Real (EffectiveThroat period hPeriod) SpinCJet
      (BundleIndex period hPeriod) :=
  frameChartPairSecondJetVectorBundleCore
    (throatSpinCSecondOrderJetBundleBaseSet period hPeriod)
    (throatSpinCSecondOrderJetBundleBaseSet_isOpen period hPeriod)
    (throatSpinCSecondOrderJetBundleIndexAt period hPeriod)
    (mem_throatSpinCSecondOrderJetBundleBaseSet_indexAt period hPeriod)
    (throatSpinCSecondOrderJetBundleCoordChange period hPeriod choice)
    (throatSpinCSecondOrderJetBundleCoordChange_self period hPeriod choice)
    (throatSpinCSecondOrderJetBundleCoordChange_continuousOn
      period hPeriod choice)
    (throatSpinCSecondOrderJetBundleCoordChange_comp period hPeriod choice)

@[simp]
theorem throatSpinCSecondOrderJetVectorBundleCore_baseSet
    (index : BundleIndex period hPeriod) :
    (throatSpinCSecondOrderJetVectorBundleCore period hPeriod choice).baseSet
        index =
      throatSpinCSecondOrderJetBundleBaseSet period hPeriod index :=
  rfl

@[simp]
theorem throatSpinCSecondOrderJetVectorBundleCore_coordChange
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod) :
    (throatSpinCSecondOrderJetVectorBundleCore period hPeriod choice).coordChange
        first second current =
      throatSpinCSecondOrderJetBundleCoordChange period hPeriod choice
        first second current :=
  rfl

end
end P0EFTJanusProgramPActualThroatSpinCSecondOrderJetVectorBundleCore4D
end JanusFormal
