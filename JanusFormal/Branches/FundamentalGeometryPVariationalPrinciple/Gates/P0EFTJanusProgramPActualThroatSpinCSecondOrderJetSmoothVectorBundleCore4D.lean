import Mathlib.Geometry.Manifold.VectorBundle.Basic
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCSecondOrderJetVectorBundleCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCSecondOrderJetBundleCoordChangeSmoothness4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFrameChartPairSecondJetVectorBundleCore4D

/-!
# Smooth vector-bundle core for actual throat SpinC second jets

The smooth overlap theorem upgrades the SpinC second-jet core to a `C∞`
vector bundle.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatSpinCSecondOrderJetSmoothVectorBundleCore4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderJetBundleAtlasData4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderJetBundleCoordChange4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderJetBundleCoordChangeSmoothness4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderJetVectorBundleCore4D
open P0EFTJanusProgramPFrameChartPairSecondJetVectorBundleCore4D

variable (period : Real) (hPeriod : period ≠ 0)
variable (choice : NormalRootChoice)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev SpinCJet :=
  FramedSecondOrderJet ThroatCoverCoordinates D9DoubledMatterFiber

/-- The associated fiber family of the SpinC second-jet core. -/
abbrev ThroatSpinCSecondOrderJetBundleFiber :=
  (throatSpinCSecondOrderJetVectorBundleCore period hPeriod choice).Fiber

/-- The SpinC second-jet vector-bundle core has smooth coordinate changes. -/
theorem throatSpinCSecondOrderJetVectorBundleCore_isContMDiff :
    letI : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
      fixedThroatQuotientChartedSpace period hPeriod
    (throatSpinCSecondOrderJetVectorBundleCore period hPeriod choice).IsContMDiff
      throatCoverModelWithCorners ∞ := by
  letI : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
    fixedThroatQuotientChartedSpace period hPeriod
  simpa only [throatSpinCSecondOrderJetVectorBundleCore] using
    (frameChartPairSecondJetVectorBundleCore_isContMDiff
      throatCoverModelWithCorners ∞
      (throatSpinCSecondOrderJetBundleBaseSet period hPeriod)
      (throatSpinCSecondOrderJetBundleBaseSet_isOpen period hPeriod)
      (throatSpinCSecondOrderJetBundleIndexAt period hPeriod)
      (mem_throatSpinCSecondOrderJetBundleBaseSet_indexAt period hPeriod)
      (throatSpinCSecondOrderJetBundleCoordChange period hPeriod choice)
      (throatSpinCSecondOrderJetBundleCoordChange_self period hPeriod choice)
      (throatSpinCSecondOrderJetBundleCoordChange_continuousOn
        period hPeriod choice)
      (throatSpinCSecondOrderJetBundleCoordChange_comp period hPeriod choice)
      (throatSpinCSecondOrderJetBundleCoordChange_contMDiffOn
        period hPeriod choice))

/-- The SpinC second-jet fiber family is a smooth vector bundle. -/
theorem throatSpinCSecondOrderJetBundleFiber_isContMDiffVectorBundle :
    letI : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
      fixedThroatQuotientChartedSpace period hPeriod
    letI :
        (throatSpinCSecondOrderJetVectorBundleCore period hPeriod choice).IsContMDiff
          throatCoverModelWithCorners ∞ :=
      throatSpinCSecondOrderJetVectorBundleCore_isContMDiff
        period hPeriod choice
    ContMDiffVectorBundle ∞ SpinCJet
      (ThroatSpinCSecondOrderJetBundleFiber period hPeriod choice)
      throatCoverModelWithCorners := by
  letI : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
    fixedThroatQuotientChartedSpace period hPeriod
  letI :
      (throatSpinCSecondOrderJetVectorBundleCore period hPeriod choice).IsContMDiff
        throatCoverModelWithCorners ∞ :=
    throatSpinCSecondOrderJetVectorBundleCore_isContMDiff period hPeriod choice
  infer_instance

end
end P0EFTJanusProgramPActualThroatSpinCSecondOrderJetSmoothVectorBundleCore4D
end JanusFormal
