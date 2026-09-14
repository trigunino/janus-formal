import Mathlib.Geometry.Manifold.VectorBundle.Basic
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCThirdOrderJetVectorBundleCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCThirdOrderJetBundleCoordChangeSmoothness4D

/-!
# Smooth vector-bundle core for actual throat SpinC third jets

The smooth overlap theorem upgrades the SpinC third-jet topological core to
a `C∞` vector bundle.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatSpinCThirdOrderJetSmoothVectorBundleCore4D

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
open P0EFTJanusProgramPActualThroatSpinCThirdOrderJetBundleCoordChangeSmoothness4D
open P0EFTJanusProgramPActualThroatSpinCThirdOrderJetVectorBundleCore4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable (period : Real) (hPeriod : period ≠ 0)
variable (choice : NormalRootChoice)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev SpinCThirdJet :=
  FramedThirdOrderJet ThroatCoverCoordinates D9DoubledMatterFiber

/-- The associated fiber family of the SpinC third-jet vector-bundle core. -/
abbrev ThroatSpinCThirdOrderJetBundleFiber :=
  (throatSpinCThirdOrderJetVectorBundleCore period hPeriod choice).Fiber

/-- The SpinC third-jet vector-bundle core has smooth coordinate changes. -/
theorem throatSpinCThirdOrderJetVectorBundleCore_isContMDiff :
    letI : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
      P0EFTJanusProgramPActualThroatSpinCThirdOrderJetBundleCoordChangeSmoothness4D.effectiveThroatChartedSpace
        period hPeriod
    (throatSpinCThirdOrderJetVectorBundleCore period hPeriod choice).IsContMDiff
      throatCoverModelWithCorners ∞ := by
  letI : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
    P0EFTJanusProgramPActualThroatSpinCThirdOrderJetBundleCoordChangeSmoothness4D.effectiveThroatChartedSpace
      period hPeriod
  constructor
  intro first second
  convert
    throatSpinCThirdOrderJetBundleContinuousCoordChange_contMDiffOn
      period hPeriod choice first second using 1 <;> rfl

/-- The SpinC third-jet fiber family is a smooth vector bundle. -/
theorem throatSpinCThirdOrderJetBundleFiber_isContMDiffVectorBundle :
    letI : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
      P0EFTJanusProgramPActualThroatSpinCThirdOrderJetBundleCoordChangeSmoothness4D.effectiveThroatChartedSpace
        period hPeriod
    letI :
        (throatSpinCThirdOrderJetVectorBundleCore period hPeriod choice).IsContMDiff
          throatCoverModelWithCorners ∞ :=
      throatSpinCThirdOrderJetVectorBundleCore_isContMDiff period hPeriod choice
    ContMDiffVectorBundle ∞ SpinCThirdJet
      (ThroatSpinCThirdOrderJetBundleFiber period hPeriod choice)
      throatCoverModelWithCorners := by
  letI : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
    P0EFTJanusProgramPActualThroatSpinCThirdOrderJetBundleCoordChangeSmoothness4D.effectiveThroatChartedSpace
      period hPeriod
  letI :
      (throatSpinCThirdOrderJetVectorBundleCore period hPeriod choice).IsContMDiff
        throatCoverModelWithCorners ∞ :=
    throatSpinCThirdOrderJetVectorBundleCore_isContMDiff period hPeriod choice
  infer_instance

end
end P0EFTJanusProgramPActualThroatSpinCThirdOrderJetSmoothVectorBundleCore4D
end JanusFormal
