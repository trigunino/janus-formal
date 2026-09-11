import Mathlib.Geometry.Manifold.VectorBundle.Basic
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeThirdOrderJetVectorBundleCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeThirdOrderJetBundleCoordChangeSmoothness4D

/-!
# Smooth vector-bundle core for actual throat gauge third jets

The smooth overlap theorem upgrades the installed topological vector-bundle
core to a `C∞` vector bundle.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatGaugeThirdOrderJetSmoothVectorBundleCore4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPFramedThirdOrderJetConstantFiberBaseChange4D
open P0EFTJanusProgramPActualThroatGaugeThirdOrderJetBundleCoordChangeSmoothness4D
open P0EFTJanusProgramPActualThroatGaugeThirdOrderJetVectorBundleCore4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev GaugeThirdJet :=
  FramedThirdOrderJet ThroatCoverCoordinates
    (FramedCovector ThroatCoverCoordinates)

/-- The associated fiber family of the third-jet vector-bundle core. -/
abbrev ThroatGaugeThirdOrderJetBundleFiber :=
  (throatGaugeThirdOrderJetVectorBundleCore period hPeriod).Fiber

/-- The third-jet vector-bundle core has smooth coordinate changes. -/
theorem throatGaugeThirdOrderJetVectorBundleCore_isContMDiff :
    letI : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
      P0EFTJanusProgramPActualThroatGaugeThirdOrderJetBundleCoordChangeSmoothness4D.effectiveThroatChartedSpace
        period hPeriod
    (throatGaugeThirdOrderJetVectorBundleCore period hPeriod).IsContMDiff
      throatCoverModelWithCorners ∞ := by
  letI : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
    P0EFTJanusProgramPActualThroatGaugeThirdOrderJetBundleCoordChangeSmoothness4D.effectiveThroatChartedSpace
      period hPeriod
  constructor
  intro first second
  convert
    throatGaugeThirdOrderJetBundleContinuousCoordChange_contMDiffOn
      period hPeriod first second using 1 <;> rfl

/-- The fiber family constructed from the core is a smooth vector bundle. -/
theorem throatGaugeThirdOrderJetBundleFiber_isContMDiffVectorBundle :
    letI : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
      P0EFTJanusProgramPActualThroatGaugeThirdOrderJetBundleCoordChangeSmoothness4D.effectiveThroatChartedSpace
        period hPeriod
    letI :
        (throatGaugeThirdOrderJetVectorBundleCore period hPeriod).IsContMDiff
          throatCoverModelWithCorners ∞ :=
      throatGaugeThirdOrderJetVectorBundleCore_isContMDiff period hPeriod
    ContMDiffVectorBundle ∞ GaugeThirdJet
      (ThroatGaugeThirdOrderJetBundleFiber period hPeriod)
      throatCoverModelWithCorners := by
  letI : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
    P0EFTJanusProgramPActualThroatGaugeThirdOrderJetBundleCoordChangeSmoothness4D.effectiveThroatChartedSpace
      period hPeriod
  letI :
      (throatGaugeThirdOrderJetVectorBundleCore period hPeriod).IsContMDiff
        throatCoverModelWithCorners ∞ :=
    throatGaugeThirdOrderJetVectorBundleCore_isContMDiff period hPeriod
  infer_instance

end
end P0EFTJanusProgramPActualThroatGaugeThirdOrderJetSmoothVectorBundleCore4D
end JanusFormal
