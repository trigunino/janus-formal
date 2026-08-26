import Mathlib.Geometry.Manifold.VectorBundle.Basic
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeSecondOrderJetVectorBundleCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeSecondOrderJetBundleCoordChangeSmoothness4D

/-!
# Smooth vector-bundle core for actual throat gauge second jets

The smooth overlap theorem upgrades the installed topological vector-bundle
core to a `C∞` vector bundle.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatGaugeSecondOrderJetSmoothVectorBundleCore4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetBundleCoordChangeSmoothness4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetVectorBundleCore4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev GaugeJet :=
  FramedSecondOrderJet ThroatCoverCoordinates
    (FramedCovector ThroatCoverCoordinates)

/-- The associated fiber family of the second-jet vector-bundle core. -/
abbrev ThroatGaugeSecondOrderJetBundleFiber :=
  (throatGaugeSecondOrderJetVectorBundleCore period hPeriod).Fiber

/-- The second-jet vector-bundle core has smooth coordinate changes. -/
theorem throatGaugeSecondOrderJetVectorBundleCore_isContMDiff :
    letI : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
      P0EFTJanusProgramPActualThroatGaugeSecondOrderJetBundleCoordChangeSmoothness4D.effectiveThroatChartedSpace
        period hPeriod
    (throatGaugeSecondOrderJetVectorBundleCore period hPeriod).IsContMDiff
      throatCoverModelWithCorners ∞ := by
  letI : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
    P0EFTJanusProgramPActualThroatGaugeSecondOrderJetBundleCoordChangeSmoothness4D.effectiveThroatChartedSpace
      period hPeriod
  constructor
  intro first second
  convert
    throatGaugeSecondOrderJetBundleCoordChange_contMDiffOn
      period hPeriod first second using 1 <;> rfl

/-- The fiber family constructed from the core is a smooth vector bundle. -/
theorem throatGaugeSecondOrderJetBundleFiber_isContMDiffVectorBundle :
    letI : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
      P0EFTJanusProgramPActualThroatGaugeSecondOrderJetBundleCoordChangeSmoothness4D.effectiveThroatChartedSpace
        period hPeriod
    letI :
        (throatGaugeSecondOrderJetVectorBundleCore period hPeriod).IsContMDiff
          throatCoverModelWithCorners ∞ :=
      throatGaugeSecondOrderJetVectorBundleCore_isContMDiff period hPeriod
    ContMDiffVectorBundle ∞ GaugeJet
      (ThroatGaugeSecondOrderJetBundleFiber period hPeriod)
      throatCoverModelWithCorners := by
  letI : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
    P0EFTJanusProgramPActualThroatGaugeSecondOrderJetBundleCoordChangeSmoothness4D.effectiveThroatChartedSpace
      period hPeriod
  letI :
      (throatGaugeSecondOrderJetVectorBundleCore period hPeriod).IsContMDiff
        throatCoverModelWithCorners ∞ :=
    throatGaugeSecondOrderJetVectorBundleCore_isContMDiff period hPeriod
  infer_instance

end
end P0EFTJanusProgramPActualThroatGaugeSecondOrderJetSmoothVectorBundleCore4D
end JanusFormal
