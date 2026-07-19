import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullLLHessianExplicitPolarization4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIntegratedPTFullLLTaylorCoefficient12Bridge4D

/-! The mixed full LL Hessian reconstructed from the C2 coefficients of the
two genuine global action curves in the sum and difference directions. -/

namespace JanusFormal
namespace P0EFTJanusFullLLMixedHessianTaylorPolarization4D

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff Topology
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusFullMatterRobinLLDirections4D
open P0EFTJanusIntegratedPTFullLLHessianAssembly4D
open P0EFTJanusFullLLVariationalAPI4D
open P0EFTJanusFullLLHessianExplicitAdditivity4D
open P0EFTJanusFullLLHessianExplicitPolarization4D
open P0EFTJanusGlobalPTDifferentialLLFullCurveTaylorReconstruction4D
open P0EFTJanusIntegratedPTFullLLTaylorCoefficient12Bridge4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

/-- Exact mixed Hessian from the quadratic coefficients of the same global
PT action along the true `x+y` and `x-y` full LL curves. -/
theorem fullLLHessian_eq_difference_integrated_C2
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (x y : FullMatterRobinLLDirections period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    fullLLHessian period hPeriod frame fields x y mu =
      (1 / 2 : Real) *
        ((∫ p, ptTaylorCoeff period hPeriod 2 frame fields
          (addDirection period hPeriod x y).llAuxMetric
          (fullDirectionLLVariation period hPeriod (addDirection period hPeriod x y)) p ∂mu) -
        (∫ p, ptTaylorCoeff period hPeriod 2 frame fields
          (subDirection period hPeriod x y).llAuxMetric
          (fullDirectionLLVariation period hPeriod (subDirection period hPeriod x y)) p ∂mu)) := by
  have hpol := fullLLHessian_polarization period hPeriod frame fields x y mu
  have hplus := integral_coefficient_two_eq_half_fullLLHessian period hPeriod frame fields
    (addDirection period hPeriod x y) mu
  have hminus := integral_coefficient_two_eq_half_fullLLHessian period hPeriod frame fields
    (subDirection period hPeriod x y) mu
  linarith

end
end P0EFTJanusFullLLMixedHessianTaylorPolarization4D
end JanusFormal
