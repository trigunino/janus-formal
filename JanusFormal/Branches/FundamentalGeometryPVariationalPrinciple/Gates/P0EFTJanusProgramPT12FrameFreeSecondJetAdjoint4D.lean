import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeFrameDerivativeAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRegularFrameCanonicalFormalAdjoint4D

/-! Ordered second-jet adjoints for finite smooth generators, with no regular-frame witness. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeSecondJetAdjoint4D
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceStokes4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceLeibniz4D
open P0EFTJanusProgramPT12CanonicalFrameDerivativeAdjoint4D
open P0EFTJanusProgramPT12CanonicalFirstOrderColumn4D
open P0EFTJanusProgramPT12FrameFreeDivergenceStokes4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev Q := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (Q period hPeriod) := reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (Q period hPeriod) := reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (Q period hPeriod) := reflectedSphereQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (Q period hPeriod) := borel _
local instance : BorelSpace (Q period hPeriod) where measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
local notation "Scalar" => SmoothQuotientField period hPeriod Real
local notation "μ" => intrinsicCanonicalLorentzVolumeMeasure period hPeriod
variable (metric : SmoothGeneralLorentzMetric period hPeriod)
variable (frame : SmoothD8Frame period hPeriod)

open P0EFTJanusRegularFrameCanonicalFormalAdjoint4D
open P0EFTJanusProgramPT12FrameFreeFrameDerivativeAdjoint4D
local notation "N" => Fin frame.count
local notation "inc" => smoothToCanonicalPhysicalBulkL2 period hPeriod
local notation "deriv" => canonicalFrameDerivativeSmooth period hPeriod frame
local notation "adj" => frameFreeFrameDerivativeAdjoint period hPeriod metric frame
local notation "mul" => canonicalScalarMul period hPeriod
local notation "integral" => canonicalSmoothScalarIntegral period hPeriod

private theorem integral_mul (coefficient test : Scalar) :
    integral (mul coefficient test) = inner Real (inc coefficient) (inc test) :=
  (canonicalScalarL2_inner period hPeriod coefficient test).symm

private theorem adjoint_pairing (direction : N) (coefficient test : Scalar) :
    inner Real (inc (adj direction coefficient)) (inc test) =
      inner Real (inc coefficient) (inc (deriv direction test)) :=
  (real_inner_comm _ _).trans
    ((frameFreeFrameDerivativeAdjoint_pairing period hPeriod metric frame direction test coefficient).symm.trans
      (real_inner_comm _ _))

/-- The adjoints are composed in reverse order; the frame derivatives need not commute. -/
theorem frameFreeSecondDerivativeAdjoint_pairing (outer innerIndex : N) (coefficient test : Scalar) :
    inner Real (inc (adj innerIndex (adj outer coefficient))) (inc test) =
      inner Real (inc coefficient) (inc (deriv outer (deriv innerIndex test))) :=
  (adjoint_pairing period hPeriod metric frame innerIndex (adj outer coefficient) test).trans
    (adjoint_pairing period hPeriod metric frame outer coefficient (deriv innerIndex test))

def frameFreeSecondJetDensity (value : Scalar) (first : N → Scalar)
    (second : N → N → Scalar) (test : Scalar) : Scalar :=
  mul value test + (∑ direction, mul (first direction) (deriv direction test)) +
    ∑ outer, ∑ innerIndex, mul (second outer innerIndex) (deriv outer (deriv innerIndex test))

def frameFreeSecondJetAdjoint (value : Scalar) (first : N → Scalar) (second : N → N → Scalar) : Scalar :=
  value + (∑ direction, adj direction (first direction)) +
    ∑ outer, ∑ innerIndex, adj innerIndex (adj outer (second outer innerIndex))

theorem frameFreeSecondJetAdjoint_pairing (value : Scalar) (first : N → Scalar)
    (second : N → N → Scalar) (test : Scalar) :
    inner Real (inc (frameFreeSecondJetAdjoint period hPeriod metric frame value first second)) (inc test) =
      integral (frameFreeSecondJetDensity period hPeriod frame value first second test) := by
  simp only [frameFreeSecondJetAdjoint, frameFreeSecondJetDensity,
    map_add, map_sum, inner_add_left, sum_inner, integral_mul]
  simp_rw [adjoint_pairing]

theorem frameFreeSecondJetAdjoint_integral (value : Scalar) (first : N → Scalar)
    (second : N → N → Scalar) (test : Scalar) :
    integral (frameFreeSecondJetDensity period hPeriod frame value first second test) =
      integral (mul (frameFreeSecondJetAdjoint period hPeriod metric frame value first second) test) :=
  (frameFreeSecondJetAdjoint_pairing period hPeriod metric frame value first second test).symm.trans
    (integral_mul period hPeriod _ test).symm

theorem frameFreeSecondJetFunctional_bound (value : Scalar) (first : N → Scalar)
    (second : N → N → Scalar) (test : Scalar) :
    ‖integral (frameFreeSecondJetDensity period hPeriod frame value first second test)‖ ≤
      ‖inc (frameFreeSecondJetAdjoint period hPeriod metric frame value first second)‖ * ‖inc test‖ := by
  rw [← frameFreeSecondJetAdjoint_pairing period hPeriod metric frame value first second test]
  exact norm_inner_le_norm _ _

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeSecondJetAdjoint4D
