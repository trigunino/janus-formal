import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12SmoothMatrixL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CanonicalFirstOrderColumn4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12L2VolumeMultiplier4D

/-! Explicit transpose action on smooth tests for bounded finite L² coefficient matrices. -/
namespace JanusFormal.P0EFTJanusProgramPT12SmoothMatrixL2Transpose4D
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 600000
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff ENNReal
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusL2PTFunctionalSpace4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceStokes4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceWeakStokes4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceLeibniz4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance : BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusProgramPT12CanonicalFirstOrderColumn4D
open P0EFTJanusProgramPT12L2VolumeMultiplier4D
open scoped BigOperators BoundedContinuousFunction

open P0EFTJanusProgramPT12SmoothMatrixL24D

def smoothTestVector {Index : Type*} (test : Index → SmoothScalarField period hPeriod) :
    PiLp 2 fun _ : Index => CanonicalPhysicalBulkL2 period hPeriod :=
  WithLp.toLp 2 fun index => smoothToCanonicalPhysicalBulkL2 period hPeriod (test index)

variable {Input Output : Type*} [Fintype Input] [Fintype Output]

def smoothMatrixTransposeTest (matrix : Output → Input → SmoothScalarField period hPeriod)
    (test : Output → SmoothScalarField period hPeriod) : Input → SmoothScalarField period hPeriod :=
  fun column => ∑ row, canonicalScalarMul period hPeriod (matrix row column) (test row)

theorem canonicalSmoothMultiplier_test_pairing (coefficient test : SmoothScalarField period hPeriod)
    (field : CanonicalPhysicalBulkL2 period hPeriod) :
    inner Real (canonicalSmoothMultiplier period hPeriod coefficient field)
      (smoothToCanonicalPhysicalBulkL2 period hPeriod test) =
      inner Real field (smoothToCanonicalPhysicalBulkL2 period hPeriod (canonicalScalarMul period hPeriod coefficient test)) := by
  rw [← canonicalSmoothMultiplier_smooth]
  exact l2VolumeMultiplier_symmetric _ _ _ _

theorem canonicalSmoothMatrixL2_test_pairing (matrix : Output → Input → SmoothScalarField period hPeriod)
    (field : PiLp 2 fun _ : Input => CanonicalPhysicalBulkL2 period hPeriod)
    (test : Output → SmoothScalarField period hPeriod) :
    inner Real (canonicalSmoothMatrixL2 period hPeriod matrix field) (smoothTestVector period hPeriod test) =
      inner Real field (smoothTestVector period hPeriod (smoothMatrixTransposeTest period hPeriod matrix test)) := by
  simp only [PiLp.inner_apply, canonicalSmoothMatrixL2_apply, sum_inner, smoothTestVector, WithLp.ofLp_toLp,
    canonicalSmoothMultiplier_test_pairing, smoothMatrixTransposeTest, map_sum, inner_sum]
  exact Finset.sum_comm

end
end JanusFormal.P0EFTJanusProgramPT12SmoothMatrixL2Transpose4D
