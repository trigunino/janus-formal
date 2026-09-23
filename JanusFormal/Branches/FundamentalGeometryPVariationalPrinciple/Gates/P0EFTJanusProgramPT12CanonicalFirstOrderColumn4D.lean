import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CanonicalFrameDerivativeAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D

/-! Weighted first-order columns and their concrete canonical-volume adjoints. -/
namespace JanusFormal.P0EFTJanusProgramPT12CanonicalFirstOrderColumn4D
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

open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusProgramPT12CanonicalFrameDerivativeAdjoint4D
open scoped BigOperators

def canonicalScalarMul (coefficient : SmoothQuotientField period hPeriod Real) :
    SmoothQuotientField period hPeriod Real →ₗ[Real] SmoothQuotientField period hPeriod Real where
  toFun := smoothScalarFieldMul period hPeriod coefficient
  map_add' first second := by
    apply SmoothQuotientField.ext period hPeriod Real
    intro point
    change coefficient point * (first point + second point) = _
    exact mul_add _ _ _
  map_smul' scalar field := by
    apply SmoothQuotientField.ext period hPeriod Real
    intro point
    change coefficient point * (scalar * field point) = scalar * (coefficient point * field point)
    ring

theorem canonicalScalarMul_pairing
    (coefficient field test : SmoothQuotientField period hPeriod Real) :
    inner Real (smoothToCanonicalPhysicalBulkL2 period hPeriod
      (canonicalScalarMul period hPeriod coefficient field))
      (smoothToCanonicalPhysicalBulkL2 period hPeriod test) =
    inner Real (smoothToCanonicalPhysicalBulkL2 period hPeriod field)
      (smoothToCanonicalPhysicalBulkL2 period hPeriod (canonicalScalarMul period hPeriod coefficient test)) := by
  rw [canonicalScalarL2_inner, canonicalScalarL2_inner]
  apply integral_congr_ae
  filter_upwards [] with point
  change (coefficient point * field point) * test point = field point * (coefficient point * test point)
  ring

/-- One Cartan column: a zeroth-order term and two weighted frame derivatives. -/
def canonicalFirstOrderColumn
    (frame : SmoothD8Frame period hPeriod) (first second : Fin frame.count)
    (zeroth firstWeight secondWeight : SmoothQuotientField period hPeriod Real) :
    SmoothQuotientField period hPeriod Real →ₗ[Real] SmoothQuotientField period hPeriod Real :=
  canonicalScalarMul period hPeriod zeroth +
    (canonicalScalarMul period hPeriod firstWeight).comp
      (canonicalFrameDerivativeSmooth period hPeriod frame first) +
    (canonicalScalarMul period hPeriod secondWeight).comp
      (canonicalFrameDerivativeSmooth period hPeriod frame second)

def canonicalFirstOrderColumnAdjoint
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (frame : SmoothD8Frame period hPeriod) (first second : Fin frame.count)
    (zeroth firstWeight secondWeight test : SmoothQuotientField period hPeriod Real) :
    SmoothQuotientField period hPeriod Real :=
  canonicalScalarMul period hPeriod zeroth test +
    canonicalFrameDerivativeAdjoint period hPeriod metric frame first
      (canonicalScalarMul period hPeriod firstWeight test) +
    canonicalFrameDerivativeAdjoint period hPeriod metric frame second
      (canonicalScalarMul period hPeriod secondWeight test)

theorem canonicalFirstOrderColumn_pairing
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (frame : SmoothD8Frame period hPeriod) (first second : Fin frame.count)
    (zeroth firstWeight secondWeight field test : SmoothQuotientField period hPeriod Real) :
    inner Real (smoothToCanonicalPhysicalBulkL2 period hPeriod
      (canonicalFirstOrderColumn period hPeriod frame first second zeroth firstWeight secondWeight field))
      (smoothToCanonicalPhysicalBulkL2 period hPeriod test) =
    inner Real (smoothToCanonicalPhysicalBulkL2 period hPeriod field)
      (smoothToCanonicalPhysicalBulkL2 period hPeriod
        (canonicalFirstOrderColumnAdjoint period hPeriod metric frame first second
          zeroth firstWeight secondWeight test)) := by
  simp only [canonicalFirstOrderColumn, canonicalFirstOrderColumnAdjoint,
    LinearMap.add_apply, LinearMap.comp_apply, map_add, inner_add_left, inner_add_right]
  apply congrArg₂ (· + ·)
  · apply congrArg₂ (· + ·)
    · exact canonicalScalarMul_pairing period hPeriod zeroth field test
    · exact (canonicalScalarMul_pairing period hPeriod firstWeight
        (canonicalFrameDerivativeSmooth period hPeriod frame first field) test).trans
        (canonicalFrameDerivativeAdjoint_pairing period hPeriod metric frame first field
          (canonicalScalarMul period hPeriod firstWeight test))
  · exact (canonicalScalarMul_pairing period hPeriod secondWeight
      (canonicalFrameDerivativeSmooth period hPeriod frame second field) test).trans
      (canonicalFrameDerivativeAdjoint_pairing period hPeriod metric frame second field
        (canonicalScalarMul period hPeriod secondWeight test))

theorem canonicalScalar_sum_apply {Index : Type*} [Fintype Index]
    (fields : Index → SmoothQuotientField period hPeriod Real) (point : EffectiveQuotient period hPeriod) :
    (∑ index, fields index) point = ∑ index, fields index point := by
  let evaluation : SmoothQuotientField period hPeriod Real →ₗ[Real] Real :=
    { toFun := fun field => field point
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  exact map_sum evaluation fields Finset.univ

end
end JanusFormal.P0EFTJanusProgramPT12CanonicalFirstOrderColumn4D
