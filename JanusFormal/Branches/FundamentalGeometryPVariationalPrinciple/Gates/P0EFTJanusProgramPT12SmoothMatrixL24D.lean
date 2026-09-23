import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CanonicalFirstOrderColumn4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12L2VolumeMultiplier4D

/-! Smooth finite coefficient matrices act boundedly on canonical L². -/
namespace JanusFormal.P0EFTJanusProgramPT12SmoothMatrixL24D
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

def boundedSmoothScalar (coefficient : SmoothScalarField period hPeriod) :
    EffectiveQuotient period hPeriod →ᵇ Real :=
  BoundedContinuousFunction.mkOfCompact ⟨coefficient, coefficient.contMDiff_toFun.continuous⟩

def canonicalSmoothMultiplier (coefficient : SmoothScalarField period hPeriod) :
    CanonicalPhysicalBulkL2 period hPeriod →L[Real] CanonicalPhysicalBulkL2 period hPeriod :=
  l2VolumeMultiplier (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
    (boundedSmoothScalar period hPeriod coefficient)

theorem canonicalSmoothMultiplier_smooth (coefficient field : SmoothScalarField period hPeriod) :
    canonicalSmoothMultiplier period hPeriod coefficient (smoothToCanonicalPhysicalBulkL2 period hPeriod field) =
      smoothToCanonicalPhysicalBulkL2 period hPeriod (canonicalScalarMul period hPeriod coefficient field) := by
  apply Lp.ext
  filter_upwards [l2VolumeMultiplier_ae (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
      (boundedSmoothScalar period hPeriod coefficient) (smoothToCanonicalPhysicalBulkL2 period hPeriod field),
    smoothFieldToL2_ae period hPeriod Real (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) field,
    smoothFieldToL2_ae period hPeriod Real (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
      (canonicalScalarMul period hPeriod coefficient field)] with point hMul hField hProduct
  exact hMul.trans ((congrArg (fun value : Real => coefficient point * value) hField).trans hProduct.symm)

variable {Input Output : Type*} [Fintype Input]

def canonicalSmoothMatrixL2 (matrix : Output → Input → SmoothScalarField period hPeriod) :
    (PiLp 2 fun _ : Input => CanonicalPhysicalBulkL2 period hPeriod) →L[Real]
      (PiLp 2 fun _ : Output => CanonicalPhysicalBulkL2 period hPeriod) :=
  (PiLp.continuousLinearEquiv 2 Real (fun _ : Output => CanonicalPhysicalBulkL2 period hPeriod)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun row => ∑ column,
      (canonicalSmoothMultiplier period hPeriod (matrix row column)).comp
        (PiLp.proj 2 (fun _ : Input => CanonicalPhysicalBulkL2 period hPeriod) column)))

theorem canonicalSmoothMatrixL2_apply (matrix : Output → Input → SmoothScalarField period hPeriod)
    (field : PiLp 2 fun _ : Input => CanonicalPhysicalBulkL2 period hPeriod) (row : Output) :
    canonicalSmoothMatrixL2 period hPeriod matrix field row =
      ∑ column, canonicalSmoothMultiplier period hPeriod (matrix row column) (field column) := by
  simp only [canonicalSmoothMatrixL2, ContinuousLinearMap.comp_apply, ContinuousLinearMap.pi_apply,
    sum_apply, ContinuousLinearEquiv.coe_coe,
    PiLp.continuousLinearEquiv_symm_apply, PiLp.proj_apply, WithLp.ofLp_toLp]

theorem canonicalSmoothMatrixL2_smooth (matrix : Output → Input → SmoothScalarField period hPeriod)
    (field : Input → SmoothScalarField period hPeriod) (row : Output) :
    canonicalSmoothMatrixL2 period hPeriod matrix
        (WithLp.toLp 2 fun column => smoothToCanonicalPhysicalBulkL2 period hPeriod (field column)) row =
      smoothToCanonicalPhysicalBulkL2 period hPeriod
        (∑ column, canonicalScalarMul period hPeriod (matrix row column) (field column)) := by
  rw [canonicalSmoothMatrixL2_apply, map_sum]
  apply Finset.sum_congr rfl
  intro column _
  exact canonicalSmoothMultiplier_smooth period hPeriod (matrix row column) (field column)

end
end JanusFormal.P0EFTJanusProgramPT12SmoothMatrixL24D
