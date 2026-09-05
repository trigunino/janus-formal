import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalTenFlowDivergenceWeakStokes4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCanonicalFullSupport4D

/-!
# Divergence of the canonical volume-preserving generators

The ten canonical flow generators are packaged as genuine smooth tangent
fields.  Flow integration by parts and full support then identify their weak
canonical divergence pointwise: it vanishes.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalTenFlowGeneratorDivergence4D

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalTenFlowFrame4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceStokes4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceWeakStokes4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCanonicalFullSupport4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance intrinsicCanonicalLorentzVolumeMeasureIsFinite :
    IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

local instance intrinsicCanonicalLorentzVolumeMeasureIsOpenPos :
    Measure.IsOpenPosMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isOpenPosMeasure period hPeriod

/-- One canonical flow generator, packaged as a smooth tangent field. -/
def canonicalTenFlowVectorField (index : Fin 10) :
    SmoothTangentField period hPeriod where
  toFun := fun point =>
    (canonicalTenFlowFrame period hPeriod).vectorAt point index
  contMDiff_toFun :=
    (canonicalTenFlowFrame period hPeriod).contMDiff_vector index

@[simp]
theorem canonicalTenFlowVectorField_apply
    (index : Fin 10) (point : EffectiveQuotient period hPeriod) :
    canonicalTenFlowVectorField period hPeriod index point =
      (canonicalTenFlowFrame period hPeriod).vectorAt point index :=
  rfl

/-- Full support separates a smooth scalar from all smooth weak tests. -/
theorem canonicalSmoothScalar_eq_zero_of_weak_pairings
    (residual : SmoothQuotientField period hPeriod Real)
    (hPairing : ∀ test : SmoothQuotientField period hPeriod Real,
      (∫ point, test point * residual point
        ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) = 0) :
    residual = 0 := by
  let measure := intrinsicCanonicalLorentzVolumeMeasure period hPeriod
  have hSquareIntegrable :
      Integrable (fun point => residual point * residual point) measure :=
    (residual.contMDiff_toFun.continuous.mul
      residual.contMDiff_toFun.continuous
      ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hSquareZero :
      (fun point => residual point * residual point) =ᵐ[measure] 0 :=
    (integral_eq_zero_iff_of_nonneg
      (fun point => mul_self_nonneg (residual point)) hSquareIntegrable).mp
        (hPairing residual)
  have hResidualZero : residual.toFun =ᵐ[measure]
      (fun _ : EffectiveQuotient period hPeriod => (0 : Real)) := by
    filter_upwards [hSquareZero] with point hPoint
    exact mul_self_eq_zero.mp hPoint
  have hResidualFunctionZero : residual.toFun =
      (fun _ : EffectiveQuotient period hPeriod => (0 : Real)) :=
    (Continuous.ae_eq_iff_eq measure residual.contMDiff_toFun.continuous
      continuous_const).mp hResidualZero
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  exact congrFun hResidualFunctionZero point

/-- The directional derivative of every smooth test along a canonical
generator has zero canonical-volume integral. -/
theorem canonicalTenFlowVectorField_testDerivative_integral_eq_zero
    (index : Fin 10)
    (test : SmoothQuotientField period hPeriod Real) :
    (∫ point,
      mvfderiv coverModelWithCorners test.toFun point
        (canonicalTenFlowVectorField period hPeriod index point)
      ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) = 0 := by
  have hIPP := canonicalTenFlowFrame_integral_inner_derivative_eq_neg
    period hPeriod index
      (constantSmoothField period hPeriod Real 1) test
  simpa [canonicalTenFlowVectorField, frameDerivative_eq_mfderiv,
    constantSmoothField, mvfderiv_const] using hIPP

/-- Every canonical volume-preserving generator has zero pointwise weak
divergence, for every regular metric used to present the redundant dual. -/
theorem canonicalTenFlowDivergence_vectorField_eq_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (index : Fin 10) :
    canonicalTenFlowDivergence period hPeriod metric
        (canonicalTenFlowVectorField period hPeriod index) = 0 := by
  apply canonicalSmoothScalar_eq_zero_of_weak_pairings period hPeriod
  intro test
  rw [canonicalTenFlowDivergence_weak_stokes period hPeriod metric]
  rw [canonicalTenFlowVectorField_testDerivative_integral_eq_zero
    period hPeriod index test]
  simp

/-- Gate marker: all ten concrete canonical generators are divergence-free as
smooth fields, not merely after integrating their divergence. -/
theorem canonical_ten_flow_generator_divergence_gate
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    ∀ index : Fin 10,
      canonicalTenFlowDivergence period hPeriod metric
          (canonicalTenFlowVectorField period hPeriod index) = 0 :=
  canonicalTenFlowDivergence_vectorField_eq_zero period hPeriod metric

end
end P0EFTJanusMappingTorusCanonicalTenFlowGeneratorDivergence4D
end JanusFormal
