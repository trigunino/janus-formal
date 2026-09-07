import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMetricInducedMaxwellResidual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalTenFlowDivergenceWeakStokes4D

/-! # Canonical formal adjoints and smooth metric-coefficient reconstruction -/

namespace JanusFormal
namespace P0EFTJanusRegularFrameCanonicalFormalAdjoint4D

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 600000
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVUltralocalMaster4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularFrameMetricInverse4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellDensityPointwise4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellStressDerivative4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPRegularFrameGaugePotentialReconstruction4D
open P0EFTJanusProgramPRegularFrameMaxwellSmoothGaugeTestSeparation4D
open P0EFTJanusProgramPRegularFrameCanonicalMaxwellVariationalResidual4D
open P0EFTJanusMetricInducedSmoothGaugeVelocity4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceStokes4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceWeakStokes4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceLeibniz4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVPairingRegularity4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance : BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance

local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

/-- Canonical integration as a linear map on smooth scalars. -/
def canonicalSmoothScalarIntegral : SmoothScalarField period hPeriod →ₗ[Real] Real where
  toFun := fun field => ∫ point, field point ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod
  map_add' := by
    intro first second
    exact integral_add
      (first.contMDiff_toFun.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (second.contMDiff_toFun.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  map_smul' := by
    intro scalar field
    exact integral_const_mul scalar field.toFun

/-- Formal adjoint of a regular-frame derivative against the fixed canonical measure. -/
def regularFrameCanonicalFormalAdjoint
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (coefficient : SmoothScalarField period hPeriod) (direction : Fin 4) :
    SmoothScalarField period hPeriod :=
  -canonicalTenFlowDivergence period hPeriod metric
    (smoothScalarSMulTangentField period hPeriod coefficient (metric.frame direction))

/-- No volume gauge is required by canonical weak Stokes. -/
theorem regularFrameCanonicalFormalAdjoint_integral
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (coefficient test : SmoothScalarField period hPeriod) (direction : Fin 4) :
    (∫ point, coefficient point *
      frameDerivativeComponentField period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric) test direction point
      ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod) =
    ∫ point, regularFrameCanonicalFormalAdjoint period hPeriod metric coefficient direction point *
      test point ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  let vector := smoothScalarSMulTangentField period hPeriod coefficient (metric.frame direction)
  have hDerivative :
      (fun point => mvfderiv coverModelWithCorners test.toFun point (vector point)) =
      (fun point => coefficient point * frameDerivativeComponentField period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric) test direction point) := by
    funext point
    change mvfderiv coverModelWithCorners test.toFun point
      (coefficient point • metric.frame direction point) =
      coefficient point * frameDerivative period hPeriod Real
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric) test point direction
    rw [map_smul, frameDerivative_eq_mfderiv]
    rfl
  have hStokes := canonicalTenFlowDivergence_weak_stokes period hPeriod metric vector test
  rw [hDerivative] at hStokes
  calc
    _ = -(∫ point, test point * canonicalTenFlowDivergence period hPeriod metric vector point
        ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by linarith only [hStokes]
    _ = _ := by
      rw [← integral_neg]
      apply congrArg (fun density : EffectiveQuotient period hPeriod → Real =>
        ∫ point, density point ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
      funext point
      change -(test point * canonicalTenFlowDivergence period hPeriod metric vector point) =
        -canonicalTenFlowDivergence period hPeriod metric vector point * test point
      ring

theorem regularFrameCanonicalFormalAdjoint_smoothIntegral
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (coefficient test : SmoothScalarField period hPeriod) (direction : Fin 4) :
    canonicalSmoothScalarIntegral period hPeriod
      (smoothScalarFieldMul period hPeriod coefficient
        (frameDerivativeComponentField period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric) test direction)) =
    canonicalSmoothScalarIntegral period hPeriod
      (smoothScalarFieldMul period hPeriod
        (regularFrameCanonicalFormalAdjoint period hPeriod metric coefficient direction) test) :=
  regularFrameCanonicalFormalAdjoint_integral period hPeriod metric coefficient test direction

/-- The metric-dual frame products represent covectors on the components of `h`. -/
def regularFrameCovariantCoefficientTensor
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (coefficients : Fin 4 → Fin 4 → SmoothScalarField period hPeriod) :
    SmoothSymmetricCovariantTwoTensor period hPeriod :=
  let frame := regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric
  ∑ first : Fin 4, ∑ second : Fin 4,
    smoothBulkScalarSMulTensor period hPeriod
      (coefficients first second)
      (smoothBulkCovectorSymmetricProduct period hPeriod
        (generalMetricFrameCovector period hPeriod frame metric.metric.tensor first)
        (generalMetricFrameCovector period hPeriod frame metric.metric.tensor second))

theorem regularFrameCovariantCoefficientTensor_pairing
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (coefficients : Fin 4 → Fin 4 → SmoothScalarField period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalMetricTensorPairingAt period hPeriod metric.metric
        (regularFrameCovariantCoefficientTensor period hPeriod metric coefficients) tensor point =
      ∑ first : Fin 4, ∑ second : Fin 4,
        coefficients first second point *
          tensor.tensor point (metric.frame first point) (metric.frame second point) := by
  let frame := regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric
  rw [generalMetricTensorPairingAt_symmetric]
  let pairing : SmoothSymmetricCovariantTwoTensor period hPeriod →ₗ[Real] Real :=
    { toFun := fun value => generalMetricTensorPairingAt period hPeriod metric.metric tensor value point
      map_add' := fun first second => generalMetricTensorPairingAt_add_right period hPeriod
        metric.metric tensor first second point
      map_smul' := fun scalar value => generalMetricTensorPairingAt_smul_right period hPeriod
        metric.metric scalar tensor value point }
  change pairing (regularFrameCovariantCoefficientTensor period hPeriod metric coefficients) = _
  unfold regularFrameCovariantCoefficientTensor
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro first _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro second _
  let coefficient := coefficients first second
  let rankOne := smoothBulkCovectorSymmetricProduct period hPeriod
    (generalMetricFrameCovector period hPeriod frame metric.metric.tensor first)
    (generalMetricFrameCovector period hPeriod frame metric.metric.tensor second)
  have hCongr : pairing (smoothBulkScalarSMulTensor period hPeriod coefficient rankOne) =
      pairing ((coefficient point) • rankOne) := by
    apply generalMetricTensorPairingAt_congr_right_at
    apply ContinuousLinearMap.ext
    intro left
    apply ContinuousLinearMap.ext
    intro right
    rfl
  rw [hCongr, map_smul]
  change coefficient point * pairing rankOne = coefficient point * _
  apply congrArg (coefficient point * ·)
  exact generalMetricSymmetricFrameProduct_pairing period hPeriod frame metric.metric
    tensor point first second

end
end P0EFTJanusRegularFrameCanonicalFormalAdjoint4D
end JanusFormal
