import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFixedVolumeEinsteinHilbertWeightedPalatini4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusSmoothPalatiniCurrentLinearCoefficients4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRegularFrameCanonicalFormalAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusStoredVolumePalatiniCurrentWeight4D

/-! # Smooth stored-volume Einstein--Hilbert residual without volume gauge -/

namespace JanusFormal
namespace P0EFTJanusStoredVolumePalatiniMetricResidual4D

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

open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothMetricParameterJet4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothPalatiniCurrent4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothPalatiniDivergence4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertFixedVariableVolumeDiscrepancy4D
open P0EFTJanusFixedVolumeEinsteinHilbertWeightedPalatini4D
open P0EFTJanusSmoothPalatiniCurrentLinearCoefficients4D
open P0EFTJanusRegularFrameCanonicalFormalAdjoint4D
open P0EFTJanusStoredVolumePalatiniCurrentWeight4D

private def weightedIntegral (weight : SmoothScalarField period hPeriod) :
    SmoothScalarField period hPeriod →ₗ[Real] Real where
  toFun := fun field => canonicalSmoothScalarIntegral period hPeriod
    (smoothScalarFieldMul period hPeriod weight field)
  map_add' := by
    intro first second
    rw [← map_add]
    apply congrArg (canonicalSmoothScalarIntegral period hPeriod)
    apply SmoothQuotientField.ext period hPeriod Real
    intro point
    change weight point * (first point + second point) = _
    exact mul_add _ _ _
  map_smul' := by
    intro scalar field
    rw [← map_smul]
    apply congrArg (canonicalSmoothScalarIntegral period hPeriod)
    apply SmoothQuotientField.ext period hPeriod Real
    intro point
    change weight point * (scalar * field point) = scalar * (weight point * field point)
    ring

private theorem weightedIntegral_mul
    (weight coefficient field : SmoothScalarField period hPeriod) :
    weightedIntegral period hPeriod weight (smoothScalarFieldMul period hPeriod coefficient field) =
      canonicalSmoothScalarIntegral period hPeriod
        (smoothScalarFieldMul period hPeriod (smoothScalarFieldMul period hPeriod weight coefficient) field) := by
  apply congrArg (canonicalSmoothScalarIntegral period hPeriod)
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  exact (mul_assoc _ _ _).symm

private def metricResidualIntegral
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    SmoothSymmetricCovariantTwoTensor period hPeriod →ₗ[Real] Real where
  toFun := fun residual => ∫ point, generalMetricTensorPairingAt period hPeriod
    metric.metric residual tensor point ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod
  map_add' := by
    intro first second
    have hi (residual : SmoothSymmetricCovariantTwoTensor period hPeriod) :=
      (generalMetricTensorPairingAt_continuous period hPeriod metric.metric residual tensor
        ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
          (μ := intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
    rw [← integral_add (hi first) (hi second)]
    apply congrArg (fun density : EffectiveQuotient period hPeriod → Real =>
      ∫ point, density point ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
    funext point
    exact generalMetricTensorPairingAt_add_left period hPeriod metric.metric first second tensor point
  map_smul' := by
    intro scalar residual
    change _ = scalar * _
    rw [← integral_const_mul]
    apply congrArg (fun density : EffectiveQuotient period hPeriod → Real =>
      ∫ point, density point ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
    funext point
    exact generalMetricTensorPairingAt_smul_left period hPeriod metric.metric scalar residual tensor point

private theorem metricResidualIntegral_coefficients
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (coefficients : Fin 4 → Fin 4 → SmoothScalarField period hPeriod) :
    metricResidualIntegral period hPeriod metric tensor
      (regularFrameCovariantCoefficientTensor period hPeriod metric coefficients) =
    ∑ first : Fin 4, ∑ second : Fin 4, canonicalSmoothScalarIntegral period hPeriod
      (smoothScalarFieldMul period hPeriod (coefficients first second)
        (regularFrameSmoothCovariantVariationCoefficient period hPeriod metric tensor first second)) := by
  calc
    _ = canonicalSmoothScalarIntegral period hPeriod
        (∑ first : Fin 4, ∑ second : Fin 4, smoothScalarFieldMul period hPeriod
          (coefficients first second)
          (regularFrameSmoothCovariantVariationCoefficient period hPeriod metric tensor first second)) := by
      apply congrArg (fun density : EffectiveQuotient period hPeriod → Real =>
        ∫ point, density point ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
      funext point
      rw [regularFrameCovariantCoefficientTensor_pairing]
      simp only [smoothScalarFieldFinsetSum_apply, smoothScalarFieldMul_apply,
        regularFrameSmoothCovariantVariationCoefficient_apply]
    _ = _ := by simp only [map_sum]

/-- Formal adjoint of one actual Palatini component, represented as a smooth tensor. -/
def weightedPalatiniComponentResidual
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (weight : SmoothScalarField period hPeriod) (vector : Fin 4) :
    SmoothSymmetricCovariantTwoTensor period hPeriod :=
  regularFrameCovariantCoefficientTensor period hPeriod metric
    (fun first second => smoothScalarFieldMul period hPeriod weight
      (smoothPalatiniValueCoefficient period hPeriod metric vector first second)) +
  ∑ derivative : Fin 4, regularFrameCovariantCoefficientTensor period hPeriod metric
    (fun first second => regularFrameCanonicalFormalAdjoint period hPeriod metric
      (smoothScalarFieldMul period hPeriod weight
        (smoothPalatiniDerivativeCoefficient period hPeriod metric vector derivative first second)) derivative)

theorem weightedPalatiniComponentResidual_integral
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (weight : SmoothScalarField period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) (vector : Fin 4) :
    canonicalSmoothScalarIntegral period hPeriod
      (smoothScalarFieldMul period hPeriod weight
        (regularFrameSmoothPalatiniCoefficient period hPeriod metric tensor vector)) =
    ∫ point, generalMetricTensorPairingAt period hPeriod metric.metric
      (weightedPalatiniComponentResidual period hPeriod metric weight vector) tensor point
      ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  change weightedIntegral period hPeriod weight
    (regularFrameSmoothPalatiniCoefficient period hPeriod metric tensor vector) =
      metricResidualIntegral period hPeriod metric tensor
        (weightedPalatiniComponentResidual period hPeriod metric weight vector)
  rw [regularFrameSmoothPalatiniCoefficient_eq_firstJet_fields]
  simp only [weightedPalatiniComponentResidual, map_add, map_sum,
    metricResidualIntegral_coefficients]
  simp_rw [weightedIntegral_mul, regularFrameCanonicalFormalAdjoint_smoothIntegral]

/-- The complete Palatini remainder, retaining the action's fixed density. -/
def regularFrameStoredVolumePalatiniResidual
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (gravitationalCoupling : Real) : SmoothSymmetricCovariantTwoTensor period hPeriod :=
  ∑ vector : Fin 4, weightedPalatiniComponentResidual period hPeriod metric
    (storedVolumePalatiniCurrentWeight period hPeriod metric gravitationalCoupling vector) vector

theorem storedVolumePalatiniRemainder_eq_residualIntegral
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (gravitationalCoupling : Real)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    (∫ point, metric.volume point / (2 * gravitationalCoupling) *
      regularFrameSmoothPalatiniCovariantDivergence period hPeriod metric tensor point
      ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod) =
    ∫ point, generalMetricTensorPairingAt period hPeriod metric.metric
      (regularFrameStoredVolumePalatiniResidual period hPeriod metric gravitationalCoupling)
      tensor point ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  rw [storedVolumePalatiniRemainder_eq_weightedCurrent, map_sum]
  change _ = metricResidualIntegral period hPeriod metric tensor
    (∑ vector : Fin 4, weightedPalatiniComponentResidual period hPeriod metric
      (storedVolumePalatiniCurrentWeight period hPeriod metric gravitationalCoupling vector) vector)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro vector _
  exact weightedPalatiniComponentResidual_integral period hPeriod metric _ tensor vector

def regularFrameStoredVolumeEinsteinHilbertResidual
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (gravitationalCoupling : Real) : SmoothSymmetricCovariantTwoTensor period hPeriod :=
  smoothSymmetricTensorAdd period hPeriod
    (regularFrameStoredVolumeRicciResidual period hPeriod metric gravitationalCoupling)
    (regularFrameStoredVolumePalatiniResidual period hPeriod metric gravitationalCoupling)

/-- Native fixed-volume EH derivative represented without a base volume gauge. -/
theorem regularFrameFixedVolumeEinsteinHilbertDerivative_eq_ungaugedResidualIntegral
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (couplings : EinsteinHilbertCouplings)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    regularGeneralMetricC0FixedVolumeEinsteinHilbertActionDerivativeAtZero period hPeriod metric
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) couplings
      (regularGeneralMetricC2SmoothDirection period hPeriod metric tensor) =
    ∫ point, generalMetricTensorPairingAt period hPeriod metric.metric
      (regularFrameStoredVolumeEinsteinHilbertResidual period hPeriod metric couplings.gravitationalCoupling)
      tensor point ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  rw [regularFrameFixedVolumeEinsteinHilbertDerivative_eq_storedRicci_add_palatini,
    storedVolumePalatiniRemainder_eq_residualIntegral]
  exact (metricResidualIntegral period hPeriod metric tensor).map_add _ _ |>.symm

end
end P0EFTJanusStoredVolumePalatiniMetricResidual4D
end JanusFormal
