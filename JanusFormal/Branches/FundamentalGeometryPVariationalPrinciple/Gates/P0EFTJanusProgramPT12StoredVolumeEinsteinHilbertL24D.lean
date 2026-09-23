import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RaisedTensorCovectorL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusStoredVolumePalatiniMetricResidual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRegularFrameFixedVolumeRicciResidual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RegularTensorCovectorL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFixedVolumeMaxwellStressResidual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRegularFrameMetricTensorTrace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RegularTensorL2Bridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRegularFrameCanonicalFormalAdjoint4D

/-! The full native fixed-volume Einstein--Hilbert variation has an actual L2 covector. -/
namespace JanusFormal.P0EFTJanusProgramPT12StoredVolumeEinsteinHilbertL24D
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

open scoped BigOperators
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D
open P0EFTJanusMappingTorusMetricCartanGlobalAction4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusRegularFrameSymmetricTensorDivergence4D
open P0EFTJanusRegularFrameMetricCartanCoefficients4D
open P0EFTJanusProgramPT12CanonicalFrameDerivativeAdjoint4D
open P0EFTJanusProgramPT12CanonicalFirstOrderColumn4D

open P0EFTJanusProgramPT12SmoothMatrixL24D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open Set

open P0EFTJanusProgramPT12FrameTensorL2Transport4D

open P0EFTJanusProgramPT12FrameTensorL2Equiv4D
open P0EFTJanusProgramPT12RegularFrameCartanClosed4D
open P0EFTJanusProgramPT12PairedRegularFrameCartan4D
open P0EFTJanusProgramPT12PairedRegularFrameCartanCore4D
open P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphCore4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusD9D10ExactFieldContentBridge4D

variable (reference : RegularGeneralLorentzMetric period hPeriod)

open scoped InnerProductSpace
open P0EFTJanusRegularFrameCanonicalFormalAdjoint4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusProgramPT12RegularTensorL2Bridge4D

open P0EFTJanusMappingTorusGeneralLorentzMetricBVUltralocalMaster4D
open P0EFTJanusMappingTorusGeneralMetricSmoothTrace4D
open P0EFTJanusProgramPRegularFrameMetricInverse4D
open P0EFTJanusProgramPRegularGeneralMetricGlobalSmoothMaxwellStressTensor4D
open P0EFTJanusProgramPRegularGeneralMetricInvariantMaxwellStressVariation4D
open P0EFTJanusFixedVolumeMaxwellStressResidual4D
open P0EFTJanusRegularFrameMetricTensorTrace4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D
open P0EFTJanusMappingTorusConformalFrameFreeMaxwellHessian4D

open P0EFTJanusRegularFrameFixedVolumeRicciResidual4D
open P0EFTJanusProgramPT12RegularTensorCovectorL24D

open P0EFTJanusProgramPT12RaisedTensorCovectorL24D
open P0EFTJanusStoredVolumePalatiniMetricResidual4D
open P0EFTJanusFixedVolumeEinsteinHilbertWeightedPalatini4D
open P0EFTJanusStoredVolumePalatiniCurrentWeight4D
open P0EFTJanusSmoothPalatiniCurrentLinearCoefficients4D
open P0EFTJanusProgramPRegularGeneralMetricGlobalSmoothEinsteinCoefficients4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothMetricParameterJet4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellStressDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertFixedVariableVolumeDiscrepancy4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVPairingRegularity4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
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

/-- The actual stored-volume Ricci term, including its sign and coupling. -/
def storedVolumeRicciL2 (gravitationalCoupling : Real) :
    GlobalGeneralMetricTensorFrameL2 period hPeriod :=
  regularTensorCovectorActualL2 period hPeriod reference fun first second =>
    (-(1 / (2 * gravitationalCoupling))) • smoothScalarFieldMul period hPeriod reference.volume
      (raisedTensorCoefficient period hPeriod reference
        (regularGeneralMetricSmoothRicciCoefficient period hPeriod reference) first second)

theorem storedVolumeRicciL2_pairing (gravitationalCoupling : Real)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    inner Real (storedVolumeRicciL2 period hPeriod reference gravitationalCoupling)
      (globalGeneralMetricTensorFrameL2LinearMap period hPeriod tensor) =
    ∫ point, generalMetricTensorPairingAt period hPeriod reference.metric
      (regularFrameStoredVolumeRicciResidual period hPeriod reference gravitationalCoupling)
      tensor point ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  rw [storedVolumeRicciL2, regularTensorCovectorActualL2_pairing]
  apply integral_congr_ae
  filter_upwards [] with point
  rw [regularFrameCovariantCoefficientTensor_pairing, regularFrameStoredVolumeRicciResidual_pairing]
  unfold regularFrameSymmetricRicciTensor
  rw [coefficientTensor_pairing_eq_raisedCoefficients]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  change (-(1 / (2 * gravitationalCoupling)) * (reference.volume point * _)) * _ = _
  ring

/-- Integration by parts moves the complete Palatini first jet onto smooth coefficients. -/
def weightedPalatiniComponentL2 (weight : SmoothScalarField period hPeriod) (vector : Fin 4) :
    GlobalGeneralMetricTensorFrameL2 period hPeriod :=
  regularTensorCovectorActualL2 period hPeriod reference
    (fun first second => smoothScalarFieldMul period hPeriod weight
      (smoothPalatiniValueCoefficient period hPeriod reference vector first second)) +
  ∑ derivative : Fin 4, regularTensorCovectorActualL2 period hPeriod reference
    (fun first second => regularFrameCanonicalFormalAdjoint period hPeriod reference
      (smoothScalarFieldMul period hPeriod weight
        (smoothPalatiniDerivativeCoefficient period hPeriod reference vector derivative first second)) derivative)

theorem weightedPalatiniComponentL2_pairing
    (weight : SmoothScalarField period hPeriod) (vector : Fin 4)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    inner Real (weightedPalatiniComponentL2 period hPeriod reference weight vector)
      (globalGeneralMetricTensorFrameL2LinearMap period hPeriod tensor) =
    ∫ point, generalMetricTensorPairingAt period hPeriod reference.metric
      (weightedPalatiniComponentResidual period hPeriod reference weight vector) tensor point
      ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  change _ = metricResidualIntegral period hPeriod reference tensor _
  simp only [weightedPalatiniComponentL2, weightedPalatiniComponentResidual,
    inner_add_left, sum_inner, map_add, map_sum, regularTensorCovectorActualL2_pairing]
  rfl

def storedVolumePalatiniL2 (gravitationalCoupling : Real) :
    GlobalGeneralMetricTensorFrameL2 period hPeriod :=
  ∑ vector : Fin 4, weightedPalatiniComponentL2 period hPeriod reference
    (storedVolumePalatiniCurrentWeight period hPeriod reference gravitationalCoupling vector) vector

theorem storedVolumePalatiniL2_pairing (gravitationalCoupling : Real)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    inner Real (storedVolumePalatiniL2 period hPeriod reference gravitationalCoupling)
      (globalGeneralMetricTensorFrameL2LinearMap period hPeriod tensor) =
    ∫ point, generalMetricTensorPairingAt period hPeriod reference.metric
      (regularFrameStoredVolumePalatiniResidual period hPeriod reference gravitationalCoupling)
      tensor point ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  change _ = metricResidualIntegral period hPeriod reference tensor _
  simp only [storedVolumePalatiniL2, regularFrameStoredVolumePalatiniResidual,
    sum_inner, map_sum, weightedPalatiniComponentL2_pairing]
  rfl

def storedVolumeEinsteinHilbertL2 (couplings : EinsteinHilbertCouplings) :
    GlobalGeneralMetricTensorFrameL2 period hPeriod :=
  storedVolumeRicciL2 period hPeriod reference couplings.gravitationalCoupling +
    storedVolumePalatiniL2 period hPeriod reference couplings.gravitationalCoupling

theorem storedVolumeEinsteinHilbertL2_pairing (couplings : EinsteinHilbertCouplings)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    inner Real (storedVolumeEinsteinHilbertL2 period hPeriod reference couplings)
      (globalGeneralMetricTensorFrameL2LinearMap period hPeriod tensor) =
    ∫ point, generalMetricTensorPairingAt period hPeriod reference.metric
      (regularFrameStoredVolumeEinsteinHilbertResidual period hPeriod reference couplings.gravitationalCoupling)
      tensor point ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  change _ = metricResidualIntegral period hPeriod reference tensor
    (regularFrameStoredVolumeRicciResidual period hPeriod reference couplings.gravitationalCoupling +
      regularFrameStoredVolumePalatiniResidual period hPeriod reference couplings.gravitationalCoupling)
  rw [storedVolumeEinsteinHilbertL2, inner_add_left, map_add,
    storedVolumeRicciL2_pairing, storedVolumePalatiniL2_pairing]
  rfl

/-- Native EH first variation, with no volume gauge or stationarity premise. -/
theorem storedVolumeEinsteinHilbertDerivative_eq_inner (couplings : EinsteinHilbertCouplings)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    regularGeneralMetricC0FixedVolumeEinsteinHilbertActionDerivativeAtZero period hPeriod reference
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) couplings
      (regularGeneralMetricC2SmoothDirection period hPeriod reference tensor) =
    inner Real (storedVolumeEinsteinHilbertL2 period hPeriod reference couplings)
      (globalGeneralMetricTensorFrameL2LinearMap period hPeriod tensor) := by
  rw [regularFrameFixedVolumeEinsteinHilbertDerivative_eq_ungaugedResidualIntegral,
    storedVolumeEinsteinHilbertL2_pairing]

theorem storedVolumeEinsteinHilbertDerivative_bound (couplings : EinsteinHilbertCouplings)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    ‖regularGeneralMetricC0FixedVolumeEinsteinHilbertActionDerivativeAtZero period hPeriod reference
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) couplings
      (regularGeneralMetricC2SmoothDirection period hPeriod reference tensor)‖ ≤
    ‖storedVolumeEinsteinHilbertL2 period hPeriod reference couplings‖ *
      ‖globalGeneralMetricTensorFrameL2LinearMap period hPeriod tensor‖ := by
  rw [storedVolumeEinsteinHilbertDerivative_eq_inner]
  exact norm_inner_le_norm _ _

end
end JanusFormal.P0EFTJanusProgramPT12StoredVolumeEinsteinHilbertL24D
