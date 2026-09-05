import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFixedVolumeEinsteinHilbertRicciPairing4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusConformalRelativeLorentzVolumeHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMetricResidualTestSeparation4D

/-! # Smooth Ricci residual for the fixed-volume gravity block -/
namespace JanusFormal
namespace P0EFTJanusRegularFrameFixedVolumeRicciResidual4D
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
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVUltralocalMaster4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open P0EFTJanusProgramPRegularGeneralMetricGlobalMaxwellDivergence4D
open P0EFTJanusProgramPRegularGeneralMetricGlobalSmoothEinsteinCoefficients4D
open P0EFTJanusProgramPRegularGeneralMetricGlobalSmoothSymmetricEinsteinTensor4D
open P0EFTJanusProgramPRegularGeneralMetricInvariantMaxwellStressVariation4D

open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusConformalRelativeLorentzVolumeHessian4D
open P0EFTJanusMappingTorusLocalEinsteinHilbertPalatiniVariation4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellStressDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2ScalarCurvatureDerivativePointwise4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertInvariantResidual4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertFixedVariableVolumeDiscrepancy4D
open P0EFTJanusProgramPRegularFrameEinsteinHilbertFrameFreeActionMeasureBridge4D
open P0EFTJanusFixedVolumeEinsteinHilbertRicciPairing4D
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralLorentzMetricBVPairingRegularity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVIntegratedMaster4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMetricResidualTestSeparation4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

/-- Reconstruction from arbitrary smooth covariant coefficients. -/
def regularFrameSmoothCoefficientTensor
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (coefficient : Fin 4 → Fin 4 → SmoothScalarField period hPeriod) :
    SmoothSymmetricCovariantTwoTensor period hPeriod :=
  ∑ first : Fin 4, ∑ second : Fin 4,
    smoothBulkScalarSMulTensor period hPeriod (coefficient first second)
      (smoothBulkCovectorSymmetricProduct period hPeriod
        (regularFrameDualCovector period hPeriod metric first)
        (regularFrameDualCovector period hPeriod metric second))

/-- The reconstructed tensor represents the dual-frame coefficient contraction. -/
theorem regularFrameSmoothCoefficientTensor_pairing
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (coefficient : Fin 4 → Fin 4 → SmoothScalarField period hPeriod)
    (variation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalMetricTensorPairingAt period hPeriod metric.metric
        (regularFrameSmoothCoefficientTensor period hPeriod metric
          coefficient) variation point =
      ∑ first : Fin 4, ∑ second : Fin 4,
        coefficient first second point *
          variation.tensor point
            (regularFrameDualVectorAt period hPeriod metric point first)
            (regularFrameDualVectorAt period hPeriod metric point second) := by
  rw [generalMetricTensorPairingAt_symmetric]
  let pairing :
      SmoothSymmetricCovariantTwoTensor period hPeriod →ₗ[Real] Real :=
    { toFun := fun tensor =>
        generalMetricTensorPairingAt period hPeriod metric.metric variation
          tensor point
      map_add' := by
        intro first second
        exact generalMetricTensorPairingAt_add_right period hPeriod
          metric.metric variation first second point
      map_smul' := by
        intro scalar tensor
        exact generalMetricTensorPairingAt_smul_right period hPeriod
          metric.metric scalar variation tensor point }
  change pairing
      (regularFrameSmoothCoefficientTensor period hPeriod metric
        coefficient) = _
  unfold regularFrameSmoothCoefficientTensor
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro first _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro second _
  let rankOne := smoothBulkCovectorSymmetricProduct period hPeriod
    (regularFrameDualCovector period hPeriod metric first)
    (regularFrameDualCovector period hPeriod metric second)
  have hCongr :
      pairing
          (smoothBulkScalarSMulTensor period hPeriod
            (coefficient first second) rankOne) =
        pairing
          ((coefficient first second point) • rankOne) := by
    apply generalMetricTensorPairingAt_congr_right_at
    apply ContinuousLinearMap.ext
    intro left
    apply ContinuousLinearMap.ext
    intro right
    rfl
  rw [hCongr, map_smul]
  apply congrArg
    (coefficient first second point * ·)
  apply generalMetricTensorPairingAt_symmetricMetricRankOne
    (first := regularFrameDualVectorAt period hPeriod metric point first)
    (second := regularFrameDualVectorAt period hPeriod metric point second)
  intro left right
  change
    (1 / 2 : Real) *
          (regularFrameDualCovector period hPeriod metric first point left *
            regularFrameDualCovector period hPeriod metric second point right) +
        (1 / 2 : Real) *
          (regularFrameDualCovector period hPeriod metric second point left *
            regularFrameDualCovector period hPeriod metric first point right) =
      _
  rw [← regularFrameDualVectorAt_metric_pairing,
    ← regularFrameDualVectorAt_metric_pairing,
    ← regularFrameDualVectorAt_metric_pairing,
    ← regularFrameDualVectorAt_metric_pairing]

/-- Symmetric Ricci tensor reconstructed from its proven smooth coefficients. -/
def regularFrameSymmetricRicciTensor
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    SmoothSymmetricCovariantTwoTensor period hPeriod :=
  regularFrameSmoothCoefficientTensor period hPeriod metric
    (regularGeneralMetricSmoothRicciCoefficient period hPeriod metric)

/-- The inverse-velocity Ricci contraction is the negative invariant pairing. -/
theorem regularFrameRicciInverseVelocity_pairing_invariant
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    tensorPairing
        (regularGeneralMetricC0InverseMetricVelocityAt period hPeriod metric
          (regularGeneralMetricC2SmoothDirection period hPeriod metric tensor) point)
        (regularGeneralMetricC0RicciMatrixAt period hPeriod metric 0 point) =
      -generalMetricTensorPairingAt period hPeriod metric.metric
        (regularFrameSymmetricRicciTensor period hPeriod metric) tensor point := by
  rw [regularGeneralMetricC0InverseMetricVelocity_pairing_eq_dualFrameSum]
  unfold regularFrameSymmetricRicciTensor
  rw [regularFrameSmoothCoefficientTensor_pairing]
  simp only [regularGeneralMetricC0RicciMatrixAt,
    regularGeneralMetricSmoothRicciCoefficient]

/-- The metric-volume weight converts the Ricci block to the canonical pairing. -/
def regularFrameFixedVolumeRicciResidual
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (gravitationalCoupling : Real) : SmoothSymmetricCovariantTwoTensor period hPeriod :=
  smoothBulkScalarSMulTensor period hPeriod
    ((-(1 / (2 * gravitationalCoupling))) •
      globalSmoothMetricVolumeRatio period hPeriod metric.metric)
    (regularFrameSymmetricRicciTensor period hPeriod metric)

theorem regularFrameFixedVolumeRicciResidual_pairing
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (gravitationalCoupling : Real)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalMetricTensorPairingAt period hPeriod metric.metric
        (regularFrameFixedVolumeRicciResidual period hPeriod metric gravitationalCoupling)
        tensor point =
      (-(1 / (2 * gravitationalCoupling)) *
        globalMetricVolumeRatio period hPeriod metric.metric point) *
      generalMetricTensorPairingAt period hPeriod metric.metric
        (regularFrameSymmetricRicciTensor period hPeriod metric) tensor point := by
  unfold regularFrameFixedVolumeRicciResidual
  rw [generalMetricTensorPairingAt_symmetric,
    generalMetricTensorPairingAt_smoothBulkScalarSMul_right,
    generalMetricTensorPairingAt_symmetric]
  rfl

/-- Exact integral representation against the canonical reference volume. -/
theorem regularFrameFixedVolumeRicciPairing_eq_residualIntegral
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (gravitationalCoupling : Real)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    regularFrameFixedVolumeEinsteinHilbertRicciPairing period hPeriod metric
        gravitationalCoupling tensor =
      ∫ point, generalMetricTensorPairingAt period hPeriod metric.metric
        (regularFrameFixedVolumeRicciResidual period hPeriod metric gravitationalCoupling)
        tensor point ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  unfold regularFrameFixedVolumeEinsteinHilbertRicciPairing
  rw [integral_generalLorentzVolumeMeasure_eq_reference]
  apply integral_congr_ae
  filter_upwards [] with point
  rw [regularFrameRicciInverseVelocity_pairing_invariant,
    regularFrameFixedVolumeRicciResidual_pairing]
  ring

/-- The genuine fixed-volume derivative is represented by a smooth Ricci residual. -/
theorem regularFrameFixedVolumeEinsteinHilbertDerivative_eq_residualIntegral
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (couplings : EinsteinHilbertCouplings)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hGauge : RegularGeneralMetricInCanonicalVolumeGauge period hPeriod metric) :
    regularGeneralMetricC0FixedVolumeEinsteinHilbertActionDerivativeAtZero
        period hPeriod metric (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
        couplings (regularGeneralMetricC2SmoothDirection period hPeriod metric tensor) =
      ∫ point, generalMetricTensorPairingAt period hPeriod metric.metric
        (regularFrameFixedVolumeRicciResidual period hPeriod metric
          couplings.gravitationalCoupling) tensor point
        ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  rw [regularFrameFixedVolumeEinsteinHilbertDerivative_eq_ricciPairing
    period hPeriod metric couplings tensor hGauge]
  exact regularFrameFixedVolumeRicciPairing_eq_residualIntegral
    period hPeriod metric couplings.gravitationalCoupling tensor

/-- Both genuine gravity derivatives use the same canonical tensor-pair pairing
that already separates the two metric sectors. -/
theorem regularFrameFixedVolumeEinsteinHilbertDerivatives_eq_pairedResidualPairing
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (plusCouplings minusCouplings : EinsteinHilbertCouplings)
    (test : GlobalMinimalPhysicalMetricTest period hPeriod)
    (hPlusGauge : RegularGeneralMetricInCanonicalVolumeGauge period hPeriod plusBase)
    (hMinusGauge : RegularGeneralMetricInCanonicalVolumeGauge period hPeriod minusBase) :
    regularGeneralMetricC0FixedVolumeEinsteinHilbertActionDerivativeAtZero
        period hPeriod plusBase (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
        plusCouplings (regularGeneralMetricC2SmoothDirection period hPeriod plusBase (test .plus)) +
      regularGeneralMetricC0FixedVolumeEinsteinHilbertActionDerivativeAtZero
        period hPeriod minusBase (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
        minusCouplings (regularGeneralMetricC2SmoothDirection period hPeriod minusBase (test .minus)) =
      regularGeneralMetricC2PairedMetricResidualPairing period hPeriod
        (plusBase.metric, minusBase.metric)
        (regularFrameFixedVolumeRicciResidual period hPeriod plusBase plusCouplings.gravitationalCoupling,
          regularFrameFixedVolumeRicciResidual period hPeriod minusBase minusCouplings.gravitationalCoupling)
        test := by
  rw [regularFrameFixedVolumeEinsteinHilbertDerivative_eq_residualIntegral
      period hPeriod plusBase plusCouplings (test .plus) hPlusGauge,
    regularFrameFixedVolumeEinsteinHilbertDerivative_eq_residualIntegral
      period hPeriod minusBase minusCouplings (test .minus) hMinusGauge]
  have hPlus := (generalMetricTensorPairingAt_continuous period hPeriod plusBase.metric
    (regularFrameFixedVolumeRicciResidual period hPeriod plusBase plusCouplings.gravitationalCoupling)
    (test .plus)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      (μ := intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
  have hMinus := (generalMetricTensorPairingAt_continuous period hPeriod minusBase.metric
    (regularFrameFixedVolumeRicciResidual period hPeriod minusBase minusCouplings.gravitationalCoupling)
    (test .minus)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      (μ := intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
  unfold regularGeneralMetricC2PairedMetricResidualPairing
    canonicalGeneralMetricTensorPairPairing generalMetricTensorPairPairingAt
    globalMinimalPhysicalMetricTestPair
  exact (integral_add hPlus hMinus).symm

end
end P0EFTJanusRegularFrameFixedVolumeRicciResidual4D
end JanusFormal
