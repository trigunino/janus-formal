import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusHolonomicCompactTestPushforward4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusHolonomicLocalDivergenceOpenSeparation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusHolonomicIntrinsicVolumeIntegralTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalTenFlowGeneratorDivergence4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameCanonicalMetricVolumeCompatibility4D

/-! # Vanishing of the ten regular-frame canonical divergence residuals

Compact coordinate tests push to global smooth tests on the quotient. Exact
intrinsic-volume transport turns canonical-flow integration by parts into
local zero advection. Open-set separation then proves the ten residuals zero
and identifies the regular-frame and weak canonical divergence operators.
-/

namespace JanusFormal
namespace P0EFTJanusRegularFrameCanonicalGeneratorsDivergenceZero4D

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalTenFlowFrame4D
open P0EFTJanusMappingTorusCanonicalTenFlowGeneratorDivergence4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceLinear4D
open P0EFTJanusProgramPRegularFrameEinsteinHilbertFrameFreeActionMeasureBridge4D
open P0EFTJanusProgramPRegularFrameCanonicalDivergenceLaw4D
open P0EFTJanusProgramPRegularFrameCanonicalDivergenceObstruction4D
open P0EFTJanusProgramPRegularFrameCanonicalDivergenceLocalFormula4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellStressDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricGlobalSmoothSymmetricEinsteinTensor4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbertWeightedPalatiniResidual4D
open P0EFTJanusCanonicalHolonomicStereographicOverlap4D
open P0EFTJanusHolonomicCompactTestPushforward4D
open P0EFTJanusHolonomicLocalDivergenceOpenSeparation4D
open P0EFTJanusHolonomicIntrinsicVolumeIntegralTransport4D

private abbrev Vector4 := Fin 4 → Real
variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

/-- The directional derivative of a smooth test along a canonical generator
is a continuous scalar, so the exact real integral transport applies. -/
theorem canonicalTenFlow_test_advection_continuous
    (index : Fin 10) (test : SmoothQuotientField period hPeriod Real) :
    Continuous (fun point => mvfderiv coverModelWithCorners test.toFun point
      (canonicalTenFlowVectorField period hPeriod index point)) := by
  simpa only [frameDerivative_eq_mfderiv, canonicalTenFlowVectorField_apply] using
    ((contMDiff_pi_space.mp (frameDerivative_contMDiff period hPeriod Real
      (canonicalTenFlowFrame period hPeriod) test)) index).continuous

/-- Exact measured holonomic neighborhoods inherit zero test advection
from the global canonical volume-preserving generators. -/
theorem canonicalTenFlow_holonomic_test_advection_integral_eq_zero
    (metric : RegularGeneralLorentzMetric period hPeriod) (index : Fin 10)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4)
    (domain : Set Vector4) (hOpen : IsOpen domain)
    (hTarget : domain ⊆ (holonomicCoordinateLocalInverse period hPeriod patch coordinate).target)
    (hImageVolume : ∀ subset : Set Vector4, MeasurableSet subset → subset ⊆ domain →
      intrinsicCanonicalLorentzVolumeMeasure period hPeriod (patch.coordinateMap '' subset) =
        ∫⁻ current in subset, ENNReal.ofReal (localMetricVolumeFactor period hPeriod
          (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch current))
    (test : Vector4 → Real) (hTest : ContDiff Real ∞ test)
    (hCompact : HasCompactSupport test) (hSupport : tsupport test ⊆ domain) :
    (∫ current, localMetricVolumeFactor period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch current *
      fderiv Real test current (pulledRegularFrameExpansion period hPeriod metric patch
        (canonicalTenFlowVectorField period hPeriod index) current) ∂volume) = 0 := by
  let pushed := holonomicPushforwardSmoothTest period hPeriod patch coordinate test
    hTest hCompact (hSupport.trans hTarget)
  let advection : EffectiveQuotient period hPeriod → Real := fun point =>
    mvfderiv coverModelWithCorners pushed.toFun point
      (canonicalTenFlowVectorField period hPeriod index point)
  let density := localMetricVolumeFactor period hPeriod
    (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch
  let field := pulledRegularFrameExpansion period hPeriod metric patch
    (canonicalTenFlowVectorField period hPeriod index)
  have hContinuous : Continuous advection :=
    canonicalTenFlow_test_advection_continuous period hPeriod index pushed
  have hGlobalZero : (∫ point, advection point
      ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) = 0 :=
    canonicalTenFlowVectorField_testDerivative_integral_eq_zero period hPeriod index pushed
  have hGlobalOutside : ∀ point, point ∉ patch.coordinateMap '' domain → advection point = 0 := by
    intro point hPoint
    exact holonomicPushforwardTest_derivative_eq_zero_off_support
      period hPeriod patch coordinate test hCompact point
      (fun hImage => hPoint (image_mono hSupport hImage))
      (canonicalTenFlowVectorField period hPeriod index point)
  have hGlobalRestricted : (∫ point in patch.coordinateMap '' domain, advection point
      ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) = 0 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hGlobalOutside]
    exact hGlobalZero
  have hPullback : ∀ current ∈ domain,
      advection (patch.coordinateMap current) = fderiv Real test current (field current) := by
    intro current hCurrent
    exact holonomicPushforwardTest_regular_frame_advection period hPeriod metric patch coordinate
      (canonicalTenFlowVectorField period hPeriod index) test hTest hCompact
      (hSupport.trans hTarget) current (hTarget hCurrent)
  have hTransport := holonomicIntrinsicVolume_integral_transport period hPeriod patch domain
    hOpen.measurableSet hImageVolume advection hContinuous
  have hLocalRestricted :
      (∫ current in domain, density current * fderiv Real test current (field current)) = 0 := by
    calc
      (∫ current in domain, density current * fderiv Real test current (field current)) =
          ∫ current in domain, density current * advection (patch.coordinateMap current) := by
        apply setIntegral_congr_fun hOpen.measurableSet
        intro current hCurrent
        exact congrArg (fun value => density current * value) (hPullback current hCurrent).symm
      _ = ∫ point in patch.coordinateMap '' domain, advection point
          ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := hTransport.symm
      _ = 0 := hGlobalRestricted
  have hLocalOutside : ∀ current, current ∉ domain →
      density current * fderiv Real test current (field current) = 0 := by
    intro current hCurrent
    rw [fderiv_of_notMem_tsupport Real (fun hMem => hCurrent (hSupport hMem))]
    simp
  change (∫ current, density current * fderiv Real test current (field current) ∂volume) = 0
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hLocalOutside]
  exact hLocalRestricted

/-- Every canonical generator has zero intrinsic-density coordinate
divergence at every point of every holonomic chart. -/
theorem canonicalTenFlow_holonomic_density_divergence_eq_zero
    (metric : RegularGeneralLorentzMetric period hPeriod) (index : Fin 10)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4) :
    holonomicLocalDensityDivergence
      (localMetricVolumeFactor period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch)
      (pulledRegularFrameExpansion period hPeriod metric patch
        (canonicalTenFlowVectorField period hPeriod index)) coordinate = 0 := by
  obtain ⟨domain, hCoordinate, hOpen, _hInjective, hTarget, hVolume⟩ :=
    exists_holonomicLocalInverse_target_volume_domain period hPeriod patch coordinate
  apply holonomic_local_divergence_open_separation_gate domain hOpen
    (localMetricVolumeFactor period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch)
    (pulledRegularFrameExpansion period hPeriod metric patch
      (canonicalTenFlowVectorField period hPeriod index))
    (localMetricVolumeFactor_contDiff period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch)
    (localMetricVolumeFactor_ne_zero period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch)
    (pulledRegularFrameExpansion_contDiff period hPeriod metric patch
      (canonicalTenFlowVectorField period hPeriod index)) ?_ coordinate hCoordinate
  intro test hTest hCompact hSupport
  exact canonicalTenFlow_holonomic_test_advection_integral_eq_zero period hPeriod metric index
    patch coordinate domain hOpen hTarget hVolume test hTest hCompact hSupport

/-- The ten finite obstructions vanish as actual smooth scalar fields in
canonical-volume gauge. -/
theorem regularFrameCanonicalGeneratorDivergenceResidual_eq_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hGauge : RegularGeneralMetricInCanonicalVolumeGauge period hPeriod metric)
    (index : Fin 10) :
    regularFrameCanonicalGeneratorDivergenceResidual period hPeriod metric index = 0 := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  obtain ⟨patch, coordinate, _hCoordinate, hFormula⟩ :=
    regularFrameCanonicalGeneratorDivergenceResidual_chartThroughEveryPoint
      period hPeriod metric hGauge index point
  change regularFrameCanonicalGeneratorDivergenceResidual period hPeriod metric index point = 0
  rw [hFormula]
  exact canonicalTenFlow_holonomic_density_divergence_eq_zero period hPeriod metric index patch coordinate

/-- The regular-frame divergence operator is the canonical weak divergence,
with the ten generator equations proved rather than assumed. -/
theorem regularFrameAlgebraicCanonicalDivergence_eq_canonical
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hGauge : RegularGeneralMetricInCanonicalVolumeGauge period hPeriod metric) :
    regularFrameAlgebraicCanonicalDivergenceAddMonoidHom period hPeriod metric =
      canonicalTenFlowDivergenceAddMonoidHom period hPeriod metric :=
  regularFrameAlgebraicCanonicalDivergence_eq_canonical_of_generator_zero period hPeriod metric
    (regularFrameCanonicalGeneratorDivergenceResidual_eq_zero period hPeriod metric hGauge)

/-- The pointwise smooth Palatini defect vanishes under canonical-volume
gauge alone, using the now-proved ten generator equations. -/
theorem regularFramePalatiniDefect_eq_zero_of_canonicalVolumeGauge
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hGauge : RegularGeneralMetricInCanonicalVolumeGauge period hPeriod metric) :
    regularGeneralMetricC2PalatiniCanonicalDivergenceDefect period hPeriod metric tensor = 0 :=
  P0EFTJanusProgramPRegularFrameCanonicalMetricVolumeCompatibility4D.regularGeneralMetricC2PalatiniCanonicalDivergenceDefect_eq_zero
    period hPeriod metric tensor hGauge
    (regularFrameCanonicalGeneratorDivergenceResidual_eq_zero period hPeriod metric hGauge)

/-- The smooth Einstein--Hilbert derivative is the pure invariant Einstein
tensor pairing, with no remaining generator-vanishing assumption. -/
theorem regularFrameEinsteinHilbertDerivative_invariantBulk_of_canonicalVolumeGauge
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (couplings : EinsteinHilbertCouplings)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hGauge : RegularGeneralMetricInCanonicalVolumeGauge period hPeriod metric) :
    regularGeneralMetricC0EinsteinHilbertActionDerivativeAtZero period hPeriod metric
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) couplings
        (regularGeneralMetricC2SmoothDirection period hPeriod metric tensor) =
      ∫ point, -(1 / (2 * couplings.gravitationalCoupling)) *
        generalMetricTensorPairingAt period hPeriod metric.metric
          (regularGeneralMetricSymmetricEinsteinTensor period hPeriod metric
            couplings.cosmologicalConstant) tensor point
        ∂(generalLorentzVolumeMeasure period hPeriod metric.metric) :=
  P0EFTJanusProgramPRegularFrameCanonicalMetricVolumeCompatibility4D.regularGeneralMetricC0EinsteinHilbertActionDerivative_smooth_invariantBulk
    period hPeriod metric couplings tensor hGauge
    (regularFrameCanonicalGeneratorDivergenceResidual_eq_zero period hPeriod metric hGauge)

/-- Gate marker: all ten residual fields vanish and the global operators agree. -/
theorem regular_frame_canonical_generators_divergence_zero_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (hGauge : RegularGeneralMetricInCanonicalVolumeGauge period hPeriod metric) :
    (∀ index : Fin 10,
      regularFrameCanonicalGeneratorDivergenceResidual period hPeriod metric index = 0) ∧
      regularFrameAlgebraicCanonicalDivergenceAddMonoidHom period hPeriod metric =
        canonicalTenFlowDivergenceAddMonoidHom period hPeriod metric :=
  ⟨regularFrameCanonicalGeneratorDivergenceResidual_eq_zero period hPeriod metric hGauge,
    regularFrameAlgebraicCanonicalDivergence_eq_canonical period hPeriod metric hGauge⟩

end
end P0EFTJanusRegularFrameCanonicalGeneratorsDivergenceZero4D
end JanusFormal
