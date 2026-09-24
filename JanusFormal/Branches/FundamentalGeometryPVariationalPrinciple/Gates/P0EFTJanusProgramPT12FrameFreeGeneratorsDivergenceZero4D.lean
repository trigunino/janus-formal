import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRegularFrameCanonicalGeneratorsDivergenceZero4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeCurrentPullback4D

/-! Canonical generator divergence vanishes in holonomic coordinates without a global frame. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeGeneratorsDivergenceZero4D
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalTenFlowFrame4D
open P0EFTJanusMappingTorusCanonicalTenFlowGeneratorDivergence4D
open P0EFTJanusCanonicalHolonomicStereographicOverlap4D
open P0EFTJanusProgramPRegularFrameCanonicalDivergenceLocalFormula4D
open P0EFTJanusHolonomicCompactTestPushforward4D
open P0EFTJanusHolonomicLocalDivergenceOpenSeparation4D
open P0EFTJanusHolonomicIntrinsicVolumeIntegralTransport4D
open P0EFTJanusRegularFrameCanonicalGeneratorsDivergenceZero4D
open P0EFTJanusProgramPT12FrameFreeCurrentPullback4D

private abbrev Vector4 := Fin 4 → Real
variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance : BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

theorem frameFreeCanonicalTenFlow_holonomic_test_advection_integral_eq_zero
    (index : Fin 10)
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
      fderiv Real test current (frameFreeCurrentPullback period hPeriod patch
        (canonicalTenFlowVectorField period hPeriod index) current) ∂volume) = 0 := by
  let pushed := holonomicPushforwardSmoothTest period hPeriod patch coordinate test
    hTest hCompact (hSupport.trans hTarget)
  let advection : EffectiveQuotient period hPeriod → Real := fun point =>
    mvfderiv coverModelWithCorners pushed.toFun point
      (canonicalTenFlowVectorField period hPeriod index point)
  let density := localMetricVolumeFactor period hPeriod
    (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch
  let field := frameFreeCurrentPullback period hPeriod patch
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
    have hDerivative := holonomicPushforwardTest_derivative_pullback
      period hPeriod patch coordinate test hTest hCompact (hSupport.trans hTarget)
      current (frameFreeCurrentPullback period hPeriod patch
        (canonicalTenFlowVectorField period hPeriod index) current) (hTarget hCurrent)
    rw [frameFreeCurrentPullback_pushforward] at hDerivative
    exact hDerivative
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

theorem frameFreeCanonicalTenFlow_holonomic_density_divergence_eq_zero
    (index : Fin 10)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Vector4) :
    holonomicLocalDensityDivergence
      (localMetricVolumeFactor period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch)
      (frameFreeCurrentPullback period hPeriod patch
        (canonicalTenFlowVectorField period hPeriod index)) coordinate = 0 := by
  obtain ⟨domain, hCoordinate, hOpen, _hInjective, hTarget, hVolume⟩ :=
    exists_holonomicLocalInverse_target_volume_domain period hPeriod patch coordinate
  apply holonomic_local_divergence_open_separation_gate domain hOpen
    (localMetricVolumeFactor period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch)
    (frameFreeCurrentPullback period hPeriod patch
      (canonicalTenFlowVectorField period hPeriod index))
    (localMetricVolumeFactor_contDiff period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch)
    (localMetricVolumeFactor_ne_zero period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod) patch)
    (frameFreeCurrentPullback_contDiff period hPeriod patch
      (canonicalTenFlowVectorField period hPeriod index)) ?_ coordinate hCoordinate
  intro test hTest hCompact hSupport
  exact frameFreeCanonicalTenFlow_holonomic_test_advection_integral_eq_zero
    period hPeriod index patch coordinate domain hOpen hTarget hVolume test hTest hCompact hSupport

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeGeneratorsDivergenceZero4D
