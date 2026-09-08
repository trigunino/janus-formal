import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameCanonicalVolumeDerivativeAtCenter4D

/-! # Explicit center derivative of the interaction volume defect -/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameC2InteractionVolumeDefectDerivative4D

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 1200000
noncomputable section
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterRegularity4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusFiniteFramePairedRelativeC2Root4D
open P0EFTJanusFiniteFrameC2CanonicalVolume4D
open P0EFTJanusFiniteFrameC2SpectralInteraction4D
open P0EFTJanusFiniteFrameDiffeomorphismBRSTSmoothFeatures4D
open P0EFTJanusFiniteFramePairedC2InteractionAction4D
open P0EFTJanusFiniteFrameC2InteractionFrozenVolumeDecomposition4D
open P0EFTJanusFiniteFrameCanonicalVolumeDerivativeAtCenter4D
open P0EFTJanusReciprocalBimetricPotential

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod
private abbrev C0Scalar := C(EffectiveQuotient period hPeriod, Real)
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance
local instance : CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

variable (geometry : GlobalCandidateAGeometry period hPeriod)
  (frame : SmoothD8Frame period hPeriod)
  (hRegular : ∀ point, Function.Bijective
    (intrinsicCandidateASylvesterAt period hPeriod geometry point))
private abbrev MetricCore :=
  GeneralMetricRelativeC2Core period hPeriod frame geometry.plusMetric
private abbrev Model := PairedFiniteFrameMetricC2Core period hPeriod geometry frame
local instance : NormedAddCommGroup (MetricCore period hPeriod geometry frame) :=
  (generalMetricRelativeC2CoreSubmodule period hPeriod frame
    geometry.plusMetric).normedAddCommGroup
local instance : NormedSpace Real (MetricCore period hPeriod geometry frame) := inferInstance

/-- Derivative of the plus-volume coefficient on the paired metric core. -/
def pairedFiniteFrameCanonicalVolumeDerivativeAtZero :
    Model period hPeriod geometry frame →L[Real] C0Scalar period hPeriod :=
  (finiteFrameCanonicalVolumeC0DerivativeAtZero period hPeriod frame geometry.plusMetric).comp
    (ContinuousLinearMap.fst Real
      (MetricCore period hPeriod geometry frame) (MetricCore period hPeriod geometry frame))

/-- Pointwise density whose integral is exactly the mobile-volume defect. -/
def pairedFiniteFrameC2InteractionVolumeDefectDensity
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (variation : Model period hPeriod geometry frame) : C0Scalar period hPeriod :=
  (-interactionScale) •
    ((finiteFrameCanonicalVolumeC0 period hPeriod frame geometry.plusMetric variation.1 -
        finiteFrameCanonicalVolumeC0 period hPeriod frame geometry.plusMetric 0) *
      canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
        (pairedFiniteFrameC2SpectralPotential period hPeriod frame geometry hRegular coefficients
          variation))

/-- Explicit derivative: moving volume times the central spectral potential. -/
def pairedFiniteFrameC2InteractionVolumeDefectDerivativeAtZero
    (interactionScale : Real) (coefficients : PotentialCoefficients) :
    Model period hPeriod geometry frame →L[Real] Real :=
  (finiteFrameBRSTCanonicalIntegralCLM period hPeriod).comp
    ((-interactionScale) •
      (((ContinuousLinearMap.mul Real (C0Scalar period hPeriod)).flip
        (canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
          (pairedFiniteFrameC2SpectralPotential period hPeriod frame geometry hRegular coefficients
            0))).comp
        (pairedFiniteFrameCanonicalVolumeDerivativeAtZero period hPeriod geometry frame)))

theorem pairedFiniteFrameC2InteractionVolumeDefectAction_eq_integral
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (variation : Model period hPeriod geometry frame) :
    pairedFiniteFrameC2InteractionVolumeDefectAction period hPeriod geometry frame hRegular
        interactionScale coefficients variation =
      finiteFrameBRSTCanonicalIntegralCLM period hPeriod
        (pairedFiniteFrameC2InteractionVolumeDefectDensity period hPeriod geometry frame hRegular
          interactionScale coefficients variation) := by
  unfold pairedFiniteFrameC2InteractionVolumeDefectAction
    pairedFiniteFrameC2InteractionAction pairedFiniteFrameC2FrozenVolumeInteractionAction
  rw [← map_sub]
  apply congrArg (finiteFrameBRSTCanonicalIntegralCLM period hPeriod)
  apply ContinuousMap.ext
  intro point
  simp only [pairedFiniteFrameC2InteractionDensity,
    pairedFiniteFrameC2FrozenVolumeInteractionDensity,
    pairedFiniteFrameC2InteractionVolumeDefectDensity, ContinuousMap.sub_apply,
    ContinuousMap.smul_apply, ContinuousMap.mul_apply, smul_eq_mul]
  ring

theorem pairedFiniteFrameC2InteractionVolumeDefectAction_hasFDerivAt_zero
    (interactionScale : Real) (coefficients : PotentialCoefficients) :
    HasFDerivAt
      (pairedFiniteFrameC2InteractionVolumeDefectAction period hPeriod geometry frame hRegular
        interactionScale coefficients)
      (pairedFiniteFrameC2InteractionVolumeDefectDerivativeAtZero period hPeriod geometry frame
        hRegular interactionScale coefficients) 0 := by
  let volume :=
    (finiteFrameCanonicalVolumeC0 period hPeriod frame geometry.plusMetric) ∘
      (fun variation : Model period hPeriod geometry frame => variation.1)
  let potential := fun variation : Model period hPeriod geometry frame =>
    canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
      (pairedFiniteFrameC2SpectralPotential period hPeriod frame geometry hRegular coefficients
        variation)
  have hVolume :=
    (finiteFrameCanonicalVolumeC0_hasFDerivAt_zero period hPeriod frame
      geometry.plusMetric).comp 0
      (ContinuousLinearMap.fst Real
        (MetricCore period hPeriod geometry frame)
          (MetricCore period hPeriod geometry frame)).hasFDerivAt
  have hPotential : DifferentiableAt Real potential 0 := by
    have hDomain := zero_mem_pairedFiniteFrameC2InteractionDomain period hPeriod geometry frame hRegular
    have hOpen := pairedFiniteFrameC2InteractionDomain_isOpen period hPeriod geometry frame hRegular
    have hPotentialOn : ContDiffOn Real 2 potential
        (pairedFiniteFrameC2InteractionDomain period hPeriod geometry frame hRegular) :=
      (canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod).contDiff.comp_contDiffOn
        ((pairedFiniteFrameC2SpectralPotential_contDiffOn period hPeriod frame geometry hRegular
          coefficients).mono fun _ hVariation => hVariation.1)
    exact ((hPotentialOn 0 hDomain).contDiffAt
      (hOpen.mem_nhds hDomain)).differentiableAt (by norm_num)
  have hDifference := hVolume.sub_const (volume 0)
  have hProduct := hDifference.mul hPotential.hasFDerivAt
  have hDensity : HasFDerivAt
      (pairedFiniteFrameC2InteractionVolumeDefectDensity period hPeriod geometry frame hRegular
        interactionScale coefficients)
      ((-interactionScale) •
        (((ContinuousLinearMap.mul Real (C0Scalar period hPeriod)).flip (potential 0)).comp
          (pairedFiniteFrameCanonicalVolumeDerivativeAtZero period hPeriod geometry frame))) 0 := by
    apply (hProduct.const_smul (-interactionScale)).congr_fderiv
    apply ContinuousLinearMap.ext
    intro direction
    simp [volume, potential, pairedFiniteFrameCanonicalVolumeDerivativeAtZero]
  have hIntegral := (finiteFrameBRSTCanonicalIntegralCLM period hPeriod).hasFDerivAt.comp 0 hDensity
  apply hIntegral.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun variation => by
    simpa [Function.comp_apply] using
      pairedFiniteFrameC2InteractionVolumeDefectAction_eq_integral period hPeriod geometry frame
        hRegular interactionScale coefficients variation

theorem pairedFiniteFrameC2InteractionVolumeDefectEuler_zero_eq_explicit
    (interactionScale : Real) (coefficients : PotentialCoefficients) :
    pairedFiniteFrameC2InteractionVolumeDefectEuler period hPeriod geometry frame hRegular
        interactionScale coefficients 0 =
      pairedFiniteFrameC2InteractionVolumeDefectDerivativeAtZero period hPeriod geometry frame
        hRegular interactionScale coefficients :=
  (pairedFiniteFrameC2InteractionVolumeDefectAction_hasFDerivAt_zero period hPeriod geometry frame
    hRegular interactionScale coefficients).fderiv

end
end P0EFTJanusFiniteFrameC2InteractionVolumeDefectDerivative4D
end JanusFormal
