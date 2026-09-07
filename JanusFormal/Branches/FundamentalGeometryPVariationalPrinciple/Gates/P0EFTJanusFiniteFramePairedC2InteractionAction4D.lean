import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2SpectralInteraction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2CanonicalVolume4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameDiffeomorphismBRSTSmoothFeatures4D

/-! # Candidate-A interaction action on the paired finite-frame C² chart

The selected paired root potential is multiplied by the positive canonical
plus-metric volume and integrated against the fixed intrinsic measure.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteFramePairedC2InteractionAction4D

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDensity4D
open P0EFTJanusVariableMetricCanonicalVolumeRatio4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterRegularity4D
open P0EFTJanusFiniteFramePairedRelativeC2Root4D
open P0EFTJanusFiniteFrameC2CanonicalVolume4D
open P0EFTJanusFiniteFrameC2SpectralInteraction4D
open P0EFTJanusFiniteFrameDiffeomorphismBRSTSmoothFeatures4D
open P0EFTJanusMatrixSquareRootInteractionDensity
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
local notation "Model" => PairedFiniteFrameMetricC2Core period hPeriod geometry frame

def pairedFiniteFrameC2InteractionDomain : Set Model :=
  pairedFiniteFrameMetricC2RootDomain period hPeriod geometry frame hRegular ∩
    Prod.fst ⁻¹' generalMetricRelativeC2VolumeDomain period hPeriod frame geometry.plusMetric

theorem pairedFiniteFrameC2InteractionDomain_isOpen :
    IsOpen (pairedFiniteFrameC2InteractionDomain period hPeriod geometry frame hRegular) :=
  (pairedFiniteFrameMetricC2RootDomain_isOpen period hPeriod geometry frame hRegular).inter
    ((generalMetricRelativeC2VolumeDomain_isOpen period hPeriod frame geometry.plusMetric).preimage
      continuous_fst)

theorem zero_mem_pairedFiniteFrameC2InteractionDomain :
    (0 : Model) ∈ pairedFiniteFrameC2InteractionDomain period hPeriod geometry frame hRegular :=
  ⟨zero_mem_pairedFiniteFrameMetricC2RootDomain period hPeriod geometry frame hRegular,
    zero_mem_generalMetricRelativeC2VolumeDomain period hPeriod frame geometry.plusMetric⟩

def pairedFiniteFrameC2InteractionDensity (interactionScale : Real)
    (coefficients : PotentialCoefficients) (variation : Model) : C0Scalar period hPeriod :=
  (-interactionScale) •
    (finiteFrameCanonicalVolumeC0 period hPeriod frame geometry.plusMetric variation.1 *
      canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
        (pairedFiniteFrameC2SpectralPotential period hPeriod frame geometry hRegular
          coefficients variation))

theorem pairedFiniteFrameC2InteractionDensity_contDiffOn (interactionScale : Real)
    (coefficients : PotentialCoefficients) :
    ContDiffOn Real 2
      (pairedFiniteFrameC2InteractionDensity period hPeriod geometry frame hRegular
        interactionScale coefficients)
      (pairedFiniteFrameC2InteractionDomain period hPeriod geometry frame hRegular) := by
  have hFirst : ContDiffOn Real 2 (fun variation : Model => variation.1)
      (pairedFiniteFrameC2InteractionDomain period hPeriod geometry frame hRegular) :=
    contDiff_fst.contDiffOn
  have hVolume := (finiteFrameCanonicalVolumeC0_contDiffOn_two period hPeriod frame
    geometry.plusMetric).comp hFirst (fun _ hVariation => hVariation.2)
  have hPotential : ContDiffOn Real 2
      (pairedFiniteFrameC2SpectralPotential period hPeriod frame geometry hRegular coefficients)
      (pairedFiniteFrameC2InteractionDomain period hPeriod geometry frame hRegular) :=
    (pairedFiniteFrameC2SpectralPotential_contDiffOn period hPeriod frame geometry
      hRegular coefficients).mono (fun _ hVariation => hVariation.1)
  have hReadout := (canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod).contDiff
    |>.comp_contDiffOn hPotential
  exact (hVolume.mul hReadout).const_smul (-interactionScale)

theorem pairedFiniteFrameC2InteractionDensity_zero_valueAt (interactionScale : Real)
    (coefficients : PotentialCoefficients) (point : EffectiveQuotient period hPeriod)
    (basis : Module.Basis (Fin 4) Real (TangentSpace coverModelWithCorners point)) :
    pairedFiniteFrameC2InteractionDensity period hPeriod geometry frame hRegular interactionScale
        coefficients 0 point =
      -interactionScale * globalMetricVolumeRatio period hPeriod geometry.plusMetric point *
        matrixSpectralPotential coefficients
          (LinearMap.toMatrix basis basis (geometry.rootAt point).toLinearMap) := by
  unfold pairedFiniteFrameC2InteractionDensity
  rw [show (0 : Model).1 = 0 by rfl]
  simp only [ContinuousMap.smul_apply, ContinuousMap.mul_apply, smul_eq_mul]
  rw [finiteFrameCanonicalVolumeC0_zero]
  rw [pairedFiniteFrameC2SpectralPotential_zero_valueAt period hPeriod frame geometry hRegular
    coefficients point basis]
  change -interactionScale *
    (globalMetricVolumeRatio period hPeriod geometry.plusMetric point *
      matrixSpectralPotential coefficients
        (LinearMap.toMatrix basis basis (geometry.rootAt point).toLinearMap)) = _
  ring

def pairedFiniteFrameC2InteractionAction (interactionScale : Real)
    (coefficients : PotentialCoefficients) (variation : Model) : Real :=
  finiteFrameBRSTCanonicalIntegralCLM period hPeriod
    (pairedFiniteFrameC2InteractionDensity period hPeriod geometry frame hRegular
      interactionScale coefficients variation)

theorem pairedFiniteFrameC2InteractionAction_contDiffOn (interactionScale : Real)
    (coefficients : PotentialCoefficients) :
    ContDiffOn Real 2
      (pairedFiniteFrameC2InteractionAction period hPeriod geometry frame hRegular
        interactionScale coefficients)
      (pairedFiniteFrameC2InteractionDomain period hPeriod geometry frame hRegular) :=
  (finiteFrameBRSTCanonicalIntegralCLM period hPeriod).contDiff.comp_contDiffOn
    (pairedFiniteFrameC2InteractionDensity_contDiffOn period hPeriod geometry frame hRegular
      interactionScale coefficients)

end
end P0EFTJanusFiniteFramePairedC2InteractionAction4D
end JanusFormal
