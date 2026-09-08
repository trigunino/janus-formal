import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameRegularPairedRelativeSmoothDerivativeTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2PhysicalEulerChainRule4D

/-! # Frozen-volume decomposition of the finite-frame interaction derivative -/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameC2InteractionFrozenVolumeDecomposition4D

set_option autoImplicit false
set_option maxHeartbeats 2000000
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
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterRegularity4D
open P0EFTJanusFiniteFramePairedRelativeC2Root4D
open P0EFTJanusFiniteFrameC2CanonicalVolume4D
open P0EFTJanusFiniteFrameC2SpectralInteraction4D
open P0EFTJanusFiniteFrameDiffeomorphismBRSTSmoothFeatures4D
open P0EFTJanusFiniteFramePairedC2InteractionAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalEulerChainRule4D
open P0EFTJanusReciprocalBimetricPotential

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod
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
private abbrev Model := PairedFiniteFrameMetricC2Core period hPeriod geometry frame

/-- Interaction density with the plus-volume coefficient frozen at the chart center. -/
def pairedFiniteFrameC2FrozenVolumeInteractionDensity
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (variation : Model period hPeriod geometry frame) :=
  (-interactionScale) •
    (finiteFrameCanonicalVolumeC0 period hPeriod frame geometry.plusMetric 0 *
      canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
        (pairedFiniteFrameC2SpectralPotential period hPeriod frame geometry hRegular
          coefficients variation))

/-- Integrated interaction action with center-frozen volume. -/
def pairedFiniteFrameC2FrozenVolumeInteractionAction
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (variation : Model period hPeriod geometry frame) : Real :=
  finiteFrameBRSTCanonicalIntegralCLM period hPeriod
    (pairedFiniteFrameC2FrozenVolumeInteractionDensity period hPeriod geometry frame hRegular
      interactionScale coefficients variation)

/-- Exact contribution caused by moving the plus-volume coefficient. -/
def pairedFiniteFrameC2InteractionVolumeDefectAction
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (variation : Model period hPeriod geometry frame) : Real :=
  pairedFiniteFrameC2InteractionAction period hPeriod geometry frame hRegular interactionScale
      coefficients variation -
    pairedFiniteFrameC2FrozenVolumeInteractionAction period hPeriod geometry frame hRegular
      interactionScale coefficients variation

theorem pairedFiniteFrameC2InteractionAction_eq_frozen_add_volumeDefect
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (variation : Model period hPeriod geometry frame) :
    pairedFiniteFrameC2InteractionAction period hPeriod geometry frame hRegular interactionScale
        coefficients variation =
      pairedFiniteFrameC2FrozenVolumeInteractionAction period hPeriod geometry frame hRegular
          interactionScale coefficients variation +
        pairedFiniteFrameC2InteractionVolumeDefectAction period hPeriod geometry frame hRegular
          interactionScale coefficients variation := by
  unfold pairedFiniteFrameC2InteractionVolumeDefectAction
  abel

theorem pairedFiniteFrameC2FrozenVolumeInteractionAction_contDiffOn
    (interactionScale : Real) (coefficients : PotentialCoefficients) :
    ContDiffOn Real 2
      (pairedFiniteFrameC2FrozenVolumeInteractionAction period hPeriod geometry frame hRegular
        interactionScale coefficients)
      (pairedFiniteFrameC2InteractionDomain period hPeriod geometry frame hRegular) := by
  have hPotential : ContDiffOn Real 2
      (pairedFiniteFrameC2SpectralPotential period hPeriod frame geometry hRegular coefficients)
      (pairedFiniteFrameC2InteractionDomain period hPeriod geometry frame hRegular) :=
    (pairedFiniteFrameC2SpectralPotential_contDiffOn period hPeriod frame geometry hRegular
      coefficients).mono fun _ hVariation => hVariation.1
  have hReadout := (canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod).contDiff
    |>.comp_contDiffOn hPotential
  have hVolume : ContDiffOn Real 2 (fun _ : Model period hPeriod geometry frame =>
      finiteFrameCanonicalVolumeC0 period hPeriod frame geometry.plusMetric 0)
      (pairedFiniteFrameC2InteractionDomain period hPeriod geometry frame hRegular) :=
    contDiffOn_const
  have hDensity := (hVolume.mul hReadout).const_smul (-interactionScale)
  exact (finiteFrameBRSTCanonicalIntegralCLM period hPeriod).contDiff.comp_contDiffOn hDensity

theorem pairedFiniteFrameC2InteractionVolumeDefectAction_contDiffOn
    (interactionScale : Real) (coefficients : PotentialCoefficients) :
    ContDiffOn Real 2
      (pairedFiniteFrameC2InteractionVolumeDefectAction period hPeriod geometry frame hRegular
        interactionScale coefficients)
      (pairedFiniteFrameC2InteractionDomain period hPeriod geometry frame hRegular) :=
  (pairedFiniteFrameC2InteractionAction_contDiffOn period hPeriod geometry frame hRegular
    interactionScale coefficients).sub
      (pairedFiniteFrameC2FrozenVolumeInteractionAction_contDiffOn period hPeriod geometry frame
        hRegular interactionScale coefficients)

def pairedFiniteFrameC2FrozenVolumeInteractionEuler
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (variation : Model period hPeriod geometry frame) :
    Model period hPeriod geometry frame →L[Real] Real :=
  fderiv Real (pairedFiniteFrameC2FrozenVolumeInteractionAction period hPeriod geometry frame
    hRegular interactionScale coefficients) variation

def pairedFiniteFrameC2InteractionVolumeDefectEuler
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (variation : Model period hPeriod geometry frame) :
    Model period hPeriod geometry frame →L[Real] Real :=
  fderiv Real (pairedFiniteFrameC2InteractionVolumeDefectAction period hPeriod geometry frame
    hRegular interactionScale coefficients) variation

/-- The mobile-volume Euler is the frozen-volume Euler plus the exact volume defect. -/
theorem pairedFiniteFrameC2InteractionEuler_eq_frozen_add_volumeDefect
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (variation : Model period hPeriod geometry frame)
    (hVariation : variation ∈
      pairedFiniteFrameC2InteractionDomain period hPeriod geometry frame hRegular) :
    pairedFiniteFrameC2InteractionEuler period hPeriod geometry frame hRegular interactionScale
        coefficients variation =
      pairedFiniteFrameC2FrozenVolumeInteractionEuler period hPeriod geometry frame hRegular
          interactionScale coefficients variation +
        pairedFiniteFrameC2InteractionVolumeDefectEuler period hPeriod geometry frame hRegular
          interactionScale coefficients variation := by
  have hOpen := pairedFiniteFrameC2InteractionDomain_isOpen period hPeriod geometry frame hRegular
  have hMobile : DifferentiableAt Real
      (pairedFiniteFrameC2InteractionAction period hPeriod geometry frame hRegular interactionScale
        coefficients) variation :=
    (((pairedFiniteFrameC2InteractionAction_contDiffOn period hPeriod geometry frame hRegular
      interactionScale coefficients) variation hVariation).contDiffAt
        (hOpen.mem_nhds hVariation)).differentiableAt (by norm_num)
  have hFrozen : DifferentiableAt Real
      (pairedFiniteFrameC2FrozenVolumeInteractionAction period hPeriod geometry frame hRegular
        interactionScale coefficients) variation :=
    (((pairedFiniteFrameC2FrozenVolumeInteractionAction_contDiffOn period hPeriod geometry frame
      hRegular interactionScale coefficients) variation hVariation).contDiffAt
        (hOpen.mem_nhds hVariation)).differentiableAt (by norm_num)
  have hDerivative := fderiv_sub hMobile hFrozen
  unfold pairedFiniteFrameC2InteractionEuler
    pairedFiniteFrameC2FrozenVolumeInteractionEuler
    pairedFiniteFrameC2InteractionVolumeDefectEuler
    pairedFiniteFrameC2InteractionVolumeDefectAction
  have hDerivative' :
      fderiv Real (fun current =>
        pairedFiniteFrameC2InteractionAction period hPeriod geometry frame hRegular interactionScale
            coefficients current -
          pairedFiniteFrameC2FrozenVolumeInteractionAction period hPeriod geometry frame hRegular
            interactionScale coefficients current) variation =
        fderiv Real (pairedFiniteFrameC2InteractionAction period hPeriod geometry frame hRegular
            interactionScale coefficients) variation -
          fderiv Real (pairedFiniteFrameC2FrozenVolumeInteractionAction period hPeriod geometry frame
            hRegular interactionScale coefficients) variation := by
    have hFunctions :
        pairedFiniteFrameC2InteractionAction period hPeriod geometry frame hRegular interactionScale
            coefficients -
          pairedFiniteFrameC2FrozenVolumeInteractionAction period hPeriod geometry frame hRegular
            interactionScale coefficients =
        fun current =>
          pairedFiniteFrameC2InteractionAction period hPeriod geometry frame hRegular interactionScale
              coefficients current -
            pairedFiniteFrameC2FrozenVolumeInteractionAction period hPeriod geometry frame hRegular
              interactionScale coefficients current := by
      funext current
      rfl
    exact (congrArg (fun action => fderiv Real action variation) hFunctions).symm.trans hDerivative
  rw [hDerivative']
  abel

end
end P0EFTJanusFiniteFrameC2InteractionFrozenVolumeDecomposition4D
end JanusFormal
