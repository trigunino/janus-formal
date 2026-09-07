import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2FullBRSTGaugeAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2InteractionAction4D

/-! # Full gauge-fixed contribution plus spectral interaction on one C² chart -/

namespace JanusFormal
namespace P0EFTJanusFiniteFramePairedC2GaugeInteractionAction4D

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
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterRegularity4D
open P0EFTJanusFiniteFramePairedC2FullBRSTGaugeAction4D
open P0EFTJanusFiniteFramePairedC2InteractionAction4D
open P0EFTJanusMatrixSquareRootInteractionDensity
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

abbrev FiniteFramePairedC2GaugeInteractionCore :=
  FiniteFramePairedC2FullBRSTGaugeCore period hPeriod frame frame frame
    geometry.plusMetric geometry.plusMetric

local notation "Input" => FiniteFramePairedC2GaugeInteractionCore period hPeriod geometry frame

def finiteFramePairedC2GaugeInteractionDomain : Set Input :=
  finiteFramePairedC2FullBRSTGaugeDomain period hPeriod frame frame frame
      geometry.plusMetric geometry.plusMetric ∩
    Prod.fst ⁻¹' pairedFiniteFrameC2InteractionDomain period hPeriod geometry frame hRegular

theorem finiteFramePairedC2GaugeInteractionDomain_isOpen :
    IsOpen (finiteFramePairedC2GaugeInteractionDomain period hPeriod geometry frame hRegular) :=
  (finiteFramePairedC2FullBRSTGaugeDomain_isOpen period hPeriod frame frame frame
    geometry.plusMetric geometry.plusMetric).inter
      ((pairedFiniteFrameC2InteractionDomain_isOpen period hPeriod geometry frame hRegular).preimage
        continuous_fst)

def finiteFramePairedC2GaugeInteractionAction (couplings : GlobalCandidateAActionCouplings)
    (interactionScale : Real) (coefficients : PotentialCoefficients) (input : Input) : Real :=
  finiteFramePairedC2FullBRSTGaugeAction period hPeriod frame frame frame
      geometry.plusMetric geometry.plusMetric couplings input +
    pairedFiniteFrameC2InteractionAction period hPeriod geometry frame hRegular
      interactionScale coefficients input.1

theorem finiteFramePairedC2GaugeInteractionAction_contDiffOn_two
    (couplings : GlobalCandidateAActionCouplings) (interactionScale : Real)
    (coefficients : PotentialCoefficients) :
    ContDiffOn Real 2
      (finiteFramePairedC2GaugeInteractionAction period hPeriod geometry frame hRegular
        couplings interactionScale coefficients)
      (finiteFramePairedC2GaugeInteractionDomain period hPeriod geometry frame hRegular) := by
  have hGauge : ContDiffOn Real 2
      (finiteFramePairedC2FullBRSTGaugeAction period hPeriod frame frame frame
        geometry.plusMetric geometry.plusMetric couplings)
      (finiteFramePairedC2GaugeInteractionDomain period hPeriod geometry frame hRegular) :=
    (finiteFramePairedC2FullBRSTGaugeAction_contDiffOn_two period hPeriod
      frame frame frame geometry.plusMetric geometry.plusMetric couplings).mono
        (fun _ hInput => hInput.1)
  have hMetrics : ContDiffOn Real 2 (fun input : Input => input.1)
      (finiteFramePairedC2GaugeInteractionDomain period hPeriod geometry frame hRegular) :=
    contDiff_fst.contDiffOn
  have hInteraction := (pairedFiniteFrameC2InteractionAction_contDiffOn period hPeriod geometry
    frame hRegular interactionScale coefficients).comp hMetrics (fun _ hInput => hInput.2)
  have h := hGauge.add hInteraction
  simp only [Function.comp_def] at h
  exact h

def finiteFramePairedC2GaugeInteractionEuler (couplings : GlobalCandidateAActionCouplings)
    (interactionScale : Real) (coefficients : PotentialCoefficients) (input : Input) :
    Input →L[Real] Real :=
  fderiv Real (finiteFramePairedC2GaugeInteractionAction period hPeriod geometry frame hRegular
    couplings interactionScale coefficients) input

theorem finiteFramePairedC2GaugeInteractionAction_hasFDerivAt
    (couplings : GlobalCandidateAActionCouplings) (interactionScale : Real)
    (coefficients : PotentialCoefficients) (input : Input)
    (hInput : input ∈ finiteFramePairedC2GaugeInteractionDomain period hPeriod geometry frame hRegular) :
    HasFDerivAt
      (finiteFramePairedC2GaugeInteractionAction period hPeriod geometry frame hRegular
        couplings interactionScale coefficients)
      (finiteFramePairedC2GaugeInteractionEuler period hPeriod geometry frame hRegular
        couplings interactionScale coefficients input) input :=
  (((finiteFramePairedC2GaugeInteractionAction_contDiffOn_two period hPeriod geometry frame hRegular
    couplings interactionScale coefficients input hInput).contDiffAt
      ((finiteFramePairedC2GaugeInteractionDomain_isOpen period hPeriod geometry frame hRegular).mem_nhds
        hInput)).differentiableAt (by norm_num)).hasFDerivAt

end
end P0EFTJanusFiniteFramePairedC2GaugeInteractionAction4D
end JanusFormal
