import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT05LLLocalDensityRelativeBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D

/-!
# T05 bulk-action local-density bridge

This module assembles the actual finite-frame Einstein--Hilbert, Abelian and
diffeomorphism BRST, interaction, and Maxwell densities used by the bulk action
underlying T03.  They are integrated by the existing canonical spacetime
integral.  The LL summand uses the throat density and integral of Gate 826.

The primitive SpinC graph already has an exact integrated action but no local
continuous density on the spacetime carrier used here.  It is therefore kept
as an explicitly typed frontier state and is evaluated only by its existing
graph action.  The resulting mixed evaluation equals the existing
physical/Maxwell/SpinC/LL bulk action exactly and is injected into Gate 819's
`.bulk` slot.  This does not construct a uniform local density for SpinC or a
local vertical differential, and does not close T05.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT05BulkActionLocalDensityBridge4D

set_option autoImplicit false
noncomputable section

open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterRegularity4D
open P0EFTJanusProgramPCandidateADiagonalDiffeomorphismKineticAdjointBridge4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusFiniteFrameDiffeomorphismBRSTSmoothFeatures4D
open P0EFTJanusFiniteFrameC2EinsteinHilbertAction4D
open P0EFTJanusFiniteFrameC2AbelianBRSTAction4D
open P0EFTJanusFiniteFrameC2DiffeomorphismBRSTAction4D
open P0EFTJanusFiniteFramePairedDiffeomorphismBRSTAction4D
open P0EFTJanusFiniteFramePairedC2FullBRSTGaugeAction4D
open P0EFTJanusFiniteFramePairedC2EinsteinBRSTAction4D
open P0EFTJanusFiniteFramePairedC2InteractionAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalAction4D
open P0EFTJanusFiniteFrameC2MobileMaxwellAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPT05LLLocalDensityRelativeBridge4D
open P0EFTJanusProgramPRelativeJetVariationalBicomplexCore4D
open P0EFTJanusProgramPRelativeJetVariationalBicomplexCore4D.RelativeJetStratum4D
open P0EFTJanusProgramPT05ExactT03RelativeVariationalRealization4D
open P0EFTJanusReciprocalBimetricPotential

attribute [local instance 2000]
  NonUnitalNormedRing.toNormedAddCommGroup NormedAlgebra.toNormedSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance bulkEffectiveThroatMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) :=
  borel _

local instance bulkEffectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

local instance bulkCanonicalThroatMeasureIsFinite :
    IsFiniteMeasure (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod

variable (geometry : GlobalCandidateAGeometry period hPeriod)
  (frame : SmoothD8Frame period hPeriod)
  (hRegular : ∀ point, Function.Bijective
    (intrinsicCandidateASylvesterAt period hPeriod geometry point))
  (couplings : GlobalCandidateAActionCouplings)

local notation "PhysicalInput" =>
  FiniteFramePairedC2PhysicalCore period hPeriod geometry frame

local notation "OldInput" =>
  FiniteFramePairedC2PhysicalMaxwellSpinCMatterCore
    period hPeriod geometry frame couplings

local notation "LLInput" =>
  GlobalMinimalPhysicalLLC0FirstJetPacket period hPeriod
    (canonicalDivergenceFreeLLFrame period hPeriod)

local notation "Input" =>
  FiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCore
    period hPeriod geometry frame couplings

/-- Sum of the two genuine finite-frame Einstein--Hilbert densities after the
physical recentering used by the action. -/
def programPT05BulkEinsteinHilbertDensity
    (input : PhysicalInput) : C(EffectiveQuotient period hPeriod, Real) :=
  let recentered :=
    finiteFramePairedC2PhysicalRecenter period hPeriod geometry frame input
  finiteFrameC2EinsteinHilbertDensity period hPeriod frame geometry.plusMetric
      couplings.plusEinstein recentered.1.1 +
    finiteFrameC2EinsteinHilbertDensity period hPeriod frame geometry.plusMetric
      couplings.minusEinstein recentered.1.2

/-- Sum of the two genuine Abelian BRST densities on the shared metric pair. -/
def programPT05BulkAbelianBRSTDensity
    (input : PhysicalInput) : C(EffectiveQuotient period hPeriod, Real) :=
  let recentered :=
    finiteFramePairedC2PhysicalRecenter period hPeriod geometry frame input
  let abelian :=
    finiteFramePairedC2FullBRSTGaugeAbelianProjection period hPeriod
      frame frame frame geometry.plusMetric geometry.plusMetric recentered
  finiteFrameC2AbelianBRSTDensity period hPeriod frame geometry.plusMetric
      abelian.1 +
    finiteFrameC2AbelianBRSTDensity period hPeriod frame geometry.plusMetric
      abelian.2

/-- Einstein-weighted diagonal diffeomorphism BRST density used by the paired
action. -/
def programPT05BulkDiffeomorphismBRSTDensity
    (input : PhysicalInput) : C(EffectiveQuotient period hPeriod, Real) :=
  let recentered :=
    finiteFramePairedC2PhysicalRecenter period hPeriod geometry frame input
  let paired :=
    finiteFramePairedC2FullBRSTGaugeDiffeomorphismProjection period hPeriod
      frame frame frame geometry.plusMetric geometry.plusMetric recentered
  candidateAPlusEinsteinKineticWeight couplings •
      finiteFrameC2DiffeomorphismBRSTDensity period hPeriod frame
        geometry.plusMetric
        (finiteFramePairedDiffeomorphismBRSTPlusInput period hPeriod
          frame frame frame geometry.plusMetric geometry.plusMetric paired) +
    candidateAMinusEinsteinKineticWeight couplings •
      finiteFrameC2DiffeomorphismBRSTDensity period hPeriod frame
        geometry.plusMetric
        (finiteFramePairedDiffeomorphismBRSTMinusInput period hPeriod
          frame frame frame geometry.plusMetric geometry.plusMetric paired)

/-- Genuine spectral interaction density on the unrecentered physical metric
pair, exactly as in the existing action. -/
def programPT05BulkInteractionDensity
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (input : PhysicalInput) : C(EffectiveQuotient period hPeriod, Real) :=
  pairedFiniteFrameC2InteractionDensity period hPeriod geometry frame hRegular
    interactionScale coefficients input.1

/-- Independently weighted mobile Maxwell densities after physical
recentering. -/
def programPT05BulkMaxwellDensity
    (input : PhysicalInput) : C(EffectiveQuotient period hPeriod, Real) :=
  let recentered :=
    finiteFramePairedC2PhysicalRecenter period hPeriod geometry frame input
  let maxwell :=
    finiteFramePairedC2PhysicalMaxwellProjection period hPeriod geometry frame
      recentered
  couplings.plusMaxwellScale •
      finiteFrameC2MobileMaxwellDensity period hPeriod frame
        geometry.plusMetric maxwell.1 +
    couplings.minusMaxwellScale •
      finiteFrameC2MobileMaxwellDensity period hPeriod frame
        geometry.plusMetric maxwell.2

/-- SpinC is retained as a closed-graph state because the existing primitive
graph action has no continuous spacetime-density representative in this API. -/
structure ProgramPT05BulkSpinCLocalDensityFrontier
    (period : Real) (hPeriod : period ≠ 0) (matterMassSquared : Real) where
  graphState :
    ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod matterMassSquared

/-- Typed packet of all presently realized bulk densities and the honest
SpinC frontier. -/
structure ProgramPT05BulkActionLocalDensityPacket
    (period : Real) (hPeriod : period ≠ 0)
    (couplings : GlobalCandidateAActionCouplings) where
  einsteinHilbertDensity : C(EffectiveQuotient period hPeriod, Real)
  abelianBRSTDensity : C(EffectiveQuotient period hPeriod, Real)
  diffeomorphismBRSTDensity : C(EffectiveQuotient period hPeriod, Real)
  interactionDensity : C(EffectiveQuotient period hPeriod, Real)
  maxwellDensity : C(EffectiveQuotient period hPeriod, Real)
  llDensity : ProgramPT05LLLocalDensityCochain period hPeriod
  spinCFrontier : ProgramPT05BulkSpinCLocalDensityFrontier period hPeriod
    couplings.matterMassSquared

/-- Canonical packet extracted from the exact old-plus-LL bulk input. -/
def programPT05CanonicalBulkActionLocalDensityPacket
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (input : Input) :
    ProgramPT05BulkActionLocalDensityPacket period hPeriod couplings where
  einsteinHilbertDensity :=
    programPT05BulkEinsteinHilbertDensity period hPeriod geometry frame
      couplings input.1.1
  abelianBRSTDensity :=
    programPT05BulkAbelianBRSTDensity period hPeriod geometry frame input.1.1
  diffeomorphismBRSTDensity :=
    programPT05BulkDiffeomorphismBRSTDensity period hPeriod geometry frame
      couplings input.1.1
  interactionDensity :=
    programPT05BulkInteractionDensity period hPeriod geometry frame hRegular
      interactionScale coefficients input.1.1
  maxwellDensity :=
    programPT05BulkMaxwellDensity period hPeriod geometry frame couplings
      input.1.1
  llDensity :=
    programPT05CanonicalPTLLLocalDensityCochain period hPeriod
      (canonicalDivergenceFreeLLFrame period hPeriod) input.2
  spinCFrontier := ⟨input.1.2⟩

/-- Total continuous spacetime density of the five realized spacetime
sectors. -/
def programPT05BulkSpacetimeDensity
    (packet : ProgramPT05BulkActionLocalDensityPacket period hPeriod couplings) :
    C(EffectiveQuotient period hPeriod, Real) :=
  packet.einsteinHilbertDensity + packet.abelianBRSTDensity +
    packet.diffeomorphismBRSTDensity + packet.interactionDensity +
      packet.maxwellDensity

/-- Direct canonical sum of the five realized spacetime densities. -/
def programPT05CanonicalBulkSpacetimeDensity
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (input : PhysicalInput) : C(EffectiveQuotient period hPeriod, Real) :=
  programPT05BulkEinsteinHilbertDensity period hPeriod geometry frame couplings
      input +
    programPT05BulkAbelianBRSTDensity period hPeriod geometry frame input +
    programPT05BulkDiffeomorphismBRSTDensity period hPeriod geometry frame
      couplings input +
    programPT05BulkInteractionDensity period hPeriod geometry frame hRegular
      interactionScale coefficients input +
    programPT05BulkMaxwellDensity period hPeriod geometry frame couplings input

@[simp]
theorem programPT05CanonicalBulkActionLocalDensityPacket_spacetimeDensity
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (input : Input) :
    programPT05BulkSpacetimeDensity period hPeriod couplings
        (programPT05CanonicalBulkActionLocalDensityPacket period hPeriod
          geometry frame hRegular couplings interactionScale coefficients input) =
      programPT05CanonicalBulkSpacetimeDensity period hPeriod geometry frame
        hRegular couplings interactionScale coefficients input.1.1 := by
  rfl

/-- Existing graph action used to evaluate the explicitly non-density SpinC
frontier. -/
def programPT05BulkSpinCFrontierAction
    (frontier : ProgramPT05BulkSpinCLocalDensityFrontier period hPeriod
      couplings.matterMassSquared) : Real :=
  programPPrimitiveSpinCMatterGraphAction period hPeriod
    couplings.matterMassSquared frontier.graphState

/-- Mixed local/integrated evaluation: one canonical spacetime integral, the
existing SpinC graph action, and the Gate-826 throat integral. -/
def programPT05BulkActionLocalDensityEvaluation
    (packet : ProgramPT05BulkActionLocalDensityPacket period hPeriod couplings) :
    Real :=
  (finiteFrameBRSTCanonicalIntegralCLM period hPeriod
      (programPT05BulkSpacetimeDensity period hPeriod couplings packet) +
    programPT05BulkSpinCFrontierAction period hPeriod couplings
      packet.spinCFrontier) +
    programPT05LLDensityIntegral period hPeriod
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) packet.llDensity

/-- The canonical spacetime density integrates to the exact physical/Maxwell
summand used by the bulk action. -/
theorem programPT05CanonicalBulkSpacetimeDensityIntegral_eq_action
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (input : PhysicalInput) :
    finiteFrameBRSTCanonicalIntegralCLM period hPeriod
        (programPT05CanonicalBulkSpacetimeDensity period hPeriod geometry frame
          hRegular couplings interactionScale coefficients input) =
      finiteFramePairedC2PhysicalMaxwellAction period hPeriod geometry frame
        hRegular couplings interactionScale coefficients input := by
  simp only [programPT05CanonicalBulkSpacetimeDensity,
    programPT05BulkEinsteinHilbertDensity,
    programPT05BulkAbelianBRSTDensity,
    programPT05BulkDiffeomorphismBRSTDensity,
    programPT05BulkInteractionDensity, programPT05BulkMaxwellDensity,
    finiteFramePairedC2PhysicalMaxwellAction,
    finiteFramePairedC2PhysicalAction,
    finiteFramePairedC2EinsteinBRSTAction,
    finiteFramePairedC2EinsteinHilbertAction,
    finiteFrameC2EinsteinHilbertAction,
    finiteFramePairedC2FullBRSTGaugeAction,
    finiteFramePairedC2AbelianBRSTAction,
    finiteFrameC2AbelianBRSTAction,
    finiteFramePairedDiffeomorphismBRSTAction,
    finiteFrameC2DiffeomorphismBRSTAction,
    pairedFiniteFrameC2InteractionAction,
    finiteFramePairedC2MobileMaxwellAction,
    finiteFrameC2MobileMaxwellAction,
    map_add, map_smul, smul_eq_mul]
  ring

/-- The canonical mixed evaluation is exactly the existing bulk action used
before compatible-LL and boundary completion in T03. -/
theorem programPT05CanonicalBulkActionLocalDensityEvaluation_eq_action
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (input : Input) :
    programPT05BulkActionLocalDensityEvaluation period hPeriod couplings
        (programPT05CanonicalBulkActionLocalDensityPacket period hPeriod
          geometry frame hRegular couplings interactionScale coefficients input) =
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLAction period hPeriod
        geometry frame hRegular couplings interactionScale coefficients input := by
  rw [programPT05BulkActionLocalDensityEvaluation]
  change
    (finiteFrameBRSTCanonicalIntegralCLM period hPeriod
        (programPT05BulkSpacetimeDensity period hPeriod couplings
          (programPT05CanonicalBulkActionLocalDensityPacket period hPeriod
            geometry frame hRegular couplings interactionScale coefficients
              input)) +
      programPPrimitiveSpinCMatterGraphAction period hPeriod
        couplings.matterMassSquared input.1.2) +
      programPT05LLDensityIntegral period hPeriod
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
        (programPT05CanonicalPTLLLocalDensityCochain period hPeriod
          (canonicalDivergenceFreeLLFrame period hPeriod) input.2) = _
  rw [programPT05CanonicalBulkActionLocalDensityPacket_spacetimeDensity,
    programPT05CanonicalBulkSpacetimeDensityIntegral_eq_action period hPeriod
      geometry frame hRegular couplings interactionScale coefficients input.1.1,
    programPT05CanonicalPTLLDensityIntegral_eq_action]
  rfl

/-- Exact Gate-819 bulk-slot injection of the evaluated local-density packet. -/
def programPT05BulkActionIntegratedRelativeCochain
    (packet : ProgramPT05BulkActionLocalDensityPacket period hPeriod couplings) :
    RelativeJetCochain ProgramPT05PhysicalJetComponent 4 0
  | .bulk =>
      (programPT05BulkActionLocalDensityEvaluation period hPeriod couplings
        packet, 0)
  | .nonNullBoundary => 0
  | .nullBoundary => 0
  | .joint => 0

/-- On canonical data, the injected bulk coefficient is exactly the existing
physical/Maxwell/SpinC/LL action. -/
theorem programPT05CanonicalBulkActionIntegratedRelativeCochain_bulk_eq_action
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (input : Input) :
    programPT05BulkActionIntegratedRelativeCochain period hPeriod couplings
        (programPT05CanonicalBulkActionLocalDensityPacket period hPeriod
          geometry frame hRegular couplings interactionScale coefficients input)
          .bulk =
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLAction period hPeriod
        geometry frame hRegular couplings interactionScale coefficients input, 0) := by
  change
    (programPT05BulkActionLocalDensityEvaluation period hPeriod couplings
      (programPT05CanonicalBulkActionLocalDensityPacket period hPeriod geometry
        frame hRegular couplings interactionScale coefficients input), 0) = _
  rw [programPT05CanonicalBulkActionLocalDensityEvaluation_eq_action]

end
end P0EFTJanusProgramPT05BulkActionLocalDensityBridge4D
end JanusFormal
