import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYStationaryLLSystem4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalBoundaryReparametrizationHilbertHessian4D

/-! # Null-generator reparametrizations in the mobile GHY product

The finite mobile-GHY chart is enlarged by one independent normalization
parameter for every null face.  The bulk LL action, the completed mobile GHY
action and the reparametrized finite-null action each occur exactly once.

This only varies null-generator normalization.  It does not vary the location
or intrinsic geometry of a null face.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullReparametrizationAction4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 600000
noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff BigOperators InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalBoundaryCompletion4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDensity4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterRegularity4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzPositiveGHYDomain4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusNullJointReparametrizationCancellation
open P0EFTJanusFiniteNullFaceAction
open P0EFTJanusProgramPGlobalNullBoundaryReparametrizationHessian4D
open P0EFTJanusProgramPGlobalBoundaryReparametrizationHilbertHessian4D
open P0EFTJanusFiniteFramePairedC2PhysicalAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYProductEuler4D
open P0EFTJanusReciprocalBimetricPotential

attribute [local instance 2000]
  NonUnitalNormedRing.toNormedAddCommGroup NormedAlgebra.toNormedSpace

attribute [local instance 100]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance : IsManifold coverModelWithCorners ω
    (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance : IsManifold throatCoverModelWithCorners ω
    (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance : CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance : BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

local instance :
    IsFiniteMeasure (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod

local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup

local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance

local instance : CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

local instance : InnerProductSpace Real ProgramPPrimitiveSpinCMatterHilbert :=
  InnerProductSpace.complexToReal

variable (geometry : GlobalCandidateAGeometry period hPeriod)
  (frame : SmoothD8Frame period hPeriod)
  (hRegular : ∀ point, Function.Bijective
    (intrinsicCandidateASylvesterAt period hPeriod geometry point))
  (couplings : GlobalCandidateAActionCouplings)
  (boundaryBase : RegularGeneralLorentzMetric period hPeriod)

local notation "OldInput" =>
  FiniteFramePairedC2PhysicalMaxwellSpinCMatterCore period hPeriod geometry frame
    couplings

local notation "LLInput" =>
  GlobalMinimalPhysicalLLC0FirstJetPacket period hPeriod
    (canonicalDivergenceFreeLLFrame period hPeriod)

local notation "BulkInput" =>
  FiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCore period hPeriod geometry frame
    couplings

local notation "GHYCore" =>
  CandidateANormalBoundaryFunctionalCore period hPeriod boundaryBase

local notation "GHYInput" => Prod GHYCore Real

local notation "MobileInput" =>
  FiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYCore period hPeriod
    geometry frame couplings boundaryBase

/-- Add one independent real normalization parameter for each null face. -/
abbrev FiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullCore
    (NullFace : Type*) :=
  MobileInput × GlobalCandidateABoundaryReparametrizationHilbert NullFace

section

variable {NullFace : Type*} [Fintype NullFace]

local notation "Input" =>
  FiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullCore period hPeriod
    geometry frame couplings boundaryBase NullFace

local instance : NormedSpace Real OldInput := Prod.normedSpace
local instance : NormedSpace Real LLInput := Prod.normedSpace
local instance : NormedSpace Real BulkInput := Prod.normedSpace

local instance mobileGHYFunctionalCoreNormedAddCommGroup :
    NormedAddCommGroup GHYCore :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.candidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    period hPeriod boundaryBase

local instance mobileGHYFunctionalCoreNormedSpace :
    NormedSpace Real GHYCore :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.candidateANormalBoundaryFunctionalCoreNormedSpace
    period hPeriod boundaryBase

local instance : NormedSpace Real GHYInput := Prod.normedSpace

local instance mobileGHYInputSMul : SMul Real MobileInput := Prod.instSMul

local instance : ContinuousSMul Real LLInput := by
  apply Prod.continuousSMul

local instance : ContinuousSMul Real BulkInput := by
  apply Prod.continuousSMul

local instance : ContinuousSMul Real GHYInput := by
  apply Prod.continuousSMul

local instance : ContinuousSMul Real MobileInput := by
  apply Prod.continuousSMul

local instance : NormedSpace Real MobileInput := Prod.normedSpace

local instance nullReparametrizationInputSMul : SMul Real Input := Prod.instSMul

local instance : ContinuousSMul Real Input := by
  apply Prod.continuousSMul

local instance : NormedSpace Real Input := Prod.normedSpace

/-- Product of the mobile-GHY domain and the full finite-dimensional null
normalization space. -/
def finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullDomain
    : Set Input :=
  finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYDomain period hPeriod
      geometry frame hRegular couplings boundaryBase ×ˢ Set.univ

omit [Fintype NullFace] in
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullDomain_isOpen
    :
    IsOpen
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullDomain period
        hPeriod geometry frame hRegular couplings boundaryBase
          (NullFace := NullFace)) :=
  (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYDomain_isOpen period
    hPeriod geometry frame hRegular couplings boundaryBase).prod isOpen_univ

omit [Fintype NullFace] in
theorem zero_mem_finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullDomain
    (hMinusCenter : finiteFramePairedC2MinusCenter period hPeriod geometry frame ∈
      generalMetricRelativeC2VolumeDomain period hPeriod frame geometry.plusMetric)
    (hTransverse : HasNoTangentialRadical period hPeriod boundaryBase.metric) :
    (0 : Input) ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullDomain period
        hPeriod geometry frame hRegular couplings boundaryBase :=
  ⟨zero_mem_finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYDomain
    period hPeriod geometry frame hRegular couplings boundaryBase hMinusCenter
      hTransverse, Set.mem_univ _⟩

/-- The bulk LL action, mobile GHY action and facewise reparametrized null
action, with no repeated boundary summand. -/
def finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullAction
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace : Type*} [Fintype NonNullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients)
    (input : Input) : Real :=
  finiteFramePairedC2PhysicalMaxwellSpinCMatterLLAction period hPeriod geometry
      frame hRegular couplings interactionScale coefficients input.1.1 +
    candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation period hPeriod
      einsteinScale boundaryBase input.1.2 +
    ∑ face : NullFace,
      finiteNullFaceReparametrizationActionCurve
        (data.nullActionFaces face) (input.2 face)

/-- Under the supplied facewise integrability contract, the added null
coordinates leave the exact mobile-GHY action unchanged. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullAction_eq_mobileGHY
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace : Type*} [Fintype NonNullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (contract : GlobalCandidateANullBoundaryReparametrizationIntegrability
      period hPeriod data)
    (einsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients)
    (input : Input) :
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullAction period
        hPeriod geometry frame hRegular couplings boundaryBase data einsteinScale
          interactionScale coefficients input =
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYAction period
        hPeriod geometry frame hRegular couplings boundaryBase data einsteinScale
          interactionScale coefficients input.1 := by
  classical
  unfold finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullAction
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYAction
    globalCandidateANullBoundaryAction
  congr 1
  apply Finset.sum_congr rfl
  intro face _
  exact finiteNullFaceReparametrizationActionCurve_eq
    (data.nullActionFaces face) (contract.toInterval period hPeriod face)
      (input.2 face)

/-- The null-reparametrization product is `C²` on its exact open domain. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullAction_contDiffOn_two
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace : Type*} [Fintype NonNullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (contract : GlobalCandidateANullBoundaryReparametrizationIntegrability
      period hPeriod data)
    (einsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients)
    (hTransverse : HasNoTangentialRadical period hPeriod boundaryBase.metric) :
    ContDiffOn Real 2
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullAction period
        hPeriod geometry frame hRegular couplings boundaryBase data einsteinScale
          interactionScale coefficients)
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullDomain period
        hPeriod geometry frame hRegular couplings boundaryBase) := by
  rw [show
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullAction period
        hPeriod geometry frame hRegular couplings boundaryBase data einsteinScale
          interactionScale coefficients =
      fun input : Input =>
        finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYAction period
          hPeriod geometry frame hRegular couplings boundaryBase data einsteinScale
            interactionScale coefficients input.1 by
    funext input
    exact
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullAction_eq_mobileGHY
        period hPeriod geometry frame hRegular couplings boundaryBase data contract
          einsteinScale interactionScale coefficients input]
  exact
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYAction_contDiffOn_two
      period hPeriod geometry frame hRegular couplings boundaryBase data
        einsteinScale interactionScale coefficients hTransverse).comp
      contDiff_fst.contDiffOn (fun _ hInput => hInput.1)

end

end
end P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullReparametrizationAction4D
end JanusFormal
