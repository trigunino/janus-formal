import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLSmoothSpinCEuler4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzPositiveGHYActionBridge4D

/-! # Independent mobile GHY product for the finite physical action

The completed mobile two-sheet GHY current is added as an independent product
coordinate.  The bulk action is the unfrozen LL action, so the GHY value is
present exactly once; the finite null-face data remain fixed.  Coupling this
boundary current to the two finite-frame metric coordinates is a later gate.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYProductEuler4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 600000
noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusGlobalGeneralMetricDeDonder4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalBoundaryCompletion4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusReciprocalBimetricPotential
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDensity4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterRegularity4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartGeometry4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalRelativeMetricCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomainOpen4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC24D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC3MetricCore4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzGHYDomain4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzPositiveGHYDomain4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzPositiveGHYActionBridge4D
open P0EFTJanusFiniteFramePairedC2PhysicalAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D

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
  FiniteFramePairedC2PhysicalMaxwellSpinCMatterCore period hPeriod geometry frame couplings

local notation "LLInput" =>
  GlobalMinimalPhysicalLLC0FirstJetPacket period hPeriod
    (canonicalDivergenceFreeLLFrame period hPeriod)

local notation "BulkInput" =>
  FiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCore period hPeriod geometry frame couplings

local notation "GHYCore" =>
  CandidateANormalBoundaryFunctionalCore period hPeriod boundaryBase

local notation "GHYInput" => Prod GHYCore Real

/-- The finite bulk/LL coordinate and the completed mobile GHY coordinate are
independent factors at this stage. -/
abbrev FiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYCore :=
  BulkInput × GHYInput

local notation "Input" =>
  FiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYCore period hPeriod
    geometry frame couplings boundaryBase

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

local instance mobileGHYInputSMul : SMul Real Input := Prod.instSMul

local instance : ContinuousSMul Real LLInput := by
  apply Prod.continuousSMul

local instance : ContinuousSMul Real BulkInput := by
  apply Prod.continuousSMul

local instance : ContinuousSMul Real GHYInput := by
  apply Prod.continuousSMul

local instance : ContinuousSMul Real Input := by
  apply Prod.continuousSMul

local instance : NormedSpace Real Input := Prod.normedSpace

/-- Product of the finite physical LL domain and the positive mobile GHY
domain.  It imposes no compatibility equation between the two factors. -/
def finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYDomain : Set Input :=
  finiteFramePairedC2PhysicalMaxwellSpinCMatterLLDomain period hPeriod geometry
      frame hRegular couplings ×ˢ
    candidateANormalBoundaryLorentzPositiveGHYDomain period hPeriod
      boundaryBase

theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYDomain_isOpen :
    IsOpen
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYDomain period
        hPeriod geometry frame hRegular couplings boundaryBase) :=
  (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLDomain_isOpen period hPeriod
      geometry frame hRegular couplings).prod
    (candidateANormalBoundaryLorentzPositiveGHYDomain_isOpen period hPeriod
      boundaryBase)

theorem zero_mem_finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYDomain
    (hMinusCenter : finiteFramePairedC2MinusCenter period hPeriod geometry frame ∈
      generalMetricRelativeC2VolumeDomain period hPeriod frame geometry.plusMetric)
    (hTransverse : HasNoTangentialRadical period hPeriod
      boundaryBase.metric) :
    (0 : Input) ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYDomain period
        hPeriod geometry frame hRegular couplings boundaryBase := by
  exact ⟨
    zero_mem_finiteFramePairedC2PhysicalMaxwellSpinCMatterLLDomain period hPeriod
      geometry frame hRegular couplings hMinusCenter,
    zero_mem_candidateANormalBoundaryLorentzPositiveGHYDomain period hPeriod
      boundaryBase hTransverse⟩

/-- Finite physical/Maxwell/SpinC/LL action plus one genuinely mobile GHY
factor and the still-fixed Candidate-A null-boundary value. -/
def finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYAction
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients)
    (input : Input) : Real :=
  finiteFramePairedC2PhysicalMaxwellSpinCMatterLLAction period hPeriod geometry
      frame hRegular couplings interactionScale coefficients input.1 +
    candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation period hPeriod
      einsteinScale boundaryBase input.2 +
    globalCandidateANullBoundaryAction period hPeriod data

/-- The independent mobile-GHY product action is `C²` on its exact positive
product domain. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYAction_contDiffOn_two
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients)
    (hTransverse : HasNoTangentialRadical period hPeriod
      boundaryBase.metric) :
    ContDiffOn Real 2
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYAction period
        hPeriod geometry frame hRegular couplings boundaryBase data einsteinScale
          interactionScale coefficients)
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYDomain period
        hPeriod geometry frame hRegular couplings boundaryBase) := by
  have hBulk : ContDiffOn Real 2
      (fun input : Input =>
        finiteFramePairedC2PhysicalMaxwellSpinCMatterLLAction period hPeriod
          geometry frame hRegular couplings interactionScale coefficients
            input.1)
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYDomain period
        hPeriod geometry frame hRegular couplings boundaryBase) :=
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLAction_contDiffOn_two period
      hPeriod geometry frame hRegular couplings interactionScale coefficients).comp
        contDiff_fst.contDiffOn (fun _ hInput => hInput.1)
  have hGHYBase : ContDiffOn Real 2
      (candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation period hPeriod
        einsteinScale boundaryBase)
      (candidateANormalBoundaryLorentzPositiveGHYDomain period hPeriod
        boundaryBase) :=
    (candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation_contDiffOn_two
      period hPeriod einsteinScale boundaryBase hTransverse).mono (by
        intro current hCurrent
        exact candidateANormalBoundaryLorentzPositiveGHYDomain_mem_ghy period
          hPeriod boundaryBase hCurrent)
  have hGHY : ContDiffOn Real 2
      (fun input : Input =>
        candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation period hPeriod
          einsteinScale boundaryBase input.2)
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYDomain period
        hPeriod geometry frame hRegular couplings boundaryBase) :=
    hGHYBase.comp contDiff_snd.contDiffOn (fun _ hInput => hInput.2)
  unfold finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYAction
  exact (hBulk.add hGHY).add contDiffOn_const

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

/-- Euler covector of the independent completed GHY factor. -/
def finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYBoundaryEuler
    (einsteinScale : Real) (current : GHYInput) : GHYInput →L[Real] Real :=
  fderiv Real
    (candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation period hPeriod
      einsteinScale boundaryBase) current

/-- Euler covector of the full independent mobile-GHY product action. -/
def finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYEuler
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients)
    (input : Input) : Input →L[Real] Real :=
  fderiv Real
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYAction period
      hPeriod geometry frame hRegular couplings boundaryBase data einsteinScale
        interactionScale coefficients) input

end
end P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYProductEuler4D
end JanusFormal
