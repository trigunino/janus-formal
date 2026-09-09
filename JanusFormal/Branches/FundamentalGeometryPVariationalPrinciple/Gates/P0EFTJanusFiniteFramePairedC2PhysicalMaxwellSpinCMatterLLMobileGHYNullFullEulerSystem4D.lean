import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullReparametrizationEuler4D

/-! # Full Euler system for the null-reparametrization product

This gate splits the Euler covector at an arbitrary admissible input into its
physical/Maxwell/SpinC, LL, independent GHY and null-normalization factors.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullFullEulerSystem4D

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
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDensity4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterRegularity4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzPositiveGHYDomain4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzPositiveGHYActionBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC24D
open P0EFTJanusNullJointReparametrizationCancellation
open P0EFTJanusFiniteNullFaceAction
open P0EFTJanusProgramPGlobalNullBoundaryReparametrizationHessian4D
open P0EFTJanusProgramPGlobalBoundaryReparametrizationHilbertHessian4D
open P0EFTJanusFiniteFramePairedC2PhysicalAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterCenterEuler4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCenterEuler4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYProductEuler4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYEulerSplit4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullReparametrizationAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullReparametrizationEuler4D
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

section

variable {NullFace : Type*} [Fintype NullFace]

local notation "NullInput" =>
  GlobalCandidateABoundaryReparametrizationHilbert NullFace

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

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

/-- At an arbitrary admissible LL input, stationarity splits into the prior
physical/Maxwell/SpinC Euler equation and the LL first-variation equation. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLEuler_eq_zero_iff_old_and_ll
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (input : BulkInput)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLDomain period hPeriod geometry
        frame hRegular couplings) :
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLEuler period hPeriod geometry
        frame hRegular couplings interactionScale coefficients input = 0 ↔
      finiteFramePairedC2PhysicalMaxwellSpinCMatterEuler period hPeriod geometry
          frame hRegular couplings interactionScale coefficients input.1 = 0 ∧
        fderiv Real
          (regularGeneralMetricC0LLPTAction period hPeriod
            (canonicalDivergenceFreeLLFrame period hPeriod)
            (intrinsicCanonicalThroatVolumeMeasure period hPeriod)) input.2 = 0 := by
  rw [finiteFramePairedC2PhysicalMaxwellSpinCMatterLLEuler_eq_old_add_ll period
    hPeriod geometry frame hRegular couplings interactionScale coefficients input
      hInput]
  constructor
  · intro hTotal
    constructor
    · apply ContinuousLinearMap.ext
      intro direction
      have hValue := congrArg
        (fun derivative : BulkInput →L[Real] Real =>
          derivative (direction, (0 : LLInput))) hTotal
      simpa using hValue
    · apply ContinuousLinearMap.ext
      intro direction
      have hValue := congrArg
        (fun derivative : BulkInput →L[Real] Real =>
          derivative ((0 : OldInput), direction)) hTotal
      simpa using hValue
  · rintro ⟨hOld, hLL⟩
    simp [hOld, hLL]

/-- At every admissible input, null-product stationarity is exactly the
physical/Maxwell/SpinC, LL and independent GHY Euler system. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullEuler_eq_zero_iff_full_system
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace : Type*} [Fintype NonNullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (contract : GlobalCandidateANullBoundaryReparametrizationIntegrability
      period hPeriod data)
    (einsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients)
    (hTransverse : HasNoTangentialRadical period hPeriod boundaryBase.metric)
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullDomain period
        hPeriod geometry frame hRegular couplings boundaryBase) :
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullEuler period
        hPeriod geometry frame hRegular couplings boundaryBase data einsteinScale
          interactionScale coefficients input = 0 ↔
      finiteFramePairedC2PhysicalMaxwellSpinCMatterEuler period hPeriod geometry
          frame hRegular couplings interactionScale coefficients input.1.1.1 = 0 ∧
        fderiv Real
          (regularGeneralMetricC0LLPTAction period hPeriod
            (canonicalDivergenceFreeLLFrame period hPeriod)
            (intrinsicCanonicalThroatVolumeMeasure period hPeriod)) input.1.1.2 = 0 ∧
        finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYBoundaryEuler
          period hPeriod boundaryBase einsteinScale input.1.2 = 0 := by
  rw [finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullEuler_eq_zero_iff_mobileGHY
    period hPeriod geometry frame hRegular couplings boundaryBase data contract
      einsteinScale interactionScale coefficients hTransverse input hInput]
  rw [finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYEuler_eq_zero_iff_bulk_and_ghy
    period hPeriod geometry frame hRegular couplings boundaryBase data
      einsteinScale interactionScale coefficients hTransverse input.1 hInput.1]
  rw [finiteFramePairedC2PhysicalMaxwellSpinCMatterLLEuler_eq_zero_iff_old_and_ll
    period hPeriod geometry frame hRegular couplings interactionScale coefficients
      input.1.1 hInput.1.1]
  constructor
  · rintro ⟨⟨hOld, hLL⟩, hGHY⟩
    exact ⟨hOld, hLL, hGHY⟩
  · rintro ⟨hOld, hLL, hGHY⟩
    exact ⟨⟨hOld, hLL⟩, hGHY⟩

end

end
end P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullFullEulerSystem4D
end JanusFormal
