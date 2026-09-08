import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullReparametrizationAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYSmoothBridge4D

/-! # Euler split for null-generator reparametrizations

Only the independent normalization parameters of the existing null generators
are varied.  Null-face position and intrinsic geometry remain fixed.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullReparametrizationEuler4D

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
open P0EFTJanusNullJointReparametrizationCancellation
open P0EFTJanusFiniteNullFaceAction
open P0EFTJanusProgramPGlobalNullBoundaryReparametrizationHessian4D
open P0EFTJanusProgramPGlobalBoundaryReparametrizationHilbertHessian4D
open P0EFTJanusFiniteFramePairedC2PhysicalAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYProductEuler4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYEulerSplit4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYSmoothBridge4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullReparametrizationAction4D
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

/-- Euler covector of the product enlarged only by null-generator
normalization parameters. -/
def finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullEuler
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace : Type*} [Fintype NonNullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients)
    (input : Input) : Input →L[Real] Real :=
  fderiv Real
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullAction period
      hPeriod geometry frame hRegular couplings boundaryBase data einsteinScale
        interactionScale coefficients) input

/-- The null-generator normalization factor contributes no Euler term: the
enlarged Euler covector is the Gate790 Euler pulled back by `fst`. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullEuler_eq_mobileGHY_comp_fst
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
          interactionScale coefficients input =
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYEuler period
        hPeriod geometry frame hRegular couplings boundaryBase data einsteinScale
          interactionScale coefficients input.1).comp
        (ContinuousLinearMap.fst Real MobileInput NullInput) := by
  have hFst : HasFDerivAt (fun current : Input => current.1)
      (ContinuousLinearMap.fst Real MobileInput NullInput) input := by
    fun_prop
  have hComposite :=
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYAction_hasFDerivAt
      period hPeriod geometry frame hRegular couplings boundaryBase data
        einsteinScale interactionScale coefficients hTransverse input.1
          hInput.1).comp input hFst
  have hAction :
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullAction period
          hPeriod geometry frame hRegular couplings boundaryBase data einsteinScale
            interactionScale coefficients =
        fun current : Input =>
          finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYAction period
            hPeriod geometry frame hRegular couplings boundaryBase data einsteinScale
              interactionScale coefficients current.1 := by
    funext current
    exact
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullAction_eq_mobileGHY
        period hPeriod geometry frame hRegular couplings boundaryBase data contract
          einsteinScale interactionScale coefficients current
  unfold finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullEuler
  rw [hAction]
  exact hComposite.fderiv

/-- Every pure null-generator normalization direction is annihilated.  No
null-face location or intrinsic-geometry direction is asserted here. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullEuler_apply_pure_null_eq_zero
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
        hPeriod geometry frame hRegular couplings boundaryBase)
    (direction : NullInput) :
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullEuler period
        hPeriod geometry frame hRegular couplings boundaryBase data einsteinScale
          interactionScale coefficients input
          (((0 : BulkInput), (0 : GHYInput)), direction) = 0 := by
  rw [finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullEuler_eq_mobileGHY_comp_fst
    period hPeriod geometry frame hRegular couplings boundaryBase data contract
      einsteinScale interactionScale coefficients hTransverse input hInput]
  let zeroDirection : MobileInput := ((0 : BulkInput), (0 : GHYInput))
  let euler : MobileInput →L[Real] Real :=
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYEuler period hPeriod
      geometry frame hRegular couplings boundaryBase data einsteinScale
        interactionScale coefficients input.1
  change euler zeroDirection = 0
  have hAdd := euler.map_add zeroDirection zeroDirection
  have hId : euler zeroDirection = euler zeroDirection + euler zeroDirection := by
    simpa [zeroDirection] using hAdd
  linarith

/-- Total stationarity in the generator-normalization product is equivalent
to stationarity of the Gate790 mobile-GHY factor. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullEuler_eq_zero_iff_mobileGHY
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
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYEuler period hPeriod
        geometry frame hRegular couplings boundaryBase data einsteinScale
          interactionScale coefficients input.1 = 0 := by
  rw [finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullEuler_eq_mobileGHY_comp_fst
    period hPeriod geometry frame hRegular couplings boundaryBase data contract
      einsteinScale interactionScale coefficients hTransverse input hInput]
  constructor
  · intro hTotal
    apply ContinuousLinearMap.ext
    intro direction
    have hValue := congrArg
      (fun derivative : Input →L[Real] Real =>
        derivative (direction, (0 : NullInput))) hTotal
    simpa using hValue
  · intro hMobile
    simp [hMobile]

/-- Smooth non-null boundary data retain the exact Candidate-A GHY value for
every allowed null-generator normalization. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullAction_smooth_ghy
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace : Type*} [Fintype NonNullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (contract : GlobalCandidateANullBoundaryReparametrizationIntegrability
      period hPeriod data)
    (einsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients)
    (bulkInput : BulkInput)
    (hTransverse : HasNoTangentialRadical period hPeriod boundaryBase.metric)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hCurrent :
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod
          boundaryBase (tensor, displacement), parameter) ∈
        candidateANormalBoundaryLorentzPositiveGHYDomain period hPeriod
          boundaryBase)
    (normalization : NullInput) :
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullAction period
        hPeriod geometry frame hRegular couplings boundaryBase data einsteinScale
          interactionScale coefficients
          ((bulkInput,
            (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod
              boundaryBase (tensor, displacement), parameter)), normalization) =
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLAction period hPeriod
          geometry frame hRegular couplings interactionScale coefficients
            bulkInput +
        globalCandidateAGHYAction period hPeriod
          (candidateANormalBoundaryLorentzPositiveGHYActionData period hPeriod
            data einsteinScale boundaryBase tensor displacement parameter
              hCurrent) +
        globalCandidateANullBoundaryAction period hPeriod data := by
  rw [finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullAction_eq_mobileGHY
    period hPeriod geometry frame hRegular couplings boundaryBase data contract
      einsteinScale interactionScale coefficients]
  exact
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYAction_smooth_ghy
      period hPeriod geometry frame hRegular couplings boundaryBase data
        einsteinScale interactionScale coefficients bulkInput hTransverse tensor
          displacement parameter hCurrent

end

end
end P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullReparametrizationEuler4D
end JanusFormal
