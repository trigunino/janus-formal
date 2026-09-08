import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYProductEuler4D

/-! # Euler split for the independent mobile GHY product -/

namespace JanusFormal
namespace P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYEulerSplit4D

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
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusReciprocalBimetricPotential
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDensity4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterRegularity4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzPositiveGHYDomain4D
open P0EFTJanusFiniteFramePairedC2PhysicalAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYProductEuler4D

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

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

/-- The `C²` action differentiates to its declared Euler covector at every
point of the positive product domain. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYAction_hasFDerivAt
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients)
    (hTransverse : HasNoTangentialRadical period hPeriod
      boundaryBase.metric)
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYDomain period
        hPeriod geometry frame hRegular couplings boundaryBase) :
    HasFDerivAt
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYAction period
        hPeriod geometry frame hRegular couplings boundaryBase data einsteinScale
          interactionScale coefficients)
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYEuler period
        hPeriod geometry frame hRegular couplings boundaryBase data einsteinScale
          interactionScale coefficients input)
      input := by
  unfold finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYEuler
  exact
    (((finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYAction_contDiffOn_two
      period hPeriod geometry frame hRegular couplings boundaryBase data
        einsteinScale interactionScale coefficients hTransverse).contDiffAt
      ((finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYDomain_isOpen
        period hPeriod geometry frame hRegular couplings boundaryBase).mem_nhds hInput)
      ).differentiableAt (by norm_num)).hasFDerivAt

/-- At every admissible point the total Euler covector is the sum of the bulk
and independent GHY covectors pulled back by the product projections. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYEuler_eq_bulk_add_ghy
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients)
    (hTransverse : HasNoTangentialRadical period hPeriod
      boundaryBase.metric)
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYDomain period
        hPeriod geometry frame hRegular couplings boundaryBase) :
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYEuler period hPeriod
        geometry frame hRegular couplings boundaryBase data einsteinScale
          interactionScale coefficients input =
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLEuler period hPeriod
        geometry frame hRegular couplings interactionScale coefficients
          input.1).comp
        (ContinuousLinearMap.fst Real BulkInput GHYInput) +
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYBoundaryEuler
        period hPeriod boundaryBase einsteinScale input.2).comp
        (ContinuousLinearMap.snd Real BulkInput GHYInput) := by
  have hFst : HasFDerivAt (fun current : Input => current.1)
      (ContinuousLinearMap.fst Real BulkInput GHYInput) input := by
    fun_prop
  have hSnd : HasFDerivAt (fun current : Input => current.2)
      (ContinuousLinearMap.snd Real BulkInput GHYInput) input := by
    fun_prop
  have hBulk :=
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLAction_hasFDerivAt period
      hPeriod geometry frame hRegular couplings interactionScale coefficients
        input.1 hInput.1).comp input hFst
  have hGHYPositive : ContDiffOn Real 2
      (candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation period hPeriod
        einsteinScale boundaryBase)
      (candidateANormalBoundaryLorentzPositiveGHYDomain period hPeriod
        boundaryBase) :=
    (candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation_contDiffOn_two
      period hPeriod einsteinScale boundaryBase hTransverse).mono (by
        intro current hCurrent
        exact candidateANormalBoundaryLorentzPositiveGHYDomain_mem_ghy period
          hPeriod boundaryBase hCurrent)
  have hGHYBase : HasFDerivAt
      (candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation period hPeriod
        einsteinScale boundaryBase)
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYBoundaryEuler
        period hPeriod boundaryBase einsteinScale input.2)
      input.2 := by
    unfold
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYBoundaryEuler
    exact
      (((hGHYPositive.contDiffAt
        ((candidateANormalBoundaryLorentzPositiveGHYDomain_isOpen period
          hPeriod boundaryBase).mem_nhds hInput.2)
        ).differentiableAt (by norm_num)).hasFDerivAt)
  have hGHY := hGHYBase.comp input hSnd
  exact
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYAction_hasFDerivAt
      period hPeriod geometry frame hRegular couplings boundaryBase data
        einsteinScale interactionScale coefficients hTransverse input hInput).unique
      ((hBulk.add hGHY).add_const
        (globalCandidateANullBoundaryAction period hPeriod data))

/-- Independence of the two factors makes total stationarity equivalent to
separate bulk and GHY stationarity. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYEuler_eq_zero_iff_bulk_and_ghy
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients)
    (hTransverse : HasNoTangentialRadical period hPeriod
      boundaryBase.metric)
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYDomain period
        hPeriod geometry frame hRegular couplings boundaryBase) :
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYEuler period hPeriod
        geometry frame hRegular couplings boundaryBase data einsteinScale
          interactionScale coefficients input = 0 ↔
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLEuler period hPeriod
          geometry frame hRegular couplings interactionScale coefficients
            input.1 = 0 ∧
        finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYBoundaryEuler
          period hPeriod boundaryBase einsteinScale input.2 = 0 := by
  rw [finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYEuler_eq_bulk_add_ghy
    period hPeriod geometry frame hRegular couplings boundaryBase data
      einsteinScale interactionScale coefficients hTransverse input hInput]
  constructor
  · intro hTotal
    constructor
    · apply ContinuousLinearMap.ext
      intro direction
      have hValue := congrArg
        (fun derivative : Input →L[Real] Real =>
          derivative (direction, (0 : GHYInput))) hTotal
      simpa using hValue
    · apply ContinuousLinearMap.ext
      intro direction
      have hValue := congrArg
        (fun derivative : Input →L[Real] Real =>
          derivative ((0 : BulkInput), direction)) hTotal
      simpa using hValue
  · rintro ⟨hBulk, hGHY⟩
    simp [hBulk, hGHY]

end
end P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYEulerSplit4D
end JanusFormal
