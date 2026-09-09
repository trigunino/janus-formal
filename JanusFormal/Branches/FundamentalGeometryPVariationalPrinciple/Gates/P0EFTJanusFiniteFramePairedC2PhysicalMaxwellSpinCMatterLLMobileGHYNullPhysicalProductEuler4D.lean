import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullFullEulerSystem4D

/-! # Finite null-face physical coordinates and Euler product

The preceding null gate varies only the normalization of each supplied null
generator.  The repository currently has no Hilbert chart of null embeddings
or screen metrics.  This gate therefore introduces the smallest explicit
finite-mode surrogate needed to expose a separate physical null Euler block:

* one real transverse-position amplitude per null face;
* three real coefficients per face for a symmetric two-dimensional screen
  metric variation.

`FiniteNullFacePhysicalActionModel` packages an open domain and a `C²` action
on those coordinates.  The old bulk/Maxwell/SpinC/LL/GHY/normalization action
is extended by that physical action, and stationarity is proved equivalent to
the old Euler system together with the new null-physical Euler equation.

This is a typed finite-dimensional variational interface, not a construction
of a moving null hypersurface.  Closing that geometric gap still requires a
map from actual null embeddings and intrinsic screen metrics into this core,
plus an agreement theorem identifying the model action with the geometric
null face and joint action.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalProductEuler4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 600000
set_option maxRecDepth 2000
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
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYProductEuler4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYEulerSplit4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullReparametrizationAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullReparametrizationEuler4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullFullEulerSystem4D
open P0EFTJanusReciprocalBimetricPotential

attribute [local instance 2000]
  NonUnitalNormedRing.toNormedAddCommGroup NormedAlgebra.toNormedSpace

attribute [local instance 100]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

/-- One transverse-position amplitude for every supplied null face. -/
abbrev FiniteNullFacePositionHilbert
    (NullFace : Type*) [Fintype NullFace] :=
  EuclideanSpace Real NullFace

/-- Three coefficients per face, the finite coordinate count of a symmetric
bilinear form on a two-dimensional screen. -/
abbrev FiniteNullFaceIntrinsicMetricHilbert
    (NullFace : Type*) [Fintype NullFace] :=
  EuclideanSpace Real (NullFace × Fin 3)

/-- Explicit finite-mode physical null-face coordinate. -/
abbrev FiniteNullFacePhysicalHilbert
    (NullFace : Type*) [Fintype NullFace] :=
  FiniteNullFacePositionHilbert NullFace ×
    FiniteNullFaceIntrinsicMetricHilbert NullFace

/-- Local `C²` action germ on the finite null-face physical coordinates.
An actual geometric realization must later instantiate this structure. -/
structure FiniteNullFacePhysicalActionModel
    (NullFace : Type*) [Fintype NullFace] where
  domain : Set (FiniteNullFacePhysicalHilbert NullFace)
  action : FiniteNullFacePhysicalHilbert NullFace → Real
  domain_isOpen : IsOpen domain
  zero_mem_domain : (0 : FiniteNullFacePhysicalHilbert NullFace) ∈ domain
  action_zero : action 0 = 0
  action_contDiffOn_two : ContDiffOn Real 2 action domain

/-- A concrete linear source model.  It witnesses that the new factor need
not be annihilated as the normalization factor was. -/
def finiteNullFacePhysicalLinearAction
    {NullFace : Type*} [Fintype NullFace]
    (positionSource : FiniteNullFacePositionHilbert NullFace →L[Real] Real)
    (intrinsicSource :
      FiniteNullFaceIntrinsicMetricHilbert NullFace →L[Real] Real)
    (input : FiniteNullFacePhysicalHilbert NullFace) : Real :=
  positionSource input.1 + intrinsicSource input.2

/-- The everywhere-defined `C∞` model associated with two continuous linear
sources. -/
def finiteNullFacePhysicalLinearActionModel
    {NullFace : Type*} [Fintype NullFace]
    (positionSource : FiniteNullFacePositionHilbert NullFace →L[Real] Real)
    (intrinsicSource :
      FiniteNullFaceIntrinsicMetricHilbert NullFace →L[Real] Real) :
    FiniteNullFacePhysicalActionModel NullFace where
  domain := Set.univ
  action := finiteNullFacePhysicalLinearAction positionSource intrinsicSource
  domain_isOpen := isOpen_univ
  zero_mem_domain := Set.mem_univ _
  action_zero := by
    simp [finiteNullFacePhysicalLinearAction]
  action_contDiffOn_two := by
    exact
      ((positionSource.contDiff.comp contDiff_fst).add
        (intrinsicSource.contDiff.comp contDiff_snd)).contDiffOn

/-- Euler covector of the physical null-face action model. -/
def finiteNullFacePhysicalEuler
    {NullFace : Type*} [Fintype NullFace]
    (model : FiniteNullFacePhysicalActionModel NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) :
    FiniteNullFacePhysicalHilbert NullFace →L[Real] Real :=
  fderiv Real model.action input

/-- The position restriction of the null-face physical Euler covector. -/
def finiteNullFacePhysicalPositionEuler
    {NullFace : Type*} [Fintype NullFace]
    (model : FiniteNullFacePhysicalActionModel NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) :
    FiniteNullFacePositionHilbert NullFace →L[Real] Real :=
  (finiteNullFacePhysicalEuler model input).comp
    (ContinuousLinearMap.inl Real
      (FiniteNullFacePositionHilbert NullFace)
      (FiniteNullFaceIntrinsicMetricHilbert NullFace))

/-- The intrinsic-screen restriction of the null-face physical Euler
covector. -/
def finiteNullFacePhysicalIntrinsicEuler
    {NullFace : Type*} [Fintype NullFace]
    (model : FiniteNullFacePhysicalActionModel NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) :
    FiniteNullFaceIntrinsicMetricHilbert NullFace →L[Real] Real :=
  (finiteNullFacePhysicalEuler model input).comp
    (ContinuousLinearMap.inr Real
      (FiniteNullFacePositionHilbert NullFace)
      (FiniteNullFaceIntrinsicMetricHilbert NullFace))

/-- Null-physical stationarity is exactly stationarity in the independent
position and intrinsic-screen directions. -/
theorem finiteNullFacePhysicalEuler_eq_zero_iff_position_and_intrinsic
    {NullFace : Type*} [Fintype NullFace]
    (model : FiniteNullFacePhysicalActionModel NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) :
    finiteNullFacePhysicalEuler model input = 0 ↔
      finiteNullFacePhysicalPositionEuler model input = 0 ∧
        finiteNullFacePhysicalIntrinsicEuler model input = 0 := by
  constructor
  · intro hEuler
    constructor
    · apply ContinuousLinearMap.ext
      intro variation
      simp [finiteNullFacePhysicalPositionEuler, hEuler]
    · apply ContinuousLinearMap.ext
      intro variation
      simp [finiteNullFacePhysicalIntrinsicEuler, hEuler]
  · rintro ⟨hPosition, hIntrinsic⟩
    apply ContinuousLinearMap.ext
    intro variation
    have hSplit :
        variation = (variation.1, 0) + (0, variation.2) := by
      apply Prod.ext <;> simp
    rw [hSplit, map_add]
    have hPositionZero := DFunLike.congr_fun hPosition variation.1
    have hIntrinsicZero := DFunLike.congr_fun hIntrinsic variation.2
    simpa [finiteNullFacePhysicalPositionEuler,
      finiteNullFacePhysicalIntrinsicEuler] using
        congrArg₂ (· + ·) hPositionZero hIntrinsicZero

/-- Exact nonzero-capable Euler block of the explicit linear source model. -/
theorem finiteNullFacePhysicalEuler_linearActionModel
    {NullFace : Type*} [Fintype NullFace]
    (positionSource : FiniteNullFacePositionHilbert NullFace →L[Real] Real)
    (intrinsicSource :
      FiniteNullFaceIntrinsicMetricHilbert NullFace →L[Real] Real)
    (input : FiniteNullFacePhysicalHilbert NullFace) :
    finiteNullFacePhysicalEuler
        (finiteNullFacePhysicalLinearActionModel positionSource intrinsicSource)
        input =
      positionSource.comp
          (ContinuousLinearMap.fst Real
            (FiniteNullFacePositionHilbert NullFace)
            (FiniteNullFaceIntrinsicMetricHilbert NullFace)) +
        intrinsicSource.comp
          (ContinuousLinearMap.snd Real
            (FiniteNullFacePositionHilbert NullFace)
            (FiniteNullFaceIntrinsicMetricHilbert NullFace)) := by
  unfold finiteNullFacePhysicalEuler
  let source : FiniteNullFacePhysicalHilbert NullFace →L[Real] Real :=
    positionSource.comp
        (ContinuousLinearMap.fst Real
          (FiniteNullFacePositionHilbert NullFace)
          (FiniteNullFaceIntrinsicMetricHilbert NullFace)) +
      intrinsicSource.comp
        (ContinuousLinearMap.snd Real
          (FiniteNullFacePositionHilbert NullFace)
          (FiniteNullFaceIntrinsicMetricHilbert NullFace))
  have hAction :
      (finiteNullFacePhysicalLinearActionModel positionSource intrinsicSource).action =
        source := by
    funext current
    rfl
  rw [hAction]
  exact source.hasFDerivAt.fderiv

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

local notation "NullNormalization" =>
  GlobalCandidateABoundaryReparametrizationHilbert NullFace

local notation "PriorInput" =>
  FiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullCore period hPeriod
    geometry frame couplings boundaryBase NullFace

local notation "NullPhysical" => FiniteNullFacePhysicalHilbert NullFace

/-- The existing normalization product enlarged by independent physical
null-face coordinates. -/
abbrev FiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalCore :=
  PriorInput × NullPhysical

local notation "Input" =>
  FiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalCore
    period hPeriod geometry frame couplings boundaryBase (NullFace := NullFace)

local instance : NormedSpace Real OldInput := Prod.normedSpace
local instance : NormedSpace Real LLInput := Prod.normedSpace
local instance : NormedSpace Real BulkInput := Prod.normedSpace

local instance nullPhysicalGHYFunctionalCoreNormedAddCommGroup :
    NormedAddCommGroup GHYCore :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.candidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    period hPeriod boundaryBase

local instance nullPhysicalGHYFunctionalCoreNormedSpace :
    NormedSpace Real GHYCore :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.candidateANormalBoundaryFunctionalCoreNormedSpace
    period hPeriod boundaryBase

local instance : NormedSpace Real GHYInput := Prod.normedSpace
local instance mobileInputSMul : SMul Real MobileInput := Prod.instSMul

local instance : ContinuousSMul Real LLInput := by
  apply Prod.continuousSMul

local instance : ContinuousSMul Real BulkInput := by
  apply Prod.continuousSMul

local instance : ContinuousSMul Real GHYInput := by
  apply Prod.continuousSMul

local instance : ContinuousSMul Real MobileInput := by
  apply Prod.continuousSMul

local instance : NormedSpace Real MobileInput := Prod.normedSpace
local instance priorInputSMul : SMul Real PriorInput := Prod.instSMul

local instance : ContinuousSMul Real PriorInput := by
  apply Prod.continuousSMul

local instance : NormedSpace Real PriorInput := Prod.normedSpace
local instance nullPhysicalInputSMul : SMul Real Input := Prod.instSMul

local instance : ContinuousSMul Real Input := by
  apply Prod.continuousSMul

local instance : NormedSpace Real Input := Prod.normedSpace

/-- Product of the exact prior domain and the physical null model domain. -/
def finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalDomain
    (model : FiniteNullFacePhysicalActionModel NullFace) : Set Input :=
  finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullDomain period
      hPeriod geometry frame hRegular couplings boundaryBase ×ˢ
    model.domain

theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalDomain_isOpen
    (model : FiniteNullFacePhysicalActionModel NullFace) :
    IsOpen
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalDomain
        period hPeriod geometry frame hRegular couplings boundaryBase model) :=
  (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullDomain_isOpen
    period hPeriod geometry frame hRegular couplings boundaryBase).prod
      model.domain_isOpen

theorem zero_mem_finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalDomain
    (model : FiniteNullFacePhysicalActionModel NullFace)
    (hMinusCenter : finiteFramePairedC2MinusCenter period hPeriod geometry frame ∈
      generalMetricRelativeC2VolumeDomain period hPeriod frame geometry.plusMetric)
    (hTransverse : HasNoTangentialRadical period hPeriod boundaryBase.metric) :
    (0 : Input) ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalDomain
        period hPeriod geometry frame hRegular couplings boundaryBase model :=
  ⟨zero_mem_finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullDomain
    period hPeriod geometry frame hRegular couplings boundaryBase hMinusCenter
      hTransverse, model.zero_mem_domain⟩

/-- Prior bulk/boundary/normalization action plus the physical null action
germ.  The new summand is relative to the supplied fixed null-face value. -/
def finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalAction
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace : Type*} [Fintype NonNullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (_contract : GlobalCandidateANullBoundaryReparametrizationIntegrability
      period hPeriod data)
    (model : FiniteNullFacePhysicalActionModel NullFace)
    (einsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients)
    (input : Input) : Real :=
  finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullAction period
      hPeriod geometry frame hRegular couplings boundaryBase data einsteinScale
        interactionScale coefficients input.1 +
    model.action input.2

/-- At zero physical null coordinate, the extension recovers the exact prior
bulk/boundary/normalization action. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalAction_zero_physical
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace : Type*} [Fintype NonNullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (contract : GlobalCandidateANullBoundaryReparametrizationIntegrability
      period hPeriod data)
    (model : FiniteNullFacePhysicalActionModel NullFace)
    (einsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients)
    (input : PriorInput) :
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalAction
        period hPeriod geometry frame hRegular couplings boundaryBase data
          contract model einsteinScale interactionScale coefficients (input, 0) =
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullAction period
        hPeriod geometry frame hRegular couplings boundaryBase data einsteinScale
          interactionScale coefficients input := by
  simp [finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalAction,
    model.action_zero]

/-- The extended action is `C²` on the exact product domain. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalAction_contDiffOn_two
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace : Type*} [Fintype NonNullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (contract : GlobalCandidateANullBoundaryReparametrizationIntegrability
      period hPeriod data)
    (model : FiniteNullFacePhysicalActionModel NullFace)
    (einsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients)
    (hTransverse : HasNoTangentialRadical period hPeriod boundaryBase.metric) :
    ContDiffOn Real 2
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalAction
        period hPeriod geometry frame hRegular couplings boundaryBase data
          contract model einsteinScale interactionScale coefficients)
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalDomain
        period hPeriod geometry frame hRegular couplings boundaryBase model) := by
  have hPrior : ContDiffOn Real 2
      (fun input : Input =>
        finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullAction period
          hPeriod geometry frame hRegular couplings boundaryBase data
            einsteinScale interactionScale coefficients input.1)
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalDomain
        period hPeriod geometry frame hRegular couplings boundaryBase model) :=
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullAction_contDiffOn_two
      period hPeriod geometry frame hRegular couplings boundaryBase data contract
        einsteinScale interactionScale coefficients hTransverse).comp
      contDiff_fst.contDiffOn (fun _ hInput => hInput.1)
  have hNull : ContDiffOn Real 2
      (fun input : Input => model.action input.2)
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalDomain
        period hPeriod geometry frame hRegular couplings boundaryBase model) :=
    model.action_contDiffOn_two.comp contDiff_snd.contDiffOn
      (fun _ hInput => hInput.2)
  exact hPrior.add hNull

/-- Euler covector of the full product with physical null coordinates. -/
def finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalEuler
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace : Type*} [Fintype NonNullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (contract : GlobalCandidateANullBoundaryReparametrizationIntegrability
      period hPeriod data)
    (model : FiniteNullFacePhysicalActionModel NullFace)
    (einsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients)
    (input : Input) : Input →L[Real] Real :=
  fderiv Real
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalAction
      period hPeriod geometry frame hRegular couplings boundaryBase data contract
        model einsteinScale interactionScale coefficients) input

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalAction_hasFDerivAt
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace : Type*} [Fintype NonNullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (contract : GlobalCandidateANullBoundaryReparametrizationIntegrability
      period hPeriod data)
    (model : FiniteNullFacePhysicalActionModel NullFace)
    (einsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients)
    (hTransverse : HasNoTangentialRadical period hPeriod boundaryBase.metric)
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalDomain
        period hPeriod geometry frame hRegular couplings boundaryBase model) :
    HasFDerivAt
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalAction
        period hPeriod geometry frame hRegular couplings boundaryBase data
          contract model einsteinScale interactionScale coefficients)
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalEuler
        period hPeriod geometry frame hRegular couplings boundaryBase data
          contract model einsteinScale interactionScale coefficients input)
      input := by
  unfold
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalEuler
  exact
    (((finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalAction_contDiffOn_two
      period hPeriod geometry frame hRegular couplings boundaryBase data contract
        model einsteinScale interactionScale coefficients hTransverse).contDiffAt
      ((finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalDomain_isOpen
        period hPeriod geometry frame hRegular couplings boundaryBase model).mem_nhds
          hInput)).differentiableAt (by norm_num)).hasFDerivAt

/-- At each admissible point the total Euler covector is the direct sum of the
prior Euler covector and the new physical null Euler covector. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalEuler_eq_prior_add_null
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace : Type*} [Fintype NonNullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (contract : GlobalCandidateANullBoundaryReparametrizationIntegrability
      period hPeriod data)
    (model : FiniteNullFacePhysicalActionModel NullFace)
    (einsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients)
    (hTransverse : HasNoTangentialRadical period hPeriod boundaryBase.metric)
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalDomain
        period hPeriod geometry frame hRegular couplings boundaryBase model) :
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalEuler
        period hPeriod geometry frame hRegular couplings boundaryBase data
          contract model einsteinScale interactionScale coefficients input =
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullEuler period
        hPeriod geometry frame hRegular couplings boundaryBase data einsteinScale
          interactionScale coefficients input.1).comp
        (ContinuousLinearMap.fst Real PriorInput NullPhysical) +
      (finiteNullFacePhysicalEuler model input.2).comp
        (ContinuousLinearMap.snd Real PriorInput NullPhysical) := by
  have hFst : HasFDerivAt (fun current : Input => current.1)
      (ContinuousLinearMap.fst Real PriorInput NullPhysical) input := by
    fun_prop
  have hSnd : HasFDerivAt (fun current : Input => current.2)
      (ContinuousLinearMap.snd Real PriorInput NullPhysical) input := by
    fun_prop
  have hPriorBase :
      HasFDerivAt
        (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullAction period
          hPeriod geometry frame hRegular couplings boundaryBase data einsteinScale
            interactionScale coefficients)
        (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullEuler period
          hPeriod geometry frame hRegular couplings boundaryBase data einsteinScale
            interactionScale coefficients input.1)
        input.1 := by
    unfold finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullEuler
    exact
      (((finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullAction_contDiffOn_two
        period hPeriod geometry frame hRegular couplings boundaryBase data contract
          einsteinScale interactionScale coefficients hTransverse).contDiffAt
        ((finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullDomain_isOpen
          period hPeriod geometry frame hRegular couplings boundaryBase).mem_nhds
            hInput.1)).differentiableAt (by norm_num)).hasFDerivAt
  have hPrior := hPriorBase.comp input hFst
  have hNullBase : HasFDerivAt model.action
      (finiteNullFacePhysicalEuler model input.2) input.2 := by
    unfold finiteNullFacePhysicalEuler
    exact
      (((model.action_contDiffOn_two.contDiffAt
        (model.domain_isOpen.mem_nhds hInput.2)).differentiableAt
          (by norm_num)).hasFDerivAt)
  have hNull := hNullBase.comp input hSnd
  exact
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalAction_hasFDerivAt
      period hPeriod geometry frame hRegular couplings boundaryBase data contract
        model einsteinScale interactionScale coefficients hTransverse input
          hInput).unique (hPrior.add hNull)

/-- A pure physical null direction is evaluated by the physical null Euler
block, rather than being annihilated like a normalization direction. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalEuler_apply_pure_null
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace : Type*} [Fintype NonNullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (contract : GlobalCandidateANullBoundaryReparametrizationIntegrability
      period hPeriod data)
    (model : FiniteNullFacePhysicalActionModel NullFace)
    (einsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients)
    (hTransverse : HasNoTangentialRadical period hPeriod boundaryBase.metric)
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalDomain
        period hPeriod geometry frame hRegular couplings boundaryBase model)
    (direction : NullPhysical) :
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalEuler
        period hPeriod geometry frame hRegular couplings boundaryBase data
          contract model einsteinScale interactionScale coefficients input
          ((0 : PriorInput), direction) =
      finiteNullFacePhysicalEuler model input.2 direction := by
  rw [finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalEuler_eq_prior_add_null
    period hPeriod geometry frame hRegular couplings boundaryBase data contract
      model einsteinScale interactionScale coefficients hTransverse input hInput]
  simp

/-- Product stationarity is exactly prior stationarity together with the
physical null-face Euler equation. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalEuler_eq_zero_iff_prior_and_null
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace : Type*} [Fintype NonNullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (contract : GlobalCandidateANullBoundaryReparametrizationIntegrability
      period hPeriod data)
    (model : FiniteNullFacePhysicalActionModel NullFace)
    (einsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients)
    (hTransverse : HasNoTangentialRadical period hPeriod boundaryBase.metric)
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalDomain
        period hPeriod geometry frame hRegular couplings boundaryBase model) :
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalEuler
        period hPeriod geometry frame hRegular couplings boundaryBase data
          contract model einsteinScale interactionScale coefficients input = 0 ↔
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullEuler period
          hPeriod geometry frame hRegular couplings boundaryBase data
            einsteinScale interactionScale coefficients input.1 = 0 ∧
        finiteNullFacePhysicalEuler model input.2 = 0 := by
  rw [finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalEuler_eq_prior_add_null
    period hPeriod geometry frame hRegular couplings boundaryBase data contract
      model einsteinScale interactionScale coefficients hTransverse input hInput]
  constructor
  · intro hTotal
    constructor
    · apply ContinuousLinearMap.ext
      intro direction
      have hValue := congrArg
        (fun derivative : Input →L[Real] Real =>
          derivative (direction, (0 : NullPhysical))) hTotal
      simpa using hValue
    · apply ContinuousLinearMap.ext
      intro direction
      have hValue := congrArg
        (fun derivative : Input →L[Real] Real =>
          derivative ((0 : PriorInput), direction)) hTotal
      simpa using hValue
  · rintro ⟨hPrior, hNull⟩
    simp [hPrior, hNull]

/-- Combined arbitrary-input Euler system, now including a physical null-face
equation in addition to the physical/Maxwell/SpinC, LL and GHY equations. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalEuler_eq_zero_iff_full_system
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace : Type*} [Fintype NonNullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (contract : GlobalCandidateANullBoundaryReparametrizationIntegrability
      period hPeriod data)
    (model : FiniteNullFacePhysicalActionModel NullFace)
    (einsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients)
    (hTransverse : HasNoTangentialRadical period hPeriod boundaryBase.metric)
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalDomain
        period hPeriod geometry frame hRegular couplings boundaryBase model) :
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalEuler
        period hPeriod geometry frame hRegular couplings boundaryBase data
          contract model einsteinScale interactionScale coefficients input = 0 ↔
      finiteFramePairedC2PhysicalMaxwellSpinCMatterEuler period hPeriod geometry
          frame hRegular couplings interactionScale coefficients input.1.1.1.1 = 0 ∧
        fderiv Real
          (regularGeneralMetricC0LLPTAction period hPeriod
            (canonicalDivergenceFreeLLFrame period hPeriod)
            (intrinsicCanonicalThroatVolumeMeasure period hPeriod))
              input.1.1.1.2 = 0 ∧
        finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYBoundaryEuler
          period hPeriod boundaryBase einsteinScale input.1.1.2 = 0 ∧
        finiteNullFacePhysicalEuler model input.2 = 0 := by
  rw [finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalEuler_eq_zero_iff_prior_and_null
    period hPeriod geometry frame hRegular couplings boundaryBase data contract
      model einsteinScale interactionScale coefficients hTransverse input hInput]
  rw [finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullEuler_eq_zero_iff_full_system
    period hPeriod geometry frame hRegular couplings boundaryBase data contract
      einsteinScale interactionScale coefficients hTransverse input.1 hInput.1]
  constructor
  · rintro ⟨⟨hPhysical, hLL, hGHY⟩, hNull⟩
    exact ⟨hPhysical, hLL, hGHY, hNull⟩
  · rintro ⟨hPhysical, hLL, hGHY, hNull⟩
    exact ⟨⟨hPhysical, hLL, hGHY⟩, hNull⟩

end

end
end P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalProductEuler4D
end JanusFormal
