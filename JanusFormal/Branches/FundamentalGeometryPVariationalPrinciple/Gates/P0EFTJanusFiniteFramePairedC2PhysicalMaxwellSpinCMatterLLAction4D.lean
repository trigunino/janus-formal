import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterCenterEuler4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC24D

/-! # Genuine LL augmentation of the finite physical action -/

namespace JanusFormal
namespace P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 600000
noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalBoundaryCompletion4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDensity4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterRegularity4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC24D
open P0EFTJanusFiniteFramePairedC2PhysicalAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterAction4D
open P0EFTJanusMatrixSquareRootInteractionDensity
open P0EFTJanusReciprocalBimetricPotential

attribute [local instance 2000]
  NonUnitalNormedRing.toNormedAddCommGroup NormedAlgebra.toNormedSpace

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

local notation "OldInput" =>
  FiniteFramePairedC2PhysicalMaxwellSpinCMatterCore period hPeriod geometry frame couplings

local notation "LLInput" =>
  GlobalMinimalPhysicalLLC0FirstJetPacket period hPeriod
    (canonicalDivergenceFreeLLFrame period hPeriod)

local instance : NormedSpace Real OldInput := Prod.normedSpace

/-- Add the complete direct/PT LL first-jet packet to the finite chart. -/
abbrev FiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCore :=
  OldInput × LLInput

local notation "Input" =>
  FiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCore period hPeriod geometry frame couplings

local instance : NormedSpace Real Input := Prod.normedSpace

def finiteFramePairedC2PhysicalMaxwellSpinCMatterLLDomain : Set Input :=
  finiteFramePairedC2PhysicalMaxwellSpinCMatterDomain period hPeriod geometry frame
      hRegular couplings ×ˢ Set.univ

theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLDomain_isOpen :
    IsOpen (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLDomain period hPeriod
      geometry frame hRegular couplings) :=
  (finiteFramePairedC2PhysicalMaxwellSpinCMatterDomain_isOpen period hPeriod
    geometry frame hRegular couplings).prod isOpen_univ

theorem zero_mem_finiteFramePairedC2PhysicalMaxwellSpinCMatterLLDomain
    (hMinusCenter : finiteFramePairedC2MinusCenter period hPeriod geometry frame ∈
      generalMetricRelativeC2VolumeDomain period hPeriod frame geometry.plusMetric) :
    (0 : Input) ∈ finiteFramePairedC2PhysicalMaxwellSpinCMatterLLDomain period hPeriod
      geometry frame hRegular couplings :=
  ⟨zero_mem_finiteFramePairedC2PhysicalMaxwellSpinCMatterDomain period hPeriod
    geometry frame hRegular couplings hMinusCenter, Set.mem_univ _⟩

/-- The finite physical/Maxwell/SpinC action plus the genuine polynomial LL action. -/
def finiteFramePairedC2PhysicalMaxwellSpinCMatterLLAction
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (input : Input) : Real :=
  finiteFramePairedC2PhysicalMaxwellSpinCMatterAction period hPeriod geometry frame
      hRegular couplings interactionScale coefficients input.1 +
    regularGeneralMetricC0LLPTAction period hPeriod
      (canonicalDivergenceFreeLLFrame period hPeriod)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) input.2

theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLAction_contDiffOn_two
    (interactionScale : Real) (coefficients : PotentialCoefficients) :
    ContDiffOn Real 2
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLAction period hPeriod geometry
        frame hRegular couplings interactionScale coefficients)
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLDomain period hPeriod geometry
        frame hRegular couplings) := by
  have hOld : ContDiffOn Real 2
      (fun input : Input =>
        finiteFramePairedC2PhysicalMaxwellSpinCMatterAction period hPeriod geometry
          frame hRegular couplings interactionScale coefficients input.1)
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLDomain period hPeriod geometry
        frame hRegular couplings) :=
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterAction_contDiffOn_two period hPeriod
      geometry frame hRegular couplings interactionScale coefficients).comp
        contDiff_fst.contDiffOn (fun _ hInput => hInput.1)
  have hLL : ContDiff Real 2
      (fun input : Input =>
        regularGeneralMetricC0LLPTAction period hPeriod
          (canonicalDivergenceFreeLLFrame period hPeriod)
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod) input.2) :=
    ((regularGeneralMetricC0LLPTAction_contDiff period hPeriod
      (canonicalDivergenceFreeLLFrame period hPeriod)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod)).of_le
        (show (2 : ℕ∞) ≤ ∞ by exact WithTop.coe_le_coe.mpr le_top)).comp contDiff_snd
  exact hOld.add hLL.contDiffOn

def finiteFramePairedC2PhysicalMaxwellSpinCMatterLLEuler
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (input : Input) : Input →L[Real] Real :=
  fderiv Real
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLAction period hPeriod geometry
      frame hRegular couplings interactionScale coefficients) input

theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLAction_hasFDerivAt
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLDomain period hPeriod geometry
        frame hRegular couplings) :
    HasFDerivAt
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLAction period hPeriod geometry
        frame hRegular couplings interactionScale coefficients)
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLEuler period hPeriod geometry
        frame hRegular couplings interactionScale coefficients input) input :=
  (((finiteFramePairedC2PhysicalMaxwellSpinCMatterLLAction_contDiffOn_two period
    hPeriod geometry frame hRegular couplings interactionScale coefficients input
      hInput).contDiffAt
        ((finiteFramePairedC2PhysicalMaxwellSpinCMatterLLDomain_isOpen period hPeriod
          geometry frame hRegular couplings).mem_nhds hInput)).differentiableAt
            (by norm_num)).hasFDerivAt

/-- On smooth LL data, the added packet action is the genuine PT-symmetric action. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLAction_smooth_ll
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (oldInput : OldInput) (fields : IndependentFields period hPeriod) :
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLAction period hPeriod geometry
        frame hRegular couplings interactionScale coefficients
        (oldInput, smoothLLCoefficientPTC0FirstJetLinearMap period hPeriod
          (canonicalDivergenceFreeLLFrame period hPeriod)
          (fields.llAuxMetric, (fields.llMeasure, fields.llField))) =
      finiteFramePairedC2PhysicalMaxwellSpinCMatterAction period hPeriod geometry
          frame hRegular couplings interactionScale coefficients oldInput +
        globalPTSymmetricDifferentialLLAction period hPeriod
          (canonicalDivergenceFreeLLFrame period hPeriod) fields
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  unfold finiteFramePairedC2PhysicalMaxwellSpinCMatterLLAction
  rw [regularGeneralMetricC0LLPTAction_smooth]

/-- The same smooth specialization is exactly the LL summand of Candidate A. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLAction_global_ll
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (oldInput : OldInput) :
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLAction period hPeriod geometry
        frame hRegular couplings interactionScale coefficients
        (oldInput, smoothLLCoefficientPTC0FirstJetLinearMap period hPeriod
          (canonicalDivergenceFreeLLFrame period hPeriod)
          ((data.boundary.llFields period hPeriod).llAuxMetric,
            ((data.boundary.llFields period hPeriod).llMeasure,
              (data.boundary.llFields period hPeriod).llField))) =
      finiteFramePairedC2PhysicalMaxwellSpinCMatterAction period hPeriod geometry
          frame hRegular couplings interactionScale coefficients oldInput +
        globalCandidateALLAction period hPeriod data := by
  rw [finiteFramePairedC2PhysicalMaxwellSpinCMatterLLAction_smooth_ll]
  rfl

end
end P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D
end JanusFormal
