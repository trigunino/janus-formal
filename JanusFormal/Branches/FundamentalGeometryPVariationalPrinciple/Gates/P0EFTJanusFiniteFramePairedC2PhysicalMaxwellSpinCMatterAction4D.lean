import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2PhysicalMaxwellEulerDecomposition4D

/-! # Primitive SpinC matter augmentation of the finite physical action -/

namespace JanusFormal
namespace P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterAction4D

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDensity4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterRegularity4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusFiniteFramePairedC2PhysicalAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellEulerDecomposition4D
open P0EFTJanusMatrixSquareRootInteractionDensity
open P0EFTJanusReciprocalBimetricPotential

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance : IsManifold coverModelWithCorners ω
    (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

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

local notation "PhysicalInput" =>
  FiniteFramePairedC2PhysicalCore period hPeriod geometry frame

/-- Product of the finite metric-gauge chart with the exact closed SpinC graph. -/
abbrev FiniteFramePairedC2PhysicalMaxwellSpinCMatterCore
    := PhysicalInput × ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
    couplings.matterMassSquared

local notation "Input" =>
  FiniteFramePairedC2PhysicalMaxwellSpinCMatterCore period hPeriod geometry frame couplings

local instance : NormedSpace Real Input := Prod.normedSpace

/-- The physical metric-gauge domain with unrestricted closed-graph matter state. -/
def finiteFramePairedC2PhysicalMaxwellSpinCMatterDomain
    : Set Input := finiteFramePairedC2PhysicalDomain period hPeriod geometry frame hRegular ×ˢ Set.univ

theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterDomain_isOpen
    : IsOpen (finiteFramePairedC2PhysicalMaxwellSpinCMatterDomain period hPeriod geometry frame
      hRegular couplings) :=
  (finiteFramePairedC2PhysicalDomain_isOpen period hPeriod geometry frame hRegular).prod
    isOpen_univ

theorem zero_mem_finiteFramePairedC2PhysicalMaxwellSpinCMatterDomain
    (hMinusCenter : finiteFramePairedC2MinusCenter period hPeriod geometry frame ∈
      generalMetricRelativeC2VolumeDomain period hPeriod frame geometry.plusMetric) :
    (0 : Input) ∈ finiteFramePairedC2PhysicalMaxwellSpinCMatterDomain period hPeriod
      geometry frame hRegular couplings :=
  ⟨zero_mem_finiteFramePairedC2PhysicalDomain period hPeriod geometry frame hRegular
    hMinusCenter, Set.mem_univ _⟩

/-- Maxwell-augmented finite physical action plus the exact primitive SpinC graph action. -/
def finiteFramePairedC2PhysicalMaxwellSpinCMatterAction
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (input : Input) : Real :=
  finiteFramePairedC2PhysicalMaxwellAction period hPeriod geometry frame hRegular
      couplings interactionScale coefficients input.1 +
    programPPrimitiveSpinCMatterGraphAction period hPeriod couplings.matterMassSquared input.2

theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterAction_contDiffOn_two
    (interactionScale : Real) (coefficients : PotentialCoefficients) :
    ContDiffOn Real 2
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterAction period hPeriod geometry frame
        hRegular couplings interactionScale coefficients)
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterDomain period hPeriod geometry frame
        hRegular couplings) := by
  have hPhysical : ContDiffOn Real 2
      (fun input : Input =>
        finiteFramePairedC2PhysicalMaxwellAction period hPeriod geometry frame hRegular
          couplings interactionScale coefficients input.1)
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterDomain period hPeriod geometry frame
        hRegular couplings) :=
    (finiteFramePairedC2PhysicalMaxwellAction_contDiffOn_two period hPeriod geometry frame
      hRegular couplings interactionScale coefficients).comp contDiff_fst.contDiffOn
        (fun _ hInput => hInput.1)
  have hMatter : ContDiffOn Real 2
      (fun input : Input =>
        programPPrimitiveSpinCMatterGraphAction period hPeriod couplings.matterMassSquared
          input.2)
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterDomain period hPeriod geometry frame
        hRegular couplings) :=
    ((programPPrimitiveSpinCMatterGraphAction_contDiff_two period hPeriod
      couplings.matterMassSquared).comp contDiff_snd).contDiffOn
  exact hPhysical.add hMatter

def finiteFramePairedC2PhysicalMaxwellSpinCMatterEuler
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (input : Input) : Input →L[Real] Real :=
  fderiv Real
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterAction period hPeriod geometry frame
      hRegular couplings interactionScale coefficients) input

theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterAction_hasFDerivAt
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterDomain period hPeriod geometry frame
        hRegular couplings) :
    HasFDerivAt
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterAction period hPeriod geometry frame
        hRegular couplings interactionScale coefficients)
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterEuler period hPeriod geometry frame
        hRegular couplings interactionScale coefficients input) input :=
  (((finiteFramePairedC2PhysicalMaxwellSpinCMatterAction_contDiffOn_two period hPeriod
    geometry frame hRegular couplings interactionScale coefficients input hInput).contDiffAt
      ((finiteFramePairedC2PhysicalMaxwellSpinCMatterDomain_isOpen period hPeriod geometry frame
        hRegular couplings).mem_nhds hInput)).differentiableAt (by norm_num)).hasFDerivAt

/-- On every finite spectral matter state, the added summand is exactly the
primitive SpinC term of the global Candidate-A action. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterAction_finite_matter
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (physicalInput : PhysicalInput)
    (configuration : GlobalFieldConfiguration period hPeriod)
    (matterCoefficients : ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    finiteFramePairedC2PhysicalMaxwellSpinCMatterAction period hPeriod geometry frame
        hRegular couplings interactionScale coefficients
        (physicalInput, programPPrimitiveSpinCMatterGraphFinite period hPeriod
          couplings.matterMassSquared matterCoefficients) =
      finiteFramePairedC2PhysicalMaxwellAction period hPeriod geometry frame hRegular
          couplings interactionScale coefficients physicalInput +
        globalCandidateAMatterAction period hPeriod
          { configuration with
            spinCMatter := programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
              matterCoefficients }
          couplings := by
  unfold finiteFramePairedC2PhysicalMaxwellSpinCMatterAction
  rw [globalCandidateAMatterAction_finite_eq_graphAction]

end
end P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterAction4D
end JanusFormal
