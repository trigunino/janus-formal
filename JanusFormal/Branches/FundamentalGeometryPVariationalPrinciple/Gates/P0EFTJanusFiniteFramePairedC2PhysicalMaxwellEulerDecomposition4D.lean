import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2PhysicalMaxwellAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2PhysicalEulerChainRule4D

/-! # Euler decomposition of the Maxwell-augmented finite physical action -/

namespace JanusFormal
namespace P0EFTJanusFiniteFramePairedC2PhysicalMaxwellEulerDecomposition4D

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
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDensity4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterRegularity4D
open P0EFTJanusFiniteFrameC2AbelianOperators4D
open P0EFTJanusFiniteFrameC2MobileMaxwellAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalEulerChainRule4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellAction4D
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

variable (plusFrame minusFrame : SmoothD8Frame period hPeriod)
  (plusBase minusBase : SmoothGeneralLorentzMetric period hPeriod)

local notation "PlusInput" =>
  GeneralMetricRelativeC2Core period hPeriod plusFrame plusBase ×
    FiniteFrameAbelianGaugeC2Core period hPeriod plusFrame

local notation "MinusInput" =>
  GeneralMetricRelativeC2Core period hPeriod minusFrame minusBase ×
    FiniteFrameAbelianGaugeC2Core period hPeriod minusFrame

local notation "PairInput" => PlusInput × MinusInput

/-- The paired Maxwell Euler is the weighted sum of its two sector Eulers. -/
theorem finiteFramePairedC2MobileMaxwellEuler_eq_sector_eulers
    (plusScale minusScale : Real) (input : PairInput)
    (hInput : input ∈
      finiteFramePairedC2MobileMaxwellDomain period hPeriod plusFrame minusFrame
        plusBase minusBase) :
    finiteFramePairedC2MobileMaxwellEuler period hPeriod plusFrame minusFrame
        plusBase minusBase plusScale minusScale input =
      plusScale •
          ((finiteFrameC2MobileMaxwellEuler period hPeriod plusFrame plusBase input.1).comp
            (ContinuousLinearMap.fst Real PlusInput MinusInput)) +
        minusScale •
          ((finiteFrameC2MobileMaxwellEuler period hPeriod minusFrame minusBase input.2).comp
            (ContinuousLinearMap.snd Real PlusInput MinusInput)) := by
  have hFst : HasFDerivAt (fun current : PairInput => current.1)
      (ContinuousLinearMap.fst Real PlusInput MinusInput) input := by
    fun_prop
  have hSnd : HasFDerivAt (fun current : PairInput => current.2)
      (ContinuousLinearMap.snd Real PlusInput MinusInput) input := by
    fun_prop
  have hPlus :=
    (finiteFrameC2MobileMaxwellAction_hasFDerivAt period hPeriod plusFrame plusBase
      input.1 hInput.1).comp input hFst
  have hMinus :=
    (finiteFrameC2MobileMaxwellAction_hasFDerivAt period hPeriod minusFrame minusBase
      input.2 hInput.2).comp input hSnd
  unfold finiteFramePairedC2MobileMaxwellEuler
  change fderiv Real
      (fun current : PairInput =>
        plusScale * finiteFrameC2MobileMaxwellAction period hPeriod plusFrame plusBase current.1 +
          minusScale * finiteFrameC2MobileMaxwellAction period hPeriod minusFrame minusBase current.2)
      input = _
  exact ((hPlus.const_mul plusScale).add (hMinus.const_mul minusScale)).fderiv

variable (geometry : GlobalCandidateAGeometry period hPeriod)
  (frame : SmoothD8Frame period hPeriod)
  (hRegular : ∀ point, Function.Bijective
    (intrinsicCandidateASylvesterAt period hPeriod geometry point))

local notation "Input" =>
  FiniteFramePairedC2PhysicalCore period hPeriod geometry frame

local notation "MaxwellInput" =>
  FiniteFramePairedC2MaxwellCore period hPeriod frame frame
    geometry.plusMetric geometry.plusMetric

private theorem finiteFramePairedC2PhysicalMaxwellProjection_mem
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalDomain period hPeriod geometry frame hRegular) :
    finiteFramePairedC2PhysicalMaxwellProjection period hPeriod geometry frame
        (finiteFramePairedC2PhysicalRecenter period hPeriod geometry frame input) ∈
      finiteFramePairedC2MobileMaxwellDomain period hPeriod frame frame
        geometry.plusMetric geometry.plusMetric := by
  exact ⟨⟨hInput.1.1.1, Set.mem_univ _⟩,
    ⟨hInput.1.1.2, Set.mem_univ _⟩⟩

/-- At every admissible point, the augmented Euler is the old physical Euler
plus the projected paired Maxwell Euler. -/
theorem finiteFramePairedC2PhysicalMaxwellEuler_eq_old_add_maxwell
    (couplings : GlobalCandidateAActionCouplings)
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalDomain period hPeriod geometry frame hRegular) :
    finiteFramePairedC2PhysicalMaxwellEuler period hPeriod geometry frame hRegular
        couplings interactionScale coefficients input =
      finiteFramePairedC2PhysicalEuler period hPeriod geometry frame hRegular
          couplings interactionScale coefficients input +
        (finiteFramePairedC2MobileMaxwellEuler period hPeriod frame frame
          geometry.plusMetric geometry.plusMetric couplings.plusMaxwellScale
          couplings.minusMaxwellScale
          (finiteFramePairedC2PhysicalMaxwellProjection period hPeriod geometry frame
            (finiteFramePairedC2PhysicalRecenter period hPeriod geometry frame input))).comp
          (finiteFramePairedC2PhysicalMaxwellProjection period hPeriod geometry frame) := by
  let projection := finiteFramePairedC2PhysicalMaxwellProjection period hPeriod geometry frame
  let recenter := finiteFramePairedC2PhysicalRecenter period hPeriod geometry frame
  let projected : MaxwellInput := projection (recenter input)
  have hInner : HasFDerivAt (fun current : Input => projection (recenter current)) projection input := by
    simpa only [Function.comp_def, ContinuousLinearMap.comp_id] using
      projection.hasFDerivAt.comp input
        (finiteFramePairedC2PhysicalRecenter_hasFDerivAt period hPeriod geometry frame input)
  have hMaxwell :=
    (finiteFramePairedC2MobileMaxwellAction_hasFDerivAt period hPeriod frame frame
      geometry.plusMetric geometry.plusMetric couplings.plusMaxwellScale
      couplings.minusMaxwellScale projected
      (finiteFramePairedC2PhysicalMaxwellProjection_mem period hPeriod geometry frame hRegular
        input hInput)).comp input hInner
  have hOld := finiteFramePairedC2PhysicalAction_hasFDerivAt period hPeriod geometry frame
    hRegular couplings interactionScale coefficients input hInput
  have hActionFunction :
      finiteFramePairedC2PhysicalMaxwellAction period hPeriod geometry frame hRegular
          couplings interactionScale coefficients =
        finiteFramePairedC2PhysicalAction period hPeriod geometry frame hRegular
            couplings interactionScale coefficients +
          (finiteFramePairedC2MobileMaxwellAction period hPeriod frame frame
              geometry.plusMetric geometry.plusMetric couplings.plusMaxwellScale
              couplings.minusMaxwellScale ∘
            fun current : Input => projection (recenter current)) := by
    funext current
    rfl
  unfold finiteFramePairedC2PhysicalMaxwellEuler
  rw [hActionFunction]
  simpa only [Function.comp_def, projection, recenter, projected] using
    (hOld.add hMaxwell).fderiv

end
end P0EFTJanusFiniteFramePairedC2PhysicalMaxwellEulerDecomposition4D
end JanusFormal
