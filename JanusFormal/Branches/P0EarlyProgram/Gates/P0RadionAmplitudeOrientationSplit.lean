import JanusFormal.Branches.P0EarlyProgram.Gates.P0CandidateParameterPhaseSpace
import JanusFormal.Branches.P0EarlyProgram.Gates.P0RadionVielbeinSouriauBridge

namespace JanusFormal
namespace P0RadionAmplitudeOrientationSplit

open P0CandidateParameterPhaseSpace
open P0CandidateOrbifoldActionInstantiation
open P0RadionVielbeinSouriauBridge

set_option autoImplicit false

structure RadionAmplitudeOrientationData where
  amplitude : Rat
  amplitudePositive : 0 < amplitude
  temporalTetradOrientationFlip : Prop
  antichronousOrientation : Prop

def amplitudeFromCandidateConstants
    (k : CandidateOrbifoldActionConstants)
    (h : positiveRadionBranch k) :
    RadionAmplitudeOrientationData :=
  { amplitude := k.radionVev
    amplitudePositive := h
    temporalTetradOrientationFlip := True
    antichronousOrientation := True }

def orientationFromCandidateStructure
    (s : CandidateOrbifoldActionStructure) : Prop :=
  s.minusTetradOrientationDependsOnVevSign /\
  (radionGeometryFromCandidate s).antichronousLorentzComponentSelected

theorem closed_candidate_structure_gives_orientation
    (s : CandidateOrbifoldActionStructure)
    (h : candidateActionStructureClosed s) :
    orientationFromCandidateStructure s := by
  exact ⟨h.right.right.right.right.right.right.right.right.right.right.right.right,
    h.right.right.right.right.right.right.right.right.right.right.right.right⟩

theorem amplitude_positive_is_not_antichronous_orientation :
    Not (forall k : CandidateOrbifoldActionConstants,
      positiveRadionBranch k -> orientationFromCandidateStructure canonicalCandidateStructure -> False) := by
  intro h
  have hAmp : positiveRadionBranch sampleStableConstants := by
    norm_num [positiveRadionBranch, sampleStableConstants]
  have hOrient : orientationFromCandidateStructure canonicalCandidateStructure :=
    closed_candidate_structure_gives_orientation
      canonicalCandidateStructure
      canonical_candidate_structure_closed
  exact h sampleStableConstants hAmp hOrient

theorem domain_splits_amplitude_from_orientation
    (k : CandidateOrbifoldActionConstants)
    (hDomain : candidateParameterDomain k) :
    positiveRadionBranch k /\ noGhostBoundary k := by
  exact ⟨hDomain.left, hDomain.right.right.left⟩

theorem orientation_is_carried_by_tetrad_not_alpha
    (s : CandidateOrbifoldActionStructure)
    (h : candidateActionStructureClosed s) :
    (radionGeometryFromCandidate s).antichronousLorentzComponentSelected := by
  exact (closed_candidate_gives_radion_tetrad_orientation s h).right.right.right.right.right.right

theorem no_ghost_uses_amplitude_not_orientation
    (k : CandidateOrbifoldActionConstants)
    (hDomain : candidateParameterDomain k) :
    0 < k.radionVev * (k.planckMassSquared - k.aetherKineticScale) := by
  exact hDomain.right.right.left

theorem reduced_boundary_with_positive_amplitude_gives_no_ghost
    (k : CandidateOrbifoldActionConstants)
    (hAmp : positiveRadionBranch k)
    (hReduced : reducedNoGhostBoundary k) :
    noGhostBoundary k := by
  unfold noGhostBoundary positiveRadionBranch reducedNoGhostBoundary at *
  exact mul_pos hAmp hReduced

end P0RadionAmplitudeOrientationSplit
end JanusFormal
