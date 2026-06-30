import JanusFormal.P0CandidateOrbifoldActionInstantiation

namespace JanusFormal
namespace P0CandidateParameterPhaseSpace

open P0CandidateOrbifoldActionInstantiation
open P0ActionTermCoefficientDerivation

set_option autoImplicit false

def noGhostBoundary (k : CandidateOrbifoldActionConstants) : Prop :=
  0 < k.radionVev * (k.planckMassSquared - k.aetherKineticScale)

def positiveRadionBranch (k : CandidateOrbifoldActionConstants) : Prop :=
  0 < k.radionVev

def reducedNoGhostBoundary (k : CandidateOrbifoldActionConstants) : Prop :=
  0 < k.planckMassSquared - k.aetherKineticScale

def noGradientBoundary (k : CandidateOrbifoldActionConstants) : Prop :=
  0 < k.planckMassSquared + k.membraneTension

def massPositiveBoundary (k : CandidateOrbifoldActionConstants) : Prop :=
  0 <= k.hassanRosenMassSquared

def candidateParameterDomain (k : CandidateOrbifoldActionConstants) : Prop :=
  positiveRadionBranch k /\
  reducedNoGhostBoundary k /\
  noGhostBoundary k /\
  noGradientBoundary k /\
  massPositiveBoundary k /\
  k.visibleSpeedUnmodified

theorem no_ghost_boundary_matches_candidate_alpha
    (k : CandidateOrbifoldActionConstants) :
    noGhostBoundary k =
      (0 < alphaFromTerms (termSystemFromCandidate k)) := by
  rfl

theorem no_gradient_boundary_matches_candidate_beta
    (k : CandidateOrbifoldActionConstants) :
    noGradientBoundary k =
      (0 < betaFromTerms (termSystemFromCandidate k)) := by
  rfl

theorem mass_boundary_matches_candidate_mass
    (k : CandidateOrbifoldActionConstants) :
    massPositiveBoundary k =
      (0 <= massSquaredFromTerms (termSystemFromCandidate k)) := by
  rfl

def canonicalCandidateStructure : CandidateOrbifoldActionStructure :=
  { cartanTetradFormalism := True
    plusEinsteinHilbertMatter := True
    minusTemporalRadionTetrad := True
    radionDoubleWellPotential := True
    gaugeLikeAetherFEqualsDA := True
    noAetherMultiplierGeometricNormal := True
    hassanRosenBoundaryMass := True
    hassanRosenDgrtCoefficients := True
    ghyJumpTermsPresent := True
    israelJunctionConditions := True
    minkowskiTwinBackground := True
    minusMetricDependsOnVevSquared := True
    minusTetradOrientationDependsOnVevSign := True }

theorem canonical_candidate_structure_closed :
    candidateActionStructureClosed canonicalCandidateStructure := by
  repeat constructor

def sampleStableConstants : CandidateOrbifoldActionConstants :=
  { planckMassSquared := 4
    radionVev := 1
    aetherKineticScale := 1
    membraneTension := 1
    hassanRosenMassSquared := 1
    visibleSpeedUnmodified := True }

theorem sample_stable_constants_in_domain :
    candidateParameterDomain sampleStableConstants := by
  norm_num [candidateParameterDomain, noGhostBoundary,
    positiveRadionBranch, reducedNoGhostBoundary,
    noGradientBoundary, massPositiveBoundary, sampleStableConstants]

theorem candidate_parameter_domain_nonempty :
    Nonempty { k : CandidateOrbifoldActionConstants // candidateParameterDomain k } := by
  exact ⟨⟨sampleStableConstants, sample_stable_constants_in_domain⟩⟩

def candidateCertificateFromDomain
    (k : CandidateOrbifoldActionConstants)
    (h : candidateParameterDomain k) :
    CandidateOrbifoldActionCertificate :=
  { constants := k
    actionStructure := canonicalCandidateStructure
    structureClosed := canonical_candidate_structure_closed
    visibleSpeed := h.right.right.right.right.right
    alphaPositive := h.right.right.left
    betaPositive := h.right.right.right.left
    massNonnegative := h.right.right.right.right.left }

theorem domain_constants_derive_tensor_stability
    (k : CandidateOrbifoldActionConstants)
    (h : candidateParameterDomain k) :
    P0LinearTensorPerturbationStability.tensorPerturbationsStable
      (P0TensorParameterDerivations.tensorCoefficientsFromCertificate
        (P0SymbolicTensorCoefficientMap.parameterCertificateFromSymbolicAction
          (P0ActionTermCoefficientDerivation.symbolicCertificateFromActionTerms
            (actionTermCertificateFromCandidate
              (candidateCertificateFromDomain k h))))) := by
  exact candidate_action_derives_tensor_stability
    (candidateCertificateFromDomain k h)

theorem domain_constants_derive_visible_luminality
    (k : CandidateOrbifoldActionConstants)
    (h : candidateParameterDomain k) :
    P0LinearTensorPerturbationStability.visibleGravitationalWaveLuminal
      (P0TensorParameterDerivations.tensorCoefficientsFromCertificate
        (P0SymbolicTensorCoefficientMap.parameterCertificateFromSymbolicAction
          (P0ActionTermCoefficientDerivation.symbolicCertificateFromActionTerms
            (actionTermCertificateFromCandidate
              (candidateCertificateFromDomain k h))))) := by
  exact candidate_action_derives_visible_luminality
    (candidateCertificateFromDomain k h)

theorem outside_no_ghost_boundary_blocks_domain
    (k : CandidateOrbifoldActionConstants)
    (hMissing : Not (noGhostBoundary k)) :
    Not (candidateParameterDomain k) := by
  intro h
  exact hMissing h.right.right.left

theorem outside_no_gradient_boundary_blocks_domain
    (k : CandidateOrbifoldActionConstants)
    (hMissing : Not (noGradientBoundary k)) :
    Not (candidateParameterDomain k) := by
  intro h
  exact hMissing h.right.right.right.left

theorem outside_mass_boundary_blocks_domain
    (k : CandidateOrbifoldActionConstants)
    (hMissing : Not (massPositiveBoundary k)) :
    Not (candidateParameterDomain k) := by
  intro h
  exact hMissing h.right.right.right.right.left

end P0CandidateParameterPhaseSpace
end JanusFormal
