import JanusFormal.Branches.P0BimetricOrbifoldPrototypeProgram.Gates.P0RadionAmplitudeOrientationSplit

namespace JanusFormal
namespace P0CandidateClosureSummary

open P0CandidateParameterPhaseSpace
open P0CandidateOrbifoldActionInstantiation
open P0RadionAmplitudeOrientationSplit
open P0RadionVielbeinSouriauBridge

set_option autoImplicit false

structure CandidateClosureChain where
  constants : CandidateOrbifoldActionConstants
  parameterDomain : candidateParameterDomain constants
  actionStructureClosed : candidateActionStructureClosed canonicalCandidateStructure

def candidateCertificateFromChain
    (c : CandidateClosureChain) :
    CandidateOrbifoldActionCertificate :=
  candidateCertificateFromDomain c.constants c.parameterDomain

theorem chain_gives_positive_amplitude
    (c : CandidateClosureChain) :
    positiveRadionBranch c.constants := by
  exact c.parameterDomain.left

theorem chain_gives_reduced_no_ghost_boundary
    (c : CandidateClosureChain) :
    reducedNoGhostBoundary c.constants := by
  exact c.parameterDomain.right.left

theorem chain_gives_no_ghost
    (c : CandidateClosureChain) :
    noGhostBoundary c.constants := by
  exact c.parameterDomain.right.right.left

theorem chain_gives_tensor_stability
    (c : CandidateClosureChain) :
    P0LinearTensorPerturbationStability.tensorPerturbationsStable
      (P0TensorParameterDerivations.tensorCoefficientsFromCertificate
        (P0SymbolicTensorCoefficientMap.parameterCertificateFromSymbolicAction
          (P0ActionTermCoefficientDerivation.symbolicCertificateFromActionTerms
            (actionTermCertificateFromCandidate
              (candidateCertificateFromChain c))))) := by
  exact domain_constants_derive_tensor_stability c.constants c.parameterDomain

theorem chain_gives_visible_luminality
    (c : CandidateClosureChain) :
    P0LinearTensorPerturbationStability.visibleGravitationalWaveLuminal
      (P0TensorParameterDerivations.tensorCoefficientsFromCertificate
        (P0SymbolicTensorCoefficientMap.parameterCertificateFromSymbolicAction
          (P0ActionTermCoefficientDerivation.symbolicCertificateFromActionTerms
            (actionTermCertificateFromCandidate
              (candidateCertificateFromChain c))))) := by
  exact domain_constants_derive_visible_luminality c.constants c.parameterDomain

theorem chain_gives_antichronous_orientation :
    orientationFromCandidateStructure canonicalCandidateStructure := by
  exact closed_candidate_structure_gives_orientation
    canonicalCandidateStructure
    canonical_candidate_structure_closed

theorem chain_separates_amplitude_and_orientation
    (c : CandidateClosureChain) :
    positiveRadionBranch c.constants /\
    orientationFromCandidateStructure canonicalCandidateStructure := by
  exact âŸ¨chain_gives_positive_amplitude c, chain_gives_antichronous_orientationâŸ©

def sampleClosureChain : CandidateClosureChain :=
  { constants := sampleStableConstants
    parameterDomain := sample_stable_constants_in_domain
    actionStructureClosed := canonical_candidate_structure_closed }

theorem sample_chain_closes_tensor_stability :
    P0LinearTensorPerturbationStability.tensorPerturbationsStable
      (P0TensorParameterDerivations.tensorCoefficientsFromCertificate
        (P0SymbolicTensorCoefficientMap.parameterCertificateFromSymbolicAction
          (P0ActionTermCoefficientDerivation.symbolicCertificateFromActionTerms
            (actionTermCertificateFromCandidate
              (candidateCertificateFromChain sampleClosureChain))))) := by
  exact chain_gives_tensor_stability sampleClosureChain

theorem sample_chain_closes_visible_luminality :
    P0LinearTensorPerturbationStability.visibleGravitationalWaveLuminal
      (P0TensorParameterDerivations.tensorCoefficientsFromCertificate
        (P0SymbolicTensorCoefficientMap.parameterCertificateFromSymbolicAction
          (P0ActionTermCoefficientDerivation.symbolicCertificateFromActionTerms
            (actionTermCertificateFromCandidate
              (candidateCertificateFromChain sampleClosureChain))))) := by
  exact chain_gives_visible_luminality sampleClosureChain

end P0CandidateClosureSummary
end JanusFormal
