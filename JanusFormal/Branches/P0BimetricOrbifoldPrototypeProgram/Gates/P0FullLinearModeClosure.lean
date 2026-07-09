import JanusFormal.Branches.P0BimetricOrbifoldPrototypeProgram.Gates.P0CandidateClosureSummary
import JanusFormal.Branches.P0BimetricOrbifoldPrototypeProgram.Gates.P0ScalarVectorModeStability

namespace JanusFormal
namespace P0FullLinearModeClosure

open P0CandidateClosureSummary
open P0ScalarVectorModeStability

set_option autoImplicit false

def tensorCoefficientsFromChain (c : CandidateClosureChain) :=
  P0TensorParameterDerivations.tensorCoefficientsFromCertificate
    (P0SymbolicTensorCoefficientMap.parameterCertificateFromSymbolicAction
      (P0ActionTermCoefficientDerivation.symbolicCertificateFromActionTerms
        (P0CandidateOrbifoldActionInstantiation.actionTermCertificateFromCandidate
          (candidateCertificateFromChain c))))

structure FullLinearModeClosure where
  chain : CandidateClosureChain
  scalar : LinearScalarModeCertificate
  vector : LinearVectorModeCertificate

def fullLinearModeClosureClosed (c : FullLinearModeClosure) : Prop :=
  P0LinearTensorPerturbationStability.tensorPerturbationsStable
    (tensorCoefficientsFromChain c.chain) /\
  P0LinearTensorPerturbationStability.visibleGravitationalWaveLuminal
    (tensorCoefficientsFromChain c.chain) /\
  scalarLinearModeStable c.scalar.coeffs /\
  vectorLinearModeStable c.vector.coeffs /\
  P0AetherGhostObservationConstraints.aetherStabilityClosed
    (stabilityConstraintsFromScalar c.scalar) /\
  P0AetherGhostObservationConstraints.aetherStabilityClosed
    (stabilityConstraintsFromVector c.vector)

theorem full_linear_mode_closure_closed
    (c : FullLinearModeClosure) :
    fullLinearModeClosureClosed c := by
  dsimp [fullLinearModeClosureClosed, tensorCoefficientsFromChain]
  constructor
  Â· exact chain_gives_tensor_stability c.chain
  constructor
  Â· exact chain_gives_visible_luminality c.chain
  constructor
  Â· exact c.scalar.stable
  constructor
  Â· exact c.vector.stable
  constructor
  Â· exact no_aether_instability_reintroduced_by_scalar c.scalar
  Â· exact no_aether_instability_reintroduced_by_vector c.vector

theorem scalar_missing_ghost_blocks_full_linear_closure
    (c : FullLinearModeClosure)
    (hMissing : Not (noScalarGhost c.scalar.coeffs)) :
    Not (fullLinearModeClosureClosed c) := by
  intro hClosed
  exact hMissing hClosed.right.right.left.left

theorem vector_missing_ghost_blocks_full_linear_closure
    (c : FullLinearModeClosure)
    (hMissing : Not (noVectorGhost c.vector.coeffs)) :
    Not (fullLinearModeClosureClosed c) := by
  intro hClosed
  exact hMissing hClosed.right.right.right.left.left

theorem scalar_vector_aether_not_reintroduced
    (c : FullLinearModeClosure) :
    P0AetherGhostObservationConstraints.aetherStabilityClosed
      (stabilityConstraintsFromScalar c.scalar) /\
    P0AetherGhostObservationConstraints.aetherStabilityClosed
      (stabilityConstraintsFromVector c.vector) := by
  exact no_aether_instability_reintroduced_scalar_and_vector c.scalar c.vector

end P0FullLinearModeClosure
end JanusFormal
