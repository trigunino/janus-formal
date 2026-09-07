import Mathlib.Analysis.SpecialFunctions.Exponential
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatrixInteractionFrechetNoether

/-! # Spectral derivative reduction for arbitrary frame commutators

Every matrix generates an actual invertible exponential frame curve. The
existing Noether theorem therefore annihilates every commutator direction.
The Sylvester bridge below exposes precisely the relative-velocity identity
needed for interaction recentering; it does not assume or assert equivariance
of a selected square-root branch.
-/

namespace JanusFormal
namespace P0EFTJanusInteractionSpectralCommutatorReduction4D
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
open scoped Matrix.Norms.Frobenius
open P0EFTJanusReciprocalBimetricPotential
open P0EFTJanusMatrixSquareRootInteractionDensity
open P0EFTJanusMatrixDiagonalGaugeNoether
open P0EFTJanusMatrixInteractionFrechetNoether
private abbrev Matrix4 := Matrix (Fin 4) (Fin 4) Real

set_option backward.isDefEq.respectTransparency false in
/-- Any real matrix is the generator of a genuine invertible frame curve. -/
def exponentialInteractionFrame (generator : Matrix4) : OneParameterDiagonalFrame where
  frame := fun scalar : Real => NormedSpace.exp (scalar • generator)
  inverse := fun scalar : Real => NormedSpace.exp (scalar • (-generator))
  generator := generator
  inverseWitness := by
    intro scalar
    constructor
    · simpa only [smul_neg, neg_add_cancel, NormedSpace.exp_zero] using
        (NormedSpace.exp_add_of_commute (𝔸 := Matrix4)
          (Commute.refl (scalar • generator)).neg_left).symm
    · simpa only [smul_neg, add_neg_cancel, NormedSpace.exp_zero] using
        (NormedSpace.exp_add_of_commute (𝔸 := Matrix4)
          (Commute.refl (scalar • generator)).neg_right).symm
  frame_zero := by rw [zero_smul, NormedSpace.exp_zero]
  inverse_zero := by rw [zero_smul, NormedSpace.exp_zero]
  frame_hasDerivAt := by
    simpa only [zero_smul, NormedSpace.exp_zero, one_mul] using
      (_root_.hasDerivAt_exp_smul_const (𝕂 := Real) generator (0 : Real))
  inverseDerivative := -generator
  inverse_hasDerivAt := by
    simpa only [zero_smul, NormedSpace.exp_zero, one_mul] using
      (_root_.hasDerivAt_exp_smul_const (𝕂 := Real) (-generator) (0 : Real))

/-- The actual spectral differential annihilates every matrix commutator. -/
theorem matrixSpectralPotentialDerivative_commutator
    (coefficients : PotentialCoefficients) (root generator : Matrix4) :
    matrixSpectralPotentialDerivative coefficients root
      (root * generator - generator * root) = 0 :=
  explicit_matrixInteraction_noether_pairing coefficients
    (exponentialInteractionFrame generator) root

/-- A frame commutator does not change the scalar spectral variation. -/
theorem matrixSpectralPotentialDerivative_add_commutator
    (coefficients : PotentialCoefficients) (root velocity generator : Matrix4) :
    matrixSpectralPotentialDerivative coefficients root
        (velocity + (root * generator - generator * root)) =
      matrixSpectralPotentialDerivative coefficients root velocity := by
  rw [map_add, matrixSpectralPotentialDerivative_commutator, add_zero]

/-- The Sylvester image of a root commutator is the relative-matrix commutator. -/
theorem matrixSylvester_root_commutator
    (root relative generator : Matrix4) (hSquare : root * root = 1 + relative) :
    root * (root * generator - generator * root) +
        (root * generator - generator * root) * root =
      relative * generator - generator * relative := by
  calc
    _ = (root * root) * generator - generator * (root * root) := by noncomm_ring
    _ = _ := by
      rw [hSquare]
      noncomm_ring

/-- The remaining recentering obligation is an exact relative-velocity
commutator. Injectivity then determines the difference of actual root velocities. -/
theorem matrixRootVelocities_eq_add_commutator_of_sylvester
    (root relative originalVelocity centeredVelocity generator : Matrix4)
    (hSquare : root * root = 1 + relative)
    (hInjective : Function.Injective (fun velocity : Matrix4 => root * velocity + velocity * root))
    (hRelativeVelocity : root * originalVelocity + originalVelocity * root =
      (root * centeredVelocity + centeredVelocity * root) +
        (relative * generator - generator * relative)) :
    originalVelocity = centeredVelocity + (root * generator - generator * root) := by
  apply hInjective
  change root * originalVelocity + originalVelocity * root =
    root * (centeredVelocity + (root * generator - generator * root)) +
      (centeredVelocity + (root * generator - generator * root)) * root
  rw [hRelativeVelocity, ← matrixSylvester_root_commutator root relative generator hSquare]
  noncomm_ring

/-- Concrete off-centre derivative reduction once the two Sylvester right-hand
sides differ by the displayed relative commutator. -/
theorem matrixSpectralPotentialDerivative_eq_of_relative_commutator
    (coefficients : PotentialCoefficients)
    (root relative originalVelocity centeredVelocity generator : Matrix4)
    (hSquare : root * root = 1 + relative)
    (hInjective : Function.Injective (fun velocity : Matrix4 => root * velocity + velocity * root))
    (hRelativeVelocity : root * originalVelocity + originalVelocity * root =
      (root * centeredVelocity + centeredVelocity * root) +
        (relative * generator - generator * relative)) :
    matrixSpectralPotentialDerivative coefficients root originalVelocity =
      matrixSpectralPotentialDerivative coefficients root centeredVelocity := by
  rw [matrixRootVelocities_eq_add_commutator_of_sylvester root relative
    originalVelocity centeredVelocity generator hSquare hInjective hRelativeVelocity]
  exact matrixSpectralPotentialDerivative_add_commutator coefficients root centeredVelocity generator

end
end P0EFTJanusInteractionSpectralCommutatorReduction4D
end JanusFormal
