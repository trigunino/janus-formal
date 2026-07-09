import JanusFormal.Branches.P0EarlyProgram.Gates.P0AetherGhostObservationConstraints

namespace JanusFormal
namespace P0ScalarVectorModeStability

open P0AetherGhostObservationConstraints

set_option autoImplicit false

structure ScalarPerturbationSetup where
  scalarModeDecomposed : Prop
  scalarConstraintPreserved : Prop
  orbifoldBoundaryJumpConditions : Prop
  quadraticActionExpanded : Prop
  scalarMassTermPresent : Prop
  hamiltonianConstraintPresent : Prop
  momentumConstraintPresent : Prop

def scalarPerturbationSetupClosed (s : ScalarPerturbationSetup) : Prop :=
  s.scalarModeDecomposed /\
  s.scalarConstraintPreserved /\
  s.orbifoldBoundaryJumpConditions /\
  s.quadraticActionExpanded /\
  s.scalarMassTermPresent /\
  s.hamiltonianConstraintPresent /\
  s.momentumConstraintPresent

structure ScalarQuadraticCoefficients where
  scalarAlphaPositive : Prop
  scalarBetaPositive : Prop
  scalarSpeedSquaredPositive : Prop
  scalarMassMatrixPositive : Prop
  scalarHyperbolicSector : Prop

def noScalarGhost (q : ScalarQuadraticCoefficients) : Prop :=
  q.scalarAlphaPositive

def noScalarGradientInstability (q : ScalarQuadraticCoefficients) : Prop :=
  q.scalarBetaPositive /\ q.scalarSpeedSquaredPositive

def scalarSectorHyperbolic (q : ScalarQuadraticCoefficients) : Prop :=
  q.scalarHyperbolicSector

def scalarLinearModeStable (q : ScalarQuadraticCoefficients) : Prop :=
  noScalarGhost q /\
  noScalarGradientInstability q /\
  scalarSectorHyperbolic q /\
  q.scalarMassMatrixPositive

structure LinearScalarModeCertificate where
  setup : ScalarPerturbationSetup
  coeffs : ScalarQuadraticCoefficients
  setupClosed : scalarPerturbationSetupClosed setup
  stable : scalarLinearModeStable coeffs

def ghostConstraintsFromScalar (c : LinearScalarModeCertificate) : GhostFreedomConstraints :=
  { hassanRosenConstraintStructure := noScalarGhost c.coeffs
    generalizedProcaDegeneracy := c.setup.scalarConstraintPreserved
    noHigherThanSecondOrderEom := c.setup.quadraticActionExpanded
    hamiltonianConstraintPresent := c.setup.hamiltonianConstraintPresent
    momentumConstraintPresent := c.setup.momentumConstraintPresent
    boulwareDeserModeRemoved := c.coeffs.scalarMassMatrixPositive
    positiveKineticSector := noScalarGhost c.coeffs }

def stabilityConstraintsFromScalar (c : LinearScalarModeCertificate) : AetherStabilityConstraints :=
  { timelikeUnitVectorConstraint := c.setup.scalarModeDecomposed
    sectorialLorentzBreakingOnly := c.setup.orbifoldBoundaryJumpConditions
    noTachyonicAetherMode := c.coeffs.scalarMassMatrixPositive
    noGradientInstability := noScalarGradientInstability c.coeffs
    topologicalCutoffWellPosed := c.setup.quadraticActionExpanded
    boundaryModesControlled := c.setup.orbifoldBoundaryJumpConditions
    vacuumDecayForbidden := scalarLinearModeStable c.coeffs }

theorem stable_scalar_certificate_gives_no_ghost
    (c : LinearScalarModeCertificate) :
    noScalarGhost c.coeffs := by
  exact c.stable.left

theorem stable_scalar_certificate_gives_no_gradient
    (c : LinearScalarModeCertificate) :
    noScalarGradientInstability c.coeffs := by
  exact c.stable.right.left

theorem stable_scalar_certificate_gives_hyperbolic
    (c : LinearScalarModeCertificate) :
    scalarSectorHyperbolic c.coeffs := by
  exact c.stable.right.right.left

theorem stable_scalar_certificate_gives_mass_positive
    (c : LinearScalarModeCertificate) :
    c.coeffs.scalarMassMatrixPositive := by
  exact c.stable.right.right.right

theorem no_aether_instability_reintroduced_by_scalar
    (c : LinearScalarModeCertificate) :
    aetherStabilityClosed (stabilityConstraintsFromScalar c) := by
  rcases c.setupClosed with
    ⟨hScalarMode, hScalarConstraint, hOrbifold, hQuadratic, hMass, hHamiltonian, hMomentum⟩
  dsimp [aetherStabilityClosed, stabilityConstraintsFromScalar]
  exact And.intro hScalarMode
    (And.intro hOrbifold
      (And.intro c.stable.right.right.right
        (And.intro c.stable.right.left
          (And.intro hQuadratic
            (And.intro hOrbifold c.stable)))))

theorem missing_scalar_ghost_blocks_scalar_closure
    (q : ScalarQuadraticCoefficients)
    (hMissing : Not (noScalarGhost q)) :
    Not (scalarLinearModeStable q) := by
  intro hStable
  exact hMissing hStable.left

theorem missing_scalar_gradient_blocks_scalar_closure
    (q : ScalarQuadraticCoefficients)
    (hMissing : Not (noScalarGradientInstability q)) :
    Not (scalarLinearModeStable q) := by
  intro hStable
  exact hMissing hStable.right.left

theorem missing_scalar_hyperbolic_blocks_scalar_closure
    (q : ScalarQuadraticCoefficients)
    (hMissing : Not (scalarSectorHyperbolic q)) :
    Not (scalarLinearModeStable q) := by
  intro hStable
  exact hMissing hStable.right.right.left

structure VectorPerturbationSetup where
  vectorModeTransverse : Prop
  orbifoldBoundaryJumpConditions : Prop
  quadraticActionExpanded : Prop
  vectorMassTermPresent : Prop
  hamiltonianConstraintPresent : Prop
  momentumConstraintPresent : Prop
  aetherPerturbationIncluded : Prop

def vectorPerturbationSetupClosed (s : VectorPerturbationSetup) : Prop :=
  s.vectorModeTransverse /\
  s.orbifoldBoundaryJumpConditions /\
  s.quadraticActionExpanded /\
  s.vectorMassTermPresent /\
  s.hamiltonianConstraintPresent /\
  s.momentumConstraintPresent /\
  s.aetherPerturbationIncluded

structure VectorQuadraticCoefficients where
  vectorAlphaPositive : Prop
  vectorBetaPositive : Prop
  vectorSpeedSquaredPositive : Prop
  vectorMassMatrixPositive : Prop
  vectorHyperbolicSector : Prop

def noVectorGhost (q : VectorQuadraticCoefficients) : Prop :=
  q.vectorAlphaPositive

def noVectorGradientInstability (q : VectorQuadraticCoefficients) : Prop :=
  q.vectorBetaPositive /\ q.vectorSpeedSquaredPositive

def vectorSectorHyperbolic (q : VectorQuadraticCoefficients) : Prop :=
  q.vectorHyperbolicSector

def vectorLinearModeStable (q : VectorQuadraticCoefficients) : Prop :=
  noVectorGhost q /\
  noVectorGradientInstability q /\
  vectorSectorHyperbolic q /\
  q.vectorMassMatrixPositive

structure LinearVectorModeCertificate where
  setup : VectorPerturbationSetup
  coeffs : VectorQuadraticCoefficients
  setupClosed : vectorPerturbationSetupClosed setup
  stable : vectorLinearModeStable coeffs

def ghostConstraintsFromVector (c : LinearVectorModeCertificate) : GhostFreedomConstraints :=
  { hassanRosenConstraintStructure := noVectorGhost c.coeffs
    generalizedProcaDegeneracy := c.setup.aetherPerturbationIncluded
    noHigherThanSecondOrderEom := c.setup.quadraticActionExpanded
    hamiltonianConstraintPresent := c.setup.hamiltonianConstraintPresent
    momentumConstraintPresent := c.setup.momentumConstraintPresent
    boulwareDeserModeRemoved := c.coeffs.vectorMassMatrixPositive
    positiveKineticSector := noVectorGhost c.coeffs }

def stabilityConstraintsFromVector (c : LinearVectorModeCertificate) : AetherStabilityConstraints :=
  { timelikeUnitVectorConstraint := c.setup.vectorModeTransverse
    sectorialLorentzBreakingOnly := c.setup.orbifoldBoundaryJumpConditions
    noTachyonicAetherMode := c.coeffs.vectorMassMatrixPositive
    noGradientInstability := noVectorGradientInstability c.coeffs
    topologicalCutoffWellPosed := c.setup.quadraticActionExpanded
    boundaryModesControlled := c.setup.orbifoldBoundaryJumpConditions
    vacuumDecayForbidden := vectorLinearModeStable c.coeffs }

theorem stable_vector_certificate_gives_no_ghost
    (c : LinearVectorModeCertificate) :
    noVectorGhost c.coeffs := by
  exact c.stable.left

theorem stable_vector_certificate_gives_no_gradient
    (c : LinearVectorModeCertificate) :
    noVectorGradientInstability c.coeffs := by
  exact c.stable.right.left

theorem stable_vector_certificate_gives_hyperbolic
    (c : LinearVectorModeCertificate) :
    vectorSectorHyperbolic c.coeffs := by
  exact c.stable.right.right.left

theorem stable_vector_certificate_gives_mass_positive
    (c : LinearVectorModeCertificate) :
    c.coeffs.vectorMassMatrixPositive := by
  exact c.stable.right.right.right

theorem no_aether_instability_reintroduced_by_vector
    (c : LinearVectorModeCertificate) :
    aetherStabilityClosed (stabilityConstraintsFromVector c) := by
  rcases c.setupClosed with
    ⟨hVectorMode, hOrbifold, hQuadratic, hMassSetup, hHamiltonian, hMomentum, hAetherIncluded⟩
  dsimp [aetherStabilityClosed, stabilityConstraintsFromVector]
  exact And.intro hVectorMode
    (And.intro hOrbifold
      (And.intro c.stable.right.right.right
        (And.intro c.stable.right.left
          (And.intro hQuadratic
            (And.intro hOrbifold c.stable)))))

theorem missing_vector_ghost_blocks_vector_closure
    (q : VectorQuadraticCoefficients)
    (hMissing : Not (noVectorGhost q)) :
    Not (vectorLinearModeStable q) := by
  intro hStable
  exact hMissing hStable.left

theorem missing_vector_gradient_blocks_vector_closure
    (q : VectorQuadraticCoefficients)
    (hMissing : Not (noVectorGradientInstability q)) :
    Not (vectorLinearModeStable q) := by
  intro hStable
  exact hMissing hStable.right.left

theorem missing_vector_hyperbolic_blocks_vector_closure
    (q : VectorQuadraticCoefficients)
    (hMissing : Not (vectorSectorHyperbolic q)) :
    Not (vectorLinearModeStable q) := by
  intro hStable
  exact hMissing hStable.right.right.left

theorem no_aether_instability_reintroduced_scalar_and_vector
    (s : LinearScalarModeCertificate)
    (v : LinearVectorModeCertificate) :
    aetherStabilityClosed (stabilityConstraintsFromScalar s) /\
    aetherStabilityClosed (stabilityConstraintsFromVector v) := by
  exact And.intro
    (no_aether_instability_reintroduced_by_scalar s)
    (no_aether_instability_reintroduced_by_vector v)

end P0ScalarVectorModeStability
end JanusFormal
