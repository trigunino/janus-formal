import JanusFormal.Branches.P0BimetricOrbifoldPrototypeProgram.Gates.P0AetherGhostObservationConstraints

namespace JanusFormal
namespace P0LinearTensorPerturbationStability

open P0AetherGhostObservationConstraints

set_option autoImplicit false

structure TensorPerturbationSetup where
  plusTensorTT : Prop
  minusTensorTT : Prop
  aetherPerturbationIncluded : Prop
  orbifoldBoundaryJumpConditions : Prop
  quadraticActionExpanded : Prop
  hassanRosenMassTerm : Prop
  aetherKineticTerm : Prop

def tensorSetupClosed (s : TensorPerturbationSetup) : Prop :=
  s.plusTensorTT /\
  s.minusTensorTT /\
  s.aetherPerturbationIncluded /\
  s.orbifoldBoundaryJumpConditions /\
  s.quadraticActionExpanded /\
  s.hassanRosenMassTerm /\
  s.aetherKineticTerm

structure TensorQuadraticCoefficients where
  alphaPositive : Prop
  betaPositive : Prop
  plusSpeedSquaredPositive : Prop
  massMatrixPositive : Prop
  c1PlusC3Zero : Prop
  visibleTensorLuminal : Prop
  minusSectorHyperbolic : Prop

def noTensorGhost (q : TensorQuadraticCoefficients) : Prop :=
  q.alphaPositive

def noTensorGradientInstability (q : TensorQuadraticCoefficients) : Prop :=
  q.betaPositive /\ q.plusSpeedSquaredPositive /\ q.minusSectorHyperbolic

def visibleGravitationalWaveLuminal (q : TensorQuadraticCoefficients) : Prop :=
  q.c1PlusC3Zero /\ q.visibleTensorLuminal

def tensorPerturbationsStable (q : TensorQuadraticCoefficients) : Prop :=
  noTensorGhost q /\
  noTensorGradientInstability q /\
  visibleGravitationalWaveLuminal q /\
  q.massMatrixPositive

structure LinearTensorPerturbationCertificate where
  setup : TensorPerturbationSetup
  coeffs : TensorQuadraticCoefficients
  setupClosed : tensorSetupClosed setup
  stable : tensorPerturbationsStable coeffs

def ghostConstraintsFromTensor
    (c : LinearTensorPerturbationCertificate) :
    GhostFreedomConstraints :=
  { hassanRosenConstraintStructure := c.setup.hassanRosenMassTerm
    generalizedProcaDegeneracy := c.setup.aetherKineticTerm
    noHigherThanSecondOrderEom := c.setup.quadraticActionExpanded
    hamiltonianConstraintPresent := c.coeffs.alphaPositive
    momentumConstraintPresent := c.coeffs.massMatrixPositive
    boulwareDeserModeRemoved := c.coeffs.massMatrixPositive
    positiveKineticSector := c.coeffs.alphaPositive }

def stabilityConstraintsFromTensor
    (c : LinearTensorPerturbationCertificate) :
    AetherStabilityConstraints :=
  { timelikeUnitVectorConstraint := c.setup.aetherPerturbationIncluded
    sectorialLorentzBreakingOnly := c.setup.orbifoldBoundaryJumpConditions
    noTachyonicAetherMode := c.coeffs.massMatrixPositive
    noGradientInstability := noTensorGradientInstability c.coeffs
    topologicalCutoffWellPosed := c.setup.orbifoldBoundaryJumpConditions
    boundaryModesControlled := c.setup.orbifoldBoundaryJumpConditions
    vacuumDecayForbidden := tensorPerturbationsStable c.coeffs }

def observationsFromTensor
    (c : LinearTensorPerturbationCertificate) :
    ObservationalConstraints :=
  { gravitationalWaveSpeedLuminal := c.coeffs.visibleTensorLuminal
    gw170817BoundSatisfied := visibleGravitationalWaveLuminal c.coeffs
    standardMatterLorentzInvariantOnPlusSheet := c.coeffs.visibleTensorLuminal
    lorentzBreakingGravitationallySuppressed := c.coeffs.c1PlusC3Zero
    weakBimetricMixing := c.coeffs.massMatrixPositive
    ppnConstraintsSatisfied := c.coeffs.c1PlusC3Zero
    cosmologyBackgroundViable := tensorPerturbationsStable c.coeffs }

theorem stable_tensor_certificate_gives_no_ghost
    (c : LinearTensorPerturbationCertificate) :
    noTensorGhost c.coeffs := by
  exact c.stable.left

theorem stable_tensor_certificate_gives_no_gradient
    (c : LinearTensorPerturbationCertificate) :
    noTensorGradientInstability c.coeffs := by
  exact c.stable.right.left

theorem stable_tensor_certificate_gives_visible_luminality
    (c : LinearTensorPerturbationCertificate) :
    visibleGravitationalWaveLuminal c.coeffs := by
  exact c.stable.right.right.left

theorem visible_luminality_requires_c1_plus_c3_zero
    (q : TensorQuadraticCoefficients)
    (h : visibleGravitationalWaveLuminal q) :
    q.c1PlusC3Zero := by
  exact h.left

theorem alpha_nonpositive_blocks_tensor_stability
    (q : TensorQuadraticCoefficients)
    (hMissing : Not q.alphaPositive) :
    Not (tensorPerturbationsStable q) := by
  intro hStable
  exact hMissing hStable.left

theorem beta_nonpositive_blocks_tensor_stability
    (q : TensorQuadraticCoefficients)
    (hMissing : Not q.betaPositive) :
    Not (tensorPerturbationsStable q) := by
  intro hStable
  exact hMissing hStable.right.left.left

theorem c1_plus_c3_not_zero_blocks_visible_luminality
    (q : TensorQuadraticCoefficients)
    (hMissing : Not q.c1PlusC3Zero) :
    Not (visibleGravitationalWaveLuminal q) := by
  intro hLuminal
  exact hMissing hLuminal.left

def tensor_certificate_gives_aether_viability_if_constraints_export
    (c : LinearTensorPerturbationCertificate)
    (hGhost : ghostFreedomClosed (ghostConstraintsFromTensor c))
    (hStability : aetherStabilityClosed (stabilityConstraintsFromTensor c))
    (hObservations : observationsClosed (observationsFromTensor c)) :
    AetherViabilityCertificate :=
  { ghost := ghostConstraintsFromTensor c
    stability := stabilityConstraintsFromTensor c
    observation := observationsFromTensor c
    ghostClosed := hGhost
    stabilityClosed := hStability
    observationClosed := hObservations }

end P0LinearTensorPerturbationStability
end JanusFormal
