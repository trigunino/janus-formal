import Mathlib

namespace JanusFormal.P0EFTJanusRealScalarU1Representation

set_option autoImplicit false

/-- A one-dimensional real orthogonal representation has a skew infinitesimal
generator. In one dimension skewness forces that generator to vanish. -/
theorem one_dimensional_real_u1_generator_is_zero
    (generator : ℝ) (hSkew : generator = -generator) :
    generator = 0 := by
  linarith

/-- Therefore the real scalar used in the minimal candidate must be neutral.
A nontrivially charged scalar would require at least a two-real-dimensional
(equivalently complex) representation and a different field manifest. -/
structure MinimalRealScalarU1Candidate where
  scalarGenerator : ℝ
  scalarCharge : ℝ
  orthogonalInfinitesimalAction : scalarGenerator = -scalarGenerator
  chargeEqualsGenerator : scalarCharge = scalarGenerator

theorem minimal_real_scalar_is_neutral
    (s : MinimalRealScalarU1Candidate) : s.scalarCharge = 0 := by
  rw [s.chargeEqualsGenerator]
  exact one_dimensional_real_u1_generator_is_zero
    s.scalarGenerator s.orthogonalInfinitesimalAction

inductive ScalarRepresentationChoice
  | neutralReal
  | chargedComplex
  deriving DecidableEq

structure MatterRepresentationClosureStatus where
  scalarChoiceFixed : Prop
  scalarMultiplicityFixed : Prop
  fermionContentFixed : Prop
  allGaugeChargesFixed : Prop
  pairedPTLevelsFixed : Prop

def matterRepresentationClosed
    (s : MatterRepresentationClosureStatus) : Prop :=
  s.scalarChoiceFixed ∧
  s.scalarMultiplicityFixed ∧
  s.fermionContentFixed ∧
  s.allGaugeChargesFixed ∧
  s.pairedPTLevelsFixed

end JanusFormal.P0EFTJanusRealScalarU1Representation
