import Mathlib

namespace JanusFormal
namespace P0EFTJanusReciprocalBimetricPotential

set_option autoImplicit false

/-- Coefficients of the four-dimensional elementary-symmetric bimetric potential. -/
structure PotentialCoefficients where
  beta0 : ℝ
  beta1 : ℝ
  beta2 : ℝ
  beta3 : ℝ
  beta4 : ℝ

/-- Exchange of the two metric sectors reverses the coefficient list. -/
def reversed (b : PotentialCoefficients) : PotentialCoefficients :=
  { beta0 := b.beta4
    beta1 := b.beta3
    beta2 := b.beta2
    beta3 := b.beta1
    beta4 := b.beta0 }

@[simp] theorem reversed_involutive (b : PotentialCoefficients) :
    reversed (reversed b) = b := by
  cases b
  rfl

/-- Potential density on a proportional branch `f = c^2 g` in four dimensions. -/
def proportionalPotential
    (b : PotentialCoefficients) (c : ℝ) : ℝ :=
  b.beta0 + 4 * b.beta1 * c + 6 * b.beta2 * c ^ 2 +
    4 * b.beta3 * c ^ 3 + b.beta4 * c ^ 4

/-- Exact reciprocal identity under metric exchange and coefficient reversal. -/
theorem reciprocal_potential_identity
    (b : PotentialCoefficients)
    (c : ℝ)
    (hC : c ≠ 0) :
    c ^ 4 * proportionalPotential (reversed b) (1 / c) =
      proportionalPotential b c := by
  unfold proportionalPotential reversed
  field_simp [hC]
  ring

/-- PT-symmetric coefficient data. -/
def PTSymmetric (b : PotentialCoefficients) : Prop :=
  b.beta0 = b.beta4 /\ b.beta1 = b.beta3

/-- PT-symmetric coefficients are fixed by reversal. -/
theorem pt_symmetric_coefficients_are_reversal_fixed
    (b : PotentialCoefficients)
    (hPT : PTSymmetric b) :
    reversed b = b := by
  rcases hPT with ⟨h04, h13⟩
  cases b
  simp_all [reversed]

/-- Self-reciprocity of a PT-symmetric proportional potential. -/
theorem pt_symmetric_potential_is_self_reciprocal
    (b : PotentialCoefficients)
    (c : ℝ)
    (hC : c ≠ 0)
    (hPT : PTSymmetric b) :
    c ^ 4 * proportionalPotential b (1 / c) =
      proportionalPotential b c := by
  have hFixed := pt_symmetric_coefficients_are_reversal_fixed b hPT
  have hIdentity := reciprocal_potential_identity b c hC
  rw [hFixed] at hIdentity
  exact hIdentity

/--
This potential is a mathematically controlled candidate completion, not an
identity already derived from the published Janus cross-source notation.  It
must reproduce the determinant-weighted weak-field signs and the desired
massless/local-GR branch before it can replace the open interaction functionals.
-/
structure ReciprocalPotentialCompletionStatus where
  solderMapOrCommonManifoldComparisonDefined : Prop
  matrixSquareRootBranchDefined : Prop
  elementarySymmetricPotentialDerived : Prop
  ptCoefficientSymmetryDerived : Prop
  noGhostConstraintProved : Prop
  janusNewtonianSignMatrixRecovered : Prop
  localGRLimitRecovered : Prop
  finiteBoundaryJunctionDerived : Prop
  alphaBranchSelected : Prop


def reciprocalPotentialCompletionClosed
    (s : ReciprocalPotentialCompletionStatus) : Prop :=
  s.solderMapOrCommonManifoldComparisonDefined /\
  s.matrixSquareRootBranchDefined /\
  s.elementarySymmetricPotentialDerived /\
  s.ptCoefficientSymmetryDerived /\
  s.noGhostConstraintProved /\
  s.janusNewtonianSignMatrixRecovered /\
  s.localGRLimitRecovered /\
  s.finiteBoundaryJunctionDerived /\
  s.alphaBranchSelected

end P0EFTJanusReciprocalBimetricPotential
end JanusFormal
