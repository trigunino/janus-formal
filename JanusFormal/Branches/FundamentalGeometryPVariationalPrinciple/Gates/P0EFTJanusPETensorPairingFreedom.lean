import Mathlib
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPEInvariantPairings

namespace JanusFormal
namespace P0EFTJanusPETensorPairingFreedom

set_option autoImplicit false

open P0EFTJanusPEInvariantPairings

/-- Diagonal traceless-tensor contraction in `(a,b)` coordinates. -/
def tensorDiagonalPairing
    (first second : TracelessTensor5) : ℝ :=
  2 * first.a * second.a +
    first.a * second.b +
    first.b * second.a +
    2 * first.b * second.b

/-- Off-diagonal traceless-tensor contraction. -/
def tensorOffDiagonalPairing
    (first second : TracelessTensor5) : ℝ :=
  2 *
    (first.xy * second.xy +
      first.xz * second.xz +
      first.yz * second.yz)

/-- Two-parameter pairing left invariant by signed coordinate permutations. -/
def combinedTensorPairing
    (diagonalScale offDiagonalScale : ℝ)
    (first second : TracelessTensor5) : ℝ :=
  diagonalScale * tensorDiagonalPairing first second +
    offDiagonalScale * tensorOffDiagonalPairing first second

/-- Cubic/signed-permutation invariance. -/
structure CubicTensorPairingInvariant
    (pairing : TracelessTensor5 → TracelessTensor5 → ℝ) : Prop where
  flipXInvariant :
    ∀ first second,
      pairing (tensorFlipX first) (tensorFlipX second) =
        pairing first second
  flipYInvariant :
    ∀ first second,
      pairing (tensorFlipY first) (tensorFlipY second) =
        pairing first second
  swapXYInvariant :
    ∀ first second,
      pairing (tensorSwapXY first) (tensorSwapXY second) =
        pairing first second
  swapYZInvariant :
    ∀ first second,
      pairing (tensorSwapYZ first) (tensorSwapYZ second) =
        pairing first second

/-- Both diagonal and off-diagonal normalizations survive the cubic subgroup. -/
theorem combined_tensor_pairing_cubic_invariant
    (diagonalScale offDiagonalScale : ℝ) :
    CubicTensorPairingInvariant
      (combinedTensorPairing diagonalScale offDiagonalScale) := by
  refine
    { flipXInvariant := ?_
      flipYInvariant := ?_
      swapXYInvariant := ?_
      swapYZInvariant := ?_ }
  all_goals
    intro first second
    rcases first with ⟨firstA, firstB, firstXY, firstXZ, firstYZ⟩
    rcases second with ⟨secondA, secondB, secondXY, secondXZ, secondYZ⟩
    simp [combinedTensorPairing, tensorDiagonalPairing,
      tensorOffDiagonalPairing, tensorFlipX, tensorFlipY,
      tensorSwapXY, tensorSwapYZ]
    ring

/-- The diagonal test recovers the first scale. -/
theorem diagonal_test_recovers_scale
    (diagonalScale offDiagonalScale : ℝ) :
    combinedTensorPairing diagonalScale offDiagonalScale
        tensorBasisA tensorBasisA =
      2 * diagonalScale := by
  norm_num [combinedTensorPairing, tensorDiagonalPairing,
    tensorOffDiagonalPairing, tensorBasisA]

/-- The off-diagonal test recovers the second scale. -/
theorem off_diagonal_test_recovers_scale
    (diagonalScale offDiagonalScale : ℝ) :
    combinedTensorPairing diagonalScale offDiagonalScale
        tensorBasisXY tensorBasisXY =
      2 * offDiagonalScale := by
  norm_num [combinedTensorPairing, tensorDiagonalPairing,
    tensorOffDiagonalPairing, tensorBasisXY]

/-- The two cubic-invariant coefficients are genuinely independent. -/
theorem combined_tensor_parameters_unique
    (firstDiagonal firstOffDiagonal
      secondDiagonal secondOffDiagonal : ℝ)
    (hEqual :
      ∀ first second,
        combinedTensorPairing firstDiagonal firstOffDiagonal first second =
          combinedTensorPairing secondDiagonal secondOffDiagonal first second) :
    firstDiagonal = secondDiagonal /\
      firstOffDiagonal = secondOffDiagonal := by
  have hDiagonal := hEqual tensorBasisA tensorBasisA
  have hOffDiagonal := hEqual tensorBasisXY tensorBasisXY
  rw [diagonal_test_recovers_scale,
    diagonal_test_recovers_scale] at hDiagonal
  rw [off_diagonal_test_recovers_scale,
    off_diagonal_test_recovers_scale] at hOffDiagonal
  constructor <;> linarith

/-- Exact rational rotation with cosine `3/5` and sine `4/5`. -/
noncomputable def tensorRotateZ345
    (tensor : TracelessTensor5) : TracelessTensor5 :=
  { a := (9 / 25 : ℝ) * tensor.a +
      (16 / 25 : ℝ) * tensor.b -
      (24 / 25 : ℝ) * tensor.xy
    b := (16 / 25 : ℝ) * tensor.a +
      (9 / 25 : ℝ) * tensor.b +
      (24 / 25 : ℝ) * tensor.xy
    xy := (12 / 25 : ℝ) * tensor.a -
      (12 / 25 : ℝ) * tensor.b -
      (7 / 25 : ℝ) * tensor.xy
    xz := (3 / 5 : ℝ) * tensor.xz -
      (4 / 5 : ℝ) * tensor.yz
    yz := (4 / 5 : ℝ) * tensor.xz +
      (3 / 5 : ℝ) * tensor.yz }

/-- One generic continuous rotation ties the diagonal and off-diagonal scales. -/
theorem rotation_invariance_forces_equal_tensor_scales
    (diagonalScale offDiagonalScale : ℝ)
    (hRotation :
      combinedTensorPairing diagonalScale offDiagonalScale
          (tensorRotateZ345 tensorBasisA)
          (tensorRotateZ345 tensorBasisA) =
        combinedTensorPairing diagonalScale offDiagonalScale
          tensorBasisA tensorBasisA) :
    diagonalScale = offDiagonalScale := by
  norm_num [combinedTensorPairing, tensorDiagonalPairing,
    tensorOffDiagonalPairing, tensorRotateZ345,
    tensorBasisA] at hRotation
  linarith

/-- Frobenius contraction, up to one overall scale. -/
def frobeniusTensorPairing
    (coefficient : ℝ)
    (first second : TracelessTensor5) : ℝ :=
  combinedTensorPairing coefficient coefficient first second

/-- Cubic invariance plus one non-cubic rotation collapses the family to Frobenius. -/
theorem rotation_compatible_pairing_is_frobenius
    (diagonalScale offDiagonalScale : ℝ)
    (hRotation :
      combinedTensorPairing diagonalScale offDiagonalScale
          (tensorRotateZ345 tensorBasisA)
          (tensorRotateZ345 tensorBasisA) =
        combinedTensorPairing diagonalScale offDiagonalScale
          tensorBasisA tensorBasisA) :
    ∀ first second,
      combinedTensorPairing diagonalScale offDiagonalScale first second =
        frobeniusTensorPairing diagonalScale first second := by
  have hScales := rotation_invariance_forces_equal_tensor_scales
    diagonalScale offDiagonalScale hRotation
  intro first second
  rw [hScales]
  rfl

/--
P.E tensor verdict: the finite signed-permutation subgroup leaves two invariant
norms, one on diagonal traceless tensors and one on off-diagonal tensors.  A
generic continuous rotation identifies them, leaving the Frobenius pairing up
to one scale.  Thus PT/Z4 or finite monodromy alone cannot justify tensor
pairing uniqueness; the full tangent rotation structure is essential.
-/
structure TensorPairingPhysicalStatus where
  tracelessTensorRepresentationConstructed : Prop
  cubicInvariantSpaceComputed : Prop
  twoCubicPairingsExhibited : Prop
  continuousRotationActionConstructed : Prop
  fullO3InvariantSpaceComputed : Prop
  frobeniusUniquenessProved : Prop
  normalizationFixedMicroscopically : Prop


def tensorPairingPhysicalClosure
    (s : TensorPairingPhysicalStatus) : Prop :=
  s.tracelessTensorRepresentationConstructed /\
  s.cubicInvariantSpaceComputed /\
  s.twoCubicPairingsExhibited /\
  s.continuousRotationActionConstructed /\
  s.fullO3InvariantSpaceComputed /\
  s.frobeniusUniquenessProved /\
  s.normalizationFixedMicroscopically

end P0EFTJanusPETensorPairingFreedom
end JanusFormal
