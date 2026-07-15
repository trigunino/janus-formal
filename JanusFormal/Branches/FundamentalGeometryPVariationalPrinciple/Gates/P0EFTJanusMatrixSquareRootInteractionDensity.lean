import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.NoncommRing
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusExplicitReciprocalCrossDensities

/-!
Pointwise matrix realization of Candidate A.  The elementary-symmetric
interaction is defined directly from a four-by-four square-root matrix, and is
proved invariant under an explicitly invertible change of frame.  A witness
ties the root to `g_plus^{-1} g_minus`.

This is a pointwise algebraic realization of the potential scalar and its
coordinate density.  It does not yet prove the density transformation law,
construct a smooth Lorentzian square-root field, or vary the spacetime integral.
-/

namespace JanusFormal
namespace P0EFTJanusMatrixSquareRootInteractionDensity

set_option autoImplicit false

noncomputable section

open Matrix
open P0EFTJanusReciprocalBimetricPotential
open P0EFTJanusExplicitReciprocalCrossDensities

abbrev Matrix4 := Matrix (Fin 4) (Fin 4) ℝ

/-- Newton identities for the four elementary symmetric matrix invariants. -/
def matrixElementary0 (_root : Matrix4) : ℝ := 1

def matrixElementary1 (root : Matrix4) : ℝ :=
  Matrix.trace root

def matrixElementary2 (root : Matrix4) : ℝ :=
  ((Matrix.trace root) ^ 2 - Matrix.trace (root * root)) / 2

def matrixElementary3 (root : Matrix4) : ℝ :=
  ((Matrix.trace root) ^ 3 -
      3 * Matrix.trace root * Matrix.trace (root * root) +
      2 * Matrix.trace (root * root * root)) / 6

def matrixElementary4 (root : Matrix4) : ℝ :=
  Matrix.det root

def matrixSpectralPotential
    (coefficients : PotentialCoefficients) (root : Matrix4) : ℝ :=
  coefficients.beta0 * matrixElementary0 root +
    coefficients.beta1 * matrixElementary1 root +
    coefficients.beta2 * matrixElementary2 root +
    coefficients.beta3 * matrixElementary3 root +
    coefficients.beta4 * matrixElementary4 root

theorem matrixElementary0_diagonal (spectrum : SquareRootSpectrum) :
    matrixElementary0 (Matrix.diagonal spectrum) = elementary0 spectrum := by
  rfl

theorem matrixElementary1_diagonal (spectrum : SquareRootSpectrum) :
    matrixElementary1 (Matrix.diagonal spectrum) = elementary1 spectrum := by
  simp [matrixElementary1, elementary1, Fin.sum_univ_four]

theorem matrixElementary2_diagonal (spectrum : SquareRootSpectrum) :
    matrixElementary2 (Matrix.diagonal spectrum) = elementary2 spectrum := by
  simp [matrixElementary2, elementary2, Matrix.diagonal_mul_diagonal,
    Fin.sum_univ_four]
  ring

theorem matrixElementary3_diagonal (spectrum : SquareRootSpectrum) :
    matrixElementary3 (Matrix.diagonal spectrum) = elementary3 spectrum := by
  simp [matrixElementary3, elementary3, Matrix.diagonal_mul_diagonal,
    Fin.sum_univ_four]
  ring

theorem matrixElementary4_diagonal (spectrum : SquareRootSpectrum) :
    matrixElementary4 (Matrix.diagonal spectrum) = elementary4 spectrum := by
  simp [matrixElementary4, elementary4, Matrix.det_diagonal,
    Fin.prod_univ_four]

/-- The matrix formula extends the exact four-eigenvalue formula. -/
theorem matrixSpectralPotential_diagonal
    (coefficients : PotentialCoefficients)
    (spectrum : SquareRootSpectrum) :
    matrixSpectralPotential coefficients (Matrix.diagonal spectrum) =
      spectralPotential coefficients spectrum := by
  unfold matrixSpectralPotential spectralPotential
  rw [matrixElementary0_diagonal, matrixElementary1_diagonal,
    matrixElementary2_diagonal, matrixElementary3_diagonal,
    matrixElementary4_diagonal]

/-- Explicit inverse-frame witness. -/
structure FrameInverseWitness (frame inverse : Matrix4) : Prop where
  inverse_mul : inverse * frame = 1
  mul_inverse : frame * inverse = 1

def conjugate (inverse frame root : Matrix4) : Matrix4 :=
  inverse * root * frame

theorem conjugate_trace
    (frame inverse root : Matrix4)
    (hFrame : FrameInverseWitness frame inverse) :
    Matrix.trace (conjugate inverse frame root) = Matrix.trace root := by
  unfold conjugate
  calc
    Matrix.trace (inverse * root * frame) =
        Matrix.trace (frame * (inverse * root)) := by
      rw [Matrix.trace_mul_comm]
    _ = Matrix.trace ((frame * inverse) * root) := by
      rw [Matrix.mul_assoc]
    _ = Matrix.trace root := by
      rw [hFrame.mul_inverse, Matrix.one_mul]

theorem conjugate_square
    (frame inverse root : Matrix4)
    (hFrame : FrameInverseWitness frame inverse) :
      conjugate inverse frame root * conjugate inverse frame root =
      conjugate inverse frame (root * root) := by
  have hCancel : ∀ x : Matrix4, frame * (inverse * x) = x := by
    intro x
    rw [← Matrix.mul_assoc, hFrame.mul_inverse, Matrix.one_mul]
  unfold conjugate
  noncomm_ring [hCancel]

theorem conjugate_cube
    (frame inverse root : Matrix4)
    (hFrame : FrameInverseWitness frame inverse) :
    conjugate inverse frame root * conjugate inverse frame root *
        conjugate inverse frame root =
      conjugate inverse frame (root * root * root) := by
  have hCancel : ∀ x : Matrix4, frame * (inverse * x) = x := by
    intro x
    rw [← Matrix.mul_assoc, hFrame.mul_inverse, Matrix.one_mul]
  unfold conjugate
  noncomm_ring [hCancel]

theorem conjugate_det
    (frame inverse root : Matrix4)
    (hFrame : FrameInverseWitness frame inverse) :
    Matrix.det (conjugate inverse frame root) = Matrix.det root := by
  have hDetInverse : Matrix.det inverse * Matrix.det frame = 1 := by
    calc
      Matrix.det inverse * Matrix.det frame =
          Matrix.det (inverse * frame) := by rw [Matrix.det_mul]
      _ = 1 := by rw [hFrame.inverse_mul, Matrix.det_one]
  unfold conjugate
  rw [Matrix.det_mul, Matrix.det_mul]
  calc
    Matrix.det inverse * Matrix.det root * Matrix.det frame =
        (Matrix.det inverse * Matrix.det frame) * Matrix.det root := by ring
    _ = Matrix.det root := by rw [hDetInverse, one_mul]

theorem conjugate_square_trace
    (frame inverse root : Matrix4)
    (hFrame : FrameInverseWitness frame inverse) :
    Matrix.trace
        (conjugate inverse frame root * conjugate inverse frame root) =
      Matrix.trace (root * root) := by
  rw [conjugate_square frame inverse root hFrame]
  exact conjugate_trace frame inverse (root * root) hFrame

theorem conjugate_cube_trace
    (frame inverse root : Matrix4)
    (hFrame : FrameInverseWitness frame inverse) :
    Matrix.trace
        (conjugate inverse frame root * conjugate inverse frame root *
          conjugate inverse frame root) =
      Matrix.trace (root * root * root) := by
  rw [conjugate_cube frame inverse root hFrame]
  exact conjugate_trace frame inverse (root * root * root) hFrame

theorem conjugate_matrixElementary0
    (frame inverse root : Matrix4) :
    matrixElementary0 (conjugate inverse frame root) =
      matrixElementary0 root := by
  rfl

theorem conjugate_matrixElementary1
    (frame inverse root : Matrix4)
    (hFrame : FrameInverseWitness frame inverse) :
    matrixElementary1 (conjugate inverse frame root) =
      matrixElementary1 root := by
  exact conjugate_trace frame inverse root hFrame

theorem conjugate_matrixElementary2
    (frame inverse root : Matrix4)
    (hFrame : FrameInverseWitness frame inverse) :
    matrixElementary2 (conjugate inverse frame root) =
      matrixElementary2 root := by
  unfold matrixElementary2
  rw [conjugate_trace frame inverse root hFrame,
    conjugate_square_trace frame inverse root hFrame]

theorem conjugate_matrixElementary3
    (frame inverse root : Matrix4)
    (hFrame : FrameInverseWitness frame inverse) :
    matrixElementary3 (conjugate inverse frame root) =
      matrixElementary3 root := by
  unfold matrixElementary3
  rw [conjugate_trace frame inverse root hFrame,
    conjugate_square_trace frame inverse root hFrame,
    conjugate_cube_trace frame inverse root hFrame]

theorem conjugate_matrixElementary4
    (frame inverse root : Matrix4)
    (hFrame : FrameInverseWitness frame inverse) :
    matrixElementary4 (conjugate inverse frame root) =
      matrixElementary4 root := by
  exact conjugate_det frame inverse root hFrame

/-- The pointwise interaction scalar is invariant under an explicitly
invertible simultaneous frame change. -/
theorem matrixSpectralPotential_conjugate
    (coefficients : PotentialCoefficients)
    (frame inverse root : Matrix4)
    (hFrame : FrameInverseWitness frame inverse) :
    matrixSpectralPotential coefficients (conjugate inverse frame root) =
      matrixSpectralPotential coefficients root := by
  unfold matrixSpectralPotential
  rw [conjugate_matrixElementary0, conjugate_matrixElementary1 frame inverse root hFrame,
    conjugate_matrixElementary2 frame inverse root hFrame,
    conjugate_matrixElementary3 frame inverse root hFrame,
    conjugate_matrixElementary4 frame inverse root hFrame]

/-- A supplied branch selector must make the square root unique at each target.
Constructing the principal Lorentzian branch is a separate analytic task. -/
structure SquareRootBranch where
  admissible : Matrix4 → Prop
  unique {left right target : Matrix4} :
    admissible left → admissible right →
      left * left = target → right * right = target → left = right

/-- Pointwise nondegenerate fields sufficient to state a branch-selected
square-root equation without an opaque inverse operation. -/
structure SquareRootPointData where
  plusMetric : Matrix4
  plusInverse : Matrix4
  minusMetric : Matrix4
  minusInverse : Matrix4
  root : Matrix4
  rootInverse : Matrix4
  branch : SquareRootBranch
  plusInverseWitness : FrameInverseWitness plusMetric plusInverse
  minusInverseWitness : FrameInverseWitness minusMetric minusInverse
  rootInverseWitness : FrameInverseWitness root rootInverse
  plusMetricSymmetric : plusMetric.transpose = plusMetric
  minusMetricSymmetric : minusMetric.transpose = minusMetric
  rootDeterminantPositive : 0 < Matrix.det root
  squareRootEquation : root * root = plusInverse * minusMetric
  rootAdmissible : branch.admissible root

theorem branch_selected_squareRoot_unique
    (branch : SquareRootBranch) (left right target : Matrix4)
    (hLeft : branch.admissible left) (hRight : branch.admissible right)
    (hLeftSquare : left * left = target)
    (hRightSquare : right * right = target) :
    left = right :=
  branch.unique hLeft hRight hLeftSquare hRightSquare

theorem minusMetric_det_eq_plusMetric_det_mul_root_det_sq
    (data : SquareRootPointData) :
    Matrix.det data.minusMetric =
      Matrix.det data.plusMetric * (Matrix.det data.root) ^ 2 := by
  have hRootDet :
      Matrix.det data.root * Matrix.det data.root =
        Matrix.det data.plusInverse * Matrix.det data.minusMetric := by
    simpa [Matrix.det_mul] using congrArg Matrix.det data.squareRootEquation
  have hPlusDet :
      Matrix.det data.plusInverse * Matrix.det data.plusMetric = 1 := by
    calc
      Matrix.det data.plusInverse * Matrix.det data.plusMetric =
          Matrix.det (data.plusInverse * data.plusMetric) := by
        rw [Matrix.det_mul]
      _ = 1 := by
        rw [data.plusInverseWitness.inverse_mul, Matrix.det_one]
  calc
    Matrix.det data.minusMetric =
        (Matrix.det data.plusInverse * Matrix.det data.plusMetric) *
          Matrix.det data.minusMetric := by rw [hPlusDet, one_mul]
    _ = Matrix.det data.plusMetric *
        (Matrix.det data.plusInverse * Matrix.det data.minusMetric) := by ring
    _ = Matrix.det data.plusMetric *
        (Matrix.det data.root * Matrix.det data.root) := by rw [← hRootDet]
    _ = Matrix.det data.plusMetric * (Matrix.det data.root) ^ 2 := by ring

/-- The positive-determinant branch gives the exact relation between the two
metric coordinate-volume factors. -/
theorem sqrt_abs_det_minus_eq_sqrt_abs_det_plus_mul_det_root
    (data : SquareRootPointData) :
    Real.sqrt |Matrix.det data.minusMetric| =
      Real.sqrt |Matrix.det data.plusMetric| * Matrix.det data.root := by
  rw [minusMetric_det_eq_plusMetric_det_mul_root_det_sq, abs_mul, abs_pow,
    Real.sqrt_mul (abs_nonneg (Matrix.det data.plusMetric)),
    Real.sqrt_sq (abs_nonneg (Matrix.det data.root)),
    abs_of_pos data.rootDeterminantPositive]

theorem diagonal_volumeRatio_is_metric_measure_ratio
    (data : SquareRootPointData) (spectrum : SquareRootSpectrum)
    (hRoot : data.root = Matrix.diagonal spectrum) :
    Real.sqrt |Matrix.det data.minusMetric| =
      Real.sqrt |Matrix.det data.plusMetric| * volumeRatio spectrum := by
  have hDet : Matrix.det (Matrix.diagonal spectrum) = volumeRatio spectrum := by
    simpa [matrixElementary4, volumeRatio] using
      matrixElementary4_diagonal spectrum
  rw [sqrt_abs_det_minus_eq_sqrt_abs_det_plus_mul_det_root, hRoot, hDet]

theorem diagonalizable_volumeRatio_is_metric_measure_ratio
    (data : SquareRootPointData)
    (frame inverse : Matrix4) (spectrum : SquareRootSpectrum)
    (hFrame : FrameInverseWitness frame inverse)
    (hRoot : data.root =
      conjugate inverse frame (Matrix.diagonal spectrum)) :
    Real.sqrt |Matrix.det data.minusMetric| =
      Real.sqrt |Matrix.det data.plusMetric| * volumeRatio spectrum := by
  have hDet : Matrix.det (Matrix.diagonal spectrum) = volumeRatio spectrum := by
    simpa [matrixElementary4, volumeRatio] using
      matrixElementary4_diagonal spectrum
  rw [sqrt_abs_det_minus_eq_sqrt_abs_det_plus_mul_det_root, hRoot,
    conjugate_det frame inverse (Matrix.diagonal spectrum) hFrame, hDet]

theorem matrixSpectralPotential_of_diagonalizable_root
    (coefficients : PotentialCoefficients)
    (data : SquareRootPointData)
    (frame inverse : Matrix4) (spectrum : SquareRootSpectrum)
    (hFrame : FrameInverseWitness frame inverse)
    (hRoot : data.root =
      conjugate inverse frame (Matrix.diagonal spectrum)) :
    matrixSpectralPotential coefficients data.root =
      spectralPotential coefficients spectrum := by
  rw [hRoot, matrixSpectralPotential_conjugate coefficients frame inverse
    (Matrix.diagonal spectrum) hFrame, matrixSpectralPotential_diagonal]

/-- Explicit common interaction density at one coordinate point. -/
def matrixCommonInteractionDensity
    (interactionScale : ℝ)
    (coefficients : PotentialCoefficients)
    (data : SquareRootPointData) : ℝ :=
  -interactionScale * Real.sqrt |Matrix.det data.plusMetric| *
    matrixSpectralPotential coefficients data.root

/-- End-to-end naming/measure bridge on a diagonal root: the matrix coordinate
density contains exactly one plus-sector volume factor multiplying the
measure-free common interaction potential. -/
theorem matrixCommonInteractionDensity_of_diagonal_root
    (interactionScale : ℝ)
    (coefficients : PotentialCoefficients)
    (data : SquareRootPointData)
    (spectrum : SquareRootSpectrum)
    (hRoot : data.root = Matrix.diagonal spectrum) :
    matrixCommonInteractionDensity interactionScale coefficients data =
      Real.sqrt |Matrix.det data.plusMetric| *
        commonInteractionPotential interactionScale coefficients spectrum := by
  rw [matrixCommonInteractionDensity, hRoot,
    matrixSpectralPotential_diagonal, commonInteractionPotential]
  ring

theorem matrixCommonInteractionDensity_of_diagonalizable_root
    (interactionScale : ℝ)
    (coefficients : PotentialCoefficients)
    (data : SquareRootPointData)
    (frame inverse : Matrix4) (spectrum : SquareRootSpectrum)
    (hFrame : FrameInverseWitness frame inverse)
    (hRoot : data.root =
      conjugate inverse frame (Matrix.diagonal spectrum)) :
    matrixCommonInteractionDensity interactionScale coefficients data =
      Real.sqrt |Matrix.det data.plusMetric| *
        commonInteractionPotential interactionScale coefficients spectrum := by
  rw [matrixCommonInteractionDensity,
    matrixSpectralPotential_of_diagonalizable_root coefficients data
      frame inverse spectrum hFrame hRoot,
    commonInteractionPotential]
  ring

/-- End-to-end bridge: on supplied nondegenerate diagonalizable point data,
the two M30 half-slots weighted by the actual two metric volumes sum to the
single matrix coordinate density. -/
theorem diagonalizable_two_M30_slots_eq_matrixCommonInteractionDensity
    {MatterPlus MatterMinus : Type*}
    (interactionScale : ℝ)
    (coefficients : PotentialCoefficients)
    (data : SquareRootPointData)
    (frame inverse : Matrix4)
    (spectrum : NonzeroSquareRootSpectrum)
    (hFrame : FrameInverseWitness frame inverse)
    (hRoot : data.root =
      conjugate inverse frame (Matrix.diagonal spectrum.1))
    (matterPlus : MatterPlus) (matterMinus : MatterMinus) :
    Real.sqrt |Matrix.det data.plusMetric| *
          plusCrossDensity interactionScale coefficients spectrum
            matterPlus matterMinus +
        Real.sqrt |Matrix.det data.minusMetric| *
          minusCrossDensity interactionScale coefficients spectrum
            matterPlus matterMinus =
      matrixCommonInteractionDensity interactionScale coefficients data := by
  have hVolume := diagonalizable_volumeRatio_is_metric_measure_ratio data
    frame inverse spectrum.1 hFrame hRoot
  calc
    Real.sqrt |Matrix.det data.plusMetric| *
          plusCrossDensity interactionScale coefficients spectrum
            matterPlus matterMinus +
        Real.sqrt |Matrix.det data.minusMetric| *
          minusCrossDensity interactionScale coefficients spectrum
            matterPlus matterMinus =
      Real.sqrt |Matrix.det data.plusMetric| *
          plusCrossDensity interactionScale coefficients spectrum
            matterPlus matterMinus +
        (Real.sqrt |Matrix.det data.plusMetric| * volumeRatio spectrum.1) *
          minusCrossDensity interactionScale coefficients spectrum
            matterPlus matterMinus := by rw [hVolume]
    _ = Real.sqrt |Matrix.det data.plusMetric| *
        commonInteractionPotential interactionScale coefficients spectrum.1 :=
      two_M30_density_slots_eq_one_common_interaction interactionScale
        (Real.sqrt |Matrix.det data.plusMetric|) coefficients spectrum
        matterPlus matterMinus
    _ = matrixCommonInteractionDensity interactionScale coefficients data :=
      (matrixCommonInteractionDensity_of_diagonalizable_root interactionScale
        coefficients data frame inverse spectrum.1 hFrame hRoot).symm

/- Lorentz signature, construction/nonemptiness of a principal branch, full
matrix reciprocity, the coordinate-density transformation law, smooth
dependence of `root`, integration and variation are deliberately not inferred
from this pointwise witness. -/

end

end P0EFTJanusMatrixSquareRootInteractionDensity
end JanusFormal
