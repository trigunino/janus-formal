import Mathlib.LinearAlgebra.UnitaryGroup
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusSpin2CircleModel

namespace JanusFormal
namespace P0EFTJanusCircleSO2Equivalence

set_option autoImplicit false

noncomputable section

open P0EFTJanusCentralLiftCocycleObstruction
open P0EFTJanusCirclePhaseTwoTorsion
open P0EFTJanusSpin2CircleModel

/-- The concrete matrix group `SO(2)`. -/
abbrev MatrixSO2 := Matrix.specialOrthogonalGroup (Fin 2) ℝ

/-- Standard real rotation matrix attached to a unit complex number. -/
def circleRotationMatrix (phase : Circle) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![((phase : ℂ).re), -((phase : ℂ).im);
     ((phase : ℂ).im),  ((phase : ℂ).re)]

/-- The standard rotation matrix of a circle phase is special orthogonal. -/
theorem circleRotationMatrix_mem_specialOrthogonal
    (phase : Circle) :
    circleRotationMatrix phase ∈ MatrixSO2 := by
  change
    !![((phase : ℂ).re), -((phase : ℂ).im);
       ((phase : ℂ).im),  ((phase : ℂ).re)] ∈ MatrixSO2
  rw [Matrix.of_mem_specialOrthogonalGroup_fin_two_iff]
  refine ⟨rfl, rfl, ?_⟩
  have hNormSq := Circle.normSq_coe phase
  simpa [Complex.normSq_apply, pow_two] using hNormSq

/-- Circle phase regarded as an `SO(2)` rotation. -/
def circleToMatrixSO2 (phase : Circle) : MatrixSO2 :=
  ⟨circleRotationMatrix phase,
    circleRotationMatrix_mem_specialOrthogonal phase⟩

@[simp]
theorem circleToMatrixSO2_one :
    circleToMatrixSO2 1 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [circleToMatrixSO2, circleRotationMatrix]

@[simp]
theorem circleToMatrixSO2_mul
    (first second : Circle) :
    circleToMatrixSO2 (first * second) =
      circleToMatrixSO2 first * circleToMatrixSO2 second := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [circleToMatrixSO2, circleRotationMatrix] <;>
    ring

/-- The standard circle-to-rotation assignment as a group homomorphism. -/
def circleToMatrixSO2Hom : Circle →* MatrixSO2 where
  toFun := circleToMatrixSO2
  map_one' := circleToMatrixSO2_one
  map_mul' := circleToMatrixSO2_mul

@[simp]
theorem circleToMatrixSO2Hom_apply (phase : Circle) :
    circleToMatrixSO2Hom phase = circleToMatrixSO2 phase := by
  rfl

/-- The real and imaginary parts of a matrix rotation recover its circle phase. -/
def matrixSO2Complex (rotation : MatrixSO2) : ℂ :=
  ⟨rotation.1 0 0, rotation.1 1 0⟩

/-- The complex number extracted from an `SO(2)` matrix has norm one. -/
theorem matrixSO2Complex_norm (rotation : MatrixSO2) :
    ‖matrixSO2Complex rotation‖ = 1 := by
  have hSO :=
    (Matrix.mem_specialOrthogonalGroup_fin_two_iff).1 rotation.2
  have hSquare := hSO.2.2
  rw [hSO.2.1] at hSquare
  have hNormSq : Complex.normSq (matrixSO2Complex rotation) = 1 := by
    simp only [matrixSO2Complex, Complex.normSq]
    change
      rotation.1 0 0 * rotation.1 0 0 +
          rotation.1 1 0 * rotation.1 1 0 = 1
    nlinarith
  rw [Complex.norm_def, hNormSq]
  norm_num

/-- Inverse map from a special orthogonal `2 × 2` matrix to its unit complex
phase. -/
def matrixSO2ToCircle (rotation : MatrixSO2) : Circle where
  val := matrixSO2Complex rotation
  property := mem_sphere_zero_iff_norm.mpr
    (matrixSO2Complex_norm rotation)

@[simp]
theorem matrixSO2ToCircle_circleToMatrixSO2
    (phase : Circle) :
    matrixSO2ToCircle (circleToMatrixSO2 phase) = phase := by
  apply Circle.ext
  apply Complex.ext <;> rfl

@[simp]
theorem circleToMatrixSO2_matrixSO2ToCircle
    (rotation : MatrixSO2) :
    circleToMatrixSO2 (matrixSO2ToCircle rotation) = rotation := by
  have hSO :=
    (Matrix.mem_specialOrthogonalGroup_fin_two_iff).1 rotation.2
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  · rfl
  · change -rotation.1 1 0 = rotation.1 0 1
    exact hSO.2.1.symm
  · rfl
  · change rotation.1 0 0 = rotation.1 1 1
    exact hSO.1

/-- Explicit group equivalence `U(1) ≃ SO(2)`. -/
def circleEquivMatrixSO2 : Circle ≃* MatrixSO2 where
  toFun := circleToMatrixSO2
  invFun := matrixSO2ToCircle
  left_inv := matrixSO2ToCircle_circleToMatrixSO2
  right_inv := circleToMatrixSO2_matrixSO2ToCircle
  map_mul' := circleToMatrixSO2_mul

/-- The circle-to-matrix map is injective. -/
theorem circleToMatrixSO2_injective :
    Function.Injective circleToMatrixSO2 :=
  circleEquivMatrixSO2.injective

/-- The circle-to-matrix map is surjective. -/
theorem circleToMatrixSO2_surjective :
    Function.Surjective circleToMatrixSO2 :=
  circleEquivMatrixSO2.surjective

/-- Matrix-valued rank-two Spin projection: first square the circle phase, then
identify the result with its `SO(2)` rotation matrix. -/
def spin2ToMatrixSO2Projection : Circle →* MatrixSO2 :=
  circleToMatrixSO2Hom.comp circleSquaringProjection

@[simp]
theorem spin2ToMatrixSO2Projection_apply (phase : Circle) :
    spin2ToMatrixSO2Projection phase =
      circleToMatrixSO2 (phase * phase) := by
  rfl

/-- The matrix-valued rank-two Spin projection is surjective. -/
theorem spin2ToMatrixSO2Projection_surjective :
    Function.Surjective spin2ToMatrixSO2Projection := by
  intro rotation
  rcases circleToMatrixSO2_surjective rotation with ⟨phase, hPhase⟩
  rcases circleSquaringProjection_surjective phase with ⟨root, hRoot⟩
  refine ⟨root, ?_⟩
  change circleToMatrixSO2 (circleSquaringProjection root) = rotation
  rw [hRoot, hPhase]

/-- Concrete central double cover `Spin(2) → SO(2)` in matrix form. -/
def spin2MatrixSO2DoubleCover :
    CentralDoubleCoverData Circle MatrixSO2 where
  projection := spin2ToMatrixSO2Projection
  kernel_central := by
    intro phase hKernel other
    exact mul_comm _ _
  minusOne := -1
  minusOne_mem_kernel := by
    change spin2ToMatrixSO2Projection (-1 : Circle) = 1
    change circleToMatrixSO2 (circleSquaringProjection (-1 : Circle)) = 1
    have hSquare : circleSquaringProjection (-1 : Circle) = 1 := by
      apply Circle.ext
      norm_num
    rw [hSquare, circleToMatrixSO2_one]
  minusOne_ne_one := Circle.neg_ne_self 1
  minusOne_sq := by
    apply Circle.ext
    norm_num
  kernel_dichotomy := by
    intro phase hKernel
    change spin2ToMatrixSO2Projection phase = 1 at hKernel
    have hMatrix :
        circleToMatrixSO2 (circleSquaringProjection phase) =
          circleToMatrixSO2 1 := by
      simpa [spin2ToMatrixSO2Projection,
        circleToMatrixSO2Hom] using hKernel
    have hCircle := circleToMatrixSO2_injective hMatrix
    change phase * phase = 1 at hCircle
    exact circle_square_eq_one_dichotomy phase hCircle

/-- The matrix model has the same two-sheeted fiber classification. -/
theorem spin2ToMatrixSO2Projection_eq_iff
    (first second : Circle) :
    spin2ToMatrixSO2Projection first =
        spin2ToMatrixSO2Projection second ↔
      first = second ∨ first = -second := by
  change
    circleToMatrixSO2 (circleSquaringProjection first) =
        circleToMatrixSO2 (circleSquaringProjection second) ↔ _
  rw [circleToMatrixSO2_injective.eq_iff,
    circleSquaringProjection_eq_iff]

/-- Exact progress boundary after the matrix `SO(2)` identification. -/
structure CircleSO2EquivalenceStatus where
  standardRotationMatrixDefined : Prop
  rotationMatrixSpecialOrthogonalProved : Prop
  circleToSO2HomConstructed : Prop
  inversePhaseMapConstructed : Prop
  circleSO2GroupEquivalenceProved : Prop
  matrixSpin2ProjectionSurjective : Prop
  matrixSpin2KernelClassified : Prop
  matrixSpin2DoubleCoverConstructed : Prop
  cliffordSpin2IdentificationProved : Prop
  smoothLieGroupEquivalenceProved : Prop
  principalBundleLiftConstructed : Prop

/-- Closure of the geometric matrix/Clifford rank-two Spin theorem. -/
def circleSO2EquivalenceClosed
    (s : CircleSO2EquivalenceStatus) : Prop :=
  s.standardRotationMatrixDefined /\
  s.rotationMatrixSpecialOrthogonalProved /\
  s.circleToSO2HomConstructed /\
  s.inversePhaseMapConstructed /\
  s.circleSO2GroupEquivalenceProved /\
  s.matrixSpin2ProjectionSurjective /\
  s.matrixSpin2KernelClassified /\
  s.matrixSpin2DoubleCoverConstructed /\
  s.cliffordSpin2IdentificationProved /\
  s.smoothLieGroupEquivalenceProved /\
  s.principalBundleLiftConstructed

/-- The explicit matrix equivalence still does not identify the circle model
with the even Clifford-algebra definition of `Spin(2)`. -/
theorem missing_clifford_spin2_blocks_full_rank_two_model
    (s : CircleSO2EquivalenceStatus)
    (hMissing : Not s.cliffordSpin2IdentificationProved) :
    Not (circleSO2EquivalenceClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.2.2.1

end

end P0EFTJanusCircleSO2Equivalence
end JanusFormal
