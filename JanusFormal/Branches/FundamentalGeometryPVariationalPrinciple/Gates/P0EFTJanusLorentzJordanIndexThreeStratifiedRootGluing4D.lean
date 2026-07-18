import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusLorentzJordanStratifiedRootGluing4D

/-!
# The index-three unipotent Jordan root stratum

For `N = A - I` with `N^3 = 0`, the positive binomial root truncates to
`I + N/2 - N^2/8`.  This gate closes that complete algebraic envelope,
proves similarity equivariance, supplies a finite inverse Sylvester operator,
and glues it to the already closed positive and index-two selectors.

The exact strict new stratum is `N^3 = 0` and `N^2 != 0`; an explicit
nonempty size-three Jordan block is included.  As in the index-two gate, this
is an algebraic envelope.  No claim is made that every member is realized by
a pair of Lorentz metrics.  Higher nilpotency index and non-unipotent Jordan
spectra remain outside this gate.
-/

namespace JanusFormal
namespace P0EFTJanusLorentzJordanIndexThreeStratifiedRootGluing4D

set_option autoImplicit false

noncomputable section

open scoped Matrix.Norms.Frobenius RightActions Topology
open P0EFTJanusPositiveDiagonalizableRelativeRoot4D
open P0EFTJanusPositiveDiagonalizableRootGluing4D
open P0EFTJanusPositiveDiagonalizableGlobalRootContinuity4D
open P0EFTJanusLorentzJordanRelativeRoot4D
open P0EFTJanusLorentzJordanStratifiedRootGluing4D

abbrev Matrix4 := P0EFTJanusPositiveDiagonalizableRelativeRoot4D.Matrix4

local instance matrix4NormedAddCommGroup : NormedAddCommGroup Matrix4 :=
  Matrix.frobeniusNormedAddCommGroup

local instance matrix4AddCommGroup : AddCommGroup Matrix4 :=
  matrix4NormedAddCommGroup.toAddCommGroup

local instance matrix4TopologicalSpace : TopologicalSpace Matrix4 :=
  matrix4NormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

local instance matrix4NormedSpace : NormedSpace Real Matrix4 :=
  Matrix.frobeniusNormedSpace

local instance matrix4Module : Module Real Matrix4 :=
  matrix4NormedSpace.toModule

/-- Conjugacy-covariant cubic displacement invariant. -/
def jordanDisplacementCube (target : Matrix4) : Matrix4 :=
  (target - 1) * (target - 1) * (target - 1)

/-- Closed unipotent Jordan envelope of nilpotency index at most three. -/
def indexThreeUnipotentLocus : Set Matrix4 :=
  {target | jordanDisplacementCube target = 0}

abbrev IndexThreeUnipotentMatrix := indexThreeUnipotentLocus

/-- The genuinely new layer beyond the index-two envelope. -/
def strictIndexThreeUnipotentLocus : Set Matrix4 :=
  indexThreeUnipotentLocus \ indexTwoUnipotentLocus

/-- New root domain obtained by replacing the index-two envelope with the
larger index-three envelope. -/
def positiveOrIndexThreeRootLocus : Set Matrix4 :=
  positiveDiagonalizableLocus ∪ indexThreeUnipotentLocus

abbrev PositiveOrIndexThreeRootMatrix := positiveOrIndexThreeRootLocus

theorem indexTwoUnipotentLocus_subset_indexThreeUnipotentLocus :
    indexTwoUnipotentLocus ⊆ indexThreeUnipotentLocus := by
  intro target hSquare
  change jordanDisplacementCube target = 0
  unfold jordanDisplacementCube
  have hSquare' : (target - 1) * (target - 1) = 0 := hSquare
  rw [hSquare', zero_mul]

theorem indexThree_decomposes_into_old_and_strict :
    indexThreeUnipotentLocus =
      indexTwoUnipotentLocus ∪ strictIndexThreeUnipotentLocus := by
  ext target
  constructor
  · intro hThree
    by_cases hTwo : target ∈ indexTwoUnipotentLocus
    · exact Or.inl hTwo
    · exact Or.inr ⟨hThree, hTwo⟩
  · rintro (hTwo | hStrict)
    · exact indexTwoUnipotentLocus_subset_indexThreeUnipotentLocus hTwo
    · exact hStrict.1

/-- The cubic displacement invariant is preserved by similarity. -/
theorem jordanDisplacementCube_similarity
    (target change inverse : Matrix4)
    (hInverseChange : inverse * change = 1)
    (hChangeInverse : change * inverse = 1) :
    jordanDisplacementCube (change * target * inverse) =
      change * jordanDisplacementCube target * inverse := by
  have hDifference :
      change * target * inverse - 1 =
        change * (target - 1) * inverse := by
    noncomm_ring [hChangeInverse]
  unfold jordanDisplacementCube
  rw [hDifference]
  calc
    (change * (target - 1) * inverse) *
          (change * (target - 1) * inverse) *
        (change * (target - 1) * inverse) =
      change * (target - 1) * (inverse * change) *
        (target - 1) * (inverse * change) *
        (target - 1) * inverse := by noncomm_ring
    _ = change * ((target - 1) * (target - 1) * (target - 1)) *
        inverse := by
      rw [hInverseChange]
      simp [mul_assoc]

theorem indexThreeUnipotent_similarity_mem
    (target : IndexThreeUnipotentMatrix) (change inverse : Matrix4)
    (hInverseChange : inverse * change = 1)
    (hChangeInverse : change * inverse = 1) :
    change * target.1 * inverse ∈ indexThreeUnipotentLocus := by
  rw [indexThreeUnipotentLocus, Set.mem_setOf_eq,
    jordanDisplacementCube_similarity target.1 change inverse
      hInverseChange hChangeInverse,
    target.property]
  simp

/-- Truncated positive binomial root on the index-three envelope. -/
def indexThreeUnipotentRoot (target : IndexThreeUnipotentMatrix) : Matrix4 :=
  let nilpotent := target.1 - 1
  1 + (1 / 2 : Real) • nilpotent -
    (1 / 8 : Real) • (nilpotent * nilpotent)

theorem indexThreeUnipotentRoot_square
    (target : IndexThreeUnipotentMatrix) :
    indexThreeUnipotentRoot target * indexThreeUnipotentRoot target =
      target.1 := by
  let nilpotent : Matrix4 := target.1 - 1
  have hCube : nilpotent * nilpotent * nilpotent = 0 := target.property
  have hCubeRight : nilpotent * (nilpotent * nilpotent) = 0 := by
    rw [← mul_assoc, hCube]
  have hFourth : (nilpotent * nilpotent) *
      (nilpotent * nilpotent) = 0 := by
    rw [← mul_assoc, hCube, zero_mul]
  have hTarget : target.1 = 1 + nilpotent := by
    dsimp [nilpotent]
    noncomm_ring
  unfold indexThreeUnipotentRoot
  change
    (1 + (1 / 2 : Real) • nilpotent -
        (1 / 8 : Real) • (nilpotent * nilpotent)) *
      (1 + (1 / 2 : Real) • nilpotent -
        (1 / 8 : Real) • (nilpotent * nilpotent)) = target.1
  rw [hTarget]
  noncomm_ring [hCube, hCubeRight, hFourth]
  module

theorem indexThreeUnipotentRoot_similarity
    (target : IndexThreeUnipotentMatrix) (change inverse : Matrix4)
    (hInverseChange : inverse * change = 1)
    (hChangeInverse : change * inverse = 1) :
    indexThreeUnipotentRoot
        ⟨change * target.1 * inverse,
          indexThreeUnipotent_similarity_mem target change inverse
            hInverseChange hChangeInverse⟩ =
      change * indexThreeUnipotentRoot target * inverse := by
  let nilpotent : Matrix4 := target.1 - 1
  have hDifference :
      change * target.1 * inverse - 1 = change * nilpotent * inverse := by
    dsimp [nilpotent]
    noncomm_ring [hChangeInverse]
  have hSquare :
      (change * nilpotent * inverse) * (change * nilpotent * inverse) =
        change * (nilpotent * nilpotent) * inverse := by
    calc
      (change * nilpotent * inverse) * (change * nilpotent * inverse) =
          change * nilpotent * (inverse * change) * nilpotent * inverse := by
            noncomm_ring
      _ = change * (nilpotent * nilpotent) * inverse := by
        rw [hInverseChange]
        simp [mul_assoc]
  unfold indexThreeUnipotentRoot
  change
    1 + (1 / 2 : Real) • (change * target.1 * inverse - 1) -
        (1 / 8 : Real) •
          ((change * target.1 * inverse - 1) *
            (change * target.1 * inverse - 1)) =
      change *
          (1 + (1 / 2 : Real) • nilpotent -
            (1 / 8 : Real) • (nilpotent * nilpotent)) * inverse
  rw [hDifference, hSquare]
  noncomm_ring [hChangeInverse]

/-- Promotion of the old index-two envelope. -/
def promoteIndexTwoToIndexThree
    (target : IndexTwoUnipotentMatrix) : IndexThreeUnipotentMatrix :=
  ⟨target.1,
    indexTwoUnipotentLocus_subset_indexThreeUnipotentLocus target.property⟩

@[simp]
theorem indexThreeUnipotentRoot_on_indexTwo
    (target : IndexTwoUnipotentMatrix) :
    indexThreeUnipotentRoot (promoteIndexTwoToIndexThree target) =
      indexTwoUnipotentRoot target := by
  unfold indexThreeUnipotentRoot indexTwoUnipotentRoot
  change
    1 + (1 / 2 : Real) • (target.1 - 1) -
        (1 / 8 : Real) • ((target.1 - 1) * (target.1 - 1)) =
      1 + (1 / 2 : Real) • (target.1 - 1)
  have hSquare : (target.1 - 1) * (target.1 - 1) = 0 := target.property
  rw [hSquare]
  simp

/-- A concrete nonempty strict index-three Jordan block. -/
def strictIndexThreeNilpotent4 : Matrix4 :=
  ![![0, 1, 0, 0],
    ![0, 0, 1, 0],
    ![0, 0, 0, 0],
    ![0, 0, 0, 0]]

def strictIndexThreeTarget4 : Matrix4 :=
  1 + strictIndexThreeNilpotent4

theorem strictIndexThreeNilpotent4_cube :
    strictIndexThreeNilpotent4 * strictIndexThreeNilpotent4 *
      strictIndexThreeNilpotent4 = 0 := by
  ext first second
  fin_cases first <;> fin_cases second <;>
    norm_num [strictIndexThreeNilpotent4, Matrix.mul_apply,
      Fin.sum_univ_succ]

theorem strictIndexThreeNilpotent4_square_ne_zero :
    strictIndexThreeNilpotent4 * strictIndexThreeNilpotent4 ≠ 0 := by
  intro hZero
  have hEntry := congrArg (fun matrix : Matrix4 => matrix 0 2) hZero
  norm_num [strictIndexThreeNilpotent4, Matrix.mul_apply,
    Fin.sum_univ_succ] at hEntry
  change (1 : Real) = 0 at hEntry
  norm_num at hEntry

theorem strictIndexThreeTarget4_displacement :
    strictIndexThreeTarget4 - 1 = strictIndexThreeNilpotent4 := by
  unfold strictIndexThreeTarget4
  abel

theorem strictIndexThreeTarget4_mem :
    strictIndexThreeTarget4 ∈ strictIndexThreeUnipotentLocus := by
  constructor
  · change jordanDisplacementCube strictIndexThreeTarget4 = 0
    rw [jordanDisplacementCube, strictIndexThreeTarget4_displacement,
      strictIndexThreeNilpotent4_cube]
  · intro hIndexTwo
    apply strictIndexThreeNilpotent4_square_ne_zero
    simpa [indexTwoUnipotentLocus, jordanDisplacementSquare,
      strictIndexThreeTarget4_displacement] using hIndexTwo

private theorem diagonal4_cube_zero_implies_zero
    (diagonal : Matrix4) (hDiagonal : diagonal.IsDiag)
    (hCube : diagonal * diagonal * diagonal = 0) :
    diagonal = 0 := by
  have hCubeDiag :
      Matrix.diagonal (Matrix.diag diagonal) *
          Matrix.diagonal (Matrix.diag diagonal) *
        Matrix.diagonal (Matrix.diag diagonal) = 0 := by
    rw [hDiagonal.diagonal_diag]
    exact hCube
  rw [← hDiagonal.diagonal_diag]
  ext first second
  by_cases hIndices : first = second
  · subst second
    have hEntry := congrArg
      (fun matrix : Matrix4 => matrix first first) hCubeDiag
    simp at hEntry
    simpa using hEntry
  · simp [hIndices]

private theorem diagonal4_eq_one_of_displacement_cube_zero
    (diagonal : Matrix4) (hDiagonal : diagonal.IsDiag)
    (hCube : jordanDisplacementCube diagonal = 0) :
    diagonal = 1 := by
  apply sub_eq_zero.mp
  apply diagonal4_cube_zero_implies_zero (diagonal - 1)
    (hDiagonal.sub Matrix.isDiag_one)
  exact hCube

theorem indexThreeUnipotent_not_realDiagonalizable
    (target : IndexThreeUnipotentMatrix) (hTarget : target.1 ≠ 1) :
    ¬ IsRealDiagonalizable4 target.1 := by
  rintro ⟨change, inverse, diagonal, hInverseChange, hChangeInverse,
    hDiagonal, hSimilarity⟩
  have hConjugatedDifference :
      inverse * (target.1 - 1) * change = diagonal - 1 := by
    rw [hSimilarity]
    calc
      inverse * (change * diagonal * inverse - 1) * change =
          (inverse * change) * diagonal * (inverse * change) -
            inverse * change := by noncomm_ring
      _ = diagonal - 1 := by rw [hInverseChange]; simp
  have hDiagonalCube : jordanDisplacementCube diagonal = 0 := by
    unfold jordanDisplacementCube
    rw [← hConjugatedDifference]
    calc
      (inverse * (target.1 - 1) * change) *
            (inverse * (target.1 - 1) * change) *
          (inverse * (target.1 - 1) * change) =
        inverse * (target.1 - 1) * (change * inverse) *
          (target.1 - 1) * (change * inverse) *
          (target.1 - 1) * change := by noncomm_ring
      _ = inverse * jordanDisplacementCube target.1 * change := by
        rw [hChangeInverse]
        simp [jordanDisplacementCube, mul_assoc]
      _ = 0 := by rw [target.property]; simp
  have hDiagonalOne := diagonal4_eq_one_of_displacement_cube_zero
    diagonal hDiagonal hDiagonalCube
  apply hTarget
  rw [hSimilarity, hDiagonalOne, mul_one, hChangeInverse]

theorem positiveDiagonalizable_inter_indexThreeUnipotent :
    positiveDiagonalizableLocus ∩ indexThreeUnipotentLocus =
      ({1} : Set Matrix4) := by
  ext target
  constructor
  · rintro ⟨hPositive, hIndexThree⟩
    have hTarget : target = 1 := by
      by_contra hNe
      rcases hPositive with ⟨data, hData⟩
      apply indexThreeUnipotent_not_realDiagonalizable
        ⟨target, hIndexThree⟩ hNe
      simpa [hData] using positiveDiagonalizable_isRealDiagonalizable4 data
    simp [hTarget]
  · intro hSingleton
    have hTarget : target = 1 := by simpa using hSingleton
    subst target
    refine ⟨one_mem_positiveDiagonalizableLocus, ?_⟩
    simp [indexThreeUnipotentLocus, jordanDisplacementCube]

/-- Sylvester operator at the index-three root. -/
def indexThreeSylvester
    (target : IndexThreeUnipotentMatrix) (variation : Matrix4) : Matrix4 :=
  indexThreeUnipotentRoot target * variation +
    variation * indexThreeUnipotentRoot target

/-- The inverse polynomial in commuting left and right multiplication by
`N`; all omitted monomials contain `N^3`. -/
def indexThreeSylvesterInverse
    (target : IndexThreeUnipotentMatrix) (rhs : Matrix4) : Matrix4 :=
  let nilpotent := target.1 - 1
  let nilpotentSq := nilpotent * nilpotent
  (1 / 2 : Real) • rhs -
    (1 / 8 : Real) • (nilpotent * rhs + rhs * nilpotent) +
    (1 / 16 : Real) •
      (nilpotentSq * rhs + nilpotent * rhs * nilpotent + rhs * nilpotentSq) -
    (5 / 128 : Real) •
      (nilpotentSq * rhs * nilpotent + nilpotent * rhs * nilpotentSq) +
    (7 / 256 : Real) • (nilpotentSq * rhs * nilpotentSq)

theorem indexThreeSylvester_inverse_apply
    (target : IndexThreeUnipotentMatrix) (rhs : Matrix4) :
    indexThreeSylvester target (indexThreeSylvesterInverse target rhs) = rhs := by
  let nilpotent : Matrix4 := target.1 - 1
  have hCube : nilpotent * nilpotent * nilpotent = 0 := target.property
  have hCubeRight : nilpotent * (nilpotent * nilpotent) = 0 := by
    rw [← mul_assoc, hCube]
  have hLeft (matrix : Matrix4) :
      nilpotent * (nilpotent * (nilpotent * matrix)) = 0 := by
    rw [← mul_assoc, ← mul_assoc, hCube, zero_mul]
  unfold indexThreeSylvester indexThreeSylvesterInverse
    indexThreeUnipotentRoot
  change
    (1 + (1 / 2 : Real) • nilpotent -
        (1 / 8 : Real) • (nilpotent * nilpotent)) *
        ((1 / 2 : Real) • rhs -
          (1 / 8 : Real) • (nilpotent * rhs + rhs * nilpotent) +
          (1 / 16 : Real) •
            ((nilpotent * nilpotent) * rhs +
              nilpotent * rhs * nilpotent +
              rhs * (nilpotent * nilpotent)) -
          (5 / 128 : Real) •
            ((nilpotent * nilpotent) * rhs * nilpotent +
              nilpotent * rhs * (nilpotent * nilpotent)) +
          (7 / 256 : Real) •
            ((nilpotent * nilpotent) * rhs *
              (nilpotent * nilpotent))) +
      ((1 / 2 : Real) • rhs -
          (1 / 8 : Real) • (nilpotent * rhs + rhs * nilpotent) +
          (1 / 16 : Real) •
            ((nilpotent * nilpotent) * rhs +
              nilpotent * rhs * nilpotent +
              rhs * (nilpotent * nilpotent)) -
          (5 / 128 : Real) •
            ((nilpotent * nilpotent) * rhs * nilpotent +
              nilpotent * rhs * (nilpotent * nilpotent)) +
          (7 / 256 : Real) •
            ((nilpotent * nilpotent) * rhs *
              (nilpotent * nilpotent))) *
        (1 + (1 / 2 : Real) • nilpotent -
          (1 / 8 : Real) • (nilpotent * nilpotent)) = rhs
  noncomm_ring [hCube]
  simp only [hCubeRight, hLeft, mul_zero, smul_zero,
    add_zero, zero_add]
  module

def indexThreeSylvesterLinearMap
    (target : IndexThreeUnipotentMatrix) : Matrix4 →ₗ[Real] Matrix4 where
  toFun := indexThreeSylvester target
  map_add' first second := by
    unfold indexThreeSylvester
    noncomm_ring
  map_smul' scalar variation := by
    unfold indexThreeSylvester
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_add]
    simp

theorem indexThreeSylvester_surjective
    (target : IndexThreeUnipotentMatrix) :
    Function.Surjective (indexThreeSylvester target) := by
  intro rhs
  exact ⟨indexThreeSylvesterInverse target rhs,
    indexThreeSylvester_inverse_apply target rhs⟩

theorem indexThreeSylvester_injective
    (target : IndexThreeUnipotentMatrix) :
    Function.Injective (indexThreeSylvester target) := by
  have hSurjective :
      Function.Surjective (indexThreeSylvesterLinearMap target) :=
    indexThreeSylvester_surjective target
  exact LinearMap.injective_iff_surjective.mpr hSurjective

theorem indexThreeSylvesterInverse_apply
    (target : IndexThreeUnipotentMatrix) (variation : Matrix4) :
    indexThreeSylvesterInverse target (indexThreeSylvester target variation) =
      variation := by
  apply indexThreeSylvester_injective target
  exact indexThreeSylvester_inverse_apply target
    (indexThreeSylvester target variation)
theorem indexThreeSylvester_bijective (target : IndexThreeUnipotentMatrix) :
    Function.Bijective (indexThreeSylvester target) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨indexThreeSylvesterInverse target,
      indexThreeSylvesterInverse_apply target,
      indexThreeSylvester_inverse_apply target⟩

def positiveTargetInIndexThreeGluedLocus
    (target : positiveDiagonalizableLocus) :
    PositiveOrIndexThreeRootMatrix :=
  ⟨target.1, Or.inl target.property⟩

def indexThreeTargetInGluedLocus
    (target : IndexThreeUnipotentMatrix) :
    PositiveOrIndexThreeRootMatrix :=
  ⟨target.1, Or.inr target.property⟩

private def indexThreeTargetOfNotPositive
    (target : PositiveOrIndexThreeRootMatrix)
    (hNotPositive : target.1 ∉ positiveDiagonalizableLocus) :
    IndexThreeUnipotentMatrix :=
  ⟨target.1, target.property.resolve_left hNotPositive⟩

def positiveOrIndexThreeRoot
    (target : PositiveOrIndexThreeRootMatrix) : Matrix4 := by
  classical
  exact if hPositive : target.1 ∈ positiveDiagonalizableLocus then
    positiveDiagonalizableGlobalRoot ⟨target.1, hPositive⟩
  else
    indexThreeUnipotentRoot
      (indexThreeTargetOfNotPositive target hPositive)

@[simp]
theorem positiveOrIndexThreeRoot_on_positive
    (target : positiveDiagonalizableLocus) :
    positiveOrIndexThreeRoot
        (positiveTargetInIndexThreeGluedLocus target) =
      positiveDiagonalizableGlobalRoot target := by
  unfold positiveOrIndexThreeRoot
  dsimp only [positiveTargetInIndexThreeGluedLocus]
  rw [dif_pos target.property]

private theorem positiveDiagonalizableGlobalRoot_one
    (hOne : (1 : Matrix4) ∈ positiveDiagonalizableLocus) :
    positiveDiagonalizableGlobalRoot ⟨1, hOne⟩ = 1 := by
  rw [positiveDiagonalizableGlobalRoot_eq_of_presentation
    ⟨1, hOne⟩ identityPositiveDiagonalizableRelativeMatrix rfl]
  exact identityPositiveDiagonalizableRelativeMatrix_root

theorem positive_and_indexThree_roots_agree
    (target : Matrix4)
    (hPositive : target ∈ positiveDiagonalizableLocus)
    (hIndexThree : target ∈ indexThreeUnipotentLocus) :
    positiveDiagonalizableGlobalRoot ⟨target, hPositive⟩ =
      indexThreeUnipotentRoot ⟨target, hIndexThree⟩ := by
  have hTarget : target = 1 := by
    have hMembership : target ∈
        positiveDiagonalizableLocus ∩ indexThreeUnipotentLocus :=
      ⟨hPositive, hIndexThree⟩
    rw [positiveDiagonalizable_inter_indexThreeUnipotent] at hMembership
    simpa using hMembership
  subst target
  rw [positiveDiagonalizableGlobalRoot_one]
  simp [indexThreeUnipotentRoot]

@[simp]
theorem positiveOrIndexThreeRoot_on_indexThree
    (target : IndexThreeUnipotentMatrix) :
    positiveOrIndexThreeRoot (indexThreeTargetInGluedLocus target) =
      indexThreeUnipotentRoot target := by
  classical
  unfold positiveOrIndexThreeRoot
  dsimp only [indexThreeTargetInGluedLocus]
  split
  · next hPositive =>
      exact positive_and_indexThree_roots_agree
        target.1 hPositive target.property
  · rfl

theorem positiveOrIndexThreeRoot_square
    (target : PositiveOrIndexThreeRootMatrix) :
    positiveOrIndexThreeRoot target * positiveOrIndexThreeRoot target =
      target.1 := by
  classical
  by_cases hPositive : target.1 ∈ positiveDiagonalizableLocus
  · rw [positiveOrIndexThreeRoot, dif_pos hPositive]
    exact positiveDiagonalizableGlobalRoot_square ⟨target.1, hPositive⟩
  · rw [positiveOrIndexThreeRoot, dif_neg hPositive]
    exact indexThreeUnipotentRoot_square
      (indexThreeTargetOfNotPositive target hPositive)

/-- Inclusion of the previously closed glued domain. -/
def previousGluedTargetInIndexThreeLocus
    (target : PositiveOrIndexTwoRootMatrix) :
    PositiveOrIndexThreeRootMatrix :=
  ⟨target.1, target.property.elim Or.inl
    (fun hIndexTwo => Or.inr
      (indexTwoUnipotentLocus_subset_indexThreeUnipotentLocus hIndexTwo))⟩

/-- The new selector is an exact extension of the old glued selector. -/
theorem positiveOrIndexThreeRoot_extends_indexTwoGluing
    (target : PositiveOrIndexTwoRootMatrix) :
    positiveOrIndexThreeRoot
        (previousGluedTargetInIndexThreeLocus target) =
      positiveOrIndexTwoRoot target := by
  classical
  by_cases hPositive : target.1 ∈ positiveDiagonalizableLocus
  · let positiveTarget : positiveDiagonalizableLocus :=
      ⟨target.1, hPositive⟩
    have hOldTarget : target =
        positiveTargetInGluedLocus positiveTarget := Subtype.ext (by rfl)
    have hNewTarget : previousGluedTargetInIndexThreeLocus target =
        positiveTargetInIndexThreeGluedLocus positiveTarget :=
      Subtype.ext (by rfl)
    calc
      positiveOrIndexThreeRoot
          (previousGluedTargetInIndexThreeLocus target) =
        positiveOrIndexThreeRoot
          (positiveTargetInIndexThreeGluedLocus positiveTarget) :=
            congrArg positiveOrIndexThreeRoot hNewTarget
      _ = positiveDiagonalizableGlobalRoot positiveTarget :=
        positiveOrIndexThreeRoot_on_positive positiveTarget
      _ = positiveOrIndexTwoRoot
          (positiveTargetInGluedLocus positiveTarget) :=
        (positiveOrIndexTwoRoot_on_positive positiveTarget).symm
      _ = positiveOrIndexTwoRoot target :=
        congrArg positiveOrIndexTwoRoot hOldTarget.symm
  · have hIndexTwo : target.1 ∈ indexTwoUnipotentLocus :=
      target.property.resolve_left hPositive
    let oldTarget : IndexTwoUnipotentMatrix := ⟨target.1, hIndexTwo⟩
    let newTarget : IndexThreeUnipotentMatrix :=
      promoteIndexTwoToIndexThree oldTarget
    have hOldTarget : target = indexTwoTargetInGluedLocus oldTarget :=
      Subtype.ext (by rfl)
    have hNewTarget : previousGluedTargetInIndexThreeLocus target =
        indexThreeTargetInGluedLocus newTarget := Subtype.ext (by rfl)
    calc
      positiveOrIndexThreeRoot
          (previousGluedTargetInIndexThreeLocus target) =
        positiveOrIndexThreeRoot
          (indexThreeTargetInGluedLocus newTarget) :=
            congrArg positiveOrIndexThreeRoot hNewTarget
      _ = indexThreeUnipotentRoot newTarget :=
        positiveOrIndexThreeRoot_on_indexThree newTarget
      _ = indexTwoUnipotentRoot oldTarget :=
        indexThreeUnipotentRoot_on_indexTwo oldTarget
      _ = positiveOrIndexTwoRoot
          (indexTwoTargetInGluedLocus oldTarget) :=
        (positiveOrIndexTwoRoot_on_indexTwo oldTarget).symm
      _ = positiveOrIndexTwoRoot target :=
        congrArg positiveOrIndexTwoRoot hOldTarget.symm

theorem positiveOrIndexThree_stratum_classification
    (target : PositiveOrIndexThreeRootMatrix) :
    target.1 ∈ positiveDiagonalizableLocus ∨
      (target.1 ∈ indexThreeUnipotentLocus ∧ target.1 ≠ 1 ∧
        ¬ IsRealDiagonalizable4 target.1) := by
  classical
  by_cases hPositive : target.1 ∈ positiveDiagonalizableLocus
  · exact Or.inl hPositive
  · right
    have hIndexThree : target.1 ∈ indexThreeUnipotentLocus :=
      target.property.resolve_left hPositive
    have hNe : target.1 ≠ 1 := by
      intro hOne
      apply hPositive
      simpa [hOne] using one_mem_positiveDiagonalizableLocus
    exact ⟨hIndexThree, hNe,
      indexThreeUnipotent_not_realDiagonalizable
        ⟨target.1, hIndexThree⟩ hNe⟩

theorem outside_positiveOrIndexThreeRootLocus_iff (target : Matrix4) :
    target ∉ positiveOrIndexThreeRootLocus ↔
      target ∉ positiveDiagonalizableLocus ∧
        jordanDisplacementCube target ≠ 0 := by
  simp [positiveOrIndexThreeRootLocus, indexThreeUnipotentLocus]

theorem positiveOrIndexThreeRoot_positiveRestriction_continuous :
    Continuous (fun target : positiveDiagonalizableLocus =>
      positiveOrIndexThreeRoot
        (positiveTargetInIndexThreeGluedLocus target)) := by
  simpa only [positiveOrIndexThreeRoot_on_positive] using
    positiveDiagonalizableGlobalRoot_continuous

theorem indexThreeUnipotentRoot_continuous :
    Continuous indexThreeUnipotentRoot := by
  unfold indexThreeUnipotentRoot
  fun_prop

theorem positiveOrIndexThreeRoot_indexThreeRestriction_continuous :
    Continuous (fun target : IndexThreeUnipotentMatrix =>
      positiveOrIndexThreeRoot (indexThreeTargetInGluedLocus target)) := by
  simpa only [positiveOrIndexThreeRoot_on_indexThree] using
    indexThreeUnipotentRoot_continuous

end

end P0EFTJanusLorentzJordanIndexThreeStratifiedRootGluing4D
end JanusFormal
