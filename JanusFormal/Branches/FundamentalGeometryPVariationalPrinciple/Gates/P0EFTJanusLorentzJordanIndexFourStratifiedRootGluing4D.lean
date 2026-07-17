import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusLorentzJordanIndexThreeStratifiedRootGluing4D

/-!
# The complete unipotent root locus in dimension four

For a four-dimensional unipotent matrix, `N = A - I` has nilpotency index at
most four.  On the locus `N^4 = 0`, the positive binomial root is exactly
`I + N/2 - N^2/8 + N^3/16`.  This gate proves its square, similarity
equivariance, continuity, and a finite polynomial inverse for its Sylvester
operator.  It glues exactly to the already closed index-at-most-three selector.

The strict fourth layer is nonempty by an explicit size-four Jordan block.
Thus all unipotent Jordan indices possible for `4 x 4` matrices are covered.
Non-unipotent Jordan spectra remain outside this gate.
-/

namespace JanusFormal
namespace P0EFTJanusLorentzJordanIndexFourStratifiedRootGluing4D

set_option autoImplicit false

noncomputable section

open scoped Matrix.Norms.Frobenius RightActions Topology
open P0EFTJanusPositiveDiagonalizableRelativeRoot4D
open P0EFTJanusPositiveDiagonalizableRootGluing4D
open P0EFTJanusPositiveDiagonalizableGlobalRootContinuity4D
open P0EFTJanusLorentzJordanRelativeRoot4D
open P0EFTJanusLorentzJordanStratifiedRootGluing4D
open P0EFTJanusLorentzJordanIndexThreeStratifiedRootGluing4D

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

/-- Ultimate nilpotent displacement invariant available in dimension four. -/
def jordanDisplacementFourth (target : Matrix4) : Matrix4 :=
  (target - 1) * (target - 1) * (target - 1) * (target - 1)

/-- Complete algebraic unipotent locus in dimension four. -/
def indexFourUnipotentLocus : Set Matrix4 :=
  {target | jordanDisplacementFourth target = 0}

abbrev IndexFourUnipotentMatrix := indexFourUnipotentLocus

def strictIndexFourUnipotentLocus : Set Matrix4 :=
  indexFourUnipotentLocus \ indexThreeUnipotentLocus

def positiveOrIndexFourRootLocus : Set Matrix4 :=
  positiveDiagonalizableLocus ∪ indexFourUnipotentLocus

abbrev PositiveOrIndexFourRootMatrix := positiveOrIndexFourRootLocus

theorem indexThreeUnipotentLocus_subset_indexFourUnipotentLocus :
    indexThreeUnipotentLocus ⊆ indexFourUnipotentLocus := by
  intro target hCube
  change jordanDisplacementFourth target = 0
  unfold jordanDisplacementFourth
  have hCube' :
      (target - 1) * (target - 1) * (target - 1) = 0 := hCube
  rw [hCube', zero_mul]

theorem indexFour_decomposes_into_old_and_strict :
    indexFourUnipotentLocus =
      indexThreeUnipotentLocus ∪ strictIndexFourUnipotentLocus := by
  ext target
  constructor
  · intro hFour
    by_cases hThree : target ∈ indexThreeUnipotentLocus
    · exact Or.inl hThree
    · exact Or.inr ⟨hFour, hThree⟩
  · rintro (hThree | hStrict)
    · exact indexThreeUnipotentLocus_subset_indexFourUnipotentLocus hThree
    · exact hStrict.1

theorem jordanDisplacementFourth_similarity
    (target change inverse : Matrix4)
    (hInverseChange : inverse * change = 1)
    (hChangeInverse : change * inverse = 1) :
    jordanDisplacementFourth (change * target * inverse) =
      change * jordanDisplacementFourth target * inverse := by
  have hDifference :
      change * target * inverse - 1 =
        change * (target - 1) * inverse := by
    noncomm_ring [hChangeInverse]
  unfold jordanDisplacementFourth
  rw [hDifference]
  calc
    (change * (target - 1) * inverse) *
            (change * (target - 1) * inverse) *
          (change * (target - 1) * inverse) *
        (change * (target - 1) * inverse) =
      change * (target - 1) * (inverse * change) *
        (target - 1) * (inverse * change) *
        (target - 1) * (inverse * change) *
        (target - 1) * inverse := by noncomm_ring
    _ = change *
        ((target - 1) * (target - 1) * (target - 1) * (target - 1)) *
          inverse := by
      rw [hInverseChange]
      simp [mul_assoc]

theorem indexFourUnipotent_similarity_mem
    (target : IndexFourUnipotentMatrix) (change inverse : Matrix4)
    (hInverseChange : inverse * change = 1)
    (hChangeInverse : change * inverse = 1) :
    change * target.1 * inverse ∈ indexFourUnipotentLocus := by
  rw [indexFourUnipotentLocus, Set.mem_setOf_eq,
    jordanDisplacementFourth_similarity target.1 change inverse
      hInverseChange hChangeInverse,
    target.property]
  simp

/-- Universal fourth-order truncated binomial root polynomial. -/
def indexFourRootPolynomial (nilpotent : Matrix4) : Matrix4 :=
  1 + (1 / 2 : Real) • nilpotent -
    (1 / 8 : Real) • (nilpotent * nilpotent) +
    (1 / 16 : Real) • (nilpotent * nilpotent * nilpotent)

def indexFourUnipotentRoot (target : IndexFourUnipotentMatrix) : Matrix4 :=
  indexFourRootPolynomial (target.1 - 1)

theorem indexFourUnipotentRoot_square
    (target : IndexFourUnipotentMatrix) :
    indexFourUnipotentRoot target * indexFourUnipotentRoot target =
      target.1 := by
  let nilpotent : Matrix4 := target.1 - 1
  have hFourth :
      nilpotent * nilpotent * nilpotent * nilpotent = 0 := target.property
  have hFourthRight :
      nilpotent * (nilpotent * (nilpotent * nilpotent)) = 0 := by
    rw [← mul_assoc, ← mul_assoc, hFourth]
  have hFifth :
      (nilpotent * nilpotent) *
        (nilpotent * nilpotent * nilpotent) = 0 := by
    rw [← mul_assoc, ← mul_assoc, hFourth, zero_mul]
  have hSixth :
      (nilpotent * nilpotent * nilpotent) *
        (nilpotent * nilpotent * nilpotent) = 0 := by
    calc
      (nilpotent * nilpotent * nilpotent) *
          (nilpotent * nilpotent * nilpotent) =
        (nilpotent * nilpotent * nilpotent * nilpotent) *
          (nilpotent * nilpotent) := by noncomm_ring
      _ = 0 := by rw [hFourth]; simp
  have hTarget : target.1 = 1 + nilpotent := by
    dsimp [nilpotent]
    noncomm_ring
  change indexFourRootPolynomial nilpotent *
      indexFourRootPolynomial nilpotent = target.1
  rw [hTarget]
  unfold indexFourRootPolynomial
  noncomm_ring [hFourth, hFourthRight, hFifth, hSixth]
  module

theorem indexFourUnipotentRoot_similarity
    (target : IndexFourUnipotentMatrix) (change inverse : Matrix4)
    (hInverseChange : inverse * change = 1)
    (hChangeInverse : change * inverse = 1) :
    indexFourUnipotentRoot
        ⟨change * target.1 * inverse,
          indexFourUnipotent_similarity_mem target change inverse
            hInverseChange hChangeInverse⟩ =
      change * indexFourUnipotentRoot target * inverse := by
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
  have hCube :
      (change * nilpotent * inverse) * (change * nilpotent * inverse) *
          (change * nilpotent * inverse) =
        change * (nilpotent * nilpotent * nilpotent) * inverse := by
    calc
      (change * nilpotent * inverse) * (change * nilpotent * inverse) *
          (change * nilpotent * inverse) =
        change * nilpotent * (inverse * change) * nilpotent *
          (inverse * change) * nilpotent * inverse := by noncomm_ring
      _ = change * (nilpotent * nilpotent * nilpotent) * inverse := by
        rw [hInverseChange]
        simp [mul_assoc]
  unfold indexFourUnipotentRoot
  change indexFourRootPolynomial (change * target.1 * inverse - 1) =
    change * indexFourRootPolynomial nilpotent * inverse
  rw [hDifference]
  unfold indexFourRootPolynomial
  rw [hCube, hSquare]
  noncomm_ring [hChangeInverse]

def promoteIndexThreeToIndexFour
    (target : IndexThreeUnipotentMatrix) : IndexFourUnipotentMatrix :=
  ⟨target.1,
    indexThreeUnipotentLocus_subset_indexFourUnipotentLocus target.property⟩

@[simp]
theorem indexFourUnipotentRoot_on_indexThree
    (target : IndexThreeUnipotentMatrix) :
    indexFourUnipotentRoot (promoteIndexThreeToIndexFour target) =
      indexThreeUnipotentRoot target := by
  have hCube :
      (target.1 - 1) * (target.1 - 1) * (target.1 - 1) = 0 :=
    target.property
  unfold indexFourUnipotentRoot
  change indexFourRootPolynomial (target.1 - 1) =
    indexThreeUnipotentRoot target
  unfold indexFourRootPolynomial indexThreeUnipotentRoot
  rw [hCube]
  simp

/-- Explicit strict size-four Jordan block. -/
def strictIndexFourNilpotent4 : Matrix4 :=
  ![![0, 1, 0, 0],
    ![0, 0, 1, 0],
    ![0, 0, 0, 1],
    ![0, 0, 0, 0]]

def strictIndexFourTarget4 : Matrix4 :=
  1 + strictIndexFourNilpotent4

theorem strictIndexFourNilpotent4_fourth :
    strictIndexFourNilpotent4 * strictIndexFourNilpotent4 *
        strictIndexFourNilpotent4 * strictIndexFourNilpotent4 = 0 := by
  ext first second
  fin_cases first <;> fin_cases second <;>
    norm_num [strictIndexFourNilpotent4, Matrix.mul_apply,
      Fin.sum_univ_succ]

theorem strictIndexFourNilpotent4_cube_ne_zero :
    strictIndexFourNilpotent4 * strictIndexFourNilpotent4 *
      strictIndexFourNilpotent4 ≠ 0 := by
  intro hZero
  have hEntry := congrArg (fun matrix : Matrix4 => matrix 0 3) hZero
  norm_num [strictIndexFourNilpotent4, Matrix.mul_apply,
    Fin.sum_univ_succ] at hEntry
  change (1 : Real) = 0 at hEntry
  norm_num at hEntry

theorem strictIndexFourTarget4_displacement :
    strictIndexFourTarget4 - 1 = strictIndexFourNilpotent4 := by
  unfold strictIndexFourTarget4
  abel

theorem strictIndexFourTarget4_mem :
    strictIndexFourTarget4 ∈ strictIndexFourUnipotentLocus := by
  constructor
  · change jordanDisplacementFourth strictIndexFourTarget4 = 0
    rw [jordanDisplacementFourth, strictIndexFourTarget4_displacement,
      strictIndexFourNilpotent4_fourth]
  · intro hIndexThree
    apply strictIndexFourNilpotent4_cube_ne_zero
    simpa [indexThreeUnipotentLocus, jordanDisplacementCube,
      strictIndexFourTarget4_displacement] using hIndexThree

private theorem diagonal4_fourth_zero_implies_zero
    (diagonal : Matrix4) (hDiagonal : diagonal.IsDiag)
    (hFourth : diagonal * diagonal * diagonal * diagonal = 0) :
    diagonal = 0 := by
  have hFourthDiag :
      Matrix.diagonal (Matrix.diag diagonal) *
            Matrix.diagonal (Matrix.diag diagonal) *
          Matrix.diagonal (Matrix.diag diagonal) *
        Matrix.diagonal (Matrix.diag diagonal) = 0 := by
    rw [hDiagonal.diagonal_diag]
    exact hFourth
  rw [← hDiagonal.diagonal_diag]
  ext first second
  by_cases hIndices : first = second
  · subst second
    have hEntry := congrArg
      (fun matrix : Matrix4 => matrix first first) hFourthDiag
    simp at hEntry
    simpa using hEntry
  · simp [hIndices]

private theorem diagonal4_eq_one_of_displacement_fourth_zero
    (diagonal : Matrix4) (hDiagonal : diagonal.IsDiag)
    (hFourth : jordanDisplacementFourth diagonal = 0) :
    diagonal = 1 := by
  apply sub_eq_zero.mp
  apply diagonal4_fourth_zero_implies_zero (diagonal - 1)
    (hDiagonal.sub Matrix.isDiag_one)
  exact hFourth

theorem indexFourUnipotent_not_realDiagonalizable
    (target : IndexFourUnipotentMatrix) (hTarget : target.1 ≠ 1) :
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
  have hDiagonalFourth : jordanDisplacementFourth diagonal = 0 := by
    unfold jordanDisplacementFourth
    rw [← hConjugatedDifference]
    calc
      (inverse * (target.1 - 1) * change) *
              (inverse * (target.1 - 1) * change) *
            (inverse * (target.1 - 1) * change) *
          (inverse * (target.1 - 1) * change) =
        inverse * (target.1 - 1) * (change * inverse) *
          (target.1 - 1) * (change * inverse) *
          (target.1 - 1) * (change * inverse) *
          (target.1 - 1) * change := by noncomm_ring
      _ = inverse * jordanDisplacementFourth target.1 * change := by
        rw [hChangeInverse]
        simp [jordanDisplacementFourth, mul_assoc]
      _ = 0 := by rw [target.property]; simp
  have hDiagonalOne := diagonal4_eq_one_of_displacement_fourth_zero
    diagonal hDiagonal hDiagonalFourth
  apply hTarget
  rw [hSimilarity, hDiagonalOne, mul_one, hChangeInverse]

theorem positiveDiagonalizable_inter_indexFourUnipotent :
    positiveDiagonalizableLocus ∩ indexFourUnipotentLocus =
      ({1} : Set Matrix4) := by
  ext target
  constructor
  · rintro ⟨hPositive, hIndexFour⟩
    have hTarget : target = 1 := by
      by_contra hNe
      rcases hPositive with ⟨data, hData⟩
      apply indexFourUnipotent_not_realDiagonalizable
        ⟨target, hIndexFour⟩ hNe
      simpa [hData] using positiveDiagonalizable_isRealDiagonalizable4 data
    simp [hTarget]
  · intro hSingleton
    have hTarget : target = 1 := by simpa using hSingleton
    subst target
    refine ⟨one_mem_positiveDiagonalizableLocus, ?_⟩
    simp [indexFourUnipotentLocus, jordanDisplacementFourth]

def indexFourSylvester
    (target : IndexFourUnipotentMatrix) (variation : Matrix4) : Matrix4 :=
  indexFourUnipotentRoot target * variation +
    variation * indexFourUnipotentRoot target

/-- Inverse polynomial in left/right multiplication by `N`, reduced modulo
`N^4 = 0` on both sides. -/
def indexFourSylvesterInversePolynomial
    (nilpotent rhs : Matrix4) : Matrix4 :=
  let nilpotentSq := nilpotent * nilpotent
  let nilpotentCube := nilpotentSq * nilpotent
  (1 / 2 : Real) • rhs -
    (1 / 8 : Real) • (nilpotent * rhs + rhs * nilpotent) +
    (1 / 16 : Real) •
      (nilpotentSq * rhs + nilpotent * rhs * nilpotent + rhs * nilpotentSq) -
    (5 / 128 : Real) •
      (nilpotentCube * rhs + nilpotentSq * rhs * nilpotent +
        nilpotent * rhs * nilpotentSq + rhs * nilpotentCube) +
    (7 / 256 : Real) •
      (nilpotentCube * rhs * nilpotent +
        nilpotentSq * rhs * nilpotentSq +
        nilpotent * rhs * nilpotentCube) -
    (21 / 1024 : Real) •
      (nilpotentCube * rhs * nilpotentSq +
        nilpotentSq * rhs * nilpotentCube) +
    (33 / 2048 : Real) •
      (nilpotentCube * rhs * nilpotentCube)

def indexFourSylvesterInverse
    (target : IndexFourUnipotentMatrix) (rhs : Matrix4) : Matrix4 :=
  indexFourSylvesterInversePolynomial (target.1 - 1) rhs

theorem indexFourSylvester_inverse_apply
    (target : IndexFourUnipotentMatrix) (rhs : Matrix4) :
    indexFourSylvester target (indexFourSylvesterInverse target rhs) = rhs := by
  let nilpotent : Matrix4 := target.1 - 1
  have hFourth :
      nilpotent * nilpotent * nilpotent * nilpotent = 0 := target.property
  have hFourthRight :
      nilpotent * (nilpotent * (nilpotent * nilpotent)) = 0 := by
    rw [← mul_assoc, ← mul_assoc, hFourth]
  have hLeft (matrix : Matrix4) :
      nilpotent * (nilpotent * (nilpotent * (nilpotent * matrix))) = 0 := by
    rw [← mul_assoc, ← mul_assoc, ← mul_assoc, hFourth, zero_mul]
  change
    indexFourRootPolynomial nilpotent *
        indexFourSylvesterInversePolynomial nilpotent rhs +
      indexFourSylvesterInversePolynomial nilpotent rhs *
        indexFourRootPolynomial nilpotent = rhs
  unfold indexFourRootPolynomial indexFourSylvesterInversePolynomial
  noncomm_ring [hFourth]
  simp only [hFourthRight, hLeft, mul_zero, smul_zero, add_zero, zero_add]
  module

def indexFourSylvesterLinearMap
    (target : IndexFourUnipotentMatrix) : Matrix4 →ₗ[Real] Matrix4 where
  toFun := indexFourSylvester target
  map_add' first second := by
    unfold indexFourSylvester
    noncomm_ring
  map_smul' scalar variation := by
    unfold indexFourSylvester
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_add]
    simp

theorem indexFourSylvester_surjective
    (target : IndexFourUnipotentMatrix) :
    Function.Surjective (indexFourSylvester target) := by
  intro rhs
  exact ⟨indexFourSylvesterInverse target rhs,
    indexFourSylvester_inverse_apply target rhs⟩

theorem indexFourSylvester_injective
    (target : IndexFourUnipotentMatrix) :
    Function.Injective (indexFourSylvester target) := by
  have hSurjective :
      Function.Surjective (indexFourSylvesterLinearMap target) :=
    indexFourSylvester_surjective target
  exact LinearMap.injective_iff_surjective.mpr hSurjective

theorem indexFourSylvesterInverse_apply
    (target : IndexFourUnipotentMatrix) (variation : Matrix4) :
    indexFourSylvesterInverse target (indexFourSylvester target variation) =
      variation := by
  apply indexFourSylvester_injective target
  exact indexFourSylvester_inverse_apply target
    (indexFourSylvester target variation)

theorem indexFourSylvester_bijective (target : IndexFourUnipotentMatrix) :
    Function.Bijective (indexFourSylvester target) :=
  ⟨indexFourSylvester_injective target,
    indexFourSylvester_surjective target⟩

def positiveTargetInIndexFourGluedLocus
    (target : positiveDiagonalizableLocus) :
    PositiveOrIndexFourRootMatrix :=
  ⟨target.1, Or.inl target.property⟩

def indexFourTargetInGluedLocus
    (target : IndexFourUnipotentMatrix) :
    PositiveOrIndexFourRootMatrix :=
  ⟨target.1, Or.inr target.property⟩

private def indexFourTargetOfNotPositive
    (target : PositiveOrIndexFourRootMatrix)
    (hNotPositive : target.1 ∉ positiveDiagonalizableLocus) :
    IndexFourUnipotentMatrix :=
  ⟨target.1, target.property.resolve_left hNotPositive⟩

def positiveOrIndexFourRoot
    (target : PositiveOrIndexFourRootMatrix) : Matrix4 := by
  classical
  exact if hPositive : target.1 ∈ positiveDiagonalizableLocus then
    positiveDiagonalizableGlobalRoot ⟨target.1, hPositive⟩
  else
    indexFourUnipotentRoot
      (indexFourTargetOfNotPositive target hPositive)

@[simp]
theorem positiveOrIndexFourRoot_on_positive
    (target : positiveDiagonalizableLocus) :
    positiveOrIndexFourRoot (positiveTargetInIndexFourGluedLocus target) =
      positiveDiagonalizableGlobalRoot target := by
  unfold positiveOrIndexFourRoot
  dsimp only [positiveTargetInIndexFourGluedLocus]
  rw [dif_pos target.property]

private theorem positiveDiagonalizableGlobalRoot_one
    (hOne : (1 : Matrix4) ∈ positiveDiagonalizableLocus) :
    positiveDiagonalizableGlobalRoot ⟨1, hOne⟩ = 1 := by
  rw [positiveDiagonalizableGlobalRoot_eq_of_presentation
    ⟨1, hOne⟩ identityPositiveDiagonalizableRelativeMatrix rfl]
  exact identityPositiveDiagonalizableRelativeMatrix_root

theorem positive_and_indexFour_roots_agree
    (target : Matrix4)
    (hPositive : target ∈ positiveDiagonalizableLocus)
    (hIndexFour : target ∈ indexFourUnipotentLocus) :
    positiveDiagonalizableGlobalRoot ⟨target, hPositive⟩ =
      indexFourUnipotentRoot ⟨target, hIndexFour⟩ := by
  have hTarget : target = 1 := by
    have hMembership : target ∈
        positiveDiagonalizableLocus ∩ indexFourUnipotentLocus :=
      ⟨hPositive, hIndexFour⟩
    rw [positiveDiagonalizable_inter_indexFourUnipotent] at hMembership
    simpa using hMembership
  subst target
  rw [positiveDiagonalizableGlobalRoot_one]
  simp [indexFourUnipotentRoot, indexFourRootPolynomial]

@[simp]
theorem positiveOrIndexFourRoot_on_indexFour
    (target : IndexFourUnipotentMatrix) :
    positiveOrIndexFourRoot (indexFourTargetInGluedLocus target) =
      indexFourUnipotentRoot target := by
  classical
  unfold positiveOrIndexFourRoot
  dsimp only [indexFourTargetInGluedLocus]
  split
  · next hPositive =>
      exact positive_and_indexFour_roots_agree
        target.1 hPositive target.property
  · rfl

theorem positiveOrIndexFourRoot_square
    (target : PositiveOrIndexFourRootMatrix) :
    positiveOrIndexFourRoot target * positiveOrIndexFourRoot target =
      target.1 := by
  classical
  by_cases hPositive : target.1 ∈ positiveDiagonalizableLocus
  · rw [positiveOrIndexFourRoot, dif_pos hPositive]
    exact positiveDiagonalizableGlobalRoot_square ⟨target.1, hPositive⟩
  · rw [positiveOrIndexFourRoot, dif_neg hPositive]
    exact indexFourUnipotentRoot_square
      (indexFourTargetOfNotPositive target hPositive)

def previousGluedTargetInIndexFourLocus
    (target : PositiveOrIndexThreeRootMatrix) :
    PositiveOrIndexFourRootMatrix :=
  ⟨target.1, target.property.elim Or.inl
    (fun hIndexThree => Or.inr
      (indexThreeUnipotentLocus_subset_indexFourUnipotentLocus hIndexThree))⟩

theorem positiveOrIndexFourRoot_extends_indexThreeGluing
    (target : PositiveOrIndexThreeRootMatrix) :
    positiveOrIndexFourRoot
        (previousGluedTargetInIndexFourLocus target) =
      positiveOrIndexThreeRoot target := by
  classical
  by_cases hPositive : target.1 ∈ positiveDiagonalizableLocus
  · let positiveTarget : positiveDiagonalizableLocus :=
      ⟨target.1, hPositive⟩
    have hOldTarget : target =
        positiveTargetInIndexThreeGluedLocus positiveTarget :=
      Subtype.ext (by rfl)
    have hNewTarget : previousGluedTargetInIndexFourLocus target =
        positiveTargetInIndexFourGluedLocus positiveTarget :=
      Subtype.ext (by rfl)
    calc
      positiveOrIndexFourRoot
          (previousGluedTargetInIndexFourLocus target) =
        positiveOrIndexFourRoot
          (positiveTargetInIndexFourGluedLocus positiveTarget) :=
            congrArg positiveOrIndexFourRoot hNewTarget
      _ = positiveDiagonalizableGlobalRoot positiveTarget :=
        positiveOrIndexFourRoot_on_positive positiveTarget
      _ = positiveOrIndexThreeRoot
          (positiveTargetInIndexThreeGluedLocus positiveTarget) :=
        (positiveOrIndexThreeRoot_on_positive positiveTarget).symm
      _ = positiveOrIndexThreeRoot target :=
        congrArg positiveOrIndexThreeRoot hOldTarget.symm
  · have hIndexThree : target.1 ∈ indexThreeUnipotentLocus :=
      target.property.resolve_left hPositive
    let oldTarget : IndexThreeUnipotentMatrix := ⟨target.1, hIndexThree⟩
    let newTarget : IndexFourUnipotentMatrix :=
      promoteIndexThreeToIndexFour oldTarget
    have hOldTarget : target = indexThreeTargetInGluedLocus oldTarget :=
      Subtype.ext (by rfl)
    have hNewTarget : previousGluedTargetInIndexFourLocus target =
        indexFourTargetInGluedLocus newTarget := Subtype.ext (by rfl)
    calc
      positiveOrIndexFourRoot
          (previousGluedTargetInIndexFourLocus target) =
        positiveOrIndexFourRoot (indexFourTargetInGluedLocus newTarget) :=
          congrArg positiveOrIndexFourRoot hNewTarget
      _ = indexFourUnipotentRoot newTarget :=
        positiveOrIndexFourRoot_on_indexFour newTarget
      _ = indexThreeUnipotentRoot oldTarget :=
        indexFourUnipotentRoot_on_indexThree oldTarget
      _ = positiveOrIndexThreeRoot
          (indexThreeTargetInGluedLocus oldTarget) :=
        (positiveOrIndexThreeRoot_on_indexThree oldTarget).symm
      _ = positiveOrIndexThreeRoot target :=
        congrArg positiveOrIndexThreeRoot hOldTarget.symm

theorem positiveOrIndexFour_stratum_classification
    (target : PositiveOrIndexFourRootMatrix) :
    target.1 ∈ positiveDiagonalizableLocus ∨
      (target.1 ∈ indexFourUnipotentLocus ∧ target.1 ≠ 1 ∧
        ¬ IsRealDiagonalizable4 target.1) := by
  classical
  by_cases hPositive : target.1 ∈ positiveDiagonalizableLocus
  · exact Or.inl hPositive
  · right
    have hIndexFour : target.1 ∈ indexFourUnipotentLocus :=
      target.property.resolve_left hPositive
    have hNe : target.1 ≠ 1 := by
      intro hOne
      apply hPositive
      simpa [hOne] using one_mem_positiveDiagonalizableLocus
    exact ⟨hIndexFour, hNe,
      indexFourUnipotent_not_realDiagonalizable
        ⟨target.1, hIndexFour⟩ hNe⟩

theorem outside_positiveOrIndexFourRootLocus_iff (target : Matrix4) :
    target ∉ positiveOrIndexFourRootLocus ↔
      target ∉ positiveDiagonalizableLocus ∧
        jordanDisplacementFourth target ≠ 0 := by
  simp [positiveOrIndexFourRootLocus, indexFourUnipotentLocus]

theorem positiveOrIndexFourRoot_positiveRestriction_continuous :
    Continuous (fun target : positiveDiagonalizableLocus =>
      positiveOrIndexFourRoot
        (positiveTargetInIndexFourGluedLocus target)) := by
  simpa only [positiveOrIndexFourRoot_on_positive] using
    positiveDiagonalizableGlobalRoot_continuous

theorem indexFourUnipotentRoot_continuous :
    Continuous indexFourUnipotentRoot := by
  unfold indexFourUnipotentRoot indexFourRootPolynomial
  fun_prop

theorem positiveOrIndexFourRoot_indexFourRestriction_continuous :
    Continuous (fun target : IndexFourUnipotentMatrix =>
      positiveOrIndexFourRoot (indexFourTargetInGluedLocus target)) := by
  simpa only [positiveOrIndexFourRoot_on_indexFour] using
    indexFourUnipotentRoot_continuous

end

end P0EFTJanusLorentzJordanIndexFourStratifiedRootGluing4D
end JanusFormal
