import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPositiveDiagonalizableGlobalRootContinuity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusLorentzJordanSylvesterRegular4D

/-!
# Gluing the positive and index-two Lorentz--Jordan root strata

The explicit Lorentz--Jordan family satisfies the coordinate-free polynomial
condition `(A - I)^2 = 0`.  This gate closes the whole algebraic stratum cut
out by that condition, not only the original one-parameter presentation.  Its
canonical root is `I + (A - I)/2`, is similarity equivariant, and has an
explicit inverse Sylvester map.

The index-two stratum meets the positive real-diagonalizable locus only at
`I`.  The two selected roots agree there, hence glue to a presentation-free
square root on their union.  Both restrictions are continuous.  We do not
claim that every matrix in the algebraic index-two stratum is a relative pair
of Lorentz metrics; the existing explicit family remains the certified
Lorentz-admissible subfamily.  Higher Jordan indices and non-unipotent Jordan
spectra remain outside this gate.
-/

namespace JanusFormal
namespace P0EFTJanusLorentzJordanStratifiedRootGluing4D

set_option autoImplicit false

noncomputable section

open scoped Matrix.Norms.Frobenius RightActions Topology
open P0EFTJanusPositiveDiagonalizableRelativeRoot4D
open P0EFTJanusPositiveDiagonalizableRootGluing4D
open P0EFTJanusPositiveDiagonalizableGlobalRootContinuity4D
open P0EFTJanusLorentzJordanRelativeRoot4D
open P0EFTJanusLorentzJordanAdmissibleSignature4D
open P0EFTJanusLorentzJordanSylvesterRegular4D

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

/-- The conjugacy-covariant polynomial which detects the closed index-two
unipotent Jordan envelope. -/
def jordanDisplacementSquare (target : Matrix4) : Matrix4 :=
  (target - 1) * (target - 1)

/-- The complete algebraic stratum on which the Jordan root truncates after
its linear nilpotent term. -/
def indexTwoUnipotentLocus : Set Matrix4 :=
  {target | jordanDisplacementSquare target = 0}

abbrev IndexTwoUnipotentMatrix := indexTwoUnipotentLocus

/-- The known positive and index-two Jordan strata, with their common identity
point retained for gluing. -/
def positiveOrIndexTwoRootLocus : Set Matrix4 :=
  positiveDiagonalizableLocus ∪ indexTwoUnipotentLocus

abbrev PositiveOrIndexTwoRootMatrix := positiveOrIndexTwoRootLocus

theorem one_mem_positiveDiagonalizableLocus :
    (1 : Matrix4) ∈ positiveDiagonalizableLocus :=
  ⟨identityPositiveDiagonalizableRelativeMatrix, rfl⟩

theorem one_mem_indexTwoUnipotentLocus :
    (1 : Matrix4) ∈ indexTwoUnipotentLocus := by
  simp [indexTwoUnipotentLocus, jordanDisplacementSquare]

/-- Every positive diagonalization is a real diagonalization in the explicit
notion used by the Lorentz--Jordan obstruction. -/
theorem positiveDiagonalizable_isRealDiagonalizable4
    (data : PositiveDiagonalizableRelativeMatrix) :
    IsRealDiagonalizable4 data.target :=
  ⟨data.eigenbasis, data.eigenbasisInv, Matrix.diagonal data.eigenvalue,
    data.inv_mul_basis, data.basis_mul_inv,
    Matrix.isDiag_diagonal data.eigenvalue,
    data.target_eq⟩

private theorem diagonal4_square_zero_implies_zero
    (diagonal : Matrix4) (hDiagonal : diagonal.IsDiag)
    (hSquare : diagonal * diagonal = 0) :
    diagonal = 0 := by
  have hSquareDiag :
      Matrix.diagonal (Matrix.diag diagonal) *
          Matrix.diagonal (Matrix.diag diagonal) = 0 := by
    rw [hDiagonal.diagonal_diag]
    exact hSquare
  rw [← hDiagonal.diagonal_diag]
  ext first second
  by_cases hIndices : first = second
  · subst second
    have hEntry := congrArg
      (fun matrix : Matrix4 => matrix first first) hSquareDiag
    simp at hEntry
    simpa using hEntry
  · simp [hIndices]

private theorem diagonal4_eq_one_of_displacement_square_zero
    (diagonal : Matrix4) (hDiagonal : diagonal.IsDiag)
    (hSquare : jordanDisplacementSquare diagonal = 0) :
    diagonal = 1 := by
  apply sub_eq_zero.mp
  apply diagonal4_square_zero_implies_zero (diagonal - 1)
    (hDiagonal.sub Matrix.isDiag_one)
  exact hSquare

/-- A nonidentity member of the index-two envelope is genuinely
nondiagonalizable. -/
theorem indexTwoUnipotent_not_realDiagonalizable
    (target : IndexTwoUnipotentMatrix) (hTarget : target.1 ≠ 1) :
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
  have hDiagonalSquare : jordanDisplacementSquare diagonal = 0 := by
    unfold jordanDisplacementSquare
    rw [← hConjugatedDifference]
    calc
      (inverse * (target.1 - 1) * change) *
          (inverse * (target.1 - 1) * change) =
        inverse * (target.1 - 1) * (change * inverse) *
          (target.1 - 1) * change := by noncomm_ring
      _ = inverse * jordanDisplacementSquare target.1 * change := by
        rw [hChangeInverse]
        simp [jordanDisplacementSquare, mul_assoc]
      _ = 0 := by rw [target.property]; simp
  have hDiagonalOne := diagonal4_eq_one_of_displacement_square_zero
    diagonal hDiagonal hDiagonalSquare
  apply hTarget
  rw [hSimilarity, hDiagonalOne, mul_one, hChangeInverse]

/-- The overlap of the positive and index-two strata is exactly the identity
matrix. -/
theorem positiveDiagonalizable_inter_indexTwoUnipotent :
    positiveDiagonalizableLocus ∩ indexTwoUnipotentLocus =
      ({1} : Set Matrix4) := by
  ext target
  constructor
  · rintro ⟨hPositive, hIndexTwo⟩
    have hTarget : target = 1 := by
      by_contra hNe
      rcases hPositive with ⟨data, hData⟩
      apply indexTwoUnipotent_not_realDiagonalizable
        ⟨target, hIndexTwo⟩ hNe
      simpa [hData] using positiveDiagonalizable_isRealDiagonalizable4 data
    simp [hTarget]
  · intro hSingleton
    have hTarget : target = 1 := by simpa using hSingleton
    subst target
    exact ⟨one_mem_positiveDiagonalizableLocus,
      one_mem_indexTwoUnipotentLocus⟩

/-- The displacement-square test is preserved by every genuine similarity. -/
theorem jordanDisplacementSquare_similarity
    (target change inverse : Matrix4)
    (hInverseChange : inverse * change = 1)
    (hChangeInverse : change * inverse = 1) :
    jordanDisplacementSquare (change * target * inverse) =
      change * jordanDisplacementSquare target * inverse := by
  have hDifference :
      change * target * inverse - 1 =
        change * (target - 1) * inverse := by
    noncomm_ring [hChangeInverse]
  unfold jordanDisplacementSquare
  rw [hDifference]
  calc
    (change * (target - 1) * inverse) *
        (change * (target - 1) * inverse) =
      change * (target - 1) * (inverse * change) *
        (target - 1) * inverse := by noncomm_ring
    _ = change * ((target - 1) * (target - 1)) * inverse := by
      rw [hInverseChange]
      simp [mul_assoc]

/-- Consequently the index-two stratum contains all similarity conjugates of
each of its presentations. -/
theorem indexTwoUnipotent_similarity_mem
    (target : IndexTwoUnipotentMatrix) (change inverse : Matrix4)
    (hInverseChange : inverse * change = 1)
    (hChangeInverse : change * inverse = 1) :
    change * target.1 * inverse ∈ indexTwoUnipotentLocus := by
  rw [indexTwoUnipotentLocus, Set.mem_setOf_eq,
    jordanDisplacementSquare_similarity target.1 change inverse
      hInverseChange hChangeInverse,
    target.property]
  simp

/-- Canonical polynomial root on the complete index-two envelope. -/
def indexTwoUnipotentRoot (target : IndexTwoUnipotentMatrix) : Matrix4 :=
  1 + (1 / 2 : Real) • (target.1 - 1)

theorem indexTwoUnipotentRoot_square
    (target : IndexTwoUnipotentMatrix) :
    indexTwoUnipotentRoot target * indexTwoUnipotentRoot target = target.1 := by
  let nilpotent : Matrix4 := target.1 - 1
  have hSquare : nilpotent * nilpotent = 0 := target.property
  have hTarget : target.1 = 1 + nilpotent := by
    dsimp [nilpotent]
    noncomm_ring
  unfold indexTwoUnipotentRoot
  change (1 + (1 / 2 : Real) • nilpotent) *
      (1 + (1 / 2 : Real) • nilpotent) = target.1
  rw [hTarget]
  noncomm_ring [hSquare]
  module

/-- The polynomial selector itself is similarity equivariant. -/
theorem indexTwoUnipotentRoot_similarity
    (target : IndexTwoUnipotentMatrix) (change inverse : Matrix4)
    (hInverseChange : inverse * change = 1)
    (hChangeInverse : change * inverse = 1) :
    indexTwoUnipotentRoot
        ⟨change * target.1 * inverse,
          indexTwoUnipotent_similarity_mem target change inverse
            hInverseChange hChangeInverse⟩ =
      change * indexTwoUnipotentRoot target * inverse := by
  unfold indexTwoUnipotentRoot
  noncomm_ring [hInverseChange, hChangeInverse]

/-- Sylvester operator at the canonical index-two root. -/
def indexTwoSylvester
    (target : IndexTwoUnipotentMatrix) (variation : Matrix4) : Matrix4 :=
  indexTwoUnipotentRoot target * variation +
    variation * indexTwoUnipotentRoot target

/-- Finite inverse valid on the entire index-two envelope. -/
def indexTwoSylvesterInverse
    (target : IndexTwoUnipotentMatrix) (rhs : Matrix4) : Matrix4 :=
  let nilpotent := target.1 - 1
  (1 / 2 : Real) • rhs -
    (1 / 8 : Real) • (nilpotent * rhs + rhs * nilpotent) +
    (1 / 16 : Real) • (nilpotent * rhs * nilpotent)

theorem indexTwoSylvester_inverse_apply
    (target : IndexTwoUnipotentMatrix) (rhs : Matrix4) :
    indexTwoSylvester target (indexTwoSylvesterInverse target rhs) = rhs := by
  let nilpotent : Matrix4 := target.1 - 1
  have hSquare : nilpotent * nilpotent = 0 := target.property
  have hLeft (matrix : Matrix4) :
      nilpotent * (nilpotent * matrix) = 0 := by
    rw [← mul_assoc, hSquare, zero_mul]
  unfold indexTwoSylvester indexTwoSylvesterInverse indexTwoUnipotentRoot
  change
    (1 + (1 / 2 : Real) • nilpotent) *
          ((1 / 2 : Real) • rhs -
            (1 / 8 : Real) • (nilpotent * rhs + rhs * nilpotent) +
            (1 / 16 : Real) • (nilpotent * rhs * nilpotent)) +
        ((1 / 2 : Real) • rhs -
            (1 / 8 : Real) • (nilpotent * rhs + rhs * nilpotent) +
            (1 / 16 : Real) • (nilpotent * rhs * nilpotent)) *
          (1 + (1 / 2 : Real) • nilpotent) = rhs
  noncomm_ring [hSquare]
  simp only [hLeft, smul_zero, add_zero]
  module

theorem indexTwoSylvesterInverse_apply
    (target : IndexTwoUnipotentMatrix) (variation : Matrix4) :
    indexTwoSylvesterInverse target (indexTwoSylvester target variation) =
      variation := by
  let nilpotent : Matrix4 := target.1 - 1
  have hSquare : nilpotent * nilpotent = 0 := target.property
  have hLeft (matrix : Matrix4) :
      nilpotent * (nilpotent * matrix) = 0 := by
    rw [← mul_assoc, hSquare, zero_mul]
  unfold indexTwoSylvester indexTwoSylvesterInverse indexTwoUnipotentRoot
  change
    (1 / 2 : Real) •
          ((1 + (1 / 2 : Real) • nilpotent) * variation +
            variation * (1 + (1 / 2 : Real) • nilpotent)) -
        (1 / 8 : Real) •
          (nilpotent *
              ((1 + (1 / 2 : Real) • nilpotent) * variation +
                variation * (1 + (1 / 2 : Real) • nilpotent)) +
            ((1 + (1 / 2 : Real) • nilpotent) * variation +
                variation * (1 + (1 / 2 : Real) • nilpotent)) *
              nilpotent) +
        (1 / 16 : Real) •
          (nilpotent *
              ((1 + (1 / 2 : Real) • nilpotent) * variation +
                variation * (1 + (1 / 2 : Real) • nilpotent)) *
            nilpotent) = variation
  noncomm_ring [hSquare]
  simp only [hLeft, smul_zero, add_zero]
  module

theorem indexTwoSylvester_bijective (target : IndexTwoUnipotentMatrix) :
    Function.Bijective (indexTwoSylvester target) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨indexTwoSylvesterInverse target,
      indexTwoSylvesterInverse_apply target,
      indexTwoSylvester_inverse_apply target⟩

/-- The original Lorentz-certified Jordan family lies in the full index-two
envelope. -/
def lorentzJordanIndexTwoTarget (parameter : Real) :
    IndexTwoUnipotentMatrix :=
  ⟨jordanRelative4 parameter, jordanRelative4_displacement_square parameter⟩

@[simp]
theorem indexTwoUnipotentRoot_lorentzJordan
    (parameter : Real) :
    indexTwoUnipotentRoot (lorentzJordanIndexTwoTarget parameter) =
      jordanRoot4 parameter := by
  ext first second
  fin_cases first <;> fin_cases second <;>
    simp [indexTwoUnipotentRoot, lorentzJordanIndexTwoTarget,
      jordanRelative4, jordanRoot4, jordanNilpotent4]
  all_goals ring

/-- Inclusion of the positive stratum into the glued domain. -/
def positiveTargetInGluedLocus
    (target : positiveDiagonalizableLocus) :
    PositiveOrIndexTwoRootMatrix :=
  ⟨target.1, Or.inl target.property⟩

/-- Inclusion of the index-two stratum into the glued domain. -/
def indexTwoTargetInGluedLocus
    (target : IndexTwoUnipotentMatrix) :
    PositiveOrIndexTwoRootMatrix :=
  ⟨target.1, Or.inr target.property⟩

private def indexTwoTargetOfNotPositive
    (target : PositiveOrIndexTwoRootMatrix)
    (hNotPositive : target.1 ∉ positiveDiagonalizableLocus) :
    IndexTwoUnipotentMatrix :=
  ⟨target.1, target.property.resolve_left hNotPositive⟩

/-- Presentation-free selector on the union of the two proved strata. -/
def positiveOrIndexTwoRoot
    (target : PositiveOrIndexTwoRootMatrix) : Matrix4 :=
  by
    classical
    exact if hPositive : target.1 ∈ positiveDiagonalizableLocus then
      positiveDiagonalizableGlobalRoot ⟨target.1, hPositive⟩
    else
      indexTwoUnipotentRoot
        (indexTwoTargetOfNotPositive target hPositive)

@[simp]
theorem positiveOrIndexTwoRoot_on_positive
    (target : positiveDiagonalizableLocus) :
    positiveOrIndexTwoRoot (positiveTargetInGluedLocus target) =
      positiveDiagonalizableGlobalRoot target := by
  simp [positiveOrIndexTwoRoot, positiveTargetInGluedLocus,
    target.property]

private theorem positiveDiagonalizableGlobalRoot_one
    (hOne : (1 : Matrix4) ∈ positiveDiagonalizableLocus) :
    positiveDiagonalizableGlobalRoot ⟨1, hOne⟩ = 1 := by
  rw [positiveDiagonalizableGlobalRoot_eq_of_presentation
    ⟨1, hOne⟩ identityPositiveDiagonalizableRelativeMatrix rfl]
  exact identityPositiveDiagonalizableRelativeMatrix_root

/-- The two formulas agree on their exact one-point overlap. -/
theorem positive_and_indexTwo_roots_agree
    (target : Matrix4)
    (hPositive : target ∈ positiveDiagonalizableLocus)
    (hIndexTwo : target ∈ indexTwoUnipotentLocus) :
    positiveDiagonalizableGlobalRoot ⟨target, hPositive⟩ =
      indexTwoUnipotentRoot ⟨target, hIndexTwo⟩ := by
  have hTarget : target = 1 := by
    have hMembership : target ∈
        positiveDiagonalizableLocus ∩ indexTwoUnipotentLocus :=
      ⟨hPositive, hIndexTwo⟩
    rw [positiveDiagonalizable_inter_indexTwoUnipotent] at hMembership
    simpa using hMembership
  subst target
  rw [positiveDiagonalizableGlobalRoot_one]
  simp [indexTwoUnipotentRoot]

@[simp]
theorem positiveOrIndexTwoRoot_on_indexTwo
    (target : IndexTwoUnipotentMatrix) :
    positiveOrIndexTwoRoot (indexTwoTargetInGluedLocus target) =
      indexTwoUnipotentRoot target := by
  classical
  unfold positiveOrIndexTwoRoot
  dsimp only [indexTwoTargetInGluedLocus]
  split
  · next hPositive =>
      exact positive_and_indexTwo_roots_agree
        target.1 hPositive target.property
  · rfl

/-- The glued selector squares to its target on the whole proved union. -/
theorem positiveOrIndexTwoRoot_square
    (target : PositiveOrIndexTwoRootMatrix) :
    positiveOrIndexTwoRoot target * positiveOrIndexTwoRoot target = target.1 := by
  classical
  by_cases hPositive : target.1 ∈ positiveDiagonalizableLocus
  · rw [positiveOrIndexTwoRoot, dif_pos hPositive]
    exact positiveDiagonalizableGlobalRoot_square ⟨target.1, hPositive⟩
  · rw [positiveOrIndexTwoRoot, dif_neg hPositive]
    exact indexTwoUnipotentRoot_square
      (indexTwoTargetOfNotPositive target hPositive)

/-- Exact disjoint classification after assigning the common identity to the
positive stratum. -/
theorem positiveOrIndexTwo_stratum_classification
    (target : PositiveOrIndexTwoRootMatrix) :
    target.1 ∈ positiveDiagonalizableLocus ∨
      (target.1 ∈ indexTwoUnipotentLocus ∧ target.1 ≠ 1 ∧
        ¬ IsRealDiagonalizable4 target.1) := by
  classical
  by_cases hPositive : target.1 ∈ positiveDiagonalizableLocus
  · exact Or.inl hPositive
  · right
    have hIndexTwo : target.1 ∈ indexTwoUnipotentLocus :=
      target.property.resolve_left hPositive
    have hNe : target.1 ≠ 1 := by
      intro hOne
      apply hPositive
      simpa [hOne] using one_mem_positiveDiagonalizableLocus
    exact ⟨hIndexTwo, hNe,
      indexTwoUnipotent_not_realDiagonalizable
        ⟨target.1, hIndexTwo⟩ hNe⟩

/-- The exact residual outside this extension is a positive-locus failure
together with a nonzero displacement-square invariant. -/
theorem outside_positiveOrIndexTwoRootLocus_iff (target : Matrix4) :
    target ∉ positiveOrIndexTwoRootLocus ↔
      target ∉ positiveDiagonalizableLocus ∧
        jordanDisplacementSquare target ≠ 0 := by
  simp [positiveOrIndexTwoRootLocus, indexTwoUnipotentLocus]

/-- Continuity on the positive restriction follows from the global positive
selector theorem. -/
theorem positiveOrIndexTwoRoot_positiveRestriction_continuous :
    Continuous (fun target : positiveDiagonalizableLocus =>
      positiveOrIndexTwoRoot (positiveTargetInGluedLocus target)) := by
  simpa only [positiveOrIndexTwoRoot_on_positive] using
    positiveDiagonalizableGlobalRoot_continuous

theorem indexTwoUnipotentRoot_continuous :
    Continuous indexTwoUnipotentRoot := by
  unfold indexTwoUnipotentRoot
  fun_prop

/-- The Jordan restriction is continuous, including through its identity
overlap with the positive stratum. -/
theorem positiveOrIndexTwoRoot_indexTwoRestriction_continuous :
    Continuous (fun target : IndexTwoUnipotentMatrix =>
      positiveOrIndexTwoRoot (indexTwoTargetInGluedLocus target)) := by
  simpa only [positiveOrIndexTwoRoot_on_indexTwo] using
    indexTwoUnipotentRoot_continuous

/-- The certified Lorentz family is recovered exactly inside the glued
selector, with signature, square-root and Sylvester regularity retained. -/
theorem lorentzJordan_stratified_root_closure (parameter : Real) :
    Nonempty (LorentzSignatureWitness4 plusMetric4) ∧
      Nonempty (LorentzSignatureWitness4 (minusMetric4 parameter)) ∧
      positiveOrIndexTwoRoot
          (indexTwoTargetInGluedLocus
            (lorentzJordanIndexTwoTarget parameter)) =
        jordanRoot4 parameter ∧
      jordanRoot4 parameter * jordanRoot4 parameter =
        plusMetricInverse4 * minusMetric4 parameter ∧
      Function.Bijective
        (indexTwoSylvester (lorentzJordanIndexTwoTarget parameter)) := by
  refine ⟨plusMetric4_lorentzian, minusMetric4_lorentzian parameter,
    ?_, jordanRoot4_square_eq_metricRelative4 parameter, ?_⟩
  · simp
  · exact indexTwoSylvester_bijective
      (lorentzJordanIndexTwoTarget parameter)

end

end P0EFTJanusLorentzJordanStratifiedRootGluing4D
end JanusFormal
