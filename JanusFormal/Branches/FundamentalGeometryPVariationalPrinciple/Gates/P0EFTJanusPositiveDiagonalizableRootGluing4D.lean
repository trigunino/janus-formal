import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPositiveDiagonalizableLocalRootBranch4D
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# Gluing positive diagonalizable roots in dimension four

The characteristic polynomial records the supplied positive spectrum with
multiplicity.  Consequently any two positive diagonalizations of the same
matrix have spectra related by a permutation.  This removes the remaining
presentation hypothesis from root and local-germ uniqueness and yields a
well-defined global square root on the positive diagonalizable locus.

No continuity of that global selector is asserted here; that is the remaining
analytic patching problem.
-/

namespace JanusFormal
namespace P0EFTJanusPositiveDiagonalizableRootGluing4D

set_option autoImplicit false

noncomputable section

open scoped Matrix.Norms.Frobenius RightActions Topology
open P0EFTJanusPositiveDiagonalizableRelativeRoot4D
open P0EFTJanusPositiveDiagonalizableLocalRootBranch4D

abbrev Matrix4 := P0EFTJanusPositiveDiagonalizableRelativeRoot4D.Matrix4
abbrev Spectrum4 := P0EFTJanusPositiveDiagonalizableRelativeRoot4D.Spectrum4

/-- Similarity with the supplied invertible eigenbasis preserves the
characteristic polynomial. -/
theorem positiveDiagonalizable_charpoly_eq_diagonal
    (data : PositiveDiagonalizableRelativeMatrix) :
    data.target.charpoly = (Matrix.diagonal data.eigenvalue).charpoly := by
  rw [data.target_eq, Matrix.charpoly_mul_comm]
  rw [← Matrix.mul_assoc, data.inv_mul_basis, Matrix.one_mul]

/-- The roots of the characteristic polynomial are exactly the supplied
eigenvalues, including multiplicities. -/
theorem positiveDiagonalizable_roots_charpoly_eq_spectrum
    (data : PositiveDiagonalizableRelativeMatrix) :
    data.target.charpoly.roots =
      Multiset.map data.eigenvalue Finset.univ.val := by
  rw [positiveDiagonalizable_charpoly_eq_diagonal,
    Matrix.charpoly_diagonal, Polynomial.roots_prod]
  · simp
  · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]

/-- Equal finite multisets of real tuple entries differ by an index
permutation.  Sorting is used only to construct the permutation; repeated
entries are retained with their full multiplicity. -/
theorem exists_permutation_of_spectrum_multiset_eq
    (first second : Spectrum4)
    (hMultiset : Multiset.map first Finset.univ.val =
      Multiset.map second Finset.univ.val) :
    ∃ permutation : Equiv.Perm (Fin 4),
      second = first ∘ permutation := by
  have hList : List.Perm (List.ofFn first) (List.ofFn second) :=
    Multiset.coe_eq_coe.mp (by
      simpa only [Fin.univ_val_map] using hMultiset)
  have hSortedPerm : List.Perm
      (List.ofFn (first ∘ Tuple.sort first))
      (List.ofFn (second ∘ Tuple.sort second)) :=
    ((Tuple.sort first).ofFn_comp_perm first).trans
      (hList.trans ((Tuple.sort second).ofFn_comp_perm second).symm)
  have hSorted : first ∘ Tuple.sort first =
      second ∘ Tuple.sort second := by
    apply List.ofFn_injective
    exact hSortedPerm.eq_of_pairwise'
      (Tuple.monotone_sort first).sortedLE_ofFn.pairwise
      (Tuple.monotone_sort second).sortedLE_ofFn.pairwise
  let permutation : Equiv.Perm (Fin 4) :=
    (Tuple.sort second).symm.trans (Tuple.sort first)
  refine ⟨permutation, ?_⟩
  funext index
  have hEntry := congrFun hSorted ((Tuple.sort second).symm index)
  simpa [permutation, Function.comp_def] using hEntry.symm

/-- Two positive diagonalizations of one target automatically have spectra
related by a permutation. -/
theorem positiveDiagonalizable_spectra_permuted_of_same_target
    (first second : PositiveDiagonalizableRelativeMatrix)
    (hTarget : first.target = second.target) :
    ∃ permutation : Equiv.Perm (Fin 4),
      second.eigenvalue = first.eigenvalue ∘ permutation := by
  apply exists_permutation_of_spectrum_multiset_eq
  rw [← positiveDiagonalizable_roots_charpoly_eq_spectrum first,
    hTarget, positiveDiagonalizable_roots_charpoly_eq_spectrum second]

/-- The selected positive similarity root depends only on the target matrix,
not on any eigenbasis or ordering used to present its diagonalization. -/
theorem positiveSimilarityRoot_eq_of_same_target
    (first second : PositiveDiagonalizableRelativeMatrix)
    (hTarget : first.target = second.target) :
    positiveSimilarityRoot first = positiveSimilarityRoot second := by
  obtain ⟨permutation, hSpectrum⟩ :=
    positiveDiagonalizable_spectra_permuted_of_same_target first second hTarget
  exact positiveSimilarityRoot_eq_of_same_target_and_permuted_spectrum
    first second permutation hTarget hSpectrum

/-- Local IFT branches based on arbitrary positive diagonalizations of the
same matrix have the same germ. -/
theorem eventually_positiveDiagonalizableLocalRootBranch_eq_of_same_target
    (first second : PositiveDiagonalizableRelativeMatrix)
    (hTarget : first.target = second.target) :
    ∀ᶠ target in 𝓝 first.target,
      positiveDiagonalizableLocalRootBranch first target =
        positiveDiagonalizableLocalRootBranch second target :=
  eventually_positiveDiagonalizableLocalRootBranch_eq_of_root_eq first second
    (positiveSimilarityRoot_eq_of_same_target first second hTarget)

/-- The genuine matrix locus admitting a real diagonalization with strictly
positive spectrum. -/
def positiveDiagonalizableLocus : Set Matrix4 :=
  {target | ∃ data : PositiveDiagonalizableRelativeMatrix,
    data.target = target}

/-- A presentation chosen only to define the global selector.  Its output is
proved independent of this choice below. -/
def chosenPositiveDiagonalization
    (target : positiveDiagonalizableLocus) :
    PositiveDiagonalizableRelativeMatrix :=
  Classical.choose target.property

theorem chosenPositiveDiagonalization_target
    (target : positiveDiagonalizableLocus) :
    (chosenPositiveDiagonalization target).target = target.1 :=
  Classical.choose_spec target.property

/-- The presentation-independent positive square root on the complete
positive diagonalizable locus. -/
def positiveDiagonalizableGlobalRoot
    (target : positiveDiagonalizableLocus) : Matrix4 :=
  positiveSimilarityRoot (chosenPositiveDiagonalization target)

/-- The global selector agrees with every supplied presentation of its target. -/
theorem positiveDiagonalizableGlobalRoot_eq_of_presentation
    (target : positiveDiagonalizableLocus)
    (data : PositiveDiagonalizableRelativeMatrix)
    (hData : data.target = target.1) :
    positiveDiagonalizableGlobalRoot target = positiveSimilarityRoot data :=
  positiveSimilarityRoot_eq_of_same_target
    (chosenPositiveDiagonalization target) data
    ((chosenPositiveDiagonalization_target target).trans hData.symm)

/-- The global selector squares exactly to its target. -/
theorem positiveDiagonalizableGlobalRoot_square
    (target : positiveDiagonalizableLocus) :
    positiveDiagonalizableGlobalRoot target *
        positiveDiagonalizableGlobalRoot target = target.1 := by
  rw [positiveDiagonalizableGlobalRoot,
    positiveSimilarityRoot_square,
    chosenPositiveDiagonalization_target]

end

end P0EFTJanusPositiveDiagonalizableRootGluing4D
end JanusFormal
