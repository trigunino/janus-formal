import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPositiveAffineJordanRoot4D

/-! # Monomial singular similarities of a positive Jordan collision -/

namespace JanusFormal
namespace P0EFTJanusMonomialSingularSimilarityJordan4D

set_option autoImplicit false
noncomputable section

open Filter
open scoped Topology
open P0EFTJanusPositiveAffineJordanRoot4D

abbrev Matrix4 := P0EFTJanusPositiveAffineJordanRoot4D.Matrix4

def monomialSingularChange (k : Nat) (t : Real) : Matrix4 :=
  !![t ^ k, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

def monomialSingularInverse (k : Nat) (t : Real) : Matrix4 :=
  !![(t ^ k)⁻¹, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

theorem monomialSingularInverse_mul_change
    (k : Nat) {t : Real} (ht : t ≠ 0) :
    monomialSingularInverse k t * monomialSingularChange k t = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [monomialSingularInverse, monomialSingularChange,
      Matrix.mul_apply, Fin.sum_univ_succ, ht]

theorem monomialSingularChange_mul_inverse
    (k : Nat) {t : Real} (ht : t ≠ 0) :
    monomialSingularChange k t * monomialSingularInverse k t = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [monomialSingularInverse, monomialSingularChange,
      Matrix.mul_apply, Fin.sum_univ_succ, ht]

/-- Conjugation by `diag(t^k,1,1,1)` adds `k` to the nilpotent vanishing
order. -/
theorem monomialSingularSimilarity_shifts_order
    (m n k : Nat) {t : Real} (ht : t ≠ 0) :
    monomialSingularChange k t * monomialJordanRoot m n t *
        monomialSingularInverse k t =
      monomialJordanRoot m (n + k) t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [monomialSingularChange, monomialSingularInverse,
      monomialJordanRoot, Matrix.mul_apply, Fin.sum_univ_succ, pow_add, ht]
  all_goals field_simp [pow_ne_zero _ ht] <;> ring

theorem monomialSingularSimilarity_vanishing_limit
    {m n k : Nat} (hm : 0 < m) (hmnk : m < n + k) :
    Tendsto (fun t => monomialSingularChange k t * monomialJordanRoot m n t *
        monomialSingularInverse k t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds collapsedJordanLimit) := by
  apply (monomialJordanRoot_vanishing_limit hm hmnk).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (monomialSingularSimilarity_shifts_order m n k ht.ne').symm

theorem monomialSingularSimilarity_critical_limit
    {m n k : Nat} (hm : 0 < m) (hmnk : m = n + k) :
    Tendsto (fun t => monomialSingularChange k t * monomialJordanRoot m n t *
        monomialSingularInverse k t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds criticalJordanLimit) := by
  subst m
  apply (monomialJordanRoot_critical_limit hm).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (monomialSingularSimilarity_shifts_order (n + k) n k ht.ne').symm

theorem monomialSingularSimilarity_diverging_entry
    {m n k : Nat} (hnkm : n + k < m) :
    Tendsto (fun t =>
      (monomialSingularChange k t * monomialJordanRoot m n t *
        monomialSingularInverse k t) 0 1)
      (nhdsWithin 0 (Set.Ioi 0)) atTop := by
  apply (monomialJordanCoefficient_diverging hnkm).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact congrArg (fun matrix : Matrix4 => matrix 0 1)
    (monomialSingularSimilarity_shifts_order m n k ht.ne').symm

end
end P0EFTJanusMonomialSingularSimilarityJordan4D
end JanusFormal
