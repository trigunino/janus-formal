import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMonomialSingularSimilarityJordan4D

/-! # Entry valuations under multi-exponent diagonal similarities -/

namespace JanusFormal
namespace P0EFTJanusMultiExponentDiagonalSimilarity4D

set_option autoImplicit false
noncomputable section

open Filter
open scoped Topology
open P0EFTJanusPositiveAffineJordanRoot4D
open P0EFTJanusGlobalDiagonalPowerLawZeroOverZeroClassification4D

abbrev Matrix4 := P0EFTJanusPositiveAffineJordanRoot4D.Matrix4

def multiExponentChange (exponent : Fin 4 → Nat) (t : Real) : Matrix4 :=
  Matrix.diagonal (fun i => t ^ exponent i)

def multiExponentInverse (exponent : Fin 4 → Nat) (t : Real) : Matrix4 :=
  Matrix.diagonal (fun i => (t ^ exponent i)⁻¹)

theorem multiExponentInverse_mul_change
    (exponent : Fin 4 → Nat) {t : Real} (ht : t ≠ 0) :
    multiExponentInverse exponent t * multiExponentChange exponent t = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [multiExponentInverse, multiExponentChange, Matrix.mul_apply,
      Fin.sum_univ_succ, pow_ne_zero _ ht]

theorem multiExponentChange_mul_inverse
    (exponent : Fin 4 → Nat) {t : Real} (ht : t ≠ 0) :
    multiExponentChange exponent t * multiExponentInverse exponent t = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [multiExponentInverse, multiExponentChange, Matrix.mul_apply,
      Fin.sum_univ_succ, pow_ne_zero _ ht]

/-- Exact entrywise conjugation law. -/
theorem multiExponentSimilarity_entry
    (exponent : Fin 4 → Nat) (matrix : Matrix4) (t : Real) (i j : Fin 4) :
    (multiExponentChange exponent t * matrix *
        multiExponentInverse exponent t) i j =
      t ^ exponent i * matrix i j * (t ^ exponent j)⁻¹ := by
  fin_cases i <;> fin_cases j <;>
    simp [multiExponentChange, multiExponentInverse, Matrix.mul_apply,
      Fin.sum_univ_succ]

def transportedMonomialEntry (rowExponent columnExponent order : Nat)
    (coefficient t : Real) : Real :=
  t ^ rowExponent * (coefficient * t ^ order) * (t ^ columnExponent)⁻¹

theorem transportedMonomialEntry_eq_positivePower
    {rowExponent columnExponent order : Nat}
    (h : columnExponent ≤ rowExponent + order) {coefficient t : Real}
    (ht : t ≠ 0) :
    transportedMonomialEntry rowExponent columnExponent order coefficient t =
      coefficient * t ^ (rowExponent + order - columnExponent) := by
  rw [transportedMonomialEntry]
  calc
    t ^ rowExponent * (coefficient * t ^ order) * (t ^ columnExponent)⁻¹ =
        coefficient * t ^ (rowExponent + order) * (t ^ columnExponent)⁻¹ := by
          rw [pow_add]; ring
    _ = coefficient * t ^ (rowExponent + order - columnExponent) := by
      rw [pow_sub₀ t ht h]
      field_simp [pow_ne_zero _ ht]

theorem transportedMonomialEntry_eq_inversePower
    {rowExponent columnExponent order : Nat}
    (h : rowExponent + order ≤ columnExponent) {coefficient t : Real}
    (ht : t ≠ 0) :
    transportedMonomialEntry rowExponent columnExponent order coefficient t =
      coefficient * (t ^ (columnExponent - (rowExponent + order)))⁻¹ := by
  rw [transportedMonomialEntry]
  have hp := pow_sub₀ t ht h
  rw [show t ^ rowExponent * (coefficient * t ^ order) =
      coefficient * t ^ (rowExponent + order) by rw [pow_add]; ring]
  field_simp [pow_ne_zero _ ht]
  calc
    coefficient * t ^ (rowExponent + order) *
        t ^ (columnExponent - (rowExponent + order)) =
      coefficient * (t ^ (rowExponent + order) *
        t ^ (columnExponent - (rowExponent + order))) := by ring
    _ = coefficient * t ^ ((rowExponent + order) +
        (columnExponent - (rowExponent + order))) := by
          simp only [pow_add]
    _ = coefficient * t ^ columnExponent := by rw [Nat.add_sub_of_le h]

theorem transportedMonomialEntry_tendsto_zero
    {rowExponent columnExponent order : Nat}
    (h : columnExponent < rowExponent + order) (coefficient : Real) :
    Tendsto (transportedMonomialEntry rowExponent columnExponent order coefficient)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hPower := positivePower_tendsto_zero (Nat.sub_pos_of_lt h)
  simpa using (hPower.const_mul coefficient).congr' (by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (transportedMonomialEntry_eq_positivePower h.le ht.ne').symm)

theorem transportedMonomialEntry_tendsto_coefficient
    {rowExponent columnExponent order : Nat}
    (h : columnExponent = rowExponent + order) (coefficient : Real) :
    Tendsto (transportedMonomialEntry rowExponent columnExponent order coefficient)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds coefficient) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  simpa [h] using (transportedMonomialEntry_eq_positivePower
    (rowExponent := rowExponent) (columnExponent := columnExponent)
    (order := order) h.le ht.ne' (coefficient := coefficient)).symm

theorem transportedMonomialEntry_tendsto_atTop
    {rowExponent columnExponent order : Nat}
    (h : rowExponent + order < columnExponent) {coefficient : Real}
    (hCoefficient : 0 < coefficient) :
    Tendsto (transportedMonomialEntry rowExponent columnExponent order coefficient)
      (nhdsWithin 0 (Set.Ioi 0)) atTop := by
  have hInv : Tendsto
      (fun t : Real => (t ^ (columnExponent - (rowExponent + order)))⁻¹)
      (nhdsWithin 0 (Set.Ioi 0)) atTop :=
    tendsto_inv_nhdsGT_zero.comp
      (positivePower_tendsto_zeroWithin (Nat.sub_pos_of_lt h))
  apply (hInv.const_mul_atTop hCoefficient).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (transportedMonomialEntry_eq_inversePower h.le ht.ne').symm

end
end P0EFTJanusMultiExponentDiagonalSimilarity4D
end JanusFormal
