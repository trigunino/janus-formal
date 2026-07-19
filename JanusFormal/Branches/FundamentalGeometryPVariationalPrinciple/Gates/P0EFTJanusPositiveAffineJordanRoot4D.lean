import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPositiveJordanCollisionZeroFrontier4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGlobalDiagonalPowerLawZeroOverZeroClassification4D

/-! # The positive affine root of one real Jordan block -/

namespace JanusFormal
namespace P0EFTJanusPositiveAffineJordanRoot4D

set_option autoImplicit false
noncomputable section

open Filter
open scoped Topology
open P0EFTJanusPositiveJordanCollisionZeroFrontier4D
open P0EFTJanusGlobalDiagonalPowerLawZeroOverZeroClassification4D

abbrev Matrix4 := P0EFTJanusPositiveJordanCollisionZeroFrontier4D.Matrix4

/-- The square-zero matrix unit in the canonical size-two Jordan block. -/
abbrev jordanNilpotent : Matrix4 := jordanCollisionMode

theorem jordanNilpotent_square : jordanNilpotent * jordanNilpotent = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jordanNilpotent, jordanCollisionMode, Matrix.mul_apply,
      Fin.sum_univ_succ]

/-- `sqrt λ I + (2 sqrt λ)⁻¹ N`, with two spectator identity blocks. -/
abbrev positiveAffineJordanRoot (lambda : Real) : Matrix4 :=
  jordanCollisionRoot lambda

theorem positiveAffineJordanRoot_square
    {lambda : Real} (hLambda : 0 < lambda) :
    positiveAffineJordanRoot lambda * positiveAffineJordanRoot lambda =
      jordanCollisionTarget lambda :=
  jordanCollisionRoot_square hLambda

/-- Uniqueness among affine expressions `a I + b N` on the Jordan block,
with the spectator blocks fixed to the principal value one. -/
theorem positiveAffineJordanRoot_coefficients_unique
    {lambda a b : Real} (hLambda : 0 < lambda) (hA : 0 < a)
    (hSquare :
      (!![a, b, 0, 0; 0, a, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] : Matrix4) *
        !![a, b, 0, 0; 0, a, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] =
          jordanCollisionTarget lambda) :
    a = Real.sqrt lambda ∧ b = (2 * Real.sqrt lambda)⁻¹ := by
  have hDiagonal := congrArg (fun matrix : Matrix4 => matrix 0 0) hSquare
  have hOffDiagonal := congrArg (fun matrix : Matrix4 => matrix 0 1) hSquare
  simp [jordanCollisionTarget, Matrix.mul_apply, Fin.sum_univ_succ] at hDiagonal hOffDiagonal
  have hSqrt : Real.sqrt lambda ≠ 0 := (Real.sqrt_pos.2 hLambda).ne'
  have hAEq : a = Real.sqrt lambda := by
    nlinarith [Real.sq_sqrt hLambda.le, Real.sqrt_nonneg lambda]
  subst a
  constructor
  · rfl
  · field_simp [hSqrt]
    linarith

/-- With fixed nonzero `N`, the nilpotent root coefficient diverges. -/
theorem fixedNilpotentCoefficient_tendsto_atTop :
    Tendsto (fun lambda : Real => positiveAffineJordanRoot lambda 0 1)
      (nhdsWithin 0 (Set.Ioi 0)) atTop :=
  jordanCollisionRoot_nilpotentCoefficient_tendsto_atTop

/-- Consequently the fixed-block root has no finite zero-frontier limit. -/
theorem fixedNilpotentRoot_no_finite_limit (candidate : Matrix4) :
    ¬ Tendsto positiveAffineJordanRoot (nhdsWithin 0 (Set.Ioi 0))
      (nhds candidate) :=
  jordanCollisionRoot_no_finite_limit candidate

/-- Root along `lambda=t^(2m)`, `N=t^n N₀`. -/
def monomialJordanRoot (m n : Nat) (t : Real) : Matrix4 :=
  !![t ^ m, t ^ n / (2 * t ^ m), 0, 0;
     0, t ^ m, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, 1]

def collapsedJordanLimit : Matrix4 :=
  !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

def criticalJordanLimit : Matrix4 :=
  !![0, 1 / 2, 0, 0; 0, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

theorem monomialJordanCoefficient_eq_pow_sub
    {m n : Nat} (hmn : m ≤ n) {t : Real} (ht : 0 < t) :
    monomialJordanRoot m n t 0 1 = (1 / 2 : Real) * t ^ (n - m) := by
  change t ^ n / (2 * t ^ m) = _
  rw [pow_sub₀ t ht.ne' hmn]
  field_simp [ht.ne']

theorem monomialJordanCoefficient_vanishing
    {m n : Nat} (hmn : m < n) :
    Tendsto (fun t : Real => monomialJordanRoot m n t 0 1)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hPow := positivePower_tendsto_zero (Nat.sub_pos_of_lt hmn)
  simpa using (hPow.const_mul (1 / 2 : Real)).congr' (by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (monomialJordanCoefficient_eq_pow_sub hmn.le ht).symm)

theorem monomialJordanCoefficient_critical (m : Nat) :
    Tendsto (fun t : Real => monomialJordanRoot m m t 0 1)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / 2)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 < t at ht
  simpa using (monomialJordanCoefficient_eq_pow_sub (m := m) (n := m) le_rfl ht).symm

theorem monomialJordanCoefficient_diverging
    {m n : Nat} (hnm : n < m) :
    Tendsto (fun t : Real => monomialJordanRoot m n t 0 1)
      (nhdsWithin 0 (Set.Ioi 0)) atTop := by
  have hInv : Tendsto (fun t : Real => (t ^ (m - n))⁻¹)
      (nhdsWithin 0 (Set.Ioi 0)) atTop :=
    tendsto_inv_nhdsGT_zero.comp
      (positivePower_tendsto_zeroWithin (Nat.sub_pos_of_lt hnm))
  apply (hInv.const_mul_atTop (by norm_num : 0 < (1 / 2 : Real))).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 < t at ht
  change (1 / 2 : Real) * (t ^ (m - n))⁻¹ = t ^ n / (2 * t ^ m)
  have hp : t ^ m = t ^ (m - n) * t ^ n := by
    rw [← pow_add, Nat.sub_add_cancel hnm.le]
  rw [hp]
  field_simp [pow_ne_zero _ ht.ne']

private theorem monomialDiagonal_tendsto_zero {m : Nat} (hm : 0 < m) :
    Tendsto (fun t : Real => t ^ m) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
  positivePower_tendsto_zero hm

theorem monomialJordanRoot_vanishing_limit
    {m n : Nat} (hm : 0 < m) (hmn : m < n) :
    Tendsto (monomialJordanRoot m n) (nhdsWithin 0 (Set.Ioi 0))
      (nhds collapsedJordanLimit) := by
  have hDiag := monomialDiagonal_tendsto_zero hm
  have hOff := monomialJordanCoefficient_vanishing hmn
  change Tendsto (fun t : Real =>
      (!![t ^ m, monomialJordanRoot m n t 0 1, 0, 0;
         0, t ^ m, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] : Matrix4))
    (nhdsWithin 0 (Set.Ioi 0)) (nhds collapsedJordanLimit)
  have hContinuous : Continuous (fun pair : Real × Real =>
      (!![pair.1, pair.2, 0, 0; 0, pair.1, 0, 0;
         0, 0, 1, 0; 0, 0, 0, 1] : Matrix4)) := by
    apply continuous_matrix
    intro i j
    fin_cases i <;> fin_cases j <;> fun_prop
  convert hContinuous.continuousAt.tendsto.comp (hDiag.prodMk_nhds hOff) using 1 <;> rfl

theorem monomialJordanRoot_critical_limit
    {m : Nat} (hm : 0 < m) :
    Tendsto (monomialJordanRoot m m) (nhdsWithin 0 (Set.Ioi 0))
      (nhds criticalJordanLimit) := by
  have hDiag := monomialDiagonal_tendsto_zero hm
  have hOff := monomialJordanCoefficient_critical m
  change Tendsto (fun t : Real =>
      (!![t ^ m, monomialJordanRoot m m t 0 1, 0, 0;
         0, t ^ m, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] : Matrix4))
    (nhdsWithin 0 (Set.Ioi 0)) (nhds criticalJordanLimit)
  have hContinuous : Continuous (fun pair : Real × Real =>
      (!![pair.1, pair.2, 0, 0; 0, pair.1, 0, 0;
         0, 0, 1, 0; 0, 0, 0, 1] : Matrix4)) := by
    apply continuous_matrix
    intro i j
    fin_cases i <;> fin_cases j <;> fun_prop
  convert hContinuous.continuousAt.tendsto.comp (hDiag.prodMk_nhds hOff) using 1 <;> rfl

/-- Affine Jordan root for arbitrary scalar eigenvalue and nilpotent amplitude. -/
def arbitraryAmplitudeJordanRoot (lambda mu : Real → Real) (t : Real) : Matrix4 :=
  !![Real.sqrt (lambda t), mu t / (2 * Real.sqrt (lambda t)), 0, 0;
     0, Real.sqrt (lambda t), 0, 0;
     0, 0, 1, 0;
     0, 0, 0, 1]

def jordanRatio (lambda mu : Real → Real) (t : Real) : Real :=
  mu t / (2 * Real.sqrt (lambda t))

def arbitraryJordanLimit (coefficient : Real) : Matrix4 :=
  !![0, coefficient, 0, 0; 0, 0, 0, 0;
     0, 0, 1, 0; 0, 0, 0, 1]

private theorem arbitraryJordanAssembly_continuous :
    Continuous (fun pair : Real × Real =>
      (!![pair.1, pair.2, 0, 0; 0, pair.1, 0, 0;
         0, 0, 1, 0; 0, 0, 0, 1] : Matrix4)) := by
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;> fun_prop

theorem arbitraryAmplitudeJordanRoot_tendsto_of_ratio
    {alpha : Type*} {l : Filter alpha} (lambda mu : alpha → Real)
    (hLambda : Tendsto lambda l (nhds 0)) {coefficient : Real}
    (hRatio : Tendsto (fun t => mu t / (2 * Real.sqrt (lambda t))) l
      (nhds coefficient)) :
    Tendsto (fun t =>
      (!![Real.sqrt (lambda t), mu t / (2 * Real.sqrt (lambda t)), 0, 0;
         0, Real.sqrt (lambda t), 0, 0;
         0, 0, 1, 0; 0, 0, 0, 1] : Matrix4)) l
      (nhds (arbitraryJordanLimit coefficient)) := by
  have hSqrt : Tendsto (fun t => Real.sqrt (lambda t)) l (nhds 0) := by
    convert Real.continuous_sqrt.continuousAt.tendsto.comp hLambda using 1
    · rfl
    · simp
  convert arbitraryJordanAssembly_continuous.continuousAt.tendsto.comp
    (hSqrt.prodMk_nhds hRatio) using 1 <;> rfl

/-- Complete finite-limit classification: the matrix limit is exactly
equivalent to the limit of its nilpotent coefficient ratio. -/
theorem arbitraryAmplitudeJordanRoot_tendsto_iff_ratio
    {alpha : Type*} {l : Filter alpha} (lambda mu : alpha → Real)
    (hLambda : Tendsto lambda l (nhds 0)) (coefficient : Real) :
    Tendsto (fun t =>
      (!![Real.sqrt (lambda t), mu t / (2 * Real.sqrt (lambda t)), 0, 0;
         0, Real.sqrt (lambda t), 0, 0;
         0, 0, 1, 0; 0, 0, 0, 1] : Matrix4)) l
        (nhds (arbitraryJordanLimit coefficient)) ↔
      Tendsto (fun t => mu t / (2 * Real.sqrt (lambda t))) l
        (nhds coefficient) := by
  constructor
  · intro hMatrix
    have hEntry := (continuous_id.matrix_elem (0 : Fin 4) (1 : Fin 4)).tendsto
      (arbitraryJordanLimit coefficient)
    convert hEntry.comp hMatrix using 1 <;> rfl
  · exact arbitraryAmplitudeJordanRoot_tendsto_of_ratio lambda mu hLambda

theorem arbitraryAmplitudeJordanRoot_no_finite_limit_of_ratio_atTop
    {alpha : Type*} {l : Filter alpha} [l.NeBot] (lambda mu : alpha → Real)
    (hRatio : Tendsto (fun t => mu t / (2 * Real.sqrt (lambda t))) l atTop)
    (candidate : Matrix4) :
    ¬ Tendsto (fun t =>
      (!![Real.sqrt (lambda t), mu t / (2 * Real.sqrt (lambda t)), 0, 0;
         0, Real.sqrt (lambda t), 0, 0;
         0, 0, 1, 0; 0, 0, 0, 1] : Matrix4)) l (nhds candidate) := by
  intro hMatrix
  have hEntry := (continuous_id.matrix_elem (0 : Fin 4) (1 : Fin 4)).tendsto candidate
  have hFinite : Tendsto (fun t => mu t / (2 * Real.sqrt (lambda t))) l
      (nhds (candidate 0 1)) := by
    convert hEntry.comp hMatrix using 1 <;> rfl
  exact not_tendsto_atTop_of_tendsto_nhds hFinite hRatio

end
end P0EFTJanusPositiveAffineJordanRoot4D
end JanusFormal
