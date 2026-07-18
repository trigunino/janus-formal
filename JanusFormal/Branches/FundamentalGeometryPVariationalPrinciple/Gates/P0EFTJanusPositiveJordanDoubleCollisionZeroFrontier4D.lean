import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPositiveJordanCollisionZeroFrontier4D

/-!
# Two simultaneous positive Jordan collisions at zero

This gate treats the genuine two-parameter family `J₂(t) ⊕ J₂(s)` on the
positive quadrant.  Its blockwise Hermite root squares exactly.  The two
independent nilpotent modes are Sylvester eigenvectors with eigenvalues
`2 * sqrt t` and `2 * sqrt s`, both of which collapse as `(t,s) → (0,0)`.
Each nilpotent root coefficient diverges, so no finite matrix limit or
continuous extension exists at the corner.

This does not classify unequal block sizes, moving similarities, paths that
change Jordan type, or general matrix `0 / 0` collisions.
-/

namespace JanusFormal
namespace P0EFTJanusPositiveJordanDoubleCollisionZeroFrontier4D

set_option autoImplicit false

noncomputable section

open scoped Matrix.Norms.Frobenius RightActions Topology
open Filter
open P0EFTJanusMatrixSquareRootFrechetSylvester
open P0EFTJanusPositiveJordanCollisionZeroFrontier4D

abbrev Matrix4 :=
  P0EFTJanusPositiveJordanCollisionZeroFrontier4D.Matrix4

/-- The positive quadrant filter at its zero corner. -/
def positivePairZeroFilter : Filter (Real × Real) :=
  nhdsWithin (0, 0) (Set.Ioi 0 ×ˢ Set.Ioi 0)

local instance positivePairZeroFilter_neBot :
    positivePairZeroFilter.NeBot := by
  unfold positivePairZeroFilter
  rw [nhdsWithin_prod_eq]
  infer_instance

theorem positivePairZeroFilter_fst :
    Tendsto Prod.fst positivePairZeroFilter
      (nhdsWithin 0 (Set.Ioi 0)) := by
  unfold positivePairZeroFilter
  rw [nhdsWithin_prod_eq]
  exact tendsto_fst

theorem positivePairZeroFilter_snd :
    Tendsto Prod.snd positivePairZeroFilter
      (nhdsWithin 0 (Set.Ioi 0)) := by
  unfold positivePairZeroFilter
  rw [nhdsWithin_prod_eq]
  exact tendsto_snd

/-- `J₂(t) ⊕ J₂(s)`. -/
def doubleJordanCollisionTarget
    (first second : Real) : Matrix4 :=
  !![first, 1, 0, 0;
     0, first, 0, 0;
     0, 0, second, 1;
     0, 0, 0, second]

/-- The blockwise Hermite root on `t,s > 0`. -/
def doubleJordanCollisionRoot
    (first second : Real) : Matrix4 :=
  !![Real.sqrt first, (2 * Real.sqrt first)⁻¹, 0, 0;
     0, Real.sqrt first, 0, 0;
     0, 0, Real.sqrt second, (2 * Real.sqrt second)⁻¹;
     0, 0, 0, Real.sqrt second]

theorem doubleJordanCollisionRoot_square
    {first second : Real} (hFirst : 0 < first) (hSecond : 0 < second) :
    doubleJordanCollisionRoot first second *
        doubleJordanCollisionRoot first second =
      doubleJordanCollisionTarget first second := by
  have hSqrtFirst : Real.sqrt first ≠ 0 :=
    (Real.sqrt_pos.2 hFirst).ne'
  have hSqrtSecond : Real.sqrt second ≠ 0 :=
    (Real.sqrt_pos.2 hSecond).ne'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [doubleJordanCollisionRoot, doubleJordanCollisionTarget,
      Matrix.mul_apply, Fin.sum_univ_succ, hSqrtFirst, hSqrtSecond] <;>
    try { field_simp [hSqrtFirst, hSqrtSecond] <;> ring }
  all_goals first
    | simpa [pow_two] using Real.sq_sqrt hFirst.le
    | simpa [pow_two] using Real.sq_sqrt hSecond.le

@[simp]
theorem doubleJordanCollisionRoot_firstCoefficient
    (first second : Real) :
    doubleJordanCollisionRoot first second 0 1 =
      (2 * Real.sqrt first)⁻¹ := by
  rfl

@[simp]
theorem doubleJordanCollisionRoot_secondCoefficient
    (first second : Real) :
    doubleJordanCollisionRoot first second 2 3 =
      (2 * Real.sqrt second)⁻¹ := by
  rfl

theorem doubleJordanCollisionRoot_firstCoefficient_tendsto_atTop :
    Tendsto
      (fun parameter : Real × Real =>
        doubleJordanCollisionRoot parameter.1 parameter.2 0 1)
      positivePairZeroFilter atTop := by
  simpa [Function.comp_def] using
    jordanCollisionRoot_nilpotentCoefficient_tendsto_atTop.comp
      positivePairZeroFilter_fst

theorem doubleJordanCollisionRoot_secondCoefficient_tendsto_atTop :
    Tendsto
      (fun parameter : Real × Real =>
        doubleJordanCollisionRoot parameter.1 parameter.2 2 3)
      positivePairZeroFilter atTop := by
  have hDivergence :
      Tendsto (fun parameter : Real => (2 : Real)⁻¹ * Real.sqrt parameter⁻¹)
        (nhdsWithin 0 (Set.Ioi 0)) atTop :=
    (Real.tendsto_sqrt_atTop.comp tendsto_inv_nhdsGT_zero).const_mul_atTop
      (by norm_num)
  refine (hDivergence.comp positivePairZeroFilter_snd).congr' ?_
  filter_upwards with parameter
  simp [doubleJordanCollisionRoot, Real.sqrt_inv]
  ring

theorem doubleJordanCollisionTarget_tendsto_zeroCorner :
    Tendsto
      (fun parameter : Real × Real =>
        doubleJordanCollisionTarget parameter.1 parameter.2)
      positivePairZeroFilter
      (nhds (doubleJordanCollisionTarget 0 0)) := by
  have hContinuous : Continuous
      (fun parameter : Real × Real =>
        doubleJordanCollisionTarget parameter.1 parameter.2) := by
    unfold doubleJordanCollisionTarget
    fun_prop
  exact hContinuous.continuousAt.tendsto.mono_left inf_le_left

/-- The first nilpotent block mode. -/
def doubleJordanCollisionFirstMode : Matrix4 :=
  !![0, 1, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0]

/-- The second nilpotent block mode. -/
def doubleJordanCollisionSecondMode : Matrix4 :=
  !![0, 0, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 1;
     0, 0, 0, 0]

theorem doubleJordanCollisionModes_linearIndependent :
    LinearIndependent Real
      ![doubleJordanCollisionFirstMode, doubleJordanCollisionSecondMode] := by
  rw [LinearIndependent.pair_iff]
  intro firstCoefficient secondCoefficient hCombination
  have hFirst := congrArg
    (fun matrix : Matrix4 => matrix 0 1) hCombination
  have hSecond := congrArg
    (fun matrix : Matrix4 => matrix 2 3) hCombination
  constructor
  · simpa [doubleJordanCollisionFirstMode,
      doubleJordanCollisionSecondMode] using hFirst
  · simpa [doubleJordanCollisionFirstMode,
      doubleJordanCollisionSecondMode] using hSecond

theorem doubleJordanCollisionSylvester_firstMode
    (first second : Real) :
    sylvesterOperator (doubleJordanCollisionRoot first second)
        doubleJordanCollisionFirstMode =
      (2 * Real.sqrt first) • doubleJordanCollisionFirstMode := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sylvesterOperator_apply, doubleJordanCollisionRoot,
      doubleJordanCollisionFirstMode] <;> ring

theorem doubleJordanCollisionSylvester_secondMode
    (first second : Real) :
    sylvesterOperator (doubleJordanCollisionRoot first second)
        doubleJordanCollisionSecondMode =
      (2 * Real.sqrt second) • doubleJordanCollisionSecondMode := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sylvesterOperator_apply, doubleJordanCollisionRoot,
      doubleJordanCollisionSecondMode] <;> ring

theorem doubleJordanCollisionFirstEigenvalue_tendsto_zero :
    Tendsto (fun parameter : Real × Real => 2 * Real.sqrt parameter.1)
      positivePairZeroFilter (nhds 0) :=
  jordanCollisionSylvesterEigenvalue_tendsto_zero.comp
    positivePairZeroFilter_fst

theorem doubleJordanCollisionSecondEigenvalue_tendsto_zero :
    Tendsto (fun parameter : Real × Real => 2 * Real.sqrt parameter.2)
      positivePairZeroFilter (nhds 0) :=
  jordanCollisionSylvesterEigenvalue_tendsto_zero.comp
    positivePairZeroFilter_snd

theorem doubleJordanCollisionRoot_no_finite_limit (candidate : Matrix4) :
    ¬ Tendsto
        (fun parameter : Real × Real =>
          doubleJordanCollisionRoot parameter.1 parameter.2)
        positivePairZeroFilter (nhds candidate) := by
  intro hLimit
  have hEvaluation : Continuous (fun matrix : Matrix4 => matrix 0 1) := by
    fun_prop
  have hCoefficient :
      Tendsto
        (fun parameter : Real × Real =>
          doubleJordanCollisionRoot parameter.1 parameter.2 0 1)
        positivePairZeroFilter (nhds (candidate 0 1)) :=
    hEvaluation.continuousAt.tendsto.comp hLimit
  exact not_tendsto_atTop_of_tendsto_nhds hCoefficient
    doubleJordanCollisionRoot_firstCoefficient_tendsto_atTop

theorem doubleJordanCollisionRoot_no_continuous_extension :
    ¬ ∃ extension : (Real × Real) → Matrix4,
        ContinuousAt extension (0, 0) ∧
          ∀ first second, 0 < first → 0 < second →
            extension (first, second) =
              doubleJordanCollisionRoot first second := by
  rintro ⟨extension, hContinuous, hAgreement⟩
  have hRestricted :
      Tendsto extension positivePairZeroFilter
        (nhds (extension (0, 0))) :=
    hContinuous.mono_left inf_le_left
  have hEventually :
      extension =ᶠ[positivePairZeroFilter]
        (fun parameter =>
          doubleJordanCollisionRoot parameter.1 parameter.2) := by
    filter_upwards [self_mem_nhdsWithin] with parameter hParameter
    exact hAgreement parameter.1 parameter.2 hParameter.1 hParameter.2
  exact doubleJordanCollisionRoot_no_finite_limit (extension (0, 0))
    (hRestricted.congr' hEventually)

end

end P0EFTJanusPositiveJordanDoubleCollisionZeroFrontier4D
end JanusFormal
