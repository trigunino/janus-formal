import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPositiveJordanCollisionZeroFrontier4D

/-!
# Similarity-natural positive Jordan collision at zero

This gate transports the canonical `J₂(t) ⊕ 1 ⊕ 1` frontier through an
arbitrary fixed real similarity.  The transported Hermite root has an exact
square for `t > 0`, no finite continuation at `t = 0`, and a nonzero
transported Sylvester mode whose eigenvalue `2 * sqrt t` collapses to zero.

This closes the full fixed-similarity class of this one-block collision.  It
does not classify moving similarities, simultaneous collisions of several
Jordan blocks, changes of Jordan type, or arbitrary matrix `0 / 0` paths.
-/

namespace JanusFormal
namespace P0EFTJanusPositiveJordanCollisionSimilarityFrontier4D

set_option autoImplicit false

noncomputable section

open scoped Matrix.Norms.Frobenius RightActions Topology
open Filter
open P0EFTJanusMatrixSquareRootFrechetSylvester
open P0EFTJanusPositiveJordanCollisionZeroFrontier4D

abbrev Matrix4 :=
  P0EFTJanusPositiveJordanCollisionZeroFrontier4D.Matrix4

/-- A fixed real change of basis, recorded with an explicit two-sided inverse. -/
structure FixedSimilarity4 where
  change : Matrix4
  inverse : Matrix4
  inverse_mul_change : inverse * change = 1
  change_mul_inverse : change * inverse = 1

/-- Conjugation by the fixed change of basis. -/
def FixedSimilarity4.conjugate (data : FixedSimilarity4)
    (matrix : Matrix4) : Matrix4 :=
  data.change * matrix * data.inverse

/-- Conjugation by the inverse change of basis. -/
def FixedSimilarity4.inverseConjugate (data : FixedSimilarity4)
    (matrix : Matrix4) : Matrix4 :=
  data.inverse * matrix * data.change

theorem FixedSimilarity4.inverseConjugate_conjugate
    (data : FixedSimilarity4) (matrix : Matrix4) :
    data.inverseConjugate (data.conjugate matrix) = matrix := by
  calc
    data.inverse * (data.change * matrix * data.inverse) * data.change =
        (data.inverse * data.change) * matrix *
          (data.inverse * data.change) := by noncomm_ring
    _ = matrix := by rw [data.inverse_mul_change]; simp

theorem FixedSimilarity4.conjugate_inverseConjugate
    (data : FixedSimilarity4) (matrix : Matrix4) :
    data.conjugate (data.inverseConjugate matrix) = matrix := by
  calc
    data.change * (data.inverse * matrix * data.change) * data.inverse =
        (data.change * data.inverse) * matrix *
          (data.change * data.inverse) := by noncomm_ring
    _ = matrix := by rw [data.change_mul_inverse]; simp

theorem FixedSimilarity4.conjugate_injective (data : FixedSimilarity4) :
    Function.Injective data.conjugate := by
  intro first second hEqual
  have hRecovered := congrArg data.inverseConjugate hEqual
  simpa [data.inverseConjugate_conjugate] using hRecovered

theorem FixedSimilarity4.conjugate_mul
    (data : FixedSimilarity4) (first second : Matrix4) :
    data.conjugate (first * second) =
      data.conjugate first * data.conjugate second := by
  unfold FixedSimilarity4.conjugate
  calc
    data.change * (first * second) * data.inverse =
        data.change * first * (data.inverse * data.change) *
          second * data.inverse := by
      rw [data.inverse_mul_change]
      noncomm_ring
    _ = (data.change * first * data.inverse) *
          (data.change * second * data.inverse) := by noncomm_ring

theorem FixedSimilarity4.conjugate_add
    (data : FixedSimilarity4) (first second : Matrix4) :
    data.conjugate (first + second) =
      data.conjugate first + data.conjugate second := by
  unfold FixedSimilarity4.conjugate
  simp [Matrix.mul_add, Matrix.add_mul]

theorem FixedSimilarity4.conjugate_smul
    (data : FixedSimilarity4) (scalar : Real) (matrix : Matrix4) :
    data.conjugate (scalar • matrix) =
      scalar • data.conjugate matrix := by
  unfold FixedSimilarity4.conjugate
  simp [Matrix.mul_smul, Matrix.smul_mul]

theorem FixedSimilarity4.conjugate_continuous (data : FixedSimilarity4) :
    Continuous data.conjugate := by
  unfold FixedSimilarity4.conjugate
  fun_prop

theorem FixedSimilarity4.inverseConjugate_continuous
    (data : FixedSimilarity4) :
    Continuous data.inverseConjugate := by
  unfold FixedSimilarity4.inverseConjugate
  fun_prop

/-- The entire fixed-similarity class of the canonical collision path. -/
def similarJordanCollisionTarget
    (data : FixedSimilarity4) (parameter : Real) : Matrix4 :=
  data.conjugate (jordanCollisionTarget parameter)

/-- The similarity-transported Hermite root. -/
def similarJordanCollisionRoot
    (data : FixedSimilarity4) (parameter : Real) : Matrix4 :=
  data.conjugate (jordanCollisionRoot parameter)

/-- The transported nonzero nilpotent mode. -/
def similarJordanCollisionMode (data : FixedSimilarity4) : Matrix4 :=
  data.conjugate jordanCollisionMode

theorem similarJordanCollisionRoot_square
    (data : FixedSimilarity4) {parameter : Real}
    (hParameter : 0 < parameter) :
    similarJordanCollisionRoot data parameter *
        similarJordanCollisionRoot data parameter =
      similarJordanCollisionTarget data parameter := by
  unfold similarJordanCollisionRoot similarJordanCollisionTarget
  rw [← data.conjugate_mul]
  exact congrArg data.conjugate
    (jordanCollisionRoot_square hParameter)

theorem similarJordanCollisionTarget_tendsto_zeroFrontier
    (data : FixedSimilarity4) :
    Tendsto (similarJordanCollisionTarget data)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (similarJordanCollisionTarget data 0)) := by
  exact data.conjugate_continuous.continuousAt.tendsto.comp
    jordanCollisionTarget_tendsto_zeroFrontier

theorem similarJordanCollisionMode_ne_zero (data : FixedSimilarity4) :
    similarJordanCollisionMode data ≠ 0 := by
  intro hZero
  have hConjugated :
      data.conjugate jordanCollisionMode = data.conjugate 0 := by
    simpa [similarJordanCollisionMode, FixedSimilarity4.conjugate] using hZero
  have hCanonical : jordanCollisionMode = 0 :=
    data.conjugate_injective hConjugated
  have hEntry := congrArg (fun matrix : Matrix4 => matrix 0 1) hCanonical
  simpa [jordanCollisionMode] using hEntry

/-- Sylvester operators commute exactly with fixed similarity. -/
theorem sylvesterOperator_conjugate
    (data : FixedSimilarity4) (root variation : Matrix4) :
    sylvesterOperator (data.conjugate root) (data.conjugate variation) =
      data.conjugate (sylvesterOperator root variation) := by
  rw [sylvesterOperator_apply, sylvesterOperator_apply,
    ← data.conjugate_mul, ← data.conjugate_mul, data.conjugate_add]

theorem similarJordanCollisionSylvester_mode
    (data : FixedSimilarity4) (parameter : Real) :
    sylvesterOperator (similarJordanCollisionRoot data parameter)
        (similarJordanCollisionMode data) =
      (2 * Real.sqrt parameter) • similarJordanCollisionMode data := by
  rw [similarJordanCollisionRoot, similarJordanCollisionMode,
    sylvesterOperator_conjugate, jordanCollisionSylvester_mode,
    data.conjugate_smul]

theorem similarJordanCollisionSylvesterEigenvalue_tendsto_zero :
    Tendsto (fun parameter : Real => 2 * Real.sqrt parameter)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
  jordanCollisionSylvesterEigenvalue_tendsto_zero

/-- A finite limit of the transported branch would pull back to a forbidden
finite limit of the canonical Hermite branch. -/
theorem similarJordanCollisionRoot_no_finite_limit
    (data : FixedSimilarity4) (candidate : Matrix4) :
    ¬ Tendsto (similarJordanCollisionRoot data)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds candidate) := by
  intro hLimit
  have hPulledBack :
      Tendsto
        (fun parameter =>
          data.inverseConjugate
            (similarJordanCollisionRoot data parameter))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (data.inverseConjugate candidate)) :=
    data.inverseConjugate_continuous.continuousAt.tendsto.comp hLimit
  have hCanonical :
      Tendsto jordanCollisionRoot (nhdsWithin 0 (Set.Ioi 0))
        (nhds (data.inverseConjugate candidate)) := by
    simpa [similarJordanCollisionRoot,
      data.inverseConjugate_conjugate] using hPulledBack
  exact jordanCollisionRoot_no_finite_limit
    (data.inverseConjugate candidate) hCanonical

theorem similarJordanCollisionRoot_no_continuous_extension
    (data : FixedSimilarity4) :
    ¬ ∃ extension : Real → Matrix4,
        ContinuousAt extension 0 ∧
          ∀ parameter, 0 < parameter →
            extension parameter = similarJordanCollisionRoot data parameter := by
  rintro ⟨extension, hContinuous, hAgreement⟩
  have hRestricted :
      Tendsto extension (nhdsWithin 0 (Set.Ioi 0))
        (nhds (extension 0)) :=
    hContinuous.mono_left inf_le_left
  have hEventually :
      extension =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
        similarJordanCollisionRoot data := by
    filter_upwards [self_mem_nhdsWithin] with parameter hParameter
    exact hAgreement parameter hParameter
  exact similarJordanCollisionRoot_no_finite_limit data (extension 0)
    (hRestricted.congr' hEventually)

end

end P0EFTJanusPositiveJordanCollisionSimilarityFrontier4D
end JanusFormal
