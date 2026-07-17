import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusLorentzJordanIndexFourStratifiedRootGluing4D

/-!
# Positive single-eigenvalue Jordan roots in dimension four

This gate treats every pair `(lambda, A)` with `lambda > 0` and
`(A - lambda I)^4 = 0`.  After normalization by `lambda`, the complete
unipotent root gate applies.  Rescaling gives the exact real root

`sqrt(lambda) I + N/(2 sqrt(lambda)) - N^2/(8 sqrt(lambda)^3)
  + N^3/(16 sqrt(lambda)^5)`.

The selector is continuous jointly in `(lambda, A)`, similarity equivariant,
and Sylvester regular.  At `lambda = 1` it is exactly the complete unipotent
selector.  Multiple distinct eigenvalues and nonpositive eigenvalues are not
classified here.
-/

namespace JanusFormal
namespace P0EFTJanusPositiveSingleEigenvalueJordanRoot4D

set_option autoImplicit false

noncomputable section

open scoped Matrix.Norms.Frobenius RightActions Topology
open P0EFTJanusPositiveDiagonalizableRelativeRoot4D
open P0EFTJanusPositiveDiagonalizableRootGluing4D
open P0EFTJanusLorentzJordanIndexFourStratifiedRootGluing4D

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

def positiveEigenvalueLocus : Set Real := Set.Ioi 0

abbrev PositiveEigenvalue := positiveEigenvalueLocus

/-- Fourth displacement around an arbitrary scalar eigenvalue. -/
def scaledJordanDisplacementFourth
    (eigenvalue : Real) (target : Matrix4) : Matrix4 :=
  let nilpotent := target - eigenvalue • (1 : Matrix4)
  nilpotent * nilpotent * nilpotent * nilpotent

/-- Pairs carrying one strictly positive eigenvalue and an arbitrary Jordan
nilpotent of index at most four. -/
def positiveSingleEigenvalueJordanLocus :
    Set (PositiveEigenvalue × Matrix4) :=
  {data | scaledJordanDisplacementFourth data.1.1 data.2 = 0}

abbrev PositiveSingleEigenvalueJordanData :=
  positiveSingleEigenvalueJordanLocus

def selectedEigenvalue
    (data : PositiveSingleEigenvalueJordanData) : Real :=
  data.1.1.1

def selectedTarget
    (data : PositiveSingleEigenvalueJordanData) : Matrix4 :=
  data.1.2

def scaledJordanNilpotent
    (data : PositiveSingleEigenvalueJordanData) : Matrix4 :=
  selectedTarget data - selectedEigenvalue data • (1 : Matrix4)

def normalizedJordanNilpotent
    (data : PositiveSingleEigenvalueJordanData) : Matrix4 :=
  (selectedEigenvalue data)⁻¹ • scaledJordanNilpotent data

theorem selectedEigenvalue_pos
    (data : PositiveSingleEigenvalueJordanData) :
    0 < selectedEigenvalue data :=
  data.1.1.2

theorem selectedEigenvalue_ne_zero
    (data : PositiveSingleEigenvalueJordanData) :
    selectedEigenvalue data ≠ 0 :=
  ne_of_gt (selectedEigenvalue_pos data)

theorem scaledJordanNilpotent_fourth
    (data : PositiveSingleEigenvalueJordanData) :
    scaledJordanNilpotent data * scaledJordanNilpotent data *
        scaledJordanNilpotent data * scaledJordanNilpotent data = 0 :=
  data.property

theorem normalizedJordanNilpotent_fourth
    (data : PositiveSingleEigenvalueJordanData) :
    normalizedJordanNilpotent data * normalizedJordanNilpotent data *
        normalizedJordanNilpotent data * normalizedJordanNilpotent data = 0 := by
  let nilpotent := scaledJordanNilpotent data
  have hFourth : nilpotent * nilpotent * nilpotent * nilpotent = 0 :=
    scaledJordanNilpotent_fourth data
  unfold normalizedJordanNilpotent
  change
    ((selectedEigenvalue data)⁻¹ • nilpotent) *
          ((selectedEigenvalue data)⁻¹ • nilpotent) *
        ((selectedEigenvalue data)⁻¹ • nilpotent) *
      ((selectedEigenvalue data)⁻¹ • nilpotent) = 0
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hFourth,
    smul_zero]

def normalizedUnipotentTarget
    (data : PositiveSingleEigenvalueJordanData) :
    IndexFourUnipotentMatrix :=
  ⟨1 + normalizedJordanNilpotent data, by
    change jordanDisplacementFourth
      (1 + normalizedJordanNilpotent data) = 0
    have hDisplacement :
        (1 + normalizedJordanNilpotent data : Matrix4) - 1 =
          normalizedJordanNilpotent data := by abel
    rw [jordanDisplacementFourth, hDisplacement,
      normalizedJordanNilpotent_fourth data]⟩

@[simp]
theorem normalizedUnipotentTarget_sub_one
    (data : PositiveSingleEigenvalueJordanData) :
    (normalizedUnipotentTarget data).1 - 1 =
      normalizedJordanNilpotent data := by
  unfold normalizedUnipotentTarget
  change (1 + normalizedJordanNilpotent data : Matrix4) - 1 =
    normalizedJordanNilpotent data
  abel

theorem denormalize_normalizedTarget
    (data : PositiveSingleEigenvalueJordanData) :
    selectedEigenvalue data • (normalizedUnipotentTarget data).1 =
      selectedTarget data := by
  have hInverse : selectedEigenvalue data *
      (selectedEigenvalue data)⁻¹ = 1 :=
    mul_inv_cancel₀ (selectedEigenvalue_ne_zero data)
  unfold normalizedUnipotentTarget normalizedJordanNilpotent
    scaledJordanNilpotent
  rw [smul_add, smul_smul, hInverse, one_smul]
  module

/-- Rescaled positive binomial root on the complete single-eigenvalue
positive Jordan stratum. -/
def positiveSingleEigenvalueJordanRoot
    (data : PositiveSingleEigenvalueJordanData) : Matrix4 :=
  Real.sqrt (selectedEigenvalue data) •
    indexFourUnipotentRoot (normalizedUnipotentTarget data)

theorem positiveSingleEigenvalueJordanRoot_square
    (data : PositiveSingleEigenvalueJordanData) :
    positiveSingleEigenvalueJordanRoot data *
        positiveSingleEigenvalueJordanRoot data = selectedTarget data := by
  let root := indexFourUnipotentRoot (normalizedUnipotentTarget data)
  have hRootSquare : root * root = (normalizedUnipotentTarget data).1 :=
    indexFourUnipotentRoot_square (normalizedUnipotentTarget data)
  have hSqrt : Real.sqrt (selectedEigenvalue data) *
      Real.sqrt (selectedEigenvalue data) = selectedEigenvalue data :=
    Real.mul_self_sqrt (le_of_lt (selectedEigenvalue_pos data))
  unfold positiveSingleEigenvalueJordanRoot
  change
    (Real.sqrt (selectedEigenvalue data) • root) *
      (Real.sqrt (selectedEigenvalue data) • root) = selectedTarget data
  calc
    (Real.sqrt (selectedEigenvalue data) • root) *
        (Real.sqrt (selectedEigenvalue data) • root) =
      (Real.sqrt (selectedEigenvalue data) *
        Real.sqrt (selectedEigenvalue data)) • (root * root) := by
          rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    _ = selectedEigenvalue data •
        (normalizedUnipotentTarget data).1 := by rw [hSqrt, hRootSquare]
    _ = selectedTarget data := denormalize_normalizedTarget data

theorem scaledJordanDisplacementFourth_similarity
    (eigenvalue : Real) (target change inverse : Matrix4)
    (hInverseChange : inverse * change = 1)
    (hChangeInverse : change * inverse = 1) :
    scaledJordanDisplacementFourth eigenvalue
        (change * target * inverse) =
      change * scaledJordanDisplacementFourth eigenvalue target * inverse := by
  have hConjugatesOne :
      change * (1 : Matrix4) * inverse = 1 := by
    simpa using hChangeInverse
  have hDifference :
      change * target * inverse - eigenvalue • (1 : Matrix4) =
        change * (target - eigenvalue • (1 : Matrix4)) * inverse := by
    rw [mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      hConjugatesOne]
  unfold scaledJordanDisplacementFourth
  rw [hDifference]
  calc
    (change * (target - eigenvalue • (1 : Matrix4)) * inverse) *
            (change * (target - eigenvalue • (1 : Matrix4)) * inverse) *
          (change * (target - eigenvalue • (1 : Matrix4)) * inverse) *
        (change * (target - eigenvalue • (1 : Matrix4)) * inverse) =
      change * (target - eigenvalue • (1 : Matrix4)) *
        (inverse * change) * (target - eigenvalue • (1 : Matrix4)) *
        (inverse * change) * (target - eigenvalue • (1 : Matrix4)) *
        (inverse * change) * (target - eigenvalue • (1 : Matrix4)) *
        inverse := by noncomm_ring
    _ = change * scaledJordanDisplacementFourth eigenvalue target *
        inverse := by
      rw [hInverseChange]
      simp [scaledJordanDisplacementFourth, mul_assoc]

def conjugatePositiveSingleEigenvalueJordanData
    (data : PositiveSingleEigenvalueJordanData)
    (change inverse : Matrix4)
    (hInverseChange : inverse * change = 1)
    (hChangeInverse : change * inverse = 1) :
    PositiveSingleEigenvalueJordanData :=
  ⟨⟨data.1.1, change * selectedTarget data * inverse⟩, by
    change scaledJordanDisplacementFourth (selectedEigenvalue data)
      (change * selectedTarget data * inverse) = 0
    have hData : scaledJordanDisplacementFourth
        (selectedEigenvalue data) (selectedTarget data) = 0 :=
      data.property
    rw [scaledJordanDisplacementFourth_similarity
      (selectedEigenvalue data) (selectedTarget data) change inverse
      hInverseChange hChangeInverse, hData]
    simp⟩

@[simp]
theorem selectedEigenvalue_conjugate
    (data : PositiveSingleEigenvalueJordanData)
    (change inverse : Matrix4)
    (hInverseChange : inverse * change = 1)
    (hChangeInverse : change * inverse = 1) :
    selectedEigenvalue
        (conjugatePositiveSingleEigenvalueJordanData data change inverse
          hInverseChange hChangeInverse) =
      selectedEigenvalue data :=
  rfl

theorem normalizedJordanNilpotent_conjugate
    (data : PositiveSingleEigenvalueJordanData)
    (change inverse : Matrix4)
    (hInverseChange : inverse * change = 1)
    (hChangeInverse : change * inverse = 1) :
    normalizedJordanNilpotent
        (conjugatePositiveSingleEigenvalueJordanData data change inverse
          hInverseChange hChangeInverse) =
      change * normalizedJordanNilpotent data * inverse := by
  have hConjugatesOne :
      change * (1 : Matrix4) * inverse = 1 := by
    simpa using hChangeInverse
  have hDifference :
      change * selectedTarget data * inverse -
          selectedEigenvalue data • (1 : Matrix4) =
        change * scaledJordanNilpotent data * inverse := by
    unfold scaledJordanNilpotent
    rw [mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      hConjugatesOne]
  unfold normalizedJordanNilpotent
  change
    (selectedEigenvalue data)⁻¹ •
        (change * selectedTarget data * inverse -
          selectedEigenvalue data • (1 : Matrix4)) =
      change * ((selectedEigenvalue data)⁻¹ •
        scaledJordanNilpotent data) * inverse
  rw [hDifference, Matrix.mul_smul, Matrix.smul_mul]

theorem indexFourRootPolynomial_similarity
    (nilpotent change inverse : Matrix4)
    (hInverseChange : inverse * change = 1)
    (hChangeInverse : change * inverse = 1) :
    indexFourRootPolynomial (change * nilpotent * inverse) =
      change * indexFourRootPolynomial nilpotent * inverse := by
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
  unfold indexFourRootPolynomial
  rw [hCube, hSquare]
  noncomm_ring [hChangeInverse]

theorem positiveSingleEigenvalueJordanRoot_similarity
    (data : PositiveSingleEigenvalueJordanData)
    (change inverse : Matrix4)
    (hInverseChange : inverse * change = 1)
    (hChangeInverse : change * inverse = 1) :
    positiveSingleEigenvalueJordanRoot
        (conjugatePositiveSingleEigenvalueJordanData data change inverse
          hInverseChange hChangeInverse) =
      change * positiveSingleEigenvalueJordanRoot data * inverse := by
  unfold positiveSingleEigenvalueJordanRoot indexFourUnipotentRoot
  rw [selectedEigenvalue_conjugate,
    normalizedUnipotentTarget_sub_one,
    normalizedUnipotentTarget_sub_one,
    normalizedJordanNilpotent_conjugate data change inverse
      hInverseChange hChangeInverse,
    indexFourRootPolynomial_similarity
      (normalizedJordanNilpotent data) change inverse
      hInverseChange hChangeInverse]
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem selectedEigenvalue_continuous :
    Continuous selectedEigenvalue := by
  unfold selectedEigenvalue
  fun_prop

theorem selectedTarget_continuous :
    Continuous selectedTarget := by
  unfold selectedTarget
  fun_prop

theorem scaledJordanNilpotent_continuous :
    Continuous scaledJordanNilpotent := by
  unfold scaledJordanNilpotent
  exact selectedTarget_continuous.sub
    (selectedEigenvalue_continuous.smul continuous_const)

theorem selectedEigenvalue_inv_continuous :
    Continuous (fun data : PositiveSingleEigenvalueJordanData =>
      (selectedEigenvalue data)⁻¹) :=
  selectedEigenvalue_continuous.inv₀
    (fun data => selectedEigenvalue_ne_zero data)

theorem normalizedJordanNilpotent_continuous :
    Continuous normalizedJordanNilpotent := by
  unfold normalizedJordanNilpotent
  exact selectedEigenvalue_inv_continuous.smul
    scaledJordanNilpotent_continuous

theorem indexFourRootPolynomial_continuous :
    Continuous indexFourRootPolynomial := by
  unfold indexFourRootPolynomial
  fun_prop

theorem positiveSingleEigenvalueJordanRoot_continuous :
    Continuous positiveSingleEigenvalueJordanRoot := by
  have hRoot : positiveSingleEigenvalueJordanRoot =
      fun data => Real.sqrt (selectedEigenvalue data) •
        indexFourRootPolynomial (normalizedJordanNilpotent data) := by
    funext data
    unfold positiveSingleEigenvalueJordanRoot indexFourUnipotentRoot
    rw [normalizedUnipotentTarget_sub_one]
  rw [hRoot]
  exact (Real.continuous_sqrt.comp selectedEigenvalue_continuous).smul
    (indexFourRootPolynomial_continuous.comp
      normalizedJordanNilpotent_continuous)

/-- Sylvester operator at the rescaled root. -/
def positiveSingleEigenvalueSylvester
    (data : PositiveSingleEigenvalueJordanData) (variation : Matrix4) : Matrix4 :=
  positiveSingleEigenvalueJordanRoot data * variation +
    variation * positiveSingleEigenvalueJordanRoot data

def positiveSingleEigenvalueSylvesterInverse
    (data : PositiveSingleEigenvalueJordanData) (rhs : Matrix4) : Matrix4 :=
  (Real.sqrt (selectedEigenvalue data))⁻¹ •
    indexFourSylvesterInverse (normalizedUnipotentTarget data) rhs

theorem positiveSingleEigenvalueSylvester_inverse_apply
    (data : PositiveSingleEigenvalueJordanData) (rhs : Matrix4) :
    positiveSingleEigenvalueSylvester data
        (positiveSingleEigenvalueSylvesterInverse data rhs) = rhs := by
  let scale := Real.sqrt (selectedEigenvalue data)
  let normalizedRoot :=
    indexFourUnipotentRoot (normalizedUnipotentTarget data)
  let inverseValue :=
    indexFourSylvesterInverse (normalizedUnipotentTarget data) rhs
  have hScalePos : 0 < scale :=
    Real.sqrt_pos.2 (selectedEigenvalue_pos data)
  have hScaleInverse : scale * scale⁻¹ = 1 :=
    mul_inv_cancel₀ (ne_of_gt hScalePos)
  have hInverseScale : scale⁻¹ * scale = 1 :=
    inv_mul_cancel₀ (ne_of_gt hScalePos)
  have hNormalized :
      normalizedRoot * inverseValue + inverseValue * normalizedRoot = rhs :=
    indexFourSylvester_inverse_apply (normalizedUnipotentTarget data) rhs
  unfold positiveSingleEigenvalueSylvester
    positiveSingleEigenvalueSylvesterInverse
    positiveSingleEigenvalueJordanRoot
  change
    (scale • normalizedRoot) * (scale⁻¹ • inverseValue) +
      (scale⁻¹ • inverseValue) * (scale • normalizedRoot) = rhs
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, smul_smul, hScaleInverse,
    hInverseScale, one_smul]
  simpa using hNormalized

def positiveSingleEigenvalueSylvesterLinearMap
    (data : PositiveSingleEigenvalueJordanData) : Matrix4 →ₗ[Real] Matrix4 where
  toFun := positiveSingleEigenvalueSylvester data
  map_add' first second := by
    unfold positiveSingleEigenvalueSylvester
    noncomm_ring
  map_smul' scalar variation := by
    unfold positiveSingleEigenvalueSylvester
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_add]
    simp

theorem positiveSingleEigenvalueSylvester_surjective
    (data : PositiveSingleEigenvalueJordanData) :
    Function.Surjective (positiveSingleEigenvalueSylvester data) := by
  intro rhs
  exact ⟨positiveSingleEigenvalueSylvesterInverse data rhs,
    positiveSingleEigenvalueSylvester_inverse_apply data rhs⟩

theorem positiveSingleEigenvalueSylvester_injective
    (data : PositiveSingleEigenvalueJordanData) :
    Function.Injective (positiveSingleEigenvalueSylvester data) := by
  have hSurjective : Function.Surjective
      (positiveSingleEigenvalueSylvesterLinearMap data) :=
    positiveSingleEigenvalueSylvester_surjective data
  exact LinearMap.injective_iff_surjective.mpr hSurjective

theorem positiveSingleEigenvalueSylvesterInverse_apply
    (data : PositiveSingleEigenvalueJordanData) (variation : Matrix4) :
    positiveSingleEigenvalueSylvesterInverse data
        (positiveSingleEigenvalueSylvester data variation) = variation := by
  apply positiveSingleEigenvalueSylvester_injective data
  exact positiveSingleEigenvalueSylvester_inverse_apply data
    (positiveSingleEigenvalueSylvester data variation)

theorem positiveSingleEigenvalueSylvester_bijective
    (data : PositiveSingleEigenvalueJordanData) :
    Function.Bijective (positiveSingleEigenvalueSylvester data) :=
  ⟨positiveSingleEigenvalueSylvester_injective data,
    positiveSingleEigenvalueSylvester_surjective data⟩

def unitPositiveEigenvalue : PositiveEigenvalue :=
  ⟨1, by
    change 0 < (1 : Real)
    norm_num⟩

def unitEigenvalueJordanData
    (target : IndexFourUnipotentMatrix) :
    PositiveSingleEigenvalueJordanData :=
  ⟨⟨unitPositiveEigenvalue, target.1⟩, by
    change scaledJordanDisplacementFourth 1 target.1 = 0
    rw [scaledJordanDisplacementFourth, one_smul]
    exact target.property⟩

@[simp]
theorem positiveSingleEigenvalueJordanRoot_at_one
    (target : IndexFourUnipotentMatrix) :
    positiveSingleEigenvalueJordanRoot (unitEigenvalueJordanData target) =
      indexFourUnipotentRoot target := by
  unfold positiveSingleEigenvalueJordanRoot normalizedUnipotentTarget
    normalizedJordanNilpotent scaledJordanNilpotent selectedEigenvalue
    selectedTarget unitEigenvalueJordanData unitPositiveEigenvalue
  simp

theorem positiveSingleEigenvalueJordanRoot_at_one_eq_gluedSelector
    (target : IndexFourUnipotentMatrix) :
    positiveSingleEigenvalueJordanRoot (unitEigenvalueJordanData target) =
      positiveOrIndexFourRoot (indexFourTargetInGluedLocus target) := by
  rw [positiveSingleEigenvalueJordanRoot_at_one,
    positiveOrIndexFourRoot_on_indexFour]

/-- Exact target-level frontier of the single positive eigenvalue gate. -/
def positiveSingleEigenvalueJordanCovered (target : Matrix4) : Prop :=
  ∃ eigenvalue : Real, 0 < eigenvalue ∧
    scaledJordanDisplacementFourth eigenvalue target = 0

theorem not_positiveSingleEigenvalueJordanCovered_iff (target : Matrix4) :
    ¬ positiveSingleEigenvalueJordanCovered target ↔
      ∀ eigenvalue : Real, 0 < eigenvalue →
        scaledJordanDisplacementFourth eigenvalue target ≠ 0 := by
  simp [positiveSingleEigenvalueJordanCovered]

end

end P0EFTJanusPositiveSingleEigenvalueJordanRoot4D
end JanusFormal
