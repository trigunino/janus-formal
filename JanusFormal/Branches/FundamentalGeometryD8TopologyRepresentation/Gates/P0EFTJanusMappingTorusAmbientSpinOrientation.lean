import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Reflection
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusAmbientSpinProjection

/-!
# Orientation of the explicit ambient Spin projection

This gate relates the even Clifford grading used by Mathlib's `spinGroup` to
the determinant of the explicit action on the four ambient coordinates.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusAmbientSpinOrientation

set_option autoImplicit false

noncomputable section

open CliffordAlgebra
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusAmbientTangentQuadraticReduction
open P0EFTJanusMappingTorusAmbientSpinProjection

/-- A rank-one reflection has determinant `-1`. -/
private theorem linearEquiv_det_reflection
    {M : Type*} [AddCommGroup M] [Module Real M] [FiniteDimensional Real M]
    (vector : M) (functional : Module.Dual Real M)
    (hReflection : functional vector = 2) :
    LinearEquiv.det (Module.reflection hReflection) = (-1 : Realˣ) := by
  apply Units.ext
  rw [LinearEquiv.coe_det]
  let basis := Module.finBasis Real M
  rw [← LinearMap.det_toMatrix basis]
  have hMatrix :
      LinearMap.toMatrix basis basis (Module.reflection hReflection).toLinearMap =
        1 - Matrix.vecMulVec (basis.repr vector) (functional ∘ basis) := by
    ext row column
    by_cases hEqual : row = column <;>
      simp [LinearMap.toMatrix_apply, Module.reflection_apply, Matrix.vecMulVec_apply,
        hEqual, mul_comm]
  rw [hMatrix]
  have hDot :
      (functional ∘ basis) ⬝ᵥ basis.repr vector = functional vector := by
    rw [dotProduct]
    calc
      ∑ index, functional (basis index) * basis.repr vector index =
          ∑ index, basis.repr vector index * functional (basis index) := by
            congr 1
            funext index
            ring
      _ = ∑ index, functional ((basis.repr vector index) • basis index) := by simp
      _ = functional (∑ index, (basis.repr vector index) • basis index) := by rw [map_sum]
      _ = functional vector := by rw [basis.sum_repr]
  have hMatrixNeg :
      1 - Matrix.vecMulVec (basis.repr vector) (functional ∘ basis) =
        1 + Matrix.vecMulVec (-(basis.repr vector)) (functional ∘ basis) := by
    ext row column
    simp [Matrix.vecMulVec_apply, Function.comp_apply, sub_eq_add_neg, mul_comm]
  have hDotNeg :
      (functional ∘ basis) ⬝ᵥ (⇑(-(basis.repr vector))) =
        -((functional ∘ basis) ⬝ᵥ (basis.repr vector)) := by
    change (functional ∘ basis) ⬝ᵥ (fun index => -(basis.repr vector index)) = _
    exact dotProduct_neg (functional ∘ basis) (fun index => basis.repr vector index)
  rw [hMatrixNeg, Matrix.vecMulVec_eq Unit,
    Matrix.det_one_add_replicateCol_mul_replicateRow, hDotNeg, hDot, hReflection]
  norm_num

/-- Negation preserves orientation in the four-dimensional ambient model. -/
private theorem ambientLinearEquiv_neg_det :
    LinearEquiv.det (LinearEquiv.neg Real :
      CoverCoordinates ≃ₗ[Real] CoverCoordinates) = 1 := by
  apply Units.ext
  rw [LinearEquiv.coe_det]
  have hNeg :
      (LinearEquiv.neg Real : CoverCoordinates ≃ₗ[Real] CoverCoordinates).toLinearMap =
        (-1 : Real) • LinearMap.id := by
    apply LinearMap.ext
    intro tangent
    change -tangent = (-1 : Real) • tangent
    simp
  rw [hNeg, LinearMap.det_smul, LinearMap.det_id]
  norm_num [CoverCoordinates]

/-- The linear functional defining reflection in a Clifford generator. -/
private def ambientVectorReflectionFunctional
    (vector : CoverCoordinates)
    [Invertible (ambientCoverEuclideanQuadraticForm vector)] :
    Module.Dual Real CoverCoordinates :=
  ⅟(ambientCoverEuclideanQuadraticForm vector) •
    (ambientCoverEuclideanQuadraticForm.polarBilin vector)

@[simp] private theorem ambientVectorReflectionFunctional_self
    (vector : CoverCoordinates)
    [Invertible (ambientCoverEuclideanQuadraticForm vector)] :
    ambientVectorReflectionFunctional vector vector = 2 := by
  change ⅟(ambientCoverEuclideanQuadraticForm vector) *
      QuadraticMap.polar ambientCoverEuclideanQuadraticForm vector vector = 2
  rw [QuadraticMap.polar_self]
  rw [two_smul, mul_add, invOf_mul_self]
  norm_num

/-- Ordinary Clifford conjugation by one vector is the negative of its
rank-one reflection. -/
private def ambientVectorConjugation
    (vector : CoverCoordinates)
    [Invertible (ambientCoverEuclideanQuadraticForm vector)] :
    CoverCoordinates ≃ₗ[Real] CoverCoordinates :=
  (Module.reflection (ambientVectorReflectionFunctional_self vector)).trans
    (LinearEquiv.neg Real)

@[simp] private theorem ambientVectorConjugation_apply
    (vector tangent : CoverCoordinates)
    [Invertible (ambientCoverEuclideanQuadraticForm vector)] :
    ambientVectorConjugation vector tangent =
      (⅟(ambientCoverEuclideanQuadraticForm vector) *
          QuadraticMap.polar ambientCoverEuclideanQuadraticForm vector tangent) • vector - tangent := by
  simp [ambientVectorConjugation, Module.reflection_apply,
    ambientVectorReflectionFunctional]

private theorem ambientVectorConjugation_det
    (vector : CoverCoordinates)
    [Invertible (ambientCoverEuclideanQuadraticForm vector)] :
    LinearEquiv.det (ambientVectorConjugation vector) = (-1 : Realˣ) := by
  rw [ambientVectorConjugation, LinearEquiv.det_trans,
    ambientLinearEquiv_neg_det,
    linearEquiv_det_reflection vector (ambientVectorReflectionFunctional vector)]
  simp

/-- A homogeneous Lipschitz unit together with its induced vector action and
the determinant predicted by its Clifford grade. -/
private structure AmbientHomogeneousConjugationWitness
    (unit : AmbientCliffordAlgebraˣ) (grade : ZMod 2) (determinant : Realˣ) where
  action : CoverCoordinates ≃ₗ[Real] CoverCoordinates
  implements : ∀ tangent,
    CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm (action tangent) =
      (unit : AmbientCliffordAlgebra) *
        CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm tangent *
        (↑(unit⁻¹) : AmbientCliffordAlgebra)
  det_action : LinearEquiv.det action = determinant
  homogeneous :
    (unit : AmbientCliffordAlgebra) ∈
      CliffordAlgebra.evenOdd ambientCoverEuclideanQuadraticForm grade

private def AmbientLipschitzOrientationWitness
    (unit : AmbientCliffordAlgebraˣ) : Prop :=
  Nonempty (AmbientHomogeneousConjugationWitness unit 0 1) ∨
    Nonempty (AmbientHomogeneousConjugationWitness unit 1 (-1))

private def AmbientHomogeneousConjugationWitness.mul
    {first second : AmbientCliffordAlgebraˣ}
    {firstGrade secondGrade : ZMod 2}
    {firstDet secondDet : Realˣ}
    (firstWitness :
      AmbientHomogeneousConjugationWitness first firstGrade firstDet)
    (secondWitness :
      AmbientHomogeneousConjugationWitness second secondGrade secondDet) :
    AmbientHomogeneousConjugationWitness (first * second)
      (firstGrade + secondGrade) (firstDet * secondDet) where
  action := secondWitness.action.trans firstWitness.action
  implements tangent := by
    calc
      CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm
          (firstWitness.action (secondWitness.action tangent)) =
          (first : AmbientCliffordAlgebra) *
            CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm
              (secondWitness.action tangent) *
            (↑(first⁻¹) : AmbientCliffordAlgebra) :=
        firstWitness.implements (secondWitness.action tangent)
      _ = (first : AmbientCliffordAlgebra) *
            ((second : AmbientCliffordAlgebra) *
              CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm tangent *
              (↑(second⁻¹) : AmbientCliffordAlgebra)) *
            (↑(first⁻¹) : AmbientCliffordAlgebra) := by
        rw [secondWitness.implements]
      _ = (↑(first * second) : AmbientCliffordAlgebra) *
            CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm tangent *
            (↑((first * second)⁻¹) : AmbientCliffordAlgebra) := by
        simp only [Units.val_mul, mul_inv_rev]
        noncomm_ring
  det_action := by
    rw [LinearEquiv.det_trans, firstWitness.det_action, secondWitness.det_action]
  homogeneous :=
    SetLike.mul_mem_graded firstWitness.homogeneous secondWitness.homogeneous

private theorem ambientLipschitzOrientationWitness_mul
    {first second : AmbientCliffordAlgebraˣ}
    (hFirst : AmbientLipschitzOrientationWitness first)
    (hSecond : AmbientLipschitzOrientationWitness second) :
    AmbientLipschitzOrientationWitness (first * second) := by
  rcases hFirst with hFirst | hFirst
  · obtain ⟨hFirst⟩ := hFirst
    rcases hSecond with hSecond | hSecond
    · obtain ⟨hSecond⟩ := hSecond
      left
      exact ⟨by simpa using hFirst.mul hSecond⟩
    · obtain ⟨hSecond⟩ := hSecond
      right
      exact ⟨by simpa using hFirst.mul hSecond⟩
  · obtain ⟨hFirst⟩ := hFirst
    rcases hSecond with hSecond | hSecond
    · obtain ⟨hSecond⟩ := hSecond
      right
      exact ⟨by simpa using hFirst.mul hSecond⟩
    · obtain ⟨hSecond⟩ := hSecond
      left
      have hGrade : (1 + 1 : ZMod 2) = 0 := by decide
      exact ⟨by simpa [hGrade] using hFirst.mul hSecond⟩

private theorem ambientLipschitzOrientationWitness_generator
    (unit : AmbientCliffordAlgebraˣ)
    (hUnit : unit ∈ ((↑) ⁻¹' Set.range
      (CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm) :
        Set AmbientCliffordAlgebraˣ)) :
    AmbientLipschitzOrientationWitness unit := by
  obtain ⟨vector, hVector⟩ := hUnit
  letI := unit.invertible
  letI : Invertible
      (CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm vector) := by
    rwa [hVector]
  letI : Invertible (ambientCoverEuclideanQuadraticForm vector) :=
    invertibleOfInvertibleι ambientCoverEuclideanQuadraticForm vector
  right
  refine ⟨{
    action := ambientVectorConjugation vector
    implements := ?_
    det_action := ambientVectorConjugation_det vector
    homogeneous := ?_ }⟩
  · intro tangent
    simp_rw [ambientVectorConjugation_apply, ← invOf_units unit, ← hVector,
      CliffordAlgebra.ι_mul_ι_mul_invOf_ι]
  · rw [← hVector]
    exact CliffordAlgebra.ι_mem_evenOdd_one ambientCoverEuclideanQuadraticForm vector

private theorem ambientLipschitzOrientationWitness_generator_inv
    (unit : AmbientCliffordAlgebraˣ)
    (hUnit : unit ∈ ((↑) ⁻¹' Set.range
      (CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm) :
        Set AmbientCliffordAlgebraˣ)) :
    AmbientLipschitzOrientationWitness unit⁻¹ := by
  obtain ⟨vector, hVector⟩ := hUnit
  letI := unit.invertible
  letI : Invertible
      (CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm vector) := by
    rwa [hVector]
  letI : Invertible (ambientCoverEuclideanQuadraticForm vector) :=
    invertibleOfInvertibleι ambientCoverEuclideanQuadraticForm vector
  right
  refine ⟨{
    action := ambientVectorConjugation vector
    implements := ?_
    det_action := ambientVectorConjugation_det vector
    homogeneous := ?_ }⟩
  · intro tangent
    simp only [inv_inv]
    simp_rw [ambientVectorConjugation_apply, ← invOf_units unit, ← hVector,
      CliffordAlgebra.invOf_ι_mul_ι_mul_ι]
  · simp_rw [← invOf_units unit, ← hVector, CliffordAlgebra.invOf_ι]
    exact CliffordAlgebra.ι_mem_evenOdd_one ambientCoverEuclideanQuadraticForm
      (⅟(ambientCoverEuclideanQuadraticForm vector) • vector)

private theorem ambientLipschitzOrientationWitness_one :
    AmbientLipschitzOrientationWitness (1 : AmbientCliffordAlgebraˣ) := by
  left
  refine ⟨{
    action := LinearEquiv.refl Real CoverCoordinates
    implements := ?_
    det_action := LinearEquiv.det_refl
    homogeneous := ?_ }⟩
  · intro tangent
    simp
  · exact Submodule.one_le.mp
      (CliffordAlgebra.one_le_evenOdd_zero ambientCoverEuclideanQuadraticForm)

/-- Every unit in Mathlib's Lipschitz group is homogeneous, and its ordinary
vector action has determinant `+1` in even grade and `-1` in odd grade. -/
private theorem ambientLipschitzOrientationWitness_of_mem
    (unit : AmbientCliffordAlgebraˣ)
    (hUnit : unit ∈ lipschitzGroup ambientCoverEuclideanQuadraticForm) :
    AmbientLipschitzOrientationWitness unit := by
  unfold lipschitzGroup at hUnit
  induction hUnit using Subgroup.closure_induction'' with
  | mem element hElement =>
      exact ambientLipschitzOrientationWitness_generator element hElement
  | inv_mem element hElement =>
      exact ambientLipschitzOrientationWitness_generator_inv element hElement
  | one => exact ambientLipschitzOrientationWitness_one
  | mul first second _ _ hFirst hSecond =>
      exact ambientLipschitzOrientationWitness_mul hFirst hSecond

/-- The explicit Clifford-conjugation projection of every ambient Spin
element is orientation preserving. -/
theorem ambientSpinProjection_det
    (lift : AmbientCoordinateSpinGroup) :
    LinearEquiv.det (ambientSpinProjection lift) = (1 : Realˣ) := by
  let unit := spinGroup.toUnits lift
  have hLipschitz : unit ∈ lipschitzGroup ambientCoverEuclideanQuadraticForm :=
    spinGroup.units_mem_lipschitzGroup lift.property
  rcases ambientLipschitzOrientationWitness_of_mem unit hLipschitz with
    hEvenWitness | hOddWitness
  · obtain ⟨evenWitness⟩ := hEvenWitness
    have hAction : evenWitness.action = ambientSpinProjection lift := by
      apply LinearEquiv.ext
      intro tangent
      apply ambientCliffordIota_injective
      rw [evenWitness.implements]
      exact (ambientSpinVectorAction_spec lift tangent).symm
    rw [← hAction]
    exact evenWitness.det_action
  · obtain ⟨oddWitness⟩ := hOddWitness
    exfalso
    have hEven : (lift : AmbientCliffordAlgebra) ∈
        CliffordAlgebra.evenOdd ambientCoverEuclideanQuadraticForm 0 := by
      simpa [CliffordAlgebra.even] using spinGroup.mem_even lift.property
    have hOdd : (lift : AmbientCliffordAlgebra) ∈
        CliffordAlgebra.evenOdd ambientCoverEuclideanQuadraticForm 1 :=
      oddWitness.homogeneous
    have hZero : (lift : AmbientCliffordAlgebra) = 0 := by
      have hBottom : (lift : AmbientCliffordAlgebra) ∈
          (⊥ : Submodule Real AmbientCliffordAlgebra) :=
        (CliffordAlgebra.evenOdd_isCompl ambientCoverEuclideanQuadraticForm).disjoint.le_bot
          ⟨hEven, hOdd⟩
      simpa using hBottom
    exact unit.ne_zero hZero

end

end P0EFTJanusMappingTorusAmbientSpinOrientation
end JanusFormal
