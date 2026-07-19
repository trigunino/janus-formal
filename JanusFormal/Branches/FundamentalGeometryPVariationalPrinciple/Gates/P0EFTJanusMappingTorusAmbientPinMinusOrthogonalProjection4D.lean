import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAmbientPinMinusProjectionContinuity4D

/-!
# Orthogonal target of the ambient Pin-minus projection

The existing twisted Clifford action was previously bundled only as a map to
`GL(4)`.  This gate proves the missing parity fact for every element of
Mathlib's Lipschitz-generated Pin group, and uses it to prove that the twisted
action preserves the negative Clifford form, hence the positive Euclidean
form.  The resulting projection is therefore a genuine continuous surjective
group morphism `Pin⁻(4) → O(4)`.

No local section, covering-map statement, or Čech lift is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusAmbientPinMinusOrthogonalProjection4D

set_option autoImplicit false

noncomputable section

open CliffordAlgebra
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusAmbientTangentQuadraticReduction
open P0EFTJanusMappingTorusAmbientPinMinusProjection4D
open P0EFTJanusMappingTorusAmbientPinMinusPointwiseTangentLift4D
open P0EFTJanusMappingTorusAmbientPinMinusProjectionContinuity4D

private theorem ambientPinMinusLipschitz_involute_parity
    (unit : AmbientPinMinusCliffordAlgebraˣ)
    (hUnit : unit ∈ lipschitzGroup ambientCoverPinMinusQuadraticForm) :
    involute (unit : AmbientPinMinusCliffordAlgebra) = unit ∨
      involute (unit : AmbientPinMinusCliffordAlgebra) = -unit := by
  unfold lipschitzGroup at hUnit
  induction hUnit using Subgroup.closure_induction'' with
  | mem unit hGenerator =>
      obtain ⟨vector, hVector⟩ := hGenerator
      right
      rw [← hVector, CliffordAlgebra.involute_ι]
  | inv_mem unit hGenerator =>
      obtain ⟨vector, hVector⟩ := hGenerator
      right
      letI := unit.invertible
      letI : Invertible
          (CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm vector) := by
        rwa [hVector]
      letI := invertibleNeg
        (CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm vector)
      letI := Invertible.map involute
        (CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm vector)
      simp_rw [← invOf_units unit, ← hVector, map_invOf,
        CliffordAlgebra.involute_ι, invOf_neg]
  | one =>
      left
      simp
  | mul first second _ _ hFirst hSecond =>
      rcases hFirst with hFirst | hFirst <;>
        rcases hSecond with hSecond | hSecond
      · left
        simpa only [Units.val_mul, map_mul, hFirst, hSecond]
      · right
        simpa only [Units.val_mul, map_mul, hFirst, hSecond, mul_neg]
      · right
        simpa only [Units.val_mul, map_mul, hFirst, hSecond, neg_mul]
      · left
        simpa only [Units.val_mul, map_mul, hFirst, hSecond, neg_mul,
          mul_neg, neg_neg]

/-- Every element of the actual ambient Pin-minus group is homogeneous for
the Clifford grade involution. -/
theorem ambientPinMinus_involute_parity
    (lift : AmbientCoordinatePinMinusGroup) :
    involute (lift : AmbientPinMinusCliffordAlgebra) = lift ∨
      involute (lift : AmbientPinMinusCliffordAlgebra) = -lift := by
  let unit := pinGroup.toUnits lift
  have hUnit : unit ∈ lipschitzGroup ambientCoverPinMinusQuadraticForm :=
    pinGroup.units_mem_lipschitzGroup lift.property
  change involute (unit : AmbientPinMinusCliffordAlgebra) = unit ∨
    involute (unit : AmbientPinMinusCliffordAlgebra) = -unit
  exact ambientPinMinusLipschitz_involute_parity unit hUnit

private theorem ambientPinMinus_twistedConjugation_square
    (lift : AmbientCoordinatePinMinusGroup)
    (value : AmbientPinMinusCliffordAlgebra) :
    (involute (lift : AmbientPinMinusCliffordAlgebra) * value *
        (↑(lift⁻¹) : AmbientPinMinusCliffordAlgebra)) *
      (involute (lift : AmbientPinMinusCliffordAlgebra) * value *
        (↑(lift⁻¹) : AmbientPinMinusCliffordAlgebra)) =
      (lift : AmbientPinMinusCliffordAlgebra) * (value * value) *
        (↑(lift⁻¹) : AmbientPinMinusCliffordAlgebra) := by
  have hInvMul :
      (↑(lift⁻¹) : AmbientPinMinusCliffordAlgebra) *
          (lift : AmbientPinMinusCliffordAlgebra) = 1 := by
    change star (lift : AmbientPinMinusCliffordAlgebra) *
      (lift : AmbientPinMinusCliffordAlgebra) = 1
    exact pinGroup.coe_star_mul_self lift
  rcases ambientPinMinus_involute_parity lift with hEven | hOdd
  · rw [hEven]
    calc
      _ = (lift : AmbientPinMinusCliffordAlgebra) * value *
          ((↑(lift⁻¹) : AmbientPinMinusCliffordAlgebra) * lift) * value *
          (↑(lift⁻¹) : AmbientPinMinusCliffordAlgebra) := by
            noncomm_ring
      _ = _ := by
        rw [hInvMul]
        noncomm_ring
  · rw [hOdd]
    calc
      _ = ((lift : AmbientPinMinusCliffordAlgebra) * value *
          (↑(lift⁻¹) : AmbientPinMinusCliffordAlgebra)) *
        ((lift : AmbientPinMinusCliffordAlgebra) * value *
          (↑(lift⁻¹) : AmbientPinMinusCliffordAlgebra)) := by
            noncomm_ring
      _ = (lift : AmbientPinMinusCliffordAlgebra) * value *
          ((↑(lift⁻¹) : AmbientPinMinusCliffordAlgebra) * lift) * value *
          (↑(lift⁻¹) : AmbientPinMinusCliffordAlgebra) := by
            noncomm_ring
      _ = _ := by
        rw [hInvMul]
        noncomm_ring

/-- The full twisted Pin-minus action preserves its defining negative
quadratic form. -/
theorem ambientPinMinusVectorAction_preserves_pinQuadraticForm
    (lift : AmbientCoordinatePinMinusGroup)
    (tangent : CoverCoordinates) :
    ambientCoverPinMinusQuadraticForm
        (ambientPinMinusVectorAction lift tangent) =
      ambientCoverPinMinusQuadraticForm tangent := by
  apply (algebraMap Real AmbientPinMinusCliffordAlgebra).injective
  rw [← CliffordAlgebra.ι_sq_scalar,
    ambientPinMinusVectorAction_spec,
    ← CliffordAlgebra.ι_sq_scalar]
  rw [ambientPinMinus_twistedConjugation_square]
  rw [CliffordAlgebra.ι_sq_scalar]
  have hMulInv :
      (lift : AmbientPinMinusCliffordAlgebra) *
          (↑(lift⁻¹) : AmbientPinMinusCliffordAlgebra) = 1 := by
    change (lift : AmbientPinMinusCliffordAlgebra) *
      star (lift : AmbientPinMinusCliffordAlgebra) = 1
    exact pinGroup.coe_mul_star_self lift
  rw [← Algebra.commutes (ambientCoverPinMinusQuadraticForm tangent)
    (lift : AmbientPinMinusCliffordAlgebra), mul_assoc, hMulInv, mul_one]

/-- Equivalently, the full twisted action preserves the positive Euclidean
form used by the Whitney reduction. -/
theorem ambientPinMinusVectorAction_preserves_euclideanQuadraticForm
    (lift : AmbientCoordinatePinMinusGroup)
    (tangent : CoverCoordinates) :
    ambientCoverEuclideanQuadraticForm
        (ambientPinMinusVectorAction lift tangent) =
      ambientCoverEuclideanQuadraticForm tangent := by
  simpa only [ambientCoverPinMinusQuadraticForm,
    QuadraticMap.neg_apply, neg_inj] using
    ambientPinMinusVectorAction_preserves_pinQuadraticForm lift tangent

/-- Each Pin-minus element acts by a genuine Euclidean orthogonal isometry. -/
def ambientPinMinusQuadraticIsometry
    (lift : AmbientCoordinatePinMinusGroup) : AmbientOrthogonalIsometry where
  __ := ambientPinMinusVectorEquiv lift
  map_app' := ambientPinMinusVectorAction_preserves_euclideanQuadraticForm lift

@[simp] theorem ambientPinMinusQuadraticIsometry_apply
    (lift : AmbientCoordinatePinMinusGroup)
    (tangent : CoverCoordinates) :
    ambientPinMinusQuadraticIsometry lift tangent =
      ambientPinMinusVectorAction lift tangent :=
  rfl

/-- Composition, identity and inverse preserve the same quadratic form, so
the concrete self-isometries form the actual ambient orthogonal group. -/
noncomputable instance ambientOrthogonalIsometryGroup :
    Group AmbientOrthogonalIsometry where
  one := QuadraticMap.IsometryEquiv.refl ambientCoverEuclideanQuadraticForm
  mul first second := second.trans first
  inv := QuadraticMap.IsometryEquiv.symm
  mul_assoc _ _ _ := rfl
  one_mul _ := by
    apply DFunLike.coe_injective
    funext tangent
    rfl
  mul_one _ := by
    apply DFunLike.coe_injective
    funext tangent
    rfl
  inv_mul_cancel equiv := by
    apply DFunLike.coe_injective
    funext tangent
    exact equiv.symm_apply_apply tangent

/-- The actual full orthogonal projection of the ambient Pin-minus group. -/
def ambientPinMinusOrthogonalProjection :
    AmbientCoordinatePinMinusGroup →* AmbientOrthogonalIsometry where
  toFun := ambientPinMinusQuadraticIsometry
  map_one' := by
    apply DFunLike.coe_injective
    funext tangent
    exact ambientPinMinusVectorAction_one tangent
  map_mul' first second := by
    apply DFunLike.coe_injective
    funext tangent
    exact ambientPinMinusVectorAction_mul first second tangent

@[simp] theorem ambientPinMinusOrthogonalProjection_toLinearEquiv
    (lift : AmbientCoordinatePinMinusGroup) :
    (ambientPinMinusOrthogonalProjection lift).toLinearEquiv =
      ambientPinMinusProjection lift :=
  rfl

/-- The orthogonal projection is continuous for the faithful Clifford and
matrix-coordinate topologies. -/
theorem continuous_ambientPinMinusOrthogonalProjection :
    Continuous ambientPinMinusOrthogonalProjection := by
  rw [ambientOrthogonalToLinearEquiv_isEmbedding.continuous_iff]
  refine continuous_ambientPinMinusProjection.congr ?_
  intro lift
  rfl

/-- Pointwise Cartan--Dieudonné surjectivity now has its honest bundled
orthogonal target. -/
theorem ambientPinMinusOrthogonalProjection_surjective :
    Function.Surjective ambientPinMinusOrthogonalProjection := by
  intro target
  rcases ambientPinMinusO4Surjective target with ⟨lift, hLift⟩
  refine ⟨lift, ?_⟩
  apply DFunLike.coe_injective
  funext tangent
  exact DFunLike.congr_fun hLift tangent

end

end P0EFTJanusMappingTorusAmbientPinMinusOrthogonalProjection4D
end JanusFormal
