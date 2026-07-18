import Mathlib.Algebra.Group.AddChar
import Mathlib.Data.ZMod.Basic
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusAmbientSpinProjection

/-!
# Twisted ambient Pin-minus projection in four dimensions

The ambient tangent mapping torus is nonorientable, so the connected Spin
projection cannot lift all of its real `O(4)` transitions.  The correct
Clifford convention for compatibility with the existing order-four normal
`Pin⁻(1)` lift uses the negative Euclidean quadratic form.  A unit normal then
squares to `-1` in the Clifford algebra.

This gate constructs the twisted vector action of Mathlib's full
`pinGroup (-Q)` and packages it as a group homomorphism to real linear
automorphisms.  It also constructs a reference reflection generator, its
nontrivial central square and its order-four law.  No atlas lift is chosen
here.  Identifying the reference axis with the geometric throat normal is
part of the downstream atlas compatibility datum, not asserted in this gate.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusAmbientPinMinusProjection4D

set_option autoImplicit false

noncomputable section

open Set
open CliffordAlgebra
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusAmbientTangentQuadraticReduction

/-- Negative Euclidean convention.  Unit reflections therefore square to
`-1`, as required by the normal `Pin⁻(1)` convention. -/
def ambientCoverPinMinusQuadraticForm :
    QuadraticForm Real CoverCoordinates :=
  -ambientCoverEuclideanQuadraticForm

@[simp] theorem ambientCoverPinMinusQuadraticForm_apply
    (tangent : CoverCoordinates) :
    ambientCoverPinMinusQuadraticForm tangent =
      -(‖tangent.1‖ ^ 2 + tangent.2 ^ 2) := by
  simp [ambientCoverPinMinusQuadraticForm,
    ambientCoverEuclideanQuadraticForm_apply]

/-- Clifford algebra for the ambient `Pin⁻` convention. -/
abbrev AmbientPinMinusCliffordAlgebra :=
  CliffordAlgebra ambientCoverPinMinusQuadraticForm

/-- Mathlib's full Pin group for the negative ambient form. -/
abbrev AmbientCoordinatePinMinusGroup :=
  pinGroup ambientCoverPinMinusQuadraticForm

/-- The vector inclusion remains injective after changing the sign of the
positive-definite form. -/
theorem ambientPinMinusCliffordIota_injective :
    Function.Injective
      (CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm) := by
  intro first second hEqual
  apply sub_eq_zero.mp
  apply ambientCoverEuclideanQuadraticForm_posDef.anisotropic
  have hIota :
      CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm
          (first - second) = 0 := by
    rw [map_sub, hEqual, sub_self]
  have hSquare := congrArg
    (fun value : AmbientPinMinusCliffordAlgebra ↦ value * value) hIota
  rw [CliffordAlgebra.ι_sq_scalar, zero_mul] at hSquare
  have hNegative : ambientCoverPinMinusQuadraticForm
      (first - second) = 0 :=
    (algebraMap Real AmbientPinMinusCliffordAlgebra).injective hSquare
  rw [ambientCoverPinMinusQuadraticForm] at hNegative
  exact neg_eq_zero.mp hNegative

private theorem ambientPinMinusTwistedImage_mem_range
    (lift : AmbientCoordinatePinMinusGroup)
    (tangent : CoverCoordinates) :
    involute (lift : AmbientPinMinusCliffordAlgebra) *
          CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm tangent *
          (↑(lift⁻¹) : AmbientPinMinusCliffordAlgebra) ∈
      LinearMap.range
        (CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm) := by
  let unit := pinGroup.toUnits lift
  have hUnit : (↑unit : AmbientPinMinusCliffordAlgebra) ∈
      pinGroup ambientCoverPinMinusQuadraticForm :=
    lift.property
  exact pinGroup.involute_act_ι_mem_range_ι hUnit tangent

/-- Vector selected by twisted Clifford conjugation by a Pin-minus element. -/
def ambientPinMinusVectorAction
    (lift : AmbientCoordinatePinMinusGroup)
    (tangent : CoverCoordinates) : CoverCoordinates :=
  Classical.choose (ambientPinMinusTwistedImage_mem_range lift tangent)

@[simp] theorem ambientPinMinusVectorAction_spec
    (lift : AmbientCoordinatePinMinusGroup)
    (tangent : CoverCoordinates) :
    CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm
        (ambientPinMinusVectorAction lift tangent) =
      involute (lift : AmbientPinMinusCliffordAlgebra) *
        CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm tangent *
        (↑(lift⁻¹) : AmbientPinMinusCliffordAlgebra) :=
  Classical.choose_spec (ambientPinMinusTwistedImage_mem_range lift tangent)

@[simp] theorem ambientPinMinusVectorAction_one
    (tangent : CoverCoordinates) :
    ambientPinMinusVectorAction
        (1 : AmbientCoordinatePinMinusGroup) tangent = tangent := by
  apply ambientPinMinusCliffordIota_injective
  rw [ambientPinMinusVectorAction_spec]
  simp

@[simp] theorem ambientPinMinusVectorAction_mul
    (first second : AmbientCoordinatePinMinusGroup)
    (tangent : CoverCoordinates) :
    ambientPinMinusVectorAction (first * second) tangent =
      ambientPinMinusVectorAction first
        (ambientPinMinusVectorAction second tangent) := by
  apply ambientPinMinusCliffordIota_injective
  simp only [ambientPinMinusVectorAction_spec, Submonoid.coe_mul]
  rw [mul_inv_rev]
  simp only [Submonoid.coe_mul, map_mul]
  noncomm_ring

/-- The twisted Pin-minus action is linear on ambient vectors. -/
def ambientPinMinusVectorLinearMap
    (lift : AmbientCoordinatePinMinusGroup) :
    CoverCoordinates →ₗ[Real] CoverCoordinates where
  toFun := ambientPinMinusVectorAction lift
  map_add' first second := by
    apply ambientPinMinusCliffordIota_injective
    simp only [map_add, ambientPinMinusVectorAction_spec]
    noncomm_ring
  map_smul' scalar tangent := by
    apply ambientPinMinusCliffordIota_injective
    simp only [map_smul, ambientPinMinusVectorAction_spec,
      Algebra.smul_def, RingHom.id_apply]
    rw [← mul_assoc,
      ← Algebra.commutes scalar
        (involute (lift : AmbientPinMinusCliffordAlgebra))]
    simp only [mul_assoc]

/-- Invertible twisted vector action.  The inverse is the action of the group
inverse. -/
def ambientPinMinusVectorEquiv
    (lift : AmbientCoordinatePinMinusGroup) :
    CoverCoordinates ≃ₗ[Real] CoverCoordinates where
  __ := ambientPinMinusVectorLinearMap lift
  invFun := ambientPinMinusVectorAction lift⁻¹
  left_inv tangent := by
    change ambientPinMinusVectorAction lift⁻¹
      (ambientPinMinusVectorAction lift tangent) = tangent
    rw [← ambientPinMinusVectorAction_mul]
    simp
  right_inv tangent := by
    change ambientPinMinusVectorAction lift
      (ambientPinMinusVectorAction lift⁻¹ tangent) = tangent
    rw [← ambientPinMinusVectorAction_mul]
    simp

/-- Genuine multiplicative twisted projection of the ambient Pin-minus
group to real linear automorphisms. -/
def ambientPinMinusProjection :
    AmbientCoordinatePinMinusGroup →*
      (CoverCoordinates ≃ₗ[Real] CoverCoordinates) where
  toFun := ambientPinMinusVectorEquiv
  map_one' := LinearEquiv.ext ambientPinMinusVectorAction_one
  map_mul' first second :=
    LinearEquiv.ext (ambientPinMinusVectorAction_mul first second)

@[simp] theorem ambientPinMinusProjection_apply
    (lift : AmbientCoordinatePinMinusGroup)
    (tangent : CoverCoordinates) :
    ambientPinMinusProjection lift tangent =
      ambientPinMinusVectorAction lift tangent :=
  rfl

/-- Fixed unit reference vector.  It is an algebraic reflection axis; no
chartwise identification with the geometric throat normal is made here. -/
def ambientPinMinusReferenceVector : CoverCoordinates :=
  (0, 1)

@[simp] theorem ambientPinMinusReferenceVector_positive_unit :
    ambientCoverEuclideanQuadraticForm ambientPinMinusReferenceVector = 1 := by
  simp [ambientPinMinusReferenceVector,
    ambientCoverEuclideanQuadraticForm_apply]

@[simp] theorem ambientPinMinusReferenceVector_negative_unit :
    ambientCoverPinMinusQuadraticForm ambientPinMinusReferenceVector = -1 := by
  simp [ambientCoverPinMinusQuadraticForm,
    ambientPinMinusReferenceVector, ambientCoverEuclideanQuadraticForm_apply]

/-- Linear functional whose rank-one reflection flips the reference normal
coordinate and fixes the three tangential coordinates. -/
def ambientPinMinusReferenceReflectionFunctional :
    Module.Dual Real CoverCoordinates where
  toFun tangent := 2 * tangent.2
  map_add' first second := by
    change 2 * (first.2 + second.2) = 2 * first.2 + 2 * second.2
    ring
  map_smul' scalar tangent := by
    change 2 * (scalar * tangent.2) = scalar * (2 * tangent.2)
    ring

@[simp] theorem ambientPinMinusReferenceReflectionFunctional_self :
    ambientPinMinusReferenceReflectionFunctional
        ambientPinMinusReferenceVector = 2 := by
  simp [ambientPinMinusReferenceReflectionFunctional,
    ambientPinMinusReferenceVector]

/-- The concrete `O(4)` reflection represented by the reference Pin-minus
generator. -/
def ambientPinMinusReferenceReflection :
    CoverCoordinates ≃ₗ[Real] CoverCoordinates :=
  (LinearEquiv.refl Real (EuclideanSpace Real (Fin 3))).prodCongr
    (LinearEquiv.neg Real)

@[simp] theorem ambientPinMinusReferenceReflection_apply
    (tangent : CoverCoordinates) :
    ambientPinMinusReferenceReflection tangent =
      (tangent.1, -tangent.2) := by
  simp [ambientPinMinusReferenceReflection]

theorem ambientPinMinusReferenceReflection_det :
    LinearEquiv.det ambientPinMinusReferenceReflection = (-1 : Realˣ) := by
  apply Units.ext
  rw [LinearEquiv.coe_det]
  change LinearMap.det
      ((LinearMap.id : EuclideanSpace Real (Fin 3) →ₗ[Real]
          EuclideanSpace Real (Fin 3)).prodMap
        (LinearEquiv.neg Real : Real ≃ₗ[Real] Real).toLinearMap) = -1
  rw [LinearMap.det_prodMap, LinearMap.det_id, one_mul,
    LinearMap.det_ring]
  norm_num

@[simp] theorem ambientCoverPinMinusQuadraticForm_polar_reference
    (tangent : CoverCoordinates) :
    QuadraticMap.polar ambientCoverPinMinusQuadraticForm
        ambientPinMinusReferenceVector tangent = -2 * tangent.2 := by
  simp [QuadraticMap.polar, ambientCoverPinMinusQuadraticForm_apply,
    ambientPinMinusReferenceVector]
  ring

/-- Every positive-Euclidean unit normal gives a genuine odd Pin-minus
generator in the negative Clifford convention. -/
theorem ambientPinMinusUnitNormalGenerator_mem
    (normal : CoverCoordinates)
    (hNormal : ambientCoverEuclideanQuadraticForm normal = 1) :
    CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm normal ∈
      pinGroup ambientCoverPinMinusQuadraticForm := by
  have hNegative : ambientCoverPinMinusQuadraticForm normal = -1 := by
    simp [ambientCoverPinMinusQuadraticForm, hNormal]
  rw [pinGroup.mem_iff]
  constructor
  · have hQuadraticUnit : IsUnit
        (ambientCoverPinMinusQuadraticForm normal) := by
      rw [hNegative]
      exact isUnit_neg_one
    obtain ⟨unit, hUnitCoe⟩ :=
      CliffordAlgebra.isUnit_ι_of_isUnit
        (Q := ambientCoverPinMinusQuadraticForm) hQuadraticUnit
    apply Submonoid.mem_map.mpr
    refine ⟨unit, ?_, ?_⟩
    · apply Subgroup.subset_closure
      change (unit : AmbientPinMinusCliffordAlgebra) ∈
        Set.range (CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm)
      exact ⟨normal, hUnitCoe.symm⟩
    · simpa only [Units.coeHom_apply, hUnitCoe]
  · apply Unitary.mem_iff.mpr
    constructor
    · calc
        star (CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm normal) *
            CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm normal =
            -(CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm normal *
              CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm normal) := by
              rw [CliffordAlgebra.star_ι, neg_mul]
        _ = 1 := by
          rw [CliffordAlgebra.ι_sq_scalar, hNegative]
          simp
    · calc
        CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm normal *
            star (CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm normal) =
            -(CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm normal *
              CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm normal) := by
              rw [CliffordAlgebra.star_ι, mul_neg]
        _ = 1 := by
          rw [CliffordAlgebra.ι_sq_scalar, hNegative]
          simp

/-- Canonical Pin-minus lift attached to a unit local normal. -/
def ambientPinMinusUnitNormalGenerator
    (normal : CoverCoordinates)
    (hNormal : ambientCoverEuclideanQuadraticForm normal = 1) :
    AmbientCoordinatePinMinusGroup :=
  ⟨CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm normal,
    ambientPinMinusUnitNormalGenerator_mem normal hNormal⟩

@[simp] theorem ambientPinMinusUnitNormalGenerator_coe
    (normal : CoverCoordinates)
    (hNormal : ambientCoverEuclideanQuadraticForm normal = 1) :
    (ambientPinMinusUnitNormalGenerator normal hNormal :
      AmbientPinMinusCliffordAlgebra) =
      CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm normal :=
  rfl

/-- Exact rank-one reflection formula for the Pin-minus lift of an arbitrary
positive-Euclidean unit normal. -/
theorem ambientPinMinusProjection_unitNormalGenerator_apply
    (normal : CoverCoordinates)
    (hNormal : ambientCoverEuclideanQuadraticForm normal = 1)
    (tangent : CoverCoordinates) :
    ambientPinMinusProjection
        (ambientPinMinusUnitNormalGenerator normal hNormal) tangent =
      tangent + QuadraticMap.polar ambientCoverPinMinusQuadraticForm
        normal tangent • normal := by
  apply ambientPinMinusCliffordIota_injective
  rw [ambientPinMinusProjection_apply, ambientPinMinusVectorAction_spec]
  let generator := ambientPinMinusUnitNormalGenerator normal hNormal
  let unit := pinGroup.toUnits generator
  letI := unit.invertible
  letI : Invertible
      (CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm normal) := by
    change Invertible (unit : AmbientPinMinusCliffordAlgebra)
    infer_instance
  letI : Invertible (ambientCoverPinMinusQuadraticForm normal) :=
    invertibleOfInvertibleι ambientCoverPinMinusQuadraticForm normal
  change involute
          (CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm normal) *
        CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm tangent *
        (↑(unit⁻¹) : AmbientPinMinusCliffordAlgebra) =
      CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm
        (tangent + QuadraticMap.polar ambientCoverPinMinusQuadraticForm
          normal tangent • normal)
  have hUnit : CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm normal =
      (unit : AmbientPinMinusCliffordAlgebra) := rfl
  simp_rw [← invOf_units unit, ← hUnit, CliffordAlgebra.involute_ι,
    neg_mul, CliffordAlgebra.ι_mul_ι_mul_invOf_ι, ← map_neg]
  congr 1
  have hNegative : ambientCoverPinMinusQuadraticForm normal = -1 := by
    simp [ambientCoverPinMinusQuadraticForm, hNormal]
  have hInverse : ⅟(ambientCoverPinMinusQuadraticForm normal) =
      (-1 : Real) := by
    rw [invOf_eq_inv, hNegative]
    norm_num
  rw [hInverse]
  module

/-- Integer cyclic lift generated by a chosen unit local normal. -/
def ambientPinMinusUnitNormalWindingLift
    (normal : CoverCoordinates)
    (hNormal : ambientCoverEuclideanQuadraticForm normal = 1)
    (winding : Int) : AmbientCoordinatePinMinusGroup :=
  ambientPinMinusUnitNormalGenerator normal hNormal ^ winding

@[simp] theorem ambientPinMinusUnitNormalWindingLift_zero
    (normal : CoverCoordinates)
    (hNormal : ambientCoverEuclideanQuadraticForm normal = 1) :
    ambientPinMinusUnitNormalWindingLift normal hNormal 0 = 1 := by
  simp [ambientPinMinusUnitNormalWindingLift]

theorem ambientPinMinusUnitNormalWindingLift_add
    (normal : CoverCoordinates)
    (hNormal : ambientCoverEuclideanQuadraticForm normal = 1)
    (first second : Int) :
    ambientPinMinusUnitNormalWindingLift normal hNormal (first + second) =
      ambientPinMinusUnitNormalWindingLift normal hNormal first *
        ambientPinMinusUnitNormalWindingLift normal hNormal second := by
  simp [ambientPinMinusUnitNormalWindingLift, zpow_add]

theorem ambientPinMinusProjection_unitNormalWindingLift
    (normal : CoverCoordinates)
    (hNormal : ambientCoverEuclideanQuadraticForm normal = 1)
    (winding : Int) :
    ambientPinMinusProjection
        (ambientPinMinusUnitNormalWindingLift normal hNormal winding) =
      ambientPinMinusProjection
          (ambientPinMinusUnitNormalGenerator normal hNormal) ^ winding := by
  exact map_zpow ambientPinMinusProjection _ winding

private theorem ambientPinMinusReferenceGenerator_mem :
    CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm
        ambientPinMinusReferenceVector ∈
      pinGroup ambientCoverPinMinusQuadraticForm := by
  rw [pinGroup.mem_iff]
  constructor
  · have hQuadraticUnit : IsUnit
        (ambientCoverPinMinusQuadraticForm ambientPinMinusReferenceVector) := by
      rw [ambientPinMinusReferenceVector_negative_unit]
      exact isUnit_neg_one
    obtain ⟨unit, hUnitCoe⟩ :=
      CliffordAlgebra.isUnit_ι_of_isUnit
        (Q := ambientCoverPinMinusQuadraticForm) hQuadraticUnit
    apply Submonoid.mem_map.mpr
    refine ⟨unit, ?_, ?_⟩
    · apply Subgroup.subset_closure
      change (unit : AmbientPinMinusCliffordAlgebra) ∈
        Set.range
          (CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm)
      exact ⟨ambientPinMinusReferenceVector, hUnitCoe.symm⟩
    · simpa only [Units.coeHom_apply, hUnitCoe]
  · apply Unitary.mem_iff.mpr
    constructor
    · calc
        star (CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm
              ambientPinMinusReferenceVector) *
            CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm
              ambientPinMinusReferenceVector =
            -(CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm
                ambientPinMinusReferenceVector *
              CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm
                ambientPinMinusReferenceVector) := by
              rw [CliffordAlgebra.star_ι, neg_mul]
        _ = 1 := by
          rw [CliffordAlgebra.ι_sq_scalar,
            ambientPinMinusReferenceVector_negative_unit]
          simp
    · calc
        CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm
              ambientPinMinusReferenceVector *
            star (CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm
              ambientPinMinusReferenceVector) =
            -(CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm
                ambientPinMinusReferenceVector *
              CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm
                ambientPinMinusReferenceVector) := by
              rw [CliffordAlgebra.star_ι, mul_neg]
        _ = 1 := by
          rw [CliffordAlgebra.ι_sq_scalar,
            ambientPinMinusReferenceVector_negative_unit]
          simp

/-- Clifford lift of the reference reflection. -/
def ambientPinMinusReferenceGenerator : AmbientCoordinatePinMinusGroup :=
  ⟨CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm
      ambientPinMinusReferenceVector,
    ambientPinMinusReferenceGenerator_mem⟩

@[simp] theorem ambientPinMinusReferenceGenerator_coe :
    (ambientPinMinusReferenceGenerator : AmbientPinMinusCliffordAlgebra) =
      CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm
        ambientPinMinusReferenceVector :=
  rfl

/-- The twisted Clifford action of the reference generator is exactly the
rank-one reflection above. -/
theorem ambientPinMinusProjection_referenceGenerator :
    ambientPinMinusProjection ambientPinMinusReferenceGenerator =
      ambientPinMinusReferenceReflection := by
  apply LinearEquiv.ext
  intro tangent
  apply ambientPinMinusCliffordIota_injective
  rw [ambientPinMinusProjection_apply, ambientPinMinusVectorAction_spec]
  let unit := pinGroup.toUnits ambientPinMinusReferenceGenerator
  letI := unit.invertible
  letI : Invertible
      (CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm
        ambientPinMinusReferenceVector) := by
    change Invertible (unit : AmbientPinMinusCliffordAlgebra)
    infer_instance
  letI : Invertible
      (ambientCoverPinMinusQuadraticForm ambientPinMinusReferenceVector) :=
    invertibleOfInvertibleι ambientCoverPinMinusQuadraticForm
      ambientPinMinusReferenceVector
  change
    involute
          (CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm
            ambientPinMinusReferenceVector) *
        CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm tangent *
        (↑(unit⁻¹) : AmbientPinMinusCliffordAlgebra) =
      CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm
        (ambientPinMinusReferenceReflection tangent)
  have hUnit :
      CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm
          ambientPinMinusReferenceVector =
        (unit : AmbientPinMinusCliffordAlgebra) := rfl
  simp_rw [← invOf_units unit, ← hUnit, CliffordAlgebra.involute_ι, neg_mul,
    CliffordAlgebra.ι_mul_ι_mul_invOf_ι, ← map_neg]
  congr 1
  have hInverse :
      ⅟(ambientCoverPinMinusQuadraticForm ambientPinMinusReferenceVector) =
        (-1 : Real) := by
    rw [invOf_eq_inv, ambientPinMinusReferenceVector_negative_unit]
    norm_num
  rw [hInverse, ambientCoverPinMinusQuadraticForm_polar_reference,
    ambientPinMinusReferenceReflection_apply]
  ext <;> simp [ambientPinMinusReferenceVector] <;> ring

/-- The central sign is the square of the reference reflection lift. -/
def ambientPinMinusCentralSign : AmbientCoordinatePinMinusGroup :=
  ambientPinMinusReferenceGenerator * ambientPinMinusReferenceGenerator

@[simp] theorem ambientPinMinusCentralSign_coe :
    (ambientPinMinusCentralSign : AmbientPinMinusCliffordAlgebra) = -1 := by
  change CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm
        ambientPinMinusReferenceVector *
      CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm
        ambientPinMinusReferenceVector = -1
  rw [CliffordAlgebra.ι_sq_scalar,
    ambientPinMinusReferenceVector_negative_unit]
  simp

/-- Every unit-normal generator squares to the same nontrivial central sign. -/
theorem ambientPinMinusUnitNormalGenerator_square
    (normal : CoverCoordinates)
    (hNormal : ambientCoverEuclideanQuadraticForm normal = 1) :
    ambientPinMinusUnitNormalGenerator normal hNormal *
        ambientPinMinusUnitNormalGenerator normal hNormal =
      ambientPinMinusCentralSign := by
  apply Subtype.ext
  change CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm normal *
      CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm normal =
    (ambientPinMinusCentralSign : AmbientPinMinusCliffordAlgebra)
  have hNegative : ambientCoverPinMinusQuadraticForm normal = -1 := by
    simp [ambientCoverPinMinusQuadraticForm, hNormal]
  rw [CliffordAlgebra.ι_sq_scalar, hNegative,
    ambientPinMinusCentralSign_coe, map_neg, map_one]

theorem ambientPinMinusCentralSign_ne_one :
    ambientPinMinusCentralSign ≠ 1 := by
  intro hSign
  have hCoe := congrArg
    (fun lift : AmbientCoordinatePinMinusGroup ↦
      (lift : AmbientPinMinusCliffordAlgebra)) hSign
  rw [ambientPinMinusCentralSign_coe] at hCoe
  have hCoe' : (-1 : AmbientPinMinusCliffordAlgebra) = 1 := by
    simpa using hCoe
  have hMap : algebraMap Real AmbientPinMinusCliffordAlgebra (-1) =
      algebraMap Real AmbientPinMinusCliffordAlgebra 1 := by
    simpa using hCoe'
  have hScalar :=
    (algebraMap Real AmbientPinMinusCliffordAlgebra).injective hMap
  norm_num at hScalar

theorem ambientPinMinusCentralSign_central
    (lift : AmbientCoordinatePinMinusGroup) :
    ambientPinMinusCentralSign * lift =
      lift * ambientPinMinusCentralSign := by
  apply Subtype.ext
  change (ambientPinMinusCentralSign : AmbientPinMinusCliffordAlgebra) *
      (lift : AmbientPinMinusCliffordAlgebra) =
    (lift : AmbientPinMinusCliffordAlgebra) *
      (ambientPinMinusCentralSign : AmbientPinMinusCliffordAlgebra)
  simp

theorem ambientPinMinusReferenceGenerator_square :
    ambientPinMinusReferenceGenerator * ambientPinMinusReferenceGenerator =
      ambientPinMinusCentralSign :=
  rfl

theorem ambientPinMinusCentralSign_square :
    ambientPinMinusCentralSign * ambientPinMinusCentralSign = 1 := by
  apply Subtype.ext
  change (ambientPinMinusCentralSign : AmbientPinMinusCliffordAlgebra) *
      (ambientPinMinusCentralSign : AmbientPinMinusCliffordAlgebra) = 1
  simp

/-- The reference reflection lift has the exact order-four `Pin⁻` pattern. -/
theorem ambientPinMinusReferenceGenerator_fourth :
    ambientPinMinusReferenceGenerator ^ 4 = 1 := by
  calc
    ambientPinMinusReferenceGenerator ^ 4 =
        (ambientPinMinusReferenceGenerator * ambientPinMinusReferenceGenerator) *
          (ambientPinMinusReferenceGenerator *
            ambientPinMinusReferenceGenerator) := by
      rw [show (4 : Nat) = 2 + 2 by decide, pow_add, pow_two]
    _ = ambientPinMinusCentralSign * ambientPinMinusCentralSign := by
      rw [ambientPinMinusReferenceGenerator_square]
    _ = 1 := ambientPinMinusCentralSign_square

private def ambientPinMinusReferenceGeneratorIntHom :
    Int →+ Additive AmbientCoordinatePinMinusGroup :=
  zmultiplesHom (Additive AmbientCoordinatePinMinusGroup)
    (Additive.ofMul ambientPinMinusReferenceGenerator)

private theorem ambientPinMinusReferenceGeneratorIntHom_four :
    ambientPinMinusReferenceGeneratorIntHom 4 = 0 := by
  apply Additive.toMul.injective
  simp only [ambientPinMinusReferenceGeneratorIntHom, zmultiplesHom_apply,
    toMul_zsmul, toMul_ofMul, toMul_zero]
  rw [zpow_ofNat, ambientPinMinusReferenceGenerator_fourth]

/-- Canonical additive lift of the order-four reference phase. -/
def ambientPinMinusReferenceZ4AddHom :
    ZMod 4 →+ Additive AmbientCoordinatePinMinusGroup :=
  ZMod.lift 4
    ⟨ambientPinMinusReferenceGeneratorIntHom,
      ambientPinMinusReferenceGeneratorIntHom_four⟩

/-- Canonical multiplicative character of the normal `ZMod 4` model into the
ambient Pin-minus group.  Its geometric use still requires the downstream
chartwise normal identification. -/
def ambientPinMinusReferenceZ4Character :
    AddChar (ZMod 4) AmbientCoordinatePinMinusGroup :=
  AddChar.toAddMonoidHomEquiv.symm ambientPinMinusReferenceZ4AddHom

/-- Evaluating the reference character on an integer residue is exactly the
corresponding integer power of the reference Pin-minus generator. -/
theorem ambientPinMinusReferenceZ4Character_intCast (winding : Int) :
    ambientPinMinusReferenceZ4Character (winding : ZMod 4) =
      ambientPinMinusReferenceGenerator ^ winding := by
  change (ambientPinMinusReferenceZ4AddHom (winding : ZMod 4)).toMul = _
  have hLift :
      ambientPinMinusReferenceZ4AddHom (winding : ZMod 4) =
        ambientPinMinusReferenceGeneratorIntHom winding := by
    exact ZMod.lift_coe 4
      ⟨ambientPinMinusReferenceGeneratorIntHom,
        ambientPinMinusReferenceGeneratorIntHom_four⟩ winding
  rw [hLift]
  simp [ambientPinMinusReferenceGeneratorIntHom]

@[simp] theorem ambientPinMinusReferenceZ4Character_one :
    ambientPinMinusReferenceZ4Character 1 =
      ambientPinMinusReferenceGenerator := by
  change (ambientPinMinusReferenceZ4AddHom (1 : ZMod 4)).toMul =
    ambientPinMinusReferenceGenerator
  have hOne :
      ambientPinMinusReferenceZ4AddHom (1 : ZMod 4) =
        ambientPinMinusReferenceGeneratorIntHom 1 := by
    exact ZMod.lift_coe 4
      ⟨ambientPinMinusReferenceGeneratorIntHom,
        ambientPinMinusReferenceGeneratorIntHom_four⟩ 1
  rw [hOne]
  simp [ambientPinMinusReferenceGeneratorIntHom]

@[simp] theorem ambientPinMinusReferenceZ4Character_two :
    ambientPinMinusReferenceZ4Character 2 =
      ambientPinMinusCentralSign := by
  calc
    ambientPinMinusReferenceZ4Character 2 =
        ambientPinMinusReferenceZ4Character (1 + 1) := by
      exact congrArg
        (fun phase : ZMod 4 ↦ ambientPinMinusReferenceZ4Character phase)
        (by decide : (2 : ZMod 4) = 1 + 1)
    _ = ambientPinMinusReferenceZ4Character 1 *
        ambientPinMinusReferenceZ4Character 1 :=
      ambientPinMinusReferenceZ4Character.map_add_eq_mul 1 1
    _ = ambientPinMinusCentralSign := by
      rw [ambientPinMinusReferenceZ4Character_one,
        ambientPinMinusReferenceGenerator_square]

@[simp] theorem ambientPinMinusReferenceZ4Character_three :
    ambientPinMinusReferenceZ4Character 3 =
      ambientPinMinusCentralSign * ambientPinMinusReferenceGenerator := by
  calc
    ambientPinMinusReferenceZ4Character 3 =
        ambientPinMinusReferenceZ4Character (2 + 1) := by
      exact congrArg ambientPinMinusReferenceZ4Character
        (by native_decide : (3 : ZMod 4) = 2 + 1)
    _ = ambientPinMinusReferenceZ4Character 2 *
        ambientPinMinusReferenceZ4Character 1 :=
      ambientPinMinusReferenceZ4Character.map_add_eq_mul 2 1
    _ = ambientPinMinusCentralSign * ambientPinMinusReferenceGenerator := by
      rw [ambientPinMinusReferenceZ4Character_two,
        ambientPinMinusReferenceZ4Character_one]

theorem ambientPinMinusReferenceZ4Character_two_ne_one :
    ambientPinMinusReferenceZ4Character 2 ≠ 1 := by
  rw [ambientPinMinusReferenceZ4Character_two]
  exact ambientPinMinusCentralSign_ne_one

/-- The Clifford central sign acts trivially on ambient vectors. -/
@[simp] theorem ambientPinMinusProjection_centralSign :
    ambientPinMinusProjection ambientPinMinusCentralSign = 1 := by
  apply LinearEquiv.ext
  intro tangent
  apply ambientPinMinusCliffordIota_injective
  rw [ambientPinMinusProjection_apply, ambientPinMinusVectorAction_spec]
  have hInv : ambientPinMinusCentralSign⁻¹ =
      ambientPinMinusCentralSign :=
    (eq_inv_of_mul_eq_one_left ambientPinMinusCentralSign_square).symm
  rw [hInv]
  simp

/-- Reversing a unit normal changes its Pin-minus generator by the nontrivial
central sign. -/
theorem ambientPinMinusUnitNormalGenerator_neg
    (normal : CoverCoordinates)
    (hNormal : ambientCoverEuclideanQuadraticForm normal = 1)
    (hNegNormal : ambientCoverEuclideanQuadraticForm (-normal) = 1) :
    ambientPinMinusUnitNormalGenerator (-normal) hNegNormal =
      ambientPinMinusCentralSign *
        ambientPinMinusUnitNormalGenerator normal hNormal := by
  apply Subtype.ext
  rw [ambientPinMinusUnitNormalGenerator_coe]
  change CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm (-normal) =
    (ambientPinMinusCentralSign : AmbientPinMinusCliffordAlgebra) *
      (ambientPinMinusUnitNormalGenerator normal hNormal :
        AmbientPinMinusCliffordAlgebra)
  rw [ambientPinMinusCentralSign_coe,
    ambientPinMinusUnitNormalGenerator_coe, map_neg]
  simp

/-- The projected reflection is independent of the sign chosen for its unit
normal. -/
theorem ambientPinMinusProjection_unitNormalGenerator_neg
    (normal : CoverCoordinates)
    (hNormal : ambientCoverEuclideanQuadraticForm normal = 1)
    (hNegNormal : ambientCoverEuclideanQuadraticForm (-normal) = 1) :
    ambientPinMinusProjection
        (ambientPinMinusUnitNormalGenerator (-normal) hNegNormal) =
      ambientPinMinusProjection
        (ambientPinMinusUnitNormalGenerator normal hNormal) := by
  rw [ambientPinMinusUnitNormalGenerator_neg normal hNormal hNegNormal,
    map_mul, ambientPinMinusProjection_centralSign, one_mul]

/-- Exact central gauge law for every integer power of a unit-normal lift. -/
theorem ambientPinMinusUnitNormalWindingLift_neg
    (normal : CoverCoordinates)
    (hNormal : ambientCoverEuclideanQuadraticForm normal = 1)
    (hNegNormal : ambientCoverEuclideanQuadraticForm (-normal) = 1)
    (winding : Int) :
    ambientPinMinusUnitNormalWindingLift (-normal) hNegNormal winding =
      ambientPinMinusCentralSign ^ winding *
        ambientPinMinusUnitNormalWindingLift normal hNormal winding := by
  rw [ambientPinMinusUnitNormalWindingLift,
    ambientPinMinusUnitNormalGenerator_neg normal hNormal hNegNormal,
    ambientPinMinusUnitNormalWindingLift]
  have hCommute : Commute ambientPinMinusCentralSign
      (ambientPinMinusUnitNormalGenerator normal hNormal) :=
    ambientPinMinusCentralSign_central
      (ambientPinMinusUnitNormalGenerator normal hNormal)
  exact hCommute.mul_zpow winding

@[simp] theorem ambientPinMinusProjection_referenceZ4Character_zero :
    ambientPinMinusProjection (ambientPinMinusReferenceZ4Character 0) = 1 := by
  simp

@[simp] theorem ambientPinMinusProjection_referenceZ4Character_one :
    ambientPinMinusProjection (ambientPinMinusReferenceZ4Character 1) =
      ambientPinMinusReferenceReflection := by
  rw [ambientPinMinusReferenceZ4Character_one,
    ambientPinMinusProjection_referenceGenerator]

@[simp] theorem ambientPinMinusProjection_referenceZ4Character_two :
    ambientPinMinusProjection (ambientPinMinusReferenceZ4Character 2) = 1 := by
  rw [ambientPinMinusReferenceZ4Character_two,
    ambientPinMinusProjection_centralSign]

@[simp] theorem ambientPinMinusProjection_referenceZ4Character_three :
    ambientPinMinusProjection (ambientPinMinusReferenceZ4Character 3) =
      ambientPinMinusReferenceReflection := by
  rw [ambientPinMinusReferenceZ4Character_three, map_mul,
    ambientPinMinusProjection_centralSign,
    ambientPinMinusProjection_referenceGenerator, one_mul]

end

end P0EFTJanusMappingTorusAmbientPinMinusProjection4D
end JanusFormal
