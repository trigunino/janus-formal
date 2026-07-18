import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusAmbientTangentQuadraticReduction

/-!
# The constructible Spin projection of the ambient Euclidean model

Mathlib defines `spinGroup Q` and proves that Clifford conjugation by its
elements preserves the range of the canonical vector inclusion.  It does not
package this action as a homomorphism to the orthogonal group.  For the
positive-definite ambient coordinate form, the vector inclusion is injective,
so this gate constructs that missing projection on the Spin component.

The construction does not identify the normal-line Pin lift with an ambient
lift.  Nor does it promote the result to the full Pin group: that requires the
twisted Clifford action and its multiplicative isometry theorem.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusAmbientSpinProjection

set_option autoImplicit false

noncomputable section

open Set Topology
open CliffordAlgebra MulAction
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusAmbientTangentOrientationCocycle
open P0EFTJanusMappingTorusAmbientTangentQuadraticReduction

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev AmbientData := reflectedSphereData period hPeriod

private abbrev AmbientCover := MappingTorusCover (AmbientData period hPeriod)

/-- The Clifford algebra of the positive Euclidean ambient coordinate form. -/
abbrev AmbientCliffordAlgebra :=
  CliffordAlgebra ambientCoverEuclideanQuadraticForm

/-- Mathlib's Spin group for the positive Euclidean ambient coordinate form. -/
abbrev AmbientCoordinateSpinGroup :=
  spinGroup ambientCoverEuclideanQuadraticForm

/-- Mathlib's Pin group for the same ambient coordinate form. -/
abbrev AmbientCoordinatePinGroup :=
  pinGroup ambientCoverEuclideanQuadraticForm

/-- Positivity makes the canonical vector inclusion into the ambient Clifford
algebra injective. -/
theorem ambientCliffordIota_injective :
    Function.Injective
      (CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm) := by
  intro first second hEqual
  apply sub_eq_zero.mp
  apply ambientCoverEuclideanQuadraticForm_posDef.anisotropic
  have hIota :
      CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm (first - second) = 0 := by
    rw [map_sub, hEqual, sub_self]
  have hSquare := congrArg
    (fun value : AmbientCliffordAlgebra ↦ value * value) hIota
  rw [CliffordAlgebra.ι_sq_scalar, zero_mul] at hSquare
  exact (algebraMap Real AmbientCliffordAlgebra).injective hSquare

@[simp] private theorem ambientSpin_coe_inv_mul
    (lift : AmbientCoordinateSpinGroup) :
    (↑(lift⁻¹) : AmbientCliffordAlgebra) * (lift : AmbientCliffordAlgebra) = 1 :=
  spinGroup.coe_star_mul_self lift

@[simp] private theorem ambientSpin_coe_mul_inv
    (lift : AmbientCoordinateSpinGroup) :
    (lift : AmbientCliffordAlgebra) * (↑(lift⁻¹) : AmbientCliffordAlgebra) = 1 :=
  spinGroup.coe_mul_star_self lift

private theorem ambientSpinConjugation_mem_range
    (lift : AmbientCoordinateSpinGroup)
    (tangent : CoverCoordinates) :
    (lift : AmbientCliffordAlgebra) *
          CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm tangent *
          (↑(lift⁻¹) : AmbientCliffordAlgebra) ∈
      LinearMap.range (CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm) := by
  let unit := spinGroup.toUnits lift
  have hUnit : (↑unit : AmbientCliffordAlgebra) ∈
      spinGroup ambientCoverEuclideanQuadraticForm := by
    exact lift.property
  have hRange := spinGroup.conjAct_smul_ι_mem_range_ι hUnit tangent
  rw [ConjAct.units_smul_def, ConjAct.ofConjAct_toConjAct] at hRange
  exact hRange

/-- Vector obtained by Clifford conjugation by a Spin element. -/
def ambientSpinVectorAction
    (lift : AmbientCoordinateSpinGroup)
    (tangent : CoverCoordinates) : CoverCoordinates :=
  Classical.choose (ambientSpinConjugation_mem_range lift tangent)

@[simp] theorem ambientSpinVectorAction_spec
    (lift : AmbientCoordinateSpinGroup)
    (tangent : CoverCoordinates) :
    CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm
        (ambientSpinVectorAction lift tangent) =
      (lift : AmbientCliffordAlgebra) *
        CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm tangent *
        (↑(lift⁻¹) : AmbientCliffordAlgebra) :=
  Classical.choose_spec (ambientSpinConjugation_mem_range lift tangent)

/-- Clifford conjugation by a Spin element is linear on ambient vectors. -/
def ambientSpinVectorLinearMap
    (lift : AmbientCoordinateSpinGroup) :
    CoverCoordinates →ₗ[Real] CoverCoordinates where
  toFun := ambientSpinVectorAction lift
  map_add' first second := by
    apply ambientCliffordIota_injective
    simp only [map_add, ambientSpinVectorAction_spec]
    noncomm_ring
  map_smul' scalar tangent := by
    apply ambientCliffordIota_injective
    simp only [map_smul, ambientSpinVectorAction_spec, Algebra.smul_def,
      RingHom.id_apply]
    rw [← mul_assoc, ← Algebra.commutes scalar (lift : AmbientCliffordAlgebra)]
    simp only [mul_assoc]

private theorem ambientSpinVectorAction_left_inv
    (lift : AmbientCoordinateSpinGroup)
    (tangent : CoverCoordinates) :
    ambientSpinVectorAction lift⁻¹ (ambientSpinVectorAction lift tangent) = tangent := by
  apply ambientCliffordIota_injective
  simp only [ambientSpinVectorAction_spec]
  calc
    (↑(lift⁻¹) : AmbientCliffordAlgebra) *
          ((lift : AmbientCliffordAlgebra) *
            CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm tangent *
            ↑(lift⁻¹)) * ↑((lift⁻¹)⁻¹) =
        (↑(lift⁻¹) * (lift : AmbientCliffordAlgebra)) *
          CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm tangent *
          (↑(lift⁻¹) * ↑((lift⁻¹)⁻¹)) := by noncomm_ring
    _ = CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm tangent := by simp

private theorem ambientSpinVectorAction_right_inv
    (lift : AmbientCoordinateSpinGroup)
    (tangent : CoverCoordinates) :
    ambientSpinVectorAction lift (ambientSpinVectorAction lift⁻¹ tangent) = tangent := by
  apply ambientCliffordIota_injective
  simp only [ambientSpinVectorAction_spec]
  calc
    (lift : AmbientCliffordAlgebra) *
          (↑(lift⁻¹) *
            CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm tangent *
            ↑((lift⁻¹)⁻¹)) * ↑(lift⁻¹) =
        ((lift : AmbientCliffordAlgebra) * ↑(lift⁻¹)) *
          CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm tangent *
          (↑((lift⁻¹)⁻¹) * ↑(lift⁻¹)) := by noncomm_ring
    _ = CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm tangent := by simp

/-- Invertible linear action of an ambient Spin element. -/
def ambientSpinVectorEquiv
    (lift : AmbientCoordinateSpinGroup) :
    CoverCoordinates ≃ₗ[Real] CoverCoordinates where
  __ := ambientSpinVectorLinearMap lift
  invFun := ambientSpinVectorAction lift⁻¹
  left_inv := ambientSpinVectorAction_left_inv lift
  right_inv := ambientSpinVectorAction_right_inv lift

@[simp] theorem ambientSpinVectorEquiv_apply
    (lift : AmbientCoordinateSpinGroup)
    (tangent : CoverCoordinates) :
    ambientSpinVectorEquiv lift tangent = ambientSpinVectorAction lift tangent :=
  rfl

/-- The Spin action preserves the ambient Euclidean quadratic form. -/
theorem ambientSpinVectorAction_preserves_quadraticForm
    (lift : AmbientCoordinateSpinGroup)
    (tangent : CoverCoordinates) :
    ambientCoverEuclideanQuadraticForm (ambientSpinVectorAction lift tangent) =
      ambientCoverEuclideanQuadraticForm tangent := by
  apply (algebraMap Real AmbientCliffordAlgebra).injective
  rw [← CliffordAlgebra.ι_sq_scalar, ambientSpinVectorAction_spec,
    ← CliffordAlgebra.ι_sq_scalar]
  simp only [mul_assoc]
  rw [← mul_assoc (↑(lift⁻¹) : AmbientCliffordAlgebra)
      (lift : AmbientCliffordAlgebra), ambientSpin_coe_inv_mul, one_mul]
  rw [← mul_assoc
      (CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm tangent)
      (CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm tangent),
    CliffordAlgebra.ι_sq_scalar]
  rw [← mul_assoc, ← Algebra.commutes, mul_assoc, ambientSpin_coe_mul_inv, mul_one]

/-- Spin elements act by genuine isometries of the ambient Euclidean form. -/
def ambientSpinQuadraticIsometry
    (lift : AmbientCoordinateSpinGroup) :
    ambientCoverEuclideanQuadraticForm.IsometryEquiv
      ambientCoverEuclideanQuadraticForm where
  __ := ambientSpinVectorEquiv lift
  map_app' := ambientSpinVectorAction_preserves_quadraticForm lift

@[simp] theorem ambientSpinVectorAction_one
    (tangent : CoverCoordinates) :
    ambientSpinVectorAction (1 : AmbientCoordinateSpinGroup) tangent = tangent := by
  apply ambientCliffordIota_injective
  simp

@[simp] theorem ambientSpinVectorAction_mul
    (first second : AmbientCoordinateSpinGroup)
    (tangent : CoverCoordinates) :
    ambientSpinVectorAction (first * second) tangent =
      ambientSpinVectorAction first (ambientSpinVectorAction second tangent) := by
  apply ambientCliffordIota_injective
  simp only [ambientSpinVectorAction_spec, Submonoid.coe_mul]
  rw [mul_inv_rev]
  simp only [Submonoid.coe_mul]
  noncomm_ring

/-- The missing Mathlib packaging: a genuine group homomorphism from the
ambient coordinate Spin group to real linear automorphisms. -/
def ambientSpinProjection :
    AmbientCoordinateSpinGroup →* (CoverCoordinates ≃ₗ[Real] CoverCoordinates) where
  toFun := ambientSpinVectorEquiv
  map_one' := LinearEquiv.ext ambientSpinVectorAction_one
  map_mul' first second := LinearEquiv.ext (ambientSpinVectorAction_mul first second)

@[simp] theorem ambientSpinProjection_apply
    (lift : AmbientCoordinateSpinGroup)
    (tangent : CoverCoordinates) :
    ambientSpinProjection lift tangent = ambientSpinVectorAction lift tangent :=
  rfl

theorem ambientSpinProjection_is_orthogonal
    (lift : AmbientCoordinateSpinGroup)
    (tangent : CoverCoordinates) :
    ambientCoverEuclideanQuadraticForm (ambientSpinProjection lift tangent) =
      ambientCoverEuclideanQuadraticForm tangent :=
  ambientSpinVectorAction_preserves_quadraticForm lift tangent

/-- Canonical inclusion of the constructible Spin component into Mathlib's
ambient Pin group. -/
def ambientSpinToPin :
    AmbientCoordinateSpinGroup →* AmbientCoordinatePinGroup where
  toFun lift := ⟨lift, lift.property.1⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Mathlib's current Pin API gives a unique vector for the twisted Clifford
action at each Pin element.  It does not package these vectors into a
multiplicative quadratic isometry. -/
theorem ambientPinTwistedImage_existsUnique
    (lift : AmbientCoordinatePinGroup)
    (tangent : CoverCoordinates) :
    ∃! image : CoverCoordinates,
      CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm image =
        involute (lift : AmbientCliffordAlgebra) *
          CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm tangent *
          (↑(lift⁻¹) : AmbientCliffordAlgebra) := by
  let unit := pinGroup.toUnits lift
  have hUnit : (↑unit : AmbientCliffordAlgebra) ∈
      pinGroup ambientCoverEuclideanQuadraticForm :=
    lift.property
  rcases pinGroup.involute_act_ι_mem_range_ι hUnit tangent with
    ⟨image, hImage⟩
  refine ⟨image, hImage, ?_⟩
  intro candidate hCandidate
  exact ambientCliffordIota_injective (hCandidate.trans hImage.symm)

/-- Exact remaining bridge for extending the constructed Spin projection to
the full Pin group.  Its fields are the missing homomorphism, its quadratic
isometry property, agreement with twisted Clifford conjugation, and agreement
with the Spin component; no readiness proposition is used. -/
structure AmbientPinProjectionExtension where
  projection :
    AmbientCoordinatePinGroup →* (CoverCoordinates ≃ₗ[Real] CoverCoordinates)
  projection_is_orthogonal : ∀ lift tangent,
    ambientCoverEuclideanQuadraticForm (projection lift tangent) =
      ambientCoverEuclideanQuadraticForm tangent
  implements_twisted_action : ∀ lift tangent,
    CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm
        (projection lift tangent) =
      involute (lift : AmbientCliffordAlgebra) *
        CliffordAlgebra.ι ambientCoverEuclideanQuadraticForm tangent *
        (↑(lift⁻¹) : AmbientCliffordAlgebra)
  restricts_to_spin :
    projection.comp ambientSpinToPin = ambientSpinProjection

/-- The only remaining atlas-specific data for a Spin Cech lift once the
projection above has been constructed. -/
structure AmbientSpinCechTransitionLift
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod) where
  transitionLift :
    AmbientCover period hPeriod → AmbientCover period hPeriod →
      CoverModel → AmbientCoordinateSpinGroup
  projects_to_transition :
    ∀ first second coordinate
      (hCoordinate :
        coordinate ∈ (ambientAtlasTransition period hPeriod first second).source),
      ambientSpinProjection (transitionLift first second coordinate) =
        (reduction.orthogonalTransition period hPeriod first second coordinate hCoordinate).toLinearEquiv
  normalized :
    ∀ anchor coordinate
      (_hCoordinate :
        coordinate ∈ (ambientAtlasTransition period hPeriod anchor anchor).source),
      transitionLift anchor anchor coordinate = 1
  cocycle :
    ∀ first second third coordinate
      (_hFirstSecond :
        coordinate ∈ (ambientAtlasTransition period hPeriod first second).source)
      (_hSecondThird :
        ambientAtlasTransition period hPeriod first second coordinate ∈
          (ambientAtlasTransition period hPeriod second third).source)
      (_hFirstThird :
        coordinate ∈ (ambientAtlasTransition period hPeriod first third).source),
      transitionLift second third
          (ambientAtlasTransition period hPeriod first second coordinate) *
          transitionLift first second coordinate =
        transitionLift first third coordinate

/-- A Spin transition lift instantiates the algebraic Pin/SpinC Cech contract
with the actual Clifford Spin group and the projection constructed above. -/
def AmbientSpinCechTransitionLift.toPinSpinCCechLiftContract
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (lift : AmbientSpinCechTransitionLift period hPeriod reduction) :
    AmbientPinSpinCCechLiftContract period hPeriod reduction
      AmbientCoordinateSpinGroup ambientSpinProjection where
  projection_is_orthogonal := ambientSpinProjection_is_orthogonal
  transitionLift := lift.transitionLift
  projects_to_transition := lift.projects_to_transition
  normalized := lift.normalized
  cocycle := lift.cocycle

end

end P0EFTJanusMappingTorusAmbientSpinProjection
end JanusFormal
