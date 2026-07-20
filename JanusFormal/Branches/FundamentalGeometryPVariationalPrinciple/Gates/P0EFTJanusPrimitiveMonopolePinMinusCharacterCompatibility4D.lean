import JanusFormal.Branches.FundamentalGeometryD.Gates.P0EFTJanusThroatMonopoleEmergence
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAmbientPinMinusProjection4D

/-!
# Primitive monopole winding and the ambient Pin-minus character

This gate identifies only the integer transition character.  It does not
construct the still-missing global principal `U(1)` monopole bundle.
-/

namespace JanusFormal
namespace P0EFTJanusPrimitiveMonopolePinMinusCharacterCompatibility4D

open P0EFTJanusMappingTorusAmbientPinMinusProjection4D
open P0EFTJanusThroatMonopoleEmergence

set_option autoImplicit false

/-- The Pin-minus transition associated with an integral monopole winding. -/
noncomputable def primitiveMonopolePinMinusTransition (chernNumber : ℤ) :
    AmbientCoordinatePinMinusGroup :=
  ambientPinMinusReferenceZ4Character (chernNumber : ZMod 4)

/-- PT/charge conjugation sends the transition to its inverse. -/
@[simp] theorem primitiveMonopolePinMinusTransition_pt (chernNumber : ℤ) :
    primitiveMonopolePinMinusTransition
        (ptConjugateChernNumber chernNumber) =
      (primitiveMonopolePinMinusTransition chernNumber)⁻¹ := by
  simp only [primitiveMonopolePinMinusTransition,
    ptConjugateChernNumber,
    ambientPinMinusReferenceZ4Character_intCast, zpow_neg]

/-- Opposite monopole charges have mutually inverse transition characters. -/
theorem primitiveMonopolePinMinusTransition_pt_product (chernNumber : ℤ) :
    primitiveMonopolePinMinusTransition
          (ptConjugateChernNumber chernNumber) *
      primitiveMonopolePinMinusTransition chernNumber = 1 := by
  rw [primitiveMonopolePinMinusTransition_pt]
  simp

/-- A primitive monopole winding has the nontrivial central Pin-minus square. -/
theorem primitiveMonopolePinMinusTransition_square
    (chernNumber : ℤ)
    (hPrimitive : chernNumber.natAbs = 1) :
    primitiveMonopolePinMinusTransition chernNumber *
        primitiveMonopolePinMinusTransition chernNumber =
      ambientPinMinusCentralSign := by
  have hPhase : (chernNumber : ZMod 4) + chernNumber = 2 := by
    obtain hNonneg | hNeg := Int.natAbs_eq chernNumber
    · have : chernNumber = 1 := by omega
      subst chernNumber
      decide
    · have : chernNumber = -1 := by omega
      subst chernNumber
      decide
  calc
    primitiveMonopolePinMinusTransition chernNumber *
          primitiveMonopolePinMinusTransition chernNumber =
        ambientPinMinusReferenceZ4Character
          ((chernNumber : ZMod 4) + chernNumber) := by
      symm
      exact ambientPinMinusReferenceZ4Character.map_add_eq_mul _ _
    _ = ambientPinMinusReferenceZ4Character 2 := by rw [hPhase]
    _ = ambientPinMinusCentralSign :=
      ambientPinMinusReferenceZ4Character_two

/-- A primitive monopole winding projects to the reference reflection. -/
theorem primitiveMonopolePinMinusTransition_projection
    (chernNumber : ℤ)
    (hPrimitive : chernNumber.natAbs = 1) :
    ambientPinMinusProjection
        (primitiveMonopolePinMinusTransition chernNumber) =
      ambientPinMinusReferenceReflection := by
  obtain hNonneg | hNeg := Int.natAbs_eq chernNumber
  · have : chernNumber = 1 := by omega
    subst chernNumber
    convert ambientPinMinusProjection_referenceZ4Character_one using 1
    norm_num [primitiveMonopolePinMinusTransition]
  · have : chernNumber = -1 := by omega
    subst chernNumber
    have hTransition :
        primitiveMonopolePinMinusTransition (-1) =
          (primitiveMonopolePinMinusTransition 1)⁻¹ := by
      simpa [ptConjugateChernNumber] using
        primitiveMonopolePinMinusTransition_pt 1
    rw [hTransition, map_inv, primitiveMonopolePinMinusTransition,
      show ((1 : ℤ) : ZMod 4) = 1 by norm_num,
      ambientPinMinusReferenceZ4Character_one,
      ambientPinMinusProjection_referenceGenerator]
    have hReflectionSquare :
        ambientPinMinusReferenceReflection *
            ambientPinMinusReferenceReflection = 1 := by
      apply LinearEquiv.ext
      intro tangent
      simp
    exact (eq_inv_of_mul_eq_one_left hReflectionSquare).symm

/-- The least nonzero throat Chern sector has the central Pin-minus square. -/
theorem leastNonzeroThroatMonopolePinMinusTransition_square
    (monopole : ThroatMonopoleClass) :
    primitiveMonopolePinMinusTransition monopole.firstChernNumber *
        primitiveMonopolePinMinusTransition monopole.firstChernNumber =
      ambientPinMinusCentralSign :=
  primitiveMonopolePinMinusTransition_square monopole.firstChernNumber
    (least_nonzero_c1_is_primitive monopole)

end P0EFTJanusPrimitiveMonopolePinMinusCharacterCompatibility4D
end JanusFormal
