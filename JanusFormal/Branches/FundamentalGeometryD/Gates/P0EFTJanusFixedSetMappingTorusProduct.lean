import Mathlib
import JanusFormal.Branches.FundamentalGeometryD.Gates.P0EFTJanusTwistedMappingGenerator

namespace JanusFormal
namespace P0EFTJanusFixedSetMappingTorusProduct

set_option autoImplicit false

variable {X : Type*}

/-- Fixed-point subtype of a fiber involution. -/
abbrev FixedPointSet (rho : X ≃ X) :=
  {x : X // rho x = x}

/-- Translation action induced on the fixed-point cylinder. -/
def fixedSetTranslation
    (rho : X ≃ X)
    (period : ℝ) :
    (FixedPointSet rho × ℝ) ≃
      (FixedPointSet rho × ℝ) where
  toFun p := (p.1, p.2 + period)
  invFun p := (p.1, p.2 - period)
  left_inv p := by
    rcases p with ⟨x, u⟩
    simp
  right_inv p := by
    rcases p with ⟨x, u⟩
    simp

/-- Inclusion of the fixed-point cylinder into the full fiber cylinder. -/
def includeFixedCylinder
    (rho : X ≃ X) :
    FixedPointSet rho × ℝ → X × ℝ :=
  fun p => (p.1.1, p.2)

/-- On fixed points, the twisted generator is exactly pure translation. -/
theorem mapping_generator_restricts_to_translation
    (rho : X ≃ X)
    (period : ℝ)
    (p : FixedPointSet rho × ℝ) :
    P0EFTJanusTwistedMappingGenerator.mappingGenerator rho period
        (includeFixedCylinder rho p) =
      includeFixedCylinder rho (fixedSetTranslation rho period p) := by
  rcases p with ⟨x, u⟩
  change (rho x.1, u + period) = (x.1, u + period)
  rw [x.2]

/-- The square on the fixed set is translation by the doubled period. -/
theorem fixed_set_translation_square
    (rho : X ≃ X)
    (period : ℝ)
    (p : FixedPointSet rho × ℝ) :
    fixedSetTranslation rho period
        (fixedSetTranslation rho period p) =
      (p.1, p.2 + 2 * period) := by
  rcases p with ⟨x, u⟩
  simp [fixedSetTranslation]
  ring

/--
After quotienting the real coordinate by the period, the fixed-point mapping
torus is the product of the fixed fiber with a circle.  For the coordinate
reflection of `S3`, the fixed fiber is the equatorial `S2`, giving the canonical
throat `S2 x S1`.
-/
structure FixedSetProductQuotientStatus where
  fixedFiberConstructed : Prop
  fixedCylinderInvariant : Prop
  restrictedActionPureTranslation : Prop
  translationQuotientCircleConstructed : Prop
  fixedMappingTorusProductHomeomorphismDerived : Prop
  fixedMappingTorusProductDiffeomorphismDerived : Prop


def fixedSetProductQuotientClosed
    (s : FixedSetProductQuotientStatus) : Prop :=
  s.fixedFiberConstructed /\
  s.fixedCylinderInvariant /\
  s.restrictedActionPureTranslation /\
  s.translationQuotientCircleConstructed /\
  s.fixedMappingTorusProductHomeomorphismDerived /\
  s.fixedMappingTorusProductDiffeomorphismDerived

end P0EFTJanusFixedSetMappingTorusProduct
end JanusFormal
