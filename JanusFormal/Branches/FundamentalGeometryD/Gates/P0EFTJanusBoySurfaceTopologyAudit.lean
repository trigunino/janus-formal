import Mathlib

namespace JanusFormal
namespace P0EFTJanusBoySurfaceTopologyAudit

set_option autoImplicit false

/-- Fundamental-group model of the projective plane underlying Boy's surface. -/
abbrev BoySurfaceLoopGroup := ZMod 2

/-- Fundamental-group model of the product throat `S2 x S1`. -/
abbrev ProductThroatLoopGroup := ℤ

/-- Every element of the Boy/RP2 loop group is killed by doubling. -/
theorem boy_loop_group_is_exponent_two
    (loop : BoySurfaceLoopGroup) :
    loop + loop = 0 := by
  native_decide

/-- The generator of the product-throat loop group is not killed by doubling. -/
theorem throat_generator_is_not_exponent_two :
    (1 : ProductThroatLoopGroup) + 1 ≠ 0 := by
  norm_num

/-- There is no additive equivalence between the two loop-group models. -/
theorem no_additive_equivalence_between_boy_and_product_throat :
    Not (Nonempty (ProductThroatLoopGroup ≃+ BoySurfaceLoopGroup)) := by
  rintro ⟨equivalence⟩
  have hBoy := boy_loop_group_is_exponent_two (equivalence 1)
  have hMapped : equivalence ((1 : ℤ) + 1) = 0 := by
    rw [equivalence.map_add]
    exact hBoy
  have hZero : equivalence (0 : ℤ) = 0 := equivalence.map_zero
  have hDomain : (1 : ℤ) + 1 = 0 := by
    apply equivalence.injective
    rw [hMapped, hZero]
  norm_num at hDomain

/-- Boy's surface and the Janus throat cannot share the stated fundamental-group invariants. -/
theorem boy_surface_cannot_be_product_throat_under_loop_identifications
    (hHomeomorphismWouldGiveLoopEquivalence :
      Nonempty (ProductThroatLoopGroup ≃+ BoySurfaceLoopGroup)) : False :=
  no_additive_equivalence_between_boy_and_product_throat
    hHomeomorphismWouldGiveLoopEquivalence

/--
Boy's surface is an immersion of `RP2`, a two-dimensional nonorientable surface
with `pi1 = Z2`.  The current Janus throat target is the orientable
three-manifold `S2 x S1`, with `pi1 = Z`.  They may share a visual
"self-returning/one-sided" intuition, but they are not the same topology.
The one-sided object in the mapping-torus model is the *normal embedding* of the
three-dimensional throat inside the four-manifold, not the intrinsic topology
of Boy's surface.
-/
structure BoySurfaceComparisonStatus where
  boyUnderlyingRP2Identified : Prop
  boyDimensionTwoProved : Prop
  boyFundamentalGroupZ2Proved : Prop
  throatProductTopologyProved : Prop
  throatDimensionThreeProved : Prop
  throatFundamentalGroupZProved : Prop
  nonhomeomorphismDerived : Prop
  visualAnalogySeparatedFromTopology : Prop


def boySurfaceComparisonClosed
    (s : BoySurfaceComparisonStatus) : Prop :=
  s.boyUnderlyingRP2Identified /\
  s.boyDimensionTwoProved /\
  s.boyFundamentalGroupZ2Proved /\
  s.throatProductTopologyProved /\
  s.throatDimensionThreeProved /\
  s.throatFundamentalGroupZProved /\
  s.nonhomeomorphismDerived /\
  s.visualAnalogySeparatedFromTopology

end P0EFTJanusBoySurfaceTopologyAudit
end JanusFormal
