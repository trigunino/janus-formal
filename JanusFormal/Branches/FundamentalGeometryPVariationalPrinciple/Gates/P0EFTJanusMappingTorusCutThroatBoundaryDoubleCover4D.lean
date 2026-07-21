import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusOrientationDoubleCover
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusThroatComplementSides

/-!
# Boundary candidate for cutting the one-sided throat

Cutting a one-sided hypersurface produces one boundary component which
double-covers the hypersurface, not two independent quotient copies.  The
existing normal-orientation double cover gives that boundary candidate here.
This file is topological only; it does not install a manifold-with-boundary
structure or assert Stokes.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D

set_option autoImplicit false

open Set
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusThroatComplementSides

variable (period : Real) (hPeriod : period ≠ 0)

/-- The connected boundary candidate obtained by cutting the one-sided throat. -/
abbrev CutThroatBoundary := OrientationDoubleThroat period hPeriod

/-- Projection of the cut boundary into the effective four-dimensional bulk. -/
def cutThroatBoundaryToBulk :
    CutThroatBoundary period hPeriod →
      MappingTorus (reflectedSphereData period hPeriod) :=
  fixedThroatQuotientInclusion period hPeriod ∘
    orientationDoubleToThroat period hPeriod

theorem continuous_cutThroatBoundaryToBulk :
    Continuous (cutThroatBoundaryToBulk period hPeriod) :=
  (continuous_fixedThroatQuotientInclusion period hPeriod).comp
    (continuous_orientationDoubleToThroat period hPeriod)

/-- The boundary candidate covers exactly the effective throat. -/
theorem range_cutThroatBoundaryToBulk :
    Set.range (cutThroatBoundaryToBulk period hPeriod) =
      effectiveThroat period hPeriod := by
  ext bulk
  constructor
  · rintro ⟨boundary, rfl⟩
    exact ⟨orientationDoubleToThroat period hPeriod boundary, rfl⟩
  · rintro ⟨throat, rfl⟩
    obtain ⟨boundary, hBoundary⟩ :=
      orientationDoubleToThroat_surjective period hPeriod throat
    exact ⟨boundary, congrArg
      (fixedThroatQuotientInclusion period hPeriod) hBoundary⟩

/-- The residual deck involution exchanges the two lifts without changing
their image in the bulk. -/
theorem cutThroatBoundaryToBulk_deck
    (boundary : CutThroatBoundary period hPeriod) :
    cutThroatBoundaryToBulk period hPeriod
        (orientationDeck period hPeriod boundary) =
      cutThroatBoundaryToBulk period hPeriod boundary := by
  unfold cutThroatBoundaryToBulk
  rw [Function.comp_apply, Function.comp_apply,
    orientationDoubleToThroat_deck]

/-- The two deck-related lifts are genuinely distinct. -/
theorem cutThroatBoundary_deck_ne_self
    (boundary : CutThroatBoundary period hPeriod) :
    orientationDeck period hPeriod boundary ≠ boundary :=
  orientationDeck_ne_self period hPeriod boundary

/-- Every throat point has exactly the two-element orientation fiber in the
cut boundary candidate. -/
theorem cutThroatBoundary_fiber_equiv_two
    (throat : MappingTorus (fixedEquatorData period hPeriod)) :
    Nonempty
      ((cutThroatBoundaryToBulk period hPeriod ⁻¹'
          {fixedThroatQuotientInclusion period hPeriod throat}) ≃ ZMod 2) := by
  have hFiber :
      cutThroatBoundaryToBulk period hPeriod ⁻¹'
          {fixedThroatQuotientInclusion period hPeriod throat} =
        orientationDoubleToThroat period hPeriod ⁻¹' {throat} := by
    ext boundary
    simp only [mem_preimage, mem_singleton_iff]
    exact (fixedThroatQuotientInclusion_injective period hPeriod).eq_iff
  obtain ⟨fiberEquiv⟩ :=
    orientationDouble_fiber_equiv_two period hPeriod throat
  exact ⟨(Equiv.setCongr hFiber).trans fiberEquiv⟩

end P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
end JanusFormal
