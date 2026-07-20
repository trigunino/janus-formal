import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusEquatorialBandScalarCurrentDeckTwist4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalThroatGaussianNormalGHYBridge4D

/-!
# Oriented flux signs on the two cut-throat lifts

The deck generator reverses both the latitude scalar current and the outward
normal.  Hence the two oriented lift contributions agree.  This is only the
sign ledger; no cut manifold or Stokes theorem is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBoundaryOrientedFluxSign4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusGaussianNormalEmbeddedHypersurface
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusEquatorialBandScalarCurrentZeroExtension4D
open P0EFTJanusEquatorialBandScalarCurrentDeckTwist4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Scalar flux after applying the outward-normal orientation sign. -/
def orientedCutLiftFlux (orientation : NormalOrientation) (current : Real) : Real :=
  orientation.sign * current

theorem orientedCutLiftFlux_opposite
    (current : Real) :
    orientedCutLiftFlux .decreasing (-current) =
      orientedCutLiftFlux .increasing current := by
  simp [orientedCutLiftFlux, NormalOrientation.sign]

/-- Deck-related boundary lifts contribute with the same oriented sign. -/
theorem equatorialBand_orientedCutLiftFlux_deck_generator
    (field test : SmoothQuotientField period hPeriod Real)
    (input : UnitThreeSphere × Real) :
    orientedCutLiftFlux .decreasing
        (equatorialBandScalarCurrentZeroExtension period hPeriod field test
          (reflectedSphereProductDeck period 1 input)) =
      orientedCutLiftFlux .increasing
        (equatorialBandScalarCurrentZeroExtension period hPeriod field test input) := by
  rw [equatorialBandScalarCurrentZeroExtension_deck_generator]
  exact orientedCutLiftFlux_opposite _

/-- The oriented sum is twice either lift contribution. -/
theorem equatorialBand_twoCutLiftFlux_sum
    (field test : SmoothQuotientField period hPeriod Real)
    (input : UnitThreeSphere × Real) :
    orientedCutLiftFlux .increasing
          (equatorialBandScalarCurrentZeroExtension period hPeriod field test input) +
        orientedCutLiftFlux .decreasing
          (equatorialBandScalarCurrentZeroExtension period hPeriod field test
            (reflectedSphereProductDeck period 1 input)) =
      2 * orientedCutLiftFlux .increasing
        (equatorialBandScalarCurrentZeroExtension period hPeriod field test input) := by
  rw [equatorialBand_orientedCutLiftFlux_deck_generator]
  ring

/-- The difference of the two oriented lift contributions vanishes. -/
theorem equatorialBand_twoCutLiftFlux_difference
    (field test : SmoothQuotientField period hPeriod Real)
    (input : UnitThreeSphere × Real) :
    orientedCutLiftFlux .increasing
          (equatorialBandScalarCurrentZeroExtension period hPeriod field test input) -
      orientedCutLiftFlux .decreasing
          (equatorialBandScalarCurrentZeroExtension period hPeriod field test
            (reflectedSphereProductDeck period 1 input)) = 0 := by
  rw [equatorialBand_orientedCutLiftFlux_deck_generator]
  ring

end
end P0EFTJanusMappingTorusCutBoundaryOrientedFluxSign4D
end JanusFormal
