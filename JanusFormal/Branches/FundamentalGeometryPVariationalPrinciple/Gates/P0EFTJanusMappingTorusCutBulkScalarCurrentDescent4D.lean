import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBoundaryScalarCurrentDescent4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D

/-!
# Scalar-current descent to the cut bulk

Even ambient windings preserve the sign-twisted current, so it descends to a
continuous scalar on the doubled-period positive-hemisphere cut bulk.  Its
boundary restriction is the previously constructed cut-boundary current.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkScalarCurrentDescent4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusEquatorialBandScalarCurrentZeroExtension4D
open P0EFTJanusEquatorialBandScalarCurrentDeckTwist4D
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusCutBoundaryScalarCurrentDescent4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev CutBulkCover :=
  MappingTorusCover (cutBulkData period hPeriod)

/-- Upstairs cutoff current on the positive-hemisphere cut cover. -/
def cutBulkScalarCurrentCover
    (field test : SmoothQuotientField period hPeriod Real)
    (point : CutBulkCover period hPeriod) : Real :=
  equatorialBandScalarCurrentZeroExtension period hPeriod field test
    (point.fiber.1, point.time)

theorem continuous_cutBulkScalarCurrentCover
    (field test : SmoothQuotientField period hPeriod Real) :
    Continuous (cutBulkScalarCurrentCover period hPeriod field test) := by
  have hInput : Continuous (fun point : CutBulkCover period hPeriod ↦
      (point.fiber.1, point.time)) :=
    (continuous_subtype_val.comp (continuous_fiber _)).prodMk
      (continuous_time _)
  exact (equatorialBandScalarCurrentZeroExtension_contMDiff
    period hPeriod field test).continuous.comp hInput

private theorem cutBulkInput_even_vadd
    (winding : Int) (point : CutBulkCover period hPeriod) :
    ((winding +ᵥ point).fiber.1, (winding +ᵥ point).time) =
      reflectedSphereProductDeck period (2 * winding)
        (point.fiber.1, point.time) := by
  have hEquivariant := congrArg
    (coverHomeomorphProd (reflectedSphereData period hPeriod))
    (cutBulkCoverToAmbient_even_equivariant period hPeriod winding point)
  rw [coverHomeomorphProd_vadd_eq_reflectedSphereProductDeck] at hEquivariant
  exact hEquivariant

theorem cutBulkScalarCurrentCover_invariant
    (field test : SmoothQuotientField period hPeriod Real)
    (winding : Int) (point : CutBulkCover period hPeriod) :
    cutBulkScalarCurrentCover period hPeriod field test (winding +ᵥ point) =
      cutBulkScalarCurrentCover period hPeriod field test point := by
  simp only [cutBulkScalarCurrentCover]
  rw [cutBulkInput_even_vadd]
  have hEquivariant :=
    SmoothAmbientNormalSignLift.deck_sign (period := period)
      (equatorialBandScalarCurrentNormalSignLift period hPeriod field test)
      (2 * winding) (point.fiber.1, point.time)
  rw [pulledBack_normal_sign_trivial, Units.val_one, one_mul] at hEquivariant
  exact hEquivariant

/-- Genuine scalar cutoff current on the cut bulk. -/
def cutBulkScalarCurrent
    (field test : SmoothQuotientField period hPeriod Real) :
    PositiveHemisphereCutBulk period hPeriod → Real :=
  Quotient.lift (cutBulkScalarCurrentCover period hPeriod field test)
    (fun first second hOrbit ↦ by
      change AddAction.orbitRel Int (CutBulkCover period hPeriod)
        first second at hOrbit
      rw [AddAction.orbitRel_apply, AddAction.mem_orbit_iff] at hOrbit
      rcases hOrbit with ⟨winding, hWinding⟩
      rw [← hWinding]
      exact cutBulkScalarCurrentCover_invariant
        period hPeriod field test winding second)

@[simp] theorem cutBulkScalarCurrent_mk
    (field test : SmoothQuotientField period hPeriod Real)
    (point : CutBulkCover period hPeriod) :
    cutBulkScalarCurrent period hPeriod field test
        (mappingTorusMk (cutBulkData period hPeriod) point) =
      cutBulkScalarCurrentCover period hPeriod field test point :=
  rfl

theorem continuous_cutBulkScalarCurrent
    (field test : SmoothQuotientField period hPeriod Real) :
    Continuous (cutBulkScalarCurrent period hPeriod field test) := by
  apply (continuous_cutBulkScalarCurrentCover period hPeriod field test).quotient_lift

/-- Restricting the bulk scalar current to the global cut boundary recovers
the scalar current already descended on that boundary. -/
theorem cutBulkScalarCurrent_cutBoundaryInclusion
    (field test : SmoothQuotientField period hPeriod Real)
    (boundary : CutThroatBoundary period hPeriod) :
    cutBulkScalarCurrent period hPeriod field test
        (cutBoundaryInclusion period hPeriod boundary) =
      cutBoundaryScalarCurrent period hPeriod field test boundary := by
  refine Quotient.inductionOn boundary ?_
  intro point
  rfl

end
end P0EFTJanusMappingTorusCutBulkScalarCurrentDescent4D
end JanusFormal
