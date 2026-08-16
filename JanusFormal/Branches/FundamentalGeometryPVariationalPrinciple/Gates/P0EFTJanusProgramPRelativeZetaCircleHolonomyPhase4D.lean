import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatMellinZetaQuillenAtlas4D

/-!
# Zeta phase monodromy and circle Quillen holonomy

The circle bridge identifies the zeta connection coefficient and its endpoint
clutching with the explicit circle determinant line.  This determines not only
a parallel section but also its exact monodromy.

The endpoint ratio of the complex zeta determinants is the clutching
multiplier.  After dividing by the positive finite-part magnitudes, the
endpoint ratio of the unitary zeta phases is therefore the normalized
clutching multiplier, namely the closed Quillen holonomy.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRelativeZetaCircleHolonomyPhase4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusCircleQuillenMetricFlatConnection
open P0EFTJanusProgramPRelativeHeatFinitePartFamily4D
open P0EFTJanusProgramPRelativeHeatMellinZetaFamily4D
open P0EFTJanusProgramPRelativeHeatMellinZetaQuillenAtlas4D
open P0EFTJanusProgramPRelativeZetaCircleConnectionBridge4D
open P0EFTJanusProgramPRelativeZetaDeterminantConnection4D
open P0EFTJanusProgramPRelativeZetaFinitePartFamily4D

/-- Endpoint ratio of complex determinant coordinates. -/
theorem relativeZetaDeterminant_endpoint_ratio_eq_clutching
    (fold : Fold)
    (family : RelativeHeatMellinZetaFamilyData)
    (bridge : RelativeZetaCircleConnectionBridgeData fold family.toZetaFamily) :
    relativeZetaDeterminantCoordinate family.toZetaFamily 0 /
        relativeZetaDeterminantCoordinate family.toZetaFamily 1 =
      circleDeterminantClutchingMultiplier fold := by
  apply (div_eq_iff
    (relativeZetaDeterminantCoordinate_ne_zero family.toZetaFamily 1)).2
  calc
    relativeZetaDeterminantCoordinate family.toZetaFamily 0 =
        circleLargeGaugeFrameCoordinateTransition fold
          (relativeZetaDeterminantCoordinate family.toZetaFamily 1) :=
      bridge.endpoint_clutching.symm
    _ = relativeZetaDeterminantCoordinate family.toZetaFamily 1 *
        circleDeterminantClutchingMultiplier fold :=
      circleLargeGaugeFrameCoordinateTransition_apply fold _
    _ = circleDeterminantClutchingMultiplier fold *
        relativeZetaDeterminantCoordinate family.toZetaFamily 1 := by
      ac_rfl

/-- Endpoint ratio of determinant magnitudes. -/
theorem relativeZetaDeterminant_endpoint_norm_ratio_eq_clutching_norm
    (fold : Fold)
    (family : RelativeHeatMellinZetaFamilyData)
    (bridge : RelativeZetaCircleConnectionBridgeData fold family.toZetaFamily) :
    ‖relativeZetaDeterminantCoordinate family.toZetaFamily 0‖ /
        ‖relativeZetaDeterminantCoordinate family.toZetaFamily 1‖ =
      ‖circleDeterminantClutchingMultiplier fold‖ := by
  have hNorm := congrArg norm
    (relativeZetaDeterminant_endpoint_ratio_eq_clutching fold family bridge)
  simpa [norm_div] using hNorm

/-- The normalized finite-part zeta phase at parameter zero is the closed
Quillen holonomy times the phase at parameter one. -/
theorem relativeZetaFinitePartPhase_endpoint
    (fold : Fold)
    (family : RelativeHeatMellinZetaFamilyData)
    (bridge : RelativeZetaCircleConnectionBridgeData fold family.toZetaFamily) :
    relativeZetaFinitePartPhase family.toFinitePartComparison 0 =
      circleQuillenClosedHolonomy fold *
        relativeZetaFinitePartPhase family.toFinitePartComparison 1 := by
  let determinant0 :=
    relativeZetaDeterminantCoordinate family.toZetaFamily 0
  let determinant1 :=
    relativeZetaDeterminantCoordinate family.toZetaFamily 1
  let magnitude0 :=
    relativeHeatFinitePartDeterminantFamily family.finitePartFamily 0
  let magnitude1 :=
    relativeHeatFinitePartDeterminantFamily family.finitePartFamily 1
  let clutching := circleDeterminantClutchingMultiplier fold
  let clutchingNorm := ‖clutching‖
  have hEndpoint : determinant0 = determinant1 * clutching := by
    dsimp [determinant0, determinant1, clutching]
    calc
      relativeZetaDeterminantCoordinate family.toZetaFamily 0 =
          circleLargeGaugeFrameCoordinateTransition fold
            (relativeZetaDeterminantCoordinate family.toZetaFamily 1) :=
        bridge.endpoint_clutching.symm
      _ = relativeZetaDeterminantCoordinate family.toZetaFamily 1 *
          circleDeterminantClutchingMultiplier fold :=
        circleLargeGaugeFrameCoordinateTransition_apply fold _
  have hMagnitude : magnitude0 = magnitude1 * clutchingNorm := by
    calc
      magnitude0 = ‖determinant0‖ := by
        dsimp [magnitude0, determinant0]
        exact
          (norm_relativeHeatMellinZetaFamilyDeterminant family 0).symm
      _ = ‖determinant1 * clutching‖ := by rw [hEndpoint]
      _ = ‖determinant1‖ * ‖clutching‖ := norm_mul _ _
      _ = magnitude1 * clutchingNorm := by
        dsimp [magnitude1, determinant1, clutchingNorm]
        rw [norm_relativeHeatMellinZetaFamilyDeterminant family 1]
  have hMagnitude1Real : magnitude1 ≠ 0 := by
    exact ne_of_gt
      (relativeHeatFinitePartDeterminantFamily_pos
        family.finitePartFamily 1)
  have hClutchingNormReal : clutchingNorm ≠ 0 := by
    dsimp [clutchingNorm, clutching]
    exact (circleDeterminantClutchingMultiplier_norm_pos fold).ne'
  have hMagnitude1 : (magnitude1 : Complex) ≠ 0 := by
    exact_mod_cast hMagnitude1Real
  have hClutchingNorm : (clutchingNorm : Complex) ≠ 0 := by
    exact_mod_cast hClutchingNormReal
  change determinant0 / (magnitude0 : Complex) =
    (clutching / (clutchingNorm : Complex)) *
      (determinant1 / (magnitude1 : Complex))
  rw [hEndpoint, hMagnitude]
  field_simp [hMagnitude1, hClutchingNorm]
  ring

/-- Equivalently, the closed circle holonomy is the endpoint ratio of the
unitary zeta phases. -/
theorem circleQuillenClosedHolonomy_eq_zetaPhase_ratio
    (fold : Fold)
    (family : RelativeHeatMellinZetaFamilyData)
    (bridge : RelativeZetaCircleConnectionBridgeData fold family.toZetaFamily) :
    circleQuillenClosedHolonomy fold =
      relativeZetaFinitePartPhase family.toFinitePartComparison 0 /
        relativeZetaFinitePartPhase family.toFinitePartComparison 1 := by
  symm
  apply (div_eq_iff ?_).2
  · exact fun hZero => by
      have hNorm := congrArg norm hZero
      rw [relativeZetaFinitePartPhase_norm_one] at hNorm
      simp at hNorm
  · exact relativeZetaFinitePartPhase_endpoint fold family bridge

/-- Public zeta-phase holonomy checkpoint. -/
theorem relative_zeta_circle_holonomy_phase_gate
    (fold : Fold)
    (family : RelativeHeatMellinZetaFamilyData)
    (bridge : RelativeZetaCircleConnectionBridgeData fold family.toZetaFamily) :
    relativeZetaDeterminantCoordinate family.toZetaFamily 0 /
        relativeZetaDeterminantCoordinate family.toZetaFamily 1 =
        circleDeterminantClutchingMultiplier fold ∧
      relativeZetaFinitePartPhase family.toFinitePartComparison 0 =
        circleQuillenClosedHolonomy fold *
          relativeZetaFinitePartPhase family.toFinitePartComparison 1 ∧
      circleQuillenClosedHolonomy fold =
        relativeZetaFinitePartPhase family.toFinitePartComparison 0 /
          relativeZetaFinitePartPhase family.toFinitePartComparison 1 :=
  ⟨relativeZetaDeterminant_endpoint_ratio_eq_clutching fold family bridge,
    relativeZetaFinitePartPhase_endpoint fold family bridge,
    circleQuillenClosedHolonomy_eq_zetaPhase_ratio fold family bridge⟩

end
end P0EFTJanusProgramPRelativeZetaCircleHolonomyPhase4D
end JanusFormal
