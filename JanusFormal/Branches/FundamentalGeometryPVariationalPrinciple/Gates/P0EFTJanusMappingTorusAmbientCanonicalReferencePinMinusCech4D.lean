import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAmbientCanonicalReferenceWinding4D

/-!
# Canonical reference Pin-minus Cech lift of the ambient deck cocycle

The true ambient overlap winding already determines a canonical
`Pin⁻(4)`-valued Cech cocycle through the reference `ZMod 4` character.  This
gate proves its normalization, strict cocycle law and continuity, and its
exact restriction to the normal `Pin⁻(1)` cocycle on the honest refined
throat overlap.  Identifying its orthogonal projection with the selected
smooth `O(4)` reduction remains the separate metric-gauge obligation.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusAmbientCanonicalReferencePinMinusCech4D

set_option autoImplicit false

noncomputable section

open Set Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusNormalPinMinusPrincipalBundle
open P0EFTJanusMappingTorusAmbientTangentOrientationCocycle
open P0EFTJanusMappingTorusAmbientPinMinusProjection4D
open P0EFTJanusMappingTorusAmbientPinMinusCechExtension4D
open P0EFTJanusMappingTorusAmbientPinMinusReferenceWindingFrontier4D
open P0EFTJanusMappingTorusAmbientCanonicalReferenceWinding4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev AmbientData := reflectedSphereData period hPeriod
private abbrev AmbientCover := MappingTorusCover (AmbientData period hPeriod)
private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatCover := MappingTorusCover (ThroatData period hPeriod)
private abbrev ThroatBase := MappingTorus (ThroatData period hPeriod)

/-- Canonical ambient Pin-minus lift selected by the true deck winding. -/
def canonicalAmbientReferencePinMinusTransitionLift
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel) : AmbientCoordinatePinMinusGroup :=
  ambientPinMinusReferenceZ4Character
    (ambientTransitionWinding period hPeriod first second coordinate : ZMod 4)

/-- The canonical lift is normalized on every genuine self-overlap. -/
theorem canonicalAmbientReferencePinMinusTransitionLift_normalized
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    [IsTopologicalGroup AmbientCoordinatePinMinusGroup]
    (anchor : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientAtlasTransition period hPeriod anchor anchor).source) :
    canonicalAmbientReferencePinMinusTransitionLift period hPeriod
        anchor anchor coordinate = 1 := by
  unfold canonicalAmbientReferencePinMinusTransitionLift
  have hWinding := (ambientReferenceWindingCechData period hPeriod).normalized
    anchor coordinate hCoordinate
  change ambientTransitionWinding period hPeriod anchor anchor coordinate = 0
    at hWinding
  rw [hWinding]
  simp

/-- Strict Cech law on every genuine ambient triple overlap. -/
theorem canonicalAmbientReferencePinMinusTransitionLift_cocycle
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    [IsTopologicalGroup AmbientCoordinatePinMinusGroup]
    (first second third : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hFirstSecond : coordinate ∈
      (ambientAtlasTransition period hPeriod first second).source)
    (hSecondThird :
      ambientAtlasTransition period hPeriod first second coordinate ∈
        (ambientAtlasTransition period hPeriod second third).source)
    (hFirstThird : coordinate ∈
      (ambientAtlasTransition period hPeriod first third).source) :
    canonicalAmbientReferencePinMinusTransitionLift period hPeriod
          second third
          (ambientAtlasTransition period hPeriod first second coordinate) *
        canonicalAmbientReferencePinMinusTransitionLift period hPeriod
          first second coordinate =
      canonicalAmbientReferencePinMinusTransitionLift period hPeriod
        first third coordinate := by
  unfold canonicalAmbientReferencePinMinusTransitionLift
  rw [← ambientPinMinusReferenceZ4Character.map_add_eq_mul]
  apply congrArg ambientPinMinusReferenceZ4Character
  have hWinding := (ambientReferenceWindingCechData period hPeriod).cocycle
    first second third coordinate hFirstSecond hSecondThird hFirstThird
  change ambientTransitionWinding period hPeriod second third
        (ambientAtlasTransition period hPeriod first second coordinate) +
      ambientTransitionWinding period hPeriod first second coordinate =
    ambientTransitionWinding period hPeriod first third coordinate at hWinding
  simpa using congrArg (fun value : Int ↦ (value : ZMod 4)) hWinding

/-- The lift is continuous on every real overlap; this follows from local
constancy of the true covering winding. -/
theorem canonicalAmbientReferencePinMinusTransitionLift_continuousOn
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    [IsTopologicalGroup AmbientCoordinatePinMinusGroup]
    (first second : AmbientCover period hPeriod) :
    ContinuousOn
      (canonicalAmbientReferencePinMinusTransitionLift period hPeriod
        first second)
      (ambientAtlasTransition period hPeriod first second).source :=
  (ambientReferenceWindingCechData period hPeriod).transitionCharacter_continuousOn
    first second

/-- On the honest refined throat overlap, the ambient lift is exactly the
already selected normal `ZMod 4` transition. -/
theorem canonicalAmbientReferencePinMinusTransitionLift_restricts_to_throat
    (first second : ThroatCover period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈
      throatAmbientChartCompatibilityOverlap period hPeriod first second) :
    canonicalAmbientReferencePinMinusTransitionLift period hPeriod
        (fixedThroatCoverInclusion period hPeriod first)
        (fixedThroatCoverInclusion period hPeriod second)
        (throatAmbientOverlapCoordinate period hPeriod first base) =
      ambientPinMinusReferenceZ4Character
        (localTransitionWinding period hPeriod first second base : ZMod 4) := by
  unfold canonicalAmbientReferencePinMinusTransitionLift
  rw [ambientTransitionWinding_throatAmbientOverlapCoordinate
    period hPeriod first second base hBase]

/-- Consequently its projected orientation character agrees exactly with the
normal `Pin⁻(1)` orientation reduction on the refined overlap. -/
theorem canonicalAmbientReferencePinMinusTransitionLift_orientation_restricts_to_throat
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    [IsTopologicalGroup AmbientCoordinatePinMinusGroup]
    (first second : ThroatCover period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈
      throatAmbientChartCompatibilityOverlap period hPeriod first second) :
    ambientLinearOrientationParity
        (ambientPinMinusProjection
          (canonicalAmbientReferencePinMinusTransitionLift period hPeriod
            (fixedThroatCoverInclusion period hPeriod first)
            (fixedThroatCoverInclusion period hPeriod second)
            (throatAmbientOverlapCoordinate period hPeriod first base))) =
      normalPinMinusOrientationReduction
        (localTransitionWinding period hPeriod first second base : ZMod 4) := by
  rw [canonicalAmbientReferencePinMinusTransitionLift_restricts_to_throat
    period hPeriod first second base hBase]
  exact ambientReferenceCharacterOrientationLaw _

end

end P0EFTJanusMappingTorusAmbientCanonicalReferencePinMinusCech4D
end JanusFormal
