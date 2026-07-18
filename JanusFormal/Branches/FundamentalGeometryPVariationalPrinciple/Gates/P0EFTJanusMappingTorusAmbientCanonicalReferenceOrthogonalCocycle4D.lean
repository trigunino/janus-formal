import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAmbientCanonicalPinMinusEdgeGauge4D

/-!
# Orthogonal cocycle projected from the canonical ambient Pin-minus lift

The four reference Pin-minus phases project either to the identity or to the
fixed reference reflection.  They therefore define genuine elements of the
ambient Euclidean orthogonal group.  Applied to the true overlap winding,
these elements form a normalized strict `O(4)` Cech cocycle whose underlying
linear maps are exactly the projections of the canonical `Pin⁻(4)` lifts.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusAmbientCanonicalReferenceOrthogonalCocycle4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusNormalPinMinusPrincipalBundle
open P0EFTJanusMappingTorusAmbientTangentOrientationCocycle
open P0EFTJanusMappingTorusAmbientTangentQuadraticReduction
open P0EFTJanusMappingTorusAmbientPinMinusProjection4D
open P0EFTJanusMappingTorusAmbientPinMinusCechExtension4D
open P0EFTJanusMappingTorusAmbientPinMinusReferenceWindingFrontier4D
open P0EFTJanusMappingTorusAmbientCanonicalReferenceWinding4D
open P0EFTJanusMappingTorusAmbientCanonicalReferencePinMinusCech4D
open P0EFTJanusMappingTorusAmbientJacobianWindingChartGaugeNoGo4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev AmbientData := reflectedSphereData period hPeriod
private abbrev AmbientCover := MappingTorusCover (AmbientData period hPeriod)
private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatCover := MappingTorusCover (ThroatData period hPeriod)
private abbrev ThroatBase := MappingTorus (ThroatData period hPeriod)

/-- Identity element of the ambient quadratic isometry type. -/
def ambientIdentityOrthogonalIsometry : AmbientOrthogonalIsometry where
  __ := LinearEquiv.refl Real CoverCoordinates
  map_app' _ := rfl

/-- Orthogonal representative of a reference `ZMod 4` phase.  Even phases
project to the identity and odd phases to the reference reflection. -/
def ambientPinMinusReferenceZ4OrthogonalIsometry
    (phase : ZMod 4) : AmbientOrthogonalIsometry :=
  if phase = 0 ∨ phase = 2 then ambientIdentityOrthogonalIsometry
  else ambientPinMinusReferenceOrthogonalIsometry

/-- Its underlying linear equivalence is exactly the Clifford projection of
the corresponding Pin-minus phase. -/
theorem ambientPinMinusReferenceZ4OrthogonalIsometry_toLinearEquiv
    (phase : ZMod 4) :
    (ambientPinMinusReferenceZ4OrthogonalIsometry phase).toLinearEquiv =
      ambientPinMinusProjection (ambientPinMinusReferenceZ4Character phase) := by
  have hCases : phase.val = 0 ∨ phase.val = 1 ∨
      phase.val = 2 ∨ phase.val = 3 := by
    have hBound := phase.val_lt
    omega
  rcases hCases with hValue | hValue | hValue | hValue
  all_goals
    rw [← ZMod.natCast_zmod_val phase, hValue]
    simp [ambientPinMinusReferenceZ4OrthogonalIsometry,
      ambientIdentityOrthogonalIsometry,
      ambientPinMinusReferenceOrthogonalIsometry,
      ambientPinMinusProjection_referenceGenerator]
    apply LinearEquiv.ext
    intro vector
    rfl

/-- On an integer residue, the reference orthogonal phase is exactly the
integer power of the reference reflection. -/
theorem ambientPinMinusReferenceZ4OrthogonalIsometry_intCast
    (winding : Int) :
    (ambientPinMinusReferenceZ4OrthogonalIsometry
        (winding : ZMod 4)).toLinearEquiv =
      ambientPinMinusReferenceOrthogonalIsometry.toLinearEquiv ^ winding := by
  rw [ambientPinMinusReferenceZ4OrthogonalIsometry_toLinearEquiv,
    ambientPinMinusReferenceZ4Character_intCast, map_zpow,
    ambientPinMinusProjection_referenceGenerator]
  rfl

/-- Canonical orthogonal transition selected by the true ambient winding. -/
def canonicalAmbientReferenceOrthogonalTransition
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel) : AmbientOrthogonalIsometry :=
  ambientPinMinusReferenceZ4OrthogonalIsometry
    (ambientTransitionWinding period hPeriod first second coordinate : ZMod 4)

/-- The canonical orthogonal transition is precisely the projection of the
canonical Pin-minus transition lift. -/
theorem canonicalAmbientReferenceOrthogonalTransition_toLinearEquiv
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel) :
    (canonicalAmbientReferenceOrthogonalTransition period hPeriod first second
      coordinate).toLinearEquiv =
      ambientPinMinusProjection
        (canonicalAmbientReferencePinMinusTransitionLift period hPeriod
          first second coordinate) := by
  exact ambientPinMinusReferenceZ4OrthogonalIsometry_toLinearEquiv _

/-- Normalization on every genuine self-overlap. -/
theorem canonicalAmbientReferenceOrthogonalTransition_normalized
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    [IsTopologicalGroup AmbientCoordinatePinMinusGroup]
    (anchor : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientAtlasTransition period hPeriod anchor anchor).source) :
    canonicalAmbientReferenceOrthogonalTransition period hPeriod anchor anchor
      coordinate = ambientIdentityOrthogonalIsometry := by
  have hLift := canonicalAmbientReferencePinMinusTransitionLift_normalized
    period hPeriod anchor coordinate hCoordinate
  have hLinear :
      (canonicalAmbientReferenceOrthogonalTransition period hPeriod anchor anchor
          coordinate).toLinearEquiv =
        ambientIdentityOrthogonalIsometry.toLinearEquiv := by
    rw [canonicalAmbientReferenceOrthogonalTransition_toLinearEquiv,
      hLift, map_one]
    apply LinearEquiv.ext
    intro vector
    rfl
  apply DFunLike.coe_injective
  funext vector
  exact LinearEquiv.congr_fun hLinear vector

/-- Strict `O(4)` Cech law inherited from the canonical Pin-minus cocycle. -/
theorem canonicalAmbientReferenceOrthogonalTransition_cocycle
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
    (canonicalAmbientReferenceOrthogonalTransition period hPeriod second third
          (ambientAtlasTransition period hPeriod first second coordinate)).toLinearEquiv *
        (canonicalAmbientReferenceOrthogonalTransition period hPeriod first
          second coordinate).toLinearEquiv =
      (canonicalAmbientReferenceOrthogonalTransition period hPeriod first third
        coordinate).toLinearEquiv := by
  have hLift := canonicalAmbientReferencePinMinusTransitionLift_cocycle
    period hPeriod first second third coordinate hFirstSecond hSecondThird
      hFirstThird
  simpa only [map_mul,
    canonicalAmbientReferenceOrthogonalTransition_toLinearEquiv] using
      congrArg ambientPinMinusProjection hLift

/-- On the honest refined throat overlap, the canonical orthogonal transition
is exactly the reference phase selected by the normal winding. -/
theorem canonicalAmbientReferenceOrthogonalTransition_restricts_to_throat
    (first second : ThroatCover period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈
      throatAmbientChartCompatibilityOverlap period hPeriod first second) :
    canonicalAmbientReferenceOrthogonalTransition period hPeriod
        (fixedThroatCoverInclusion period hPeriod first)
        (fixedThroatCoverInclusion period hPeriod second)
        (throatAmbientOverlapCoordinate period hPeriod first base) =
      ambientPinMinusReferenceZ4OrthogonalIsometry
        (localTransitionWinding period hPeriod first second base : ZMod 4) := by
  unfold canonicalAmbientReferenceOrthogonalTransition
  rw [ambientTransitionWinding_throatAmbientOverlapCoordinate
    period hPeriod first second base hBase]

/-- Its underlying map is the exact Clifford projection of the normal phase. -/
theorem canonicalAmbientReferenceOrthogonalTransition_projection_restricts_to_throat
    (first second : ThroatCover period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈
      throatAmbientChartCompatibilityOverlap period hPeriod first second) :
    (canonicalAmbientReferenceOrthogonalTransition period hPeriod
        (fixedThroatCoverInclusion period hPeriod first)
        (fixedThroatCoverInclusion period hPeriod second)
        (throatAmbientOverlapCoordinate period hPeriod first base)).toLinearEquiv =
      ambientPinMinusProjection
        (ambientPinMinusReferenceZ4Character
          (localTransitionWinding period hPeriod first second base : ZMod 4)) := by
  rw [canonicalAmbientReferenceOrthogonalTransition_toLinearEquiv,
    canonicalAmbientReferencePinMinusTransitionLift_restricts_to_throat
      period hPeriod first second base hBase]

/-- The projected orientation on the refined overlap is the normal reduction. -/
theorem canonicalAmbientReferenceOrthogonalTransition_orientation_restricts_to_throat
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    [IsTopologicalGroup AmbientCoordinatePinMinusGroup]
    (first second : ThroatCover period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈
      throatAmbientChartCompatibilityOverlap period hPeriod first second) :
    ambientLinearOrientationParity
        (canonicalAmbientReferenceOrthogonalTransition period hPeriod
          (fixedThroatCoverInclusion period hPeriod first)
          (fixedThroatCoverInclusion period hPeriod second)
          (throatAmbientOverlapCoordinate period hPeriod first base)).toLinearEquiv =
      normalPinMinusOrientationReduction
        (localTransitionWinding period hPeriod first second base : ZMod 4) := by
  rw [canonicalAmbientReferenceOrthogonalTransition_toLinearEquiv,
    canonicalAmbientReferencePinMinusTransitionLift_restricts_to_throat
      period hPeriod first second base hBase]
  exact ambientReferenceCharacterOrientationLaw _

end

end P0EFTJanusMappingTorusAmbientCanonicalReferenceOrthogonalCocycle4D
end JanusFormal
