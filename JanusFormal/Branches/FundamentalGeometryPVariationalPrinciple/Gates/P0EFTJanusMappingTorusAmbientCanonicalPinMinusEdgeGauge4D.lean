import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusAmbientSpinAtlasObstruction
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAmbientCanonicalReferencePinMinusCech4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAmbientJacobianWindingChartGaugeNoGo4D

/-!
# Canonical edge gauge between the ambient O(4) and Pin-minus cocycles

For every supplied orthonormal reduction, the actual reduced transition and
the projection of the canonical `Pin⁻(4)` lift differ by a unique edge gauge.
The gauge satisfies the exact conjugation-twisted Cech law.  Its triviality is
proved equivalent to the remaining reference-winding reduction law.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusAmbientCanonicalPinMinusEdgeGauge4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusAmbientTangentOrientationCocycle
open P0EFTJanusMappingTorusAmbientTangentQuadraticReduction
open P0EFTJanusMappingTorusAmbientSpinAtlasObstruction
open P0EFTJanusMappingTorusAmbientPinMinusProjection4D
open P0EFTJanusMappingTorusAmbientPinMinusReferenceWindingFrontier4D
open P0EFTJanusMappingTorusAmbientCanonicalReferenceWinding4D
open P0EFTJanusMappingTorusAmbientCanonicalReferencePinMinusCech4D
open P0EFTJanusMappingTorusAmbientJacobianWindingChartGaugeNoGo4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev AmbientData := reflectedSphereData period hPeriod
private abbrev AmbientCover := MappingTorusCover (AmbientData period hPeriod)

/-- Unique pointwise edge gauge carrying the reduced `O(4)` transition to the
projection of the canonical Pin-minus lift. -/
def canonicalAmbientPinMinusEdgeGauge
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientAtlasTransition period hPeriod first second).source) :
    CoverCoordinates ≃ₗ[Real] CoverCoordinates :=
  cechEdgeGauge
    (reduction.orthogonalTransition period hPeriod first second coordinate
      hCoordinate).toLinearEquiv
    (ambientPinMinusProjection
      (canonicalAmbientReferencePinMinusTransitionLift period hPeriod
        first second coordinate))

/-- Applying the edge gauge reaches the canonical Pin-minus projection
exactly. -/
theorem actual_mul_canonicalAmbientPinMinusEdgeGauge
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientAtlasTransition period hPeriod first second).source) :
    (reduction.orthogonalTransition period hPeriod first second coordinate
        hCoordinate).toLinearEquiv *
      canonicalAmbientPinMinusEdgeGauge period hPeriod reduction first second
        coordinate hCoordinate =
      ambientPinMinusProjection
        (canonicalAmbientReferencePinMinusTransitionLift period hPeriod
          first second coordinate) :=
  actual_mul_cechEdgeGauge _ _

/-- The canonical edge gauges obey the conjugation-twisted Cech law forced by
the two strict transition cocycles. -/
theorem canonicalAmbientPinMinusEdgeGauge_twisted_cocycle
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    [IsTopologicalGroup AmbientCoordinatePinMinusGroup]
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (first second third : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hFirstSecond : coordinate ∈
      (ambientAtlasTransition period hPeriod first second).source)
    (hSecondThird :
      ambientAtlasTransition period hPeriod first second coordinate ∈
        (ambientAtlasTransition period hPeriod second third).source)
    (hFirstThird : coordinate ∈
      (ambientAtlasTransition period hPeriod first third).source) :
    canonicalAmbientPinMinusEdgeGauge period hPeriod reduction first third
        coordinate hFirstThird =
      (reduction.orthogonalTransition period hPeriod first second coordinate
          hFirstSecond).toLinearEquiv⁻¹ *
        canonicalAmbientPinMinusEdgeGauge period hPeriod reduction second third
          (ambientAtlasTransition period hPeriod first second coordinate)
          hSecondThird *
        (reduction.orthogonalTransition period hPeriod first second coordinate
          hFirstSecond).toLinearEquiv *
        canonicalAmbientPinMinusEdgeGauge period hPeriod reduction first second
          coordinate hFirstSecond := by
  apply cechEdgeGauge_twisted_cocycle
  · exact ambientOrthogonalTransition_cocycle period hPeriod reduction
      first second third coordinate hFirstSecond hSecondThird hFirstThird
  · have hLift :=
      canonicalAmbientReferencePinMinusTransitionLift_cocycle period hPeriod
        first second third coordinate hFirstSecond hSecondThird hFirstThird
    simpa only [map_mul] using congrArg ambientPinMinusProjection hLift

/-- Exact residual proposition: every canonical edge gauge is trivial. -/
def CanonicalAmbientPinMinusEdgeGaugeTrivial
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod) : Prop :=
  ∀ first second coordinate
    (hCoordinate : coordinate ∈
      (ambientAtlasTransition period hPeriod first second).source),
    canonicalAmbientPinMinusEdgeGauge period hPeriod reduction first second
      coordinate hCoordinate = 1

/-- Triviality of the canonical edge gauge is exactly the previously isolated
reference-winding orthogonal reduction law. -/
theorem canonicalAmbientPinMinusEdgeGaugeTrivial_iff_reductionLaw
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    [IsTopologicalGroup AmbientCoordinatePinMinusGroup]
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod) :
    CanonicalAmbientPinMinusEdgeGaugeTrivial period hPeriod reduction ↔
      AmbientReferenceWindingOrthogonalReductionLaw period hPeriod reduction
        (ambientReferenceWindingCechData period hPeriod) := by
  constructor
  · intro hGauge first second coordinate hCoordinate
    have hExact := actual_mul_canonicalAmbientPinMinusEdgeGauge period hPeriod
      reduction first second coordinate hCoordinate
    rw [hGauge first second coordinate hCoordinate, mul_one] at hExact
    exact hExact.symm
  · intro hLaw first second coordinate hCoordinate
    unfold canonicalAmbientPinMinusEdgeGauge cechEdgeGauge
    have hProjection := hLaw first second coordinate hCoordinate
    change ambientPinMinusProjection
        (ambientPinMinusReferenceZ4Character
          (ambientTransitionWinding period hPeriod first second coordinate :
            ZMod 4)) = _ at hProjection
    change (reduction.orthogonalTransition period hPeriod first second
        coordinate hCoordinate).toLinearEquiv⁻¹ *
      ambientPinMinusProjection
        (ambientPinMinusReferenceZ4Character
          (ambientTransitionWinding period hPeriod first second coordinate :
            ZMod 4)) = 1
    rw [hProjection]
    simp

end

end P0EFTJanusMappingTorusAmbientCanonicalPinMinusEdgeGauge4D
end JanusFormal
