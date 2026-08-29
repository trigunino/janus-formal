import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAmbientCanonicalLatitudePinMinusLift4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalNormalLiftContinuityReduction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeScalarNormalCurrent4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionTransportBridge4D

/-!
# Canonical latitude normal: comparison of the two presentations

This gate makes the `T01` comparison map explicit.  Product coordinates on
the cover are first converted back to a cover tangent vector, pushed through
the covering projection, and finally read in a genuine quotient-tangent
trivialization.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLatitudeNormalPresentationComparison4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusMappingTorusIntrinsicCoverLorentzTensor4D
open P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionAlgebraic4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalNormalLiftContinuityReduction4D
open P0EFTJanusMappingTorusCanonicalLatitudeScalarNormalCurrent4D
open P0EFTJanusMappingTorusIntrinsicCanonicalLatitudeNormalImage4D
open P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionTransportBridge4D
open P0EFTJanusMappingTorusAmbientCanonicalLatitudePinMinusLift4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveCover := MappingTorusCover (sphereData period hPeriod)
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)
private abbrev EffectiveThroatCover :=
  MappingTorusCover (throatData period hPeriod)

private abbrev throatProjectionLocalHomeomorph :
    IsLocalHomeomorph
      (mappingTorusMk (throatData period hPeriod)) :=
  (mappingTorusMk_isCoveringMap
    (throatData period hPeriod)).isLocalHomeomorph

private local instance effectiveCoverChartedSpace :
    ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod

private local instance effectiveCoverIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveCover period hPeriod) :=
  reflectedSphereCover_isManifold period hPeriod

private local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

private local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private abbrev QuotientTangentFiber
    (point : EffectiveQuotient period hPeriod) :=
  TangentSpace coverModelWithCorners point

/-- The quotient point below a chosen cover point. -/
def quotientPointOfCover (point : EffectiveCover period hPeriod) :
    EffectiveQuotient period hPeriod :=
  mappingTorusMk (sphereData period hPeriod) point

/-- Explicit change from cover-product coordinates to the coordinates of a
chosen genuine quotient-tangent trivialization. -/
def coverProductToQuotientTangentCoordinates
    (chart : EffectiveQuotient period hPeriod)
    (point : EffectiveCover period hPeriod)
    (coordinate : CoverCoordinates) : CoverCoordinates :=
  ((trivializationAt CoverCoordinates
      (QuotientTangentFiber period hPeriod) chart)
    ⟨quotientPointOfCover period hPeriod point,
      mfderiv coverModelWithCorners coverModelWithCorners
        (mappingTorusMk (sphereData period hPeriod)) point
        ((coverProductDerivativeEquiv period hPeriod point).symm coordinate)⟩).2

/-- The comparison map really reads the pushed-forward cover tangent in the
selected quotient chart. -/
theorem coverProductToQuotientTangentCoordinates_apply
    (chart : EffectiveQuotient period hPeriod)
    (point : EffectiveCover period hPeriod)
    (vector : TangentSpace coverModelWithCorners point) :
    coverProductToQuotientTangentCoordinates period hPeriod chart point
        (coverProductDerivative period hPeriod point vector) =
      ((trivializationAt CoverCoordinates
          (QuotientTangentFiber period hPeriod) chart)
        ⟨quotientPointOfCover period hPeriod point,
          mfderiv coverModelWithCorners coverModelWithCorners
            (mappingTorusMk (sphereData period hPeriod)) point vector⟩).2 := by
  have hVector :
      (coverProductDerivativeEquiv period hPeriod point).symm
          (coverProductDerivative period hPeriod point vector) = vector := by
    rw [← coverProductDerivativeEquiv_toContinuousLinearMap]
    exact (coverProductDerivativeEquiv period hPeriod point).symm_apply_apply vector
  unfold coverProductToQuotientTangentCoordinates
  rw [hVector]

/-- `T01`: the product representative `canonicalLatitudeNormalCoordinates`
is transported to the quotient-atlas presentation by one explicit map. -/
theorem canonicalLatitudeNormal_presentations_compare
    (chart : EffectiveQuotient period hPeriod)
    (anchor : EffectiveThroatCover period hPeriod) :
    coverProductToQuotientTangentCoordinates period hPeriod chart
        (fixedThroatCoverInclusion period hPeriod anchor)
        (canonicalLatitudeNormalCoordinates period hPeriod anchor) =
      ((trivializationAt CoverCoordinates
          (QuotientTangentFiber period hPeriod) chart)
        ⟨quotientPointOfCover period hPeriod
            (fixedThroatCoverInclusion period hPeriod anchor),
          mfderiv coverModelWithCorners coverModelWithCorners
            (mappingTorusMk (sphereData period hPeriod))
            (fixedThroatCoverInclusion period hPeriod anchor)
            (coverLatitudeNormalVector period hPeriod anchor)⟩).2 := by
  exact coverProductToQuotientTangentCoordinates_apply
    period hPeriod chart (fixedThroatCoverInclusion period hPeriod anchor)
      (coverLatitudeNormalVector period hPeriod anchor)

/-- At the throat (`normal = 0`), the intrinsic normal-coordinate
presentation is exactly the transported cover-section presentation. -/
theorem canonicalLatitudeNormalCoordinate_eq_sectionPresentation
    (chart : EffectiveQuotient period hPeriod)
    (base : CanonicalLatitudeBase) :
    canonicalLatitudeNormalCoordinate period hPeriod chart (base, 0) =
      coverProductToQuotientTangentCoordinates period hPeriod chart
        (fixedThroatCoverInclusion period hPeriod
          (canonicalLatitudeAnchor period hPeriod base))
        (canonicalLatitudeSectionNormal period hPeriod
          (canonicalLatitudeAnchor period hPeriod base)
          (canonicalLatitudeThroatMap period hPeriod base)) := by
  let anchor := canonicalLatitudeAnchor period hPeriod base
  have hInverse :
      (throatProjectionLocalHomeomorph period hPeriod).localInverseAt
          anchor (canonicalLatitudeThroatMap period hPeriod base) =
        anchor := by
    unfold canonicalLatitudeThroatMap
    exact (throatProjectionLocalHomeomorph period hPeriod)
      |>.localInverseAt_apply_self
  have hSection :
      canonicalLatitudeSectionNormal period hPeriod anchor
          (canonicalLatitudeThroatMap period hPeriod base) =
        canonicalLatitudeNormalCoordinates period hPeriod anchor := by
    unfold canonicalLatitudeSectionNormal
    rw [hInverse]
  rw [show canonicalLatitudeAnchor period hPeriod base = anchor from rfl,
    hSection, canonicalLatitudeNormal_presentations_compare]
  unfold canonicalLatitudeNormalCoordinate
  change
    ((trivializationAt CoverCoordinates
        (QuotientTangentFiber period hPeriod) chart)
      (canonicalLatitudeNormalLift period hPeriod (base, 0))).2 = _
  apply congrArg (fun tangent =>
    ((trivializationAt CoverCoordinates
      (QuotientTangentFiber period hPeriod) chart) tangent).2)
  have hCoverPair :
      (⟨normalLatitudeCover period hPeriod anchor 0,
          mfderiv 𝓘(Real, Real) coverModelWithCorners
            (normalLatitudeCover period hPeriod anchor) 0 1⟩ :
        TangentBundle coverModelWithCorners
          (EffectiveCover period hPeriod)) =
        ⟨fixedThroatCoverInclusion period hPeriod anchor,
          coverLatitudeNormalVector period hPeriod anchor⟩ := by
    apply Bundle.TotalSpace.ext
    · exact normalLatitudeCover_zero period hPeriod anchor
    · exact
        (coverLatitudeNormalVector_heq_rawDerivative
          period hPeriod anchor).symm
  have hProjected := congrArg
    (tangentMap coverModelWithCorners coverModelWithCorners
      (mappingTorusMk (sphereData period hPeriod))) hCoverPair
  unfold canonicalLatitudeNormalLift quotientPointOfCover
    quotientNormalLatitude
  rw [canonicalLatitudeNormalVector_eq_projectionDerivative]
  simpa only [Prod.fst, Prod.snd, tangentMap] using hProjected

end

end P0EFTJanusMappingTorusCanonicalLatitudeNormalPresentationComparison4D
end JanusFormal
