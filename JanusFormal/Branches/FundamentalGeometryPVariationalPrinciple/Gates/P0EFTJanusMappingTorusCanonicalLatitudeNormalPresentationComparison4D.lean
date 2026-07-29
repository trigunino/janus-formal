import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAmbientCanonicalLatitudePinMinusLift4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalNormalLiftContinuityReduction4D

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
open P0EFTJanusMappingTorusIntrinsicCanonicalLatitudeNormalImage4D
open P0EFTJanusMappingTorusAmbientCanonicalLatitudePinMinusLift4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveCover := MappingTorusCover (sphereData period hPeriod)
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)
private abbrev EffectiveThroatCover :=
  MappingTorusCover (throatData period hPeriod)

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

end

end P0EFTJanusMappingTorusCanonicalLatitudeNormalPresentationComparison4D
end JanusFormal
