import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalNormalLiftContinuityReduction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeScalarNormalCurrent4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAmbientCanonicalReferenceOrthogonalCocycle4D

/-!
# Smooth canonical normal frames on the genuine quotient atlas

The analytic latitude tangent is expressed in every genuine tangent
trivialization.  Its intrinsic Lorentz square is one, hence every coordinate
representative is nonzero.  Euclidean normalization and the polynomial
quaternionic frame application are therefore smooth on each chart domain.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLatitudeNormalAtlasFrame4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalNormalLiftContinuityReduction4D
open P0EFTJanusMappingTorusCanonicalLatitudeScalarNormalCurrent4D
open P0EFTJanusMappingTorusAmbientPinMinusProjection4D
open P0EFTJanusMappingTorusAmbientJacobianWindingChartGaugeNoGo4D
open P0EFTJanusMappingTorusAmbientCanonicalReferenceOrthogonalCocycle4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private abbrev QuotientTangentFiber
    (point : EffectiveQuotient period hPeriod) :=
  TangentSpace coverModelWithCorners point

private abbrev tangentTrivialization
    (anchor : EffectiveQuotient period hPeriod) :=
  trivializationAt CoverCoordinates (QuotientTangentFiber period hPeriod) anchor

/-- The canonical normal coordinate never vanishes on a genuine chart
domain. -/
theorem canonicalLatitudeNormalCoordinate_ne_zero
    (anchor : EffectiveQuotient period hPeriod)
    (parameter : CanonicalLatitudeParameter)
    (hParameter : parameter ∈
      canonicalLatitudeNormalCoordinateDomain period hPeriod anchor) :
    canonicalLatitudeNormalCoordinate period hPeriod anchor parameter ≠ 0 := by
  let lift := canonicalLatitudeNormalLift period hPeriod parameter
  let trivialization := tangentTrivialization period hPeriod anchor
  change lift.1 ∈ trivialization.baseSet at hParameter
  have hSource : lift ∈ trivialization.source :=
    trivialization.mem_source.mpr hParameter
  have hVector : lift.2 ≠ 0 := by
    change canonicalLatitudeNormalVector period hPeriod
      parameter.1 parameter.2 ≠ 0
    intro hZero
    have hUnit := intrinsicMetric_canonicalLatitudeNormalVector_self
      period hPeriod parameter.1 parameter.2
    rw [hZero] at hUnit
    simpa using hUnit
  intro hCoordinate
  apply hVector
  change (trivialization lift).2 = 0 at hCoordinate
  let equivalence := trivialization.continuousLinearEquivAt Real lift.1
    (trivialization.mem_source.1 hSource)
  have hApply : equivalence lift.2 = 0 :=
    (trivialization.continuousLinearEquivAt_apply'
      (R := Real) lift hSource).trans hCoordinate
  apply equivalence.injective
  rw [hApply, map_zero]

/-- Smooth normalized local normal coordinates. -/
def canonicalLatitudeNormalizedNormalCoordinate
    (anchor : EffectiveQuotient period hPeriod)
    (parameter : CanonicalLatitudeParameter) : CoverCoordinates :=
  ambientNormalizeNormal
    (canonicalLatitudeNormalCoordinate period hPeriod anchor parameter)

theorem canonicalLatitudeNormalizedNormalCoordinate_contMDiffOn
    (anchor : EffectiveQuotient period hPeriod) :
    ContMDiffOn canonicalLatitudeParameterModelWithCorners
      𝓘(Real, CoverCoordinates) ∞
      (canonicalLatitudeNormalizedNormalCoordinate period hPeriod anchor)
      (canonicalLatitudeNormalCoordinateDomain period hPeriod anchor) := by
  intro parameter hParameter
  exact (ambientNormalizeNormal_contDiffAt
      (canonicalLatitudeNormalCoordinate period hPeriod anchor parameter)
      (canonicalLatitudeNormalCoordinate_ne_zero period hPeriod anchor parameter
        hParameter)).contMDiffAt.comp_contMDiffWithinAt parameter
    (canonicalLatitudeNormalCoordinate_contMDiffOn period hPeriod anchor
      parameter hParameter)

/-- Pointwise application of the canonical normalized quaternionic frame. -/
def canonicalLatitudeQuaternionFrameApply
    (anchor : EffectiveQuotient period hPeriod)
    (vector : CoverCoordinates)
    (parameter : CanonicalLatitudeParameter) : CoverCoordinates :=
  ambientQuaternionFrameApplication
    (canonicalLatitudeNormalizedNormalCoordinate period hPeriod anchor parameter,
      vector)

/-- Every vector component of the canonical quaternionic frame varies
smoothly on each genuine atlas domain. -/
theorem canonicalLatitudeQuaternionFrameApply_contMDiffOn
    (anchor : EffectiveQuotient period hPeriod)
    (vector : CoverCoordinates) :
    ContMDiffOn canonicalLatitudeParameterModelWithCorners
      𝓘(Real, CoverCoordinates) ∞
      (canonicalLatitudeQuaternionFrameApply period hPeriod anchor vector)
      (canonicalLatitudeNormalCoordinateDomain period hPeriod anchor) := by
  intro parameter hParameter
  exact ambientQuaternionFrameApplication_contDiff.contDiffAt.contMDiffAt
    |>.comp_contMDiffWithinAt parameter
      ((canonicalLatitudeNormalizedNormalCoordinate_contMDiffOn
          period hPeriod anchor parameter hParameter).prodMk_space
        contMDiffWithinAt_const)

/-- The actual orthogonal frame represented by the preceding smooth
application. -/
def canonicalLatitudeQuaternionFrame
    (anchor : EffectiveQuotient period hPeriod)
    (parameter : CanonicalLatitudeParameter)
    (hParameter : parameter ∈
      canonicalLatitudeNormalCoordinateDomain period hPeriod anchor) :
    AmbientOrthogonalIsometry :=
  ambientQuaternionFrame
    (canonicalLatitudeNormalizedNormalCoordinate period hPeriod anchor parameter)
    (ambientNormalizeNormal_unit
      (canonicalLatitudeNormalCoordinate period hPeriod anchor parameter)
      (canonicalLatitudeNormalCoordinate_ne_zero period hPeriod anchor parameter
        hParameter))

theorem canonicalLatitudeQuaternionFrame_referenceVector
    (anchor : EffectiveQuotient period hPeriod)
    (parameter : CanonicalLatitudeParameter)
    (hParameter : parameter ∈
      canonicalLatitudeNormalCoordinateDomain period hPeriod anchor) :
    canonicalLatitudeQuaternionFrame period hPeriod anchor parameter hParameter
        ambientPinMinusReferenceVector =
      canonicalLatitudeNormalizedNormalCoordinate period hPeriod anchor parameter := by
  exact ambientQuaternionFrame_apply_referenceVector _ _

/-- The locally normalized Pin-minus winding projects to the corresponding
power of the reflection aligned by the actual atlas frame. -/
theorem canonicalLatitudeAtlasPinProjection_eq_alignedReflection
    (anchor : EffectiveQuotient period hPeriod)
    (parameter : CanonicalLatitudeParameter)
    (hParameter : parameter ∈
      canonicalLatitudeNormalCoordinateDomain period hPeriod anchor)
    (winding : Int) :
    ambientPinMinusProjection
        (ambientNormalizedPinMinusWindingLift
          (canonicalLatitudeNormalCoordinate period hPeriod anchor parameter)
          (canonicalLatitudeNormalCoordinate_ne_zero period hPeriod anchor
            parameter hParameter) winding) =
      (ambientAlignedNormalReflection
        (canonicalLatitudeQuaternionFrame period hPeriod anchor parameter
          hParameter)).toLinearEquiv ^ winding := by
  exact ambientPinMinusProjection_normalizedWindingLift_eq_alignedReflection
    (canonicalLatitudeNormalCoordinate period hPeriod anchor parameter)
    (canonicalLatitudeNormalCoordinate_ne_zero period hPeriod anchor parameter
      hParameter) winding

/-- Exact all-winding gauge law: the smooth atlas frame intertwines the local
normal Pin-minus projection with the canonical reference `O(4)` phase. -/
theorem canonicalLatitudeAtlasPinProjection_intertwines_reference
    (anchor : EffectiveQuotient period hPeriod)
    (parameter : CanonicalLatitudeParameter)
    (hParameter : parameter ∈
      canonicalLatitudeNormalCoordinateDomain period hPeriod anchor)
    (winding : Int) :
    ambientPinMinusProjection
          (ambientNormalizedPinMinusWindingLift
            (canonicalLatitudeNormalCoordinate period hPeriod anchor parameter)
            (canonicalLatitudeNormalCoordinate_ne_zero period hPeriod anchor
              parameter hParameter) winding) *
        (canonicalLatitudeQuaternionFrame period hPeriod anchor parameter
          hParameter).toLinearEquiv =
      (canonicalLatitudeQuaternionFrame period hPeriod anchor parameter
          hParameter).toLinearEquiv *
        (ambientPinMinusReferenceZ4OrthogonalIsometry
          (winding : ZMod 4)).toLinearEquiv := by
  let frame := canonicalLatitudeQuaternionFrame period hPeriod anchor parameter
    hParameter
  have hIntertwine := integerHolonomy_intertwined_of_generator
    (ambientAlignedNormalReflection frame).toLinearEquiv
    ambientPinMinusReferenceOrthogonalIsometry.toLinearEquiv
    frame.toLinearEquiv
    (ambientAlignedNormalReflection_linearEquiv_mul frame) winding
  rw [← canonicalLatitudeAtlasPinProjection_eq_alignedReflection
      period hPeriod anchor parameter hParameter winding,
    ← ambientPinMinusReferenceZ4OrthogonalIsometry_intCast winding] at hIntertwine
  exact hIntertwine

end

end P0EFTJanusMappingTorusCanonicalLatitudeNormalAtlasFrame4D
end JanusFormal
