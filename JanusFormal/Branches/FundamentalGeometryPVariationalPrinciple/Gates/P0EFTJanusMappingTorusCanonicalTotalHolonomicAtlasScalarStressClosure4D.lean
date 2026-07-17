import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalTotalR4BallParametrization4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalHolonomicAtlasCoverReduction4D

/-!
# Unconditional canonical holonomic-atlas scalar-stress closure

The total `R^4` ball parametrization gives a holonomic chart through every
point of the effective quotient.  Taking all such total holonomic patches as
one field-independent atlas produces an actual covering atlas.  The existing
local Noether theorem then promotes local scalar Euler equations on that atlas
to chartwise and quotient-pointwise vanishing of the already formalized local
stress-divergence coordinates.

This is the coordinate-global conclusion.  It does not construct or claim an
additional abstract covariant-derivative field independently of those
chartwise divergence values.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalTotalHolonomicAtlasScalarStressClosure4D

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarJet4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasCoverReduction4D

variable (period : Real) (hPeriod : period ≠ 0)

abbrev Vector4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient :=
  MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Unconditional pointwise chart existence obtained by discharging the
total-ball input of the canonical chart construction. -/
theorem canonicalTotalHolonomicChartThroughEveryPoint :
    CanonicalHolonomicChartThroughEveryPoint period hPeriod :=
  P0EFTJanusMappingTorusCanonicalHolonomicChartBallRealization4D.canonicalHolonomicChartThroughEveryPoint_of_totalR4BallParametrizations
    period hPeriod
    P0EFTJanusMappingTorusCanonicalTotalR4BallParametrization4D.totalR4BallParametrizationsExist

/-- The actual field-independent covering atlas consisting of all genuine
total holonomic patches. -/
def canonicalTotalHolonomicAtlasCover :
    CanonicalHolonomicAtlasCover period hPeriod where
  atlasPatches := Set.univ
  covers := by
    intro point
    rcases canonicalTotalHolonomicChartThroughEveryPoint period hPeriod point with
      ⟨patch, coordinate, hCoordinate⟩
    exact ⟨patch, Set.mem_univ patch, coordinate, hCoordinate⟩

@[simp] theorem canonicalTotalHolonomicAtlasCover_patch_mem
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    patch ∈ (canonicalTotalHolonomicAtlasCover period hPeriod).atlasPatches :=
  Set.mem_univ patch

/-- Explicit coverage theorem for the selected canonical total atlas. -/
theorem canonicalTotalHolonomicAtlasCover_covers
    (point : EffectiveQuotient period hPeriod) :
    ∃ patch ∈ (canonicalTotalHolonomicAtlasCover period hPeriod).atlasPatches,
      ∃ coordinate : Vector4, patch.coordinateMap coordinate = point :=
  (canonicalTotalHolonomicAtlasCover period hPeriod).covers point

/-- The formerly residual atlas-realizability proposition is unconditional.
-/
theorem canonicalHolonomicAtlasCoverRealizable_unconditional :
    CanonicalHolonomicAtlasCoverRealizable period hPeriod :=
  ⟨canonicalTotalHolonomicAtlasCover period hPeriod⟩

/-- Local Euler equations on the canonical total atlas imply stress
conservation in every coordinate of every selected patch by the existing
local Noether identity. -/
theorem canonicalTotalHolonomicAtlas_localScalarStressConserved_of_euler
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (massSquared source : Real)
    (hEuler : HolonomicAtlasLocalScalarEulerEquations period hPeriod metric
      field (canonicalTotalHolonomicAtlasCover period hPeriod)
      massSquared source) :
    HolonomicAtlasLocalScalarStressConserved period hPeriod metric field
      (canonicalTotalHolonomicAtlasCover period hPeriod)
      massSquared source :=
  holonomicAtlasLocalScalarStressConserved_of_euler period hPeriod metric field
    (canonicalTotalHolonomicAtlasCover period hPeriod) massSquared source hEuler

/-- Chartwise conservation and actual atlas coverage give a zero local
stress-divergence representative at every quotient point. -/
theorem canonicalTotalHolonomicAtlas_quotientPointwiseScalarStressConserved_of_euler
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (massSquared source : Real)
    (hEuler : HolonomicAtlasLocalScalarEulerEquations period hPeriod metric
      field (canonicalTotalHolonomicAtlasCover period hPeriod)
      massSquared source) :
    QuotientPointwiseLocalScalarStressConserved period hPeriod metric field
      (canonicalTotalHolonomicAtlasCover period hPeriod)
      massSquared source :=
  quotientPointwiseLocalScalarStressConserved_of_atlas period hPeriod metric
    field (canonicalTotalHolonomicAtlasCover period hPeriod) massSquared source
    (canonicalTotalHolonomicAtlas_localScalarStressConserved_of_euler
      period hPeriod metric field massSquared source hEuler)

/-- Coordinate-global closure: under the atlas-local scalar Euler equations,
both the chartwise and quotient-pointwise stress-divergence statements hold.
No stronger abstract divergence field is asserted. -/
theorem canonicalTotalHolonomicAtlas_scalarStressConservation_closure
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (massSquared source : Real)
    (hEuler : HolonomicAtlasLocalScalarEulerEquations period hPeriod metric
      field (canonicalTotalHolonomicAtlasCover period hPeriod)
      massSquared source) :
    HolonomicAtlasLocalScalarStressConserved period hPeriod metric field
        (canonicalTotalHolonomicAtlasCover period hPeriod)
        massSquared source ∧
      QuotientPointwiseLocalScalarStressConserved period hPeriod metric field
        (canonicalTotalHolonomicAtlasCover period hPeriod)
        massSquared source :=
  ⟨canonicalTotalHolonomicAtlas_localScalarStressConserved_of_euler
      period hPeriod metric field massSquared source hEuler,
    canonicalTotalHolonomicAtlas_quotientPointwiseScalarStressConserved_of_euler
      period hPeriod metric field massSquared source hEuler⟩

end
end P0EFTJanusMappingTorusCanonicalTotalHolonomicAtlasScalarStressClosure4D
end JanusFormal
