import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D

/-!
# Transition-free reduction of global scalar-stress conservation

Vanishing of a tangent vector is invariant under every frame change.  Hence
the conclusion `div_g T = 0` does not require literal equality of raw
coordinate arrays on overlaps.  It only requires genuine holonomic patches
covering the quotient and the local Euler equation in every selected patch.

This gate isolates the sole remaining geometric realization statement as
`CanonicalHolonomicAtlasCoverRealizable`.  Once such a cover is supplied, all
chartwise and pointwise stress-conservation consequences are unconditional.
No construction of a global component array is claimed.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalHolonomicAtlasCoverReduction4D

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
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D

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

/-- Metric- and field-independent geometric content still missing from the
quotient API: genuine total holonomic patch packages whose images cover the
effective quotient. -/
structure CanonicalHolonomicAtlasCover where
  atlasPatches : Set (SmoothHolonomicFrameChart4 period hPeriod)
  covers : ∀ point : EffectiveQuotient period hPeriod,
    ∃ patch ∈ atlasPatches, ∃ coordinate : Vector4,
      patch.coordinateMap coordinate = point

/-- The unique residual realization proposition.  It contains no metric,
scalar field, overlap-jet equality or field equation. -/
def CanonicalHolonomicAtlasCoverRealizable : Prop :=
  Nonempty (CanonicalHolonomicAtlasCover period hPeriod)

/-- Pointwise form of the sole residual geometric statement.  This is the
smallest project-specific lemma needed from a coordinate-ball construction:
one genuine totalized holonomic chart through each quotient point. -/
def CanonicalHolonomicChartThroughEveryPoint : Prop :=
  ∀ point : EffectiveQuotient period hPeriod,
    ∃ patch : SmoothHolonomicFrameChart4 period hPeriod,
      ∃ coordinate : Vector4, patch.coordinateMap coordinate = point

/-- A covering family is equivalent to the pointwise chart-existence lemma;
no finiteness, overlap or field-dependent data are hidden in the reduction. -/
theorem canonicalHolonomicAtlasCoverRealizable_iff_chartThroughEveryPoint :
    CanonicalHolonomicAtlasCoverRealizable period hPeriod ↔
      CanonicalHolonomicChartThroughEveryPoint period hPeriod := by
  constructor
  · rintro ⟨atlas⟩ point
    rcases atlas.covers point with ⟨patch, _hPatch, coordinate, hCoordinate⟩
    exact ⟨patch, coordinate, hCoordinate⟩
  · intro hCharts
    refine ⟨{ atlasPatches := Set.univ, covers := ?_ }⟩
    intro point
    rcases hCharts point with ⟨patch, coordinate, hCoordinate⟩
    exact ⟨patch, Set.mem_univ patch, coordinate, hCoordinate⟩

/-- The previous, stronger rebased-jet bridge contains the reduced geometric
cover data. -/
def CanonicalHolonomicAtlasStressConservationBridge.toAtlasCover
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (bridge : CanonicalHolonomicAtlasStressConservationBridge
      period hPeriod metric field) :
    CanonicalHolonomicAtlasCover period hPeriod where
  atlasPatches := bridge.atlasPatches
  covers := bridge.covers

/-- Euler equations in every coordinate of every selected covering patch. -/
def HolonomicAtlasLocalScalarEulerEquations
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (atlas : CanonicalHolonomicAtlasCover period hPeriod)
    (massSquared source : Real) : Prop :=
  ∀ patch : SmoothHolonomicFrameChart4 period hPeriod,
    patch ∈ atlas.atlasPatches → ∀ coordinate : Vector4,
      localSmoothScalarEulerResidual period hPeriod metric patch field
        massSquared source coordinate = 0

/-- Stress conservation in every coordinate of every selected covering
patch.  This statement is stronger than conservation in one chosen chart. -/
def HolonomicAtlasLocalScalarStressConserved
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (atlas : CanonicalHolonomicAtlasCover period hPeriod)
    (massSquared source : Real) : Prop :=
  ∀ patch : SmoothHolonomicFrameChart4 period hPeriod,
    patch ∈ atlas.atlasPatches → ∀ coordinate : Vector4,
      localSmoothScalarStressDivergence period hPeriod metric patch field
        massSquared source coordinate = 0

/-- The exact local Noether identity closes conservation on the entire atlas;
no transition-jet hypothesis is used. -/
theorem holonomicAtlasLocalScalarStressConserved_of_euler
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (atlas : CanonicalHolonomicAtlasCover period hPeriod)
    (massSquared source : Real)
    (hEuler : HolonomicAtlasLocalScalarEulerEquations period hPeriod metric
      field atlas massSquared source) :
    HolonomicAtlasLocalScalarStressConserved period hPeriod metric field atlas
      massSquared source := by
  intro patch hPatch
  exact localSmoothScalarStressDivergence_eq_zero_of_euler
    period hPeriod metric patch field massSquared source
      (hEuler patch hPatch)

/-- Coordinate-honest pointwise formulation on the quotient: every point has
a selected holonomic representative at which the realized divergence is
zero. -/
def QuotientPointwiseLocalScalarStressConserved
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (atlas : CanonicalHolonomicAtlasCover period hPeriod)
    (massSquared source : Real) : Prop :=
  ∀ point : EffectiveQuotient period hPeriod,
    ∃ patch ∈ atlas.atlasPatches, ∃ coordinate : Vector4,
      patch.coordinateMap coordinate = point ∧
        localSmoothScalarStressDivergence period hPeriod metric patch field
          massSquared source coordinate = 0

/-- Chartwise conservation plus the covering property gives conservation at
every quotient point. -/
theorem quotientPointwiseLocalScalarStressConserved_of_atlas
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (atlas : CanonicalHolonomicAtlasCover period hPeriod)
    (massSquared source : Real)
    (hConserved : HolonomicAtlasLocalScalarStressConserved period hPeriod
      metric field atlas massSquared source) :
    QuotientPointwiseLocalScalarStressConserved period hPeriod metric field
      atlas massSquared source := by
  intro point
  rcases atlas.covers point with ⟨patch, hPatch, coordinate, hCoordinate⟩
  exact ⟨patch, hPatch, coordinate, hCoordinate,
    hConserved patch hPatch coordinate⟩

/-- Compact closure: a covering holonomic atlas and its local Euler equations
already imply both chartwise and pointwise stress conservation. -/
theorem canonicalHolonomicAtlasCover_scalarStressConservation_closure
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (atlas : CanonicalHolonomicAtlasCover period hPeriod)
    (massSquared source : Real)
    (hEuler : HolonomicAtlasLocalScalarEulerEquations period hPeriod metric
      field atlas massSquared source) :
    HolonomicAtlasLocalScalarStressConserved period hPeriod metric field atlas
        massSquared source ∧
      QuotientPointwiseLocalScalarStressConserved period hPeriod metric field
        atlas massSquared source := by
  let hConserved := holonomicAtlasLocalScalarStressConserved_of_euler
    period hPeriod metric field atlas massSquared source hEuler
  exact ⟨hConserved,
    quotientPointwiseLocalScalarStressConserved_of_atlas period hPeriod metric
      field atlas massSquared source hConserved⟩

/-- Existential form useful to downstream gates: once one covering atlas
supports the local Euler equations, one such atlas supports pointwise
conservation on the quotient. -/
theorem exists_quotientPointwiseLocalScalarStressConserved_of_exists_eulerAtlas
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (field : SmoothScalarField period hPeriod)
    (massSquared source : Real)
    (hAtlas : ∃ atlas : CanonicalHolonomicAtlasCover period hPeriod,
      HolonomicAtlasLocalScalarEulerEquations period hPeriod metric field atlas
        massSquared source) :
    ∃ atlas : CanonicalHolonomicAtlasCover period hPeriod,
      QuotientPointwiseLocalScalarStressConserved period hPeriod metric field
        atlas massSquared source := by
  rcases hAtlas with ⟨atlas, hEuler⟩
  exact ⟨atlas,
    (canonicalHolonomicAtlasCover_scalarStressConservation_closure
      period hPeriod metric field atlas massSquared source hEuler).2⟩

end

end P0EFTJanusMappingTorusCanonicalHolonomicAtlasCoverReduction4D
end JanusFormal
