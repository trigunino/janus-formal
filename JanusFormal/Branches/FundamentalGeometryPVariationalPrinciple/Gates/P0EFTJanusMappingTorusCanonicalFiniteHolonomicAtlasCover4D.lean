import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusCompactQuotient
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalTotalR4BallParametrization4D

/-!
# A finite global holonomic atlas on the physical mapping torus

The total-ball construction supplies a genuine smooth holonomic chart through
every quotient point.  Each chart image is open because its coordinate map is
a local diffeomorphism.  Compactness therefore selects finitely many of these
actual charts.  The already constructed genuine coordinate transitions are
smooth local diffeomorphisms at every represented overlap point.

This is finite global coverage and transition regularity.  It does not by
itself provide a partition of unity or cancellation of oriented face fluxes.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalFiniteHolonomicAtlasCover4D

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasCoverReduction4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D
open P0EFTJanusMappingTorusCanonicalTotalR4BallParametrization4D

variable (period : Real) (hPeriod : period ≠ 0)

abbrev Vector4 :=
  P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient :=
  MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

/-- A finite family of genuine total holonomic charts covering every quotient
point by an actual coordinate representative. -/
structure FiniteCanonicalHolonomicAtlas where
  patches : Finset (SmoothHolonomicFrameChart4 period hPeriod)
  covers : ∀ point : EffectiveQuotient period hPeriod,
    ∃ patch ∈ patches, ∃ coordinate : Vector4,
      patch.coordinateMap coordinate = point

/-- Every total holonomic chart has open image. -/
theorem smoothHolonomicFrameChart4_isOpen_range
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    IsOpen (Set.range patch.coordinateMap) :=
  patch.coordinateMap_isLocalDiffeomorph.isOpen_range

/-- Compactness extracts a finite subcover from the unconditional
chart-through-every-point construction. -/
theorem finiteCanonicalHolonomicAtlas_nonempty :
    Nonempty (FiniteCanonicalHolonomicAtlas period hPeriod) := by
  classical
  have hOpen : ∀ patch : SmoothHolonomicFrameChart4 period hPeriod,
      IsOpen (Set.range patch.coordinateMap) :=
    smoothHolonomicFrameChart4_isOpen_range period hPeriod
  have hCover : (Set.univ : Set (EffectiveQuotient period hPeriod)) ⊆
      ⋃ patch : SmoothHolonomicFrameChart4 period hPeriod,
        Set.range patch.coordinateMap := by
    intro point _hPoint
    rcases canonicalHolonomicChartThroughEveryPoint period hPeriod point with
      ⟨patch, coordinate, hCoordinate⟩
    exact Set.mem_iUnion.mpr ⟨patch, ⟨coordinate, hCoordinate⟩⟩
  obtain ⟨patches, hPatches⟩ :=
    (isCompact_univ :
      IsCompact (Set.univ : Set (EffectiveQuotient period hPeriod)))
      |>.elim_finite_subcover
        (fun patch : SmoothHolonomicFrameChart4 period hPeriod =>
          Set.range patch.coordinateMap)
        hOpen hCover
  refine ⟨{ patches := patches, covers := ?_ }⟩
  intro point
  have hPoint := hPatches (Set.mem_univ point)
  rcases Set.mem_iUnion.mp hPoint with ⟨patch, hPoint⟩
  rcases Set.mem_iUnion.mp hPoint with ⟨hPatch, hPoint⟩
  rcases hPoint with ⟨coordinate, hCoordinate⟩
  exact ⟨patch, hPatch, coordinate, hCoordinate⟩

/-- A fixed, field-independent finite holonomic atlas selected from the
compactness theorem. -/
def canonicalFiniteHolonomicAtlas :
    FiniteCanonicalHolonomicAtlas period hPeriod :=
  Classical.choice
    (finiteCanonicalHolonomicAtlas_nonempty period hPeriod)

/-- The selected finite atlas covers the entire physical quotient. -/
theorem canonicalFiniteHolonomicAtlas_covers
    (point : EffectiveQuotient period hPeriod) :
    ∃ patch ∈ (canonicalFiniteHolonomicAtlas period hPeriod).patches,
      ∃ coordinate : Vector4, patch.coordinateMap coordinate = point :=
  (canonicalFiniteHolonomicAtlas period hPeriod).covers point

/-- Transition regularity required on all represented overlaps of the
selected finite atlas. -/
def FiniteCanonicalHolonomicAtlasTransitionsRegular
    (atlas : FiniteCanonicalHolonomicAtlas period hPeriod) : Prop :=
  ∀ firstPatch ∈ atlas.patches, ∀ secondPatch ∈ atlas.patches,
    ∀ (firstCoordinate secondCoordinate : Vector4)
      (samePoint : firstPatch.coordinateMap firstCoordinate =
        secondPatch.coordinateMap secondCoordinate),
      IsLocalDiffeomorphAt (modelWithCornersSelf Real Vector4)
        (modelWithCornersSelf Real Vector4) ∞
        (holonomicCoordinateTransitionAt period hPeriod firstPatch secondPatch
          firstCoordinate secondCoordinate samePoint)
        firstCoordinate

/-- Every transition in the selected finite atlas is the genuine smooth local
diffeomorphism already supplied by the holonomic transition construction. -/
theorem canonicalFiniteHolonomicAtlas_transitionsRegular :
    FiniteCanonicalHolonomicAtlasTransitionsRegular period hPeriod
      (canonicalFiniteHolonomicAtlas period hPeriod) := by
  intro firstPatch _hFirst secondPatch _hSecond firstCoordinate
    secondCoordinate samePoint
  exact holonomicCoordinateTransitionAt_isLocalDiffeomorphAt period hPeriod
    firstPatch secondPatch firstCoordinate secondCoordinate samePoint

/-- A finite atlas can be consumed by APIs expecting the earlier set-valued
atlas interface. -/
def FiniteCanonicalHolonomicAtlas.toAtlasCover
    (atlas : FiniteCanonicalHolonomicAtlas period hPeriod) :
    CanonicalHolonomicAtlasCover period hPeriod where
  atlasPatches := { patch | patch ∈ atlas.patches }
  covers := atlas.covers

/-- Gate marker: finite global coverage and genuine smooth transition maps
are both unconditional.  Integral gluing remains a later gate. -/
theorem mapping_torus_canonical_finite_holonomic_atlas_cover_gate :
    (∀ point : EffectiveQuotient period hPeriod,
        ∃ patch ∈ (canonicalFiniteHolonomicAtlas period hPeriod).patches,
          ∃ coordinate : Vector4,
            patch.coordinateMap coordinate = point) ∧
      FiniteCanonicalHolonomicAtlasTransitionsRegular period hPeriod
        (canonicalFiniteHolonomicAtlas period hPeriod) :=
  ⟨canonicalFiniteHolonomicAtlas_covers period hPeriod,
    canonicalFiniteHolonomicAtlas_transitionsRegular period hPeriod⟩

end
end P0EFTJanusMappingTorusCanonicalFiniteHolonomicAtlasCover4D
end JanusFormal
