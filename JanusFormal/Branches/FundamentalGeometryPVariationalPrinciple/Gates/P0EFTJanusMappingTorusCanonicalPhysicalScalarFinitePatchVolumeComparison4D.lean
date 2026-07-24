import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarFinitePatchMeasuredChartCover4D

/-!
# Canonical/Lebesgue comparison on the finite Rellich patches

The explicit measured stereographic charts and the fixed tangent-generator
charts have smooth locally invertible transition maps.  Compactness then
turns both transition directions into uniform Lipschitz bounds.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarFinitePatchVolumeComparison4D

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusCompleteTimeFlow4D
open P0EFTJanusMappingTorusCanonicalLatitudeCoareaClosure4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1IntrinsicPatchCoordinates4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEuclideanRellichCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarStereographicVolumeComparison4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarLocalVolumeTransport4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFinitePatchMeasuredChartCover4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData :=
  reflectedSphereData period hPeriod

private abbrev EffectiveCover :=
  MappingTorusCover (sphereData period hPeriod)

private abbrev EffectiveQuotient :=
  MappingTorus (sphereData period hPeriod)

private abbrev StandardSphere :=
  Metric.sphere (0 : EuclideanR4) 1

private abbrev Patch :=
  FiniteTangentGeneratorPatch period hPeriod

local instance canonicalChartHilbertMeasurableSpace :
    MeasurableSpace CanonicalChartHilbertCoordinates :=
  borel CanonicalChartHilbertCoordinates

local instance canonicalChartHilbertBorelSpace :
    BorelSpace CanonicalChartHilbertCoordinates where
  measurable_eq := rfl

local instance coverCoordinatesVolumeIsAddHaarMeasure :
    (volume : Measure CoverCoordinates).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure _ _

local instance effectiveCoverChartedSpace :
    ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod

local instance effectiveCoverIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveCover period hPeriod) :=
  reflectedSphereCover_isManifold period hPeriod

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) :=
  borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

private def partialDiffeomorphProd
    {E H M E' H' M' F G N F' G' N' : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E] [TopologicalSpace H]
    [TopologicalSpace M] [ChartedSpace H M]
    [NormedAddCommGroup E'] [NormedSpace Real E'] [TopologicalSpace H']
    [TopologicalSpace M'] [ChartedSpace H' M']
    [NormedAddCommGroup F] [NormedSpace Real F] [TopologicalSpace G]
    [TopologicalSpace N] [ChartedSpace G N]
    [NormedAddCommGroup F'] [NormedSpace Real F'] [TopologicalSpace G']
    [TopologicalSpace N'] [ChartedSpace G' N']
    {I : ModelWithCorners Real E H} {I' : ModelWithCorners Real E' H'}
    {J : ModelWithCorners Real F G} {J' : ModelWithCorners Real F' G'}
    {n : ℕ∞ω}
    (Φ : PartialDiffeomorph I I' M M' n)
    (Ψ : PartialDiffeomorph J J' N N' n) :
    PartialDiffeomorph (I.prod J) (I'.prod J')
      (M × N) (M' × N') n where
  __ := Φ.toOpenPartialHomeomorph.prod Ψ.toOpenPartialHomeomorph
  contMDiffOn_toFun := Φ.contMDiffOn.prodMap Ψ.contMDiffOn
  contMDiffOn_invFun := Φ.symm.contMDiffOn.prodMap Ψ.symm.contMDiffOn

private def unitThreeSphereDiffeomorph :
    UnitThreeSphere ≃ₘ^ω⟮(𝓡 3), (𝓡 3)⟯ StandardSphere where
  toEquiv := unitThreeSphereHomeomorph.toEquiv
  contMDiff_toFun :=
    chartedSpacePullback_toFun_contMDiff
      (𝓡 3) ω unitThreeSphereHomeomorph
  contMDiff_invFun :=
    chartedSpacePullback_invFun_contMDiff
      (𝓡 3) ω unitThreeSphereHomeomorph

private def effectiveCoverProductDiffeomorph :
    EffectiveCover period hPeriod ≃ₘ^ω⟮
      coverModelWithCorners, coverModelWithCorners⟯
        UnitThreeSphere × Real where
  toEquiv :=
    (coverHomeomorphProd (sphereData period hPeriod)).toEquiv
  contMDiff_toFun :=
    chartedSpacePullback_toFun_contMDiff
      coverModelWithCorners ω
      (coverHomeomorphProd (sphereData period hPeriod))
  contMDiff_invFun :=
    chartedSpacePullback_invFun_contMDiff
      coverModelWithCorners ω
      (coverHomeomorphProd (sphereData period hPeriod))

private theorem canonicalLorentzFundamentalDomainMap_isLocalDiffeomorph :
    IsLocalDiffeomorph coverModelWithCorners
      coverModelWithCorners ω
      (canonicalLorentzFundamentalDomainMap period hPeriod) := by
  intro parameter
  let sphereProduct :=
    unitThreeSphereDiffeomorph.symm.prodCongr
      (Diffeomorph.refl 𝓘(Real, Real) Real ω)
  have hSphere :=
    sphereProduct.isLocalDiffeomorph parameter
  have hCover :=
    (effectiveCoverProductDiffeomorph period hPeriod).symm
      |>.isLocalDiffeomorph (sphereProduct parameter)
  have hProjection :=
    reflectedSphere_projection_isLocalDiffeomorph
      period hPeriod
      ((effectiveCoverProductDiffeomorph period hPeriod).symm
        (sphereProduct parameter))
  have hFirst :=
    IsLocalDiffeomorphAt.comp
      (I := coverModelWithCorners)
      (J := coverModelWithCorners)
      (K := coverModelWithCorners)
      (M := StandardSphere × Real)
      (N := UnitThreeSphere × Real)
      (P := EffectiveCover period hPeriod)
      (n := ω) hSphere hCover
  have hComposite :=
    IsLocalDiffeomorphAt.comp
      (I := coverModelWithCorners)
      (J := coverModelWithCorners)
      (K := coverModelWithCorners)
      (M := StandardSphere × Real)
      (N := EffectiveCover period hPeriod)
      (P := EffectiveQuotient period hPeriod)
      (n := ω) hFirst hProjection
  convert hComposite using 1
  funext point
  rfl

private def stereographicPartialDiffeomorph
    (pole : StandardSphere) :
    PartialDiffeomorph (𝓡 3) (𝓡 3)
      StandardSphere (EuclideanSpace Real (Fin 3)) ω where
  toPartialEquiv := (stereographic' 3 pole).toPartialEquiv
  open_source := (stereographic' 3 pole).open_source
  open_target := (stereographic' 3 pole).open_target
  contMDiffOn_toFun := by
    have hChartEq :
        chartAt (EuclideanSpace Real (Fin 3)) (-pole) =
          stereographic' 3 pole := by
      change stereographic' 3 (- -pole) = stereographic' 3 pole
      rw [neg_neg]
    have hChartAt :
        chartAt (EuclideanSpace Real (Fin 3)) (-pole) ∈
          IsManifold.maximalAtlas (𝓡 3) ω StandardSphere :=
      IsManifold.chart_mem_maximalAtlas
        (I := 𝓡 3) (-pole)
    rw [hChartEq] at hChartAt
    exact contMDiffOn_of_mem_maximalAtlas hChartAt
  contMDiffOn_invFun := by
    have hChartEq :
        chartAt (EuclideanSpace Real (Fin 3)) (-pole) =
          stereographic' 3 pole := by
      change stereographic' 3 (- -pole) = stereographic' 3 pole
      rw [neg_neg]
    have hChartAt :
        chartAt (EuclideanSpace Real (Fin 3)) (-pole) ∈
          IsManifold.maximalAtlas (𝓡 3) ω StandardSphere :=
      IsManifold.chart_mem_maximalAtlas
        (I := 𝓡 3) (-pole)
    rw [hChartEq] at hChartAt
    exact contMDiffOn_symm_of_mem_maximalAtlas hChartAt

private def stereographicProductPartialDiffeomorph
    (pole : StandardSphere) :
    PartialDiffeomorph coverModelWithCorners
      coverModelWithCorners CoverCoordinates
      (StandardSphere × Real) ω :=
  partialDiffeomorphProd
    (stereographicPartialDiffeomorph pole).symm
    (Diffeomorph.refl 𝓘(Real, Real) Real ω).toPartialDiffeomorph

private theorem stereographicProductMap_isLocalDiffeomorph
    (pole : StandardSphere) :
    IsLocalDiffeomorph coverModelWithCorners
      coverModelWithCorners ω
      (fun coordinate : CoverCoordinates =>
        (stereographicInverseSphere pole coordinate.1,
          coordinate.2)) := by
  intro coordinate
  have hSource :
      coordinate ∈
        (stereographicProductPartialDiffeomorph pole).source := by
    constructor
    · change coordinate.1 ∈
        (stereographicPartialDiffeomorph pole).symm.source
      change coordinate.1 ∈ (stereographic' 3 pole).target
      simp
    · show coordinate.2 ∈
        ((Diffeomorph.refl 𝓘(Real, Real) Real ω)
          |>.toPartialDiffeomorph).source
      change coordinate.2 ∈ (Set.univ : Set Real)
      exact Set.mem_univ _
  have hLocal :=
    (stereographicProductPartialDiffeomorph pole)
      |>.isLocalDiffeomorphAt _ _ _ hSource
  convert hLocal using 1
  funext point
  rfl

/-- The ambient shifted stereographic parametrization is locally an analytic
diffeomorphism at every coordinate. -/
theorem shiftedStereographicPhysicalMapAmbient_isLocalDiffeomorph
    (shift : Real)
    (pole : StandardSphere) :
    IsLocalDiffeomorph coverModelWithCorners
      coverModelWithCorners ω
      (shiftedStereographicPhysicalMapAmbient
        period hPeriod shift pole) := by
  intro coordinate
  let spherePoint : StandardSphere × Real :=
    (stereographicInverseSphere pole coordinate.1, coordinate.2)
  let quotientPoint :=
    canonicalLorentzFundamentalDomainMap
      period hPeriod spherePoint
  have hStereographic :=
    stereographicProductMap_isLocalDiffeomorph
      pole coordinate
  have hFundamental :=
    canonicalLorentzFundamentalDomainMap_isLocalDiffeomorph
      period hPeriod spherePoint
  have hFlow :=
    (effectiveTimeFlowDiffeomorph period hPeriod shift)
      |>.isLocalDiffeomorph quotientPoint
  have hFirst :=
    IsLocalDiffeomorphAt.comp
      (I := coverModelWithCorners)
      (J := coverModelWithCorners)
      (K := coverModelWithCorners)
      (M := CoverCoordinates)
      (N := StandardSphere × Real)
      (P := EffectiveQuotient period hPeriod)
      (n := ω) hStereographic hFundamental
  have hComposite :=
    IsLocalDiffeomorphAt.comp
      (I := coverModelWithCorners)
      (J := coverModelWithCorners)
      (K := coverModelWithCorners)
      (M := CoverCoordinates)
      (N := EffectiveQuotient period hPeriod)
      (P := EffectiveQuotient period hPeriod)
      (n := ω) hFirst hFlow
  convert hComposite using 1
  funext point
  rfl

/-- Fixed patch coordinates, extended to all quotient points by
`extChartAt`, followed by the Hilbert-model identification. -/
def finiteTangentPatchAmbientHilbertCoordinate
    (patch : Patch period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    CanonicalChartHilbertCoordinates :=
  canonicalChartHilbertEquivCoverCoordinates.symm
    (extChartAt coverModelWithCorners patch.1 point)

/-- Transition from an explicit shifted stereographic chart to one fixed
finite tangent-generator chart. -/
def shiftedStereographicToFiniteTangentPatch
    (patch : Patch period hPeriod)
    (shift : Real)
    (pole : StandardSphere)
    (coordinate : CoverCoordinates) :
    CanonicalChartHilbertCoordinates :=
  finiteTangentPatchAmbientHilbertCoordinate
    period hPeriod patch
    (shiftedStereographicPhysicalMapAmbient
      period hPeriod shift pole coordinate)

private def quotientExtChartPartialDiffeomorph
    (anchor : EffectiveQuotient period hPeriod) :
    PartialDiffeomorph coverModelWithCorners
      (modelWithCornersSelf Real CoverCoordinates)
      (EffectiveQuotient period hPeriod) CoverCoordinates ω where
  toPartialEquiv := extChartAt coverModelWithCorners anchor
  open_source :=
    isOpen_extChartAt_source (I := coverModelWithCorners) anchor
  open_target :=
    isOpen_extChartAt_target (I := coverModelWithCorners) anchor
  contMDiffOn_toFun := by
    rw [extChartAt_source]
    exact contMDiffOn_extChartAt
      (I := coverModelWithCorners) (n := ω) (x := anchor)
  contMDiffOn_invFun :=
    contMDiffOn_extChartAt_symm
      (I := coverModelWithCorners) (n := ω) anchor

/-- On the source of the fixed quotient chart, the transition to Hilbert
coordinates is a local analytic diffeomorphism. -/
theorem shiftedStereographicToFiniteTangentPatch_isLocalDiffeomorphAt
    (patch : Patch period hPeriod)
    (shift : Real)
    (pole : StandardSphere)
    (coordinate : CoverCoordinates)
    (hCoordinate :
      shiftedStereographicPhysicalMapAmbient
          period hPeriod shift pole coordinate ∈
        (chartAt CoverModel patch.1).source) :
    IsLocalDiffeomorphAt
        coverModelWithCorners
        (modelWithCornersSelf Real CanonicalChartHilbertCoordinates)
        ω
        (shiftedStereographicToFiniteTangentPatch
          period hPeriod patch shift pole)
        coordinate := by
  have hShift :=
    shiftedStereographicPhysicalMapAmbient_isLocalDiffeomorph
      period hPeriod shift pole coordinate
  have hCoordinate' :
      shiftedStereographicPhysicalMapAmbient
          period hPeriod shift pole coordinate ∈
        (quotientExtChartPartialDiffeomorph
          period hPeriod patch.1).source := by
    change
      shiftedStereographicPhysicalMapAmbient
          period hPeriod shift pole coordinate ∈
        (extChartAt coverModelWithCorners patch.1).source
    rwa [extChartAt_source]
  have hChart :=
    (quotientExtChartPartialDiffeomorph
      period hPeriod patch.1).isLocalDiffeomorphAt
        _ _ _ hCoordinate'
  let linearDiffeomorph :
      CoverCoordinates ≃ₘ^ω⟮
        modelWithCornersSelf Real CoverCoordinates,
        modelWithCornersSelf Real
          CanonicalChartHilbertCoordinates⟯
        CanonicalChartHilbertCoordinates :=
    { toEquiv :=
        canonicalChartHilbertEquivCoverCoordinates.symm.toEquiv
      contMDiff_toFun :=
        canonicalChartHilbertEquivCoverCoordinates.symm.contDiff.contMDiff
      contMDiff_invFun :=
        canonicalChartHilbertEquivCoverCoordinates.contDiff.contMDiff }
  have hLinear :=
    linearDiffeomorph
      |>.isLocalDiffeomorph
        (extChartAt coverModelWithCorners patch.1
          (shiftedStereographicPhysicalMapAmbient
            period hPeriod shift pole coordinate))
  have hFirst :=
    IsLocalDiffeomorphAt.comp
      (I := coverModelWithCorners)
      (J := coverModelWithCorners)
      (K := modelWithCornersSelf Real CoverCoordinates)
      (M := CoverCoordinates)
      (N := EffectiveQuotient period hPeriod)
      (P := CoverCoordinates)
      (n := ω) hShift hChart
  have hComposite :=
    IsLocalDiffeomorphAt.comp
      (I := coverModelWithCorners)
      (J := modelWithCornersSelf Real CoverCoordinates)
      (K := modelWithCornersSelf Real
        CanonicalChartHilbertCoordinates)
      (M := CoverCoordinates)
      (N := CoverCoordinates)
      (P := CanonicalChartHilbertCoordinates)
      (n := ω) hFirst hLinear
  have hComposite' :
      IsLocalDiffeomorphAt
        coverModelWithCorners
        (modelWithCornersSelf Real
          CanonicalChartHilbertCoordinates)
        ω
        (shiftedStereographicToFiniteTangentPatch
          period hPeriod patch shift pole)
        coordinate := by
    convert hComposite using 1
    funext point
    rfl
  exact hComposite'

/-! ## Compact overlap pieces and uniform transition bounds -/

/-- A compact quotient piece pulled back to the ambient product coordinates
of one shifted measured stereographic chart. -/
def shiftedStereographicAmbientPiece
    (shift : Real)
    (pole : StandardSphere)
    (piece : Set (EffectiveQuotient period hPeriod)) :
    Set CoverCoordinates :=
  canonicalInteriorStereographicCoordinateInclusion period ''
    (shiftedCanonicalInteriorStereographicPhysicalMap
      period hPeriod shift pole ⁻¹' piece)

theorem shiftedStereographicAmbientPiece_isCompact
    (shift : Real)
    (pole : StandardSphere)
    {piece : Set (EffectiveQuotient period hPeriod)}
    (hPieceCompact : IsCompact piece)
    (hPieceRange :
      piece ⊆ Set.range
        (shiftedCanonicalInteriorStereographicPhysicalMap
          period hPeriod shift pole)) :
    IsCompact
      (shiftedStereographicAmbientPiece
        period hPeriod shift pole piece) := by
  have hPreimage :
      IsCompact
        (shiftedCanonicalInteriorStereographicPhysicalMap
          period hPeriod shift pole ⁻¹' piece) :=
    (shiftedCanonicalInteriorStereographicPhysicalMap_isOpenEmbedding
      period hPeriod shift pole).isEmbedding.isInducing
        |>.isCompact_preimage' hPieceCompact hPieceRange
  exact hPreimage.image
    (canonicalInteriorStereographicCoordinateInclusion_isOpenEmbedding
      period).continuous

theorem shiftedStereographicPhysicalMapAmbient_image_ambientPiece
    (shift : Real)
    (pole : StandardSphere)
    {piece : Set (EffectiveQuotient period hPeriod)}
    (hPieceRange :
      piece ⊆ Set.range
        (shiftedCanonicalInteriorStereographicPhysicalMap
          period hPeriod shift pole)) :
    shiftedStereographicPhysicalMapAmbient
        period hPeriod shift pole ''
      shiftedStereographicAmbientPiece
        period hPeriod shift pole piece =
      piece := by
  apply Set.Subset.antisymm
  · rintro point ⟨_, ⟨coordinate, hCoordinate, rfl⟩, rfl⟩
    rw [shiftedStereographicPhysicalMapAmbient_agrees]
    exact hCoordinate
  · intro point hPoint
    obtain ⟨coordinate, hCoordinate⟩ :=
      hPieceRange hPoint
    refine
      ⟨canonicalInteriorStereographicCoordinateInclusion
          period coordinate,
        ⟨coordinate, ?_, rfl⟩, ?_⟩
    · simpa [hCoordinate] using hPoint
    · rw [shiftedStereographicPhysicalMapAmbient_agrees]
      exact hCoordinate

/-- The forward transition from stereographic coordinates to fixed Hilbert
coordinates is uniformly Lipschitz on every compact measured-chart piece. -/
theorem exists_shiftedStereographicToFiniteTangentPatch_lipschitzOn
    (patch : Patch period hPeriod)
    (shift : Real)
    (pole : StandardSphere)
    {piece : Set (EffectiveQuotient period hPeriod)}
    (hPieceCompact : IsCompact piece)
    (hPiecePatch :
      piece ⊆ finiteTangentGeneratorClosedPatch
        period hPeriod patch)
    (hPieceRange :
      piece ⊆ Set.range
        (shiftedCanonicalInteriorStereographicPhysicalMap
          period hPeriod shift pole)) :
    ∃ constant : NNReal,
      LipschitzOnWith constant
        (shiftedStereographicToFiniteTangentPatch
          period hPeriod patch shift pole)
        (shiftedStereographicAmbientPiece
          period hPeriod shift pole piece) := by
  apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (shiftedStereographicAmbientPiece_isCompact
      period hPeriod shift pole hPieceCompact hPieceRange)
  intro coordinate hCoordinate
  obtain ⟨source, hSourcePiece, rfl⟩ := hCoordinate
  have hPhysicalPiece :
      shiftedStereographicPhysicalMapAmbient
          period hPeriod shift pole
          (canonicalInteriorStereographicCoordinateInclusion
            period source) ∈ piece := by
    rw [shiftedStereographicPhysicalMapAmbient_agrees]
    exact hSourcePiece
  have hChartSource :
      shiftedStereographicPhysicalMapAmbient
          period hPeriod shift pole
          (canonicalInteriorStereographicCoordinateInclusion
            period source) ∈
        (chartAt CoverModel patch.1).source := by
    rw [← finiteTangentGeneratorOpenPatch_eq_chart_source
      period hPeriod patch]
    exact finiteTangentGeneratorClosedPatch_subset_openPatch
      period hPeriod patch (hPiecePatch hPhysicalPiece)
  have hLocal :=
    shiftedStereographicToFiniteTangentPatch_isLocalDiffeomorphAt
      period hPeriod patch shift pole
      (canonicalInteriorStereographicCoordinateInclusion
        period source) hChartSource
  have hManifold :
      ContMDiffAt coverModelWithCorners
        (modelWithCornersSelf Real
          CanonicalChartHilbertCoordinates)
        1
        (shiftedStereographicToFiniteTangentPatch
          period hPeriod patch shift pole)
        (canonicalInteriorStereographicCoordinateInclusion
          period source) :=
    hLocal.contMDiffAt.of_le (by simp)
  have hSelf :
      ContMDiffAt
        (modelWithCornersSelf Real CoverCoordinates)
        (modelWithCornersSelf Real
          CanonicalChartHilbertCoordinates)
        1
        (shiftedStereographicToFiniteTangentPatch
          period hPeriod patch shift pole)
        (canonicalInteriorStereographicCoordinateInclusion
          period source) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hManifold
  obtain ⟨constant, neighborhood, hNeighborhood, hLipschitz⟩ :=
    hSelf.contDiffAt.exists_lipschitzOnWith
  exact
    ⟨constant, neighborhood,
      mem_nhdsWithin_of_mem_nhds hNeighborhood, hLipschitz⟩

/-- Open ambient source of the measured stereographic chart. -/
def canonicalInteriorStereographicAmbientStrip :
    Set CoverCoordinates :=
  Set.range
    (canonicalInteriorStereographicCoordinateInclusion period)

theorem canonicalInteriorStereographicAmbientStrip_isOpen :
    IsOpen
      (canonicalInteriorStereographicAmbientStrip period) :=
  (canonicalInteriorStereographicCoordinateInclusion_isOpenEmbedding
    period).isOpen_range

theorem shiftedStereographicAmbientPiece_subset_strip
    (shift : Real)
    (pole : StandardSphere)
    (piece : Set (EffectiveQuotient period hPeriod)) :
    shiftedStereographicAmbientPiece
        period hPeriod shift pole piece ⊆
      canonicalInteriorStereographicAmbientStrip period := by
  rintro _ ⟨coordinate, _, rfl⟩
  exact ⟨coordinate, rfl⟩

theorem shiftedStereographicAmbientPiece_mapsTo_piece
    (shift : Real)
    (pole : StandardSphere)
    (piece : Set (EffectiveQuotient period hPeriod)) :
    Set.MapsTo
      (shiftedStereographicPhysicalMapAmbient
        period hPeriod shift pole)
      (shiftedStereographicAmbientPiece
        period hPeriod shift pole piece)
      piece := by
  rintro _ ⟨coordinate, hCoordinate, rfl⟩
  rw [shiftedStereographicPhysicalMapAmbient_agrees]
  exact hCoordinate

theorem shiftedStereographicAmbientPiece_subset_chartSource
    (patch : Patch period hPeriod)
    (shift : Real)
    (pole : StandardSphere)
    {piece : Set (EffectiveQuotient period hPeriod)}
    (hPiecePatch :
      piece ⊆ finiteTangentGeneratorClosedPatch
        period hPeriod patch) :
    shiftedStereographicAmbientPiece
        period hPeriod shift pole piece ⊆
      shiftedStereographicPhysicalMapAmbient
          period hPeriod shift pole ⁻¹'
        (chartAt CoverModel patch.1).source := by
  intro coordinate hCoordinate
  rw [← finiteTangentGeneratorOpenPatch_eq_chart_source
    period hPeriod patch]
  exact finiteTangentGeneratorClosedPatch_subset_openPatch
    period hPeriod patch
    (hPiecePatch
      (shiftedStereographicAmbientPiece_mapsTo_piece
        period hPeriod shift pole piece hCoordinate))

theorem shiftedStereographicPhysicalMapAmbient_injOn_strip
    (shift : Real)
    (pole : StandardSphere) :
    Set.InjOn
      (shiftedStereographicPhysicalMapAmbient
        period hPeriod shift pole)
      (canonicalInteriorStereographicAmbientStrip period) := by
  rintro _ ⟨first, rfl⟩ _ ⟨second, rfl⟩ hEqual
  have hMeasured :
      shiftedCanonicalInteriorStereographicPhysicalMap
          period hPeriod shift pole first =
        shiftedCanonicalInteriorStereographicPhysicalMap
          period hPeriod shift pole second := by
    simpa only [
      shiftedStereographicPhysicalMapAmbient_agrees] using hEqual
  have hSource :=
    (shiftedCanonicalInteriorStereographicPhysicalMap_isOpenEmbedding
      period hPeriod shift pole).injective hMeasured
  exact congrArg
    (canonicalInteriorStereographicCoordinateInclusion period)
    hSource

/-- The transition is injective wherever the measured strip meets the source
of the selected fixed quotient chart. -/
theorem shiftedStereographicToFiniteTangentPatch_injOn
    (patch : Patch period hPeriod)
    (shift : Real)
    (pole : StandardSphere) :
    Set.InjOn
      (shiftedStereographicToFiniteTangentPatch
        period hPeriod patch shift pole)
      (canonicalInteriorStereographicAmbientStrip period ∩
        shiftedStereographicPhysicalMapAmbient
          period hPeriod shift pole ⁻¹'
            (chartAt CoverModel patch.1).source) := by
  intro first hFirst second hSecond hEqual
  have hChartEqual :
      extChartAt coverModelWithCorners patch.1
          (shiftedStereographicPhysicalMapAmbient
            period hPeriod shift pole first) =
        extChartAt coverModelWithCorners patch.1
          (shiftedStereographicPhysicalMapAmbient
            period hPeriod shift pole second) := by
    apply canonicalChartHilbertEquivCoverCoordinates.symm.injective
    simpa [shiftedStereographicToFiniteTangentPatch,
      finiteTangentPatchAmbientHilbertCoordinate] using hEqual
  have hFirstSource :
      shiftedStereographicPhysicalMapAmbient
          period hPeriod shift pole first ∈
        (extChartAt coverModelWithCorners patch.1).source := by
    rw [extChartAt_source]
    exact hFirst.2
  have hSecondSource :
      shiftedStereographicPhysicalMapAmbient
          period hPeriod shift pole second ∈
        (extChartAt coverModelWithCorners patch.1).source := by
    rw [extChartAt_source]
    exact hSecond.2
  have hPhysicalEqual :=
    (extChartAt coverModelWithCorners patch.1).injOn
      hFirstSource hSecondSource hChartEqual
  exact
    shiftedStereographicPhysicalMapAmbient_injOn_strip
      period hPeriod shift pole
      hFirst.1 hSecond.1 hPhysicalEqual

/-- Chosen inverse of the transition on one compact overlap image.  Its
off-image value is irrelevant. -/
def finiteTangentPatchToShiftedStereographic
    (patch : Patch period hPeriod)
    (shift : Real)
    (pole : StandardSphere)
    (piece : Set (EffectiveQuotient period hPeriod))
    (coordinate : CanonicalChartHilbertCoordinates) :
    CoverCoordinates := by
  classical
  exact
    if hCoordinate :
        coordinate ∈
          shiftedStereographicToFiniteTangentPatch
              period hPeriod patch shift pole ''
            shiftedStereographicAmbientPiece
              period hPeriod shift pole piece
    then Classical.choose hCoordinate
    else 0

theorem finiteTangentPatchToShiftedStereographic_mem
    (patch : Patch period hPeriod)
    (shift : Real)
    (pole : StandardSphere)
    {piece : Set (EffectiveQuotient period hPeriod)}
    {coordinate : CanonicalChartHilbertCoordinates}
    (hCoordinate :
      coordinate ∈
        shiftedStereographicToFiniteTangentPatch
            period hPeriod patch shift pole ''
          shiftedStereographicAmbientPiece
            period hPeriod shift pole piece) :
    finiteTangentPatchToShiftedStereographic
        period hPeriod patch shift pole piece coordinate ∈
      shiftedStereographicAmbientPiece
        period hPeriod shift pole piece := by
  classical
  rw [finiteTangentPatchToShiftedStereographic,
    dif_pos hCoordinate]
  exact (Classical.choose_spec hCoordinate).1

theorem shiftedStereographicToFiniteTangentPatch_inverse
    (patch : Patch period hPeriod)
    (shift : Real)
    (pole : StandardSphere)
    {piece : Set (EffectiveQuotient period hPeriod)}
    {coordinate : CanonicalChartHilbertCoordinates}
    (hCoordinate :
      coordinate ∈
        shiftedStereographicToFiniteTangentPatch
            period hPeriod patch shift pole ''
          shiftedStereographicAmbientPiece
            period hPeriod shift pole piece) :
    shiftedStereographicToFiniteTangentPatch
        period hPeriod patch shift pole
        (finiteTangentPatchToShiftedStereographic
        period hPeriod patch shift pole piece coordinate) =
      coordinate := by
  classical
  rw [finiteTangentPatchToShiftedStereographic,
    dif_pos hCoordinate]
  exact (Classical.choose_spec hCoordinate).2

theorem shiftedStereographicToFiniteTangentPatch_injOn_ambientPiece
    (patch : Patch period hPeriod)
    (shift : Real)
    (pole : StandardSphere)
    {piece : Set (EffectiveQuotient period hPeriod)}
    (hPiecePatch :
      piece ⊆ finiteTangentGeneratorClosedPatch
        period hPeriod patch) :
    Set.InjOn
      (shiftedStereographicToFiniteTangentPatch
        period hPeriod patch shift pole)
      (shiftedStereographicAmbientPiece
        period hPeriod shift pole piece) := by
  apply
    (shiftedStereographicToFiniteTangentPatch_injOn
      period hPeriod patch shift pole).mono
  intro coordinate hCoordinate
  exact
    ⟨shiftedStereographicAmbientPiece_subset_strip
        period hPeriod shift pole piece hCoordinate,
      shiftedStereographicAmbientPiece_subset_chartSource
        period hPeriod patch shift pole hPiecePatch hCoordinate⟩

theorem finiteTangentPatchToShiftedStereographic_transition
    (patch : Patch period hPeriod)
    (shift : Real)
    (pole : StandardSphere)
    {piece : Set (EffectiveQuotient period hPeriod)}
    (hPiecePatch :
      piece ⊆ finiteTangentGeneratorClosedPatch
        period hPeriod patch)
    {coordinate : CoverCoordinates}
    (hCoordinate :
      coordinate ∈ shiftedStereographicAmbientPiece
        period hPeriod shift pole piece) :
    finiteTangentPatchToShiftedStereographic
        period hPeriod patch shift pole piece
        (shiftedStereographicToFiniteTangentPatch
          period hPeriod patch shift pole coordinate) =
      coordinate := by
  apply
    shiftedStereographicToFiniteTangentPatch_injOn_ambientPiece
      period hPeriod patch shift pole hPiecePatch
  · exact finiteTangentPatchToShiftedStereographic_mem
      period hPeriod patch shift pole
      ⟨coordinate, hCoordinate, rfl⟩
  · exact hCoordinate
  · exact shiftedStereographicToFiniteTangentPatch_inverse
      period hPeriod patch shift pole
      ⟨coordinate, hCoordinate, rfl⟩

/-- The inverse transition is uniformly Lipschitz on the compact image of
every measured-chart piece. -/
theorem exists_finiteTangentPatchToShiftedStereographic_lipschitzOn
    (patch : Patch period hPeriod)
    (shift : Real)
    (pole : StandardSphere)
    {piece : Set (EffectiveQuotient period hPeriod)}
    (hPieceCompact : IsCompact piece)
    (hPiecePatch :
      piece ⊆ finiteTangentGeneratorClosedPatch
        period hPeriod patch)
    (hPieceRange :
      piece ⊆ Set.range
        (shiftedCanonicalInteriorStereographicPhysicalMap
          period hPeriod shift pole)) :
    ∃ constant : NNReal,
      LipschitzOnWith constant
        (finiteTangentPatchToShiftedStereographic
          period hPeriod patch shift pole piece)
        (shiftedStereographicToFiniteTangentPatch
            period hPeriod patch shift pole ''
          shiftedStereographicAmbientPiece
            period hPeriod shift pole piece) := by
  let ambientPiece :=
    shiftedStereographicAmbientPiece
      period hPeriod shift pole piece
  let transition :=
    shiftedStereographicToFiniteTangentPatch
      period hPeriod patch shift pole
  let transitionImage :=
    transition '' ambientPiece
  have hAmbientCompact : IsCompact ambientPiece :=
    shiftedStereographicAmbientPiece_isCompact
      period hPeriod shift pole hPieceCompact hPieceRange
  obtain ⟨forwardConstant, hForward⟩ :=
    exists_shiftedStereographicToFiniteTangentPatch_lipschitzOn
      period hPeriod patch shift pole
      hPieceCompact hPiecePatch hPieceRange
  have hImageCompact : IsCompact transitionImage :=
    hAmbientCompact.image_of_continuousOn hForward.continuousOn
  apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    hImageCompact
  intro imageCoordinate hImageCoordinate
  obtain ⟨source, hSourcePiece, rfl⟩ := hImageCoordinate
  have hChartSource :
      shiftedStereographicPhysicalMapAmbient
          period hPeriod shift pole source ∈
        (chartAt CoverModel patch.1).source :=
    shiftedStereographicAmbientPiece_subset_chartSource
      period hPeriod patch shift pole hPiecePatch hSourcePiece
  have hLocal :=
    shiftedStereographicToFiniteTangentPatch_isLocalDiffeomorphAt
      period hPeriod patch shift pole source hChartSource
  let localInverse := hLocal.localInverse
  have hInverseManifold :
      ContMDiffAt
        (modelWithCornersSelf Real
          CanonicalChartHilbertCoordinates)
        coverModelWithCorners
        1 localInverse (transition source) := by
    exact hLocal.localInverse_contMDiffAt.of_le (by simp)
  have hInverseSelf :
      ContMDiffAt
        (modelWithCornersSelf Real
          CanonicalChartHilbertCoordinates)
        (modelWithCornersSelf Real CoverCoordinates)
        1 localInverse (transition source) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hInverseManifold
  have hInverseValue :
      localInverse (transition source) = source := by
    exact hLocal.localInverse_left_inv
      hLocal.localInverse_mem_target
  obtain ⟨constant, neighborhood, hNeighborhood, hLipschitz⟩ :=
    hInverseSelf.contDiffAt.exists_lipschitzOnWith
  have hInverseSource :
      localInverse.source ∈ 𝓝 (transition source) :=
    localInverse.open_source.mem_nhds
      hLocal.localInverse_mem_source
  have hSourceStrip :
      source ∈ canonicalInteriorStereographicAmbientStrip period :=
    shiftedStereographicAmbientPiece_subset_strip
      period hPeriod shift pole piece hSourcePiece
  have hInverseStrip :
      localInverse ⁻¹'
          canonicalInteriorStereographicAmbientStrip period ∈
        𝓝 (transition source) := by
    apply hInverseSelf.contDiffAt.continuousAt.preimage_mem_nhds
    exact
      (canonicalInteriorStereographicAmbientStrip_isOpen period).mem_nhds
        (by rwa [hInverseValue])
  have hPhysicalContinuous :
      ContinuousAt
        (shiftedStereographicPhysicalMapAmbient
          period hPeriod shift pole ∘ localInverse)
        (transition source) :=
    (shiftedStereographicPhysicalMapAmbient_contMDiff
      period hPeriod shift pole).continuous.continuousAt.comp
        hInverseSelf.contDiffAt.continuousAt
  have hInverseChart :
      (shiftedStereographicPhysicalMapAmbient
          period hPeriod shift pole ∘ localInverse) ⁻¹'
          (chartAt CoverModel patch.1).source ∈
        𝓝 (transition source) := by
    apply hPhysicalContinuous.preimage_mem_nhds
    exact
      (chartAt CoverModel patch.1).open_source.mem_nhds
        (by simpa [Function.comp_def, hInverseValue] using hChartSource)
  let localSet : Set CanonicalChartHilbertCoordinates :=
    neighborhood ∩
      (localInverse.source ∩
        (localInverse ⁻¹'
          canonicalInteriorStereographicAmbientStrip period ∩
        (shiftedStereographicPhysicalMapAmbient
            period hPeriod shift pole ∘ localInverse) ⁻¹'
          (chartAt CoverModel patch.1).source))
  have hLocalSet :
      localSet ∈ 𝓝 (transition source) := by
    dsimp [localSet]
    exact Filter.inter_mem hNeighborhood
      (Filter.inter_mem hInverseSource
        (Filter.inter_mem hInverseStrip hInverseChart))
  refine
    ⟨constant, localSet ∩ transitionImage,
      Filter.inter_mem
        (mem_nhdsWithin_of_mem_nhds hLocalSet)
        self_mem_nhdsWithin, ?_⟩
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro first hFirst second hSecond
  have firstLocal := hFirst.1
  have firstImage := hFirst.2
  have secondLocal := hSecond.1
  have secondImage := hSecond.2
  have hFirstInverse :
      finiteTangentPatchToShiftedStereographic
          period hPeriod patch shift pole piece first =
        localInverse first := by
    apply shiftedStereographicToFiniteTangentPatch_injOn
      period hPeriod patch shift pole
    · exact
        ⟨shiftedStereographicAmbientPiece_subset_strip
            period hPeriod shift pole piece
            (finiteTangentPatchToShiftedStereographic_mem
              period hPeriod patch shift pole firstImage),
          shiftedStereographicAmbientPiece_subset_chartSource
            period hPeriod patch shift pole hPiecePatch
            (finiteTangentPatchToShiftedStereographic_mem
              period hPeriod patch shift pole firstImage)⟩
    · exact ⟨firstLocal.2.2.1, firstLocal.2.2.2⟩
    · calc
        transition
            (finiteTangentPatchToShiftedStereographic
              period hPeriod patch shift pole piece first) =
          first :=
            shiftedStereographicToFiniteTangentPatch_inverse
              period hPeriod patch shift pole firstImage
        _ = transition (localInverse first) :=
          (hLocal.localInverse_right_inv firstLocal.2.1).symm
  have hSecondInverse :
      finiteTangentPatchToShiftedStereographic
          period hPeriod patch shift pole piece second =
        localInverse second := by
    apply shiftedStereographicToFiniteTangentPatch_injOn
      period hPeriod patch shift pole
    · exact
        ⟨shiftedStereographicAmbientPiece_subset_strip
            period hPeriod shift pole piece
            (finiteTangentPatchToShiftedStereographic_mem
              period hPeriod patch shift pole secondImage),
          shiftedStereographicAmbientPiece_subset_chartSource
            period hPeriod patch shift pole hPiecePatch
            (finiteTangentPatchToShiftedStereographic_mem
              period hPeriod patch shift pole secondImage)⟩
    · exact ⟨secondLocal.2.2.1, secondLocal.2.2.2⟩
    · calc
        transition
            (finiteTangentPatchToShiftedStereographic
              period hPeriod patch shift pole piece second) =
          second :=
            shiftedStereographicToFiniteTangentPatch_inverse
              period hPeriod patch shift pole secondImage
        _ = transition (localInverse second) :=
          (hLocal.localInverse_right_inv secondLocal.2.1).symm
  simpa [hFirstInverse, hSecondInverse] using
    hLipschitz.dist_le_mul
      first firstLocal.1 second secondLocal.1

/-! ## Exact local measure transport -/

theorem finiteTangentPatchAmbientHilbertCoordinate_continuousOn
    (patch : Patch period hPeriod) :
    ContinuousOn
      (finiteTangentPatchAmbientHilbertCoordinate
        period hPeriod patch)
      (finiteTangentGeneratorClosedPatch
        period hPeriod patch) := by
  apply
    canonicalChartHilbertEquivCoverCoordinates.symm.continuous
      |>.comp_continuousOn
  apply (continuousOn_extChartAt patch.1).mono
  intro point hPoint
  rw [extChartAt_source,
    ← finiteTangentGeneratorOpenPatch_eq_chart_source
      period hPeriod patch]
  exact finiteTangentGeneratorClosedPatch_subset_openPatch
    period hPeriod patch hPoint

theorem finiteTangentPatchAmbientHilbertCoordinate_injOn
    (patch : Patch period hPeriod) :
    Set.InjOn
      (finiteTangentPatchAmbientHilbertCoordinate
        period hPeriod patch)
      (finiteTangentGeneratorClosedPatch
        period hPeriod patch) := by
  intro first hFirst second hSecond hEqual
  apply (extChartAt coverModelWithCorners patch.1).injOn
  · rw [extChartAt_source,
      ← finiteTangentGeneratorOpenPatch_eq_chart_source
        period hPeriod patch]
    exact finiteTangentGeneratorClosedPatch_subset_openPatch
      period hPeriod patch hFirst
  · rw [extChartAt_source,
      ← finiteTangentGeneratorOpenPatch_eq_chart_source
        period hPeriod patch]
    exact finiteTangentGeneratorClosedPatch_subset_openPatch
      period hPeriod patch hSecond
  · exact canonicalChartHilbertEquivCoverCoordinates.symm.injective
      (by simpa [finiteTangentPatchAmbientHilbertCoordinate] using hEqual)

theorem finiteTangentPatchCanonicalCoordinateMeasure_eq_map_ambient
    (patch : Patch period hPeriod) :
    finiteTangentPatchCanonicalCoordinateMeasure
        period hPeriod patch =
      Measure.map
        (finiteTangentPatchAmbientHilbertCoordinate
          period hPeriod patch)
        ((intrinsicCanonicalLorentzVolumeMeasure
          period hPeriod).restrict
            (finiteTangentGeneratorClosedPatch
              period hPeriod patch)) := by
  let sourceMeasure :=
    finiteTangentPatchCanonicalSourceMeasure
      period hPeriod patch
  have hAmbientAE :
      AEMeasurable
        (finiteTangentPatchAmbientHilbertCoordinate
          period hPeriod patch)
        (Measure.map
          (Subtype.val :
            FiniteTangentPatchDomain period hPeriod patch →
              EffectiveQuotient period hPeriod)
          sourceMeasure) := by
    rw [finiteTangentPatchCanonicalSourceMeasure_map_subtype]
    exact
      (finiteTangentPatchAmbientHilbertCoordinate_continuousOn
        period hPeriod patch).aemeasurable
          (finiteTangentGeneratorClosedPatch_isClosed
            period hPeriod patch).measurableSet
  have hMapMap :=
    hAmbientAE.map_map_of_aemeasurable
      (measurable_subtype_coe.aemeasurable :
        AEMeasurable
          (Subtype.val :
            FiniteTangentPatchDomain period hPeriod patch →
              EffectiveQuotient period hPeriod)
          sourceMeasure)
  calc
    finiteTangentPatchCanonicalCoordinateMeasure
        period hPeriod patch =
      Measure.map
        (finiteTangentPatchHilbertCoordinate
          period hPeriod patch) sourceMeasure := rfl
    _ = Measure.map
        (finiteTangentPatchAmbientHilbertCoordinate
            period hPeriod patch ∘ Subtype.val)
        sourceMeasure := by
      congr 1
    _ = Measure.map
        (finiteTangentPatchAmbientHilbertCoordinate
          period hPeriod patch)
        (Measure.map
          (Subtype.val :
            FiniteTangentPatchDomain period hPeriod patch →
              EffectiveQuotient period hPeriod)
          sourceMeasure) := hMapMap.symm
    _ = Measure.map
        (finiteTangentPatchAmbientHilbertCoordinate
          period hPeriod patch)
        ((intrinsicCanonicalLorentzVolumeMeasure
          period hPeriod).restrict
            (finiteTangentGeneratorClosedPatch
              period hPeriod patch)) := by
      rw [finiteTangentPatchCanonicalSourceMeasure_map_subtype]

theorem finiteTangentPatchCanonicalCoordinateMeasure_restrict_piece
    (patch : Patch period hPeriod)
    {piece : Set (EffectiveQuotient period hPeriod)}
    (hPieceCompact : IsCompact piece)
    (hPiecePatch :
      piece ⊆ finiteTangentGeneratorClosedPatch
        period hPeriod patch) :
    (finiteTangentPatchCanonicalCoordinateMeasure
        period hPeriod patch).restrict
          (finiteTangentPatchAmbientHilbertCoordinate
            period hPeriod patch '' piece) =
      Measure.map
        (finiteTangentPatchAmbientHilbertCoordinate
          period hPeriod patch)
        ((intrinsicCanonicalLorentzVolumeMeasure
          period hPeriod).restrict piece) := by
  let closedPatch :=
    finiteTangentGeneratorClosedPatch
      period hPeriod patch
  let coordinateMap :=
    finiteTangentPatchAmbientHilbertCoordinate
      period hPeriod patch
  have hPieceMeasurable : MeasurableSet piece :=
    hPieceCompact.isClosed.measurableSet
  have hImageCompact : IsCompact (coordinateMap '' piece) :=
    hPieceCompact.image_of_continuousOn
      ((finiteTangentPatchAmbientHilbertCoordinate_continuousOn
        period hPeriod patch).mono hPiecePatch)
  have hAmbientAE :
      AEMeasurable coordinateMap
        ((intrinsicCanonicalLorentzVolumeMeasure
          period hPeriod).restrict closedPatch) :=
    (finiteTangentPatchAmbientHilbertCoordinate_continuousOn
      period hPeriod patch).aemeasurable
        (finiteTangentGeneratorClosedPatch_isClosed
          period hPeriod patch).measurableSet
  rw [finiteTangentPatchCanonicalCoordinateMeasure_eq_map_ambient]
  rw [Measure.restrict_map_of_aemeasurable
    hAmbientAE hImageCompact.isClosed.measurableSet]
  congr 1
  rw [Measure.restrict_restrict₀
    (hAmbientAE.nullMeasurable hImageCompact.isClosed.measurableSet)]
  congr 1
  apply Set.Subset.antisymm
  · rintro point ⟨⟨imagePoint, hImagePoint, hEqual⟩, hPointPatch⟩
    have hPointEqual : point = imagePoint :=
      finiteTangentPatchAmbientHilbertCoordinate_injOn
        period hPeriod patch hPointPatch
          (hPiecePatch hImagePoint) hEqual.symm
    rwa [hPointEqual]
  · intro point hPoint
    exact ⟨⟨point, hPoint, rfl⟩, hPiecePatch hPoint⟩

theorem shiftedTransition_image_eq_patchCoordinate_image
    (patch : Patch period hPeriod)
    (shift : Real)
    (pole : StandardSphere)
    {piece : Set (EffectiveQuotient period hPeriod)}
    (hPieceRange :
      piece ⊆ Set.range
        (shiftedCanonicalInteriorStereographicPhysicalMap
          period hPeriod shift pole)) :
    shiftedStereographicToFiniteTangentPatch
          period hPeriod patch shift pole ''
        shiftedStereographicAmbientPiece
          period hPeriod shift pole piece =
      finiteTangentPatchAmbientHilbertCoordinate
          period hPeriod patch ''
        piece := by
  calc
    shiftedStereographicToFiniteTangentPatch
          period hPeriod patch shift pole ''
        shiftedStereographicAmbientPiece
          period hPeriod shift pole piece =
      finiteTangentPatchAmbientHilbertCoordinate
          period hPeriod patch ''
        (shiftedStereographicPhysicalMapAmbient
            period hPeriod shift pole ''
          shiftedStereographicAmbientPiece
            period hPeriod shift pole piece) := by
      rw [Set.image_image]
      rfl
    _ = finiteTangentPatchAmbientHilbertCoordinate
          period hPeriod patch '' piece := by
      rw [shiftedStereographicPhysicalMapAmbient_image_ambientPiece
        period hPeriod shift pole hPieceRange]

theorem map_stereographicInclusion_restrict_piece
    (shift : Real)
    (pole : StandardSphere)
    (piece : Set (EffectiveQuotient period hPeriod)) :
    Measure.map
        (canonicalInteriorStereographicCoordinateInclusion period)
        ((canonicalInteriorStereographicMeasure
          period pole).restrict
            (shiftedCanonicalInteriorStereographicPhysicalMap
              period hPeriod shift pole ⁻¹' piece)) =
      (stereographicProductCoordinateMeasure pole).restrict
        (shiftedStereographicAmbientPiece
          period hPeriod shift pole piece) := by
  have hRestricted :=
    (canonicalInteriorStereographicCoordinateInclusion_measurePreserving
      period pole).restrict_image_emb
        (canonicalInteriorStereographicCoordinateInclusion_isOpenEmbedding
          period).measurableEmbedding
        (shiftedCanonicalInteriorStereographicPhysicalMap
          period hPeriod shift pole ⁻¹' piece)
  calc
    Measure.map
        (canonicalInteriorStereographicCoordinateInclusion period)
        ((canonicalInteriorStereographicMeasure
          period pole).restrict
            (shiftedCanonicalInteriorStereographicPhysicalMap
              period hPeriod shift pole ⁻¹' piece)) =
      ((stereographicProductCoordinateMeasure pole).restrict
        (Set.range
          (canonicalInteriorStereographicCoordinateInclusion
            period))).restrict
        (shiftedStereographicAmbientPiece
          period hPeriod shift pole piece) := by
      simpa [shiftedStereographicAmbientPiece] using hRestricted.map_eq
    _ = (stereographicProductCoordinateMeasure pole).restrict
        (shiftedStereographicAmbientPiece
          period hPeriod shift pole piece) :=
      Measure.restrict_restrict_of_subset
        (shiftedStereographicAmbientPiece_subset_strip
          period hPeriod shift pole piece)

theorem map_shiftedStereographic_restrict_piece
    (shift : Real)
    (pole : StandardSphere)
    {piece : Set (EffectiveQuotient period hPeriod)}
    (hPieceRange :
      piece ⊆ Set.range
        (shiftedCanonicalInteriorStereographicPhysicalMap
          period hPeriod shift pole)) :
    Measure.map
        (shiftedCanonicalInteriorStereographicPhysicalMap
          period hPeriod shift pole)
        ((canonicalInteriorStereographicMeasure
          period pole).restrict
            (shiftedCanonicalInteriorStereographicPhysicalMap
              period hPeriod shift pole ⁻¹' piece)) =
      (intrinsicCanonicalLorentzVolumeMeasure
        period hPeriod).restrict piece := by
  have hRestricted :=
    (shiftedCanonicalInteriorStereographicPhysicalMap_measurePreserving
      period hPeriod shift pole).restrict_image_emb
        (shiftedCanonicalInteriorStereographicPhysicalMap_isOpenEmbedding
          period hPeriod shift pole).measurableEmbedding
        (shiftedCanonicalInteriorStereographicPhysicalMap
          period hPeriod shift pole ⁻¹' piece)
  have hImage :
      shiftedCanonicalInteriorStereographicPhysicalMap
          period hPeriod shift pole ''
        (shiftedCanonicalInteriorStereographicPhysicalMap
          period hPeriod shift pole ⁻¹' piece) =
      piece :=
    Set.image_preimage_eq_of_subset hPieceRange
  calc
    Measure.map
        (shiftedCanonicalInteriorStereographicPhysicalMap
          period hPeriod shift pole)
        ((canonicalInteriorStereographicMeasure
          period pole).restrict
            (shiftedCanonicalInteriorStereographicPhysicalMap
              period hPeriod shift pole ⁻¹' piece)) =
      ((intrinsicCanonicalLorentzVolumeMeasure
        period hPeriod).restrict
          (Set.range
            (shiftedCanonicalInteriorStereographicPhysicalMap
              period hPeriod shift pole))).restrict piece := by
      simpa [hImage] using hRestricted.map_eq
    _ = (intrinsicCanonicalLorentzVolumeMeasure
        period hPeriod).restrict piece :=
      Measure.restrict_restrict_of_subset hPieceRange

/-- Exact pushforward of the local stereographic product measure through the
transition to the fixed Hilbert coordinates. -/
theorem map_shiftedTransition_surfaceMeasure
    (patch : Patch period hPeriod)
    (shift : Real)
    (pole : StandardSphere)
    {piece : Set (EffectiveQuotient period hPeriod)}
    (hPieceCompact : IsCompact piece)
    (hPiecePatch :
      piece ⊆ finiteTangentGeneratorClosedPatch
        period hPeriod patch)
    (hPieceRange :
      piece ⊆ Set.range
        (shiftedCanonicalInteriorStereographicPhysicalMap
          period hPeriod shift pole)) :
    Measure.map
        (shiftedStereographicToFiniteTangentPatch
          period hPeriod patch shift pole)
        ((stereographicProductCoordinateMeasure pole).restrict
          (shiftedStereographicAmbientPiece
            period hPeriod shift pole piece)) =
      (finiteTangentPatchCanonicalCoordinateMeasure
        period hPeriod patch).restrict
          (shiftedStereographicToFiniteTangentPatch
              period hPeriod patch shift pole ''
            shiftedStereographicAmbientPiece
              period hPeriod shift pole piece) := by
  let sourceMeasure :=
    (canonicalInteriorStereographicMeasure
      period pole).restrict
        (shiftedCanonicalInteriorStereographicPhysicalMap
          period hPeriod shift pole ⁻¹' piece)
  let ambientPiece :=
    shiftedStereographicAmbientPiece
      period hPeriod shift pole piece
  let transition :=
    shiftedStereographicToFiniteTangentPatch
      period hPeriod patch shift pole
  let coordinateMap :=
    finiteTangentPatchAmbientHilbertCoordinate
      period hPeriod patch
  have hInclusionMap :
      Measure.map
          (canonicalInteriorStereographicCoordinateInclusion period)
          sourceMeasure =
        (stereographicProductCoordinateMeasure pole).restrict
          ambientPiece :=
    map_stereographicInclusion_restrict_piece
      period hPeriod shift pole piece
  have hPhysicalMap :
      Measure.map
          (shiftedCanonicalInteriorStereographicPhysicalMap
            period hPeriod shift pole)
          sourceMeasure =
        (intrinsicCanonicalLorentzVolumeMeasure
          period hPeriod).restrict piece :=
    map_shiftedStereographic_restrict_piece
      period hPeriod shift pole hPieceRange
  obtain ⟨forwardConstant, hForward⟩ :=
    exists_shiftedStereographicToFiniteTangentPatch_lipschitzOn
      period hPeriod patch shift pole
      hPieceCompact hPiecePatch hPieceRange
  have hAmbientMeasurable : MeasurableSet ambientPiece :=
    (shiftedStereographicAmbientPiece_isCompact
      period hPeriod shift pole hPieceCompact hPieceRange)
      |>.isClosed.measurableSet
  have hTransitionAE :
      AEMeasurable transition
        ((stereographicProductCoordinateMeasure pole).restrict
          ambientPiece) :=
    hForward.continuousOn.aemeasurable hAmbientMeasurable
  have hTransitionAE' :
      AEMeasurable transition
        (Measure.map
          (canonicalInteriorStereographicCoordinateInclusion period)
          sourceMeasure) := by
    rwa [hInclusionMap]
  have hCoordinateAE :
      AEMeasurable coordinateMap
        ((intrinsicCanonicalLorentzVolumeMeasure
          period hPeriod).restrict piece) :=
    ((finiteTangentPatchAmbientHilbertCoordinate_continuousOn
      period hPeriod patch).mono hPiecePatch).aemeasurable
        hPieceCompact.isClosed.measurableSet
  have hCoordinateAE' :
      AEMeasurable coordinateMap
        (Measure.map
          (shiftedCanonicalInteriorStereographicPhysicalMap
            period hPeriod shift pole)
          sourceMeasure) := by
    rwa [hPhysicalMap]
  have hInclusionMapMap :=
    hTransitionAE'.map_map_of_aemeasurable
      ((canonicalInteriorStereographicCoordinateInclusion_isOpenEmbedding
        period).continuous.measurable.aemeasurable.restrict)
  have hPhysicalMapMap :=
    hCoordinateAE'.map_map_of_aemeasurable
      ((shiftedCanonicalInteriorStereographicPhysicalMap_isOpenEmbedding
        period hPeriod shift pole).continuous.measurable.aemeasurable.restrict)
  calc
    Measure.map transition
        ((stereographicProductCoordinateMeasure pole).restrict
          ambientPiece) =
      Measure.map transition
        (Measure.map
          (canonicalInteriorStereographicCoordinateInclusion period)
          sourceMeasure) := by rw [hInclusionMap]
    _ = Measure.map
        (transition ∘
          canonicalInteriorStereographicCoordinateInclusion period)
        sourceMeasure := hInclusionMapMap
    _ = Measure.map
        (coordinateMap ∘
          shiftedCanonicalInteriorStereographicPhysicalMap
            period hPeriod shift pole)
        sourceMeasure := by
      congr 1
    _ = Measure.map coordinateMap
        (Measure.map
          (shiftedCanonicalInteriorStereographicPhysicalMap
            period hPeriod shift pole)
          sourceMeasure) := hPhysicalMapMap.symm
    _ = Measure.map coordinateMap
        ((intrinsicCanonicalLorentzVolumeMeasure
          period hPeriod).restrict piece) := by rw [hPhysicalMap]
    _ = (finiteTangentPatchCanonicalCoordinateMeasure
        period hPeriod patch).restrict
          (coordinateMap '' piece) :=
      (finiteTangentPatchCanonicalCoordinateMeasure_restrict_piece
        period hPeriod patch hPieceCompact hPiecePatch).symm
    _ = (finiteTangentPatchCanonicalCoordinateMeasure
        period hPeriod patch).restrict
          (transition '' ambientPiece) := by
      rw [shiftedTransition_image_eq_patchCoordinate_image
        period hPeriod patch shift pole hPieceRange]

/-! ## Quantitative comparison on one compact overlap -/

structure FiniteTangentPatchPieceCanonicalLebesgueComparison
    (patch : Patch period hPeriod)
    (shift : Real)
    (pole : StandardSphere)
    (piece : Set (EffectiveQuotient period hPeriod)) where
  lebesgueBound : ENNReal
  lebesgueBound_ne_top : lebesgueBound ≠ ⊤
  lebesgue_le_canonical :
    (volume : Measure CanonicalChartHilbertCoordinates).restrict
        (shiftedStereographicToFiniteTangentPatch
            period hPeriod patch shift pole ''
          shiftedStereographicAmbientPiece
            period hPeriod shift pole piece) ≤
      lebesgueBound •
        (finiteTangentPatchCanonicalCoordinateMeasure
          period hPeriod patch).restrict
            (shiftedStereographicToFiniteTangentPatch
                period hPeriod patch shift pole ''
              shiftedStereographicAmbientPiece
                period hPeriod shift pole piece)
  canonicalBound : ENNReal
  canonicalBound_ne_top : canonicalBound ≠ ⊤
  canonical_le_lebesgue :
    (finiteTangentPatchCanonicalCoordinateMeasure
        period hPeriod patch).restrict
          (shiftedStereographicToFiniteTangentPatch
              period hPeriod patch shift pole ''
            shiftedStereographicAmbientPiece
              period hPeriod shift pole piece) ≤
      canonicalBound •
        (volume : Measure CanonicalChartHilbertCoordinates).restrict
          (shiftedStereographicToFiniteTangentPatch
              period hPeriod patch shift pole ''
            shiftedStereographicAmbientPiece
              period hPeriod shift pole piece)

/-- Every compact overlap piece has finite two-sided canonical/Lebesgue
comparison constants derived from its explicit smooth transition. -/
theorem finiteTangentPatchPieceCanonicalLebesgueComparison_nonempty
    (patch : Patch period hPeriod)
    (shift : Real)
    (pole : StandardSphere)
    {piece : Set (EffectiveQuotient period hPeriod)}
    (hPieceCompact : IsCompact piece)
    (hPiecePatch :
      piece ⊆ finiteTangentGeneratorClosedPatch
        period hPeriod patch)
    (hPieceRange :
      piece ⊆ Set.range
        (shiftedCanonicalInteriorStereographicPhysicalMap
          period hPeriod shift pole)) :
    Nonempty
      (FiniteTangentPatchPieceCanonicalLebesgueComparison
        period hPeriod patch shift pole piece) := by
  classical
  let sourceSupport :=
    shiftedStereographicAmbientPiece
      period hPeriod shift pole piece
  let transition :=
    shiftedStereographicToFiniteTangentPatch
      period hPeriod patch shift pole
  let inverse :=
    finiteTangentPatchToShiftedStereographic
      period hPeriod patch shift pole piece
  let targetSupport := transition '' sourceSupport
  let sourceLebesgue :=
    (volume : Measure CoverCoordinates).restrict sourceSupport
  let sourceSurface :=
    (stereographicProductCoordinateMeasure pole).restrict sourceSupport
  let targetLebesgue :=
    (volume : Measure CanonicalChartHilbertCoordinates).restrict
      targetSupport
  let targetCanonical :=
    (finiteTangentPatchCanonicalCoordinateMeasure
      period hPeriod patch).restrict targetSupport
  have hSourceCompact : IsCompact sourceSupport :=
    shiftedStereographicAmbientPiece_isCompact
      period hPeriod shift pole hPieceCompact hPieceRange
  have hSourceMeasurable : MeasurableSet sourceSupport :=
    hSourceCompact.isClosed.measurableSet
  obtain ⟨forwardConstant, hForwardLipschitz⟩ :=
    exists_shiftedStereographicToFiniteTangentPatch_lipschitzOn
      period hPeriod patch shift pole
      hPieceCompact hPiecePatch hPieceRange
  obtain ⟨inverseConstant, hInverseLipschitz⟩ :=
    exists_finiteTangentPatchToShiftedStereographic_lipschitzOn
      period hPeriod patch shift pole
      hPieceCompact hPiecePatch hPieceRange
  have hTargetCompact : IsCompact targetSupport :=
    hSourceCompact.image_of_continuousOn
      hForwardLipschitz.continuousOn
  have hTargetMeasurable : MeasurableSet targetSupport :=
    hTargetCompact.isClosed.measurableSet
  obtain ⟨forwardBound, hForwardBound, hForwardVolumes⟩ :=
    exists_volume_image_le_of_lipschitzOn
      (Source := CoverCoordinates)
      (Target := CanonicalChartHilbertCoordinates)
      (by simp [CoverCoordinates])
      (by simp [CanonicalChartHilbertCoordinates])
      hForwardLipschitz
  obtain ⟨inverseBound, hInverseBound, hInverseVolumes⟩ :=
    exists_volume_image_le_of_lipschitzOn
      (Source := CanonicalChartHilbertCoordinates)
      (Target := CoverCoordinates)
      (by simp [CanonicalChartHilbertCoordinates])
      (by simp [CoverCoordinates])
      hInverseLipschitz
  have hTransitionAELebesgue :
      AEMeasurable transition sourceLebesgue :=
    hForwardLipschitz.continuousOn.aemeasurable hSourceMeasurable
  have hTransitionAESurface :
      AEMeasurable transition sourceSurface :=
    hForwardLipschitz.continuousOn.aemeasurable hSourceMeasurable
  have hSurfaceTransport :
      Measure.map transition sourceSurface = targetCanonical :=
    map_shiftedTransition_surfaceMeasure
      period hPeriod patch shift pole
      hPieceCompact hPiecePatch hPieceRange
  let sourceComparison :=
    compactStereographicProductLebesgueComparison
      pole hSourceCompact
  have hForwardImage (subset : Set CanonicalChartHilbertCoordinates) :
      transition '' (transition ⁻¹' subset ∩ sourceSupport) =
        subset ∩ targetSupport := by
    ext coordinate
    constructor
    · rintro ⟨source, ⟨hSourceSubset, hSourceSupport⟩, rfl⟩
      exact ⟨hSourceSubset, ⟨source, hSourceSupport, rfl⟩⟩
    · rintro ⟨hCoordinateSubset, source, hSourceSupport, rfl⟩
      exact
        ⟨source, ⟨hCoordinateSubset, hSourceSupport⟩, rfl⟩
  have hInverseImage (subset : Set CanonicalChartHilbertCoordinates) :
      inverse '' (subset ∩ targetSupport) =
        transition ⁻¹' subset ∩ sourceSupport := by
    ext coordinate
    constructor
    · rintro ⟨imageCoordinate,
        ⟨hImageSubset, source, hSourceSupport, rfl⟩, rfl⟩
      have hInverse :
          inverse (transition source) = source := by
        simpa [inverse, transition] using
          (finiteTangentPatchToShiftedStereographic_transition
            period hPeriod patch shift pole hPiecePatch hSourceSupport)
      rw [hInverse]
      exact ⟨hImageSubset, hSourceSupport⟩
    · rintro ⟨hCoordinateSubset, hCoordinateSupport⟩
      refine
        ⟨transition coordinate,
          ⟨hCoordinateSubset,
            ⟨coordinate, hCoordinateSupport, rfl⟩⟩, ?_⟩
      simpa [inverse, transition] using
        (finiteTangentPatchToShiftedStereographic_transition
          period hPeriod patch shift pole
          hPiecePatch hCoordinateSupport)
  have hTargetLebesgue_le_push :
      targetLebesgue ≤
        forwardBound • Measure.map transition sourceLebesgue := by
    apply Measure.le_iff.2
    intro subset hSubset
    rw [Measure.smul_apply,
      Measure.map_apply_of_aemeasurable
        hTransitionAELebesgue hSubset,
      smul_eq_mul]
    dsimp only [targetLebesgue, sourceLebesgue]
    rw [Measure.restrict_apply hSubset,
      Measure.restrict_apply₀
      (hTransitionAELebesgue.nullMeasurable hSubset)]
    have hVolumes :=
      hForwardVolumes
        (transition ⁻¹' subset ∩ sourceSupport)
        Set.inter_subset_right
    rwa [hForwardImage subset] at hVolumes
  have hPush_le_targetLebesgue :
      Measure.map transition sourceLebesgue ≤
        inverseBound • targetLebesgue := by
    apply Measure.le_iff.2
    intro subset hSubset
    rw [Measure.map_apply_of_aemeasurable
        hTransitionAELebesgue hSubset,
      Measure.smul_apply, smul_eq_mul]
    dsimp only [targetLebesgue, sourceLebesgue]
    rw [Measure.restrict_apply₀
        (hTransitionAELebesgue.nullMeasurable hSubset),
      Measure.restrict_apply hSubset]
    have hVolumes :=
      hInverseVolumes (subset ∩ targetSupport)
        Set.inter_subset_right
    rwa [hInverseImage subset] at hVolumes
  have hPushLebesgue_le_canonical :
      Measure.map transition sourceLebesgue ≤
        sourceComparison.lebesgueBound • targetCanonical := by
    rw [← hSurfaceTransport]
    apply Measure.le_iff.2
    intro subset hSubset
    rw [Measure.map_apply_of_aemeasurable
        hTransitionAELebesgue hSubset,
      Measure.smul_apply,
      Measure.map_apply_of_aemeasurable
        hTransitionAESurface hSubset]
    exact sourceComparison.lebesgue_le_surface
      (transition ⁻¹' subset)
  have hCanonical_le_pushLebesgue :
      targetCanonical ≤
        sourceComparison.surfaceBound •
          Measure.map transition sourceLebesgue := by
    rw [← hSurfaceTransport]
    apply Measure.le_iff.2
    intro subset hSubset
    rw [Measure.map_apply_of_aemeasurable
        hTransitionAESurface hSubset,
      Measure.smul_apply,
      Measure.map_apply_of_aemeasurable
        hTransitionAELebesgue hSubset]
    exact sourceComparison.surface_le_lebesgue
      (transition ⁻¹' subset)
  refine ⟨{
      lebesgueBound :=
        forwardBound * sourceComparison.lebesgueBound
      lebesgueBound_ne_top :=
        ENNReal.mul_ne_top hForwardBound
          sourceComparison.lebesgueBound_ne_top
      lebesgue_le_canonical := ?_
      canonicalBound := sourceComparison.surfaceBound * inverseBound
      canonicalBound_ne_top :=
        ENNReal.mul_ne_top
          sourceComparison.surfaceBound_ne_top hInverseBound
      canonical_le_lebesgue := ?_
    }⟩
  · intro subset
    rw [Measure.smul_apply]
    calc
      targetLebesgue subset ≤
          forwardBound *
            Measure.map transition sourceLebesgue subset :=
        hTargetLebesgue_le_push subset
      _ ≤ forwardBound *
          (sourceComparison.lebesgueBound *
            targetCanonical subset) :=
        mul_le_mul_left'
          (hPushLebesgue_le_canonical subset) forwardBound
      _ = (forwardBound * sourceComparison.lebesgueBound) *
          targetCanonical subset := by ac_rfl
  · intro subset
    rw [Measure.smul_apply]
    calc
      targetCanonical subset ≤
          sourceComparison.surfaceBound *
            Measure.map transition sourceLebesgue subset :=
        hCanonical_le_pushLebesgue subset
      _ ≤ sourceComparison.surfaceBound *
          (inverseBound * targetLebesgue subset) :=
        mul_le_mul_left'
          (hPush_le_targetLebesgue subset)
          sourceComparison.surfaceBound
      _ = (sourceComparison.surfaceBound * inverseBound) *
          targetLebesgue subset := by ac_rfl

/-- Chosen quantitative comparison certificate on one compact overlap. -/
def finiteTangentPatchPieceCanonicalLebesgueComparison
    (patch : Patch period hPeriod)
    (shift : Real)
    (pole : StandardSphere)
    {piece : Set (EffectiveQuotient period hPeriod)}
    (hPieceCompact : IsCompact piece)
    (hPiecePatch :
      piece ⊆ finiteTangentGeneratorClosedPatch
        period hPeriod patch)
    (hPieceRange :
      piece ⊆ Set.range
        (shiftedCanonicalInteriorStereographicPhysicalMap
          period hPeriod shift pole)) :
    FiniteTangentPatchPieceCanonicalLebesgueComparison
      period hPeriod patch shift pole piece :=
  Classical.choice
    (finiteTangentPatchPieceCanonicalLebesgueComparison_nonempty
      period hPeriod patch shift pole
      hPieceCompact hPiecePatch hPieceRange)

/-! ## Finite aggregation on one tangent-generator patch -/

theorem finiteTangentPatchHilbertSupport_eq_image_ambient
    (patch : Patch period hPeriod) :
    finiteTangentPatchHilbertSupport period hPeriod patch =
      finiteTangentPatchAmbientHilbertCoordinate
          period hPeriod patch ''
        finiteTangentGeneratorClosedPatch
          period hPeriod patch := by
  rw [finiteTangentPatchHilbertSupport,
    finiteTangentPatchCoverSupport,
    coverSupportInCanonicalChartHilbert,
    Set.image_image]
  rfl

private theorem measuredChartCover_piece_subset_patch
    (patch : Patch period hPeriod)
    (cover : FiniteTangentPatchMeasuredChartCover
      period hPeriod patch)
    {chart : Real × StandardSphere}
    (hChart : chart ∈ cover.charts) :
    cover.piece chart ⊆
      finiteTangentGeneratorClosedPatch
        period hPeriod patch := by
  rw [cover.covers]
  intro point hPoint
  exact Set.mem_iUnion.2
    ⟨chart, Set.mem_iUnion.2 ⟨hChart, hPoint⟩⟩

/-- The finitely many compact measured overlaps give the full two-sided
canonical/Lebesgue comparison on one actual tangent-generator patch. -/
theorem finiteTangentPatchCanonicalLebesgueComparison_nonempty
    (patch : Patch period hPeriod) :
    Nonempty
      (FiniteTangentPatchCanonicalLebesgueComparison
        period hPeriod patch) := by
  classical
  let cover :=
    finiteTangentPatchMeasuredChartCover
      period hPeriod patch
  let support :=
    finiteTangentPatchHilbertSupport
      period hPeriod patch
  let targetPiece :
      ↥cover.charts → Set CanonicalChartHilbertCoordinates :=
    fun chart =>
      finiteTangentPatchAmbientHilbertCoordinate
          period hPeriod patch ''
        cover.piece chart.1
  have hPiecePatch (chart : ↥cover.charts) :
      cover.piece chart.1 ⊆
        finiteTangentGeneratorClosedPatch
          period hPeriod patch :=
    measuredChartCover_piece_subset_patch
      period hPeriod patch cover chart.2
  let comparison
      (chart : ↥cover.charts) :
      FiniteTangentPatchPieceCanonicalLebesgueComparison
        period hPeriod patch chart.1.1 chart.1.2
          (cover.piece chart.1) :=
    finiteTangentPatchPieceCanonicalLebesgueComparison
      period hPeriod patch chart.1.1 chart.1.2
      (cover.piece_isCompact chart.1)
      (hPiecePatch chart)
      (cover.piece_subset_chart chart.1)
  have hTransitionTarget (chart : ↥cover.charts) :
      shiftedStereographicToFiniteTangentPatch
            period hPeriod patch chart.1.1 chart.1.2 ''
          shiftedStereographicAmbientPiece
            period hPeriod chart.1.1 chart.1.2
              (cover.piece chart.1) =
        targetPiece chart := by
    change
      shiftedStereographicToFiniteTangentPatch
            period hPeriod patch chart.1.1 chart.1.2 ''
          shiftedStereographicAmbientPiece
            period hPeriod chart.1.1 chart.1.2
              (cover.piece chart.1) =
        finiteTangentPatchAmbientHilbertCoordinate
            period hPeriod patch ''
          cover.piece chart.1
    exact shiftedTransition_image_eq_patchCoordinate_image
      period hPeriod patch chart.1.1 chart.1.2
      (cover.piece_subset_chart chart.1)
  have hLocalLebesgue (chart : ↥cover.charts) :
      (volume : Measure CanonicalChartHilbertCoordinates).restrict
          (targetPiece chart) ≤
        (comparison chart).lebesgueBound •
          (finiteTangentPatchCanonicalCoordinateMeasure
            period hPeriod patch).restrict
              (targetPiece chart) := by
    rw [← hTransitionTarget chart]
    exact (comparison chart).lebesgue_le_canonical
  have hLocalCanonical (chart : ↥cover.charts) :
      (finiteTangentPatchCanonicalCoordinateMeasure
          period hPeriod patch).restrict
            (targetPiece chart) ≤
        (comparison chart).canonicalBound •
          (volume : Measure
            CanonicalChartHilbertCoordinates).restrict
              (targetPiece chart) := by
    rw [← hTransitionTarget chart]
    exact (comparison chart).canonical_le_lebesgue
  have hSupport :
      support = ⋃ chart : ↥cover.charts, targetPiece chart := by
    change
      finiteTangentPatchHilbertSupport period hPeriod patch =
        ⋃ chart : ↥cover.charts, targetPiece chart
    rw [finiteTangentPatchHilbertSupport_eq_image_ambient,
      cover.covers]
    ext coordinate
    simp only [Set.mem_image, Set.mem_iUnion]
    constructor
    · rintro ⟨point, ⟨chart, hChart, hPiece⟩, rfl⟩
      refine ⟨⟨chart, hChart⟩, ?_⟩
      change
        finiteTangentPatchAmbientHilbertCoordinate
              period hPeriod patch point ∈
          finiteTangentPatchAmbientHilbertCoordinate
              period hPeriod patch ''
            cover.piece chart
      exact ⟨point, hPiece, rfl⟩
    · rintro ⟨chart, hCoordinate⟩
      change
        coordinate ∈
          finiteTangentPatchAmbientHilbertCoordinate
              period hPeriod patch ''
            cover.piece chart.1 at hCoordinate
      obtain ⟨point, hPiece, rfl⟩ := hCoordinate
      exact
        ⟨point, ⟨chart.1, chart.2, hPiece⟩, rfl⟩
  have hTargetPieceSubset
      (chart : ↥cover.charts) :
      targetPiece chart ⊆ support := by
    rw [hSupport]
    exact Set.subset_iUnion (fun index => targetPiece index) chart
  have hRestrictSupportApply_le_sum
      (μ : Measure CanonicalChartHilbertCoordinates)
      (subset : Set CanonicalChartHilbertCoordinates)
      (hSubset : MeasurableSet subset) :
      μ.restrict support subset ≤
        ∑ chart : ↥cover.charts,
          μ.restrict (targetPiece chart) subset := by
    rw [Measure.restrict_apply hSubset, hSupport]
    calc
      μ (subset ∩ ⋃ chart : ↥cover.charts, targetPiece chart) =
          μ (⋃ chart : ↥cover.charts,
            subset ∩ targetPiece chart) := by
        congr 1
        ext coordinate
        simp
      _ ≤ ∑ chart : ↥cover.charts,
          μ (subset ∩ targetPiece chart) :=
        measure_iUnion_fintype_le μ
          (fun chart : ↥cover.charts =>
            subset ∩ targetPiece chart)
      _ = ∑ chart : ↥cover.charts,
          μ.restrict (targetPiece chart) subset := by
        apply Finset.sum_congr rfl
        intro chart _
        rw [Measure.restrict_apply hSubset]
  refine ⟨{
      lebesgueBound :=
        ∑ chart : ↥cover.charts,
          (comparison chart).lebesgueBound
      lebesgueBound_ne_top := by
        apply ENNReal.sum_ne_top.2
        intro chart _
        exact (comparison chart).lebesgueBound_ne_top
      lebesgue_le_canonical := ?_
      canonicalBound :=
        ∑ chart : ↥cover.charts,
          (comparison chart).canonicalBound
      canonicalBound_ne_top := by
        apply ENNReal.sum_ne_top.2
        intro chart _
        exact (comparison chart).canonicalBound_ne_top
      canonical_le_lebesgue := ?_
    }⟩
  · apply Measure.le_iff.2
    intro subset hSubset
    rw [Measure.smul_apply, smul_eq_mul]
    calc
      (volume : Measure
          CanonicalChartHilbertCoordinates).restrict support subset ≤
          ∑ chart : ↥cover.charts,
            (volume : Measure
              CanonicalChartHilbertCoordinates).restrict
                (targetPiece chart) subset :=
        hRestrictSupportApply_le_sum volume subset hSubset
      _ ≤ ∑ chart : ↥cover.charts,
          (comparison chart).lebesgueBound *
            (finiteTangentPatchCanonicalCoordinateMeasure
              period hPeriod patch).restrict
                (targetPiece chart) subset := by
        apply Finset.sum_le_sum
        intro chart _
        simpa only [Measure.smul_apply, smul_eq_mul] using
          (hLocalLebesgue chart subset)
      _ ≤ ∑ chart : ↥cover.charts,
          (comparison chart).lebesgueBound *
            finiteTangentPatchCanonicalCoordinateMeasure
              period hPeriod patch subset := by
        apply Finset.sum_le_sum
        intro chart _
        exact mul_le_mul_left'
          (Measure.restrict_le_self subset)
          (comparison chart).lebesgueBound
      _ =
          (∑ chart : ↥cover.charts,
            (comparison chart).lebesgueBound) *
              finiteTangentPatchCanonicalCoordinateMeasure
                period hPeriod patch subset := by
        rw [Finset.sum_mul]
  · rw [← finiteTangentPatchCanonicalCoordinateMeasure_restrict_support
      period hPeriod patch]
    apply Measure.le_iff.2
    intro subset hSubset
    rw [Measure.smul_apply, smul_eq_mul]
    calc
      (finiteTangentPatchCanonicalCoordinateMeasure
          period hPeriod patch).restrict support subset ≤
          ∑ chart : ↥cover.charts,
            (finiteTangentPatchCanonicalCoordinateMeasure
              period hPeriod patch).restrict
                (targetPiece chart) subset :=
        hRestrictSupportApply_le_sum
          (finiteTangentPatchCanonicalCoordinateMeasure
            period hPeriod patch) subset hSubset
      _ ≤ ∑ chart : ↥cover.charts,
          (comparison chart).canonicalBound *
            (volume : Measure
              CanonicalChartHilbertCoordinates).restrict
                (targetPiece chart) subset := by
        apply Finset.sum_le_sum
        intro chart _
        simpa only [Measure.smul_apply, smul_eq_mul] using
          (hLocalCanonical chart subset)
      _ ≤ ∑ chart : ↥cover.charts,
          (comparison chart).canonicalBound *
            (volume : Measure
              CanonicalChartHilbertCoordinates).restrict
                support subset := by
        apply Finset.sum_le_sum
        intro chart _
        exact mul_le_mul_left'
          ((Measure.restrict_mono_set
            (volume : Measure CanonicalChartHilbertCoordinates)
            (hTargetPieceSubset chart)) subset)
          (comparison chart).canonicalBound
      _ =
          (∑ chart : ↥cover.charts,
            (comparison chart).canonicalBound) *
              (volume : Measure
                CanonicalChartHilbertCoordinates).restrict
                  support subset := by
        rw [Finset.sum_mul]

/-- Chosen global canonical/Lebesgue comparison on every actual compact
tangent-generator patch. -/
def finiteTangentPatchCanonicalLebesgueComparison
    (patch : Patch period hPeriod) :
    FiniteTangentPatchCanonicalLebesgueComparison
      period hPeriod patch :=
  Classical.choice
    (finiteTangentPatchCanonicalLebesgueComparison_nonempty
      period hPeriod patch)

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarFinitePatchVolumeComparison4D
end JanusFormal
