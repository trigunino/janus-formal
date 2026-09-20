import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLCanonicalThroatFinitePatchMeasuredChartCover4D

/-!
# Canonical/Lebesgue comparison on the finite Rellich patches

The explicit measured stereographic charts and the fixed throat-generator
charts have smooth locally invertible transition maps.  Compactness then
turns both transition directions into uniform Lipschitz bounds.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12LLCanonicalThroatFinitePatchVolumeComparison4D

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusCompleteTimeFlow4D
open P0EFTJanusMappingTorusCompleteIndependentFieldTimeAction4D
open P0EFTJanusMappingTorusCanonicalLatitudeCoareaClosure4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusProgramPT12LLCanonicalThroatEuclideanRellichCore4D
open P0EFTJanusMappingTorusCanonicalThroatStereographicVolumeComparison4D
open P0EFTJanusMappingTorusCanonicalThroatLocalVolumeTransport4D
open P0EFTJanusProgramPT12LLCanonicalThroatFinitePatchMeasuredChartCover4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev throatData :=
  fixedEquatorData period hPeriod

private abbrev EffectiveThroatCover :=
  MappingTorusCover (throatData period hPeriod)

private abbrev EffectiveThroat :=
  MappingTorus (throatData period hPeriod)

private abbrev StandardSphere :=
  Metric.sphere (0 : EuclideanR3) 1

local instance euclideanR3_finrank :
    Fact (Module.finrank Real EuclideanR3 = 2 + 1) :=
  ⟨by simp [EuclideanR3]⟩

private abbrev Patch :=
  FiniteThroatGeneratorPatch period hPeriod

local instance canonicalChartHilbertMeasurableSpace :
    MeasurableSpace CanonicalThroatChartHilbertCoordinates :=
  borel CanonicalThroatChartHilbertCoordinates

local instance canonicalChartHilbertBorelSpace :
    BorelSpace CanonicalThroatChartHilbertCoordinates where
  measurable_eq := rfl

local instance throatCoverCoordinatesVolumeIsAddHaarMeasure :
    (volume : Measure ThroatCoverCoordinates).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure _ _

local instance effectiveThroatCoverChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroatCover period hPeriod) :=
  fixedThroatCoverChartedSpace period hPeriod

local instance effectiveThroatCoverIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroatCover period hPeriod) :=
  fixedThroatCover_isManifold period hPeriod

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance effectiveThroatMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) :=
  borel _

local instance effectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
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

private def equatorialTwoSphereDiffeomorph :
    EquatorialTwoSphere ≃ₘ^ω⟮(𝓡 2), (𝓡 2)⟯ StandardSphere where
  toEquiv := equatorialTwoSphereHomeomorph.toEquiv
  contMDiff_toFun :=
    chartedSpacePullback_toFun_contMDiff
      (𝓡 2) ω equatorialTwoSphereHomeomorph
  contMDiff_invFun :=
    chartedSpacePullback_invFun_contMDiff
      (𝓡 2) ω equatorialTwoSphereHomeomorph

private def effectiveThroatCoverProductDiffeomorph :
    EffectiveThroatCover period hPeriod ≃ₘ^ω⟮
      throatCoverModelWithCorners, throatCoverModelWithCorners⟯
        EquatorialTwoSphere × Real where
  toEquiv :=
    (coverHomeomorphProd (throatData period hPeriod)).toEquiv
  contMDiff_toFun :=
    chartedSpacePullback_toFun_contMDiff
      throatCoverModelWithCorners ω
      (coverHomeomorphProd (throatData period hPeriod))
  contMDiff_invFun :=
    chartedSpacePullback_invFun_contMDiff
      throatCoverModelWithCorners ω
      (coverHomeomorphProd (throatData period hPeriod))

private theorem canonicalLatitudeThroatMap_isLocalDiffeomorph :
    IsLocalDiffeomorph throatCoverModelWithCorners
      throatCoverModelWithCorners ω
      (canonicalLatitudeThroatMap period hPeriod) := by
  intro parameter
  let sphereProduct :=
    equatorialTwoSphereDiffeomorph.symm.prodCongr
      (Diffeomorph.refl 𝓘(Real, Real) Real ω)
  have hSphere :=
    sphereProduct.isLocalDiffeomorph parameter
  have hCover :=
    (effectiveThroatCoverProductDiffeomorph period hPeriod).symm
      |>.isLocalDiffeomorph (sphereProduct parameter)
  have hProjection :=
    fixedThroat_projection_isLocalDiffeomorph
      period hPeriod
      ((effectiveThroatCoverProductDiffeomorph period hPeriod).symm
        (sphereProduct parameter))
  have hFirst :=
    IsLocalDiffeomorphAt.comp
      (I := throatCoverModelWithCorners)
      (J := throatCoverModelWithCorners)
      (K := throatCoverModelWithCorners)
      (M := StandardSphere × Real)
      (N := EquatorialTwoSphere × Real)
      (P := EffectiveThroatCover period hPeriod)
      (n := ω) hSphere hCover
  have hComposite :=
    IsLocalDiffeomorphAt.comp
      (I := throatCoverModelWithCorners)
      (J := throatCoverModelWithCorners)
      (K := throatCoverModelWithCorners)
      (M := StandardSphere × Real)
      (N := EffectiveThroatCover period hPeriod)
      (P := EffectiveThroat period hPeriod)
      (n := ω) hFirst hProjection
  convert hComposite using 1
  funext point
  rfl

private def stereographicPartialDiffeomorph
    (pole : StandardSphere) :
    PartialDiffeomorph (𝓡 2) (𝓡 2)
      StandardSphere (EuclideanSpace Real (Fin 2)) ω where
  toPartialEquiv := (stereographic' 2 pole).toPartialEquiv
  open_source := (stereographic' 2 pole).open_source
  open_target := (stereographic' 2 pole).open_target
  contMDiffOn_toFun := by
    have hChartEq :
        chartAt (EuclideanSpace Real (Fin 2)) (-pole) =
          stereographic' 2 pole := by
      change stereographic' 2 (- -pole) = stereographic' 2 pole
      rw [neg_neg]
    have hChartAt :
        chartAt (EuclideanSpace Real (Fin 2)) (-pole) ∈
          IsManifold.maximalAtlas (𝓡 2) ω StandardSphere :=
      IsManifold.chart_mem_maximalAtlas
        (I := 𝓡 2) (-pole)
    rw [hChartEq] at hChartAt
    exact contMDiffOn_of_mem_maximalAtlas hChartAt
  contMDiffOn_invFun := by
    have hChartEq :
        chartAt (EuclideanSpace Real (Fin 2)) (-pole) =
          stereographic' 2 pole := by
      change stereographic' 2 (- -pole) = stereographic' 2 pole
      rw [neg_neg]
    have hChartAt :
        chartAt (EuclideanSpace Real (Fin 2)) (-pole) ∈
          IsManifold.maximalAtlas (𝓡 2) ω StandardSphere :=
      IsManifold.chart_mem_maximalAtlas
        (I := 𝓡 2) (-pole)
    rw [hChartEq] at hChartAt
    exact contMDiffOn_symm_of_mem_maximalAtlas hChartAt

private def stereographicProductPartialDiffeomorph
    (pole : StandardSphere) :
    PartialDiffeomorph throatCoverModelWithCorners
      throatCoverModelWithCorners ThroatCoverCoordinates
      (StandardSphere × Real) ω :=
  partialDiffeomorphProd
    (stereographicPartialDiffeomorph pole).symm
    (Diffeomorph.refl 𝓘(Real, Real) Real ω).toPartialDiffeomorph

private theorem stereographicProductMap_isLocalDiffeomorph
    (pole : StandardSphere) :
    IsLocalDiffeomorph throatCoverModelWithCorners
      throatCoverModelWithCorners ω
      (fun coordinate : ThroatCoverCoordinates =>
        (stereographicInverseSphere pole coordinate.1,
          coordinate.2)) := by
  intro coordinate
  have hSource :
      coordinate ∈
        (stereographicProductPartialDiffeomorph pole).source := by
    constructor
    · change coordinate.1 ∈
        (stereographicPartialDiffeomorph pole).symm.source
      change coordinate.1 ∈ (stereographic' 2 pole).target
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
  simp [stereographicProductPartialDiffeomorph,
    partialDiffeomorphProd, stereographicPartialDiffeomorph,
    stereographicInverseSphere_eq_stereographic_symm,
    Diffeomorph.toPartialDiffeomorph, Diffeomorph.refl]

/-- The ambient shifted stereographic parametrization is locally an analytic
diffeomorphism at every coordinate. -/
theorem shiftedThroatStereographicPhysicalMapAmbient_isLocalDiffeomorph
    (shift : Real)
    (pole : StandardSphere) :
    IsLocalDiffeomorph throatCoverModelWithCorners
      throatCoverModelWithCorners ω
      (shiftedThroatStereographicPhysicalMapAmbient
        period hPeriod shift pole) := by
  intro coordinate
  let spherePoint : StandardSphere × Real :=
    (stereographicInverseSphere pole coordinate.1, coordinate.2)
  let quotientPoint :=
    canonicalLatitudeThroatMap
      period hPeriod spherePoint
  have hStereographic :=
    stereographicProductMap_isLocalDiffeomorph
      pole coordinate
  have hFundamental :=
    canonicalLatitudeThroatMap_isLocalDiffeomorph
      period hPeriod spherePoint
  have hFlow :=
    (throatTimeFlowDiffeomorph period hPeriod shift)
      |>.isLocalDiffeomorph quotientPoint
  have hFirst :=
    IsLocalDiffeomorphAt.comp
      (I := throatCoverModelWithCorners)
      (J := throatCoverModelWithCorners)
      (K := throatCoverModelWithCorners)
      (M := ThroatCoverCoordinates)
      (N := StandardSphere × Real)
      (P := EffectiveThroat period hPeriod)
      (n := ω) hStereographic hFundamental
  have hComposite :=
    IsLocalDiffeomorphAt.comp
      (I := throatCoverModelWithCorners)
      (J := throatCoverModelWithCorners)
      (K := throatCoverModelWithCorners)
      (M := ThroatCoverCoordinates)
      (N := EffectiveThroat period hPeriod)
      (P := EffectiveThroat period hPeriod)
      (n := ω) hFirst hFlow
  convert hComposite using 1
  funext point
  rfl

/-- Fixed patch coordinates, extended to all quotient points by
`extChartAt`, followed by the Hilbert-model identification. -/
def finiteThroatGeneratorPatchAmbientHilbertCoordinate
    (patch : Patch period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    CanonicalThroatChartHilbertCoordinates :=
  canonicalThroatChartHilbertEquivCoverCoordinates.symm
    (extChartAt throatCoverModelWithCorners patch.1 point)

/-- Transition from an explicit shifted stereographic chart to one fixed
finite throat-generator chart. -/
def shiftedStereographicToFiniteThroatGeneratorPatch
    (patch : Patch period hPeriod)
    (shift : Real)
    (pole : StandardSphere)
    (coordinate : ThroatCoverCoordinates) :
    CanonicalThroatChartHilbertCoordinates :=
  finiteThroatGeneratorPatchAmbientHilbertCoordinate
    period hPeriod patch
    (shiftedThroatStereographicPhysicalMapAmbient
      period hPeriod shift pole coordinate)

private def quotientExtChartPartialDiffeomorph
    (anchor : EffectiveThroat period hPeriod) :
    PartialDiffeomorph throatCoverModelWithCorners
      (modelWithCornersSelf Real ThroatCoverCoordinates)
      (EffectiveThroat period hPeriod) ThroatCoverCoordinates ω where
  toPartialEquiv := extChartAt throatCoverModelWithCorners anchor
  open_source :=
    isOpen_extChartAt_source (I := throatCoverModelWithCorners) anchor
  open_target :=
    isOpen_extChartAt_target (I := throatCoverModelWithCorners) anchor
  contMDiffOn_toFun := by
    rw [extChartAt_source]
    exact contMDiffOn_extChartAt
      (I := throatCoverModelWithCorners) (n := ω) (x := anchor)
  contMDiffOn_invFun :=
    contMDiffOn_extChartAt_symm
      (I := throatCoverModelWithCorners) (n := ω) anchor

/-- On the source of the fixed quotient chart, the transition to Hilbert
coordinates is a local analytic diffeomorphism. -/
theorem shiftedStereographicToFiniteThroatGeneratorPatch_isLocalDiffeomorphAt
    (patch : Patch period hPeriod)
    (shift : Real)
    (pole : StandardSphere)
    (coordinate : ThroatCoverCoordinates)
    (hCoordinate :
      shiftedThroatStereographicPhysicalMapAmbient
          period hPeriod shift pole coordinate ∈
        (chartAt ThroatCoverModel patch.1).source) :
    IsLocalDiffeomorphAt
        throatCoverModelWithCorners
        (modelWithCornersSelf Real CanonicalThroatChartHilbertCoordinates)
        ω
        (shiftedStereographicToFiniteThroatGeneratorPatch
          period hPeriod patch shift pole)
        coordinate := by
  have hShift :=
    shiftedThroatStereographicPhysicalMapAmbient_isLocalDiffeomorph
      period hPeriod shift pole coordinate
  have hCoordinate' :
      shiftedThroatStereographicPhysicalMapAmbient
          period hPeriod shift pole coordinate ∈
        (quotientExtChartPartialDiffeomorph
          period hPeriod patch.1).source := by
    change
      shiftedThroatStereographicPhysicalMapAmbient
          period hPeriod shift pole coordinate ∈
        (extChartAt throatCoverModelWithCorners patch.1).source
    rwa [extChartAt_source]
  have hChart :=
    (quotientExtChartPartialDiffeomorph
      period hPeriod patch.1).isLocalDiffeomorphAt
        _ _ _ hCoordinate'
  let linearDiffeomorph :
      ThroatCoverCoordinates ≃ₘ^ω⟮
        modelWithCornersSelf Real ThroatCoverCoordinates,
        modelWithCornersSelf Real
          CanonicalThroatChartHilbertCoordinates⟯
        CanonicalThroatChartHilbertCoordinates :=
    { toEquiv :=
        canonicalThroatChartHilbertEquivCoverCoordinates.symm.toEquiv
      contMDiff_toFun :=
        canonicalThroatChartHilbertEquivCoverCoordinates.symm.contDiff.contMDiff
      contMDiff_invFun :=
        canonicalThroatChartHilbertEquivCoverCoordinates.contDiff.contMDiff }
  have hLinear :=
    linearDiffeomorph
      |>.isLocalDiffeomorph
        (extChartAt throatCoverModelWithCorners patch.1
          (shiftedThroatStereographicPhysicalMapAmbient
            period hPeriod shift pole coordinate))
  have hFirst :=
    IsLocalDiffeomorphAt.comp
      (I := throatCoverModelWithCorners)
      (J := throatCoverModelWithCorners)
      (K := modelWithCornersSelf Real ThroatCoverCoordinates)
      (M := ThroatCoverCoordinates)
      (N := EffectiveThroat period hPeriod)
      (P := ThroatCoverCoordinates)
      (n := ω) hShift hChart
  have hComposite :=
    IsLocalDiffeomorphAt.comp
      (I := throatCoverModelWithCorners)
      (J := modelWithCornersSelf Real ThroatCoverCoordinates)
      (K := modelWithCornersSelf Real
        CanonicalThroatChartHilbertCoordinates)
      (M := ThroatCoverCoordinates)
      (N := ThroatCoverCoordinates)
      (P := CanonicalThroatChartHilbertCoordinates)
      (n := ω) hFirst hLinear
  have hComposite' :
      IsLocalDiffeomorphAt
        throatCoverModelWithCorners
        (modelWithCornersSelf Real
          CanonicalThroatChartHilbertCoordinates)
        ω
        (shiftedStereographicToFiniteThroatGeneratorPatch
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
    (piece : Set (EffectiveThroat period hPeriod)) :
    Set ThroatCoverCoordinates :=
  throatInteriorStereographicCoordinateInclusion period ''
    (shiftedThroatInteriorStereographicPhysicalMap
      period hPeriod shift pole ⁻¹' piece)

theorem shiftedStereographicAmbientPiece_isCompact
    (shift : Real)
    (pole : StandardSphere)
    {piece : Set (EffectiveThroat period hPeriod)}
    (hPieceCompact : IsCompact piece)
    (hPieceRange :
      piece ⊆ Set.range
        (shiftedThroatInteriorStereographicPhysicalMap
          period hPeriod shift pole)) :
    IsCompact
      (shiftedStereographicAmbientPiece
        period hPeriod shift pole piece) := by
  have hPreimage :
      IsCompact
        (shiftedThroatInteriorStereographicPhysicalMap
          period hPeriod shift pole ⁻¹' piece) :=
    (shiftedThroatInteriorStereographicPhysicalMap_isOpenEmbedding
      period hPeriod shift pole).isEmbedding.isInducing
        |>.isCompact_preimage' hPieceCompact hPieceRange
  exact hPreimage.image
    (throatInteriorStereographicCoordinateInclusion_isOpenEmbedding
      period).continuous

theorem shiftedThroatStereographicPhysicalMapAmbient_image_ambientPiece
    (shift : Real)
    (pole : StandardSphere)
    {piece : Set (EffectiveThroat period hPeriod)}
    (hPieceRange :
      piece ⊆ Set.range
        (shiftedThroatInteriorStereographicPhysicalMap
          period hPeriod shift pole)) :
    shiftedThroatStereographicPhysicalMapAmbient
        period hPeriod shift pole ''
      shiftedStereographicAmbientPiece
        period hPeriod shift pole piece =
      piece := by
  apply Set.Subset.antisymm
  · rintro point ⟨_, ⟨coordinate, hCoordinate, rfl⟩, rfl⟩
    rw [shiftedThroatStereographicPhysicalMapAmbient_agrees]
    exact hCoordinate
  · intro point hPoint
    obtain ⟨coordinate, hCoordinate⟩ :=
      hPieceRange hPoint
    refine
      ⟨throatInteriorStereographicCoordinateInclusion
          period coordinate,
        ⟨coordinate, ?_, rfl⟩, ?_⟩
    · simpa [hCoordinate] using hPoint
    · rw [shiftedThroatStereographicPhysicalMapAmbient_agrees]
      exact hCoordinate

/-- The forward transition from stereographic coordinates to fixed Hilbert
coordinates is uniformly Lipschitz on every compact measured-chart piece. -/
theorem exists_shiftedStereographicToFiniteThroatGeneratorPatch_lipschitzOn
    (patch : Patch period hPeriod)
    (shift : Real)
    (pole : StandardSphere)
    {piece : Set (EffectiveThroat period hPeriod)}
    (hPieceCompact : IsCompact piece)
    (hPiecePatch :
      piece ⊆ finiteThroatGeneratorClosedPatch
        period hPeriod patch)
    (hPieceRange :
      piece ⊆ Set.range
        (shiftedThroatInteriorStereographicPhysicalMap
          period hPeriod shift pole)) :
    ∃ constant : NNReal,
      LipschitzOnWith constant
        (shiftedStereographicToFiniteThroatGeneratorPatch
          period hPeriod patch shift pole)
        (shiftedStereographicAmbientPiece
          period hPeriod shift pole piece) := by
  apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (shiftedStereographicAmbientPiece_isCompact
      period hPeriod shift pole hPieceCompact hPieceRange)
  intro coordinate hCoordinate
  obtain ⟨source, hSourcePiece, rfl⟩ := hCoordinate
  have hPhysicalPiece :
      shiftedThroatStereographicPhysicalMapAmbient
          period hPeriod shift pole
          (throatInteriorStereographicCoordinateInclusion
            period source) ∈ piece := by
    rw [shiftedThroatStereographicPhysicalMapAmbient_agrees]
    exact hSourcePiece
  have hChartSource :
      shiftedThroatStereographicPhysicalMapAmbient
          period hPeriod shift pole
          (throatInteriorStereographicCoordinateInclusion
            period source) ∈
        (chartAt ThroatCoverModel patch.1).source := by
    rw [← finiteThroatGeneratorOpenPatch_eq_chart_source
      period hPeriod patch]
    exact finiteThroatGeneratorClosedPatch_subset_openPatch
      period hPeriod patch (hPiecePatch hPhysicalPiece)
  have hLocal :=
    shiftedStereographicToFiniteThroatGeneratorPatch_isLocalDiffeomorphAt
      period hPeriod patch shift pole
      (throatInteriorStereographicCoordinateInclusion
        period source) hChartSource
  have hManifold :
      ContMDiffAt throatCoverModelWithCorners
        (modelWithCornersSelf Real
          CanonicalThroatChartHilbertCoordinates)
        1
        (shiftedStereographicToFiniteThroatGeneratorPatch
          period hPeriod patch shift pole)
        (throatInteriorStereographicCoordinateInclusion
          period source) :=
    hLocal.contMDiffAt.of_le (by simp)
  have hSelf :
      ContMDiffAt
        (modelWithCornersSelf Real ThroatCoverCoordinates)
        (modelWithCornersSelf Real
          CanonicalThroatChartHilbertCoordinates)
        1
        (shiftedStereographicToFiniteThroatGeneratorPatch
          period hPeriod patch shift pole)
        (throatInteriorStereographicCoordinateInclusion
          period source) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hManifold
  obtain ⟨constant, neighborhood, hNeighborhood, hLipschitz⟩ :=
    hSelf.contDiffAt.exists_lipschitzOnWith
  exact
    ⟨constant, neighborhood,
      mem_nhdsWithin_of_mem_nhds hNeighborhood, hLipschitz⟩

/-- Open ambient source of the measured stereographic chart. -/
def throatInteriorStereographicAmbientStrip :
    Set ThroatCoverCoordinates :=
  Set.range
    (throatInteriorStereographicCoordinateInclusion period)

theorem throatInteriorStereographicAmbientStrip_isOpen :
    IsOpen
      (throatInteriorStereographicAmbientStrip period) :=
  (throatInteriorStereographicCoordinateInclusion_isOpenEmbedding
    period).isOpen_range

theorem shiftedStereographicAmbientPiece_subset_strip
    (shift : Real)
    (pole : StandardSphere)
    (piece : Set (EffectiveThroat period hPeriod)) :
    shiftedStereographicAmbientPiece
        period hPeriod shift pole piece ⊆
      throatInteriorStereographicAmbientStrip period := by
  rintro _ ⟨coordinate, _, rfl⟩
  exact ⟨coordinate, rfl⟩

theorem shiftedStereographicAmbientPiece_mapsTo_piece
    (shift : Real)
    (pole : StandardSphere)
    (piece : Set (EffectiveThroat period hPeriod)) :
    Set.MapsTo
      (shiftedThroatStereographicPhysicalMapAmbient
        period hPeriod shift pole)
      (shiftedStereographicAmbientPiece
        period hPeriod shift pole piece)
      piece := by
  rintro _ ⟨coordinate, hCoordinate, rfl⟩
  rw [shiftedThroatStereographicPhysicalMapAmbient_agrees]
  exact hCoordinate

theorem shiftedStereographicAmbientPiece_subset_chartSource
    (patch : Patch period hPeriod)
    (shift : Real)
    (pole : StandardSphere)
    {piece : Set (EffectiveThroat period hPeriod)}
    (hPiecePatch :
      piece ⊆ finiteThroatGeneratorClosedPatch
        period hPeriod patch) :
    shiftedStereographicAmbientPiece
        period hPeriod shift pole piece ⊆
      shiftedThroatStereographicPhysicalMapAmbient
          period hPeriod shift pole ⁻¹'
        (chartAt ThroatCoverModel patch.1).source := by
  intro coordinate hCoordinate
  rw [← finiteThroatGeneratorOpenPatch_eq_chart_source
    period hPeriod patch]
  exact finiteThroatGeneratorClosedPatch_subset_openPatch
    period hPeriod patch
    (hPiecePatch
      (shiftedStereographicAmbientPiece_mapsTo_piece
        period hPeriod shift pole piece hCoordinate))

theorem shiftedThroatStereographicPhysicalMapAmbient_injOn_strip
    (shift : Real)
    (pole : StandardSphere) :
    Set.InjOn
      (shiftedThroatStereographicPhysicalMapAmbient
        period hPeriod shift pole)
      (throatInteriorStereographicAmbientStrip period) := by
  rintro _ ⟨first, rfl⟩ _ ⟨second, rfl⟩ hEqual
  have hMeasured :
      shiftedThroatInteriorStereographicPhysicalMap
          period hPeriod shift pole first =
        shiftedThroatInteriorStereographicPhysicalMap
          period hPeriod shift pole second := by
    simpa only [
      shiftedThroatStereographicPhysicalMapAmbient_agrees] using hEqual
  have hSource :=
    (shiftedThroatInteriorStereographicPhysicalMap_isOpenEmbedding
      period hPeriod shift pole).injective hMeasured
  exact congrArg
    (throatInteriorStereographicCoordinateInclusion period)
    hSource

/-- The transition is injective wherever the measured strip meets the source
of the selected fixed quotient chart. -/
theorem shiftedStereographicToFiniteThroatGeneratorPatch_injOn
    (patch : Patch period hPeriod)
    (shift : Real)
    (pole : StandardSphere) :
    Set.InjOn
      (shiftedStereographicToFiniteThroatGeneratorPatch
        period hPeriod patch shift pole)
      (throatInteriorStereographicAmbientStrip period ∩
        shiftedThroatStereographicPhysicalMapAmbient
          period hPeriod shift pole ⁻¹'
            (chartAt ThroatCoverModel patch.1).source) := by
  intro first hFirst second hSecond hEqual
  have hChartEqual :
      extChartAt throatCoverModelWithCorners patch.1
          (shiftedThroatStereographicPhysicalMapAmbient
            period hPeriod shift pole first) =
        extChartAt throatCoverModelWithCorners patch.1
          (shiftedThroatStereographicPhysicalMapAmbient
            period hPeriod shift pole second) := by
    apply canonicalThroatChartHilbertEquivCoverCoordinates.symm.injective
    simpa [shiftedStereographicToFiniteThroatGeneratorPatch,
      finiteThroatGeneratorPatchAmbientHilbertCoordinate] using hEqual
  have hFirstSource :
      shiftedThroatStereographicPhysicalMapAmbient
          period hPeriod shift pole first ∈
        (extChartAt throatCoverModelWithCorners patch.1).source := by
    rw [extChartAt_source]
    exact hFirst.2
  have hSecondSource :
      shiftedThroatStereographicPhysicalMapAmbient
          period hPeriod shift pole second ∈
        (extChartAt throatCoverModelWithCorners patch.1).source := by
    rw [extChartAt_source]
    exact hSecond.2
  have hPhysicalEqual :=
    (extChartAt throatCoverModelWithCorners patch.1).injOn
      hFirstSource hSecondSource hChartEqual
  exact
    shiftedThroatStereographicPhysicalMapAmbient_injOn_strip
      period hPeriod shift pole
      hFirst.1 hSecond.1 hPhysicalEqual

/-- Chosen inverse of the transition on one compact overlap image.  Its
off-image value is irrelevant. -/
def finiteThroatGeneratorPatchToShiftedStereographic
    (patch : Patch period hPeriod)
    (shift : Real)
    (pole : StandardSphere)
    (piece : Set (EffectiveThroat period hPeriod))
    (coordinate : CanonicalThroatChartHilbertCoordinates) :
    ThroatCoverCoordinates := by
  classical
  exact
    if hCoordinate :
        coordinate ∈
          shiftedStereographicToFiniteThroatGeneratorPatch
              period hPeriod patch shift pole ''
            shiftedStereographicAmbientPiece
              period hPeriod shift pole piece
    then Classical.choose hCoordinate
    else 0

theorem finiteThroatGeneratorPatchToShiftedStereographic_mem
    (patch : Patch period hPeriod)
    (shift : Real)
    (pole : StandardSphere)
    {piece : Set (EffectiveThroat period hPeriod)}
    {coordinate : CanonicalThroatChartHilbertCoordinates}
    (hCoordinate :
      coordinate ∈
        shiftedStereographicToFiniteThroatGeneratorPatch
            period hPeriod patch shift pole ''
          shiftedStereographicAmbientPiece
            period hPeriod shift pole piece) :
    finiteThroatGeneratorPatchToShiftedStereographic
        period hPeriod patch shift pole piece coordinate ∈
      shiftedStereographicAmbientPiece
        period hPeriod shift pole piece := by
  classical
  rw [finiteThroatGeneratorPatchToShiftedStereographic,
    dif_pos hCoordinate]
  exact (Classical.choose_spec hCoordinate).1

theorem shiftedStereographicToFiniteThroatGeneratorPatch_inverse
    (patch : Patch period hPeriod)
    (shift : Real)
    (pole : StandardSphere)
    {piece : Set (EffectiveThroat period hPeriod)}
    {coordinate : CanonicalThroatChartHilbertCoordinates}
    (hCoordinate :
      coordinate ∈
        shiftedStereographicToFiniteThroatGeneratorPatch
            period hPeriod patch shift pole ''
          shiftedStereographicAmbientPiece
            period hPeriod shift pole piece) :
    shiftedStereographicToFiniteThroatGeneratorPatch
        period hPeriod patch shift pole
        (finiteThroatGeneratorPatchToShiftedStereographic
        period hPeriod patch shift pole piece coordinate) =
      coordinate := by
  classical
  rw [finiteThroatGeneratorPatchToShiftedStereographic,
    dif_pos hCoordinate]
  exact (Classical.choose_spec hCoordinate).2

theorem shiftedStereographicToFiniteThroatGeneratorPatch_injOn_ambientPiece
    (patch : Patch period hPeriod)
    (shift : Real)
    (pole : StandardSphere)
    {piece : Set (EffectiveThroat period hPeriod)}
    (hPiecePatch :
      piece ⊆ finiteThroatGeneratorClosedPatch
        period hPeriod patch) :
    Set.InjOn
      (shiftedStereographicToFiniteThroatGeneratorPatch
        period hPeriod patch shift pole)
      (shiftedStereographicAmbientPiece
        period hPeriod shift pole piece) := by
  apply
    (shiftedStereographicToFiniteThroatGeneratorPatch_injOn
      period hPeriod patch shift pole).mono
  intro coordinate hCoordinate
  exact
    ⟨shiftedStereographicAmbientPiece_subset_strip
        period hPeriod shift pole piece hCoordinate,
      shiftedStereographicAmbientPiece_subset_chartSource
        period hPeriod patch shift pole hPiecePatch hCoordinate⟩

theorem finiteThroatGeneratorPatchToShiftedStereographic_transition
    (patch : Patch period hPeriod)
    (shift : Real)
    (pole : StandardSphere)
    {piece : Set (EffectiveThroat period hPeriod)}
    (hPiecePatch :
      piece ⊆ finiteThroatGeneratorClosedPatch
        period hPeriod patch)
    {coordinate : ThroatCoverCoordinates}
    (hCoordinate :
      coordinate ∈ shiftedStereographicAmbientPiece
        period hPeriod shift pole piece) :
    finiteThroatGeneratorPatchToShiftedStereographic
        period hPeriod patch shift pole piece
        (shiftedStereographicToFiniteThroatGeneratorPatch
          period hPeriod patch shift pole coordinate) =
      coordinate := by
  apply
    shiftedStereographicToFiniteThroatGeneratorPatch_injOn_ambientPiece
      period hPeriod patch shift pole hPiecePatch
  · exact finiteThroatGeneratorPatchToShiftedStereographic_mem
      period hPeriod patch shift pole
      ⟨coordinate, hCoordinate, rfl⟩
  · exact hCoordinate
  · exact shiftedStereographicToFiniteThroatGeneratorPatch_inverse
      period hPeriod patch shift pole
      ⟨coordinate, hCoordinate, rfl⟩

/-- The inverse transition is uniformly Lipschitz on the compact image of
every measured-chart piece. -/
theorem exists_finiteThroatGeneratorPatchToShiftedStereographic_lipschitzOn
    (patch : Patch period hPeriod)
    (shift : Real)
    (pole : StandardSphere)
    {piece : Set (EffectiveThroat period hPeriod)}
    (hPieceCompact : IsCompact piece)
    (hPiecePatch :
      piece ⊆ finiteThroatGeneratorClosedPatch
        period hPeriod patch)
    (hPieceRange :
      piece ⊆ Set.range
        (shiftedThroatInteriorStereographicPhysicalMap
          period hPeriod shift pole)) :
    ∃ constant : NNReal,
      LipschitzOnWith constant
        (finiteThroatGeneratorPatchToShiftedStereographic
          period hPeriod patch shift pole piece)
        (shiftedStereographicToFiniteThroatGeneratorPatch
            period hPeriod patch shift pole ''
          shiftedStereographicAmbientPiece
            period hPeriod shift pole piece) := by
  let ambientPiece :=
    shiftedStereographicAmbientPiece
      period hPeriod shift pole piece
  let transition :=
    shiftedStereographicToFiniteThroatGeneratorPatch
      period hPeriod patch shift pole
  let transitionImage :=
    transition '' ambientPiece
  have hAmbientCompact : IsCompact ambientPiece :=
    shiftedStereographicAmbientPiece_isCompact
      period hPeriod shift pole hPieceCompact hPieceRange
  obtain ⟨forwardConstant, hForward⟩ :=
    exists_shiftedStereographicToFiniteThroatGeneratorPatch_lipschitzOn
      period hPeriod patch shift pole
      hPieceCompact hPiecePatch hPieceRange
  have hImageCompact : IsCompact transitionImage :=
    hAmbientCompact.image_of_continuousOn hForward.continuousOn
  apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    hImageCompact
  intro imageCoordinate hImageCoordinate
  obtain ⟨source, hSourcePiece, rfl⟩ := hImageCoordinate
  have hChartSource :
      shiftedThroatStereographicPhysicalMapAmbient
          period hPeriod shift pole source ∈
        (chartAt ThroatCoverModel patch.1).source :=
    shiftedStereographicAmbientPiece_subset_chartSource
      period hPeriod patch shift pole hPiecePatch hSourcePiece
  have hLocal :=
    shiftedStereographicToFiniteThroatGeneratorPatch_isLocalDiffeomorphAt
      period hPeriod patch shift pole source hChartSource
  let localInverse := hLocal.localInverse
  have hInverseManifold :
      ContMDiffAt
        (modelWithCornersSelf Real
          CanonicalThroatChartHilbertCoordinates)
        throatCoverModelWithCorners
        1 localInverse (transition source) := by
    exact hLocal.localInverse_contMDiffAt.of_le (by simp)
  have hInverseSelf :
      ContMDiffAt
        (modelWithCornersSelf Real
          CanonicalThroatChartHilbertCoordinates)
        (modelWithCornersSelf Real ThroatCoverCoordinates)
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
      source ∈ throatInteriorStereographicAmbientStrip period :=
    shiftedStereographicAmbientPiece_subset_strip
      period hPeriod shift pole piece hSourcePiece
  have hInverseStrip :
      localInverse ⁻¹'
          throatInteriorStereographicAmbientStrip period ∈
        𝓝 (transition source) := by
    apply hInverseSelf.contDiffAt.continuousAt.preimage_mem_nhds
    exact
      (throatInteriorStereographicAmbientStrip_isOpen period).mem_nhds
        (by rwa [hInverseValue])
  have hPhysicalContinuous :
      ContinuousAt
        (shiftedThroatStereographicPhysicalMapAmbient
          period hPeriod shift pole ∘ localInverse)
        (transition source) :=
    (shiftedThroatStereographicPhysicalMapAmbient_contMDiff
      period hPeriod shift pole).continuous.continuousAt.comp
        hInverseSelf.contDiffAt.continuousAt
  have hInverseChart :
      (shiftedThroatStereographicPhysicalMapAmbient
          period hPeriod shift pole ∘ localInverse) ⁻¹'
          (chartAt ThroatCoverModel patch.1).source ∈
        𝓝 (transition source) := by
    apply hPhysicalContinuous.preimage_mem_nhds
    exact
      (chartAt ThroatCoverModel patch.1).open_source.mem_nhds
        (by simpa [Function.comp_def, hInverseValue] using hChartSource)
  let localSet : Set CanonicalThroatChartHilbertCoordinates :=
    neighborhood ∩
      (localInverse.source ∩
        (localInverse ⁻¹'
          throatInteriorStereographicAmbientStrip period ∩
        (shiftedThroatStereographicPhysicalMapAmbient
            period hPeriod shift pole ∘ localInverse) ⁻¹'
          (chartAt ThroatCoverModel patch.1).source))
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
      finiteThroatGeneratorPatchToShiftedStereographic
          period hPeriod patch shift pole piece first =
        localInverse first := by
    apply shiftedStereographicToFiniteThroatGeneratorPatch_injOn
      period hPeriod patch shift pole
    · exact
        ⟨shiftedStereographicAmbientPiece_subset_strip
            period hPeriod shift pole piece
            (finiteThroatGeneratorPatchToShiftedStereographic_mem
              period hPeriod patch shift pole firstImage),
          shiftedStereographicAmbientPiece_subset_chartSource
            period hPeriod patch shift pole hPiecePatch
            (finiteThroatGeneratorPatchToShiftedStereographic_mem
              period hPeriod patch shift pole firstImage)⟩
    · exact ⟨firstLocal.2.2.1, firstLocal.2.2.2⟩
    · calc
        transition
            (finiteThroatGeneratorPatchToShiftedStereographic
              period hPeriod patch shift pole piece first) =
          first :=
            shiftedStereographicToFiniteThroatGeneratorPatch_inverse
              period hPeriod patch shift pole firstImage
        _ = transition (localInverse first) :=
          (hLocal.localInverse_right_inv firstLocal.2.1).symm
  have hSecondInverse :
      finiteThroatGeneratorPatchToShiftedStereographic
          period hPeriod patch shift pole piece second =
        localInverse second := by
    apply shiftedStereographicToFiniteThroatGeneratorPatch_injOn
      period hPeriod patch shift pole
    · exact
        ⟨shiftedStereographicAmbientPiece_subset_strip
            period hPeriod shift pole piece
            (finiteThroatGeneratorPatchToShiftedStereographic_mem
              period hPeriod patch shift pole secondImage),
          shiftedStereographicAmbientPiece_subset_chartSource
            period hPeriod patch shift pole hPiecePatch
            (finiteThroatGeneratorPatchToShiftedStereographic_mem
              period hPeriod patch shift pole secondImage)⟩
    · exact ⟨secondLocal.2.2.1, secondLocal.2.2.2⟩
    · calc
        transition
            (finiteThroatGeneratorPatchToShiftedStereographic
              period hPeriod patch shift pole piece second) =
          second :=
            shiftedStereographicToFiniteThroatGeneratorPatch_inverse
              period hPeriod patch shift pole secondImage
        _ = transition (localInverse second) :=
          (hLocal.localInverse_right_inv secondLocal.2.1).symm
  simpa [hFirstInverse, hSecondInverse] using
    hLipschitz.dist_le_mul
      first firstLocal.1 second secondLocal.1

/-! ## Exact local measure transport -/

theorem finiteThroatGeneratorPatchAmbientHilbertCoordinate_continuousOn
    (patch : Patch period hPeriod) :
    ContinuousOn
      (finiteThroatGeneratorPatchAmbientHilbertCoordinate
        period hPeriod patch)
      (finiteThroatGeneratorClosedPatch
        period hPeriod patch) := by
  apply
    canonicalThroatChartHilbertEquivCoverCoordinates.symm.continuous
      |>.comp_continuousOn
  apply (continuousOn_extChartAt patch.1).mono
  intro point hPoint
  rw [extChartAt_source,
    ← finiteThroatGeneratorOpenPatch_eq_chart_source
      period hPeriod patch]
  exact finiteThroatGeneratorClosedPatch_subset_openPatch
    period hPeriod patch hPoint

theorem finiteThroatGeneratorPatchAmbientHilbertCoordinate_injOn
    (patch : Patch period hPeriod) :
    Set.InjOn
      (finiteThroatGeneratorPatchAmbientHilbertCoordinate
        period hPeriod patch)
      (finiteThroatGeneratorClosedPatch
        period hPeriod patch) := by
  intro first hFirst second hSecond hEqual
  apply (extChartAt throatCoverModelWithCorners patch.1).injOn
  · rw [extChartAt_source,
      ← finiteThroatGeneratorOpenPatch_eq_chart_source
        period hPeriod patch]
    exact finiteThroatGeneratorClosedPatch_subset_openPatch
      period hPeriod patch hFirst
  · rw [extChartAt_source,
      ← finiteThroatGeneratorOpenPatch_eq_chart_source
        period hPeriod patch]
    exact finiteThroatGeneratorClosedPatch_subset_openPatch
      period hPeriod patch hSecond
  · exact canonicalThroatChartHilbertEquivCoverCoordinates.symm.injective
      (by simpa [finiteThroatGeneratorPatchAmbientHilbertCoordinate] using hEqual)

theorem finiteThroatGeneratorPatchCanonicalCoordinateMeasure_eq_map_ambient
    (patch : Patch period hPeriod) :
    finiteThroatGeneratorPatchCanonicalCoordinateMeasure
        period hPeriod patch =
      Measure.map
        (finiteThroatGeneratorPatchAmbientHilbertCoordinate
          period hPeriod patch)
        ((intrinsicCanonicalThroatVolumeMeasure
          period hPeriod).restrict
            (finiteThroatGeneratorClosedPatch
              period hPeriod patch)) := by
  let sourceMeasure :=
    finiteThroatGeneratorPatchCanonicalSourceMeasure
      period hPeriod patch
  have hAmbientAE :
      AEMeasurable
        (finiteThroatGeneratorPatchAmbientHilbertCoordinate
          period hPeriod patch)
        (Measure.map
          (Subtype.val :
            FiniteThroatGeneratorPatchDomain period hPeriod patch →
              EffectiveThroat period hPeriod)
          sourceMeasure) := by
    rw [finiteThroatGeneratorPatchCanonicalSourceMeasure_map_subtype]
    exact
      (finiteThroatGeneratorPatchAmbientHilbertCoordinate_continuousOn
        period hPeriod patch).aemeasurable
          (finiteThroatGeneratorClosedPatch_isClosed
            period hPeriod patch).measurableSet
  have hMapMap :=
    hAmbientAE.map_map_of_aemeasurable
      (measurable_subtype_coe.aemeasurable :
        AEMeasurable
          (Subtype.val :
            FiniteThroatGeneratorPatchDomain period hPeriod patch →
              EffectiveThroat period hPeriod)
          sourceMeasure)
  calc
    finiteThroatGeneratorPatchCanonicalCoordinateMeasure
        period hPeriod patch =
      Measure.map
        (finiteThroatGeneratorPatchHilbertCoordinate
          period hPeriod patch) sourceMeasure := rfl
    _ = Measure.map
        (finiteThroatGeneratorPatchAmbientHilbertCoordinate
            period hPeriod patch ∘ Subtype.val)
        sourceMeasure := by
      congr 1
    _ = Measure.map
        (finiteThroatGeneratorPatchAmbientHilbertCoordinate
          period hPeriod patch)
        (Measure.map
          (Subtype.val :
            FiniteThroatGeneratorPatchDomain period hPeriod patch →
              EffectiveThroat period hPeriod)
          sourceMeasure) := hMapMap.symm
    _ = Measure.map
        (finiteThroatGeneratorPatchAmbientHilbertCoordinate
          period hPeriod patch)
        ((intrinsicCanonicalThroatVolumeMeasure
          period hPeriod).restrict
            (finiteThroatGeneratorClosedPatch
              period hPeriod patch)) := by
      rw [finiteThroatGeneratorPatchCanonicalSourceMeasure_map_subtype]

theorem finiteThroatGeneratorPatchCanonicalCoordinateMeasure_restrict_piece
    (patch : Patch period hPeriod)
    {piece : Set (EffectiveThroat period hPeriod)}
    (hPieceCompact : IsCompact piece)
    (hPiecePatch :
      piece ⊆ finiteThroatGeneratorClosedPatch
        period hPeriod patch) :
    (finiteThroatGeneratorPatchCanonicalCoordinateMeasure
        period hPeriod patch).restrict
          (finiteThroatGeneratorPatchAmbientHilbertCoordinate
            period hPeriod patch '' piece) =
      Measure.map
        (finiteThroatGeneratorPatchAmbientHilbertCoordinate
          period hPeriod patch)
        ((intrinsicCanonicalThroatVolumeMeasure
          period hPeriod).restrict piece) := by
  let closedPatch :=
    finiteThroatGeneratorClosedPatch
      period hPeriod patch
  let coordinateMap :=
    finiteThroatGeneratorPatchAmbientHilbertCoordinate
      period hPeriod patch
  have hPieceMeasurable : MeasurableSet piece :=
    hPieceCompact.isClosed.measurableSet
  have hImageCompact : IsCompact (coordinateMap '' piece) :=
    hPieceCompact.image_of_continuousOn
      ((finiteThroatGeneratorPatchAmbientHilbertCoordinate_continuousOn
        period hPeriod patch).mono hPiecePatch)
  have hAmbientAE :
      AEMeasurable coordinateMap
        ((intrinsicCanonicalThroatVolumeMeasure
          period hPeriod).restrict closedPatch) :=
    (finiteThroatGeneratorPatchAmbientHilbertCoordinate_continuousOn
      period hPeriod patch).aemeasurable
        (finiteThroatGeneratorClosedPatch_isClosed
          period hPeriod patch).measurableSet
  rw [finiteThroatGeneratorPatchCanonicalCoordinateMeasure_eq_map_ambient]
  rw [Measure.restrict_map_of_aemeasurable
    hAmbientAE hImageCompact.isClosed.measurableSet]
  congr 1
  rw [Measure.restrict_restrict₀
    (hAmbientAE.nullMeasurable hImageCompact.isClosed.measurableSet)]
  congr 1
  apply Set.Subset.antisymm
  · rintro point ⟨⟨imagePoint, hImagePoint, hEqual⟩, hPointPatch⟩
    have hPointEqual : point = imagePoint :=
      finiteThroatGeneratorPatchAmbientHilbertCoordinate_injOn
        period hPeriod patch hPointPatch
          (hPiecePatch hImagePoint) hEqual.symm
    rwa [hPointEqual]
  · intro point hPoint
    exact ⟨⟨point, hPoint, rfl⟩, hPiecePatch hPoint⟩

theorem shiftedTransition_image_eq_patchCoordinate_image
    (patch : Patch period hPeriod)
    (shift : Real)
    (pole : StandardSphere)
    {piece : Set (EffectiveThroat period hPeriod)}
    (hPieceRange :
      piece ⊆ Set.range
        (shiftedThroatInteriorStereographicPhysicalMap
          period hPeriod shift pole)) :
    shiftedStereographicToFiniteThroatGeneratorPatch
          period hPeriod patch shift pole ''
        shiftedStereographicAmbientPiece
          period hPeriod shift pole piece =
      finiteThroatGeneratorPatchAmbientHilbertCoordinate
          period hPeriod patch ''
        piece := by
  calc
    shiftedStereographicToFiniteThroatGeneratorPatch
          period hPeriod patch shift pole ''
        shiftedStereographicAmbientPiece
          period hPeriod shift pole piece =
      finiteThroatGeneratorPatchAmbientHilbertCoordinate
          period hPeriod patch ''
        (shiftedThroatStereographicPhysicalMapAmbient
            period hPeriod shift pole ''
          shiftedStereographicAmbientPiece
            period hPeriod shift pole piece) := by
      rw [Set.image_image]
      rfl
    _ = finiteThroatGeneratorPatchAmbientHilbertCoordinate
          period hPeriod patch '' piece := by
      rw [shiftedThroatStereographicPhysicalMapAmbient_image_ambientPiece
        period hPeriod shift pole hPieceRange]

theorem map_stereographicInclusion_restrict_piece
    (shift : Real)
    (pole : StandardSphere)
    (piece : Set (EffectiveThroat period hPeriod)) :
    Measure.map
        (throatInteriorStereographicCoordinateInclusion period)
        ((throatInteriorStereographicMeasure
          period pole).restrict
            (shiftedThroatInteriorStereographicPhysicalMap
              period hPeriod shift pole ⁻¹' piece)) =
      (stereographicProductCoordinateMeasure pole).restrict
        (shiftedStereographicAmbientPiece
          period hPeriod shift pole piece) := by
  have hRestricted :=
    (throatInteriorStereographicCoordinateInclusion_measurePreserving
      period pole).restrict_image_emb
        (throatInteriorStereographicCoordinateInclusion_isOpenEmbedding
          period).measurableEmbedding
        (shiftedThroatInteriorStereographicPhysicalMap
          period hPeriod shift pole ⁻¹' piece)
  calc
    Measure.map
        (throatInteriorStereographicCoordinateInclusion period)
        ((throatInteriorStereographicMeasure
          period pole).restrict
            (shiftedThroatInteriorStereographicPhysicalMap
              period hPeriod shift pole ⁻¹' piece)) =
      ((stereographicProductCoordinateMeasure pole).restrict
        (Set.range
          (throatInteriorStereographicCoordinateInclusion
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
    {piece : Set (EffectiveThroat period hPeriod)}
    (hPieceRange :
      piece ⊆ Set.range
        (shiftedThroatInteriorStereographicPhysicalMap
          period hPeriod shift pole)) :
    Measure.map
        (shiftedThroatInteriorStereographicPhysicalMap
          period hPeriod shift pole)
        ((throatInteriorStereographicMeasure
          period pole).restrict
            (shiftedThroatInteriorStereographicPhysicalMap
              period hPeriod shift pole ⁻¹' piece)) =
      (intrinsicCanonicalThroatVolumeMeasure
        period hPeriod).restrict piece := by
  have hRestricted :=
    (shiftedThroatInteriorStereographicPhysicalMap_measurePreserving
      period hPeriod shift pole).restrict_image_emb
        (shiftedThroatInteriorStereographicPhysicalMap_isOpenEmbedding
          period hPeriod shift pole).measurableEmbedding
        (shiftedThroatInteriorStereographicPhysicalMap
          period hPeriod shift pole ⁻¹' piece)
  have hImage :
      shiftedThroatInteriorStereographicPhysicalMap
          period hPeriod shift pole ''
        (shiftedThroatInteriorStereographicPhysicalMap
          period hPeriod shift pole ⁻¹' piece) =
      piece :=
    Set.image_preimage_eq_of_subset hPieceRange
  calc
    Measure.map
        (shiftedThroatInteriorStereographicPhysicalMap
          period hPeriod shift pole)
        ((throatInteriorStereographicMeasure
          period pole).restrict
            (shiftedThroatInteriorStereographicPhysicalMap
              period hPeriod shift pole ⁻¹' piece)) =
      ((intrinsicCanonicalThroatVolumeMeasure
        period hPeriod).restrict
          (Set.range
            (shiftedThroatInteriorStereographicPhysicalMap
              period hPeriod shift pole))).restrict piece := by
      simpa [hImage] using hRestricted.map_eq
    _ = (intrinsicCanonicalThroatVolumeMeasure
        period hPeriod).restrict piece :=
      Measure.restrict_restrict_of_subset hPieceRange

/-- Exact pushforward of the local stereographic product measure through the
transition to the fixed Hilbert coordinates. -/
theorem map_shiftedTransition_surfaceMeasure
    (patch : Patch period hPeriod)
    (shift : Real)
    (pole : StandardSphere)
    {piece : Set (EffectiveThroat period hPeriod)}
    (hPieceCompact : IsCompact piece)
    (hPiecePatch :
      piece ⊆ finiteThroatGeneratorClosedPatch
        period hPeriod patch)
    (hPieceRange :
      piece ⊆ Set.range
        (shiftedThroatInteriorStereographicPhysicalMap
          period hPeriod shift pole)) :
    Measure.map
        (shiftedStereographicToFiniteThroatGeneratorPatch
          period hPeriod patch shift pole)
        ((stereographicProductCoordinateMeasure pole).restrict
          (shiftedStereographicAmbientPiece
            period hPeriod shift pole piece)) =
      (finiteThroatGeneratorPatchCanonicalCoordinateMeasure
        period hPeriod patch).restrict
          (shiftedStereographicToFiniteThroatGeneratorPatch
              period hPeriod patch shift pole ''
            shiftedStereographicAmbientPiece
              period hPeriod shift pole piece) := by
  let sourceMeasure :=
    (throatInteriorStereographicMeasure
      period pole).restrict
        (shiftedThroatInteriorStereographicPhysicalMap
          period hPeriod shift pole ⁻¹' piece)
  let ambientPiece :=
    shiftedStereographicAmbientPiece
      period hPeriod shift pole piece
  let transition :=
    shiftedStereographicToFiniteThroatGeneratorPatch
      period hPeriod patch shift pole
  let coordinateMap :=
    finiteThroatGeneratorPatchAmbientHilbertCoordinate
      period hPeriod patch
  have hInclusionMap :
      Measure.map
          (throatInteriorStereographicCoordinateInclusion period)
          sourceMeasure =
        (stereographicProductCoordinateMeasure pole).restrict
          ambientPiece :=
    map_stereographicInclusion_restrict_piece
      period hPeriod shift pole piece
  have hPhysicalMap :
      Measure.map
          (shiftedThroatInteriorStereographicPhysicalMap
            period hPeriod shift pole)
          sourceMeasure =
        (intrinsicCanonicalThroatVolumeMeasure
          period hPeriod).restrict piece :=
    map_shiftedStereographic_restrict_piece
      period hPeriod shift pole hPieceRange
  obtain ⟨forwardConstant, hForward⟩ :=
    exists_shiftedStereographicToFiniteThroatGeneratorPatch_lipschitzOn
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
          (throatInteriorStereographicCoordinateInclusion period)
          sourceMeasure) := by
    rwa [hInclusionMap]
  have hCoordinateAE :
      AEMeasurable coordinateMap
        ((intrinsicCanonicalThroatVolumeMeasure
          period hPeriod).restrict piece) :=
    ((finiteThroatGeneratorPatchAmbientHilbertCoordinate_continuousOn
      period hPeriod patch).mono hPiecePatch).aemeasurable
        hPieceCompact.isClosed.measurableSet
  have hCoordinateAE' :
      AEMeasurable coordinateMap
        (Measure.map
          (shiftedThroatInteriorStereographicPhysicalMap
            period hPeriod shift pole)
          sourceMeasure) := by
    rwa [hPhysicalMap]
  have hInclusionMapMap :=
    hTransitionAE'.map_map_of_aemeasurable
      ((throatInteriorStereographicCoordinateInclusion_isOpenEmbedding
        period).continuous.measurable.aemeasurable.restrict)
  have hPhysicalMapMap :=
    hCoordinateAE'.map_map_of_aemeasurable
      ((shiftedThroatInteriorStereographicPhysicalMap_isOpenEmbedding
        period hPeriod shift pole).continuous.measurable.aemeasurable.restrict)
  calc
    Measure.map transition
        ((stereographicProductCoordinateMeasure pole).restrict
          ambientPiece) =
      Measure.map transition
        (Measure.map
          (throatInteriorStereographicCoordinateInclusion period)
          sourceMeasure) := by rw [hInclusionMap]
    _ = Measure.map
        (transition ∘
          throatInteriorStereographicCoordinateInclusion period)
        sourceMeasure := hInclusionMapMap
    _ = Measure.map
        (coordinateMap ∘
          shiftedThroatInteriorStereographicPhysicalMap
            period hPeriod shift pole)
        sourceMeasure := by
      congr 1
    _ = Measure.map coordinateMap
        (Measure.map
          (shiftedThroatInteriorStereographicPhysicalMap
            period hPeriod shift pole)
          sourceMeasure) := hPhysicalMapMap.symm
    _ = Measure.map coordinateMap
        ((intrinsicCanonicalThroatVolumeMeasure
          period hPeriod).restrict piece) := by rw [hPhysicalMap]
    _ = (finiteThroatGeneratorPatchCanonicalCoordinateMeasure
        period hPeriod patch).restrict
          (coordinateMap '' piece) :=
      (finiteThroatGeneratorPatchCanonicalCoordinateMeasure_restrict_piece
        period hPeriod patch hPieceCompact hPiecePatch).symm
    _ = (finiteThroatGeneratorPatchCanonicalCoordinateMeasure
        period hPeriod patch).restrict
          (transition '' ambientPiece) := by
      rw [shiftedTransition_image_eq_patchCoordinate_image
        period hPeriod patch shift pole hPieceRange]

/-! ## Quantitative comparison on one compact overlap -/

structure FiniteThroatGeneratorPatchPieceCanonicalLebesgueComparison
    (patch : Patch period hPeriod)
    (shift : Real)
    (pole : StandardSphere)
    (piece : Set (EffectiveThroat period hPeriod)) where
  lebesgueBound : ENNReal
  lebesgueBound_ne_top : lebesgueBound ≠ ⊤
  lebesgue_le_canonical :
    (volume : Measure CanonicalThroatChartHilbertCoordinates).restrict
        (shiftedStereographicToFiniteThroatGeneratorPatch
            period hPeriod patch shift pole ''
          shiftedStereographicAmbientPiece
            period hPeriod shift pole piece) ≤
      lebesgueBound •
        (finiteThroatGeneratorPatchCanonicalCoordinateMeasure
          period hPeriod patch).restrict
            (shiftedStereographicToFiniteThroatGeneratorPatch
                period hPeriod patch shift pole ''
              shiftedStereographicAmbientPiece
                period hPeriod shift pole piece)
  canonicalBound : ENNReal
  canonicalBound_ne_top : canonicalBound ≠ ⊤
  canonical_le_lebesgue :
    (finiteThroatGeneratorPatchCanonicalCoordinateMeasure
        period hPeriod patch).restrict
          (shiftedStereographicToFiniteThroatGeneratorPatch
              period hPeriod patch shift pole ''
            shiftedStereographicAmbientPiece
              period hPeriod shift pole piece) ≤
      canonicalBound •
        (volume : Measure CanonicalThroatChartHilbertCoordinates).restrict
          (shiftedStereographicToFiniteThroatGeneratorPatch
              period hPeriod patch shift pole ''
            shiftedStereographicAmbientPiece
              period hPeriod shift pole piece)

/-- Every compact overlap piece has finite two-sided canonical/Lebesgue
comparison constants derived from its explicit smooth transition. -/
theorem finiteThroatGeneratorPatchPieceCanonicalLebesgueComparison_nonempty
    (patch : Patch period hPeriod)
    (shift : Real)
    (pole : StandardSphere)
    {piece : Set (EffectiveThroat period hPeriod)}
    (hPieceCompact : IsCompact piece)
    (hPiecePatch :
      piece ⊆ finiteThroatGeneratorClosedPatch
        period hPeriod patch)
    (hPieceRange :
      piece ⊆ Set.range
        (shiftedThroatInteriorStereographicPhysicalMap
          period hPeriod shift pole)) :
    Nonempty
      (FiniteThroatGeneratorPatchPieceCanonicalLebesgueComparison
        period hPeriod patch shift pole piece) := by
  classical
  let sourceSupport :=
    shiftedStereographicAmbientPiece
      period hPeriod shift pole piece
  let transition :=
    shiftedStereographicToFiniteThroatGeneratorPatch
      period hPeriod patch shift pole
  let inverse :=
    finiteThroatGeneratorPatchToShiftedStereographic
      period hPeriod patch shift pole piece
  let targetSupport := transition '' sourceSupport
  let sourceLebesgue :=
    (volume : Measure ThroatCoverCoordinates).restrict sourceSupport
  let sourceSurface :=
    (stereographicProductCoordinateMeasure pole).restrict sourceSupport
  let targetLebesgue :=
    (volume : Measure CanonicalThroatChartHilbertCoordinates).restrict
      targetSupport
  let targetCanonical :=
    (finiteThroatGeneratorPatchCanonicalCoordinateMeasure
      period hPeriod patch).restrict targetSupport
  have hSourceCompact : IsCompact sourceSupport :=
    shiftedStereographicAmbientPiece_isCompact
      period hPeriod shift pole hPieceCompact hPieceRange
  have hSourceMeasurable : MeasurableSet sourceSupport :=
    hSourceCompact.isClosed.measurableSet
  obtain ⟨forwardConstant, hForwardLipschitz⟩ :=
    exists_shiftedStereographicToFiniteThroatGeneratorPatch_lipschitzOn
      period hPeriod patch shift pole
      hPieceCompact hPiecePatch hPieceRange
  obtain ⟨inverseConstant, hInverseLipschitz⟩ :=
    exists_finiteThroatGeneratorPatchToShiftedStereographic_lipschitzOn
      period hPeriod patch shift pole
      hPieceCompact hPiecePatch hPieceRange
  have hTargetCompact : IsCompact targetSupport :=
    hSourceCompact.image_of_continuousOn
      hForwardLipschitz.continuousOn
  have hTargetMeasurable : MeasurableSet targetSupport :=
    hTargetCompact.isClosed.measurableSet
  obtain ⟨forwardBound, hForwardBound, hForwardVolumes⟩ :=
    P0EFTJanusMappingTorusCanonicalPhysicalScalarStereographicVolumeComparison4D.exists_volume_image_le_of_lipschitzOn_of_finrank
      (dimension := 3)
      (Source := ThroatCoverCoordinates)
      (Target := CanonicalThroatChartHilbertCoordinates)
      (by simp [ThroatCoverCoordinates])
      (by simp [CanonicalThroatChartHilbertCoordinates])
      hForwardLipschitz
  obtain ⟨inverseBound, hInverseBound, hInverseVolumes⟩ :=
    P0EFTJanusMappingTorusCanonicalPhysicalScalarStereographicVolumeComparison4D.exists_volume_image_le_of_lipschitzOn_of_finrank
      (dimension := 3)
      (Source := CanonicalThroatChartHilbertCoordinates)
      (Target := ThroatCoverCoordinates)
      (by simp [CanonicalThroatChartHilbertCoordinates])
      (by simp [ThroatCoverCoordinates])
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
  have hForwardImage (subset : Set CanonicalThroatChartHilbertCoordinates) :
      transition '' (transition ⁻¹' subset ∩ sourceSupport) =
        subset ∩ targetSupport := by
    ext coordinate
    constructor
    · rintro ⟨source, ⟨hSourceSubset, hSourceSupport⟩, rfl⟩
      exact ⟨hSourceSubset, ⟨source, hSourceSupport, rfl⟩⟩
    · rintro ⟨hCoordinateSubset, source, hSourceSupport, rfl⟩
      exact
        ⟨source, ⟨hCoordinateSubset, hSourceSupport⟩, rfl⟩
  have hInverseImage (subset : Set CanonicalThroatChartHilbertCoordinates) :
      inverse '' (subset ∩ targetSupport) =
        transition ⁻¹' subset ∩ sourceSupport := by
    ext coordinate
    constructor
    · rintro ⟨imageCoordinate,
        ⟨hImageSubset, source, hSourceSupport, rfl⟩, rfl⟩
      have hInverse :
          inverse (transition source) = source := by
        simpa [inverse, transition] using
          (finiteThroatGeneratorPatchToShiftedStereographic_transition
            period hPeriod patch shift pole hPiecePatch hSourceSupport)
      rw [hInverse]
      exact ⟨hImageSubset, hSourceSupport⟩
    · rintro ⟨hCoordinateSubset, hCoordinateSupport⟩
      refine
        ⟨transition coordinate,
          ⟨hCoordinateSubset,
            ⟨coordinate, hCoordinateSupport, rfl⟩⟩, ?_⟩
      simpa [inverse, transition] using
        (finiteThroatGeneratorPatchToShiftedStereographic_transition
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
def finiteThroatGeneratorPatchPieceCanonicalLebesgueComparison
    (patch : Patch period hPeriod)
    (shift : Real)
    (pole : StandardSphere)
    {piece : Set (EffectiveThroat period hPeriod)}
    (hPieceCompact : IsCompact piece)
    (hPiecePatch :
      piece ⊆ finiteThroatGeneratorClosedPatch
        period hPeriod patch)
    (hPieceRange :
      piece ⊆ Set.range
        (shiftedThroatInteriorStereographicPhysicalMap
          period hPeriod shift pole)) :
    FiniteThroatGeneratorPatchPieceCanonicalLebesgueComparison
      period hPeriod patch shift pole piece :=
  Classical.choice
    (finiteThroatGeneratorPatchPieceCanonicalLebesgueComparison_nonempty
      period hPeriod patch shift pole
      hPieceCompact hPiecePatch hPieceRange)

/-! ## Finite aggregation on one throat-generator patch -/

theorem finiteThroatGeneratorPatchHilbertSupport_eq_image_ambient
    (patch : Patch period hPeriod) :
    finiteThroatGeneratorPatchHilbertSupport period hPeriod patch =
      finiteThroatGeneratorPatchAmbientHilbertCoordinate
          period hPeriod patch ''
        finiteThroatGeneratorClosedPatch
          period hPeriod patch := by
  rw [finiteThroatGeneratorPatchHilbertSupport,
    finiteThroatGeneratorPatchCoordinateSupport,
    Set.image_image]
  rfl

private theorem measuredChartCover_piece_subset_patch
    (patch : Patch period hPeriod)
    (cover : FiniteThroatGeneratorPatchMeasuredChartCover
      period hPeriod patch)
    {chart : Real × StandardSphere}
    (hChart : chart ∈ cover.charts) :
    cover.piece chart ⊆
      finiteThroatGeneratorClosedPatch
        period hPeriod patch := by
  rw [cover.covers]
  intro point hPoint
  exact Set.mem_iUnion.2
    ⟨chart, Set.mem_iUnion.2 ⟨hChart, hPoint⟩⟩

/-- The finitely many compact measured overlaps give the full two-sided
canonical/Lebesgue comparison on one actual throat-generator patch. -/
theorem finiteThroatGeneratorPatchCanonicalLebesgueComparison_nonempty
    (patch : Patch period hPeriod) :
    Nonempty
      (FiniteThroatGeneratorPatchCanonicalLebesgueComparison
        period hPeriod patch) := by
  classical
  let cover :=
    finiteThroatGeneratorPatchMeasuredChartCover
      period hPeriod patch
  let support :=
    finiteThroatGeneratorPatchHilbertSupport
      period hPeriod patch
  let targetPiece :
      ↥cover.charts → Set CanonicalThroatChartHilbertCoordinates :=
    fun chart =>
      finiteThroatGeneratorPatchAmbientHilbertCoordinate
          period hPeriod patch ''
        cover.piece chart.1
  have hPiecePatch (chart : ↥cover.charts) :
      cover.piece chart.1 ⊆
        finiteThroatGeneratorClosedPatch
          period hPeriod patch :=
    measuredChartCover_piece_subset_patch
      period hPeriod patch cover chart.2
  let comparison
      (chart : ↥cover.charts) :
      FiniteThroatGeneratorPatchPieceCanonicalLebesgueComparison
        period hPeriod patch chart.1.1 chart.1.2
          (cover.piece chart.1) :=
    finiteThroatGeneratorPatchPieceCanonicalLebesgueComparison
      period hPeriod patch chart.1.1 chart.1.2
      (cover.piece_isCompact chart.1)
      (hPiecePatch chart)
      (cover.piece_subset_chart chart.1)
  have hTransitionTarget (chart : ↥cover.charts) :
      shiftedStereographicToFiniteThroatGeneratorPatch
            period hPeriod patch chart.1.1 chart.1.2 ''
          shiftedStereographicAmbientPiece
            period hPeriod chart.1.1 chart.1.2
              (cover.piece chart.1) =
        targetPiece chart := by
    change
      shiftedStereographicToFiniteThroatGeneratorPatch
            period hPeriod patch chart.1.1 chart.1.2 ''
          shiftedStereographicAmbientPiece
            period hPeriod chart.1.1 chart.1.2
              (cover.piece chart.1) =
        finiteThroatGeneratorPatchAmbientHilbertCoordinate
            period hPeriod patch ''
          cover.piece chart.1
    exact shiftedTransition_image_eq_patchCoordinate_image
      period hPeriod patch chart.1.1 chart.1.2
      (cover.piece_subset_chart chart.1)
  have hLocalLebesgue (chart : ↥cover.charts) :
      (volume : Measure CanonicalThroatChartHilbertCoordinates).restrict
          (targetPiece chart) ≤
        (comparison chart).lebesgueBound •
          (finiteThroatGeneratorPatchCanonicalCoordinateMeasure
            period hPeriod patch).restrict
              (targetPiece chart) := by
    rw [← hTransitionTarget chart]
    exact (comparison chart).lebesgue_le_canonical
  have hLocalCanonical (chart : ↥cover.charts) :
      (finiteThroatGeneratorPatchCanonicalCoordinateMeasure
          period hPeriod patch).restrict
            (targetPiece chart) ≤
        (comparison chart).canonicalBound •
          (volume : Measure
            CanonicalThroatChartHilbertCoordinates).restrict
              (targetPiece chart) := by
    rw [← hTransitionTarget chart]
    exact (comparison chart).canonical_le_lebesgue
  have hSupport :
      support = ⋃ chart : ↥cover.charts, targetPiece chart := by
    change
      finiteThroatGeneratorPatchHilbertSupport period hPeriod patch =
        ⋃ chart : ↥cover.charts, targetPiece chart
    rw [finiteThroatGeneratorPatchHilbertSupport_eq_image_ambient,
      cover.covers]
    ext coordinate
    simp only [Set.mem_image, Set.mem_iUnion]
    constructor
    · rintro ⟨point, ⟨chart, hChart, hPiece⟩, rfl⟩
      refine ⟨⟨chart, hChart⟩, ?_⟩
      change
        finiteThroatGeneratorPatchAmbientHilbertCoordinate
              period hPeriod patch point ∈
          finiteThroatGeneratorPatchAmbientHilbertCoordinate
              period hPeriod patch ''
            cover.piece chart
      exact ⟨point, hPiece, rfl⟩
    · rintro ⟨chart, hCoordinate⟩
      change
        coordinate ∈
          finiteThroatGeneratorPatchAmbientHilbertCoordinate
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
      (μ : Measure CanonicalThroatChartHilbertCoordinates)
      (subset : Set CanonicalThroatChartHilbertCoordinates)
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
          CanonicalThroatChartHilbertCoordinates).restrict support subset ≤
          ∑ chart : ↥cover.charts,
            (volume : Measure
              CanonicalThroatChartHilbertCoordinates).restrict
                (targetPiece chart) subset :=
        hRestrictSupportApply_le_sum volume subset hSubset
      _ ≤ ∑ chart : ↥cover.charts,
          (comparison chart).lebesgueBound *
            (finiteThroatGeneratorPatchCanonicalCoordinateMeasure
              period hPeriod patch).restrict
                (targetPiece chart) subset := by
        apply Finset.sum_le_sum
        intro chart _
        simpa only [Measure.smul_apply, smul_eq_mul] using
          (hLocalLebesgue chart subset)
      _ ≤ ∑ chart : ↥cover.charts,
          (comparison chart).lebesgueBound *
            finiteThroatGeneratorPatchCanonicalCoordinateMeasure
              period hPeriod patch subset := by
        apply Finset.sum_le_sum
        intro chart _
        exact mul_le_mul_left'
          (Measure.restrict_le_self subset)
          (comparison chart).lebesgueBound
      _ =
          (∑ chart : ↥cover.charts,
            (comparison chart).lebesgueBound) *
              finiteThroatGeneratorPatchCanonicalCoordinateMeasure
                period hPeriod patch subset := by
        rw [Finset.sum_mul]
  · rw [← finiteThroatGeneratorPatchCanonicalCoordinateMeasure_restrict_support
      period hPeriod patch]
    apply Measure.le_iff.2
    intro subset hSubset
    rw [Measure.smul_apply, smul_eq_mul]
    calc
      (finiteThroatGeneratorPatchCanonicalCoordinateMeasure
          period hPeriod patch).restrict support subset ≤
          ∑ chart : ↥cover.charts,
            (finiteThroatGeneratorPatchCanonicalCoordinateMeasure
              period hPeriod patch).restrict
                (targetPiece chart) subset :=
        hRestrictSupportApply_le_sum
          (finiteThroatGeneratorPatchCanonicalCoordinateMeasure
            period hPeriod patch) subset hSubset
      _ ≤ ∑ chart : ↥cover.charts,
          (comparison chart).canonicalBound *
            (volume : Measure
              CanonicalThroatChartHilbertCoordinates).restrict
                (targetPiece chart) subset := by
        apply Finset.sum_le_sum
        intro chart _
        simpa only [Measure.smul_apply, smul_eq_mul] using
          (hLocalCanonical chart subset)
      _ ≤ ∑ chart : ↥cover.charts,
          (comparison chart).canonicalBound *
            (volume : Measure
              CanonicalThroatChartHilbertCoordinates).restrict
                support subset := by
        apply Finset.sum_le_sum
        intro chart _
        exact mul_le_mul_left'
          ((Measure.restrict_mono_set
            (volume : Measure CanonicalThroatChartHilbertCoordinates)
            (hTargetPieceSubset chart)) subset)
          (comparison chart).canonicalBound
      _ =
          (∑ chart : ↥cover.charts,
            (comparison chart).canonicalBound) *
              (volume : Measure
                CanonicalThroatChartHilbertCoordinates).restrict
                  support subset := by
        rw [Finset.sum_mul]

/-- Chosen global canonical/Lebesgue comparison on every actual compact
throat-generator patch. -/
def finiteThroatGeneratorPatchCanonicalLebesgueComparison
    (patch : Patch period hPeriod) :
    FiniteThroatGeneratorPatchCanonicalLebesgueComparison
      period hPeriod patch :=
  Classical.choice
    (finiteThroatGeneratorPatchCanonicalLebesgueComparison_nonempty
      period hPeriod patch)

end
end P0EFTJanusProgramPT12LLCanonicalThroatFinitePatchVolumeComparison4D
end JanusFormal
