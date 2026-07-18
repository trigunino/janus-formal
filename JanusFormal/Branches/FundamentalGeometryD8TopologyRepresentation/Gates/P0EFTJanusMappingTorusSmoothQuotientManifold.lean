import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusSmoothQuotient

/-!
# Smooth manifolds on the effective mapping-torus quotients

This gate installs the covering-induced smooth structures whose transition
functions are the smooth integer deck transformations proved in the preceding
gate.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusSmoothQuotientManifold

set_option autoImplicit false

noncomputable section

open Set Metric Topology
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient

section LocalSections

variable {X : Type*} [TopologicalSpace X] [T2Space X]
  [LocallyCompactSpace X]

private abbrev projectionIsLocalHomeomorph (data : MappingTorusData X) :
    IsLocalHomeomorph (mappingTorusMk data) :=
  (mappingTorusMk_isCoveringMap data).isLocalHomeomorph

omit [T2Space X] [LocallyCompactSpace X] in
private theorem mappingTorusMk_vadd
    (data : MappingTorusData X) (winding : ℤ)
    (point : MappingTorusCover data) :
    mappingTorusMk data (winding +ᵥ point) = mappingTorusMk data point :=
  (mappingTorusMk_eq_iff_exists_vadd data _ _).2 ⟨winding, rfl⟩

/-- Local inverses based at arbitrary covering points which are simultaneously
defined at a quotient point differ locally by the deck transformation joining
their values there. -/
theorem localInverseAt_eventuallyEq_vadd_of_mem
    (data : MappingTorusData X)
    (firstAnchor secondAnchor : MappingTorusCover data)
    (base : MappingTorus data)
    (hFirstSource : base ∈
      ((projectionIsLocalHomeomorph data).localInverseAt firstAnchor).source)
    (hSecondSource : base ∈
      ((projectionIsLocalHomeomorph data).localInverseAt secondAnchor).source)
    (winding : ℤ)
    (hWinding : winding +ᵥ
      (projectionIsLocalHomeomorph data).localInverseAt firstAnchor base =
      (projectionIsLocalHomeomorph data).localInverseAt secondAnchor base) :
    (projectionIsLocalHomeomorph data).localInverseAt secondAnchor =ᶠ[𝓝 base]
      (fun point => winding +ᵥ
        (projectionIsLocalHomeomorph data).localInverseAt firstAnchor point) := by
  let hf := projectionIsLocalHomeomorph data
  let firstSection := hf.localInverseAt firstAnchor
  let secondSection := hf.localInverseAt secondAnchor
  have hFirstSource' : firstSection.source ∈ 𝓝 base :=
    firstSection.open_source.mem_nhds hFirstSource
  have hSecondSource' : secondSection.source ∈ 𝓝 base :=
    secondSection.open_source.mem_nhds hSecondSource
  have hSecondContinuous : ContinuousAt secondSection base :=
    secondSection.continuousAt hSecondSource
  have hSecondTarget : secondSection ⁻¹' secondSection.target ∈ 𝓝 base := by
    apply hSecondContinuous.preimage_mem_nhds
    exact secondSection.open_target.mem_nhds (secondSection.map_source hSecondSource)
  have hFirstContinuous : ContinuousAt firstSection base :=
    firstSection.continuousAt hFirstSource
  have hDeckContinuous : ContinuousAt (fun point => winding +ᵥ firstSection point) base :=
    (continuous_const_vadd data winding).continuousAt.comp hFirstContinuous
  have hDeckTarget :
      (fun point => winding +ᵥ firstSection point) ⁻¹' secondSection.target ∈ 𝓝 base := by
    apply hDeckContinuous.preimage_mem_nhds
    rw [hWinding]
    exact secondSection.open_target.mem_nhds (secondSection.map_source hSecondSource)
  filter_upwards [hFirstSource', hSecondSource', hSecondTarget, hDeckTarget]
    with point hFirst hSecond hSecondTargetPoint hDeckTargetPoint
  apply hf.injOn_localInverseAt_target hSecondTargetPoint hDeckTargetPoint
  calc
    mappingTorusMk data (secondSection point) = point :=
      hf.apply_localInverseAt_of_mem hSecond
    _ = mappingTorusMk data (firstSection point) :=
      (hf.apply_localInverseAt_of_mem hFirst).symm
    _ = mappingTorusMk data (winding +ᵥ firstSection point) :=
      (mappingTorusMk_vadd data winding _).symm

end LocalSections

section SmoothDescent

variable {𝕜 E H X : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] [TopologicalSpace X] [T2Space X]
  [LocallyCompactSpace X]

variable (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)

/-- The quotient atlas induced from the specified atlas on the cover.  Its
topology is the existing orbit-quotient topology because the projection is the
same local homeomorphism. -/
@[implicit_reducible] def mappingTorusSmoothChartedSpace
    (data : MappingTorusData X)
    [ChartedSpace H (MappingTorusCover data)] :
    ChartedSpace H (MappingTorus data) :=
  (mappingTorusMk_isCoveringMap data).isLocalHomeomorph.chartedSpace
    (mappingTorusMk_surjective data)

/-- Coordinate changes between local-section charts based at arbitrary cover
points are smooth. -/
theorem localSectionChart_transition_mem_groupoid
    (data : MappingTorusData X)
    [ChartedSpace H (MappingTorusCover data)]
    [IsManifold I n (MappingTorusCover data)]
    (hDeck : ∀ winding : ℤ,
      ContMDiff I I n
        (winding +ᵥ · : MappingTorusCover data → MappingTorusCover data))
    (firstAnchor secondAnchor : MappingTorusCover data) :
    let hf := (mappingTorusMk_isCoveringMap data).isLocalHomeomorph
    ((hf.localInverseAt firstAnchor).trans (chartAt H firstAnchor)).symm.trans
      ((hf.localInverseAt secondAnchor).trans (chartAt H secondAnchor)) ∈
        contDiffGroupoid n I := by
  let hf := (mappingTorusMk_isCoveringMap data).isLocalHomeomorph
  let firstSection := hf.localInverseAt firstAnchor
  let secondSection := hf.localInverseAt secondAnchor
  let firstChart := chartAt H firstAnchor
  let secondChart := chartAt H secondAnchor
  let transition := (firstSection.trans firstChart).symm.trans
    (secondSection.trans secondChart)
  change transition ∈ contDiffGroupoid n I
  apply (contDiffGroupoid n I).locality
  intro coordinate hCoordinate
  have hCoordinate' := hCoordinate
  simp only [transition, firstSection, secondSection, firstChart, secondChart,
    mfld_simps] at hCoordinate'
  let base := firstSection.symm (firstChart.symm coordinate)
  let firstPoint := firstChart.symm coordinate
  let secondPoint := secondSection base
  have hFirstPointTarget : firstPoint ∈ firstSection.target :=
    hCoordinate'.1.2
  have hFirstSource : base ∈ firstSection.source := by
    exact firstSection.symm.map_source hFirstPointTarget
  have hSecondSource : base ∈ secondSection.source := hCoordinate'.2.1
  have hFirstValue : firstSection base = firstPoint := by
    exact firstSection.right_inv hFirstPointTarget
  have hProjection : mappingTorusMk data secondPoint =
      mappingTorusMk data firstPoint := by
    calc
      mappingTorusMk data secondPoint = base :=
        hf.apply_localInverseAt_of_mem hSecondSource
      _ = mappingTorusMk data (firstSection base) :=
        (hf.apply_localInverseAt_of_mem hFirstSource).symm
      _ = mappingTorusMk data firstPoint := congrArg _ hFirstValue
  obtain ⟨winding, hWinding⟩ :=
    (mappingTorusMk_eq_iff_exists_vadd data secondPoint firstPoint).1 hProjection
  have hWinding' : winding +ᵥ firstSection base = secondSection base := by
    rw [hFirstValue]
    exact hWinding
  have hSections := localInverseAt_eventuallyEq_vadd_of_mem data
    firstAnchor secondAnchor base hFirstSource hSecondSource winding hWinding'
  let deck : MappingTorusCover data ≃ₜ MappingTorusCover data :=
    Homeomorph.vadd winding
  let deckTransition := (firstChart.symm.trans deck.toOpenPartialHomeomorph).trans
    secondChart
  have hDeckForward : ContMDiff I I n deck := hDeck winding
  have hDeckBackward : ContMDiff I I n deck.symm := by
    exact (hDeck (-winding)).congr fun point => by
      simp [deck]
  have hDeckTransition : deckTransition ∈ contDiffGroupoid n I := by
    exact smoothHomeomorph_coordinateChange_mem_groupoid deck
      hDeckForward hDeckBackward (chart_mem_atlas H firstAnchor)
        (chart_mem_atlas H secondAnchor)
  have hCoordinateTarget : coordinate ∈
      (firstSection.trans firstChart).target := by
    simpa only [mfld_simps] using hCoordinate'.1
  have hInverseContinuous : ContinuousAt
      (firstSection.trans firstChart).symm coordinate :=
    (firstSection.trans firstChart).symm.continuousAt hCoordinateTarget
  have hSectionsCoordinate := hSections.comp_tendsto hInverseContinuous
  have hTransitionEq : transition =ᶠ[𝓝 coordinate] deckTransition := by
    filter_upwards [hSectionsCoordinate,
      (firstSection.trans firstChart).open_target.mem_nhds hCoordinateTarget]
      with point hPointEq hPointTarget
    simp only [transition, deckTransition, Function.comp_apply, mfld_simps]
    change secondSection (firstSection.symm (firstChart.symm point)) =
      winding +ᵥ firstSection (firstSection.symm (firstChart.symm point)) at hPointEq
    rw [hPointEq]
    have hPointTarget' := hPointTarget
    simp only [mfld_simps] at hPointTarget'
    rw [firstSection.right_inv hPointTarget'.2]
    rfl
  have hDeckCoordinate : coordinate ∈ deckTransition.source := by
    simp only [deckTransition, mfld_simps]
    constructor
    · exact hCoordinate'.1.1
    · change winding +ᵥ firstPoint ∈ secondChart.source
      rw [hWinding]
      exact hCoordinate'.2.2
  have hEqSet : {point | transition point = deckTransition point} ∈ 𝓝 coordinate :=
    hTransitionEq
  obtain ⟨smoothSet, hSmoothSubset, hSmoothOpen, hCoordinateSmooth⟩ :=
    mem_nhds_iff.mp hEqSet
  let localMap := deckTransition.restr smoothSet
  have hLocalMap : localMap ∈ contDiffGroupoid n I := by
    exact closedUnderRestriction' hDeckTransition hSmoothOpen
  have hCoordinateLocal : coordinate ∈ localMap.source := by
    simp only [localMap, mfld_simps]
    exact ⟨hDeckCoordinate, by simpa [hSmoothOpen.interior_eq] using hCoordinateSmooth⟩
  let neighborhood := transition.source ∩ localMap.source
  refine ⟨neighborhood, transition.open_source.inter localMap.open_source,
    ⟨hCoordinate, hCoordinateLocal⟩, ?_⟩
  have hEqualTransition : Set.EqOn transition localMap neighborhood := by
    intro point hPoint
    change transition point = deckTransition point
    apply hSmoothSubset
    have hLocalSource := hPoint.2
    simp only [localMap, mfld_simps] at hLocalSource
    exact interior_subset hLocalSource.2
  rw [OpenPartialHomeomorph.restr_source_inter]
  exact (contDiffGroupoid n I).mem_of_eqOnSource
    (closedUnderRestriction' hLocalMap transition.open_source)
    (OpenPartialHomeomorph.Set.EqOn.restr_eqOn_source hEqualTransition)

/-- Smooth deck transformations make the covering-induced quotient atlas a
`C^n` manifold atlas. -/
theorem mappingTorus_isManifold_of_smooth_deck
    (data : MappingTorusData X)
    [ChartedSpace H (MappingTorusCover data)]
    [IsManifold I n (MappingTorusCover data)]
    (hDeck : ∀ winding : ℤ,
      ContMDiff I I n
        (winding +ᵥ · : MappingTorusCover data → MappingTorusCover data)) :
    letI : ChartedSpace H (MappingTorus data) :=
      mappingTorusSmoothChartedSpace data
    IsManifold I n (MappingTorus data) := by
  letI : ChartedSpace H (MappingTorus data) :=
    mappingTorusSmoothChartedSpace data
  refine { compatible := ?_ }
  rintro first second ⟨firstBase, rfl⟩ ⟨secondBase, rfl⟩
  exact localSectionChart_transition_mem_groupoid I n data hDeck _ _

/-- Every local-section chart, not just the selected chart at a quotient point,
belongs to the maximal quotient atlas. -/
theorem localSectionChart_mem_maximalAtlas
    (data : MappingTorusData X)
    [ChartedSpace H (MappingTorusCover data)]
    [IsManifold I n (MappingTorusCover data)]
    (hDeck : ∀ winding : ℤ,
      ContMDiff I I n
        (winding +ᵥ · : MappingTorusCover data → MappingTorusCover data))
    (anchor : MappingTorusCover data) :
    letI : ChartedSpace H (MappingTorus data) :=
      mappingTorusSmoothChartedSpace data
    let hf := (mappingTorusMk_isCoveringMap data).isLocalHomeomorph
    (hf.localInverseAt anchor).trans (chartAt H anchor) ∈
      IsManifold.maximalAtlas I n (MappingTorus data) := by
  letI : ChartedSpace H (MappingTorus data) :=
    mappingTorusSmoothChartedSpace data
  letI : IsManifold I n (MappingTorus data) :=
    mappingTorus_isManifold_of_smooth_deck I n data hDeck
  dsimp only
  intro selectedChart hSelectedChart
  rcases hSelectedChart with ⟨selectedBase, rfl⟩
  constructor
  · exact localSectionChart_transition_mem_groupoid I n data hDeck anchor _
  · exact localSectionChart_transition_mem_groupoid I n data hDeck _ anchor

/-- A covering local inverse, restricted by the cover chart at its anchor, is
a genuine partial `C^n` diffeomorphism for the descended quotient atlas. -/
def mappingTorusLocalSectionPartialDiffeomorph
    (data : MappingTorusData X)
    [ChartedSpace H (MappingTorusCover data)]
    [IsManifold I n (MappingTorusCover data)]
    (hDeck : ∀ winding : ℤ,
      ContMDiff I I n
        (winding +ᵥ · : MappingTorusCover data → MappingTorusCover data))
    (anchor : MappingTorusCover data) :
    letI : ChartedSpace H (MappingTorus data) :=
      mappingTorusSmoothChartedSpace data
    PartialDiffeomorph I I (MappingTorus data) (MappingTorusCover data) n := by
  letI : ChartedSpace H (MappingTorus data) :=
    mappingTorusSmoothChartedSpace data
  letI : IsManifold I n (MappingTorus data) :=
    mappingTorus_isManifold_of_smooth_deck I n data hDeck
  let hf := (mappingTorusMk_isCoveringMap data).isLocalHomeomorph
  let quotientChart := (hf.localInverseAt anchor).trans (chartAt H anchor)
  let coverChart := chartAt H anchor
  let localHomeomorph := quotientChart.trans coverChart.symm
  have hQuotientChart : quotientChart ∈
      IsManifold.maximalAtlas I n (MappingTorus data) :=
    localSectionChart_mem_maximalAtlas I n data hDeck anchor
  have hCoverChart : coverChart ∈
      IsManifold.maximalAtlas I n (MappingTorusCover data) :=
    IsManifold.chart_mem_maximalAtlas anchor
  exact
    { __ := localHomeomorph
      contMDiffOn_toFun :=
        (contMDiffOn_symm_of_mem_maximalAtlas hCoverChart).comp
          ((contMDiffOn_of_mem_maximalAtlas hQuotientChart).mono inter_subset_left)
          inter_subset_right
      contMDiffOn_invFun :=
        (contMDiffOn_symm_of_mem_maximalAtlas hQuotientChart).comp
          ((contMDiffOn_of_mem_maximalAtlas hCoverChart).mono inter_subset_left)
          inter_subset_right }

/-- The quotient projection is a `C^n` local diffeomorphism for the descended
atlas. -/
theorem mappingTorus_projection_isLocalDiffeomorph
    (data : MappingTorusData X)
    [ChartedSpace H (MappingTorusCover data)]
    [IsManifold I n (MappingTorusCover data)]
    (hDeck : ∀ winding : ℤ,
      ContMDiff I I n
        (winding +ᵥ · : MappingTorusCover data → MappingTorusCover data)) :
    letI : ChartedSpace H (MappingTorus data) :=
      mappingTorusSmoothChartedSpace data
    IsLocalDiffeomorph I I n (mappingTorusMk data) := by
  letI : ChartedSpace H (MappingTorus data) :=
    mappingTorusSmoothChartedSpace data
  letI : IsManifold I n (MappingTorus data) :=
    mappingTorus_isManifold_of_smooth_deck I n data hDeck
  intro anchor
  let localSection :=
    mappingTorusLocalSectionPartialDiffeomorph I n data hDeck anchor
  refine ⟨localSection.symm, ?_, ?_⟩
  · simp [localSection, mappingTorusLocalSectionPartialDiffeomorph]
  · intro point hPoint
    simp [localSection, mappingTorusLocalSectionPartialDiffeomorph]
    let hf := (mappingTorusMk_isCoveringMap data).isLocalHomeomorph
    change point ∈ (((hf.localInverseAt anchor).trans
      (chartAt H anchor)).trans (chartAt H anchor).symm).target at hPoint
    simp only [mfld_simps] at hPoint
    rw [(chartAt H anchor).left_inv hPoint.1]

end SmoothDescent

section ReflectedSphereQuotients

open P0EFTJanusReflectionFixedThroat

variable (period : ℝ) (hPeriod : period ≠ 0)

/-- The covering-induced analytic atlas on the fixed-throat quotient. -/
@[implicit_reducible] def fixedThroatQuotientChartedSpace :
    ChartedSpace ThroatCoverModel
      (MappingTorus (fixedEquatorData period hPeriod)) := by
  letI : ChartedSpace ThroatCoverModel
      (MappingTorusCover (fixedEquatorData period hPeriod)) :=
    fixedThroatCoverChartedSpace period hPeriod
  exact mappingTorusSmoothChartedSpace (fixedEquatorData period hPeriod)

/-- The covering-induced analytic atlas on the reflected-sphere quotient. -/
@[implicit_reducible] def reflectedSphereQuotientChartedSpace :
    ChartedSpace CoverModel
      (MappingTorus (reflectedSphereData period hPeriod)) := by
  letI : ChartedSpace CoverModel
      (MappingTorusCover (reflectedSphereData period hPeriod)) :=
    reflectedSphereCoverChartedSpace period hPeriod
  exact mappingTorusSmoothChartedSpace (reflectedSphereData period hPeriod)

/-- The actual fixed-throat quotient is an analytic three-manifold for the
covering-induced atlas. -/
theorem fixedThroatQuotient_isManifold :
    @IsManifold ℝ _ ThroatCoverCoordinates _ _ ThroatCoverModel _
      throatCoverModelWithCorners ω
      (MappingTorus (fixedEquatorData period hPeriod)) _
      (fixedThroatQuotientChartedSpace period hPeriod) := by
  letI : ChartedSpace ThroatCoverModel
      (MappingTorusCover (fixedEquatorData period hPeriod)) :=
    fixedThroatCoverChartedSpace period hPeriod
  letI : IsManifold throatCoverModelWithCorners ω
      (MappingTorusCover (fixedEquatorData period hPeriod)) :=
    fixedThroatCover_isManifold period hPeriod
  exact mappingTorus_isManifold_of_smooth_deck
    throatCoverModelWithCorners ω (fixedEquatorData period hPeriod)
      (fixedThroatCover_deck_contMDiff period hPeriod)

/-- The actual effective reflected-sphere quotient is an analytic
four-manifold for the covering-induced atlas. -/
theorem reflectedSphereQuotient_isManifold :
    @IsManifold ℝ _ CoverCoordinates _ _ CoverModel _
      coverModelWithCorners ω
      (MappingTorus (reflectedSphereData period hPeriod)) _
      (reflectedSphereQuotientChartedSpace period hPeriod) := by
  letI : ChartedSpace CoverModel
      (MappingTorusCover (reflectedSphereData period hPeriod)) :=
    reflectedSphereCoverChartedSpace period hPeriod
  letI : IsManifold coverModelWithCorners ω
      (MappingTorusCover (reflectedSphereData period hPeriod)) :=
    reflectedSphereCover_isManifold period hPeriod
  exact mappingTorus_isManifold_of_smooth_deck
    coverModelWithCorners ω (reflectedSphereData period hPeriod)
      (reflectedSphereCover_deck_contMDiff period hPeriod)

/-- The fixed-throat quotient projection is an analytic local
diffeomorphism. -/
theorem fixedThroat_projection_isLocalDiffeomorph :
    letI : ChartedSpace ThroatCoverModel
        (MappingTorusCover (fixedEquatorData period hPeriod)) :=
      fixedThroatCoverChartedSpace period hPeriod
    letI : IsManifold throatCoverModelWithCorners ω
        (MappingTorusCover (fixedEquatorData period hPeriod)) :=
      fixedThroatCover_isManifold period hPeriod
    letI : ChartedSpace ThroatCoverModel
        (MappingTorus (fixedEquatorData period hPeriod)) :=
      fixedThroatQuotientChartedSpace period hPeriod
    letI : IsManifold throatCoverModelWithCorners ω
        (MappingTorus (fixedEquatorData period hPeriod)) :=
      fixedThroatQuotient_isManifold period hPeriod
    IsLocalDiffeomorph throatCoverModelWithCorners throatCoverModelWithCorners ω
      (mappingTorusMk (fixedEquatorData period hPeriod)) := by
  letI : ChartedSpace ThroatCoverModel
      (MappingTorusCover (fixedEquatorData period hPeriod)) :=
    fixedThroatCoverChartedSpace period hPeriod
  letI : IsManifold throatCoverModelWithCorners ω
      (MappingTorusCover (fixedEquatorData period hPeriod)) :=
    fixedThroatCover_isManifold period hPeriod
  letI : ChartedSpace ThroatCoverModel
      (MappingTorus (fixedEquatorData period hPeriod)) :=
    fixedThroatQuotientChartedSpace period hPeriod
  letI : IsManifold throatCoverModelWithCorners ω
      (MappingTorus (fixedEquatorData period hPeriod)) :=
    fixedThroatQuotient_isManifold period hPeriod
  exact mappingTorus_projection_isLocalDiffeomorph
    throatCoverModelWithCorners ω (fixedEquatorData period hPeriod)
      (fixedThroatCover_deck_contMDiff period hPeriod)

/-- The reflected-sphere quotient projection is an analytic local
diffeomorphism. -/
theorem reflectedSphere_projection_isLocalDiffeomorph :
    letI : ChartedSpace CoverModel
        (MappingTorusCover (reflectedSphereData period hPeriod)) :=
      reflectedSphereCoverChartedSpace period hPeriod
    letI : IsManifold coverModelWithCorners ω
        (MappingTorusCover (reflectedSphereData period hPeriod)) :=
      reflectedSphereCover_isManifold period hPeriod
    letI : ChartedSpace CoverModel
        (MappingTorus (reflectedSphereData period hPeriod)) :=
      reflectedSphereQuotientChartedSpace period hPeriod
    letI : IsManifold coverModelWithCorners ω
        (MappingTorus (reflectedSphereData period hPeriod)) :=
      reflectedSphereQuotient_isManifold period hPeriod
    IsLocalDiffeomorph coverModelWithCorners coverModelWithCorners ω
      (mappingTorusMk (reflectedSphereData period hPeriod)) := by
  letI : ChartedSpace CoverModel
      (MappingTorusCover (reflectedSphereData period hPeriod)) :=
    reflectedSphereCoverChartedSpace period hPeriod
  letI : IsManifold coverModelWithCorners ω
      (MappingTorusCover (reflectedSphereData period hPeriod)) :=
    reflectedSphereCover_isManifold period hPeriod
  letI : ChartedSpace CoverModel
      (MappingTorus (reflectedSphereData period hPeriod)) :=
    reflectedSphereQuotientChartedSpace period hPeriod
  letI : IsManifold coverModelWithCorners ω
      (MappingTorus (reflectedSphereData period hPeriod)) :=
    reflectedSphereQuotient_isManifold period hPeriod
  exact mappingTorus_projection_isLocalDiffeomorph
    coverModelWithCorners ω (reflectedSphereData period hPeriod)
      (reflectedSphereCover_deck_contMDiff period hPeriod)

/-- The effective fixed-throat inclusion descends to an analytic map between
the actual covering-induced quotient manifolds. -/
theorem fixedThroatQuotientInclusion_contMDiff :
    letI : ChartedSpace ThroatCoverModel
        (MappingTorus (fixedEquatorData period hPeriod)) :=
      fixedThroatQuotientChartedSpace period hPeriod
    letI : ChartedSpace CoverModel
        (MappingTorus (reflectedSphereData period hPeriod)) :=
      reflectedSphereQuotientChartedSpace period hPeriod
    ContMDiff throatCoverModelWithCorners coverModelWithCorners ω
      (fixedThroatQuotientInclusion period hPeriod) := by
  letI : ChartedSpace ThroatCoverModel
      (MappingTorus (fixedEquatorData period hPeriod)) :=
    fixedThroatQuotientChartedSpace period hPeriod
  letI : ChartedSpace CoverModel
      (MappingTorus (reflectedSphereData period hPeriod)) :=
    reflectedSphereQuotientChartedSpace period hPeriod
  letI : ChartedSpace ThroatCoverModel
      (MappingTorusCover (fixedEquatorData period hPeriod)) :=
    fixedThroatCoverChartedSpace period hPeriod
  letI : IsManifold throatCoverModelWithCorners ω
      (MappingTorusCover (fixedEquatorData period hPeriod)) :=
    fixedThroatCover_isManifold period hPeriod
  letI : ChartedSpace CoverModel
      (MappingTorusCover (reflectedSphereData period hPeriod)) :=
    reflectedSphereCoverChartedSpace period hPeriod
  letI : IsManifold coverModelWithCorners ω
      (MappingTorusCover (reflectedSphereData period hPeriod)) :=
    reflectedSphereCover_isManifold period hPeriod
  letI : IsManifold throatCoverModelWithCorners ω
      (MappingTorus (fixedEquatorData period hPeriod)) :=
    fixedThroatQuotient_isManifold period hPeriod
  letI : IsManifold coverModelWithCorners ω
      (MappingTorus (reflectedSphereData period hPeriod)) :=
    reflectedSphereQuotient_isManifold period hPeriod
  have hSourceProjection := fixedThroat_projection_isLocalDiffeomorph
    period hPeriod
  have hTargetProjection := reflectedSphere_projection_isLocalDiffeomorph
    period hPeriod
  have hLift : ContMDiff throatCoverModelWithCorners coverModelWithCorners ω
      (fun point => mappingTorusMk (reflectedSphereData period hPeriod)
        (fixedThroatCoverInclusion period hPeriod point)) :=
    hTargetProjection.contMDiff.comp
      (fixedThroatCoverInclusion_contMDiff period hPeriod)
  intro quotientPoint
  obtain ⟨anchor, rfl⟩ :=
    mappingTorusMk_surjective (fixedEquatorData period hPeriod) quotientPoint
  have hLocal := hSourceProjection anchor
  have hLocalLift : ContMDiffAt throatCoverModelWithCorners
      coverModelWithCorners ω
      ((fun point => mappingTorusMk (reflectedSphereData period hPeriod)
          (fixedThroatCoverInclusion period hPeriod point)) ∘
        hLocal.localInverse)
      (mappingTorusMk (fixedEquatorData period hPeriod) anchor) :=
    hLift.contMDiffAt.comp _ hLocal.localInverse_contMDiffAt
  apply hLocalLift.congr_of_eventuallyEq
  filter_upwards [hLocal.localInverse_eventuallyEq_right] with point hPoint
  rw [Function.comp_apply]
  rw [← fixedThroatQuotientInclusion_mk]
  exact congrArg (fixedThroatQuotientInclusion period hPeriod) hPoint.symm

end ReflectedSphereQuotients

end

end P0EFTJanusMappingTorusSmoothQuotientManifold
end JanusFormal
