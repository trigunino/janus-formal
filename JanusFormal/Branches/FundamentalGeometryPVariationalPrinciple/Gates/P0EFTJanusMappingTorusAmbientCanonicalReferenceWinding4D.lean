import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAmbientPinMinusReferenceWindingFrontier4D

/-!
# Canonical ambient overlap winding

The winding below is the unique deck index relating the two genuine covering
local sections on an ambient atlas overlap.  The value `0` only totalizes the
function away from the transition source, where no Cech law uses it.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusAmbientCanonicalReferenceWinding4D

set_option autoImplicit false

noncomputable section

open Set Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusAmbientTangentOrientationCocycle
open P0EFTJanusMappingTorusAmbientPinMinusProjection4D
open P0EFTJanusMappingTorusAmbientPinMinusReferenceWindingFrontier4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev AmbientData := reflectedSphereData period hPeriod
private abbrev AmbientCover := MappingTorusCover (AmbientData period hPeriod)
private abbrev AmbientBase := MappingTorus (AmbientData period hPeriod)
private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatCover := MappingTorusCover (ThroatData period hPeriod)
private abbrev ThroatBase := MappingTorus (ThroatData period hPeriod)

private local instance ambientCoverChartedSpace :
    ChartedSpace CoverModel (AmbientCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod

private local instance throatCoverChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatCover period hPeriod) :=
  fixedThroatCoverChartedSpace period hPeriod

private abbrev ambientProjectionIsLocalHomeomorph :
    IsLocalHomeomorph (mappingTorusMk (AmbientData period hPeriod)) :=
  (mappingTorusMk_isCoveringMap (AmbientData period hPeriod)).isLocalHomeomorph

private abbrev throatProjectionIsLocalHomeomorph :
    IsLocalHomeomorph (mappingTorusMk (ThroatData period hPeriod)) :=
  (mappingTorusMk_isCoveringMap (ThroatData period hPeriod)).isLocalHomeomorph

/-- Throat covering section transported into the ambient cover. -/
def includedThroatLocalLift
    (anchor : ThroatCover period hPeriod) (base : ThroatBase period hPeriod) :
    AmbientCover period hPeriod :=
  fixedThroatCoverInclusion period hPeriod
    ((throatProjectionIsLocalHomeomorph period hPeriod).localInverseAt anchor base)

/-- Honest refinement on which the independently chosen throat and ambient
covering sections can be compared. -/
def throatAmbientSectionCompatibilityDomain
    (anchor : ThroatCover period hPeriod) : Set (ThroatBase period hPeriod) :=
  let throatSection :=
    (throatProjectionIsLocalHomeomorph period hPeriod).localInverseAt anchor
  let ambientAnchor := fixedThroatCoverInclusion period hPeriod anchor
  let ambientSection :=
    (ambientProjectionIsLocalHomeomorph period hPeriod).localInverseAt ambientAnchor
  ((throatSection.source ∩
      fixedThroatQuotientInclusion period hPeriod ⁻¹' ambientSection.source) ∩
    includedThroatLocalLift period hPeriod anchor ⁻¹' ambientSection.target)

theorem throatAmbientSectionCompatibilityDomain_isOpen
    (anchor : ThroatCover period hPeriod) :
    IsOpen (throatAmbientSectionCompatibilityDomain period hPeriod anchor) := by
  let throatSection :=
    (throatProjectionIsLocalHomeomorph period hPeriod).localInverseAt anchor
  let ambientAnchor := fixedThroatCoverInclusion period hPeriod anchor
  let ambientSection :=
    (ambientProjectionIsLocalHomeomorph period hPeriod).localInverseAt ambientAnchor
  have hBaseOpen : IsOpen
      (throatSection.source ∩
        fixedThroatQuotientInclusion period hPeriod ⁻¹' ambientSection.source) :=
    throatSection.open_source.inter
      (ambientSection.open_source.preimage
        (continuous_fixedThroatQuotientInclusion period hPeriod))
  have hLiftContinuous : ContinuousOn
      (includedThroatLocalLift period hPeriod anchor) throatSection.source :=
    (continuous_fixedThroatCoverInclusion period hPeriod).comp_continuousOn'
      throatSection.continuousOn
  exact (hLiftContinuous.mono inter_subset_left).isOpen_inter_preimage
    hBaseOpen ambientSection.open_target

theorem mappingTorusMk_mem_throatAmbientSectionCompatibilityDomain
    (anchor : ThroatCover period hPeriod) :
    mappingTorusMk (ThroatData period hPeriod) anchor ∈
      throatAmbientSectionCompatibilityDomain period hPeriod anchor := by
  let throatProjection := throatProjectionIsLocalHomeomorph period hPeriod
  let ambientProjection := ambientProjectionIsLocalHomeomorph period hPeriod
  let ambientAnchor := fixedThroatCoverInclusion period hPeriod anchor
  change
    ((mappingTorusMk (ThroatData period hPeriod) anchor ∈
        (throatProjection.localInverseAt anchor).source ∧
      fixedThroatQuotientInclusion period hPeriod
          (mappingTorusMk (ThroatData period hPeriod) anchor) ∈
        (ambientProjection.localInverseAt ambientAnchor).source) ∧
      includedThroatLocalLift period hPeriod anchor
          (mappingTorusMk (ThroatData period hPeriod) anchor) ∈
        (ambientProjection.localInverseAt ambientAnchor).target)
  refine ⟨⟨throatProjection.apply_self_mem_localInverseAt_source, ?_⟩, ?_⟩
  · rw [fixedThroatQuotientInclusion_mk]
    exact ambientProjection.apply_self_mem_localInverseAt_source
  · rw [includedThroatLocalLift, throatProjection.localInverseAt_apply_self]
    exact ambientProjection.self_mem_localInverseAt_target

theorem throatAmbientSectionCompatibilityDomain_mem_throatSource
    (anchor : ThroatCover period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈
      throatAmbientSectionCompatibilityDomain period hPeriod anchor) :
    base ∈ ((throatProjectionIsLocalHomeomorph period hPeriod).localInverseAt
      anchor).source :=
  hBase.1.1

theorem throatAmbientSectionCompatibilityDomain_mem_ambientSource
    (anchor : ThroatCover period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈
      throatAmbientSectionCompatibilityDomain period hPeriod anchor) :
    fixedThroatQuotientInclusion period hPeriod base ∈
      ((ambientProjectionIsLocalHomeomorph period hPeriod).localInverseAt
        (fixedThroatCoverInclusion period hPeriod anchor)).source :=
  hBase.1.2

theorem throatAmbientSectionCompatibilityDomain_includedLift_mem_target
    (anchor : ThroatCover period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈
      throatAmbientSectionCompatibilityDomain period hPeriod anchor) :
    includedThroatLocalLift period hPeriod anchor base ∈
      ((ambientProjectionIsLocalHomeomorph period hPeriod).localInverseAt
        (fixedThroatCoverInclusion period hPeriod anchor)).target :=
  hBase.2

/-- On the refined domain, the ambient local section is exactly the included
throat local section; no deck shift or arbitrary representative is inserted. -/
theorem ambientLocalInverse_fixedThroatQuotientInclusion
    (anchor : ThroatCover period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈
      throatAmbientSectionCompatibilityDomain period hPeriod anchor) :
    (ambientProjectionIsLocalHomeomorph period hPeriod).localInverseAt
        (fixedThroatCoverInclusion period hPeriod anchor)
        (fixedThroatQuotientInclusion period hPeriod base) =
      includedThroatLocalLift period hPeriod anchor base := by
  let throatProjection := throatProjectionIsLocalHomeomorph period hPeriod
  let ambientProjection := ambientProjectionIsLocalHomeomorph period hPeriod
  let throatSection := throatProjection.localInverseAt anchor
  let ambientAnchor := fixedThroatCoverInclusion period hPeriod anchor
  let ambientSection := ambientProjection.localInverseAt ambientAnchor
  have hThroatSource : base ∈ throatSection.source := hBase.1.1
  have hAmbientSource : fixedThroatQuotientInclusion period hPeriod base ∈
      ambientSection.source := hBase.1.2
  have hIncludedTarget : includedThroatLocalLift period hPeriod anchor base ∈
      ambientSection.target := hBase.2
  have hAmbientTarget :
      ambientSection (fixedThroatQuotientInclusion period hPeriod base) ∈
        ambientSection.target :=
    ambientSection.map_source hAmbientSource
  apply ambientProjection.injOn_localInverseAt_target
    hAmbientTarget hIncludedTarget
  calc
    mappingTorusMk (AmbientData period hPeriod)
        (ambientSection (fixedThroatQuotientInclusion period hPeriod base)) =
        fixedThroatQuotientInclusion period hPeriod base :=
      ambientProjection.apply_localInverseAt_of_mem hAmbientSource
    _ = fixedThroatQuotientInclusion period hPeriod
          (mappingTorusMk (ThroatData period hPeriod) (throatSection base)) :=
      congrArg (fixedThroatQuotientInclusion period hPeriod)
        (throatProjection.apply_localInverseAt_of_mem hThroatSource).symm
    _ = mappingTorusMk (AmbientData period hPeriod)
          (includedThroatLocalLift period hPeriod anchor base) := by
      rw [fixedThroatQuotientInclusion_mk]
      rfl

/-- Refinement on which section naturality also lands in the ambient cover
chart based at the included throat anchor. -/
def throatAmbientChartCompatibilityDomain
    (anchor : ThroatCover period hPeriod) : Set (ThroatBase period hPeriod) :=
  throatAmbientSectionCompatibilityDomain period hPeriod anchor ∩
    includedThroatLocalLift period hPeriod anchor ⁻¹'
      (chartAt CoverModel
        (fixedThroatCoverInclusion period hPeriod anchor)).source

theorem throatAmbientChartCompatibilityDomain_isOpen
    (anchor : ThroatCover period hPeriod) :
    IsOpen (throatAmbientChartCompatibilityDomain period hPeriod anchor) := by
  let throatSection :=
    (throatProjectionIsLocalHomeomorph period hPeriod).localInverseAt anchor
  have hLiftContinuous : ContinuousOn
      (includedThroatLocalLift period hPeriod anchor) throatSection.source :=
    (continuous_fixedThroatCoverInclusion period hPeriod).comp_continuousOn'
      throatSection.continuousOn
  exact (hLiftContinuous.mono (fun base hBase ↦
    throatAmbientSectionCompatibilityDomain_mem_throatSource
      period hPeriod anchor base hBase)).isOpen_inter_preimage
    (throatAmbientSectionCompatibilityDomain_isOpen period hPeriod anchor)
    (chartAt CoverModel
      (fixedThroatCoverInclusion period hPeriod anchor)).open_source

theorem mappingTorusMk_mem_throatAmbientChartCompatibilityDomain
    (anchor : ThroatCover period hPeriod) :
    mappingTorusMk (ThroatData period hPeriod) anchor ∈
      throatAmbientChartCompatibilityDomain period hPeriod anchor := by
  refine ⟨mappingTorusMk_mem_throatAmbientSectionCompatibilityDomain
    period hPeriod anchor, ?_⟩
  change includedThroatLocalLift period hPeriod anchor
      (mappingTorusMk (ThroatData period hPeriod) anchor) ∈
    (chartAt CoverModel
      (fixedThroatCoverInclusion period hPeriod anchor)).source
  rw [includedThroatLocalLift,
    (throatProjectionIsLocalHomeomorph period hPeriod).localInverseAt_apply_self]
  exact mem_chart_source CoverModel
    (fixedThroatCoverInclusion period hPeriod anchor)

theorem throatAmbientChartCompatibilityDomain_mem_sectionDomain
    (anchor : ThroatCover period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈
      throatAmbientChartCompatibilityDomain period hPeriod anchor) :
    base ∈ throatAmbientSectionCompatibilityDomain period hPeriod anchor :=
  hBase.1

theorem throatAmbientChartCompatibilityDomain_includedLift_mem_chartSource
    (anchor : ThroatCover period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈
      throatAmbientChartCompatibilityDomain period hPeriod anchor) :
    includedThroatLocalLift period hPeriod anchor base ∈
      (chartAt CoverModel
        (fixedThroatCoverInclusion period hPeriod anchor)).source :=
  hBase.2

/-- Every compatible throat base point lies in the actual quotient chart of
the corresponding included ambient anchor. -/
theorem fixedThroatQuotientInclusion_mem_ambientQuotientLocalChart_source
    (anchor : ThroatCover period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈
      throatAmbientChartCompatibilityDomain period hPeriod anchor) :
    fixedThroatQuotientInclusion period hPeriod base ∈
      (ambientQuotientLocalChart period hPeriod
        (fixedThroatCoverInclusion period hPeriod anchor)).source := by
  change fixedThroatQuotientInclusion period hPeriod base ∈
    (((ambientProjectionIsLocalHomeomorph period hPeriod).localInverseAt
        (fixedThroatCoverInclusion period hPeriod anchor)).trans
      (chartAt CoverModel
        (fixedThroatCoverInclusion period hPeriod anchor))).source
  rw [OpenPartialHomeomorph.trans_source]
  refine ⟨throatAmbientSectionCompatibilityDomain_mem_ambientSource
    period hPeriod anchor base hBase.1, ?_⟩
  change (ambientProjectionIsLocalHomeomorph period hPeriod).localInverseAt
      (fixedThroatCoverInclusion period hPeriod anchor)
      (fixedThroatQuotientInclusion period hPeriod base) ∈
    (chartAt CoverModel
      (fixedThroatCoverInclusion period hPeriod anchor)).source
  rw [ambientLocalInverse_fixedThroatQuotientInclusion
    period hPeriod anchor base hBase.1]
  exact hBase.2

/-- Genuine throat overlap on which both independent ambient sections and
both ambient cover charts are simultaneously compatible. -/
def throatAmbientChartCompatibilityOverlap
    (first second : ThroatCover period hPeriod) : Set (ThroatBase period hPeriod) :=
  throatAmbientChartCompatibilityDomain period hPeriod first ∩
    throatAmbientChartCompatibilityDomain period hPeriod second

theorem throatAmbientChartCompatibilityOverlap_isOpen
    (first second : ThroatCover period hPeriod) :
    IsOpen (throatAmbientChartCompatibilityOverlap period hPeriod first second) :=
  (throatAmbientChartCompatibilityDomain_isOpen period hPeriod first).inter
    (throatAmbientChartCompatibilityDomain_isOpen period hPeriod second)

theorem throatAmbientChartCompatibilityOverlap_subset_normalBundleOverlap
    (first second : ThroatCover period hPeriod) :
    throatAmbientChartCompatibilityOverlap period hPeriod first second ⊆
      normalBundleBaseSet period hPeriod first ∩
        normalBundleBaseSet period hPeriod second := by
  intro base hBase
  change base ∈
    ((throatProjectionIsLocalHomeomorph period hPeriod).localInverseAt
        first).source ∩
      ((throatProjectionIsLocalHomeomorph period hPeriod).localInverseAt
        second).source
  exact ⟨
    throatAmbientSectionCompatibilityDomain_mem_throatSource
      period hPeriod first base hBase.1.1,
    throatAmbientSectionCompatibilityDomain_mem_throatSource
      period hPeriod second base hBase.2.1⟩

/-- Ambient coordinate of a compatible throat base point, written in the
first included ambient chart. -/
def throatAmbientOverlapCoordinate
    (first : ThroatCover period hPeriod) (base : ThroatBase period hPeriod) :
    CoverModel :=
  ambientQuotientLocalChart period hPeriod
      (fixedThroatCoverInclusion period hPeriod first)
    (fixedThroatQuotientInclusion period hPeriod base)

theorem throatAmbientOverlapCoordinate_continuousOn
    (first second : ThroatCover period hPeriod) :
    ContinuousOn (throatAmbientOverlapCoordinate period hPeriod first)
      (throatAmbientChartCompatibilityOverlap period hPeriod first second) := by
  intro base hBase
  have hFirst :=
    fixedThroatQuotientInclusion_mem_ambientQuotientLocalChart_source
      period hPeriod first base hBase.1
  exact ((ambientQuotientLocalChart period hPeriod
    (fixedThroatCoverInclusion period hPeriod first)).continuousAt hFirst).comp
      (continuous_fixedThroatQuotientInclusion period hPeriod).continuousAt
    |>.continuousWithinAt

theorem throatAmbientOverlapCoordinate_mem_ambientAtlasTransition_source
    (first second : ThroatCover period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈
      throatAmbientChartCompatibilityOverlap period hPeriod first second) :
    throatAmbientOverlapCoordinate period hPeriod first base ∈
      (ambientAtlasTransition period hPeriod
        (fixedThroatCoverInclusion period hPeriod first)
        (fixedThroatCoverInclusion period hPeriod second)).source := by
  have hFirst :=
    fixedThroatQuotientInclusion_mem_ambientQuotientLocalChart_source
      period hPeriod first base hBase.1
  have hSecond :=
    fixedThroatQuotientInclusion_mem_ambientQuotientLocalChart_source
      period hPeriod second base hBase.2
  change
    (ambientQuotientLocalChart period hPeriod
      (fixedThroatCoverInclusion period hPeriod first))
        (fixedThroatQuotientInclusion period hPeriod base) ∈
      ((ambientQuotientLocalChart period hPeriod
          (fixedThroatCoverInclusion period hPeriod first)).symm.trans
        (ambientQuotientLocalChart period hPeriod
          (fixedThroatCoverInclusion period hPeriod second))).source
  rw [OpenPartialHomeomorph.trans_source]
  refine ⟨(ambientQuotientLocalChart period hPeriod
    (fixedThroatCoverInclusion period hPeriod first)).map_source hFirst, ?_⟩
  change
    (ambientQuotientLocalChart period hPeriod
      (fixedThroatCoverInclusion period hPeriod first)).symm
        ((ambientQuotientLocalChart period hPeriod
          (fixedThroatCoverInclusion period hPeriod first))
            (fixedThroatQuotientInclusion period hPeriod base)) ∈
      (ambientQuotientLocalChart period hPeriod
        (fixedThroatCoverInclusion period hPeriod second)).source
  rw [(ambientQuotientLocalChart period hPeriod
    (fixedThroatCoverInclusion period hPeriod first)).left_inv hFirst]
  exact hSecond

private def transitionBase
    (first : AmbientCover period hPeriod) (coordinate : CoverModel) :
    AmbientBase period hPeriod :=
  (ambientQuotientLocalChart period hPeriod first).symm coordinate

private theorem transitionBase_throatAmbientOverlapCoordinate
    (first second : ThroatCover period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈
      throatAmbientChartCompatibilityOverlap period hPeriod first second) :
    transitionBase period hPeriod
        (fixedThroatCoverInclusion period hPeriod first)
        (throatAmbientOverlapCoordinate period hPeriod first base) =
      fixedThroatQuotientInclusion period hPeriod base := by
  exact (ambientQuotientLocalChart period hPeriod
    (fixedThroatCoverInclusion period hPeriod first)).left_inv
      (fixedThroatQuotientInclusion_mem_ambientQuotientLocalChart_source
        period hPeriod first base hBase.1)

private theorem transition_mem_firstChart_target
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientAtlasTransition period hPeriod first second).source) :
    coordinate ∈ (ambientQuotientLocalChart period hPeriod first).target := by
  change coordinate ∈
    ((ambientQuotientLocalChart period hPeriod first).symm.trans
      (ambientQuotientLocalChart period hPeriod second)).source at hCoordinate
  rw [OpenPartialHomeomorph.trans_source] at hCoordinate
  exact hCoordinate.1

private theorem transitionBase_mem_firstSection_source
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientAtlasTransition period hPeriod first second).source) :
    transitionBase period hPeriod first coordinate ∈
      ((ambientProjectionIsLocalHomeomorph period hPeriod).localInverseAt
        first).source := by
  have hChartSource : transitionBase period hPeriod first coordinate ∈
      (ambientQuotientLocalChart period hPeriod first).source :=
    (ambientQuotientLocalChart period hPeriod first).symm.map_source
      (transition_mem_firstChart_target period hPeriod
        first second coordinate hCoordinate)
  change transitionBase period hPeriod first coordinate ∈
    (((ambientProjectionIsLocalHomeomorph period hPeriod).localInverseAt first).trans
      (chartAt CoverModel first)).source at hChartSource
  rw [OpenPartialHomeomorph.trans_source] at hChartSource
  exact hChartSource.1

private theorem transitionBase_mem_secondSection_source
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientAtlasTransition period hPeriod first second).source) :
    transitionBase period hPeriod first coordinate ∈
      ((ambientProjectionIsLocalHomeomorph period hPeriod).localInverseAt
        second).source := by
  change coordinate ∈
    ((ambientQuotientLocalChart period hPeriod first).symm.trans
      (ambientQuotientLocalChart period hPeriod second)).source at hCoordinate
  rw [OpenPartialHomeomorph.trans_source] at hCoordinate
  have hSecondChartSource := hCoordinate.2
  change transitionBase period hPeriod first coordinate ∈
    (((ambientProjectionIsLocalHomeomorph period hPeriod).localInverseAt second).trans
      (chartAt CoverModel second)).source at hSecondChartSource
  rw [OpenPartialHomeomorph.trans_source] at hSecondChartSource
  exact hSecondChartSource.1

private theorem transition_basePoint
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientAtlasTransition period hPeriod first second).source) :
    transitionBase period hPeriod second
        (ambientAtlasTransition period hPeriod first second coordinate) =
      transitionBase period hPeriod first coordinate := by
  change coordinate ∈
    ((ambientQuotientLocalChart period hPeriod first).symm.trans
      (ambientQuotientLocalChart period hPeriod second)).source at hCoordinate
  rw [OpenPartialHomeomorph.trans_source] at hCoordinate
  change
    (ambientQuotientLocalChart period hPeriod second).symm
        ((ambientQuotientLocalChart period hPeriod second)
          ((ambientQuotientLocalChart period hPeriod first).symm coordinate)) =
      (ambientQuotientLocalChart period hPeriod first).symm coordinate
  exact (ambientQuotientLocalChart period hPeriod second).left_inv hCoordinate.2

private theorem exists_transition_winding
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientAtlasTransition period hPeriod first second).source) :
    ∃ winding : Int,
      winding +ᵥ
          (ambientProjectionIsLocalHomeomorph period hPeriod).localInverseAt
            first (transitionBase period hPeriod first coordinate) =
        (ambientProjectionIsLocalHomeomorph period hPeriod).localInverseAt
          second (transitionBase period hPeriod first coordinate) := by
  let projection := ambientProjectionIsLocalHomeomorph period hPeriod
  let base := transitionBase period hPeriod first coordinate
  have hFirstSource := transitionBase_mem_firstSection_source period hPeriod
    first second coordinate hCoordinate
  have hSecondSource := transitionBase_mem_secondSection_source period hPeriod
    first second coordinate hCoordinate
  have hFirstProjection :
      mappingTorusMk (AmbientData period hPeriod)
          (projection.localInverseAt first base) = base :=
    projection.apply_localInverseAt_of_mem hFirstSource
  have hSecondProjection :
      mappingTorusMk (AmbientData period hPeriod)
          (projection.localInverseAt second base) = base :=
    projection.apply_localInverseAt_of_mem hSecondSource
  exact (mappingTorusMk_eq_iff_exists_vadd (AmbientData period hPeriod)
    (projection.localInverseAt second base)
    (projection.localInverseAt first base)).1
      (hSecondProjection.trans hFirstProjection.symm)

/-- The actual deck index of an ambient atlas overlap. -/
def ambientTransitionWinding
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel) : Int := by
  classical
  exact if hCoordinate : coordinate ∈
        (ambientAtlasTransition period hPeriod first second).source then
      Classical.choose
        (exists_transition_winding period hPeriod first second coordinate hCoordinate)
    else 0

theorem ambientTransitionWinding_vadd
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientAtlasTransition period hPeriod first second).source) :
    ambientTransitionWinding period hPeriod first second coordinate +ᵥ
        (ambientProjectionIsLocalHomeomorph period hPeriod).localInverseAt
          first (transitionBase period hPeriod first coordinate) =
      (ambientProjectionIsLocalHomeomorph period hPeriod).localInverseAt
        second (transitionBase period hPeriod first coordinate) := by
  rw [ambientTransitionWinding, dif_pos hCoordinate]
  exact Classical.choose_spec
    (exists_transition_winding period hPeriod first second coordinate hCoordinate)

theorem ambientTransitionWinding_unique
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientAtlasTransition period hPeriod first second).source)
    (winding : Int)
    (hWinding : winding +ᵥ
        (ambientProjectionIsLocalHomeomorph period hPeriod).localInverseAt
          first (transitionBase period hPeriod first coordinate) =
      (ambientProjectionIsLocalHomeomorph period hPeriod).localInverseAt
        second (transitionBase period hPeriod first coordinate)) :
    winding = ambientTransitionWinding period hPeriod first second coordinate := by
  apply IsCancelVAdd.right_cancel _ _
    ((ambientProjectionIsLocalHomeomorph period hPeriod).localInverseAt
      first (transitionBase period hPeriod first coordinate))
  exact hWinding.trans
    (ambientTransitionWinding_vadd period hPeriod
      first second coordinate hCoordinate).symm

/-- On the honest compatible overlap, the ambient deck cocycle restricts
exactly to the throat deck cocycle. -/
theorem ambientTransitionWinding_throatAmbientOverlapCoordinate
    (first second : ThroatCover period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈
      throatAmbientChartCompatibilityOverlap period hPeriod first second) :
    ambientTransitionWinding period hPeriod
        (fixedThroatCoverInclusion period hPeriod first)
        (fixedThroatCoverInclusion period hPeriod second)
        (throatAmbientOverlapCoordinate period hPeriod first base) =
      localTransitionWinding period hPeriod first second base := by
  let winding := localTransitionWinding period hPeriod first second base
  have hNormalBase : base ∈
      normalBundleBaseSet period hPeriod first ∩
        normalBundleBaseSet period hPeriod second :=
    throatAmbientChartCompatibilityOverlap_subset_normalBundleOverlap
      period hPeriod first second hBase
  have hIncludedDeck := congrArg
    (fixedThroatCoverInclusion period hPeriod)
    (localTransitionWinding_vadd period hPeriod
      first second base hNormalBase)
  rw [fixedThroatCoverInclusion_equivariant] at hIncludedDeck
  change winding +ᵥ includedThroatLocalLift period hPeriod first base =
    includedThroatLocalLift period hPeriod second base at hIncludedDeck
  rw [← ambientLocalInverse_fixedThroatQuotientInclusion
        period hPeriod first base hBase.1.1,
      ← ambientLocalInverse_fixedThroatQuotientInclusion
        period hPeriod second base hBase.2.1] at hIncludedDeck
  have hTransitionBase :=
    transitionBase_throatAmbientOverlapCoordinate period hPeriod
      first second base hBase
  rw [← hTransitionBase] at hIncludedDeck
  have hCoordinate :=
    throatAmbientOverlapCoordinate_mem_ambientAtlasTransition_source
      period hPeriod first second base hBase
  exact (ambientTransitionWinding_unique period hPeriod
    (fixedThroatCoverInclusion period hPeriod first)
    (fixedThroatCoverInclusion period hPeriod second)
    (throatAmbientOverlapCoordinate period hPeriod first base)
    hCoordinate winding hIncludedDeck).symm

private theorem ambientTransitionWinding_self
    (anchor : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientAtlasTransition period hPeriod anchor anchor).source) :
    ambientTransitionWinding period hPeriod anchor anchor coordinate = 0 := by
  apply IsCancelVAdd.right_cancel _ _
    ((ambientProjectionIsLocalHomeomorph period hPeriod).localInverseAt
      anchor (transitionBase period hPeriod anchor coordinate))
  rw [zero_vadd]
  exact ambientTransitionWinding_vadd period hPeriod
    anchor anchor coordinate hCoordinate

private theorem ambientTransitionWinding_add
    (first second third : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hFirstSecond : coordinate ∈
      (ambientAtlasTransition period hPeriod first second).source)
    (hSecondThird :
      ambientAtlasTransition period hPeriod first second coordinate ∈
        (ambientAtlasTransition period hPeriod second third).source)
    (hFirstThird : coordinate ∈
      (ambientAtlasTransition period hPeriod first third).source) :
    ambientTransitionWinding period hPeriod second third
          (ambientAtlasTransition period hPeriod first second coordinate) +
        ambientTransitionWinding period hPeriod first second coordinate =
      ambientTransitionWinding period hPeriod first third coordinate := by
  let projection := ambientProjectionIsLocalHomeomorph period hPeriod
  let base := transitionBase period hPeriod first coordinate
  have hBase := transition_basePoint period hPeriod
    first second coordinate hFirstSecond
  have hFirstSecondDeck := ambientTransitionWinding_vadd period hPeriod
    first second coordinate hFirstSecond
  have hSecondThirdDeck := ambientTransitionWinding_vadd period hPeriod
    second third (ambientAtlasTransition period hPeriod first second coordinate)
      hSecondThird
  rw [hBase] at hSecondThirdDeck
  have hFirstThirdDeck := ambientTransitionWinding_vadd period hPeriod
    first third coordinate hFirstThird
  apply IsCancelVAdd.right_cancel _ _ (projection.localInverseAt first base)
  rw [add_vadd, hFirstSecondDeck, hSecondThirdDeck, hFirstThirdDeck]

theorem ambientTransitionWinding_eventuallyEq
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientAtlasTransition period hPeriod first second).source) :
    Filter.EventuallyEq (nhds coordinate)
      (ambientTransitionWinding period hPeriod first second)
      (fun _ ↦ ambientTransitionWinding period hPeriod first second coordinate) := by
  let projection := ambientProjectionIsLocalHomeomorph period hPeriod
  let firstChart := ambientQuotientLocalChart period hPeriod first
  let base := transitionBase period hPeriod first coordinate
  let winding := ambientTransitionWinding period hPeriod first second coordinate
  have hFirstSource := transitionBase_mem_firstSection_source period hPeriod
    first second coordinate hCoordinate
  have hSecondSource := transitionBase_mem_secondSection_source period hPeriod
    first second coordinate hCoordinate
  have hSections := localInverseAt_eventuallyEq_vadd_of_mem
    (AmbientData period hPeriod) first second base hFirstSource hSecondSource winding
      (ambientTransitionWinding_vadd period hPeriod
        first second coordinate hCoordinate)
  have hCoordinateTarget := transition_mem_firstChart_target period hPeriod
    first second coordinate hCoordinate
  have hInverseContinuous : ContinuousAt firstChart.symm coordinate :=
    firstChart.symm.continuousAt hCoordinateTarget
  have hSectionsCoordinate := hSections.comp_tendsto hInverseContinuous
  have hOverlap :
      (ambientAtlasTransition period hPeriod first second).source ∈ nhds coordinate :=
    (ambientAtlasTransition period hPeriod first second).open_source.mem_nhds hCoordinate
  filter_upwards [hSectionsCoordinate, hOverlap]
    with nearby hSectionsNearby hNearby
  apply IsCancelVAdd.right_cancel _ _
    (projection.localInverseAt first (firstChart.symm nearby))
  exact (ambientTransitionWinding_vadd period hPeriod
    first second nearby hNearby).trans hSectionsNearby

private theorem transitionCharacter_continuousOn
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    [IsTopologicalGroup AmbientCoordinatePinMinusGroup]
    (first second : AmbientCover period hPeriod) :
    ContinuousOn
      (fun coordinate ↦ ambientPinMinusReferenceZ4Character
        (ambientTransitionWinding period hPeriod first second coordinate : ZMod 4))
      (ambientAtlasTransition period hPeriod first second).source := by
  intro coordinate hCoordinate
  let overlap := (ambientAtlasTransition period hPeriod first second).source
  have hWindingEq : Filter.EventuallyEq (nhdsWithin coordinate overlap)
      (ambientTransitionWinding period hPeriod first second)
      (fun _ ↦ ambientTransitionWinding period hPeriod first second coordinate) :=
    (ambientTransitionWinding_eventuallyEq period hPeriod
      first second coordinate hCoordinate).filter_mono inf_le_left
  have hCharacterEq := hWindingEq.fun_comp
    (fun winding : Int ↦
      ambientPinMinusReferenceZ4Character (winding : ZMod 4))
  exact (continuousWithinAt_const : ContinuousWithinAt
    (fun _ : CoverModel ↦ ambientPinMinusReferenceZ4Character
      (ambientTransitionWinding period hPeriod first second coordinate : ZMod 4))
    overlap coordinate).congr_of_eventuallyEq_of_mem hCharacterEq hCoordinate

/-- Canonical Cech data supplied by the true ambient covering sections. -/
def ambientReferenceWindingCechData
    [TopologicalSpace AmbientCoordinatePinMinusGroup]
    [IsTopologicalGroup AmbientCoordinatePinMinusGroup] :
    AmbientReferenceWindingCechData period hPeriod where
  transitionWinding := ambientTransitionWinding period hPeriod
  realizes_deck := ambientTransitionWinding_vadd period hPeriod
  normalized := ambientTransitionWinding_self period hPeriod
  cocycle := ambientTransitionWinding_add period hPeriod
  transitionCharacter_continuousOn :=
    transitionCharacter_continuousOn period hPeriod

end

end P0EFTJanusMappingTorusAmbientCanonicalReferenceWinding4D
end JanusFormal
