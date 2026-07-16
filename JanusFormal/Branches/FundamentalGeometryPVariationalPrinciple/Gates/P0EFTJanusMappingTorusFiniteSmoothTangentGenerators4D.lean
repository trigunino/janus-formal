import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusH1GraphTrace4D

/-!
# Finite smooth tangent generators on the effective D8 quotient

Compactness reduces the tangent-bundle trivialization cover of the actual
four-dimensional mapping torus to finitely many charts.  A smooth partition
of unity subordinate to that finite cover globalizes the associated local
frames.  The resulting finite family of smooth vector fields spans every
tangent fiber; no parallelizability assumption is used.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open Set Bundle Module MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusL2PTFunctionalSpace4D
open P0EFTJanusMappingTorusH1GraphTrace4D

variable (period : ℝ) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)
private abbrev EffectiveThroat := MappingTorus (throatData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) :=
  borel (EffectiveQuotient period hPeriod)

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance effectiveThroatCompactSpace :
    CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance effectiveThroatMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) :=
  borel (EffectiveThroat period hPeriod)

local instance effectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

private abbrev TangentFiber (point : EffectiveQuotient period hPeriod) :=
  TangentSpace coverModelWithCorners point

private abbrev tangentTrivialization
    (anchor : EffectiveQuotient period hPeriod) :=
  trivializationAt CoverCoordinates (TangentFiber period hPeriod) anchor

/-- A finite set of actual quotient points whose tangent trivializations cover
the effective D8 mapping torus. -/
theorem exists_finite_tangent_trivialization_cover :
    ∃ anchors : Finset (EffectiveQuotient period hPeriod),
      (Set.univ : Set (EffectiveQuotient period hPeriod)) ⊆
        ⋃ anchor ∈ anchors, (tangentTrivialization period hPeriod anchor).baseSet := by
  apply isCompact_univ.elim_finite_subcover
  · exact fun anchor => (tangentTrivialization period hPeriod anchor).open_baseSet
  · intro point _
    exact mem_iUnion_of_mem point
      (FiberBundle.mem_baseSet_trivializationAt' point)

private def coverAnchors : Finset (EffectiveQuotient period hPeriod) :=
  (exists_finite_tangent_trivialization_cover period hPeriod).choose

private theorem coverAnchors_cover :
    (Set.univ : Set (EffectiveQuotient period hPeriod)) ⊆
      ⋃ anchor ∈ coverAnchors period hPeriod,
        (tangentTrivialization period hPeriod anchor).baseSet :=
  (exists_finite_tangent_trivialization_cover period hPeriod).choose_spec

private abbrev Anchor := {anchor // anchor ∈ coverAnchors period hPeriod}

private def tangentCover (anchor : Anchor period hPeriod) :
    Set (EffectiveQuotient period hPeriod) :=
  (tangentTrivialization period hPeriod anchor.1).baseSet

private theorem tangentCover_isOpen (anchor : Anchor period hPeriod) :
    IsOpen (tangentCover period hPeriod anchor) :=
  (tangentTrivialization period hPeriod anchor.1).open_baseSet

private theorem tangentCover_covers :
    (Set.univ : Set (EffectiveQuotient period hPeriod)) ⊆
      ⋃ anchor : Anchor period hPeriod, tangentCover period hPeriod anchor := by
  intro point hPoint
  rcases mem_iUnion₂.mp (coverAnchors_cover period hPeriod hPoint) with
    ⟨anchor, hAnchor, hPointAnchor⟩
  exact mem_iUnion_of_mem ⟨anchor, hAnchor⟩ hPointAnchor

/-- A finite smooth partition of unity subordinate to tangent-bundle
trivializations of the actual compact quotient. -/
theorem exists_finite_tangent_partition :
    ∃ partition : SmoothPartitionOfUnity (Anchor period hPeriod)
        coverModelWithCorners (EffectiveQuotient period hPeriod) Set.univ,
      partition.IsSubordinate (tangentCover period hPeriod) := by
  exact SmoothPartitionOfUnity.exists_isSubordinate coverModelWithCorners
    isClosed_univ (tangentCover period hPeriod)
    (tangentCover_isOpen period hPeriod) (tangentCover_covers period hPeriod)

private def tangentPartition :
    SmoothPartitionOfUnity (Anchor period hPeriod)
      coverModelWithCorners (EffectiveQuotient period hPeriod) Set.univ :=
  (exists_finite_tangent_partition period hPeriod).choose

private theorem tangentPartition_subordinate :
    (tangentPartition period hPeriod).IsSubordinate
      (tangentCover period hPeriod) :=
  (exists_finite_tangent_partition period hPeriod).choose_spec

/-- Public finite patch index extracted from the tangent trivialization cover.
The underlying choice remains encapsulated. -/
abbrev FiniteTangentGeneratorPatch := Anchor period hPeriod

/-- Open tangent-trivialization patch attached to one finite anchor. -/
def finiteTangentGeneratorOpenPatch
    (patch : FiniteTangentGeneratorPatch period hPeriod) :
    Set (EffectiveQuotient period hPeriod) :=
  tangentCover period hPeriod patch

theorem finiteTangentGeneratorOpenPatch_isOpen
    (patch : FiniteTangentGeneratorPatch period hPeriod) :
    IsOpen (finiteTangentGeneratorOpenPatch period hPeriod patch) :=
  tangentCover_isOpen period hPeriod patch

/-- Closed support of the subordinate partition weight.  These are the
compact pieces on which quantitative transition estimates may be taken. -/
def finiteTangentGeneratorClosedPatch
    (patch : FiniteTangentGeneratorPatch period hPeriod) :
    Set (EffectiveQuotient period hPeriod) :=
  tsupport (tangentPartition period hPeriod patch)

theorem finiteTangentGeneratorClosedPatch_isClosed
    (patch : FiniteTangentGeneratorPatch period hPeriod) :
    IsClosed (finiteTangentGeneratorClosedPatch period hPeriod patch) :=
  isClosed_closure

theorem finiteTangentGeneratorClosedPatch_subset_openPatch
    (patch : FiniteTangentGeneratorPatch period hPeriod) :
    finiteTangentGeneratorClosedPatch period hPeriod patch ⊆
      finiteTangentGeneratorOpenPatch period hPeriod patch :=
  tangentPartition_subordinate period hPeriod patch

/-- The closed partition supports still cover the whole quotient. -/
theorem finiteTangentGeneratorClosedPatch_covers
    (point : EffectiveQuotient period hPeriod) :
    ∃ patch : FiniteTangentGeneratorPatch period hPeriod,
      point ∈ finiteTangentGeneratorClosedPatch period hPeriod patch := by
  obtain ⟨patch, hPatch⟩ :=
    (tangentPartition period hPeriod).exists_pos_of_mem (Set.mem_univ point)
  refine ⟨patch, subset_closure ?_⟩
  exact ne_of_gt hPatch

private abbrev BasisIndex := Fin (Module.finrank ℝ CoverCoordinates)

private def tangentModelBasis : Basis BasisIndex ℝ CoverCoordinates :=
  Module.finBasis ℝ CoverCoordinates

private abbrev GeneratorIndex := Anchor period hPeriod × BasisIndex

/-- Partition-weighted local-frame vectors, now defined globally on the real
quotient tangent bundle. -/
private def generatorSection
    (index : GeneratorIndex period hPeriod)
    (point : EffectiveQuotient period hPeriod) : TangentFiber period hPeriod point :=
  tangentPartition period hPeriod index.1 point •
    (tangentTrivialization period hPeriod index.1.1).localFrame
      tangentModelBasis index.2 point

private theorem generatorSection_contMDiff
    (index : GeneratorIndex period hPeriod) :
    ContMDiff coverModelWithCorners coverModelWithCorners.tangent ∞
      (fun point =>
        (⟨point, generatorSection period hPeriod index point⟩ :
          TangentBundle coverModelWithCorners
            (EffectiveQuotient period hPeriod))) := by
  exact ContMDiffOn.smul_section_of_tsupport
    ((tangentPartition period hPeriod index.1).contMDiff.contMDiffOn)
    (tangentCover_isOpen period hPeriod index.1)
    (tangentPartition_subordinate period hPeriod index.1)
    ((tangentTrivialization period hPeriod index.1.1).contMDiffOn_localFrame_baseSet
      (n := ∞) tangentModelBasis index.2)

private theorem generatorSection_spans
    (point : EffectiveQuotient period hPeriod) :
    Submodule.span ℝ
      (Set.range (fun index : GeneratorIndex period hPeriod =>
        generatorSection period hPeriod index point)) = ⊤ := by
  obtain ⟨anchor, hAnchor⟩ :=
    (tangentPartition period hPeriod).exists_pos_of_mem (Set.mem_univ point)
  have hAnchorNe : tangentPartition period hPeriod anchor point ≠ 0 :=
    ne_of_gt hAnchor
  have hPointSupport :
      point ∈ Function.support (tangentPartition period hPeriod anchor) :=
    hAnchorNe
  have hPointBase : point ∈ tangentCover period hPeriod anchor :=
    tangentPartition_subordinate period hPeriod anchor
      (subset_closure hPointSupport)
  apply top_unique
  calc
    ⊤ ≤ Submodule.span ℝ
        (Set.range (fun index : BasisIndex =>
          (tangentTrivialization period hPeriod anchor.1).localFrame
            tangentModelBasis index point)) :=
      ((tangentTrivialization period hPeriod anchor.1).isLocalFrameOn_localFrame_baseSet
          coverModelWithCorners ∞
          tangentModelBasis).generating hPointBase
    _ ≤ Submodule.span ℝ
        (Set.range (fun index : GeneratorIndex period hPeriod =>
          generatorSection period hPeriod index point)) := by
      apply Submodule.span_le.mpr
      rintro vector ⟨basisIndex, rfl⟩
      have hGenerator : generatorSection period hPeriod (anchor, basisIndex) point ∈
          Submodule.span ℝ
            (Set.range (fun index : GeneratorIndex period hPeriod =>
              generatorSection period hPeriod index point)) :=
        Submodule.subset_span ⟨(anchor, basisIndex), rfl⟩
      have hScaled := (Submodule.span ℝ
        (Set.range (fun index : GeneratorIndex period hPeriod =>
          generatorSection period hPeriod index point))).smul_mem
            (tangentPartition period hPeriod anchor point)⁻¹ hGenerator
      simpa [generatorSection, hAnchorNe] using hScaled

private def generatorIndexEquivFin :
    GeneratorIndex period hPeriod ≃
      Fin (Fintype.card (GeneratorIndex period hPeriod)) :=
  Fintype.equivFin (GeneratorIndex period hPeriod)

/-- An unconditional finite `C∞` spanning family on the true compact D8
quotient.  It is obtained from finitely many tangent trivializations, not from
a global frame. -/
def finiteSmoothTangentFrame : SmoothD8Frame period hPeriod where
  count := Fintype.card (GeneratorIndex period hPeriod)
  vectorAt point index := generatorSection period hPeriod
    ((generatorIndexEquivFin period hPeriod).symm index) point
  spansAt point := by
    have hRange :
        Set.range (fun index : Fin (Fintype.card (GeneratorIndex period hPeriod)) =>
          generatorSection period hPeriod
            ((generatorIndexEquivFin period hPeriod).symm index) point) =
          Set.range (fun index : GeneratorIndex period hPeriod =>
            generatorSection period hPeriod index point) := by
      ext vector
      constructor
      · rintro ⟨index, rfl⟩
        exact ⟨(generatorIndexEquivFin period hPeriod).symm index, rfl⟩
      · rintro ⟨index, rfl⟩
        exact ⟨generatorIndexEquivFin period hPeriod index, by simp⟩
    rw [hRange]
    exact generatorSection_spans period hPeriod point
  contMDiff_vector index :=
    generatorSection_contMDiff period hPeriod
      ((generatorIndexEquivFin period hPeriod).symm index)

/-- In particular, the finite smooth spanning-family input is inhabited with
no geometric hypothesis beyond the already proved compact analytic quotient. -/
theorem finiteSmoothTangentFrame_nonempty :
    Nonempty (SmoothD8Frame period hPeriod) :=
  ⟨finiteSmoothTangentFrame period hPeriod⟩

/-- The frame input of the graph-H¹ construction is closed unconditionally
on the actual effective D8 quotient. -/
theorem smoothD8FrameInput_closed :
    Nonempty (SmoothD8Frame period hPeriod) :=
  finiteSmoothTangentFrame_nonempty period hPeriod

section QuantitativeTrace

universe u

variable (Fiber : Type u)
  [NormedAddCommGroup Fiber] [NormedSpace ℝ Fiber]

/-- The graph-H¹ completion attached directly to the constructed finite
smooth tangent family. -/
abbrev FiniteFrameH1GraphSpace
    (mu : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure mu] :=
  H1GraphSpace period hPeriod Fiber
    (finiteSmoothTangentFrame period hPeriod) mu

/-- Canonical smooth inclusion into the now-unconditional graph-H¹ space. -/
def smoothToFiniteFrameH1Graph
    (mu : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure mu] :
    SmoothQuotientField period hPeriod Fiber →ₗ[ℝ]
      FiniteFrameH1GraphSpace period hPeriod Fiber mu :=
  smoothToH1GraphLinearMap period hPeriod Fiber
    (finiteSmoothTangentFrame period hPeriod) mu

theorem smoothToFiniteFrameH1Graph_denseRange
    (mu : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure mu] :
    DenseRange (smoothToFiniteFrameH1Graph period hPeriod Fiber mu) :=
  smoothToH1Graph_denseRange period hPeriod Fiber
    (finiteSmoothTangentFrame period hPeriod) mu

/-- The finite spacetime measure concentrated on the embedded effective
throat and induced by a finite throat measure. -/
def throatSupportedSpacetimeMeasure
    (nu : Measure (EffectiveThroat period hPeriod)) :
    Measure (EffectiveQuotient period hPeriod) :=
  Measure.map (fixedThroatQuotientInclusion period hPeriod) nu

private instance throatSupportedSpacetimeMeasure_isFinite
    (nu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure nu] :
    IsFiniteMeasure (throatSupportedSpacetimeMeasure period hPeriod nu) := by
  unfold throatSupportedSpacetimeMeasure
  infer_instance

private theorem throatInclusion_measurable :
    Measurable (fixedThroatQuotientInclusion period hPeriod) :=
  (fixedThroatQuotientInclusion_contMDiff period hPeriod).continuous.measurable

/-- For the throat-supported spacetime measure, the global value norm is
exactly the norm of the genuine throat restriction. -/
theorem smoothTrace_norm_eq_spacetimeValue_norm
    (nu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure nu]
    (field : SmoothQuotientField period hPeriod Fiber) :
    ‖smoothTraceToL2 period hPeriod Fiber nu field‖ =
      ‖smoothFieldToL2 period hPeriod Fiber
        (throatSupportedSpacetimeMeasure period hPeriod nu) field‖ := by
  rw [smoothTraceToL2, smoothFieldToL2, Lp.norm_toLp, Lp.norm_toLp]
  congr 1
  symm
  simpa [throatSupportedSpacetimeMeasure, throatTrace, Function.comp_def] using
    (eLpNorm_map_measure
      (smoothQuotientField_memLp period hPeriod Fiber
        (throatSupportedSpacetimeMeasure period hPeriod nu) field).1
      (throatInclusion_measurable period hPeriod).aemeasurable)

/-- Forgetting derivative coordinates from the first-jet graph is a
contraction. -/
theorem h1GraphToL2_norm_le
    (frame : SmoothD8Frame period hPeriod)
    (mu : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure mu]
    (field : H1GraphSpace period hPeriod Fiber frame mu) :
    ‖h1GraphToL2 period hPeriod Fiber frame mu field‖ ≤ ‖field‖ := by
  let projection :=
    (ContinuousLinearMap.fst ℝ Fiber (Fin frame.count → Fiber)).compLpL
      (2 : ENNReal) mu
  have hProjection : ‖projection‖ ≤ 1 :=
    (ContinuousLinearMap.norm_compLpL_le
      (ContinuousLinearMap.fst ℝ Fiber (Fin frame.count → Fiber))).trans
        (ContinuousLinearMap.norm_fst_le ℝ Fiber (Fin frame.count → Fiber))
  change ‖projection field.1‖ ≤ ‖field‖
  calc
    ‖projection field.1‖ ≤ ‖projection‖ * ‖field.1‖ := projection.le_opNorm field.1
    _ ≤ 1 * ‖field.1‖ :=
      mul_le_mul_of_nonneg_right hProjection (norm_nonneg field.1)
    _ = ‖field‖ := by simp

/-- A quantitative trace theorem on the actual embedded throat:
when the spacetime measure contains precisely the pushed-forward throat
measure, the trace constant is `1`. -/
def throatSupportedHasH1TraceBound
    (frame : SmoothD8Frame period hPeriod)
    (nu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure nu] :
    HasH1TraceBound period hPeriod Fiber frame
      (throatSupportedSpacetimeMeasure period hPeriod nu) nu where
  constant := 1
  nonnegative := zero_le_one
  bound field := by
    change ‖smoothTraceToL2 period hPeriod Fiber nu field‖ ≤ _
    rw [one_mul, smoothTrace_norm_eq_spacetimeValue_norm]
    rw [← h1GraphToL2_agrees_on_smooth period hPeriod Fiber frame
      (throatSupportedSpacetimeMeasure period hPeriod nu) field]
    exact h1GraphToL2_norm_le period hPeriod Fiber frame
      (throatSupportedSpacetimeMeasure period hPeriod nu)
      (smoothToH1GraphLinearMap period hPeriod Fiber frame
        (throatSupportedSpacetimeMeasure period hPeriod nu) field)

/-- The corresponding unconditional continuous trace operator on the graph
completion (once the graph's tangent family is fixed). -/
def throatSupportedH1Trace
    [CompleteSpace Fiber]
    (frame : SmoothD8Frame period hPeriod)
    (nu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure nu] :
    H1GraphSpace period hPeriod Fiber frame
        (throatSupportedSpacetimeMeasure period hPeriod nu) →L[ℝ]
      Lp Fiber (2 : ENNReal) nu :=
  h1Trace period hPeriod Fiber frame
    (throatSupportedSpacetimeMeasure period hPeriod nu) nu
    (throatSupportedHasH1TraceBound period hPeriod Fiber frame nu)

theorem throatSupportedH1Trace_agrees_on_smooth
    [CompleteSpace Fiber]
    (frame : SmoothD8Frame period hPeriod)
    (nu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure nu]
    (field : SmoothQuotientField period hPeriod Fiber) :
    throatSupportedH1Trace period hPeriod Fiber frame nu
        (smoothToH1GraphLinearMap period hPeriod Fiber frame
          (throatSupportedSpacetimeMeasure period hPeriod nu) field) =
      smoothTraceL2LinearMap period hPeriod Fiber nu field :=
  h1Trace_agrees_on_smooth period hPeriod Fiber frame
    (throatSupportedSpacetimeMeasure period hPeriod nu) nu
    (throatSupportedHasH1TraceBound period hPeriod Fiber frame nu) field

theorem throatSupportedH1Trace_norm_le
    [CompleteSpace Fiber]
    (frame : SmoothD8Frame period hPeriod)
    (nu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure nu]
    (field : H1GraphSpace period hPeriod Fiber frame
      (throatSupportedSpacetimeMeasure period hPeriod nu)) :
    ‖throatSupportedH1Trace period hPeriod Fiber frame nu field‖ ≤ ‖field‖ := by
  simpa [throatSupportedH1Trace, throatSupportedHasH1TraceBound] using
    h1Trace_norm_le period hPeriod Fiber frame
    (throatSupportedSpacetimeMeasure period hPeriod nu) nu
    (throatSupportedHasH1TraceBound period hPeriod Fiber frame nu) field

/-- The fully connected trace on the graph-H¹ completion built from the
unconditional finite tangent family. -/
def finiteFrameThroatSupportedH1Trace
    [CompleteSpace Fiber]
    (nu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure nu] :
    FiniteFrameH1GraphSpace period hPeriod Fiber
        (throatSupportedSpacetimeMeasure period hPeriod nu) →L[ℝ]
      Lp Fiber (2 : ENNReal) nu :=
  throatSupportedH1Trace period hPeriod Fiber
    (finiteSmoothTangentFrame period hPeriod) nu

theorem finiteFrameThroatSupportedH1Trace_agrees_on_smooth
    [CompleteSpace Fiber]
    (nu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure nu]
    (field : SmoothQuotientField period hPeriod Fiber) :
    finiteFrameThroatSupportedH1Trace period hPeriod Fiber nu
        (smoothToFiniteFrameH1Graph period hPeriod Fiber
          (throatSupportedSpacetimeMeasure period hPeriod nu) field) =
      smoothTraceL2LinearMap period hPeriod Fiber nu field :=
  throatSupportedH1Trace_agrees_on_smooth period hPeriod Fiber
    (finiteSmoothTangentFrame period hPeriod) nu field

theorem finiteFrameThroatSupportedH1Trace_norm_le
    [CompleteSpace Fiber]
    (nu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure nu]
    (field : FiniteFrameH1GraphSpace period hPeriod Fiber
      (throatSupportedSpacetimeMeasure period hPeriod nu)) :
    ‖finiteFrameThroatSupportedH1Trace period hPeriod Fiber nu field‖ ≤
      ‖field‖ :=
  throatSupportedH1Trace_norm_le period hPeriod Fiber
    (finiteSmoothTangentFrame period hPeriod) nu field

end QuantitativeTrace

end

end P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
end JanusFormal
