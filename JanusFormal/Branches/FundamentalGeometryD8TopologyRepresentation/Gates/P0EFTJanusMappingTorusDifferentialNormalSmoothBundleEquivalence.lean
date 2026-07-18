import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusDifferentialNormalTopologicalBundle

/-!
# Smooth total comparison for the differential normal bundle

This gate packages the already constructed total-space homeomorphism as an
analytic diffeomorphism.  It uses exactly the transported atlas from the
topological comparison gate, so no second smooth structure is introduced.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusDifferentialNormalSmoothBundleEquivalence

set_option autoImplicit false

noncomputable section

open Set Topology
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusGlobalNormalEquivalence
open P0EFTJanusMappingTorusDifferentialNormalTopologicalBundle

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatBase :=
  MappingTorus (fixedEquatorData period hPeriod)

private local instance throatBaseChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

private local instance ambientBaseChartedSpace :
    ChartedSpace CoverModel
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  reflectedSphereQuotientChartedSpace period hPeriod

private local instance throatBaseIsManifold :
    IsManifold throatCoverModelWithCorners ω (ThroatBase period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

private local instance normalCoreIsContMDiff :
    (fixedThroatNormalVectorBundleCore period hPeriod).IsContMDiff
      throatCoverModelWithCorners ω :=
  fixedThroatNormalVectorBundleCore_isContMDiff period hPeriod

private abbrev NormalTotalModel :=
  throatCoverModelWithCorners.prod 𝓘(Real, Real)

@[simp] private theorem differentialNormalTotalHomeomorph_symm_base
    (normal : DifferentialNormalTotalSpace period hPeriod) :
    ((differentialNormalTotalHomeomorph period hPeriod).symm normal).1 =
      normal.1 :=
  rfl

private theorem differentialNormalTotalHomeomorph_contMDiff :
    ContMDiff NormalTotalModel NormalTotalModel ω
      (differentialNormalTotalHomeomorph period hPeriod) := by
  intro normal
  let anchor :=
    (fixedThroatNormalVectorBundleCore period hPeriod).indexAt normal.1
  let sourceTriv :=
    (fixedThroatNormalVectorBundleCore period hPeriod).localTriv anchor
  let targetTriv := differentialNormalLocalTriv period hPeriod anchor
  letI : MemTrivializationAtlas sourceTriv := by
    refine ⟨⟨anchor, ?_⟩⟩
    rfl
  letI : MemTrivializationAtlas targetTriv := by
    refine ⟨⟨anchor, ?_⟩⟩
    rfl
  have hSource : normal ∈ sourceTriv.source := by
    rw [sourceTriv.mem_source]
    exact (fixedThroatNormalVectorBundleCore period hPeriod).mem_baseSet_at normal.1
  have hTarget :
      differentialNormalTotalHomeomorph period hPeriod normal ∈
        targetTriv.source := by
    rw [targetTriv.mem_source]
    exact (fixedThroatNormalVectorBundleCore period hPeriod).mem_baseSet_at normal.1
  rw [targetTriv.contMDiffAt_iff hTarget]
  constructor
  · simpa only [differentialNormalTotalHomeomorph_base] using
      (Bundle.contMDiffAt_proj
        (E := FixedThroatNormalFiber period hPeriod) (n := ω))
  · have hTriv :=
      (sourceTriv.contMDiffOn
        (IB := throatCoverModelWithCorners) (n := ω) normal hSource).snd
    have hTrivAt := hTriv.contMDiffAt (sourceTriv.open_source.mem_nhds hSource)
    have hCoord :
        (fun x =>
          (targetTriv
            (differentialNormalTotalHomeomorph period hPeriod x)).2) =
          fun x => (sourceTriv x).2 := by
      funext x
      change
        (sourceTriv
          ((differentialNormalTotalHomeomorph period hPeriod).symm
            (differentialNormalTotalHomeomorph period hPeriod x))).2 =
          (sourceTriv x).2
      rw [Homeomorph.symm_apply_apply]
    rw [hCoord]
    exact hTrivAt

private theorem differentialNormalTotalHomeomorph_symm_contMDiff :
    ContMDiff NormalTotalModel NormalTotalModel ω
      (differentialNormalTotalHomeomorph period hPeriod).symm := by
  intro normal
  let anchor :=
    (fixedThroatNormalVectorBundleCore period hPeriod).indexAt normal.1
  let sourceTriv :=
    (fixedThroatNormalVectorBundleCore period hPeriod).localTriv anchor
  let targetTriv := differentialNormalLocalTriv period hPeriod anchor
  letI : MemTrivializationAtlas sourceTriv := by
    refine ⟨⟨anchor, ?_⟩⟩
    rfl
  letI : MemTrivializationAtlas targetTriv := by
    refine ⟨⟨anchor, ?_⟩⟩
    rfl
  have hTarget : normal ∈ targetTriv.source := by
    rw [targetTriv.mem_source]
    exact (fixedThroatNormalVectorBundleCore period hPeriod).mem_baseSet_at normal.1
  have hSource :
      (differentialNormalTotalHomeomorph period hPeriod).symm normal ∈
        sourceTriv.source := by
    rw [sourceTriv.mem_source]
    exact (fixedThroatNormalVectorBundleCore period hPeriod).mem_baseSet_at normal.1
  rw [sourceTriv.contMDiffAt_iff hSource]
  constructor
  · simpa only [differentialNormalTotalHomeomorph_symm_base] using
      (Bundle.contMDiffAt_proj
        (E := DifferentialNormalFiber period hPeriod) (n := ω))
  · have hTriv :=
      (targetTriv.contMDiffOn
        (IB := throatCoverModelWithCorners) (n := ω) normal hTarget).snd
    have hTrivAt := hTriv.contMDiffAt (targetTriv.open_source.mem_nhds hTarget)
    have hCoord :
        (fun x =>
          (sourceTriv
            ((differentialNormalTotalHomeomorph period hPeriod).symm x)).2) =
          fun x => (targetTriv x).2 := by
      rfl
    rw [hCoord]
    exact hTrivAt

/-- The exact global comparison is an analytic diffeomorphism for the
transported differential-normal atlas. -/
def differentialNormalTotalDiffeomorph :
    Diffeomorph NormalTotalModel NormalTotalModel
      (Bundle.TotalSpace Real (FixedThroatNormalFiber period hPeriod))
      (DifferentialNormalTotalSpace period hPeriod) ω where
  toEquiv := differentialNormalTotalEquiv period hPeriod
  contMDiff_toFun :=
    differentialNormalTotalHomeomorph_contMDiff period hPeriod
  contMDiff_invFun :=
    differentialNormalTotalHomeomorph_symm_contMDiff period hPeriod

theorem differentialNormalTotalDiffeomorph_toHomeomorph :
    (differentialNormalTotalDiffeomorph period hPeriod).toHomeomorph =
      differentialNormalTotalHomeomorph period hPeriod := by
  apply Homeomorph.toEquiv_injective
  rfl

@[simp] theorem differentialNormalTotalDiffeomorph_base
    (normal : Bundle.TotalSpace Real
      (FixedThroatNormalFiber period hPeriod)) :
    (differentialNormalTotalDiffeomorph period hPeriod normal).1 = normal.1 :=
  rfl

@[simp] theorem differentialNormalTotalDiffeomorph_fiber
    (point : ThroatBase period hPeriod)
    (normal : FixedThroatNormalFiber period hPeriod point) :
    (differentialNormalTotalDiffeomorph period hPeriod
      ⟨point, normal⟩).2 =
      differentialNormalFiberEquiv period hPeriod point normal :=
  rfl

theorem differentialNormalTotalDiffeomorph_add
    (point : ThroatBase period hPeriod)
    (first second : FixedThroatNormalFiber period hPeriod point) :
    differentialNormalTotalDiffeomorph period hPeriod
        ⟨point, first + second⟩ =
      ⟨point,
        differentialNormalFiberEquiv period hPeriod point first +
          differentialNormalFiberEquiv period hPeriod point second⟩ := by
  exact differentialNormalTotalEquiv_add period hPeriod point first second

theorem differentialNormalTotalDiffeomorph_smul
    (point : ThroatBase period hPeriod) (scalar : Real)
    (normal : FixedThroatNormalFiber period hPeriod point) :
    differentialNormalTotalDiffeomorph period hPeriod
        ⟨point, scalar • normal⟩ =
      ⟨point, scalar •
        differentialNormalFiberEquiv period hPeriod point normal⟩ := by
  exact differentialNormalTotalEquiv_smul period hPeriod point scalar normal

/-- In the transported charts the diffeomorphism is literally the identity;
therefore it preserves the original one-turn sign cocycle. -/
theorem differentialNormalTotalDiffeomorph_localTriv
    (anchor : MappingTorusCover (fixedEquatorData period hPeriod))
    (normal : Bundle.TotalSpace Real
      (FixedThroatNormalFiber period hPeriod)) :
    differentialNormalLocalTriv period hPeriod anchor
        (differentialNormalTotalDiffeomorph period hPeriod normal) =
      (fixedThroatNormalVectorBundleCore period hPeriod).localTriv anchor normal := by
  change
    (fixedThroatNormalVectorBundleCore period hPeriod).localTriv anchor
        ((differentialNormalTotalHomeomorph period hPeriod).symm
          (differentialNormalTotalHomeomorph period hPeriod normal)) =
      (fixedThroatNormalVectorBundleCore period hPeriod).localTriv anchor normal
  rw [Homeomorph.symm_apply_apply]

/-- The transported atlas has exactly the source normal-line transition
cocycle. -/
theorem differentialNormalTotalDiffeomorph_coordChange_eq
    (first second : MappingTorusCover (fixedEquatorData period hPeriod))
    {point : ThroatBase period hPeriod}
    (hPoint : point ∈ normalBundleBaseSet period hPeriod first ∩
      normalBundleBaseSet period hPeriod second)
    (normal : Real) :
    (differentialNormalLocalTriv period hPeriod first).coordChangeL Real
        (differentialNormalLocalTriv period hPeriod second) point normal =
      (fixedThroatNormalVectorBundleCore period hPeriod).coordChange
        first second point normal :=
  differentialNormalLocalTriv_coordChange_eq period hPeriod
    first second hPoint normal

/-- One circuit in the transported differential-normal atlas is still the
nontrivial transition `-id`. -/
theorem differentialNormalTotalDiffeomorph_one_loop_coordChange_eq_neg_id
    (anchor : MappingTorusCover (fixedEquatorData period hPeriod))
    (normal : Real) :
    (differentialNormalLocalTriv period hPeriod anchor).coordChangeL Real
        (differentialNormalLocalTriv period hPeriod ((1 : ℤ) +ᵥ anchor))
        (mappingTorusMk (fixedEquatorData period hPeriod) anchor) normal =
      -normal := by
  let projection :=
    (mappingTorusMk_isCoveringMap
      (fixedEquatorData period hPeriod)).isLocalHomeomorph
  let base := mappingTorusMk (fixedEquatorData period hPeriod) anchor
  have hProjection :
      mappingTorusMk (fixedEquatorData period hPeriod) ((1 : ℤ) +ᵥ anchor) =
        base :=
    (mappingTorusMk_isAddQuotientCoveringMap
      (fixedEquatorData period hPeriod)).map_vadd 1
  have hFirst : base ∈ normalBundleBaseSet period hPeriod anchor :=
    projection.apply_self_mem_localInverseAt_source
  have hSecond :
      base ∈ normalBundleBaseSet period hPeriod ((1 : ℤ) +ᵥ anchor) := by
    rw [← hProjection]
    exact projection.apply_self_mem_localInverseAt_source
  rw [differentialNormalTotalDiffeomorph_coordChange_eq period hPeriod
    anchor ((1 : ℤ) +ᵥ anchor) ⟨hFirst, hSecond⟩ normal]
  exact one_loop_coordChange_eq_neg_id period hPeriod anchor normal

end

end P0EFTJanusMappingTorusDifferentialNormalSmoothBundleEquivalence
end JanusFormal
