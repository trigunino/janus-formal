import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusSmoothThroatEmbedding

/-!
# The effective throat is a genuine smooth embedding

This gate closes the remaining Mathlib `IsSmoothEmbedding` frontier for the
effective fixed throat.  It constructs an explicit stereographic normal form
for `S² ↪ S³`, transports it through the algebraic sphere models and product
covers, and descends it through the mapping-torus local sections.

The final result records separately the global smooth embedding, the fixed
one-dimensional complement, the closed topological embedding, differential
injectivity, and the codimension-one normal quotient.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusIsSmoothEmbedding

set_option autoImplicit false

noncomputable section

open Set
open scoped RealInnerProductSpace Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatEmbedding

theorem insert_inner (x y : EuclideanR3) :
    inner ℝ (euclideanEquatorInsertCLM x) (euclideanEquatorInsertCLM y) = inner ℝ x y := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  simp [euclideanEquatorInsertCLM, euclideanEquatorInsertLinearMap,
    dotProduct, Fin.sum_univ_succ]

noncomputable def orthogonalEquatorInsert (v : EuclideanR3) :
    (ℝ ∙ v)ᗮ →L[ℝ] (ℝ ∙ euclideanEquatorInsertCLM v)ᗮ :=
  (euclideanEquatorInsertCLM.comp (ℝ ∙ v)ᗮ.subtypeL).codRestrict
    ((ℝ ∙ euclideanEquatorInsertCLM v)ᗮ) (fun w => by
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
      change inner ℝ (euclideanEquatorInsertCLM v)
        (euclideanEquatorInsertCLM (w : EuclideanR3)) = 0
      rw [insert_inner]
      exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp w.property)

theorem insert_norm (x : EuclideanR3) :
    ‖euclideanEquatorInsertCLM x‖ = ‖x‖ := by
  have hsq : ‖euclideanEquatorInsertCLM x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, insert_inner]
  nlinarith [norm_nonneg (euclideanEquatorInsertCLM x), norm_nonneg x]

theorem orthogonalProjection_insert
    (v x : EuclideanR3) (hv : ‖v‖ = 1) :
    orthogonalEquatorInsert v ((ℝ ∙ v)ᗮ.orthogonalProjectionOnto x) =
      (ℝ ∙ euclideanEquatorInsertCLM v)ᗮ.orthogonalProjectionOnto
        (euclideanEquatorInsertCLM x) := by
  apply Subtype.ext
  rw [Submodule.orthogonalProjectionOnto_orthogonal,
    Submodule.orthogonalProjectionOnto_orthogonal]
  change euclideanEquatorInsertCLM (x - (ℝ ∙ v).starProjection x) =
    euclideanEquatorInsertCLM x -
      (ℝ ∙ euclideanEquatorInsertCLM v).starProjection
        (euclideanEquatorInsertCLM x)
  rw [Submodule.starProjection_unit_singleton ℝ hv,
    Submodule.starProjection_unit_singleton ℝ (insert_norm v |>.trans hv)]
  simp only [map_sub, map_smul, insert_inner]

theorem stereoToFun_insert
    (v x : EuclideanR3) (hv : ‖v‖ = 1) :
    orthogonalEquatorInsert v (stereoToFun v x) =
      stereoToFun (euclideanEquatorInsertCLM v)
        (euclideanEquatorInsertCLM x) := by
  rw [stereoToFun_apply, stereoToFun_apply]
  rw [map_smul, orthogonalProjection_insert v x hv]
  simp only [innerSL_apply_apply, insert_inner]

theorem neg_spherePoint_ne_zero (point : StandardEquatorialTwoSphere) :
    (-point.1 : EuclideanR3) ≠ 0 :=
  neg_ne_zero.mpr (ne_zero_of_mem_unit_sphere point)

theorem inserted_neg_spherePoint_ne_zero (point : StandardEquatorialTwoSphere) :
    euclideanEquatorInsertCLM (-point.1 : EuclideanR3) ≠ 0 := by
  intro h
  apply neg_spherePoint_ne_zero point
  apply euclideanEquatorInsertCLM_injective
  simpa only [map_zero] using h

noncomputable def standardChartLinearMap
    (point : StandardEquatorialTwoSphere) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3) := by
  letI : Fact (Module.finrank ℝ EuclideanR3 = 2 + 1) := ⟨by simp⟩
  letI : Fact (Module.finrank ℝ EuclideanR4 = 3 + 1) := ⟨by simp⟩
  let sourcePole : EuclideanR3 := -point.1
  let targetPole : EuclideanR4 := euclideanEquatorInsertCLM sourcePole
  let sourceRepr :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (E := EuclideanR3) 2
      (show sourcePole ≠ 0 by simpa [sourcePole] using
        neg_spherePoint_ne_zero point)).repr
  let targetRepr :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (E := EuclideanR4) 3
      (show targetPole ≠ 0 by simpa [targetPole, sourcePole] using
        inserted_neg_spherePoint_ne_zero point)).repr
  exact targetRepr.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((orthogonalEquatorInsert sourcePole).comp
      sourceRepr.symm.toContinuousLinearEquiv.toContinuousLinearMap)

theorem standardChartLinearMap_injective
    (point : StandardEquatorialTwoSphere) :
    Function.Injective (standardChartLinearMap point) := by
  letI : Fact (Module.finrank ℝ EuclideanR3 = 2 + 1) := ⟨by simp⟩
  letI : Fact (Module.finrank ℝ EuclideanR4 = 3 + 1) := ⟨by simp⟩
  change Function.Injective
    ((OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (E := EuclideanR4) 3
      (inserted_neg_spherePoint_ne_zero point)).repr.toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((orthogonalEquatorInsert (-point.1 : EuclideanR3)).comp
        (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (E := EuclideanR3) 2
          (neg_spherePoint_ne_zero point)).repr.symm.toContinuousLinearEquiv.toContinuousLinearMap))
  intro first second h
  apply (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (E := EuclideanR3) 2
    (neg_spherePoint_ne_zero point)).repr.symm.injective
  apply Subtype.ext
  apply euclideanEquatorInsertCLM_injective
  exact congrArg Subtype.val
    ((OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (E := EuclideanR4) 3
      (inserted_neg_spherePoint_ne_zero point)).repr.injective h)

theorem standardEquatorInclusion_neg
    (point : StandardEquatorialTwoSphere) :
    standardEquatorInclusion (-point) = -standardEquatorInclusion point := by
  apply Subtype.ext
  change euclideanEquatorInsertCLM (-point.1) =
    -euclideanEquatorInsertCLM point.1
  exact map_neg _ _

@[implicit_reducible] noncomputable def standardEquatorSourceChart
    (anchor : StandardEquatorialTwoSphere) :
    OpenPartialHomeomorph StandardEquatorialTwoSphere
      (EuclideanSpace ℝ (Fin 2)) := by
  letI : Fact (Module.finrank ℝ EuclideanR3 = 2 + 1) := ⟨by simp⟩
  exact stereographic' 2 (-anchor)

@[implicit_reducible] noncomputable def standardEquatorTargetChart
    (anchor : StandardEquatorialTwoSphere) :
    OpenPartialHomeomorph StandardUnitThreeSphere
      (EuclideanSpace ℝ (Fin 3)) := by
  letI : Fact (Module.finrank ℝ EuclideanR4 = 3 + 1) := ⟨by simp⟩
  exact stereographic' 3 (standardEquatorInclusion (-anchor))

theorem standardStereographic_commutes
    (anchor point : StandardEquatorialTwoSphere) :
    standardEquatorTargetChart anchor (standardEquatorInclusion point) =
      standardChartLinearMap anchor (standardEquatorSourceChart anchor point) := by
  letI : Fact (Module.finrank ℝ EuclideanR3 = 2 + 1) := ⟨by simp⟩
  letI : Fact (Module.finrank ℝ EuclideanR4 = 3 + 1) := ⟨by simp⟩
  let sourceRepr :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (E := EuclideanR3) 2
      (neg_spherePoint_ne_zero anchor)).repr
  let targetRepr :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (E := EuclideanR4) 3
      (inserted_neg_spherePoint_ne_zero anchor)).repr
  change
    targetRepr
        (stereoToFun (euclideanEquatorInsertCLM (-anchor.1))
          (euclideanEquatorInsertCLM point.1)) =
      standardChartLinearMap anchor
        (sourceRepr (stereoToFun (-anchor.1) point.1))
  rw [← stereoToFun_insert (-anchor.1) point.1]
  · change targetRepr
        (orthogonalEquatorInsert (-anchor.1) (stereoToFun (-anchor.1) point.1)) =
      targetRepr (orthogonalEquatorInsert (-anchor.1)
        (sourceRepr.symm (sourceRepr (stereoToFun (-anchor.1) point.1))))
    rw [sourceRepr.symm_apply_apply]
  · simp [norm_eq_of_mem_sphere anchor]

abbrev StandardNormalCoordinate := EuclideanSpace ℝ (Fin 1)

noncomputable def standardChartEquiv
    (point : StandardEquatorialTwoSphere) :
    (EuclideanSpace ℝ (Fin 2) × StandardNormalCoordinate) ≃L[ℝ]
      EuclideanSpace ℝ (Fin 3) := by
  let A := standardChartLinearMap point
  have hA : Function.Injective A := standardChartLinearMap_injective point
  let rangeEquiv : EuclideanSpace ℝ (Fin 2) ≃L[ℝ]
      LinearMap.range A.toLinearMap :=
    (LinearEquiv.ofInjective A.toLinearMap hA).toContinuousLinearEquiv
  have hRange : Module.finrank ℝ (LinearMap.range A.toLinearMap) = 2 := by
    rw [LinearMap.finrank_range_of_inj hA]
    simp
  have hOrthogonal :
      Module.finrank ℝ StandardNormalCoordinate =
        Module.finrank ℝ (LinearMap.range A.toLinearMap)ᗮ := by
    have hSum := (LinearMap.range A.toLinearMap).finrank_add_finrank_orthogonal
    have hTarget : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
    rw [hRange, hTarget] at hSum
    calc
      Module.finrank ℝ StandardNormalCoordinate = 1 := by simp [StandardNormalCoordinate]
      _ = Module.finrank ℝ (LinearMap.range A.toLinearMap)ᗮ := by omega
  let normalEquiv : StandardNormalCoordinate ≃L[ℝ]
      (LinearMap.range A.toLinearMap)ᗮ :=
    (LinearEquiv.ofFinrankEq StandardNormalCoordinate
      (LinearMap.range A.toLinearMap)ᗮ hOrthogonal).toContinuousLinearEquiv
  exact (rangeEquiv.prodCongr normalEquiv).trans
    ((LinearMap.range A.toLinearMap).prodEquivOfIsTopCompl
      (LinearMap.range A.toLinearMap)ᗮ
      (LinearMap.range A.toLinearMap).isTopCompl_orthogonal)

@[simp] theorem standardChartEquiv_zero
    (point : StandardEquatorialTwoSphere)
    (coordinate : EuclideanSpace ℝ (Fin 2)) :
    standardChartEquiv point (coordinate, 0) =
      standardChartLinearMap point coordinate := by
  simp [standardChartEquiv, Submodule.coe_prodEquivOfIsTopCompl]

theorem standardEquatorSourceChart_mem_atlas
    (point : StandardEquatorialTwoSphere) :
    standardEquatorSourceChart point ∈
      atlas (EuclideanSpace ℝ (Fin 2)) StandardEquatorialTwoSphere := by
  letI : Fact (Module.finrank ℝ EuclideanR3 = 2 + 1) := ⟨by simp⟩
  exact ⟨-point, rfl⟩

theorem standardEquatorTargetChart_mem_atlas
    (point : StandardEquatorialTwoSphere) :
    standardEquatorTargetChart point ∈
      atlas (EuclideanSpace ℝ (Fin 3)) StandardUnitThreeSphere := by
  letI : Fact (Module.finrank ℝ EuclideanR4 = 3 + 1) := ⟨by simp⟩
  exact ⟨standardEquatorInclusion (-point), rfl⟩

theorem standardEquatorInclusion_isImmersionOfComplement :
    Manifold.IsImmersionOfComplement StandardNormalCoordinate
      (𝓡 2) (𝓡 3) ω standardEquatorInclusion := by
  intro anchor
  letI : Fact (Module.finrank ℝ EuclideanR3 = 2 + 1) := ⟨by simp⟩
  letI : Fact (Module.finrank ℝ EuclideanR4 = 3 + 1) := ⟨by simp⟩
  apply Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
    standardEquatorInclusion_contMDiff.continuous.continuousAt
    (standardChartEquiv anchor)
    (standardEquatorSourceChart anchor)
    (standardEquatorTargetChart anchor)
  · simpa [standardEquatorSourceChart] using
      ne_neg_of_mem_unit_sphere ℝ anchor
  · simpa [standardEquatorTargetChart, standardEquatorInclusion_neg] using
      ne_neg_of_mem_unit_sphere ℝ (standardEquatorInclusion anchor)
  · exact IsManifold.subset_maximalAtlas
      (standardEquatorSourceChart_mem_atlas anchor)
  · exact IsManifold.subset_maximalAtlas
      (standardEquatorTargetChart_mem_atlas anchor)
  · intro coordinate hCoordinate
    simp only [Function.comp_apply, mfld_simps] at hCoordinate ⊢
    rw [standardChartEquiv_zero]
    let sourcePoint := (standardEquatorSourceChart anchor).symm coordinate
    rw [standardStereographic_commutes anchor sourcePoint]
    congr 1
    exact (standardEquatorSourceChart anchor).right_inv hCoordinate

@[implicit_reducible] noncomputable def actualEquatorSourceChart
    (anchor : EquatorialTwoSphere) :
    OpenPartialHomeomorph EquatorialTwoSphere
      (EuclideanSpace ℝ (Fin 2)) :=
  equatorialTwoSphereHomeomorph.transOpenPartialHomeomorph
    (standardEquatorSourceChart (equatorialTwoSphereHomeomorph anchor))

@[implicit_reducible] noncomputable def actualEquatorTargetChart
    (anchor : EquatorialTwoSphere) :
    OpenPartialHomeomorph UnitThreeSphere
      (EuclideanSpace ℝ (Fin 3)) :=
  unitThreeSphereHomeomorph.transOpenPartialHomeomorph
    (standardEquatorTargetChart (equatorialTwoSphereHomeomorph anchor))

theorem actualEquatorSourceChart_mem_atlas (anchor : EquatorialTwoSphere) :
    actualEquatorSourceChart anchor ∈
      atlas (EuclideanSpace ℝ (Fin 2)) EquatorialTwoSphere :=
  ⟨standardEquatorSourceChart (equatorialTwoSphereHomeomorph anchor),
    standardEquatorSourceChart_mem_atlas _, rfl⟩

theorem actualEquatorTargetChart_mem_atlas (anchor : EquatorialTwoSphere) :
    actualEquatorTargetChart anchor ∈
      atlas (EuclideanSpace ℝ (Fin 3)) UnitThreeSphere :=
  ⟨standardEquatorTargetChart (equatorialTwoSphereHomeomorph anchor),
    standardEquatorTargetChart_mem_atlas _, rfl⟩

theorem actualEquatorInclusion_in_standard_coords
    (point : EquatorialTwoSphere) :
    unitThreeSphereHomeomorph (equatorialSphereInclusion point) =
      standardEquatorInclusion (equatorialTwoSphereHomeomorph point) := by
  apply unitThreeSphereHomeomorph.symm.injective
  simpa using (standardEquatorInclusion_conjugates_actual point).symm

theorem equatorialSphereInclusion_isImmersionOfComplement :
    Manifold.IsImmersionOfComplement StandardNormalCoordinate
      (𝓡 2) (𝓡 3) ω equatorialSphereInclusion := by
  intro anchor
  let standardAnchor := equatorialTwoSphereHomeomorph anchor
  apply Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
    continuous_equatorialSphereInclusion.continuousAt
    (standardChartEquiv standardAnchor)
    (actualEquatorSourceChart anchor)
    (actualEquatorTargetChart anchor)
  · simpa [actualEquatorSourceChart, standardAnchor,
      standardEquatorSourceChart] using
      ne_neg_of_mem_unit_sphere ℝ standardAnchor
  · rw [show equatorialSphereInclusion anchor =
        unitThreeSphereHomeomorph.symm
          (standardEquatorInclusion standardAnchor) by
      apply unitThreeSphereHomeomorph.injective
      simpa [standardAnchor] using actualEquatorInclusion_in_standard_coords anchor]
    simpa [actualEquatorTargetChart, standardAnchor,
      standardEquatorTargetChart, standardEquatorInclusion_neg] using
      ne_neg_of_mem_unit_sphere ℝ (standardEquatorInclusion standardAnchor)
  · exact IsManifold.subset_maximalAtlas
      (actualEquatorSourceChart_mem_atlas anchor)
  · exact IsManifold.subset_maximalAtlas
      (actualEquatorTargetChart_mem_atlas anchor)
  · intro coordinate hCoordinate
    simp only [Function.comp_apply, mfld_simps] at hCoordinate ⊢
    rw [standardChartEquiv_zero]
    let sourcePoint := (actualEquatorSourceChart anchor).symm coordinate
    change standardEquatorTargetChart standardAnchor
        (unitThreeSphereHomeomorph
          (equatorialSphereInclusion sourcePoint)) = _
    rw [actualEquatorInclusion_in_standard_coords sourcePoint]
    rw [standardStereographic_commutes standardAnchor
      (equatorialTwoSphereHomeomorph sourcePoint)]
    congr 1
    exact (actualEquatorSourceChart anchor).right_inv hCoordinate

abbrev ThroatNormalComplement := StandardNormalCoordinate × PUnit.{1}

set_option backward.isDefEq.respectTransparency false in
theorem equatorialSphereInclusion_prod_id_isImmersionOfComplement :
    Manifold.IsImmersionOfComplement ThroatNormalComplement
      throatCoverModelWithCorners coverModelWithCorners ω
      (Prod.map equatorialSphereInclusion (id : ℝ → ℝ)) :=
  equatorialSphereInclusion_isImmersionOfComplement.prodMap
    Manifold.IsImmersionOfComplement.id

section PullbackMaximalAtlas

variable {𝕜 E H M N : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] [TopologicalSpace M] [TopologicalSpace N]
  (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)
  (equiv : M ≃ₜ N) [ChartedSpace H N]

theorem chartedSpacePullback_mem_maximalAtlas
    (targetChart : OpenPartialHomeomorph N H)
    (hTarget : targetChart ∈ IsManifold.maximalAtlas I n N) :
    letI : ChartedSpace H M := chartedSpacePullback equiv
    equiv.transOpenPartialHomeomorph targetChart ∈
      IsManifold.maximalAtlas I n M := by
  letI : ChartedSpace H M := chartedSpacePullback equiv
  rintro _ ⟨selectedTarget, hSelectedTarget, rfl⟩
  have hForward :
      (equiv.transOpenPartialHomeomorph targetChart).symm.trans
          (equiv.transOpenPartialHomeomorph selectedTarget) =
        targetChart.symm.trans selectedTarget := by
    ext point <;> simp
  have hBackward :
      (equiv.transOpenPartialHomeomorph selectedTarget).symm.trans
          (equiv.transOpenPartialHomeomorph targetChart) =
        selectedTarget.symm.trans targetChart := by
    ext point <;> simp
  rw [hForward, hBackward]
  exact hTarget selectedTarget hSelectedTarget

end PullbackMaximalAtlas

set_option backward.isDefEq.respectTransparency false in
theorem fixedThroatCoverInclusion_isImmersionOfComplement
    (period : ℝ) (hPeriod : period ≠ 0) :
    letI : ChartedSpace ThroatCoverModel
        (MappingTorusCover (fixedEquatorData period hPeriod)) :=
      fixedThroatCoverChartedSpace period hPeriod
    letI : ChartedSpace CoverModel
        (MappingTorusCover (reflectedSphereData period hPeriod)) :=
      reflectedSphereCoverChartedSpace period hPeriod
    Manifold.IsImmersionOfComplement ThroatNormalComplement
      throatCoverModelWithCorners coverModelWithCorners ω
      (fixedThroatCoverInclusion period hPeriod) := by
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
  intro anchor
  let sourceHomeomorph :=
    coverHomeomorphProd (fixedEquatorData period hPeriod)
  let targetHomeomorph :=
    coverHomeomorphProd (reflectedSphereData period hPeriod)
  let productInclusion :=
    Prod.map equatorialSphereInclusion (id : ℝ → ℝ)
  have hConjugacy
      (point : MappingTorusCover (fixedEquatorData period hPeriod)) :
      targetHomeomorph (fixedThroatCoverInclusion period hPeriod point) =
        productInclusion (sourceHomeomorph point) :=
    rfl
  let hProduct :=
    equatorialSphereInclusion_prod_id_isImmersionOfComplement
      (sourceHomeomorph anchor)
  let sourceChart := sourceHomeomorph.transOpenPartialHomeomorph hProduct.domChart
  let targetChart := targetHomeomorph.transOpenPartialHomeomorph hProduct.codChart
  apply Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
    (continuous_fixedThroatCoverInclusion period hPeriod).continuousAt
    hProduct.equiv sourceChart targetChart
  · exact hProduct.mem_domChart_source
  · change productInclusion (sourceHomeomorph anchor) ∈ hProduct.codChart.source
    exact hProduct.mem_codChart_source
  · exact chartedSpacePullback_mem_maximalAtlas
      throatCoverModelWithCorners ω sourceHomeomorph hProduct.domChart
      hProduct.domChart_mem_maximalAtlas
  · exact chartedSpacePullback_mem_maximalAtlas
      coverModelWithCorners ω targetHomeomorph hProduct.codChart
      hProduct.codChart_mem_maximalAtlas
  · intro coordinate hCoordinate
    have hCoordinate' :
        coordinate ∈ (hProduct.domChart.extend throatCoverModelWithCorners).target := by
      simpa [sourceChart] using hCoordinate
    simpa [sourceChart, targetChart, hConjugacy] using
      hProduct.writtenInCharts hCoordinate'

section MaximalSmoothHomeomorphCoordinates

variable {𝕜 E H M : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω} [IsManifold I n M]

theorem smoothHomeomorph_coordinateChange_mem_groupoid_of_mem_maximalAtlas
    (homeo : M ≃ₜ M)
    (hForward : ContMDiff I I n homeo)
    (hBackward : ContMDiff I I n homeo.symm)
    {first second : OpenPartialHomeomorph M H}
    (hFirst : first ∈ IsManifold.maximalAtlas I n M)
    (hSecond : second ∈ IsManifold.maximalAtlas I n M) :
    (first.symm.trans homeo.toOpenPartialHomeomorph).trans second ∈
      contDiffGroupoid n I := by
  let deck := homeo.toOpenPartialHomeomorph
  let transition := (first.symm.trans deck).trans second
  have hLocal : ChartedSpace.LiftPropOn
      (contDiffGroupoid n I).IsLocalStructomorphWithinAt
      deck deck.source := by
    rw [isLocalStructomorphOn_contDiffGroupoid_iff]
    constructor
    · exact hForward.contMDiffOn.congr fun _ _ => rfl
    · exact hBackward.contMDiffOn.congr fun _ _ => rfl
  apply (contDiffGroupoid n I).locality
  intro coordinate hCoordinate
  have hCoordinate' : coordinate ∈ first.target ∩
      first.symm ⁻¹' (deck.source ∩ deck ⁻¹' second.source) := by
    simpa only [transition, deck, mfld_simps] using hCoordinate
  have hProperty :=
    StructureGroupoid.LocalInvariantProp.liftPropOn_indep_chart
      (StructureGroupoid.isLocalStructomorphWithinAt_localInvariantProp
        (contDiffGroupoid n I))
      hFirst hSecond hLocal hCoordinate'
  obtain ⟨localMap, hLocalMap, hEqual, hCoordinateLocal⟩ :=
    hProperty hCoordinate'.2.1
  let neighborhood := transition.source ∩ localMap.source
  refine ⟨neighborhood, transition.open_source.inter localMap.open_source,
    ⟨hCoordinate, hCoordinateLocal⟩, ?_⟩
  have hEqualTransition : Set.EqOn transition localMap
      (transition.source ∩ localMap.source) := by
    intro point hPoint
    exact hEqual ⟨by simp [deck], hPoint.2⟩
  rw [OpenPartialHomeomorph.restr_source_inter]
  exact (contDiffGroupoid n I).mem_of_eqOnSource
    (closedUnderRestriction' hLocalMap transition.open_source)
    (OpenPartialHomeomorph.Set.EqOn.restr_eqOn_source hEqualTransition)

end MaximalSmoothHomeomorphCoordinates

section ArbitraryLocalSectionCharts

variable {𝕜 E H X : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] [TopologicalSpace X] [T2Space X]
  [LocallyCompactSpace X]
  (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)

theorem localSectionChart_transition_mem_groupoid_of_mem_maximalAtlas
    (data : MappingTorusData X)
    [ChartedSpace H (MappingTorusCover data)]
    [IsManifold I n (MappingTorusCover data)]
    (hDeck : ∀ winding : ℤ,
      ContMDiff I I n
        (winding +ᵥ · : MappingTorusCover data → MappingTorusCover data))
    (firstAnchor secondAnchor : MappingTorusCover data)
    (firstChart secondChart : OpenPartialHomeomorph (MappingTorusCover data) H)
    (hFirstChart : firstChart ∈
      IsManifold.maximalAtlas I n (MappingTorusCover data))
    (hSecondChart : secondChart ∈
      IsManifold.maximalAtlas I n (MappingTorusCover data)) :
    let hf := (mappingTorusMk_isCoveringMap data).isLocalHomeomorph
    ((hf.localInverseAt firstAnchor).trans firstChart).symm.trans
      ((hf.localInverseAt secondAnchor).trans secondChart) ∈
        contDiffGroupoid n I := by
  let hf := (mappingTorusMk_isCoveringMap data).isLocalHomeomorph
  let firstSection := hf.localInverseAt firstAnchor
  let secondSection := hf.localInverseAt secondAnchor
  let transition := (firstSection.trans firstChart).symm.trans
    (secondSection.trans secondChart)
  change transition ∈ contDiffGroupoid n I
  apply (contDiffGroupoid n I).locality
  intro coordinate hCoordinate
  have hCoordinate' := hCoordinate
  simp only [transition, firstSection, secondSection, mfld_simps] at hCoordinate'
  let base := firstSection.symm (firstChart.symm coordinate)
  let firstPoint := firstChart.symm coordinate
  let secondPoint := secondSection base
  have hFirstPointTarget : firstPoint ∈ firstSection.target :=
    hCoordinate'.1.2
  have hFirstSource : base ∈ firstSection.source :=
    firstSection.symm.map_source hFirstPointTarget
  have hSecondSource : base ∈ secondSection.source := hCoordinate'.2.1
  have hFirstValue : firstSection base = firstPoint :=
    firstSection.right_inv hFirstPointTarget
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
    exact (hDeck (-winding)).congr fun point => by simp [deck]
  have hDeckTransition : deckTransition ∈ contDiffGroupoid n I := by
    exact smoothHomeomorph_coordinateChange_mem_groupoid_of_mem_maximalAtlas
      deck hDeckForward hDeckBackward hFirstChart hSecondChart
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
  have hLocalMap : localMap ∈ contDiffGroupoid n I :=
    closedUnderRestriction' hDeckTransition hSmoothOpen
  have hCoordinateLocal : coordinate ∈ localMap.source := by
    simp only [localMap, mfld_simps]
    exact ⟨hDeckCoordinate, by
      simpa [hSmoothOpen.interior_eq] using hCoordinateSmooth⟩
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

theorem localSectionTrans_mem_maximalAtlas
    (data : MappingTorusData X)
    [ChartedSpace H (MappingTorusCover data)]
    [IsManifold I n (MappingTorusCover data)]
    (hDeck : ∀ winding : ℤ,
      ContMDiff I I n
        (winding +ᵥ · : MappingTorusCover data → MappingTorusCover data))
    (anchor : MappingTorusCover data)
    (coverChart : OpenPartialHomeomorph (MappingTorusCover data) H)
    (hCoverChart : coverChart ∈
      IsManifold.maximalAtlas I n (MappingTorusCover data)) :
    letI : ChartedSpace H (MappingTorus data) :=
      mappingTorusSmoothChartedSpace data
    let hf := (mappingTorusMk_isCoveringMap data).isLocalHomeomorph
    (hf.localInverseAt anchor).trans coverChart ∈
      IsManifold.maximalAtlas I n (MappingTorus data) := by
  letI : ChartedSpace H (MappingTorus data) :=
    mappingTorusSmoothChartedSpace data
  letI : IsManifold I n (MappingTorus data) :=
    mappingTorus_isManifold_of_smooth_deck I n data hDeck
  dsimp only
  intro selectedChart hSelectedChart
  rcases hSelectedChart with ⟨selectedBase, rfl⟩
  constructor
  · exact localSectionChart_transition_mem_groupoid_of_mem_maximalAtlas
      I n data hDeck anchor _ coverChart _ hCoverChart
      (IsManifold.chart_mem_maximalAtlas _)
  · exact localSectionChart_transition_mem_groupoid_of_mem_maximalAtlas
      I n data hDeck _ anchor _ coverChart
      (IsManifold.chart_mem_maximalAtlas _) hCoverChart

end ArbitraryLocalSectionCharts

set_option backward.isDefEq.respectTransparency false in
theorem fixedThroatQuotientInclusion_isImmersionOfComplement
    (period : ℝ) (hPeriod : period ≠ 0) :
    letI : ChartedSpace ThroatCoverModel
        (MappingTorus (fixedEquatorData period hPeriod)) :=
      fixedThroatQuotientChartedSpace period hPeriod
    letI : ChartedSpace CoverModel
        (MappingTorus (reflectedSphereData period hPeriod)) :=
      reflectedSphereQuotientChartedSpace period hPeriod
    Manifold.IsImmersionOfComplement ThroatNormalComplement
      throatCoverModelWithCorners coverModelWithCorners ω
      (fixedThroatQuotientInclusion period hPeriod) := by
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
  letI : ChartedSpace ThroatCoverModel
      (MappingTorus (fixedEquatorData period hPeriod)) :=
    fixedThroatQuotientChartedSpace period hPeriod
  letI : IsManifold throatCoverModelWithCorners ω
      (MappingTorus (fixedEquatorData period hPeriod)) :=
    fixedThroatQuotient_isManifold period hPeriod
  letI : ChartedSpace CoverModel
      (MappingTorus (reflectedSphereData period hPeriod)) :=
    reflectedSphereQuotientChartedSpace period hPeriod
  letI : IsManifold coverModelWithCorners ω
      (MappingTorus (reflectedSphereData period hPeriod)) :=
    reflectedSphereQuotient_isManifold period hPeriod
  intro quotientPoint
  obtain ⟨anchor, rfl⟩ :=
    mappingTorusMk_surjective (fixedEquatorData period hPeriod) quotientPoint
  let sourceProjection :=
    (mappingTorusMk_isCoveringMap
      (fixedEquatorData period hPeriod)).isLocalHomeomorph
  let targetAnchor := fixedThroatCoverInclusion period hPeriod anchor
  let targetProjection :=
    (mappingTorusMk_isCoveringMap
      (reflectedSphereData period hPeriod)).isLocalHomeomorph
  let sourceSection := sourceProjection.localInverseAt anchor
  let targetSection := targetProjection.localInverseAt targetAnchor
  let hCover := fixedThroatCoverInclusion_isImmersionOfComplement
    period hPeriod anchor
  let sourceRestriction : Set
      (MappingTorusCover (fixedEquatorData period hPeriod)) :=
    fixedThroatCoverInclusion period hPeriod ⁻¹' targetSection.target
  have hSourceRestrictionOpen : IsOpen sourceRestriction :=
    targetSection.open_target.preimage
      (continuous_fixedThroatCoverInclusion period hPeriod)
  let sourceCoverChart := hCover.domChart.restr sourceRestriction
  have hSourceCoverChart : sourceCoverChart ∈
      IsManifold.maximalAtlas throatCoverModelWithCorners ω
        (MappingTorusCover (fixedEquatorData period hPeriod)) := by
    exact restr_mem_maximalAtlas (contDiffGroupoid ω throatCoverModelWithCorners)
      hCover.domChart_mem_maximalAtlas hSourceRestrictionOpen
  let sourceChart := sourceSection.trans sourceCoverChart
  let targetChart := targetSection.trans hCover.codChart
  apply Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
    (continuous_fixedThroatQuotientInclusion period hPeriod).continuousAt
    hCover.equiv sourceChart targetChart
  · simpa [sourceChart, sourceCoverChart, sourceRestriction,
      hSourceRestrictionOpen.interior_eq, sourceSection, sourceProjection,
      targetSection, targetProjection, targetAnchor] using
      hCover.mem_domChart_source
  · simpa [targetChart, targetSection, targetProjection, targetAnchor,
      fixedThroatQuotientInclusion_mk] using hCover.mem_codChart_source
  · exact localSectionTrans_mem_maximalAtlas throatCoverModelWithCorners ω
      (fixedEquatorData period hPeriod)
      (fixedThroatCover_deck_contMDiff period hPeriod)
      anchor sourceCoverChart hSourceCoverChart
  · exact localSectionTrans_mem_maximalAtlas coverModelWithCorners ω
      (reflectedSphereData period hPeriod)
      (reflectedSphereCover_deck_contMDiff period hPeriod)
      targetAnchor hCover.codChart hCover.codChart_mem_maximalAtlas
  · intro coordinate hCoordinate
    have hCoordinateData := hCoordinate
    simp only [sourceChart, mfld_simps] at hCoordinateData
    have hCoordinate' :
        coordinate ∈ (hCover.domChart.extend throatCoverModelWithCorners).target := by
      have hSourceCoverTarget := hCoordinateData.1
      simpa [sourceCoverChart] using hSourceCoverTarget.1
    let coverPoint := sourceCoverChart.symm coordinate
    have hCoverPointRestriction : coverPoint ∈ sourceRestriction := by
      have hCoverPointSource := sourceCoverChart.symm.map_source hCoordinateData.1
      exact interior_subset hCoverPointSource.2
    have hTargetInverse :
        targetSection
            (mappingTorusMk (reflectedSphereData period hPeriod)
              (fixedThroatCoverInclusion period hPeriod coverPoint)) =
          fixedThroatCoverInclusion period hPeriod coverPoint := by
      simpa [targetSection, targetProjection] using
        targetSection.right_inv hCoverPointRestriction
    have hWritten := hCover.writtenInCharts hCoordinate'
    have hWritten' := hWritten
    simp only [Function.comp_apply, mfld_simps] at hWritten'
    have hReflCoordinate :
        (PartialEquiv.refl ThroatCoverCoordinates).symm coordinate = coordinate :=
      rfl
    rw [hReflCoordinate] at hWritten'
    have hSourceProjection
        (point : MappingTorusCover (fixedEquatorData period hPeriod)) :
        sourceSection.symm point =
          mappingTorusMk (fixedEquatorData period hPeriod) point := by
      simp [sourceSection, sourceProjection.localInverseAt_symm]
    let chartPoint := hCover.domChart.symm
      ((PartialEquiv.refl ThroatCoverCoordinates).symm coordinate)
    have hChartPoint : chartPoint = coverPoint := by
      simp [chartPoint, coverPoint, sourceCoverChart]
    have hTargetInverseChart :
        targetSection
            (mappingTorusMk (reflectedSphereData period hPeriod)
              (fixedThroatCoverInclusion period hPeriod chartPoint)) =
          fixedThroatCoverInclusion period hPeriod chartPoint := by
      simpa [hChartPoint] using hTargetInverse
    simpa [sourceChart, targetChart, sourceCoverChart, hSourceProjection,
      fixedThroatQuotientInclusion_mk, hTargetInverseChart, chartPoint] using hWritten'

theorem fixedThroatCoverInclusion_isSmoothEmbedding
    (period : ℝ) (hPeriod : period ≠ 0) :
    letI : ChartedSpace ThroatCoverModel
        (MappingTorusCover (fixedEquatorData period hPeriod)) :=
      fixedThroatCoverChartedSpace period hPeriod
    letI : ChartedSpace CoverModel
        (MappingTorusCover (reflectedSphereData period hPeriod)) :=
      reflectedSphereCoverChartedSpace period hPeriod
    Manifold.IsSmoothEmbedding throatCoverModelWithCorners
      coverModelWithCorners ω (fixedThroatCoverInclusion period hPeriod) := by
  letI : ChartedSpace ThroatCoverModel
      (MappingTorusCover (fixedEquatorData period hPeriod)) :=
    fixedThroatCoverChartedSpace period hPeriod
  letI : ChartedSpace CoverModel
      (MappingTorusCover (reflectedSphereData period hPeriod)) :=
    reflectedSphereCoverChartedSpace period hPeriod
  exact ⟨(fixedThroatCoverInclusion_isImmersionOfComplement
    period hPeriod).isImmersion,
    fixedThroatCoverInclusion_isEmbedding period hPeriod⟩

theorem fixedThroatQuotientInclusion_isImmersion
    (period : ℝ) (hPeriod : period ≠ 0) :
    letI : ChartedSpace ThroatCoverModel
        (MappingTorus (fixedEquatorData period hPeriod)) :=
      fixedThroatQuotientChartedSpace period hPeriod
    letI : ChartedSpace CoverModel
        (MappingTorus (reflectedSphereData period hPeriod)) :=
      reflectedSphereQuotientChartedSpace period hPeriod
    Manifold.IsImmersion throatCoverModelWithCorners coverModelWithCorners ω
      (fixedThroatQuotientInclusion period hPeriod) := by
  letI : ChartedSpace ThroatCoverModel
      (MappingTorus (fixedEquatorData period hPeriod)) :=
    fixedThroatQuotientChartedSpace period hPeriod
  letI : ChartedSpace CoverModel
      (MappingTorus (reflectedSphereData period hPeriod)) :=
    reflectedSphereQuotientChartedSpace period hPeriod
  exact (fixedThroatQuotientInclusion_isImmersionOfComplement
    period hPeriod).isImmersion

theorem fixedThroatQuotientInclusion_isSmoothEmbedding
    (period : ℝ) (hPeriod : period ≠ 0) :
    letI : ChartedSpace ThroatCoverModel
        (MappingTorus (fixedEquatorData period hPeriod)) :=
      fixedThroatQuotientChartedSpace period hPeriod
    letI : ChartedSpace CoverModel
        (MappingTorus (reflectedSphereData period hPeriod)) :=
      reflectedSphereQuotientChartedSpace period hPeriod
    Manifold.IsSmoothEmbedding throatCoverModelWithCorners
      coverModelWithCorners ω
      (fixedThroatQuotientInclusion period hPeriod) := by
  letI : ChartedSpace ThroatCoverModel
      (MappingTorus (fixedEquatorData period hPeriod)) :=
    fixedThroatQuotientChartedSpace period hPeriod
  letI : ChartedSpace CoverModel
      (MappingTorus (reflectedSphereData period hPeriod)) :=
    reflectedSphereQuotientChartedSpace period hPeriod
  exact ⟨fixedThroatQuotientInclusion_isImmersion period hPeriod,
    fixedThroatQuotientInclusion_isEmbedding period hPeriod⟩

theorem fixedThroatQuotientInclusion_fullSmoothEmbeddingClosure
    (period : ℝ) (hPeriod : period ≠ 0) :
    letI : ChartedSpace ThroatCoverModel
        (MappingTorus (fixedEquatorData period hPeriod)) :=
      fixedThroatQuotientChartedSpace period hPeriod
    letI : ChartedSpace CoverModel
        (MappingTorus (reflectedSphereData period hPeriod)) :=
      reflectedSphereQuotientChartedSpace period hPeriod
    Manifold.IsSmoothEmbedding throatCoverModelWithCorners
        coverModelWithCorners ω
        (fixedThroatQuotientInclusion period hPeriod) ∧
      Manifold.IsImmersionOfComplement ThroatNormalComplement
        throatCoverModelWithCorners coverModelWithCorners ω
        (fixedThroatQuotientInclusion period hPeriod) ∧
      Topology.IsClosedEmbedding
        (fixedThroatQuotientInclusion period hPeriod) ∧
      (∀ point, Function.Injective
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatQuotientInclusion period hPeriod) point)) ∧
      ∀ point, Module.finrank ℝ
        (TangentSpace coverModelWithCorners
            (fixedThroatQuotientInclusion period hPeriod point) ⧸
          LinearMap.range
            (mfderiv throatCoverModelWithCorners coverModelWithCorners
              (fixedThroatQuotientInclusion period hPeriod) point).toLinearMap) = 1 := by
  letI : ChartedSpace ThroatCoverModel
      (MappingTorus (fixedEquatorData period hPeriod)) :=
    fixedThroatQuotientChartedSpace period hPeriod
  letI : ChartedSpace CoverModel
      (MappingTorus (reflectedSphereData period hPeriod)) :=
    reflectedSphereQuotientChartedSpace period hPeriod
  refine ⟨fixedThroatQuotientInclusion_isSmoothEmbedding period hPeriod,
    fixedThroatQuotientInclusion_isImmersionOfComplement period hPeriod,
    fixedThroatQuotientInclusion_isClosedEmbedding period hPeriod,
    mfderiv_fixedThroatQuotientInclusion_injective period hPeriod,
    mfderiv_fixedThroatQuotientInclusion_normal_finrank period hPeriod⟩

end

end P0EFTJanusMappingTorusIsSmoothEmbedding
end JanusFormal
