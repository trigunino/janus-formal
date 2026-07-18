import Mathlib.Geometry.Manifold.SmoothEmbedding
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusSmoothQuotientManifold
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusThroatComplementSides

/-!
# The effective throat is a closed smooth map into the smooth quotient

This gate proves the global topological-embedding part of the effective
fixed-throat inclusion.  Closedness is descended from the closed equatorial
cover inclusion through the two orbit quotient maps.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusSmoothThroatEmbedding

set_option autoImplicit false

noncomputable section

open Set Topology
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusThroatComplementSides

universe u

set_option backward.isDefEq.respectTransparency false in
private def tangentSpaceModelEquiv
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H M : Type*} [TopologicalSpace H] [TopologicalSpace M]
    [ChartedSpace H M] (I : ModelWithCorners ℝ E H) (point : M) :
    TangentSpace I point ≃L[ℝ] E :=
  ContinuousLinearEquiv.refl ℝ E

section AmbientDifferential

/-- Linear zero-normal insertion underlying the standard equatorial sphere
inclusion. -/
def euclideanEquatorInsertLinearMap : EuclideanR3 →ₗ[ℝ] EuclideanR4 where
  toFun point :=
    (EuclideanSpace.equiv (Fin 4) ℝ).symm
      (Fin.cases 0 ((EuclideanSpace.equiv (Fin 3) ℝ) point))
  map_add' first second := by
    apply (EuclideanSpace.equiv (Fin 4) ℝ).injective
    funext index
    refine Fin.cases ?_ (fun tailIndex => ?_) index
    · simp
    · simp
  map_smul' scalar point := by
    apply (EuclideanSpace.equiv (Fin 4) ℝ).injective
    funext index
    refine Fin.cases ?_ (fun tailIndex => ?_) index
    · simp
    · simp

/-- Continuous-linear packaging of the zero-normal insertion. -/
def euclideanEquatorInsertCLM : EuclideanR3 →L[ℝ] EuclideanR4 :=
  LinearMap.toContinuousLinearMap euclideanEquatorInsertLinearMap

@[simp] theorem euclideanEquatorInsertCLM_apply (point : EuclideanR3) :
    euclideanEquatorInsertCLM point = euclideanEquatorInsert point :=
  rfl

theorem euclideanEquatorInsertCLM_injective :
    Function.Injective euclideanEquatorInsertCLM := by
  intro first second hEqual
  apply (EuclideanSpace.equiv (Fin 3) ℝ).injective
  funext index
  have hCoordinate := congrFun
    (congrArg (EuclideanSpace.equiv (Fin 4) ℝ) hEqual) index.succ
  simpa [euclideanEquatorInsertCLM, euclideanEquatorInsertLinearMap] using hCoordinate

/-- The ambient differential of zero-normal insertion is injective at every
point. -/
theorem mfderiv_euclideanEquatorInsert_injective (point : EuclideanR3) :
    Function.Injective
      (mfderiv 𝓘(ℝ, EuclideanR3) 𝓘(ℝ, EuclideanR4)
        euclideanEquatorInsert point) := by
  rw [show euclideanEquatorInsert = euclideanEquatorInsertCLM from by
    funext coordinate
    exact (euclideanEquatorInsertCLM_apply coordinate).symm]
  rw [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv]
  exact euclideanEquatorInsertCLM_injective

/-- The standard equatorial inclusion `S² → S³` has injective manifold
differential. -/
theorem mfderiv_standardEquatorInclusion_injective
    (point : StandardEquatorialTwoSphere) :
    Function.Injective
      (mfderiv (𝓡 2) (𝓡 3) standardEquatorInclusion point) := by
  letI : Fact (Module.finrank ℝ EuclideanR3 = 2 + 1) := ⟨by simp⟩
  letI : Fact (Module.finrank ℝ EuclideanR4 = 3 + 1) := ⟨by simp⟩
  have hInclusion : MDifferentiableAt (𝓡 2) (𝓡 3)
      standardEquatorInclusion point :=
    standardEquatorInclusion_contMDiff.mdifferentiableAt (by simp)
  have hTargetCoe : MDifferentiableAt (𝓡 3) 𝓘(ℝ, EuclideanR4)
      ((↑) : StandardUnitThreeSphere → EuclideanR4)
      (standardEquatorInclusion point) :=
    (contMDiff_coe_sphere (m := ω) (n := 3)
      (standardEquatorInclusion point)).mdifferentiableAt (by simp)
  have hSourceCoe : MDifferentiableAt (𝓡 2) 𝓘(ℝ, EuclideanR3)
      ((↑) : StandardEquatorialTwoSphere → EuclideanR3) point :=
    (contMDiff_coe_sphere (m := ω) (n := 2) point).mdifferentiableAt (by simp)
  have hAmbient : MDifferentiableAt 𝓘(ℝ, EuclideanR3)
      𝓘(ℝ, EuclideanR4) euclideanEquatorInsert point.1 :=
    euclideanEquatorInsert_contDiff.contMDiff.mdifferentiableAt (by simp)
  have hDerivative :
      (mfderiv (𝓡 3) 𝓘(ℝ, EuclideanR4)
          ((↑) : StandardUnitThreeSphere → EuclideanR4)
          (standardEquatorInclusion point)).comp
        (mfderiv (𝓡 2) (𝓡 3) standardEquatorInclusion point) =
      (mfderiv 𝓘(ℝ, EuclideanR3) 𝓘(ℝ, EuclideanR4)
          euclideanEquatorInsert point.1).comp
        (mfderiv (𝓡 2) 𝓘(ℝ, EuclideanR3)
          ((↑) : StandardEquatorialTwoSphere → EuclideanR3) point) := by
    rw [← mfderiv_comp point hTargetCoe hInclusion,
      ← mfderiv_comp point hAmbient hSourceCoe]
    rfl
  intro first second hEqual
  apply mfderiv_coe_sphere_injective (n := 2) point
  apply mfderiv_euclideanEquatorInsert_injective point.1
  have hFirst := congrArg (fun derivative => derivative first) hDerivative
  have hSecond := congrArg (fun derivative => derivative second) hDerivative
  simp only [ContinuousLinearMap.comp_apply] at hFirst hSecond
  exact hFirst.symm.trans ((congrArg _ hEqual).trans hSecond)

end AmbientDifferential

section DifferentialTransport

variable {𝕜 E F H G M N : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace H] [TopologicalSpace G]
  (I : ModelWithCorners 𝕜 E H) (J : ModelWithCorners 𝕜 F G)
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N]

/-- A differentiable map with a differentiable left inverse has injective
manifold differential. -/
theorem mfderiv_injective_of_leftInverse
    {forward : M → N} {backward : N → M} (point : M)
    (hForward : MDifferentiableAt I J forward point)
    (hBackward : MDifferentiableAt J I backward (forward point))
    (hLeft : Function.LeftInverse backward forward) :
    Function.Injective (mfderiv I J forward point) := by
  intro first second hEqual
  have hDerivative := mfderiv_comp point hBackward hForward
  rw [hLeft.comp_eq_id, mfderiv_id] at hDerivative
  have hFirst := congrArg (fun derivative => derivative first) hDerivative
  have hSecond := congrArg (fun derivative => derivative second) hDerivative
  exact hFirst.trans ((congrArg _ hEqual).trans hSecond.symm)

end DifferentialTransport

section ActualSphereDifferential

/-- The algebraic equatorial inclusion used by the mapping-torus cover has
injective manifold differential for the transported analytic atlases. -/
theorem mfderiv_equatorialSphereInclusion_injective
    (point : EquatorialTwoSphere) :
    Function.Injective
      (mfderiv (𝓡 2) (𝓡 3) equatorialSphereInclusion point) := by
  have hSourceForward := chartedSpacePullback_toFun_contMDiff
    (𝓡 2) ω equatorialTwoSphereHomeomorph
  have hSourceBackward := chartedSpacePullback_invFun_contMDiff
    (𝓡 2) ω equatorialTwoSphereHomeomorph
  have hTargetBackward := chartedSpacePullback_invFun_contMDiff
    (𝓡 3) ω unitThreeSphereHomeomorph
  have hTargetForward := chartedSpacePullback_toFun_contMDiff
    (𝓡 3) ω unitThreeSphereHomeomorph
  have hSourceAt : MDifferentiableAt (𝓡 2) (𝓡 2)
      equatorialTwoSphereHomeomorph point :=
    hSourceForward.mdifferentiableAt (by simp)
  have hStandardAt : MDifferentiableAt (𝓡 2) (𝓡 3)
      standardEquatorInclusion (equatorialTwoSphereHomeomorph point) :=
    standardEquatorInclusion_contMDiff.mdifferentiableAt (by simp)
  have hTargetBackwardAt : MDifferentiableAt (𝓡 3) (𝓡 3)
      unitThreeSphereHomeomorph.symm
      (standardEquatorInclusion (equatorialTwoSphereHomeomorph point)) :=
    hTargetBackward.mdifferentiableAt (by simp)
  have hTargetForwardAt : MDifferentiableAt (𝓡 3) (𝓡 3)
      unitThreeSphereHomeomorph
      (unitThreeSphereHomeomorph.symm
        (standardEquatorInclusion (equatorialTwoSphereHomeomorph point))) :=
    hTargetForward.mdifferentiableAt (by simp)
  have hSourceDerivative : Function.Injective
      (mfderiv (𝓡 2) (𝓡 2) equatorialTwoSphereHomeomorph point) :=
    mfderiv_injective_of_leftInverse (𝓡 2) (𝓡 2) point hSourceAt
      (hSourceBackward.mdifferentiableAt (x := equatorialTwoSphereHomeomorph point)
        (by simp))
      equatorialTwoSphereHomeomorph.left_inv
  have hStandardDerivative : Function.Injective
      (mfderiv (𝓡 2) (𝓡 3) standardEquatorInclusion
        (equatorialTwoSphereHomeomorph point)) :=
    mfderiv_standardEquatorInclusion_injective _
  have hTargetDerivative : Function.Injective
      (mfderiv (𝓡 3) (𝓡 3) unitThreeSphereHomeomorph.symm
        (standardEquatorInclusion (equatorialTwoSphereHomeomorph point))) :=
    mfderiv_injective_of_leftInverse (𝓡 3) (𝓡 3) _ hTargetBackwardAt
      hTargetForwardAt
      unitThreeSphereHomeomorph.right_inv
  rw [show equatorialSphereInclusion =
      unitThreeSphereHomeomorph.symm ∘ standardEquatorInclusion ∘
        equatorialTwoSphereHomeomorph from by
    funext source
    exact (standardEquatorInclusion_conjugates_actual source).symm]
  rw [mfderiv_comp point hTargetBackwardAt
      (hStandardAt.comp point hSourceAt),
    mfderiv_comp point hStandardAt hSourceAt]
  exact hTargetDerivative.comp (hStandardDerivative.comp hSourceDerivative)

set_option backward.isDefEq.respectTransparency false in
/-- The product of the equatorial inclusion with the identity time direction
has injective differential. -/
theorem mfderiv_equatorialSphereInclusion_prod_id_injective
    (point : EquatorialTwoSphere × ℝ) :
    Function.Injective
      (mfderiv throatCoverModelWithCorners coverModelWithCorners
        (Prod.map equatorialSphereInclusion (id : ℝ → ℝ)) point) := by
  have hSphere :=
    equatorialSphereInclusion_contMDiff.mdifferentiableAt (x := point.1) (by simp)
  have hTime : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
      (id : ℝ → ℝ) point.2 := mdifferentiableAt_id
  rw [mfderiv_prodMap hSphere hTime]
  intro first second hEqual
  apply Prod.ext
  · apply mfderiv_equatorialSphereInclusion_injective point.1
    exact congrArg Prod.fst hEqual
  · have hSecond := congrArg (fun output => output.2) hEqual
    change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (id : ℝ → ℝ) point.2 first.2 =
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (id : ℝ → ℝ) point.2 second.2
      at hSecond
    simpa only [mfderiv_id, id_eq, ContinuousLinearMap.id_apply] using hSecond

end ActualSphereDifferential

variable (period : ℝ) (hPeriod : period ≠ 0)

set_option backward.isDefEq.respectTransparency false in
/-- The lifted fixed-throat inclusion has injective differential for the
explicit analytic cover atlases. -/
theorem mfderiv_fixedThroatCoverInclusion_injective
    (point : MappingTorusCover (fixedEquatorData period hPeriod)) :
    letI : ChartedSpace ThroatCoverModel
        (MappingTorusCover (fixedEquatorData period hPeriod)) :=
      fixedThroatCoverChartedSpace period hPeriod
    letI : ChartedSpace CoverModel
        (MappingTorusCover (reflectedSphereData period hPeriod)) :=
      reflectedSphereCoverChartedSpace period hPeriod
    Function.Injective
      (mfderiv throatCoverModelWithCorners coverModelWithCorners
        (fixedThroatCoverInclusion period hPeriod) point) := by
  letI : ChartedSpace ThroatCoverModel
      (MappingTorusCover (fixedEquatorData period hPeriod)) :=
    fixedThroatCoverChartedSpace period hPeriod
  letI : ChartedSpace CoverModel
      (MappingTorusCover (reflectedSphereData period hPeriod)) :=
    reflectedSphereCoverChartedSpace period hPeriod
  let sourceHomeomorph :=
    coverHomeomorphProd (fixedEquatorData period hPeriod)
  let targetHomeomorph :=
    coverHomeomorphProd (reflectedSphereData period hPeriod)
  let productInclusion :=
    Prod.map equatorialSphereInclusion (id : ℝ → ℝ)
  have hSourceForward := chartedSpacePullback_toFun_contMDiff
    throatCoverModelWithCorners ω sourceHomeomorph
  have hSourceBackward := chartedSpacePullback_invFun_contMDiff
    throatCoverModelWithCorners ω sourceHomeomorph
  have hSourceAt : MDifferentiableAt throatCoverModelWithCorners
      throatCoverModelWithCorners sourceHomeomorph point :=
    hSourceForward.mdifferentiableAt (by simp)
  have hSourceBackwardAt : MDifferentiableAt throatCoverModelWithCorners
      throatCoverModelWithCorners sourceHomeomorph.symm
      (sourceHomeomorph point) :=
    hSourceBackward.mdifferentiableAt (by simp)
  have hTargetAt : MDifferentiableAt coverModelWithCorners
      coverModelWithCorners targetHomeomorph
      (fixedThroatCoverInclusion period hPeriod point) :=
    (chartedSpacePullback_toFun_contMDiff coverModelWithCorners ω
      targetHomeomorph).mdifferentiableAt (by simp)
  have hCoverAt : MDifferentiableAt throatCoverModelWithCorners
      coverModelWithCorners (fixedThroatCoverInclusion period hPeriod) point :=
    (fixedThroatCoverInclusion_contMDiff period hPeriod).mdifferentiableAt
      (by simp)
  have hProductAt : MDifferentiableAt throatCoverModelWithCorners
      coverModelWithCorners productInclusion (sourceHomeomorph point) :=
    (equatorialSphereInclusion_contMDiff.prodMap contMDiff_id)
      |>.mdifferentiableAt (by simp)
  have hSourceDerivative : Function.Injective
      (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
        sourceHomeomorph point) :=
    mfderiv_injective_of_leftInverse throatCoverModelWithCorners
      throatCoverModelWithCorners point hSourceAt hSourceBackwardAt
      sourceHomeomorph.left_inv
  have hProductDerivative : Function.Injective
      (mfderiv throatCoverModelWithCorners coverModelWithCorners
        productInclusion (sourceHomeomorph point)) :=
    mfderiv_equatorialSphereInclusion_prod_id_injective _
  have hDerivative :
      (mfderiv coverModelWithCorners coverModelWithCorners targetHomeomorph
          (fixedThroatCoverInclusion period hPeriod point)).comp
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatCoverInclusion period hPeriod) point) =
      (mfderiv throatCoverModelWithCorners coverModelWithCorners
          productInclusion (sourceHomeomorph point)).comp
        (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
          sourceHomeomorph point) := by
    rw [← mfderiv_comp point hTargetAt hCoverAt,
      ← mfderiv_comp point hProductAt hSourceAt]
    rfl
  intro first second hEqual
  apply hSourceDerivative
  apply hProductDerivative
  have hFirst := congrArg (fun derivative => derivative first) hDerivative
  have hSecond := congrArg (fun derivative => derivative second) hDerivative
  exact hFirst.symm.trans ((congrArg _ hEqual).trans hSecond)

/-- The range of the lifted fixed-throat inclusion is exactly the zero-normal
locus in the reflected-sphere cover. -/
theorem range_fixedThroatCoverInclusion :
    Set.range (fixedThroatCoverInclusion period hPeriod) =
      coverThroat period hPeriod := by
  ext point
  constructor
  · rintro ⟨source, rfl⟩
    exact source.fiber.2.2
  · intro hPoint
    change point.fiber.1 0 = 0 at hPoint
    let equator : EquatorialTwoSphere :=
      ⟨point.fiber.1, point.fiber.2, hPoint⟩
    let source : MappingTorusCover (fixedEquatorData period hPeriod) :=
      ⟨equator, point.time⟩
    refine ⟨source, ?_⟩
    apply MappingTorusCover.ext <;> rfl

/-- The lifted fixed-throat inclusion is a closed topological embedding. -/
theorem fixedThroatCoverInclusion_isClosedEmbedding :
    Topology.IsClosedEmbedding (fixedThroatCoverInclusion period hPeriod) := by
  refine ⟨fixedThroatCoverInclusion_isEmbedding period hPeriod, ?_⟩
  rw [range_fixedThroatCoverInclusion period hPeriod]
  exact coverThroat_isClosed period hPeriod

/-- Pulling the image of a throat-quotient set back to the four-dimensional
cover gives exactly the image of its pullback to the throat cover. -/
theorem targetProjection_preimage_image (subset : Set
    (MappingTorus (fixedEquatorData period hPeriod))) :
    mappingTorusMk (reflectedSphereData period hPeriod) ⁻¹'
        (fixedThroatQuotientInclusion period hPeriod '' subset) =
      fixedThroatCoverInclusion period hPeriod ''
        (mappingTorusMk (fixedEquatorData period hPeriod) ⁻¹' subset) := by
  ext point
  constructor
  · rintro ⟨throatPoint, hThroatPoint, hImage⟩
    obtain ⟨representative, rfl⟩ :=
      mappingTorusMk_surjective (fixedEquatorData period hPeriod) throatPoint
    rw [fixedThroatQuotientInclusion_mk] at hImage
    obtain ⟨winding, hWinding⟩ :=
      (mappingTorusMk_eq_iff_exists_vadd
        (reflectedSphereData period hPeriod) point
        (fixedThroatCoverInclusion period hPeriod representative)).1 hImage.symm
    refine ⟨winding +ᵥ representative, ?_, ?_⟩
    · change mappingTorusMk (fixedEquatorData period hPeriod)
          (winding +ᵥ representative) ∈ subset
      rw [(mappingTorusMk_isAddQuotientCoveringMap
        (fixedEquatorData period hPeriod)).map_vadd]
      exact hThroatPoint
    · rw [fixedThroatCoverInclusion_equivariant]
      exact hWinding
  · rintro ⟨representative, hRepresentative, rfl⟩
    refine ⟨mappingTorusMk (fixedEquatorData period hPeriod) representative,
      hRepresentative, ?_⟩
    exact fixedThroatQuotientInclusion_mk period hPeriod representative

/-- The quotient fixed-throat inclusion is a closed map. -/
theorem fixedThroatQuotientInclusion_isClosedMap :
    IsClosedMap (fixedThroatQuotientInclusion period hPeriod) := by
  intro subset hSubset
  have hSourcePreimage : IsClosed
      (mappingTorusMk (fixedEquatorData period hPeriod) ⁻¹' subset) :=
    hSubset.preimage
      (mappingTorusMk_isAddQuotientCoveringMap
        (fixedEquatorData period hPeriod)).continuous
  have hTargetPreimage : IsClosed
      (mappingTorusMk (reflectedSphereData period hPeriod) ⁻¹'
        (fixedThroatQuotientInclusion period hPeriod '' subset)) := by
    rw [targetProjection_preimage_image period hPeriod subset]
    exact (fixedThroatCoverInclusion_isClosedEmbedding period hPeriod).isClosedMap
      _ hSourcePreimage
  exact (mappingTorusMk_isAddQuotientCoveringMap
    (reflectedSphereData period hPeriod)).toIsQuotientMap.isCoinducing
      |>.isClosed_preimage.mp hTargetPreimage

/-- The effective fixed throat is a closed topological embedding in the
four-dimensional quotient. -/
theorem fixedThroatQuotientInclusion_isClosedEmbedding :
    Topology.IsClosedEmbedding
      (fixedThroatQuotientInclusion period hPeriod) :=
  Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_fixedThroatQuotientInclusion period hPeriod)
    (fixedThroatQuotientInclusion_injective period hPeriod)
    (fixedThroatQuotientInclusion_isClosedMap period hPeriod)

/-- In particular, the effective fixed throat carries exactly the subspace
topology induced from the effective four-dimensional quotient. -/
theorem fixedThroatQuotientInclusion_isEmbedding :
    Topology.IsEmbedding (fixedThroatQuotientInclusion period hPeriod) :=
  (fixedThroatQuotientInclusion_isClosedEmbedding period hPeriod).isEmbedding

set_option backward.isDefEq.respectTransparency false in
/-- The differential of the effective fixed-throat inclusion is injective at
every quotient point. -/
theorem mfderiv_fixedThroatQuotientInclusion_injective
    (point : MappingTorus (fixedEquatorData period hPeriod)) :
    letI : ChartedSpace ThroatCoverModel
        (MappingTorus (fixedEquatorData period hPeriod)) :=
      fixedThroatQuotientChartedSpace period hPeriod
    letI : ChartedSpace CoverModel
        (MappingTorus (reflectedSphereData period hPeriod)) :=
      reflectedSphereQuotientChartedSpace period hPeriod
    Function.Injective
      (mfderiv throatCoverModelWithCorners coverModelWithCorners
        (fixedThroatQuotientInclusion period hPeriod) point) := by
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
  obtain ⟨anchor, rfl⟩ :=
    mappingTorusMk_surjective (fixedEquatorData period hPeriod) point
  have hSourceLocal :=
    fixedThroat_projection_isLocalDiffeomorph period hPeriod anchor
  have hTargetLocal :=
    reflectedSphere_projection_isLocalDiffeomorph period hPeriod
      (fixedThroatCoverInclusion period hPeriod anchor)
  have hSourceAt := hSourceLocal.mdifferentiableAt (by simp)
  have hTargetAt := hTargetLocal.mdifferentiableAt (by simp)
  have hCoverAt : MDifferentiableAt throatCoverModelWithCorners
      coverModelWithCorners (fixedThroatCoverInclusion period hPeriod) anchor :=
    (fixedThroatCoverInclusion_contMDiff period hPeriod).mdifferentiableAt
      (by simp)
  have hQuotientAt : MDifferentiableAt throatCoverModelWithCorners
      coverModelWithCorners (fixedThroatQuotientInclusion period hPeriod)
      (mappingTorusMk (fixedEquatorData period hPeriod) anchor) :=
    (fixedThroatQuotientInclusion_contMDiff period hPeriod).mdifferentiableAt
      (by simp)
  have hCoverDerivative : Function.Injective
      (mfderiv throatCoverModelWithCorners coverModelWithCorners
        (fixedThroatCoverInclusion period hPeriod) anchor) :=
    mfderiv_fixedThroatCoverInclusion_injective period hPeriod anchor
  have hDerivative :
      (mfderiv coverModelWithCorners coverModelWithCorners
          (mappingTorusMk (reflectedSphereData period hPeriod))
          (fixedThroatCoverInclusion period hPeriod anchor)).comp
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatCoverInclusion period hPeriod) anchor) =
      (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatQuotientInclusion period hPeriod)
          (mappingTorusMk (fixedEquatorData period hPeriod) anchor)).comp
        (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
          (mappingTorusMk (fixedEquatorData period hPeriod)) anchor) := by
    rw [← mfderiv_comp anchor hTargetAt hCoverAt,
      ← mfderiv_comp anchor hQuotientAt hSourceAt]
    rfl
  intro first second hEqual
  obtain ⟨firstLift, hFirstLift⟩ :=
    (hSourceLocal.mfderivToContinuousLinearEquiv (by simp)).surjective first
  obtain ⟨secondLift, hSecondLift⟩ :=
    (hSourceLocal.mfderivToContinuousLinearEquiv (by simp)).surjective second
  have hFirstLift' :
      mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
        (mappingTorusMk (fixedEquatorData period hPeriod)) anchor firstLift = first := by
    rw [← hSourceLocal.mfderivToContinuousLinearEquiv_coe (by simp)]
    exact hFirstLift
  have hSecondLift' :
      mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
        (mappingTorusMk (fixedEquatorData period hPeriod)) anchor secondLift = second := by
    rw [← hSourceLocal.mfderivToContinuousLinearEquiv_coe (by simp)]
    exact hSecondLift
  have hLiftEqual : firstLift = secondLift := by
    apply hCoverDerivative
    apply (hTargetLocal.mfderivToContinuousLinearEquiv (by simp)).injective
    have hFirst := congrArg (fun derivative => derivative firstLift) hDerivative
    have hSecond := congrArg (fun derivative => derivative secondLift) hDerivative
    change mfderiv coverModelWithCorners coverModelWithCorners
          (mappingTorusMk (reflectedSphereData period hPeriod))
          (fixedThroatCoverInclusion period hPeriod anchor)
          (mfderiv throatCoverModelWithCorners coverModelWithCorners
            (fixedThroatCoverInclusion period hPeriod) anchor firstLift) =
        mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatQuotientInclusion period hPeriod)
          (mappingTorusMk (fixedEquatorData period hPeriod) anchor)
          (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
            (mappingTorusMk (fixedEquatorData period hPeriod)) anchor firstLift)
      at hFirst
    change mfderiv coverModelWithCorners coverModelWithCorners
          (mappingTorusMk (reflectedSphereData period hPeriod))
          (fixedThroatCoverInclusion period hPeriod anchor)
          (mfderiv throatCoverModelWithCorners coverModelWithCorners
            (fixedThroatCoverInclusion period hPeriod) anchor secondLift) =
        mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatQuotientInclusion period hPeriod)
          (mappingTorusMk (fixedEquatorData period hPeriod) anchor)
          (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
            (mappingTorusMk (fixedEquatorData period hPeriod)) anchor secondLift)
      at hSecond
    exact hFirst.trans
      (((congrArg _ hFirstLift').trans hEqual |>.trans
        (congrArg _ hSecondLift').symm).trans hSecond.symm)
  exact hFirstLift'.symm.trans ((congrArg _ hLiftEqual).trans hSecondLift')

set_option backward.isDefEq.respectTransparency false in
/-- The differential normal quotient has real dimension one at every throat
point.  This is the pointwise codimension-one part of the normal-line
identification. -/
theorem mfderiv_fixedThroatQuotientInclusion_normal_finrank
    (point : MappingTorus (fixedEquatorData period hPeriod)) :
    letI : ChartedSpace ThroatCoverModel
        (MappingTorus (fixedEquatorData period hPeriod)) :=
      fixedThroatQuotientChartedSpace period hPeriod
    letI : ChartedSpace CoverModel
        (MappingTorus (reflectedSphereData period hPeriod)) :=
      reflectedSphereQuotientChartedSpace period hPeriod
    Module.finrank ℝ
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
  let derivative := mfderiv throatCoverModelWithCorners coverModelWithCorners
    (fixedThroatQuotientInclusion period hPeriod) point
  let sourceEquiv := tangentSpaceModelEquiv throatCoverModelWithCorners point
  let targetEquiv := tangentSpaceModelEquiv coverModelWithCorners
    (fixedThroatQuotientInclusion period hPeriod point)
  letI : FiniteDimensional ℝ
      (TangentSpace throatCoverModelWithCorners point) :=
    sourceEquiv.toLinearEquiv.symm.finiteDimensional
  letI : FiniteDimensional ℝ
      (TangentSpace coverModelWithCorners
        (fixedThroatQuotientInclusion period hPeriod point)) :=
    targetEquiv.toLinearEquiv.symm.finiteDimensional
  have hInjective : Function.Injective derivative :=
    mfderiv_fixedThroatQuotientInclusion_injective period hPeriod point
  have hRange : Module.finrank ℝ (LinearMap.range derivative.toLinearMap) =
      Module.finrank ℝ (TangentSpace throatCoverModelWithCorners point) :=
    LinearMap.finrank_range_of_inj hInjective
  have hDimension := (LinearMap.range derivative.toLinearMap).finrank_quotient_add_finrank
  change Module.finrank ℝ
      (TangentSpace coverModelWithCorners
          (fixedThroatQuotientInclusion period hPeriod point) ⧸
        LinearMap.range derivative.toLinearMap) = 1
  rw [hRange] at hDimension
  have hSource : Module.finrank ℝ
      (TangentSpace throatCoverModelWithCorners point) = 3 := by
    calc
      Module.finrank ℝ (TangentSpace throatCoverModelWithCorners point) =
          Module.finrank ℝ ThroatCoverCoordinates :=
        sourceEquiv.toLinearEquiv.finrank_eq
      _ = 3 := by simp [ThroatCoverCoordinates]
  have hTarget : Module.finrank ℝ
      (TangentSpace coverModelWithCorners
        (fixedThroatQuotientInclusion period hPeriod point)) = 4 := by
    calc
      Module.finrank ℝ (TangentSpace coverModelWithCorners
          (fixedThroatQuotientInclusion period hPeriod point)) =
          Module.finrank ℝ CoverCoordinates :=
        targetEquiv.toLinearEquiv.finrank_eq
      _ = 4 := by simp [CoverCoordinates]
  omega

/-- Complete checked smooth-embedding data available in Mathlib today:
smoothness, the global subspace topology, and pointwise injective manifold
differential. -/
theorem fixedThroatQuotientInclusion_smoothEmbeddingData :
    letI : ChartedSpace ThroatCoverModel
        (MappingTorus (fixedEquatorData period hPeriod)) :=
      fixedThroatQuotientChartedSpace period hPeriod
    letI : ChartedSpace CoverModel
        (MappingTorus (reflectedSphereData period hPeriod)) :=
      reflectedSphereQuotientChartedSpace period hPeriod
    ContMDiff throatCoverModelWithCorners coverModelWithCorners ω
        (fixedThroatQuotientInclusion period hPeriod) ∧
      Topology.IsEmbedding (fixedThroatQuotientInclusion period hPeriod) ∧
      ∀ point, Function.Injective
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatQuotientInclusion period hPeriod) point) := by
  refine ⟨fixedThroatQuotientInclusion_contMDiff period hPeriod,
    fixedThroatQuotientInclusion_isEmbedding period hPeriod, ?_⟩
  exact mfderiv_fixedThroatQuotientInclusion_injective period hPeriod

end

end P0EFTJanusMappingTorusSmoothThroatEmbedding
end JanusFormal
