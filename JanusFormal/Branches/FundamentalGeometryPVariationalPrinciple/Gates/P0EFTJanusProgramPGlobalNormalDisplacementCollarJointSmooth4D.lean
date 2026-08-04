import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalNormalDisplacementCollarGraph4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusEquivariantSmoothDescent4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalNormalLiftContinuityReduction4D

/-!
# Joint smoothness of the global normal-displacement collar

The scalar coordinate of a genuine smooth normal section is smooth on the
mapping-torus cover.  Consequently the explicit `arctan` collar graph is
jointly smooth in the physical throat point and deformation parameter.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalNormalDisplacementCollarJointSmooth4D

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalNormalLiftContinuityReduction4D
open P0EFTJanusMappingTorusEquivariantSmoothDescent4D
open P0EFTJanusProgramPGlobalNormalDisplacementCollarGraph4D

attribute [local instance 10000] instChartedSpaceCoverModelEffectiveQuotient

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev throatData := fixedEquatorData period hPeriod
private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev ThroatCover := MappingTorusCover (throatData period hPeriod)
private abbrev EffectiveCover := MappingTorusCover (sphereData period hPeriod)
private abbrev EffectiveThroat := MappingTorus (throatData period hPeriod)
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance (priority := 20000) throatCoverChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatCover period hPeriod) :=
  fixedThroatCoverChartedSpace period hPeriod

local instance (priority := 20000) throatCoverIsManifold :
    IsManifold throatCoverModelWithCorners ω (ThroatCover period hPeriod) :=
  fixedThroatCover_isManifold period hPeriod

local instance (priority := 20000) effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance (priority := 20000) effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance (priority := 20000) normalCoreIsContMDiff :
    (fixedThroatNormalVectorBundleCore period hPeriod).IsContMDiff
      throatCoverModelWithCorners ω :=
  fixedThroatNormalVectorBundleCore_isContMDiff period hPeriod

local instance (priority := 20000) effectiveCoverChartedSpace :
    ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod

local instance (priority := 20000) effectiveCoverIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveCover period hPeriod) :=
  reflectedSphereCover_isManifold period hPeriod

local instance (priority := 20000) effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance (priority := 20000) effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private theorem normalCoordinateLift_eq_fixed_of_mem_target
    (displacement : SmoothNormalDisplacement period hPeriod)
    (anchor nearby : ThroatCover period hPeriod)
    (hNearby : nearby ∈
      ((mappingTorusMk_isCoveringMap (throatData period hPeriod)).isLocalHomeomorph
        |>.localInverseAt anchor).target) :
    normalCoordinateLift period hPeriod displacement nearby =
      ((fixedThroatNormalVectorBundleCore period hPeriod).localTriv anchor
        ⟨mappingTorusMk (throatData period hPeriod) nearby,
          displacement (mappingTorusMk (throatData period hPeriod) nearby)⟩).2 := by
  let core := fixedThroatNormalVectorBundleCore period hPeriod
  let projection :=
    (mappingTorusMk_isCoveringMap (throatData period hPeriod)).isLocalHomeomorph
  let base := mappingTorusMk (throatData period hPeriod) nearby
  have hFixed : base ∈ normalBundleBaseSet period hPeriod anchor := by
    change base ∈ (projection.localInverseAt anchor).source
    have hMapped := (projection.localInverseAt anchor).map_target hNearby
    simpa [base, projection] using hMapped
  have hMoving : base ∈ normalBundleBaseSet period hPeriod nearby := by
    exact mappingTorusMk_mem_normalBundleBaseSet period hPeriod nearby
  have hFixedInverse : projection.localInverseAt anchor base = nearby := by
    simpa [base, projection] using
      (projection.localInverseAt anchor).right_inv hNearby
  have hMovingInverse : projection.localInverseAt nearby base = nearby := by
    simp [base]
  have hTransition := localTransitionWinding_vadd period hPeriod
    anchor nearby base ⟨hFixed, hMoving⟩
  have hWinding : localTransitionWinding period hPeriod anchor nearby base = 0 := by
    apply IsCancelVAdd.right_cancel _ _ nearby
    rw [zero_vadd]
    simpa [hFixedInverse, hMovingInverse] using hTransition
  change core.coordChange (core.indexAt base) nearby base
      (displacement base) =
    core.coordChange (core.indexAt base) anchor base (displacement base)
  rw [← core.coordChange_comp (core.indexAt base) anchor nearby base
    ⟨⟨core.mem_baseSet_at base, hFixed⟩, hMoving⟩ (displacement base)]
  change normalSignCLM
      (localTransitionWinding period hPeriod anchor nearby base)
      (core.coordChange (core.indexAt base) anchor base (displacement base)) = _
  rw [hWinding]
  simp [normalSignCLM]

theorem normalCoordinateLift_contMDiff
    (displacement : SmoothNormalDisplacement period hPeriod) :
    ContMDiff throatCoverModelWithCorners (modelWithCornersSelf Real Real) ∞
      (normalCoordinateLift period hPeriod displacement) := by
  intro anchor
  let core := fixedThroatNormalVectorBundleCore period hPeriod
  let base := mappingTorusMk (throatData period hPeriod) anchor
  let localTriv := core.localTriv anchor
  letI : MemTrivializationAtlas localTriv := by
    refine ⟨⟨anchor, ?_⟩⟩
    rfl
  have hBase : base ∈ localTriv.baseSet := by
    exact mappingTorusMk_mem_normalBundleBaseSet period hPeriod anchor
  have hLocalCoordinate :
      ContMDiffAt throatCoverModelWithCorners (modelWithCornersSelf Real Real) ∞
        (fun point : EffectiveThroat period hPeriod =>
          (localTriv ⟨point, displacement point⟩).2) base := by
    exact (localTriv.contMDiffAt_section_iff hBase).mp
      (displacement.contMDiff.of_le (by simp)).contMDiffAt
  have hProjection : ContMDiffAt throatCoverModelWithCorners
      throatCoverModelWithCorners ∞
      (mappingTorusMk (throatData period hPeriod)) anchor :=
    (fixedThroat_projection_isLocalDiffeomorph period hPeriod).contMDiff
      |>.of_le (by simp)
      |>.contMDiffAt
  have hFixed : ContMDiffAt throatCoverModelWithCorners
      (modelWithCornersSelf Real Real) ∞
      (fun nearby : ThroatCover period hPeriod =>
        (localTriv
          ⟨mappingTorusMk (throatData period hPeriod) nearby,
            displacement (mappingTorusMk (throatData period hPeriod) nearby)⟩).2)
      anchor := by
    exact hLocalCoordinate.comp anchor hProjection
  apply hFixed.congr_of_eventuallyEq
  have hTarget :
      ((mappingTorusMk_isCoveringMap (throatData period hPeriod)).isLocalHomeomorph
        |>.localInverseAt anchor).target ∈ nhds anchor :=
    ((mappingTorusMk_isCoveringMap (throatData period hPeriod)).isLocalHomeomorph
      |>.localInverseAt anchor).open_target.mem_nhds
      ((mappingTorusMk_isCoveringMap (throatData period hPeriod)).isLocalHomeomorph
        |>.self_mem_localInverseAt_target)
  filter_upwards [hTarget] with nearby hNearby
  exact normalCoordinateLift_eq_fixed_of_mem_target period hPeriod
    displacement anchor nearby hNearby

theorem normalGraphCoordinateValue_joint_contMDiff
    (displacement : SmoothNormalDisplacement period hPeriod) :
    ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) ∞
      (fun point : ThroatCover period hPeriod × Real =>
        (normalGraphCoordinate period hPeriod displacement point.2 point.1).1) := by
  have hLift : ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) ∞
      (fun point : ThroatCover period hPeriod × Real =>
        normalCoordinateLift period hPeriod displacement point.1) :=
    (normalCoordinateLift_contMDiff period hPeriod displacement).comp contMDiff_fst
  have hProduct : ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) ∞
      (fun point : ThroatCover period hPeriod × Real =>
        point.2 * normalCoordinateLift period hPeriod displacement point.1) :=
    contMDiff_snd.mul hLift
  exact Real.contDiff_arctan.contMDiff.comp hProduct

theorem normalGraphCoverQuotientMap_joint_contMDiff
    (displacement : SmoothNormalDisplacement period hPeriod) :
    ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      coverModelWithCorners ∞
      (fun point : ThroatCover period hPeriod × Real =>
        mappingTorusMk (sphereData period hPeriod)
          (normalGraphCoverMap period hPeriod displacement point.2 point.1)) := by
  have hSourceCoordinates : ContMDiff throatCoverModelWithCorners
      throatCoverModelWithCorners ∞
      (coverHomeomorphProd (throatData period hPeriod)) :=
    chartedSpacePullback_toFun_contMDiff throatCoverModelWithCorners ∞
      (coverHomeomorphProd (throatData period hPeriod))
  have hSourceCoordinatesOnProduct : ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      throatCoverModelWithCorners ∞
      (fun point : ThroatCover period hPeriod × Real =>
        coverHomeomorphProd (throatData period hPeriod) point.1) :=
    hSourceCoordinates.comp contMDiff_fst
  have hSphere : ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real (EuclideanSpace Real (Fin 2))) ∞
      (fun point : ThroatCover period hPeriod × Real => point.1.fiber) :=
    contMDiff_fst.comp hSourceCoordinatesOnProduct
  have hTime : ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) ∞
      (fun point : ThroatCover period hPeriod × Real => point.1.time) :=
    contMDiff_snd.comp hSourceCoordinatesOnProduct
  have hStandardSphere : ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real (EuclideanSpace Real (Fin 2))) ∞
      (fun point : ThroatCover period hPeriod × Real =>
        equatorialTwoSphereHomeomorph point.1.fiber) :=
    (chartedSpacePullback_toFun_contMDiff
      (modelWithCornersSelf Real (EuclideanSpace Real (Fin 2))) ∞
      equatorialTwoSphereHomeomorph).comp hSphere
  have hBase : ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      canonicalLatitudeBaseModelWithCorners ∞
      (fun point : ThroatCover period hPeriod × Real =>
        (equatorialTwoSphereHomeomorph point.1.fiber, point.1.time)) :=
    hStandardSphere.prodMk hTime
  have hParameter : ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      canonicalLatitudeParameterModelWithCorners ∞
      (fun point : ThroatCover period hPeriod × Real =>
        ((equatorialTwoSphereHomeomorph point.1.fiber, point.1.time),
          (normalGraphCoordinate period hPeriod displacement point.2 point.1).1)) :=
    hBase.prodMk
      (normalGraphCoordinateValue_joint_contMDiff period hPeriod displacement)
  exact ((canonicalLatitudeCollar_contMDiff period hPeriod).comp hParameter).congr
    (fun point => by
      simp [canonicalLatitudeCollarMap, canonicalLatitudeAnchor,
        quotientNormalLatitude, normalGraphCoverMap])

def normalGraphInvariantMap
    (displacement : SmoothNormalDisplacement period hPeriod) :
    ThroatCover period hPeriod × Real → EffectiveQuotient period hPeriod :=
  fun point => mappingTorusMk (sphereData period hPeriod)
    (normalGraphCoverMap period hPeriod displacement point.2 point.1)

theorem normalGraphInvariantMap_vadd
    (displacement : SmoothNormalDisplacement period hPeriod)
    (winding : Int) (point : ThroatCover period hPeriod × Real) :
    normalGraphInvariantMap period hPeriod displacement
        (winding +ᵥ point.1, point.2) =
      normalGraphInvariantMap period hPeriod displacement point := by
  unfold normalGraphInvariantMap
  rw [normalGraphCoverMap_vadd]
  exact (mappingTorusMk_isAddQuotientCoveringMap
    (sphereData period hPeriod)).map_vadd winding

def throatPartialDiffeomorphSmooth
    (Φ : PartialDiffeomorph throatCoverModelWithCorners
      throatCoverModelWithCorners (ThroatCover period hPeriod)
      (EffectiveThroat period hPeriod) ω) :
    PartialDiffeomorph throatCoverModelWithCorners
      throatCoverModelWithCorners (ThroatCover period hPeriod)
      (EffectiveThroat period hPeriod) ∞ where
  toPartialEquiv := Φ.toPartialEquiv
  open_source := Φ.open_source
  open_target := Φ.open_target
  contMDiffOn_toFun := Φ.contMDiffOn_toFun.of_le (by simp)
  contMDiffOn_invFun := Φ.contMDiffOn_invFun.of_le (by simp)

theorem fixedThroat_projection_isLocalDiffeomorph_smooth :
    IsLocalDiffeomorph throatCoverModelWithCorners
      throatCoverModelWithCorners ∞
      (mappingTorusMk (throatData period hPeriod)) := by
  intro anchor
  rcases fixedThroat_projection_isLocalDiffeomorph period hPeriod anchor with
    ⟨Φ, hAnchor, hEq⟩
  exact ⟨throatPartialDiffeomorphSmooth period hPeriod Φ, hAnchor, hEq⟩

theorem normalGraph_joint_contMDiff
    (displacement : SmoothNormalDisplacement period hPeriod) :
    ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      coverModelWithCorners ∞
      (fun point : EffectiveThroat period hPeriod × Real =>
        normalGraph period hPeriod displacement point.2 point.1) := by
  have hDescended := mappingTorusInvariantMapProd_contMDiff
    (throatData period hPeriod) throatCoverModelWithCorners ∞
    (modelWithCornersSelf Real Real) coverModelWithCorners
    (normalGraphInvariantMap period hPeriod displacement)
    (normalGraphInvariantMap_vadd period hPeriod displacement)
    (fixedThroat_projection_isLocalDiffeomorph_smooth period hPeriod)
    (normalGraphCoverQuotientMap_joint_contMDiff period hPeriod displacement)
  exact hDescended.congr (fun point => by
    rcases point with ⟨quotientPoint, parameter⟩
    refine Quotient.inductionOn quotientPoint ?_
    intro anchor
    rfl)

end
end P0EFTJanusProgramPGlobalNormalDisplacementCollarJointSmooth4D
end JanusFormal
