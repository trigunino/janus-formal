import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIdentityMappingTorusLocalDiffeomorph4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkCapOverlapSmoothEmbedding4D

/-!
# Local diffeomorphism of the cap overlap inclusion
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkCapOverlapLocalDiffeomorph4D

set_option autoImplicit false
noncomputable section

open Set Topology
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusEquatorialTubularDiffeomorph4D
open P0EFTJanusEquatorialTubularAmbientInverseJointSmooth4D
open P0EFTJanusIdentityMappingTorusSmoothFunctor4D
open P0EFTJanusIdentityMappingTorusLocalDiffeomorph4D
open P0EFTJanusMappingTorusCutBulkOpenCapSmoothMappingTorus4D
open P0EFTJanusMappingTorusCutBulkCollarCapCoverCompatibility4D
open P0EFTJanusMappingTorusCutBulkCollarCapCoverExactOverlap4D
open P0EFTJanusMappingTorusCutBulkCollarCapQuotientCompatibility4D
open P0EFTJanusMappingTorusCutBulkCapOverlapSmoothEmbedding4D

local instance equatorialSphericalBandOpenLocallyCompactSpace :
    LocallyCompactSpace equatorialSphericalBandOpen :=
  equatorialSphericalBandOpen.2.locallyCompactSpace

local instance positiveUnitLatitudeBandOpenLocallyCompactSpace :
    LocallyCompactSpace positiveUnitLatitudeBandOpen :=
  positiveUnitLatitudeBandOpen.2.locallyCompactSpace

local instance positiveHemisphereInteriorOpenLocallyCompactSpace :
    LocallyCompactSpace positiveHemisphereInteriorOpen :=
  positiveHemisphereInteriorOpen.2.locallyCompactSpace

private def positiveUnitLatitudeBandBasePoint :
    positiveUnitLatitudeBandOpen := by
  let standard : StandardEquatorialTwoSphere :=
    ⟨EuclideanSpace.single 0 1, by simp⟩
  let equator : EquatorialTwoSphere :=
    equatorialTwoSphereHomeomorph.symm standard
  let normal : equatorialTubularNormalOpen :=
    ⟨(1 : Real) / 2, by
      constructor <;> linarith [Real.pi_gt_three]⟩
  let parameter : positiveUnitTubularParameterOpen :=
    ⟨(equator, normal), by
      change 0 < normal.1 ∧ normal.1 < 1
      norm_num [normal]⟩
  exact positiveUnitTubularHomeomorph parameter

private instance positiveUnitLatitudeBandOpenNonempty :
    Nonempty positiveUnitLatitudeBandOpen :=
  ⟨positiveUnitLatitudeBandBasePoint⟩

private def capFiberBandInverse
    (base : positiveUnitLatitudeBandOpen)
    (point : positiveHemisphereInteriorOpen) :
    positiveUnitLatitudeBandOpen := by
  by_cases hUpper : point.1.1 0 < Real.sin 1
  · let band : equatorialSphericalBandOpen := ⟨point.1, by
      change |point.1.1 0| < 1
      rw [abs_of_pos point.2]
      exact hUpper.trans_le (Real.sin_le_one 1)⟩
    exact ⟨band, (mem_positiveUnitLatitudeBandOpen_iff band).2
      ⟨point.2, hUpper⟩⟩
  · exact base

private theorem capFiberBandInverse_contMDiffOn
    (base : positiveUnitLatitudeBandOpen) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (capFiberBandInverse base)
      (Set.range positiveUnitLatitudeBandToCapFiber) := by
  intro point hPoint
  rcases hPoint with ⟨source, rfl⟩
  have hUpper :
      (positiveUnitLatitudeBandToCapFiber source).1.1 0 < Real.sin 1 :=
    (mem_positiveUnitLatitudeBandOpen_iff source.1).1 source.2 |>.2
  have hOpen : IsOpen
      {point : positiveHemisphereInteriorOpen |
        point.1.1 0 < Real.sin 1} := by
    exact isOpen_lt
      ((continuous_apply 0).comp
        (continuous_subtype_val.comp continuous_subtype_val)) continuous_const
  have hAt : ContMDiffAt (𝓡 3) (𝓡 3) ∞
      (capFiberBandInverse base)
      (positiveUnitLatitudeBandToCapFiber source) := by
    rw [← ContMDiffAt.subtypeVal_comp_iff positiveUnitLatitudeBandOpen]
    rw [← ContMDiffAt.subtypeVal_comp_iff equatorialSphericalBandOpen]
    apply (contMDiff_subtype_val : ContMDiff (𝓡 3) (𝓡 3) ∞
      (Subtype.val : positiveHemisphereInteriorOpen → UnitThreeSphere))
      |>.contMDiffAt.congr_of_eventuallyEq
    filter_upwards [hOpen.mem_nhds hUpper] with point hPoint
    simp [Function.comp_def, capFiberBandInverse, hPoint]
  exact hAt.contMDiffWithinAt

private def positiveUnitLatitudeBandToCapFiberPartialDiffeomorph
    (base : positiveUnitLatitudeBandOpen) :
    PartialDiffeomorph (𝓡 3) (𝓡 3)
      positiveUnitLatitudeBandOpen positiveHemisphereInteriorOpen ∞ where
  __ := (positiveUnitLatitudeBandToCapFiber_isOpenEmbedding)
    |>.toOpenPartialHomeomorph positiveUnitLatitudeBandToCapFiber
  contMDiffOn_toFun := positiveUnitLatitudeBandToCapFiber_contMDiff.contMDiffOn
  contMDiffOn_invFun := by
    rw [IsOpenEmbedding.toOpenPartialHomeomorph_target]
    refine (capFiberBandInverse_contMDiffOn base).congr ?_
    intro point hPoint
    apply positiveUnitLatitudeBandToCapFiber_isOpenEmbedding.injective
    change positiveUnitLatitudeBandToCapFiber
        ((positiveUnitLatitudeBandToCapFiber_isOpenEmbedding
          |>.toOpenPartialHomeomorph
            positiveUnitLatitudeBandToCapFiber).symm point) =
      positiveUnitLatitudeBandToCapFiber (capFiberBandInverse base point)
    rw [positiveUnitLatitudeBandToCapFiber_isOpenEmbedding
      |>.toOpenPartialHomeomorph_right_inv
        positiveUnitLatitudeBandToCapFiber hPoint]
    rcases hPoint with ⟨source, rfl⟩
    have hUpper : source.1.1.1 0 < Real.sin 1 :=
      (mem_positiveUnitLatitudeBandOpen_iff source.1).1 source.2 |>.2
    have hUpper' :
        (positiveUnitLatitudeBandToCapFiber source).1.1 0 < Real.sin 1 :=
      hUpper
    apply Subtype.ext
    rw [capFiberBandInverse, dif_pos hUpper']
    rfl

theorem positiveUnitLatitudeBandToCapFiber_isLocalDiffeomorph :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
      positiveUnitLatitudeBandToCapFiber := by
  intro point
  refine ⟨positiveUnitLatitudeBandToCapFiberPartialDiffeomorph point,
    by trivial, ?_⟩
  intro source _
  rfl

variable (period : Real) (hPeriod : period ≠ 0)

private instance smoothCutCapOverlapNonempty :
    Nonempty (SmoothCutCapOverlap period hPeriod) := by
  exact ⟨mappingTorusMk _
    ⟨positiveUnitLatitudeBandBasePoint, 0⟩⟩

theorem smoothCutCapOverlapToSmoothCap_isLocalDiffeomorph :
    letI : ChartedSpace (IdentityCoverModel (EuclideanSpace Real (Fin 3)))
        (SmoothCutCapOverlap period hPeriod) :=
      smoothCutCapOverlapChartedSpace period hPeriod
    letI : ChartedSpace CoverModel (SmoothCutBulkOpenCap period hPeriod) :=
      cutBulkOpenCapQuotientChartedSpace period hPeriod
    IsLocalDiffeomorph
      (identityCoverModelWithCorners (𝓡 3)) coverModelWithCorners ∞
      (smoothCutCapOverlapToSmoothCap period hPeriod) := by
  letI : ChartedSpace (IdentityCoverModel (EuclideanSpace Real (Fin 3)))
      (SmoothCutCapOverlap period hPeriod) :=
    smoothCutCapOverlapChartedSpace period hPeriod
  letI : ChartedSpace CoverModel (SmoothCutBulkOpenCap period hPeriod) :=
    cutBulkOpenCapQuotientChartedSpace period hPeriod
  exact identityMappingTorusMap_isLocalDiffeomorph (𝓡 3)
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod) (𝓡 3)
    positiveUnitLatitudeBandToCapFiber
    positiveUnitLatitudeBandToCapFiber_isLocalDiffeomorph

private theorem contMDiffOn_openEmbeddingInverse_of_isLocalDiffeomorph
    {KField E H E' H' M N : Type*} [NontriviallyNormedField KField]
    [NormedAddCommGroup E] [NormedSpace KField E] [TopologicalSpace H]
    [NormedAddCommGroup E'] [NormedSpace KField E'] [TopologicalSpace H']
    [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace H' N]
    [Nonempty M]
    {I : ModelWithCorners KField E H}
    {J : ModelWithCorners KField E' H'}
    {n : ℕ∞ω} {f : M → N}
    (hOpen : IsOpenEmbedding f)
    (hLocal : IsLocalDiffeomorph I J n f) :
    ContMDiffOn J I n (hOpen.toOpenPartialHomeomorph f).symm
      (Set.range f) := by
  intro target hTarget
  rcases hTarget with ⟨source, rfl⟩
  obtain ⟨Φ, hSource, hEq⟩ := hLocal source
  have hImage : f source ∈ Φ.target := by
    rw [hEq hSource]
    exact Φ.map_source hSource
  have hAt : ContMDiffAt J I n Φ.symm (f source) := by
    rw [hEq hSource]
    exact Φ.symm.contMDiffOn.contMDiffAt
      (Φ.open_target.mem_nhds (Φ.map_source hSource))
  apply (hAt.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [Φ.open_target.mem_nhds hImage] with target hTarget
  apply hOpen.injective
  have hTargetRange : target ∈ Set.range f :=
    ⟨Φ.symm.toFun target, by
      calc
        f (Φ.symm.toFun target) =
            Φ.toFun (Φ.symm.toFun target) :=
          hEq (Φ.map_target hTarget)
        _ = target := Φ.right_inv hTarget⟩
  rw [hOpen.toOpenPartialHomeomorph_right_inv f hTargetRange]
  symm
  calc
    f (Φ.symm.toFun target) =
        Φ.toFun (Φ.symm.toFun target) :=
      hEq (Φ.map_target hTarget)
    _ = target := Φ.right_inv hTarget

theorem smoothCutCapOverlapToSmoothCap_inverse_contMDiffOn :
    letI : ChartedSpace (IdentityCoverModel (EuclideanSpace Real (Fin 3)))
        (SmoothCutCapOverlap period hPeriod) :=
      smoothCutCapOverlapChartedSpace period hPeriod
    letI : ChartedSpace CoverModel (SmoothCutBulkOpenCap period hPeriod) :=
      cutBulkOpenCapQuotientChartedSpace period hPeriod
    ContMDiffOn coverModelWithCorners
      (identityCoverModelWithCorners (𝓡 3)) ∞
      ((smoothCutCapOverlapToSmoothCap_isOpenEmbedding period hPeriod)
        |>.toOpenPartialHomeomorph
          (smoothCutCapOverlapToSmoothCap period hPeriod)).symm
      (Set.range (smoothCutCapOverlapToSmoothCap period hPeriod)) := by
  letI : ChartedSpace (IdentityCoverModel (EuclideanSpace Real (Fin 3)))
      (SmoothCutCapOverlap period hPeriod) :=
    smoothCutCapOverlapChartedSpace period hPeriod
  letI : ChartedSpace CoverModel (SmoothCutBulkOpenCap period hPeriod) :=
    cutBulkOpenCapQuotientChartedSpace period hPeriod
  exact contMDiffOn_openEmbeddingInverse_of_isLocalDiffeomorph
    (smoothCutCapOverlapToSmoothCap_isOpenEmbedding period hPeriod)
    (smoothCutCapOverlapToSmoothCap_isLocalDiffeomorph period hPeriod)

end
end P0EFTJanusMappingTorusCutBulkCapOverlapLocalDiffeomorph4D
end JanusFormal
