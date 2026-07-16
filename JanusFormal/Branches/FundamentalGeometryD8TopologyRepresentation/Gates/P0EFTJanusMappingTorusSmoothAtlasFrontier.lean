import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusQuotient

/-!
# Smooth-atlas frontier for the effective mapping torus

The concrete algebraic `S^3` is identified with Mathlib's Euclidean unit
sphere and receives its analytic atlas.  This gives the product cover an
explicit analytic four-manifold structure.  The effective orbit quotient then
has the covering-induced charted-space structure and is an actual topological
four-manifold (`C^0`).

Mathlib's quotient-manifold API currently stops exactly here: smooth
compatibility of the quotient atlas for a smooth properly discontinuous action
and smoothness of the quotient projection remain TODOs in
`Geometry.Manifold.Instances.Quotient`.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusSmoothAtlasFrontier

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped Manifold ContDiff
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient

section PullbackAtlas

variable {𝕜 E H M N : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] [TopologicalSpace M] [TopologicalSpace N]

variable (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)

/-- Pull a charted-space atlas back along a global homeomorphism. -/
@[implicit_reducible] def chartedSpacePullback (equiv : M ≃ₜ N) [ChartedSpace H N] :
    ChartedSpace H M where
  atlas := {chart | ∃ targetChart ∈ atlas H N,
    chart = equiv.transOpenPartialHomeomorph targetChart}
  chartAt point := equiv.transOpenPartialHomeomorph (chartAt H (equiv point))
  mem_chart_source point := by simp
  chart_mem_atlas point := ⟨chartAt H (equiv point), chart_mem_atlas H _, rfl⟩

/-- Pulling back a `C^n` atlas along a homeomorphism preserves all transition
maps and therefore the manifold class. -/
theorem isManifold_chartedSpacePullback
    (equiv : M ≃ₜ N) [ChartedSpace H N] [IsManifold I n N] :
    letI : ChartedSpace H M := chartedSpacePullback equiv
    IsManifold I n M := by
  letI : ChartedSpace H M := chartedSpacePullback equiv
  refine { compatible := ?_ }
  rintro first second ⟨firstTarget, hFirst, rfl⟩
    ⟨secondTarget, hSecond, rfl⟩
  have hTransition :
      (equiv.transOpenPartialHomeomorph firstTarget).symm.trans
          (equiv.transOpenPartialHomeomorph secondTarget) =
        firstTarget.symm.trans secondTarget := by
    ext point <;> simp
  rw [hTransition]
  exact (contDiffGroupoid n I).compatible hFirst hSecond

end PullbackAtlas

/-- Euclidean ambient four-space used by Mathlib's analytic sphere atlas. -/
abbrev EuclideanR4 := EuclideanSpace ℝ (Fin 4)

/-- Mathlib's standard analytic unit three-sphere. -/
abbrev StandardUnitThreeSphere := Metric.sphere (0 : EuclideanR4) 1

/-- The algebraic radius used by the Janus gate is the squared Euclidean norm
after transporting the coordinate vector to `EuclideanSpace`. -/
theorem euclidean_norm_sq_eq_radiusSquared (point : R4Point) :
    ‖(EuclideanSpace.equiv (Fin 4) ℝ).symm point‖ ^ 2 = radiusSquared point := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

/-- Homeomorphism from the actual Janus algebraic sphere to Mathlib's standard
analytic sphere. -/
private def toStandardSphere (point : UnitThreeSphere) : StandardUnitThreeSphere :=
  ⟨(EuclideanSpace.equiv (Fin 4) ℝ).symm point.1, by
    rw [Metric.mem_sphere, dist_zero_right]
    have hSquare :
        ‖(EuclideanSpace.equiv (Fin 4) ℝ).symm point.1‖ ^ 2 = 1 := by
      rw [euclidean_norm_sq_eq_radiusSquared]
      exact point.2
    nlinarith [norm_nonneg ((EuclideanSpace.equiv (Fin 4) ℝ).symm point.1)]⟩

private def fromStandardSphere (point : StandardUnitThreeSphere) : UnitThreeSphere :=
  ⟨EuclideanSpace.equiv (Fin 4) ℝ point.1, by
    unfold OnUnitThreeSphere
    rw [← euclidean_norm_sq_eq_radiusSquared]
    simp only [ContinuousLinearEquiv.symm_apply_apply]
    have hNorm : ‖point.1‖ = 1 := by
      have hSphere := point.2
      simp only [Metric.mem_sphere, dist_zero_right] at hSphere
      exact hSphere
    simp [hNorm]⟩

def unitThreeSphereHomeomorph : UnitThreeSphere ≃ₜ StandardUnitThreeSphere where
  toFun := toStandardSphere
  invFun := fromStandardSphere
  left_inv point := by
    apply Subtype.ext
    exact (EuclideanSpace.equiv (Fin 4) ℝ).apply_symm_apply point.1
  right_inv point := by
    apply Subtype.ext
    exact (EuclideanSpace.equiv (Fin 4) ℝ).symm_apply_apply point.1
  continuous_toFun :=
    ((EuclideanSpace.equiv (Fin 4) ℝ).symm.continuous.comp
      continuous_subtype_val).subtype_mk (fun point => (toStandardSphere point).2)
  continuous_invFun :=
    ((EuclideanSpace.equiv (Fin 4) ℝ).continuous.comp
      continuous_subtype_val).subtype_mk (fun point => (fromStandardSphere point).2)

/-- Explicit analytic atlas on the actual algebraic unit sphere. -/
instance unitThreeSphereChartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin 3)) UnitThreeSphere :=
  chartedSpacePullback unitThreeSphereHomeomorph

/-- The actual algebraic unit sphere is an analytic three-manifold. -/
instance unitThreeSphereIsManifold :
    IsManifold (𝓡 3) ω UnitThreeSphere :=
  isManifold_chartedSpacePullback (𝓡 3) ω unitThreeSphereHomeomorph

instance unitThreeSphereLocallyCompactSpace :
    LocallyCompactSpace UnitThreeSphere :=
  unitThreeSphereHomeomorph.locallyCompactSpace_iff.mpr inferInstance

/-- Euclidean ambient space for the equatorial two-sphere. -/
abbrev EuclideanR3 := EuclideanSpace ℝ (Fin 3)

/-- Mathlib's standard analytic unit two-sphere. -/
abbrev StandardEquatorialTwoSphere := Metric.sphere (0 : EuclideanR3) 1

private def equatorialTail (point : EquatorialTwoSphere) : Fin 3 → ℝ :=
  fun index => point.1 index.succ

private def equatorialInsert (coordinates : Fin 3 → ℝ) : R4Point :=
  Fin.cases 0 coordinates

private def toStandardEquator
    (point : EquatorialTwoSphere) : StandardEquatorialTwoSphere :=
  ⟨(EuclideanSpace.equiv (Fin 3) ℝ).symm (equatorialTail point), by
    rw [Metric.mem_sphere, dist_zero_right]
    have hRadius :
        ‖(EuclideanSpace.equiv (Fin 3) ℝ).symm (equatorialTail point)‖ ^ 2 = 1 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp only [Fin.sum_univ_three]
      change point.1 1 ^ 2 + point.1 2 ^ 2 + point.1 3 ^ 2 = 1
      have hSphere := point.2.1
      unfold OnUnitThreeSphere radiusSquared at hSphere
      simp only [Fin.sum_univ_four] at hSphere
      have hZero : point.1 0 = 0 := point.2.2
      rw [hZero] at hSphere
      norm_num at hSphere
      exact hSphere
    nlinarith [norm_nonneg
      ((EuclideanSpace.equiv (Fin 3) ℝ).symm (equatorialTail point))]⟩

private def fromStandardEquator
    (point : StandardEquatorialTwoSphere) : EquatorialTwoSphere :=
  ⟨equatorialInsert (EuclideanSpace.equiv (Fin 3) ℝ point.1), by
    constructor
    · unfold OnUnitThreeSphere radiusSquared equatorialInsert
      rw [Fin.sum_univ_succ]
      simp only [Fin.cases_zero, Fin.cases_succ, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
        zero_add]
      have hNorm : ‖point.1‖ = 1 := by
        have hSphere := point.2
        simp only [Metric.mem_sphere, dist_zero_right] at hSphere
        exact hSphere
      have hSquare := EuclideanSpace.real_norm_sq_eq point.1
      rw [hNorm] at hSquare
      norm_num at hSquare
      simpa using hSquare.symm
    · rfl⟩

/-- Homeomorphism identifying the actual equatorial subtype with the standard
analytic unit two-sphere. -/
def equatorialTwoSphereHomeomorph :
    EquatorialTwoSphere ≃ₜ StandardEquatorialTwoSphere where
  toFun := toStandardEquator
  invFun := fromStandardEquator
  left_inv point := by
    apply Subtype.ext
    change equatorialInsert
        ((EuclideanSpace.equiv (Fin 3) ℝ)
          ((EuclideanSpace.equiv (Fin 3) ℝ).symm (equatorialTail point))) = point.1
    rw [(EuclideanSpace.equiv (Fin 3) ℝ).apply_symm_apply]
    funext index
    refine Fin.cases ?_ (fun tailIndex => ?_) index
    · simpa [equatorialInsert] using point.2.2.symm
    · rfl
  right_inv point := by
    apply Subtype.ext
    apply (EuclideanSpace.equiv (Fin 3) ℝ).injective
    funext index
    change equatorialInsert
        ((EuclideanSpace.equiv (Fin 3) ℝ) point.1) index.succ =
      ((EuclideanSpace.equiv (Fin 3) ℝ) point.1) index
    rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous.comp
    apply continuous_pi
    intro index
    exact (continuous_apply index.succ).comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro index
    fin_cases index
    · exact continuous_const
    · exact (continuous_apply 0).comp
        ((EuclideanSpace.equiv (Fin 3) ℝ).continuous.comp continuous_subtype_val)
    · exact (continuous_apply 1).comp
        ((EuclideanSpace.equiv (Fin 3) ℝ).continuous.comp continuous_subtype_val)
    · exact (continuous_apply 2).comp
        ((EuclideanSpace.equiv (Fin 3) ℝ).continuous.comp continuous_subtype_val)

instance equatorialTwoSphereChartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin 2)) EquatorialTwoSphere :=
  chartedSpacePullback equatorialTwoSphereHomeomorph

instance equatorialTwoSphereIsManifold :
    IsManifold (𝓡 2) ω EquatorialTwoSphere :=
  isManifold_chartedSpacePullback (𝓡 2) ω equatorialTwoSphereHomeomorph

instance equatorialTwoSphereLocallyCompactSpace :
    LocallyCompactSpace EquatorialTwoSphere :=
  equatorialTwoSphereHomeomorph.locallyCompactSpace_iff.mpr inferInstance

/-- Four-dimensional normed coordinate space of the product model. -/
abbrev CoverCoordinates := EuclideanSpace ℝ (Fin 3) × ℝ

/-- Tagged topological model carried by the sphere-times-real cover. -/
abbrev CoverModel := ModelProd (EuclideanSpace ℝ (Fin 3)) ℝ

/-- Model with corners for the analytic product cover. -/
abbrev coverModelWithCorners :
    ModelWithCorners ℝ CoverCoordinates CoverModel :=
  (𝓡 3).prod 𝓘(ℝ, ℝ)

/-- Three-dimensional model of the fixed-throat cover. -/
abbrev ThroatCoverCoordinates := EuclideanSpace ℝ (Fin 2) × ℝ

abbrev ThroatCoverModel := ModelProd (EuclideanSpace ℝ (Fin 2)) ℝ

abbrev throatCoverModelWithCorners :
    ModelWithCorners ℝ ThroatCoverCoordinates ThroatCoverModel :=
  (𝓡 2).prod 𝓘(ℝ, ℝ)

/-- The concrete fiber-times-time product is an analytic four-manifold. -/
theorem unitThreeSphere_prod_real_isManifold :
    IsManifold coverModelWithCorners ω (UnitThreeSphere × ℝ) := by
  infer_instance

section ReflectedMappingTorus

variable (period : ℝ) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod

/-- Explicit analytic atlas on the actual fixed-throat product cover. -/
@[implicit_reducible] def fixedThroatCoverChartedSpace :
    ChartedSpace ThroatCoverModel
      (MappingTorusCover (fixedEquatorData period hPeriod)) :=
  chartedSpacePullback (coverHomeomorphProd (fixedEquatorData period hPeriod))

theorem fixedThroatCover_isManifold :
    @IsManifold ℝ _ ThroatCoverCoordinates _ _ ThroatCoverModel _
      throatCoverModelWithCorners ω
      (MappingTorusCover (fixedEquatorData period hPeriod)) _
      (fixedThroatCoverChartedSpace period hPeriod) :=
  isManifold_chartedSpacePullback throatCoverModelWithCorners ω
    (coverHomeomorphProd (fixedEquatorData period hPeriod))

/-- The actual equatorial inclusion is a topological embedding. -/
theorem equatorialSphereInclusion_isEmbedding :
    Topology.IsEmbedding equatorialSphereInclusion := by
  let hSubset : {point : R4Point | OnEquatorialTwoSphere point} ⊆
      {point : R4Point | OnUnitThreeSphere point} := fun _ hPoint => hPoint.1
  have hEquality :
      (Set.inclusion hSubset : EquatorialTwoSphere → UnitThreeSphere) =
        equatorialSphereInclusion := by
    funext point
    apply Subtype.ext
    rfl
  rw [← hEquality]
  exact Topology.IsEmbedding.inclusion hSubset

/-- The lifted fixed throat is embedded in the analytic product cover. -/
theorem fixedThroatCoverInclusion_isEmbedding :
    Topology.IsEmbedding (fixedThroatCoverInclusion period hPeriod) := by
  have hProduct : Topology.IsEmbedding
      (Prod.map equatorialSphereInclusion (id : ℝ → ℝ)) :=
    equatorialSphereInclusion_isEmbedding.prodMap Topology.IsEmbedding.id
  have hComposite :=
    (coverHomeomorphProd (sphereData period hPeriod)).symm.isEmbedding.comp
      (hProduct.comp
        (coverHomeomorphProd (fixedEquatorData period hPeriod)).isEmbedding)
  have hEquality :
      (⇑(coverHomeomorphProd (sphereData period hPeriod)).symm ∘
          Prod.map equatorialSphereInclusion (id : ℝ → ℝ) ∘
          ⇑(coverHomeomorphProd (fixedEquatorData period hPeriod))) =
        fixedThroatCoverInclusion period hPeriod := by
    funext point
    rfl
  rw [hEquality] at hComposite
  exact hComposite

/-- For the induced product atlases the lifted throat inclusion is a `C^0`
manifold embedding.  Smoothness is the remaining atlas-compatibility step. -/
theorem fixedThroatCoverInclusion_contMDiff_zero :
    ContMDiff throatCoverModelWithCorners coverModelWithCorners 0
      (fixedThroatCoverInclusion period hPeriod) := by
  rw [contMDiff_zero_iff]
  exact continuous_fixedThroatCoverInclusion period hPeriod

/-- The fixed-throat quotient inherits its concrete three-dimensional
covering-induced charted-space structure. -/
theorem fixedThroat_quotient_has_chartedSpace :
    Nonempty (ChartedSpace ThroatCoverModel
      (MappingTorus (fixedEquatorData period hPeriod))) :=
  ⟨inferInstance⟩

/-- The fixed throat is an actual topological (`C^0`) three-manifold. -/
theorem fixedThroat_quotient_isTopologicalManifold :
    IsManifold throatCoverModelWithCorners 0
      (MappingTorus (fixedEquatorData period hPeriod)) := by
  infer_instance

/-- The induced inclusion of the effective throat quotient is a `C^0`
manifold map. -/
theorem fixedThroatQuotientInclusion_contMDiff_zero :
    ContMDiff throatCoverModelWithCorners coverModelWithCorners 0
      (fixedThroatQuotientInclusion period hPeriod) := by
  rw [contMDiff_zero_iff]
  exact continuous_fixedThroatQuotientInclusion period hPeriod

/-- A specific analytic atlas on the actual packaged mapping-torus cover,
pulled back from `S^3 × ℝ` by its defining homeomorphism. -/
@[implicit_reducible] def reflectedSphereCoverChartedSpace :
    ChartedSpace CoverModel (MappingTorusCover (sphereData period hPeriod)) :=
  chartedSpacePullback (coverHomeomorphProd (sphereData period hPeriod))

/-- With that explicit atlas, the actual mapping-torus cover is analytic. -/
theorem reflectedSphereCover_isManifold :
    @IsManifold ℝ _ CoverCoordinates _ _ CoverModel _ coverModelWithCorners ω
      (MappingTorusCover (sphereData period hPeriod)) _
      (reflectedSphereCoverChartedSpace period hPeriod) :=
  isManifold_chartedSpacePullback coverModelWithCorners ω
    (coverHomeomorphProd (sphereData period hPeriod))

/-- The already-constructed covering quotient supplies an explicit local
homeomorphism at every cover point. -/
theorem reflectedSphere_projection_isLocalHomeomorph :
    IsLocalHomeomorph (mappingTorusMk (sphereData period hPeriod)) :=
  (mappingTorusMk_isCoveringMap (sphereData period hPeriod)).isLocalHomeomorph

/-- The effective quotient has the concrete covering-induced four-dimensional
charted-space structure. -/
theorem reflectedSphere_quotient_has_chartedSpace :
    Nonempty (ChartedSpace CoverModel (MappingTorus (sphereData period hPeriod))) :=
  ⟨inferInstance⟩

/-- Independently of the still-missing smooth quotient compatibility theorem,
the effective quotient is an actual topological (`C^0`) four-manifold. -/
theorem reflectedSphere_quotient_isTopologicalManifold :
    IsManifold coverModelWithCorners 0
      (MappingTorus (sphereData period hPeriod)) := by
  infer_instance

/-- Every deck iterate is compatible with the covering atlas at the complete
topological (`C^0`) level.  Promoting `0` to `∞` is exactly the missing smooth
quotient-action theorem. -/
theorem reflectedSphere_deck_contMDiff_zero (winding : ℤ) :
    ContMDiff coverModelWithCorners coverModelWithCorners 0
      (winding +ᵥ · : MappingTorusCover (sphereData period hPeriod) →
        MappingTorusCover (sphereData period hPeriod)) := by
  rw [contMDiff_zero_iff]
  exact continuous_const_vadd _ winding

/-- The quotient projection is a `C^0` manifold map for the actual induced
atlases. -/
theorem reflectedSphere_projection_contMDiff_zero :
    ContMDiff coverModelWithCorners coverModelWithCorners 0
      (mappingTorusMk (sphereData period hPeriod)) := by
  rw [contMDiff_zero_iff]
  exact continuous_quotient_mk'

/-- The quotient projection is continuous, open, surjective and locally a
homeomorphism; these are the complete topological inputs of its covering
atlas. -/
theorem reflectedSphere_projection_topological_atlas_closure :
    Continuous (mappingTorusMk (sphereData period hPeriod)) ∧
    IsOpenMap (mappingTorusMk (sphereData period hPeriod)) ∧
    Function.Surjective (mappingTorusMk (sphereData period hPeriod)) ∧
    IsLocalHomeomorph (mappingTorusMk (sphereData period hPeriod)) := by
  have hCover := mappingTorusMk_isCoveringMap (sphereData period hPeriod)
  exact ⟨hCover.continuous, hCover.isOpenMap,
    mappingTorusMk_surjective _, hCover.isLocalHomeomorph⟩

end ReflectedMappingTorus

end

end P0EFTJanusMappingTorusSmoothAtlasFrontier
end JanusFormal
