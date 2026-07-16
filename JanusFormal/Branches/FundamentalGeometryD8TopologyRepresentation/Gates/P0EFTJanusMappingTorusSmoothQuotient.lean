import Mathlib.Geometry.Manifold.LocalDiffeomorph
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusSmoothAtlasFrontier

/-!
# Smooth-deck descent data for the effective mapping torus

This gate proves that the integer deck actions and fixed-throat inclusion are
smooth on the analytic covers.  It also proves the local-section transition
law and the groupoid compatibility needed to descend their atlases.  It does
not yet install the resulting `ChartedSpace` or `IsManifold` instances on the
quotient types.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusSmoothQuotient

set_option autoImplicit false

noncomputable section

open Set Metric Topology
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier

section PullbackAtlas

variable {𝕜 E H M N : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] [TopologicalSpace M] [TopologicalSpace N]

variable (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)

/-- The defining homeomorphism of a pulled-back atlas is smooth. -/
theorem chartedSpacePullback_toFun_contMDiff
    (equiv : M ≃ₜ N) [ChartedSpace H N] [IsManifold I n N] :
    @ContMDiff 𝕜 _ E _ _ H _ I M _ (chartedSpacePullback equiv)
      E _ _ H _ I N _ _ n equiv := by
  letI : ChartedSpace H M := chartedSpacePullback equiv
  letI : IsManifold I n M := isManifold_chartedSpacePullback I n equiv
  rw [contMDiff_iff]
  constructor
  · exact equiv.continuous
  · intro point targetPoint
    have hChart : (chartAt H point : OpenPartialHomeomorph M H) =
        equiv.transOpenPartialHomeomorph (chartAt H (equiv point)) := rfl
    have hId := (contMDiff_iff.mp
      (contMDiff_id : ContMDiff I I n (id : N → N))).2
        (equiv point) targetPoint
    convert hId using 1
    · ext coordinate
      simp [hChart, extChartAt, Function.comp_def]
    · ext coordinate
      simp [hChart, extChartAt, Function.comp_def]

/-- The inverse of the defining homeomorphism is smooth for the pulled-back
atlas. -/
theorem chartedSpacePullback_invFun_contMDiff
    (equiv : M ≃ₜ N) [ChartedSpace H N] [IsManifold I n N] :
    @ContMDiff 𝕜 _ E _ _ H _ I N _ _
      E _ _ H _ I M _ (chartedSpacePullback equiv) n equiv.symm := by
  letI : ChartedSpace H M := chartedSpacePullback equiv
  letI : IsManifold I n M := isManifold_chartedSpacePullback I n equiv
  rw [contMDiff_iff]
  constructor
  · exact equiv.symm.continuous
  · intro point targetPoint
    have hChart : (chartAt H targetPoint : OpenPartialHomeomorph M H) =
        equiv.transOpenPartialHomeomorph (chartAt H (equiv targetPoint)) := rfl
    have hId := (contMDiff_iff.mp
      (contMDiff_id : ContMDiff I I n (id : N → N))).2
        point (equiv targetPoint)
    convert hId using 1
    · ext coordinate
      simp [hChart, extChartAt, Function.comp_def]
    · ext coordinate
      simp [hChart, extChartAt, Function.comp_def]

end PullbackAtlas

section AnalyticDeckAction

open P0EFTJanusReflectionFixedThroat

/-- Coordinate reflection is analytic on the algebraic ambient four-space. -/
theorem reflectPoint_contDiff : ContDiff ℝ ω reflectPoint := by
  rw [contDiff_pi]
  intro index
  by_cases hIndex : index = 0
  · simpa [reflectPoint, hIndex] using
      (contDiff_apply ℝ ℝ index).neg
  · simpa [reflectPoint, hIndex] using
      (contDiff_apply ℝ ℝ index)

/-- The corresponding reflection on Mathlib's Euclidean four-space. -/
def euclideanReflection (point : EuclideanR4) : EuclideanR4 :=
  (EuclideanSpace.equiv (Fin 4) ℝ).symm
    (reflectPoint ((EuclideanSpace.equiv (Fin 4) ℝ) point))

theorem euclideanReflection_contDiff :
    ContDiff ℝ ω euclideanReflection := by
  exact (EuclideanSpace.equiv (Fin 4) ℝ).symm.contDiff.comp
    (reflectPoint_contDiff.comp (EuclideanSpace.equiv (Fin 4) ℝ).contDiff)

private theorem euclideanReflection_mem_standardSphere
    (point : StandardUnitThreeSphere) :
    euclideanReflection point.1 ∈ Metric.sphere (0 : EuclideanR4) 1 := by
  rw [Metric.mem_sphere, dist_zero_right]
  have hNorm : ‖point.1‖ = 1 := by
    have hSphere := point.2
    simp only [Metric.mem_sphere, dist_zero_right] at hSphere
    exact hSphere
  have hUnit : OnUnitThreeSphere
      ((EuclideanSpace.equiv (Fin 4) ℝ) point.1) := by
    unfold OnUnitThreeSphere
    rw [← euclidean_norm_sq_eq_radiusSquared]
    simp [hNorm]
  have hReflected := reflection_preserves_unit_three_sphere
    ((EuclideanSpace.equiv (Fin 4) ℝ) point.1) hUnit
  unfold OnUnitThreeSphere at hReflected
  rw [← euclidean_norm_sq_eq_radiusSquared] at hReflected
  change ‖euclideanReflection point.1‖ ^ 2 = 1 at hReflected
  change ‖euclideanReflection point.1‖ = 1
  nlinarith [norm_nonneg (euclideanReflection point.1)]

/-- Analytic reflection of the standard unit three-sphere. -/
def standardSphereReflection :
    StandardUnitThreeSphere → StandardUnitThreeSphere :=
  fun point => ⟨euclideanReflection point.1,
    euclideanReflection_mem_standardSphere point⟩

theorem standardSphereReflection_contMDiff :
    ContMDiff (𝓡 3) (𝓡 3) ω standardSphereReflection := by
  letI : Fact (Module.finrank ℝ EuclideanR4 = 3 + 1) := ⟨by simp⟩
  apply ContMDiff.codRestrict_sphere
  exact euclideanReflection_contDiff.contMDiff.comp contMDiff_coe_sphere

theorem standardSphereReflection_conjugates_actual
    (point : UnitThreeSphere) :
    unitThreeSphereHomeomorph.symm
        (standardSphereReflection (unitThreeSphereHomeomorph point)) =
      sphereReflection point := by
  apply Subtype.ext
  rfl

/-- The actual algebraic sphere reflection is analytic for the transported
atlas. -/
theorem sphereReflection_contMDiff :
    ContMDiff (𝓡 3) (𝓡 3) ω sphereReflection := by
  have hTo := chartedSpacePullback_toFun_contMDiff (𝓡 3) ω
    unitThreeSphereHomeomorph
  have hInv := chartedSpacePullback_invFun_contMDiff (𝓡 3) ω
    unitThreeSphereHomeomorph
  have hComposite := hInv.comp
    (standardSphereReflection_contMDiff.comp hTo)
  exact hComposite.congr standardSphereReflection_conjugates_actual

theorem sphereReflection_inv_contMDiff :
    ContMDiff (𝓡 3) (𝓡 3) ω sphereReflection.symm := by
  exact sphereReflection_contMDiff.congr fun point => rfl

/-- Every monodromy iterate on the sphere fiber is analytic. -/
theorem sphereReflection_zpow_contMDiff (winding : ℤ) :
    ContMDiff (𝓡 3) (𝓡 3) ω (sphereReflection ^ winding) := by
  induction winding using Int.induction_on with
  | zero => exact
      (contMDiff_id : ContMDiff (𝓡 3) (𝓡 3) ω
        (id : UnitThreeSphere → UnitThreeSphere)).congr fun _ => rfl
  | succ winding ih =>
      rw [zpow_add_one]
      exact ih.comp sphereReflection_contMDiff
  | pred winding ih =>
      rw [zpow_sub_one]
      exact ih.comp sphereReflection_inv_contMDiff

/-- Insert a zero normal coordinate into Euclidean three-space. -/
private def rawEquatorInsert (coordinates : Fin 3 → ℝ) : Fin 4 → ℝ :=
  Fin.cases 0 coordinates

theorem rawEquatorInsert_contDiff : ContDiff ℝ ω rawEquatorInsert := by
  rw [contDiff_pi]
  intro index
  refine Fin.cases ?_ (fun tailIndex => ?_) index
  · exact contDiff_const
  · exact contDiff_apply ℝ ℝ tailIndex

def euclideanEquatorInsert (point : EuclideanR3) : EuclideanR4 :=
  (EuclideanSpace.equiv (Fin 4) ℝ).symm
    (rawEquatorInsert ((EuclideanSpace.equiv (Fin 3) ℝ) point))

theorem euclideanEquatorInsert_contDiff :
    ContDiff ℝ ω euclideanEquatorInsert := by
  exact (EuclideanSpace.equiv (Fin 4) ℝ).symm.contDiff.comp
    (rawEquatorInsert_contDiff.comp
      (EuclideanSpace.equiv (Fin 3) ℝ).contDiff)

private theorem euclideanEquatorInsert_norm_sq (point : EuclideanR3) :
    ‖euclideanEquatorInsert point‖ ^ 2 = ‖point‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  rw [Fin.sum_univ_succ]
  simp [euclideanEquatorInsert, rawEquatorInsert]

private theorem euclideanEquatorInsert_mem_standardSphere
    (point : StandardEquatorialTwoSphere) :
    euclideanEquatorInsert point.1 ∈ Metric.sphere (0 : EuclideanR4) 1 := by
  rw [Metric.mem_sphere, dist_zero_right]
  have hNorm : ‖point.1‖ = 1 := by
    have hSphere := point.2
    simp only [Metric.mem_sphere, dist_zero_right] at hSphere
    exact hSphere
  have hSquare := euclideanEquatorInsert_norm_sq point.1
  nlinarith [norm_nonneg (euclideanEquatorInsert point.1)]

/-- Standard analytic inclusion `S² ↪ S³` as the zero-normal equator. -/
def standardEquatorInclusion :
    StandardEquatorialTwoSphere → StandardUnitThreeSphere :=
  fun point => ⟨euclideanEquatorInsert point.1,
    euclideanEquatorInsert_mem_standardSphere point⟩

theorem standardEquatorInclusion_contMDiff :
    ContMDiff (𝓡 2) (𝓡 3) ω standardEquatorInclusion := by
  letI : Fact (Module.finrank ℝ EuclideanR3 = 2 + 1) := ⟨by simp⟩
  letI : Fact (Module.finrank ℝ EuclideanR4 = 3 + 1) := ⟨by simp⟩
  apply ContMDiff.codRestrict_sphere
  exact euclideanEquatorInsert_contDiff.contMDiff.comp contMDiff_coe_sphere

theorem standardEquatorInclusion_conjugates_actual
    (point : EquatorialTwoSphere) :
    unitThreeSphereHomeomorph.symm
        (standardEquatorInclusion (equatorialTwoSphereHomeomorph point)) =
      equatorialSphereInclusion point := by
  apply Subtype.ext
  funext index
  refine Fin.cases ?_ (fun tailIndex => ?_) index
  · exact point.2.2.symm
  · rfl

/-- The actual fixed-equator inclusion is analytic. -/
theorem equatorialSphereInclusion_contMDiff :
    ContMDiff (𝓡 2) (𝓡 3) ω equatorialSphereInclusion := by
  have hTo := chartedSpacePullback_toFun_contMDiff (𝓡 2) ω
    equatorialTwoSphereHomeomorph
  have hInv := chartedSpacePullback_invFun_contMDiff (𝓡 3) ω
    unitThreeSphereHomeomorph
  have hComposite := hInv.comp
    (standardEquatorInclusion_contMDiff.comp hTo)
  exact hComposite.congr fun point =>
    (standardEquatorInclusion_conjugates_actual point).symm

section Covers

variable (period : ℝ) (hPeriod : period ≠ 0)

/-- Deck transformation written in the ordinary product coordinates. -/
def reflectedSphereProductDeck (winding : ℤ) :
    UnitThreeSphere × ℝ → UnitThreeSphere × ℝ :=
  Prod.map (⇑(sphereReflection ^ winding) :
      UnitThreeSphere → UnitThreeSphere)
    (fun time => time + (winding : ℝ) * period)

theorem reflectedSphereProductDeck_contMDiff (winding : ℤ) :
    ContMDiff coverModelWithCorners coverModelWithCorners ω
      (reflectedSphereProductDeck period winding) := by
  have hTime : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ω
      (fun time : ℝ => time + (winding : ℝ) * period) :=
    (contDiff_id.add contDiff_const).contMDiff.congr fun _ => rfl
  exact ContMDiff.prodMap (sphereReflection_zpow_contMDiff winding) hTime

/-- Every deck transformation of the packaged reflected-sphere cover is
analytic for the explicit pulled-back atlas. -/
theorem reflectedSphereCover_deck_contMDiff (winding : ℤ) :
    @ContMDiff ℝ _ CoverCoordinates _ _ CoverModel _ coverModelWithCorners
      (MappingTorusCover (reflectedSphereData period hPeriod)) _
      (reflectedSphereCoverChartedSpace period hPeriod)
      CoverCoordinates _ _ CoverModel _ coverModelWithCorners
      (MappingTorusCover (reflectedSphereData period hPeriod)) _
      (reflectedSphereCoverChartedSpace period hPeriod) ω
      (winding +ᵥ ·) := by
  letI : ChartedSpace CoverModel
      (MappingTorusCover (reflectedSphereData period hPeriod)) :=
    reflectedSphereCoverChartedSpace period hPeriod
  letI : IsManifold coverModelWithCorners ω
      (MappingTorusCover (reflectedSphereData period hPeriod)) :=
    reflectedSphereCover_isManifold period hPeriod
  have hTo := chartedSpacePullback_toFun_contMDiff coverModelWithCorners ω
    (coverHomeomorphProd (reflectedSphereData period hPeriod))
  have hInv := chartedSpacePullback_invFun_contMDiff coverModelWithCorners ω
    (coverHomeomorphProd (reflectedSphereData period hPeriod))
  have hComposite := hInv.comp
    ((reflectedSphereProductDeck_contMDiff period winding).comp hTo)
  exact hComposite.congr fun point => by
    apply MappingTorusCover.ext
    · change ((sphereReflection ^ winding) point.fiber) =
        ((sphereReflection ^ winding) point.fiber)
      rfl
    · rfl

private theorem refl_zpow_apply {X : Type*} [TopologicalSpace X]
    (winding : ℤ) (point : X) :
    ((Homeomorph.refl X) ^ winding) point = point := by
  rw [show ((Homeomorph.refl X) ^ winding) point =
      ((Homeomorph.refl X) ^ winding).toEquiv point from rfl,
    homeomorph_toEquiv_zpow]
  rw [show (Homeomorph.refl X).toEquiv = 1 from rfl, one_zpow]
  rfl

def fixedThroatProductDeck (winding : ℤ) :
    EquatorialTwoSphere × ℝ → EquatorialTwoSphere × ℝ :=
  fun point => (point.1, point.2 + (winding : ℝ) * period)

theorem fixedThroatProductDeck_contMDiff (winding : ℤ) :
    ContMDiff throatCoverModelWithCorners throatCoverModelWithCorners ω
      (fixedThroatProductDeck period winding) := by
  have hTime : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ω
      (fun time : ℝ => time + (winding : ℝ) * period) :=
    (contDiff_id.add contDiff_const).contMDiff.congr fun _ => rfl
  exact (contMDiff_id : ContMDiff (𝓡 2) (𝓡 2) ω
    (id : EquatorialTwoSphere → EquatorialTwoSphere)).prodMap hTime

/-- Every deck transformation of the fixed-throat cover is analytic. -/
theorem fixedThroatCover_deck_contMDiff (winding : ℤ) :
    @ContMDiff ℝ _ ThroatCoverCoordinates _ _ ThroatCoverModel _
      throatCoverModelWithCorners
      (MappingTorusCover (fixedEquatorData period hPeriod)) _
      (fixedThroatCoverChartedSpace period hPeriod)
      ThroatCoverCoordinates _ _ ThroatCoverModel _
      throatCoverModelWithCorners
      (MappingTorusCover (fixedEquatorData period hPeriod)) _
      (fixedThroatCoverChartedSpace period hPeriod) ω
      (winding +ᵥ ·) := by
  letI : ChartedSpace ThroatCoverModel
      (MappingTorusCover (fixedEquatorData period hPeriod)) :=
    fixedThroatCoverChartedSpace period hPeriod
  letI : IsManifold throatCoverModelWithCorners ω
      (MappingTorusCover (fixedEquatorData period hPeriod)) :=
    fixedThroatCover_isManifold period hPeriod
  have hTo := chartedSpacePullback_toFun_contMDiff
    throatCoverModelWithCorners ω
    (coverHomeomorphProd (fixedEquatorData period hPeriod))
  have hInv := chartedSpacePullback_invFun_contMDiff
    throatCoverModelWithCorners ω
    (coverHomeomorphProd (fixedEquatorData period hPeriod))
  have hComposite := hInv.comp
    ((fixedThroatProductDeck_contMDiff period winding).comp hTo)
  exact hComposite.congr fun point => by
    apply MappingTorusCover.ext
    · exact refl_zpow_apply winding point.fiber
    · rfl

/-- The lifted fixed throat is an analytic embedding into the reflected cover. -/
theorem fixedThroatCoverInclusion_contMDiff :
    @ContMDiff ℝ _ ThroatCoverCoordinates _ _ ThroatCoverModel _
      throatCoverModelWithCorners
      (MappingTorusCover (fixedEquatorData period hPeriod)) _
      (fixedThroatCoverChartedSpace period hPeriod)
      CoverCoordinates _ _ CoverModel _ coverModelWithCorners
      (MappingTorusCover (reflectedSphereData period hPeriod)) _
      (reflectedSphereCoverChartedSpace period hPeriod) ω
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
  have hTo := chartedSpacePullback_toFun_contMDiff
    throatCoverModelWithCorners ω
    (coverHomeomorphProd (fixedEquatorData period hPeriod))
  have hInv := chartedSpacePullback_invFun_contMDiff
    coverModelWithCorners ω
    (coverHomeomorphProd (reflectedSphereData period hPeriod))
  have hProduct : ContMDiff throatCoverModelWithCorners
      coverModelWithCorners ω
      (Prod.map equatorialSphereInclusion (id : ℝ → ℝ)) :=
    equatorialSphereInclusion_contMDiff.prodMap contMDiff_id
  have hComposite := hInv.comp (hProduct.comp hTo)
  exact hComposite.congr fun point => by
    apply MappingTorusCover.ext <;> rfl

end Covers

end AnalyticDeckAction

section QuotientLocalSections

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

/-- Two local sections of the mapping-torus covering which select points in
the same fiber differ locally by the unique deck transformation joining their
values. -/
theorem localInverseAt_eventuallyEq_vadd
    (data : MappingTorusData X) (first second : MappingTorusCover data)
    (winding : ℤ) (hWinding : winding +ᵥ first = second) :
    (projectionIsLocalHomeomorph data).localInverseAt second =ᶠ[
        𝓝 (mappingTorusMk data first)]
      (fun base => winding +ᵥ
        (projectionIsLocalHomeomorph data).localInverseAt first base) := by
  let hf := projectionIsLocalHomeomorph data
  let firstSection := hf.localInverseAt first
  let secondSection := hf.localInverseAt second
  have hProjection : mappingTorusMk data second = mappingTorusMk data first := by
    rw [← hWinding]
    exact mappingTorusMk_vadd data winding first
  have hFirstSource : firstSection.source ∈ 𝓝 (mappingTorusMk data first) :=
    firstSection.open_source.mem_nhds hf.apply_self_mem_localInverseAt_source
  have hSecondSource : secondSection.source ∈ 𝓝 (mappingTorusMk data first) := by
    rw [← hProjection]
    exact secondSection.open_source.mem_nhds
      hf.apply_self_mem_localInverseAt_source
  have hSecondContinuous : ContinuousAt secondSection
      (mappingTorusMk data first) := by
    rw [← hProjection]
    exact secondSection.continuousAt hf.apply_self_mem_localInverseAt_source
  have hSecondValue :
      secondSection (mappingTorusMk data first) = second := by
    rw [← hProjection]
    exact hf.localInverseAt_apply_self
  have hSecondTarget : secondSection ⁻¹' secondSection.target ∈
      𝓝 (mappingTorusMk data first) := by
    apply hSecondContinuous.preimage_mem_nhds
    rw [hSecondValue]
    exact secondSection.open_target.mem_nhds
      hf.self_mem_localInverseAt_target
  have hFirstContinuous : ContinuousAt firstSection
      (mappingTorusMk data first) :=
    firstSection.continuousAt hf.apply_self_mem_localInverseAt_source
  have hDeckContinuous : ContinuousAt
      (fun base => winding +ᵥ firstSection base)
      (mappingTorusMk data first) :=
    (continuous_const_vadd data winding).continuousAt.comp hFirstContinuous
  have hDeckValue :
      winding +ᵥ firstSection (mappingTorusMk data first) = second := by
    rw [hf.localInverseAt_apply_self]
    exact hWinding
  have hDeckTarget :
      (fun base => winding +ᵥ firstSection base) ⁻¹' secondSection.target ∈
        𝓝 (mappingTorusMk data first) := by
    apply hDeckContinuous.preimage_mem_nhds
    rw [hDeckValue]
    exact secondSection.open_target.mem_nhds
      hf.self_mem_localInverseAt_target
  filter_upwards [hFirstSource, hSecondSource, hSecondTarget, hDeckTarget]
    with base hFirstSourceBase hSecondSourceBase hSecondTargetBase hDeckTargetBase
  apply hf.injOn_localInverseAt_target hSecondTargetBase hDeckTargetBase
  calc
    mappingTorusMk data (secondSection base) = base :=
      hf.apply_localInverseAt_of_mem hSecondSourceBase
    _ = mappingTorusMk data (firstSection base) :=
      (hf.apply_localInverseAt_of_mem hFirstSourceBase).symm
    _ = mappingTorusMk data (winding +ᵥ firstSection base) :=
      (mappingTorusMk_vadd data winding _).symm

end QuotientLocalSections

section SmoothHomeomorphCoordinates

variable {𝕜 E H M : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω} [IsManifold I n M]

/-- A homeomorphism which is `C^n` in both directions gives a groupoid-valued
change of coordinates between arbitrary atlas charts. -/
theorem smoothHomeomorph_coordinateChange_mem_groupoid
    (homeo : M ≃ₜ M)
    (hForward : ContMDiff I I n homeo)
    (hBackward : ContMDiff I I n homeo.symm)
    {first second : OpenPartialHomeomorph M H}
    (hFirst : first ∈ atlas H M) (hSecond : second ∈ atlas H M) :
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
    simpa only [transition, deck, mfld_simps]
      using hCoordinate
  have hProperty :=
    StructureGroupoid.LocalInvariantProp.liftPropOn_indep_chart
      (StructureGroupoid.isLocalStructomorphWithinAt_localInvariantProp
        (contDiffGroupoid n I))
      ((contDiffGroupoid n I).subset_maximalAtlas hFirst)
      ((contDiffGroupoid n I).subset_maximalAtlas hSecond)
      hLocal hCoordinate'
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

end SmoothHomeomorphCoordinates

end

end P0EFTJanusMappingTorusSmoothQuotient
end JanusFormal
