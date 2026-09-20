import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarStereographicVolumeComparison4D

/-!
# Quantitative stereographic volume comparison in dimension three

This file supplies the geometric core needed by the local Rellich transport.
On a compact set of one stereographic chart, the cone extension of the chart
inverse is bi-Lipschitz on a fixed radial annulus.  Euclidean Hausdorff-volume
estimates then compare round surface measure and chart Lebesgue measure.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalThroatStereographicVolumeComparison4D

set_option autoImplicit false
noncomputable section

open MeasureTheory Measure Metric Set
open scoped ContDiff ENNReal Manifold Pointwise
open P0EFTJanusMappingTorusSmoothAtlasFrontier

private abbrev StandardSphere := Metric.sphere (0 : EuclideanR3) 1

local instance euclideanR3_finrank :
    Fact (Module.finrank Real EuclideanR3 = 2 + 1) :=
  ⟨by simp [EuclideanR3]⟩

local instance chartRadial_volume_isAddHaarMeasure :
    (volume : Measure
      (EuclideanSpace Real (Fin 2) × Real)).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure _ _

private def orthogonalChartEquiv (pole : StandardSphere) :
    (Real ∙ (pole : EuclideanR3))ᗮ ≃ₗᵢ[Real]
      EuclideanSpace Real (Fin 2) :=
  (OrthonormalBasis.fromOrthogonalSpanSingleton 2
    (ne_zero_of_mem_unit_sphere pole)).repr

/-- The inverse of the standard stereographic chart, viewed in ambient
three-space. -/
def stereographicInverseVector
    (pole : StandardSphere)
    (coordinate : EuclideanSpace Real (Fin 2)) : EuclideanR3 :=
  stereoInvFunAux (pole : EuclideanR3)
    (((orthogonalChartEquiv pole).symm coordinate :
      (Real ∙ (pole : EuclideanR3))ᗮ) : EuclideanR3)

theorem stereographicInverseVector_mem_sphere
    (pole : StandardSphere)
    (coordinate : EuclideanSpace Real (Fin 2)) :
    stereographicInverseVector pole coordinate ∈
      Metric.sphere (0 : EuclideanR3) 1 :=
  stereoInvFunAux_mem (norm_eq_of_mem_sphere pole)
    ((orthogonalChartEquiv pole).symm coordinate).2

/-- The inverse stereographic chart as a point of the unit sphere. -/
def stereographicInverseSphere
    (pole : StandardSphere)
    (coordinate : EuclideanSpace Real (Fin 2)) : StandardSphere :=
  ⟨stereographicInverseVector pole coordinate,
    stereographicInverseVector_mem_sphere pole coordinate⟩

@[simp] theorem coe_stereographicInverseSphere
    (pole : StandardSphere)
    (coordinate : EuclideanSpace Real (Fin 2)) :
    (stereographicInverseSphere pole coordinate : EuclideanR3) =
      stereographicInverseVector pole coordinate :=
  rfl

theorem stereographicInverseSphere_eq_stereographic_symm
    (pole : StandardSphere) :
    stereographicInverseSphere pole =
      (stereographic' 2 pole).symm := by
  rfl

theorem stereographicInverseSphere_isOpenEmbedding
    (pole : StandardSphere) :
    Topology.IsOpenEmbedding
      (stereographicInverseSphere pole) := by
  rw [stereographicInverseSphere_eq_stereographic_symm]
  exact (stereographic' 2 pole).symm.to_isOpenEmbedding
    (by simp)

theorem norm_stereographicInverseVector
    (pole : StandardSphere)
    (coordinate : EuclideanSpace Real (Fin 2)) :
    ‖stereographicInverseVector pole coordinate‖ = 1 := by
  simpa [Metric.mem_sphere, dist_zero_right] using
    stereographicInverseVector_mem_sphere pole coordinate

/-- Radial extension of one stereographic inverse. -/
def stereographicConeMap
    (pole : StandardSphere)
    (point : EuclideanSpace Real (Fin 2) × Real) : EuclideanR3 :=
  point.2 • stereographicInverseVector pole point.1

/-- A fixed positive radial shell, represented in the open positive ray.
Its ambient-real image is the half-open interval `[1, 2)`. -/
private def polarRadialShell : Set (Ioi (0 : Real)) :=
  Iio ⟨2, by norm_num⟩ \ Iio ⟨1, by norm_num⟩

private theorem volumeIoiPow_polarRadialShell :
    Measure.volumeIoiPow 2 polarRadialShell =
      ENNReal.ofReal (7 / 3 : Real) := by
  rw [polarRadialShell, measure_sdiff
    (Iio_subset_Iio (by norm_num))
    measurableSet_Iio.nullMeasurableSet
    (by simp [Measure.volumeIoiPow_apply_Iio])]
  simp [Measure.volumeIoiPow_apply_Iio]
  norm_num
  rw [← ENNReal.ofReal_sub (8 / 3)
    (by norm_num : (0 : Real) ≤ 1 / 3)]
  norm_num

private def polarConeSet
    (sphereSet : Set StandardSphere) : Set EuclideanR3 :=
  ((↑) : ({0}ᶜ : Set EuclideanR3) → EuclideanR3) ''
    ((homeomorphUnitSphereProd EuclideanR3).symm ''
      (sphereSet ×ˢ polarRadialShell))

private theorem volume_polarConeSet
    (sphereSet : Set StandardSphere) :
    (volume : Measure EuclideanR3) (polarConeSet sphereSet) =
      (volume : Measure EuclideanR3).toSphere sphereSet *
        ENNReal.ofReal (7 / 3 : Real) := by
  unfold polarConeSet
  calc
    (volume : Measure EuclideanR3)
        (((↑) : ({0}ᶜ : Set EuclideanR3) → EuclideanR3) ''
          ((homeomorphUnitSphereProd EuclideanR3).symm ''
            (sphereSet ×ˢ polarRadialShell))) =
      ((volume : Measure EuclideanR3).comap
        ((↑) : ({0}ᶜ : Set EuclideanR3) → EuclideanR3))
          ((homeomorphUnitSphereProd EuclideanR3).symm ''
            (sphereSet ×ˢ polarRadialShell)) :=
      (comap_subtype_coe_apply
        (measurableSet_singleton (0 : EuclideanR3)).compl
        (volume : Measure EuclideanR3) _).symm
    _ = ((volume : Measure EuclideanR3).toSphere.prod
          (Measure.volumeIoiPow 2))
        (sphereSet ×ˢ polarRadialShell) := by
      rw [Homeomorph.image_symm]
      have hPolar :
          MeasurePreserving
            (homeomorphUnitSphereProd EuclideanR3).toMeasurableEquiv
            ((volume : Measure EuclideanR3).comap
              ((↑) : ({0}ᶜ : Set EuclideanR3) → EuclideanR3))
            ((volume : Measure EuclideanR3).toSphere.prod
              (Measure.volumeIoiPow 2)) := by
        simpa [EuclideanR3,
          Homeomorph.toMeasurableEquiv_coe] using
          (Measure.measurePreserving_homeomorphUnitSphereProd
            (μ := (volume : Measure EuclideanR3)))
      exact hPolar.measure_preimage_equiv
        (sphereSet ×ˢ polarRadialShell)
    _ = (volume : Measure EuclideanR3).toSphere sphereSet *
        ENNReal.ofReal (7 / 3 : Real) := by
      rw [Measure.prod_prod, volumeIoiPow_polarRadialShell]

private theorem polarConeSet_stereographicInverseSphere_image
    (pole : StandardSphere)
    (subset : Set (EuclideanSpace Real (Fin 2))) :
    polarConeSet
        (stereographicInverseSphere pole '' subset) =
      stereographicConeMap pole ''
        (subset ×ˢ Ico (1 : Real) 2) := by
  ext ambientPoint
  constructor
  · rintro ⟨nonzeroPoint, ⟨polarPoint, hPolarPoint, rfl⟩, rfl⟩
    rcases polarPoint with ⟨spherePoint, radialPoint⟩
    obtain ⟨coordinate, hCoordinate, hSphere⟩ :=
      hPolarPoint.1
    change stereographicInverseSphere pole coordinate =
      spherePoint at hSphere
    subst spherePoint
    refine ⟨(coordinate, radialPoint.1),
      ⟨hCoordinate, ?_⟩, ?_⟩
    · exact ⟨le_of_not_gt hPolarPoint.2.2,
        hPolarPoint.2.1⟩
    · simp [stereographicConeMap]
  · rintro ⟨point, hPoint, rfl⟩
    have hRadius : 0 < point.2 :=
      lt_of_lt_of_le zero_lt_one hPoint.2.1
    let radialPoint : Ioi (0 : Real) :=
      ⟨point.2, hRadius⟩
    let spherePoint : StandardSphere :=
      stereographicInverseSphere pole point.1
    refine ⟨(homeomorphUnitSphereProd EuclideanR3).symm
        (spherePoint, radialPoint), ?_, ?_⟩
    · refine ⟨(spherePoint, radialPoint), ?_, rfl⟩
      exact ⟨⟨point.1, hPoint.1, rfl⟩,
        ⟨hPoint.2.2, not_lt_of_ge hPoint.2.1⟩⟩
    · simp [spherePoint, radialPoint, stereographicConeMap]

theorem volume_stereographicConeMap_image_shell
    (pole : StandardSphere)
    (subset : Set (EuclideanSpace Real (Fin 2))) :
    (volume : Measure EuclideanR3)
        (stereographicConeMap pole ''
          (subset ×ˢ Ico (1 : Real) 2)) =
      (volume : Measure EuclideanR3).toSphere
          (stereographicInverseSphere pole '' subset) *
        ENNReal.ofReal (7 / 3 : Real) := by
  rw [← polarConeSet_stereographicInverseSphere_image,
    volume_polarConeSet]

private theorem polarSurfaceFactor_ne_zero :
    ENNReal.ofReal (7 / 3 : Real) ≠ 0 := by
  norm_num

private theorem polarSurfaceFactor_ne_top :
    ENNReal.ofReal (7 / 3 : Real) ≠ ⊤ :=
  ENNReal.ofReal_ne_top

private theorem volume_prod_Ico_one_two
    (subset : Set (EuclideanSpace Real (Fin 2))) :
    (volume : Measure
      (EuclideanSpace Real (Fin 2) × Real))
        (subset ×ˢ Ico (1 : Real) 2) =
      (volume : Measure
        (EuclideanSpace Real (Fin 2))) subset := by
  change ((volume : Measure
      (EuclideanSpace Real (Fin 2))).prod
        (volume : Measure Real))
      (subset ×ˢ Ico (1 : Real) 2) =
    (volume : Measure
      (EuclideanSpace Real (Fin 2))) subset
  rw [Measure.prod_prod, Real.volume_Ico]
  norm_num

theorem stereographicInverseVector_contDiff
    (pole : StandardSphere) :
    ContDiff Real ω (stereographicInverseVector pole) := by
  exact (contDiff_stereoInvFunAux (v := (pole : EuclideanR3))).comp
    ((Real ∙ (pole : EuclideanR3))ᗮ.subtypeL.contDiff.comp
      (orthogonalChartEquiv pole).symm.contDiff)

theorem stereographicConeMap_contDiff
    (pole : StandardSphere) :
    ContDiff Real ω (stereographicConeMap pole) := by
  exact (contDiff_snd.smul
    ((stereographicInverseVector_contDiff pole).comp contDiff_fst))

/-- Explicit inverse-coordinate formula for the cone chart away from the
origin and the pole ray. -/
def stereographicConeInverse
    (pole : StandardSphere)
    (point : EuclideanR3) :
    EuclideanSpace Real (Fin 2) × Real :=
  (orthogonalChartEquiv pole
      (stereoToFun (pole : EuclideanR3) (‖point‖⁻¹ • point)),
    ‖point‖)

theorem stereographicConeInverse_leftInverse
    (pole : StandardSphere)
    (point : EuclideanSpace Real (Fin 2) × Real)
    (hRadius : 0 < point.2) :
    stereographicConeInverse pole (stereographicConeMap pole point) =
      point := by
  have hNorm :
      ‖stereographicConeMap pole point‖ = point.2 := by
    rw [stereographicConeMap, norm_smul,
      norm_stereographicInverseVector, mul_one,
      Real.norm_eq_abs, abs_of_pos hRadius]
  apply Prod.ext
  · change orthogonalChartEquiv pole
        (stereoToFun (pole : EuclideanR3)
          (‖stereographicConeMap pole point‖⁻¹ •
            stereographicConeMap pole point)) = point.1
    rw [hNorm]
    have hNormalize :
        point.2⁻¹ • stereographicConeMap pole point =
          stereographicInverseVector pole point.1 := by
      rw [stereographicConeMap, smul_smul,
        inv_mul_cancel₀ hRadius.ne', one_smul]
    rw [hNormalize]
    change orthogonalChartEquiv pole
        (stereoToFun (pole : EuclideanR3)
          (stereoInvFunAux (pole : EuclideanR3)
            ((orthogonalChartEquiv pole).symm point.1))) = point.1
    change orthogonalChartEquiv pole
        (stereoToFun (pole : EuclideanR3)
          (stereoInvFun (norm_eq_of_mem_sphere pole)
            ((orthogonalChartEquiv pole).symm point.1))) = point.1
    rw [stereo_right_inv, LinearIsometryEquiv.apply_symm_apply]
  · exact hNorm

theorem stereographicConeMap_ne_zero
    (pole : StandardSphere)
    (point : EuclideanSpace Real (Fin 2) × Real)
    (hRadius : 0 < point.2) :
    stereographicConeMap pole point ≠ 0 := by
  intro hZero
  have hNormZero := congrArg norm hZero
  rw [stereographicConeMap, norm_smul,
    norm_stereographicInverseVector, mul_one,
    Real.norm_eq_abs, abs_of_pos hRadius, norm_zero] at hNormZero
  exact hRadius.ne' hNormZero

private theorem normalize_contDiffAt
    (point : EuclideanR3) (hPoint : point ≠ 0) :
    ContDiffAt Real 1 (fun value : EuclideanR3 => ‖value‖⁻¹ • value)
      point :=
  ((contDiffAt_norm Real hPoint).inv
    (by simpa using norm_ne_zero_iff.mpr hPoint)).smul contDiffAt_id

private theorem stereographicForwardAmbient_contDiffAt
    (pole : StandardSphere) (point : EuclideanR3)
    (hAwayFromPole :
      innerSL Real (pole : EuclideanR3) point ≠ 1) :
    ContDiffAt Real 1
      (fun value : EuclideanR3 =>
        orthogonalChartEquiv pole
          (stereoToFun (pole : EuclideanR3) value))
      point := by
  have hOpen :
      IsOpen {value : EuclideanR3 |
        innerSL Real (pole : EuclideanR3) value ≠ 1} := by
    have hClosed :
        IsClosed {value : EuclideanR3 |
          innerSL Real (pole : EuclideanR3) value = 1} :=
      isClosed_eq
        (innerSL Real (pole : EuclideanR3)).continuous continuous_const
    simpa only [Set.compl_setOf] using hClosed.isOpen_compl
  have hStereo :
      ContDiffAt Real 1 (stereoToFun (pole : EuclideanR3)) point :=
    (contDiffOn_stereoToFun (v := (pole : EuclideanR3))).contDiffAt
      (hOpen.mem_nhds hAwayFromPole)
  exact (orthogonalChartEquiv pole).contDiff.contDiffAt.comp
    point hStereo

private theorem stereographicConeInverse_contDiffAt
    (pole : StandardSphere) (point : EuclideanR3)
    (hPoint : point ≠ 0)
    (hAwayFromPole :
      innerSL Real (pole : EuclideanR3) (‖point‖⁻¹ • point) ≠ 1) :
    ContDiffAt Real 1 (stereographicConeInverse pole) point := by
  have hNormalize := normalize_contDiffAt point hPoint
  have hForward :=
    stereographicForwardAmbient_contDiffAt pole
      (‖point‖⁻¹ • point) hAwayFromPole
  have hFirst :
      ContDiffAt Real 1
        (fun value : EuclideanR3 =>
          orthogonalChartEquiv pole
            (stereoToFun (pole : EuclideanR3) (‖value‖⁻¹ • value)))
        point :=
    ContDiffAt.fun_comp
      (f := fun value : EuclideanR3 => ‖value‖⁻¹ • value)
      (g := fun value : EuclideanR3 =>
        orthogonalChartEquiv pole
          (stereoToFun (pole : EuclideanR3) value))
      point hForward hNormalize
  exact hFirst.prodMk (contDiffAt_norm Real hPoint)

theorem stereographicConeInverse_contDiffAt_image
    (pole : StandardSphere)
    (point : EuclideanSpace Real (Fin 2) × Real)
    (hRadius : 0 < point.2) :
    ContDiffAt Real 1 (stereographicConeInverse pole)
      (stereographicConeMap pole point) := by
  let imagePoint := stereographicConeMap pole point
  have hImagePoint : imagePoint ≠ 0 :=
    stereographicConeMap_ne_zero pole point hRadius
  have hNormalize :
      ‖imagePoint‖⁻¹ • imagePoint =
        stereographicInverseVector pole point.1 := by
    dsimp [imagePoint]
    rw [stereographicConeMap, norm_smul,
      norm_stereographicInverseVector, mul_one,
      Real.norm_eq_abs, abs_of_pos hRadius, smul_smul,
      inv_mul_cancel₀ hRadius.ne', one_smul]
  have hAwayFromPole :
      innerSL Real (pole : EuclideanR3)
          (‖imagePoint‖⁻¹ • imagePoint) ≠ 1 := by
    rw [hNormalize]
    intro hInner
    have hEqual :
        stereographicInverseVector pole point.1 = (pole : EuclideanR3) := by
      exact ((inner_eq_one_iff_of_norm_eq_one
        (norm_eq_of_mem_sphere pole)
        (norm_stereographicInverseVector pole point.1)).mp hInner).symm
    exact (stereoInvFun_ne_north_pole
      (norm_eq_of_mem_sphere pole)
      ((orthogonalChartEquiv pole).symm point.1))
      (Subtype.ext hEqual)
  exact stereographicConeInverse_contDiffAt
    pole imagePoint hImagePoint hAwayFromPole

/-! ## Compact annulus bi-Lipschitz bounds -/

/-- Fixed positive annulus used to convert surface measure to ordinary
three-dimensional volume without approaching the cone vertex. -/
def stereographicConeAnnulus
    (support : Set (EuclideanSpace Real (Fin 2))) :
    Set (EuclideanSpace Real (Fin 2) × Real) :=
  support ×ˢ Set.Icc (1 : Real) 2

theorem stereographicConeAnnulus_isCompact
    {support : Set (EuclideanSpace Real (Fin 2))}
    (hSupport : IsCompact support) :
    IsCompact (stereographicConeAnnulus support) :=
  hSupport.prod isCompact_Icc

theorem exists_stereographicConeMap_lipschitzOn
    (pole : StandardSphere)
    {support : Set (EuclideanSpace Real (Fin 2))}
    (hSupport : IsCompact support) :
    ∃ constant : NNReal,
      LipschitzOnWith constant (stereographicConeMap pole)
        (stereographicConeAnnulus support) := by
  apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (stereographicConeAnnulus_isCompact hSupport)
  exact ((stereographicConeMap_contDiff pole).of_le
    (by simp)).locallyLipschitz.locallyLipschitzOn

theorem exists_stereographicConeInverse_lipschitzOn
    (pole : StandardSphere)
    {support : Set (EuclideanSpace Real (Fin 2))}
    (hSupport : IsCompact support) :
    ∃ constant : NNReal,
      LipschitzOnWith constant (stereographicConeInverse pole)
        (stereographicConeMap pole ''
          stereographicConeAnnulus support) := by
  let annulus := stereographicConeAnnulus support
  have hAnnulus : IsCompact annulus :=
    stereographicConeAnnulus_isCompact hSupport
  have hImage : IsCompact (stereographicConeMap pole '' annulus) :=
    hAnnulus.image (stereographicConeMap_contDiff pole).continuous
  apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hImage
  intro imagePoint hImagePoint
  obtain ⟨point, hPoint, rfl⟩ := hImagePoint
  have hRadius : 0 < point.2 := by
    exact lt_of_lt_of_le zero_lt_one hPoint.2.1
  obtain ⟨constant, neighborhood, hNeighborhood, hLipschitz⟩ :=
    (stereographicConeInverse_contDiffAt_image
      pole point hRadius).exists_lipschitzOnWith
  exact ⟨constant, neighborhood,
    mem_nhdsWithin_of_mem_nhds hNeighborhood, hLipschitz⟩

theorem stereographicConeMap_exists_volume_image_bound
    (pole : StandardSphere)
    {support : Set (EuclideanSpace Real (Fin 2) × Real)}
    {constant : NNReal}
    (hLipschitz : LipschitzOnWith constant
      (stereographicConeMap pole) support) :
    ∃ bound : ENNReal, bound ≠ ⊤ ∧
      ∀ subset ⊆ support,
        (volume : Measure EuclideanR3)
            (stereographicConeMap pole '' subset) ≤
          bound *
            (volume : Measure
              (EuclideanSpace Real (Fin 2) × Real)) subset := by
  apply
    P0EFTJanusMappingTorusCanonicalPhysicalScalarStereographicVolumeComparison4D.exists_volume_image_le_of_lipschitzOn_of_finrank
      (dimension := 3)
    (Source := EuclideanSpace Real (Fin 2) × Real)
    (Target := EuclideanR3)
    (by simp [EuclideanR3])
    (by simp [EuclideanR3])
  exact hLipschitz

theorem stereographicConeMap_exists_volume_preimage_bound
    (pole : StandardSphere)
    {support : Set (EuclideanSpace Real (Fin 2) × Real)}
    {constant : NNReal}
    (hPositiveRadius : ∀ point ∈ support, 0 < point.2)
    (hInverseLipschitz : LipschitzOnWith constant
      (stereographicConeInverse pole)
      (stereographicConeMap pole '' support)) :
    ∃ bound : ENNReal, bound ≠ ⊤ ∧
      ∀ subset ⊆ support,
        (volume : Measure
            (EuclideanSpace Real (Fin 2) × Real)) subset ≤
          bound *
            (volume : Measure EuclideanR3)
              (stereographicConeMap pole '' subset) := by
  obtain ⟨bound, hBound, hVolumes⟩ :=
    P0EFTJanusMappingTorusCanonicalPhysicalScalarStereographicVolumeComparison4D.exists_volume_image_le_of_lipschitzOn_of_finrank
      (dimension := 3)
    (Source := EuclideanR3)
    (Target := EuclideanSpace Real (Fin 2) × Real)
    (by simp [EuclideanR3])
    (by simp [EuclideanR3])
    hInverseLipschitz
  refine ⟨bound, hBound, ?_⟩
  intro subset hSubset
  have hVolume :=
    hVolumes (stereographicConeMap pole '' subset)
      (Set.image_mono hSubset)
  have hImageIdentity :
      stereographicConeInverse pole ''
          (stereographicConeMap pole '' subset) =
        subset := by
    ext point
    constructor
    · rintro ⟨_, ⟨source, hSource, rfl⟩, rfl⟩
      simpa [stereographicConeInverse_leftInverse pole source
        (hPositiveRadius source (hSubset hSource))] using hSource
    · intro hPoint
      exact ⟨stereographicConeMap pole point,
        ⟨point, hPoint, rfl⟩,
        stereographicConeInverse_leftInverse pole point
          (hPositiveRadius point (hSubset hPoint))⟩
  simpa [hImageIdentity] using hVolume

/-- Round surface measure pulled back to one stereographic coordinate space. -/
def stereographicSurfaceCoordinateMeasure
    (pole : StandardSphere) :
    Measure (EuclideanSpace Real (Fin 2)) :=
  ((volume : Measure EuclideanR3).toSphere).comap
    (stereographicInverseSphere pole)

theorem stereographicSurfaceCoordinateMeasure_apply
    (pole : StandardSphere)
    (subset : Set (EuclideanSpace Real (Fin 2))) :
    stereographicSurfaceCoordinateMeasure pole subset =
      (volume : Measure EuclideanR3).toSphere
        (stereographicInverseSphere pole '' subset) := by
  exact
    (stereographicInverseSphere_isOpenEmbedding pole).measurableEmbedding.comap_apply
      _ subset

local instance stereographicSurfaceCoordinateMeasure_isFinite
    (pole : StandardSphere) :
    IsFiniteMeasure (stereographicSurfaceCoordinateMeasure pole) := by
  constructor
  rw [stereographicSurfaceCoordinateMeasure_apply pole]
  exact measure_lt_top _ _

/-- Uniform two-sided comparison between chart Lebesgue measure and round
surface measure on one compact stereographic support. -/
structure StereographicSurfaceLebesgueComparison
    (pole : StandardSphere)
    (support : Set (EuclideanSpace Real (Fin 2))) where
  lebesgueBound : ENNReal
  lebesgueBound_ne_top : lebesgueBound ≠ ⊤
  lebesgue_le_surface :
    ∀ subset ⊆ support,
      (volume : Measure
          (EuclideanSpace Real (Fin 2))) subset ≤
        lebesgueBound *
          (volume : Measure EuclideanR3).toSphere
            (stereographicInverseSphere pole '' subset)
  surfaceBound : ENNReal
  surfaceBound_ne_top : surfaceBound ≠ ⊤
  surface_le_lebesgue :
    ∀ subset ⊆ support,
      (volume : Measure EuclideanR3).toSphere
          (stereographicInverseSphere pole '' subset) ≤
        surfaceBound *
          (volume : Measure
            (EuclideanSpace Real (Fin 2))) subset

namespace StereographicSurfaceLebesgueComparison

theorem restricted_lebesgue_le_surface
    {pole : StandardSphere}
    {support : Set (EuclideanSpace Real (Fin 2))}
    (comparison :
      StereographicSurfaceLebesgueComparison pole support) :
    (volume : Measure (EuclideanSpace Real (Fin 2))).restrict support ≤
      comparison.lebesgueBound •
        (stereographicSurfaceCoordinateMeasure pole).restrict support := by
  apply Measure.le_iff.2
  intro subset hSubset
  rw [Measure.restrict_apply hSubset, Measure.smul_apply,
    Measure.restrict_apply hSubset, smul_eq_mul,
    stereographicSurfaceCoordinateMeasure_apply pole]
  exact comparison.lebesgue_le_surface
    (subset ∩ support) inter_subset_right

theorem restricted_surface_le_lebesgue
    {pole : StandardSphere}
    {support : Set (EuclideanSpace Real (Fin 2))}
    (comparison :
      StereographicSurfaceLebesgueComparison pole support) :
    (stereographicSurfaceCoordinateMeasure pole).restrict support ≤
      comparison.surfaceBound •
        (volume : Measure
          (EuclideanSpace Real (Fin 2))).restrict support := by
  apply Measure.le_iff.2
  intro subset hSubset
  rw [Measure.restrict_apply hSubset,
    stereographicSurfaceCoordinateMeasure_apply pole,
    Measure.smul_apply, Measure.restrict_apply hSubset, smul_eq_mul]
  exact comparison.surface_le_lebesgue
    (subset ∩ support) inter_subset_right

end StereographicSurfaceLebesgueComparison

/-- The round surface measure has finite positive chart density bounds on
every compact subset of a stereographic chart. -/
def compactStereographicSurfaceLebesgueComparison
    (pole : StandardSphere)
    {support : Set (EuclideanSpace Real (Fin 2))}
    (hSupport : IsCompact support) :
    StereographicSurfaceLebesgueComparison pole support := by
  let forwardConstantExistence :=
    exists_stereographicConeMap_lipschitzOn pole hSupport
  let forwardConstant :=
    Classical.choose forwardConstantExistence
  have hForwardLipschitz :=
    Classical.choose_spec forwardConstantExistence
  let forwardBoundExistence :=
    stereographicConeMap_exists_volume_image_bound
      pole hForwardLipschitz
  let forwardBound :=
    Classical.choose forwardBoundExistence
  have hForwardBound :
      forwardBound ≠ (⊤ : ENNReal) :=
    (Classical.choose_spec forwardBoundExistence).1
  have hForwardVolumes :=
    (Classical.choose_spec forwardBoundExistence).2
  let inverseConstantExistence :=
    exists_stereographicConeInverse_lipschitzOn pole hSupport
  let inverseConstant :=
    Classical.choose inverseConstantExistence
  have hInverseLipschitz :=
    Classical.choose_spec inverseConstantExistence
  have hPositiveRadius :
      ∀ point ∈ stereographicConeAnnulus support,
        0 < point.2 := by
    intro point hPoint
    exact lt_of_lt_of_le zero_lt_one hPoint.2.1
  let inverseBoundExistence :=
    stereographicConeMap_exists_volume_preimage_bound
      pole hPositiveRadius hInverseLipschitz
  let inverseBound :=
    Classical.choose inverseBoundExistence
  have hInverseBound :
      inverseBound ≠ (⊤ : ENNReal) :=
    (Classical.choose_spec inverseBoundExistence).1
  have hInverseVolumes :=
    (Classical.choose_spec inverseBoundExistence).2
  let surfaceFactor : ENNReal :=
    ENNReal.ofReal (7 / 3 : Real)
  refine
    { lebesgueBound := inverseBound * surfaceFactor
      lebesgueBound_ne_top := ENNReal.mul_ne_top hInverseBound
        polarSurfaceFactor_ne_top
      lebesgue_le_surface := ?_
      surfaceBound := surfaceFactor⁻¹ * forwardBound
      surfaceBound_ne_top :=
        ENNReal.mul_ne_top
          (ENNReal.inv_ne_top.2 polarSurfaceFactor_ne_zero)
          hForwardBound
      surface_le_lebesgue := ?_ }
  · intro subset hSubset
    have hShellSubset :
        subset ×ˢ Ico (1 : Real) 2 ⊆
          stereographicConeAnnulus support := by
      rintro ⟨coordinate, radius⟩
        ⟨hCoordinate, hRadius⟩
      exact ⟨hSubset hCoordinate,
        ⟨hRadius.1, hRadius.2.le⟩⟩
    have hVolume :=
      hInverseVolumes
        (subset ×ˢ Ico (1 : Real) 2) hShellSubset
    rw [volume_prod_Ico_one_two,
      volume_stereographicConeMap_image_shell] at hVolume
    calc
      (volume : Measure
          (EuclideanSpace Real (Fin 2))) subset ≤
        inverseBound *
          ((volume : Measure EuclideanR3).toSphere
            (stereographicInverseSphere pole '' subset) *
              surfaceFactor) := hVolume
      _ = (inverseBound * surfaceFactor) *
          (volume : Measure EuclideanR3).toSphere
            (stereographicInverseSphere pole '' subset) := by
        ac_rfl
  · intro subset hSubset
    have hShellSubset :
        subset ×ˢ Ico (1 : Real) 2 ⊆
          stereographicConeAnnulus support := by
      rintro ⟨coordinate, radius⟩
        ⟨hCoordinate, hRadius⟩
      exact ⟨hSubset hCoordinate,
        ⟨hRadius.1, hRadius.2.le⟩⟩
    have hVolume :=
      hForwardVolumes
        (subset ×ˢ Ico (1 : Real) 2) hShellSubset
    rw [volume_stereographicConeMap_image_shell,
      volume_prod_Ico_one_two] at hVolume
    calc
      (volume : Measure EuclideanR3).toSphere
          (stereographicInverseSphere pole '' subset) =
        surfaceFactor⁻¹ *
          ((volume : Measure EuclideanR3).toSphere
            (stereographicInverseSphere pole '' subset) *
              surfaceFactor) := by
        symm
        calc
          surfaceFactor⁻¹ *
              ((volume : Measure EuclideanR3).toSphere
                (stereographicInverseSphere pole '' subset) *
                  surfaceFactor) =
            (surfaceFactor⁻¹ * surfaceFactor) *
              (volume : Measure EuclideanR3).toSphere
                (stereographicInverseSphere pole '' subset) := by
              ac_rfl
          _ = (volume : Measure EuclideanR3).toSphere
                (stereographicInverseSphere pole '' subset) := by
              rw [ENNReal.inv_mul_cancel
                polarSurfaceFactor_ne_zero
                polarSurfaceFactor_ne_top, one_mul]
      _ ≤ surfaceFactor⁻¹ *
          (forwardBound *
            (volume : Measure
              (EuclideanSpace Real (Fin 2))) subset) :=
        mul_le_mul_left' hVolume _
      _ = (surfaceFactor⁻¹ * forwardBound) *
          (volume : Measure
            (EuclideanSpace Real (Fin 2))) subset := by
        ac_rfl

/-- Product of the pulled-back round surface measure and Lebesgue time. -/
def stereographicProductCoordinateMeasure
    (pole : StandardSphere) :
    Measure (EuclideanSpace Real (Fin 2) × Real) :=
  (stereographicSurfaceCoordinateMeasure pole).prod
    (volume : Measure Real)

private theorem prod_mono_left
    {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    {first second : Measure α}
    (time : Measure β) [SFinite time]
    (hMeasures : first ≤ second) :
    first.prod time ≤ second.prod time := by
  apply Measure.le_iff.2
  intro subset hSubset
  rw [Measure.prod_apply hSubset, Measure.prod_apply hSubset]
  exact lintegral_mono' hMeasures le_rfl

/-- Uniform two-sided comparison on an arbitrary compact subset of a
stereographic space-time product chart. -/
structure StereographicProductLebesgueComparison
    (pole : StandardSphere)
    (support : Set (EuclideanSpace Real (Fin 2) × Real)) where
  lebesgueBound : ENNReal
  lebesgueBound_ne_top : lebesgueBound ≠ ⊤
  lebesgue_le_surface :
    (volume : Measure
      (EuclideanSpace Real (Fin 2) × Real)).restrict support ≤
      lebesgueBound •
        (stereographicProductCoordinateMeasure pole).restrict support
  surfaceBound : ENNReal
  surfaceBound_ne_top : surfaceBound ≠ ⊤
  surface_le_lebesgue :
    (stereographicProductCoordinateMeasure pole).restrict support ≤
      surfaceBound •
        (volume : Measure
          (EuclideanSpace Real (Fin 2) × Real)).restrict support

/-- Compact stereographic product charts have finite positive volume
comparison constants, obtained from the round geometry rather than assumed. -/
def compactStereographicProductLebesgueComparison
    (pole : StandardSphere)
    {support : Set (EuclideanSpace Real (Fin 2) × Real)}
    (hSupport : IsCompact support) :
    StereographicProductLebesgueComparison pole support := by
  let spatialSupport :
      Set (EuclideanSpace Real (Fin 2)) :=
    Prod.fst '' support
  have hSpatialCompact : IsCompact spatialSupport :=
    hSupport.image continuous_fst
  let surfaceComparison :=
    compactStereographicSurfaceLebesgueComparison
      pole hSpatialCompact
  have hSupportSubset :
      support ⊆ spatialSupport ×ˢ (Set.univ : Set Real) := by
    intro point hPoint
    exact ⟨⟨point, hPoint, rfl⟩, Set.mem_univ point.2⟩
  have hLebesgueProduct :=
    prod_mono_left (volume : Measure Real)
      surfaceComparison.restricted_lebesgue_le_surface
  rw [Measure.prod_smul_left] at hLebesgueProduct
  have hSurfaceProduct :=
    prod_mono_left (volume : Measure Real)
      surfaceComparison.restricted_surface_le_lebesgue
  rw [Measure.prod_smul_left] at hSurfaceProduct
  have hLebesgueRestricted :
      (((volume : Measure
          (EuclideanSpace Real (Fin 2))).restrict spatialSupport).prod
          (volume : Measure Real)).restrict support =
        (volume : Measure
          (EuclideanSpace Real (Fin 2) × Real)).restrict support := by
    rw [Measure.restrict_prod_eq_prod_univ,
      Measure.restrict_restrict_of_subset hSupportSubset,
      ← Measure.volume_eq_prod]
  have hSurfaceRestricted :
      (((stereographicSurfaceCoordinateMeasure pole).restrict
          spatialSupport).prod (volume : Measure Real)).restrict support =
        (stereographicProductCoordinateMeasure pole).restrict support := by
    rw [Measure.restrict_prod_eq_prod_univ,
      Measure.restrict_restrict_of_subset hSupportSubset]
    rfl
  refine
    { lebesgueBound := surfaceComparison.lebesgueBound
      lebesgueBound_ne_top :=
        surfaceComparison.lebesgueBound_ne_top
      lebesgue_le_surface := ?_
      surfaceBound := surfaceComparison.surfaceBound
      surfaceBound_ne_top :=
        surfaceComparison.surfaceBound_ne_top
      surface_le_lebesgue := ?_ }
  · have hRestricted :=
      Measure.restrict_mono_measure hLebesgueProduct support
    rw [Measure.restrict_smul, hLebesgueRestricted,
      hSurfaceRestricted] at hRestricted
    exact hRestricted
  · have hRestricted :=
      Measure.restrict_mono_measure hSurfaceProduct support
    rw [Measure.restrict_smul, hSurfaceRestricted,
      hLebesgueRestricted] at hRestricted
    exact hRestricted

/-- The compact product comparison exposed on the canonical throat chart
coordinate type. -/
def compactThroatCoverLebesgueComparison
    (pole : StandardEquatorialTwoSphere)
    {support : Set ThroatCoverCoordinates}
    (hSupport : IsCompact support) :
    StereographicProductLebesgueComparison pole support :=
  compactStereographicProductLebesgueComparison pole hSupport

end
end P0EFTJanusMappingTorusCanonicalThroatStereographicVolumeComparison4D
end JanusFormal


