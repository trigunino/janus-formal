import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLorentzInteriorDenseParametrization4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLorentzVolumeTimeTranslationInvariance4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarStereographicVolumeComparison4D

/-!
# Local canonical-volume transport

The open fundamental strip is an injective, measure-preserving
parametrization of the mapping torus away from one null seam.  Together with
the stereographic product comparison this is the geometric input for the
finite-chart Rellich localization.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarLocalVolumeTransport4D

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeCoareaClosure4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalLorentzInteriorDenseParametrization4D
open P0EFTJanusMappingTorusCompleteTimeFlow4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeTimeTranslationInvariance4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarStereographicVolumeComparison4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData :=
  reflectedSphereData period hPeriod

private abbrev EffectiveQuotient :=
  MappingTorus (sphereData period hPeriod)

local instance effectiveCoverChartedSpace :
    ChartedSpace CoverModel
      (MappingTorusCover (sphereData period hPeriod)) :=
  reflectedSphereCoverChartedSpace period hPeriod

local instance effectiveCoverIsManifold :
    IsManifold coverModelWithCorners ω
      (MappingTorusCover (sphereData period hPeriod)) :=
  reflectedSphereCover_isManifold period hPeriod

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) :=
  borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- Open fundamental-strip parameters as points of the product cover. -/
def canonicalLorentzInteriorCoverMap
    (parameter : CanonicalLorentzInteriorParameter period) :
    MappingTorusCover (sphereData period hPeriod) :=
  (coverHomeomorphProd (sphereData period hPeriod)).symm
    (unitThreeSphereHomeomorph.symm parameter.1, parameter.2.1)

theorem canonicalLorentzInteriorCoverMap_isOpenEmbedding :
    Topology.IsOpenEmbedding
      (canonicalLorentzInteriorCoverMap period hPeriod) := by
  have hProduct :
      Topology.IsOpenEmbedding
        (Prod.map unitThreeSphereHomeomorph.symm
          (Subtype.val :
            canonicalLorentzInteriorTime period → Real)) :=
    unitThreeSphereHomeomorph.symm.isOpenEmbedding.prodMap
      isOpen_Ioo.isOpenEmbedding_subtypeVal
  exact
    (coverHomeomorphProd
      (sphereData period hPeriod)).symm.isOpenEmbedding.comp hProduct

/-- The open fundamental strip contains exactly one representative of every
orbit that it meets. -/
theorem canonicalLorentzInteriorPhysicalMap_injective :
    Function.Injective
      (canonicalLorentzInteriorPhysicalMap period hPeriod) := by
  intro first second hEqual
  change
    mappingTorusMk (sphereData period hPeriod)
        ((coverHomeomorphProd (sphereData period hPeriod)).symm
          (unitThreeSphereHomeomorph.symm first.1, first.2.1)) =
      mappingTorusMk (sphereData period hPeriod)
        ((coverHomeomorphProd (sphereData period hPeriod)).symm
          (unitThreeSphereHomeomorph.symm second.1, second.2.1)) at hEqual
  obtain ⟨winding, hWinding⟩ :=
    (mappingTorusMk_eq_iff_exists_vadd
      (sphereData period hPeriod) _ _).1 hEqual
  have hTime := congrArg MappingTorusCover.time hWinding
  change second.2.1 + (winding : Real) * period = first.2.1 at hTime
  have hWidth :
      max 0 period - min 0 period = |period| := by
    simpa using max_sub_min_eq_abs 0 period
  have hDifference :
      |first.2.1 - second.2.1| < |period| := by
    rw [abs_lt]
    constructor
    · rw [← hWidth]
      linarith [first.2.2.1, second.2.2.2]
    · rw [← hWidth]
      linarith [first.2.2.2, second.2.2.1]
  have hWindingMul :
      (winding : Real) * period =
        first.2.1 - second.2.1 := by
    linarith
  have hWindingAbsMul :
      |(winding : Real)| * |period| < |period| := by
    rw [← abs_mul, hWindingMul]
    exact hDifference
  have hWindingAbs : |(winding : Real)| < 1 := by
    rw [← mul_lt_mul_iff_right₀ (abs_pos.mpr hPeriod)]
    simpa [mul_comm] using hWindingAbsMul
  have hWindingLower : (-1 : Int) < winding := by
    exact_mod_cast (abs_lt.mp hWindingAbs).1
  have hWindingUpper : winding < (1 : Int) := by
    exact_mod_cast (abs_lt.mp hWindingAbs).2
  have hWindingZero : winding = 0 := by omega
  subst winding
  have hCover :
      (coverHomeomorphProd (sphereData period hPeriod)).symm
          (unitThreeSphereHomeomorph.symm second.1, second.2.1) =
        (coverHomeomorphProd (sphereData period hPeriod)).symm
          (unitThreeSphereHomeomorph.symm first.1, first.2.1) := by
    simpa using hWinding
  have hProduct := congrArg
    (coverHomeomorphProd (sphereData period hPeriod)) hCover
  change
    (unitThreeSphereHomeomorph.symm second.1, second.2.1) =
      (unitThreeSphereHomeomorph.symm first.1, first.2.1) at hProduct
  apply Prod.ext
  · exact unitThreeSphereHomeomorph.symm.injective
      (congrArg Prod.fst hProduct).symm
  · apply Subtype.ext
    exact (congrArg Prod.snd hProduct).symm

/-- The injective fundamental strip is an open chart of the mapping torus. -/
theorem canonicalLorentzInteriorPhysicalMap_isOpenEmbedding :
    Topology.IsOpenEmbedding
      (canonicalLorentzInteriorPhysicalMap period hPeriod) := by
  have hLocal :
      IsLocalHomeomorph
        (canonicalLorentzInteriorPhysicalMap period hPeriod) := by
    change IsLocalHomeomorph
      (mappingTorusMk (sphereData period hPeriod) ∘
        canonicalLorentzInteriorCoverMap period hPeriod)
    exact
      (mappingTorusMk_isCoveringMap
        (sphereData period hPeriod)).isLocalHomeomorph.comp
          (canonicalLorentzInteriorCoverMap_isOpenEmbedding
            period hPeriod).isLocalHomeomorph
  exact hLocal.isOpenEmbedding_of_injective
    (canonicalLorentzInteriorPhysicalMap_injective period hPeriod)

/-- The canonical quotient volume is concentrated on the open fundamental
strip; the omitted gluing seam is null. -/
theorem canonicalLorentzInteriorPhysicalMap_compl_range_null :
    intrinsicCanonicalLorentzVolumeMeasure period hPeriod
        (Set.range
          (canonicalLorentzInteriorPhysicalMap period hPeriod))ᶜ = 0 := by
  rw [← (canonicalLorentzInteriorPhysicalMap_measurePreserving
    period hPeriod).map_eq]
  rw [Measure.map_apply
    (canonicalLorentzInteriorPhysicalMap_continuous
      period hPeriod).measurable
    (canonicalLorentzInteriorPhysicalMap_isOpenEmbedding
      period hPeriod).isOpen_range.measurableSet.compl]
  simp

/-- Pulling the quotient volume back along the open fundamental strip
recovers exactly the source product measure. -/
theorem intrinsicCanonicalLorentzVolumeMeasure_comap_interior :
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod).comap
        (canonicalLorentzInteriorPhysicalMap period hPeriod) =
      canonicalLorentzInteriorMeasure period := by
  ext subset hSubset
  rw [(canonicalLorentzInteriorPhysicalMap_isOpenEmbedding
      period hPeriod).measurableEmbedding.comap_apply]
  rw [← (canonicalLorentzInteriorPhysicalMap_measurePreserving
    period hPeriod).map_eq]
  rw [(canonicalLorentzInteriorPhysicalMap_isOpenEmbedding
      period hPeriod).measurableEmbedding.map_apply]
  rw [(canonicalLorentzInteriorPhysicalMap_injective
    period hPeriod).preimage_image]

/-! ## Explicit measured stereographic charts -/

private abbrev StandardSphere :=
  Metric.sphere (0 : EuclideanR4) 1

/-- Product coordinates for one stereographic chart of the open strip. -/
abbrev CanonicalInteriorStereographicCoordinates :=
  EuclideanSpace Real (Fin 3) × canonicalLorentzInteriorTime period

/-- Stereographic coordinates mapped into the open fundamental strip. -/
def canonicalInteriorStereographicParameterMap
    (pole : StandardSphere)
    (coordinate : CanonicalInteriorStereographicCoordinates period) :
    CanonicalLorentzInteriorParameter period :=
  (stereographicInverseSphere pole coordinate.1, coordinate.2)

/-- Exact source measure in stereographic space-time coordinates. -/
def canonicalInteriorStereographicMeasure
    (pole : StandardSphere) :
    Measure (CanonicalInteriorStereographicCoordinates period) :=
  (stereographicSurfaceCoordinateMeasure pole).prod
    (canonicalLorentzInteriorTimeMeasure period)

local instance stereographicSurfaceCoordinateMeasure_isFinite
    (pole : StandardSphere) :
    IsFiniteMeasure (stereographicSurfaceCoordinateMeasure pole) := by
  constructor
  rw [stereographicSurfaceCoordinateMeasure_apply pole]
  exact measure_lt_top _ _

local instance canonicalLorentzInteriorTimeMeasure_isFinite :
    IsFiniteMeasure (canonicalLorentzInteriorTimeMeasure period) := by
  constructor
  change ((volume : Measure Real).comap
      (Subtype.val : canonicalLorentzInteriorTime period → Real)) Set.univ <
        (⊤ : ENNReal)
  have hTimeMeasurable :
      MeasurableSet (canonicalLorentzInteriorTime period) := by
    exact measurableSet_Ioo
  rw [comap_subtype_coe_apply hTimeMeasurable volume Set.univ]
  rw [Set.image_univ, Subtype.range_coe]
  unfold canonicalLorentzInteriorTime
  rw [Real.volume_Ioo]
  exact ENNReal.ofReal_lt_top

theorem canonicalInteriorStereographicParameterMap_isOpenEmbedding
    (pole : StandardSphere) :
    Topology.IsOpenEmbedding
      (canonicalInteriorStereographicParameterMap period pole) := by
  have hProduct :=
    (stereographicInverseSphere_isOpenEmbedding pole).prodMap
      (Topology.IsOpenEmbedding.id :
        Topology.IsOpenEmbedding
          (id : canonicalLorentzInteriorTime period →
            canonicalLorentzInteriorTime period))
  convert hProduct using 1
  funext coordinate
  rfl

theorem canonicalInteriorStereographicParameterMap_range
    (pole : StandardSphere) :
    Set.range (canonicalInteriorStereographicParameterMap period pole) =
      Set.range (stereographicInverseSphere pole) ×ˢ
        (Set.univ : Set (canonicalLorentzInteriorTime period)) := by
  ext parameter
  constructor
  · rintro ⟨coordinate, rfl⟩
    exact ⟨⟨coordinate.1, rfl⟩, Set.mem_univ coordinate.2⟩
  · rintro ⟨⟨coordinate, hCoordinate⟩, _⟩
    refine ⟨(coordinate, parameter.2), ?_⟩
    apply Prod.ext
    · exact hCoordinate
    · rfl

theorem canonicalInteriorStereographicMeasure_measurePreserving
    (pole : StandardSphere) :
    MeasurePreserving
      (canonicalInteriorStereographicParameterMap period pole)
      (canonicalInteriorStereographicMeasure period pole)
      ((canonicalLorentzInteriorMeasure period).restrict
        (Set.range
          (canonicalInteriorStereographicParameterMap period pole))) := by
  have hSphere :
      MeasurePreserving
        (stereographicInverseSphere pole)
        (stereographicSurfaceCoordinateMeasure pole)
        (((volume : Measure EuclideanR4).toSphere).restrict
          (Set.range (stereographicInverseSphere pole))) := by
    refine
      ⟨(stereographicInverseSphere_isOpenEmbedding
          pole).continuous.measurable, ?_⟩
    exact
      (stereographicInverseSphere_isOpenEmbedding
        pole).measurableEmbedding.map_comap _
  have hProduct := MeasurePreserving.prod hSphere
    (MeasurePreserving.id
      (canonicalLorentzInteriorTimeMeasure period))
  convert hProduct using 1
  · funext coordinate
    rfl
  · rfl
  · rw [canonicalInteriorStereographicParameterMap_range]
    change
      (((volume : Measure EuclideanR4).toSphere).prod
        (canonicalLorentzInteriorTimeMeasure period)).restrict
          (Set.range (stereographicInverseSphere pole) ×ˢ Set.univ) =
        _
    rw [← Measure.prod_restrict]
    simp

/-- Unshifted physical stereographic chart. -/
def canonicalInteriorStereographicPhysicalMap
    (pole : StandardSphere)
    (coordinate : CanonicalInteriorStereographicCoordinates period) :
    EffectiveQuotient period hPeriod :=
  canonicalLorentzInteriorPhysicalMap period hPeriod
    (canonicalInteriorStereographicParameterMap period pole coordinate)

theorem canonicalInteriorStereographicPhysicalMap_isOpenEmbedding
    (pole : StandardSphere) :
    Topology.IsOpenEmbedding
      (canonicalInteriorStereographicPhysicalMap
        period hPeriod pole) := by
  exact
    (canonicalLorentzInteriorPhysicalMap_isOpenEmbedding
      period hPeriod).comp
        (canonicalInteriorStereographicParameterMap_isOpenEmbedding
          period pole)

theorem canonicalInteriorStereographicPhysicalMap_measurePreserving
    (pole : StandardSphere) :
    MeasurePreserving
      (canonicalInteriorStereographicPhysicalMap period hPeriod pole)
      (canonicalInteriorStereographicMeasure period pole)
      ((intrinsicCanonicalLorentzVolumeMeasure period hPeriod).restrict
        (Set.range
          (canonicalInteriorStereographicPhysicalMap
            period hPeriod pole))) := by
  let parameterRange :=
    Set.range (canonicalInteriorStereographicParameterMap period pole)
  have hPhysicalRestricted :=
    (canonicalLorentzInteriorPhysicalMap_measurePreserving
      period hPeriod).restrict_image_emb
        (canonicalLorentzInteriorPhysicalMap_isOpenEmbedding
          period hPeriod).measurableEmbedding parameterRange
  have hComposite := hPhysicalRestricted.comp
    (canonicalInteriorStereographicMeasure_measurePreserving
      period pole)
  convert hComposite using 1
  · funext coordinate
    rfl
  · congr 2
    exact Set.range_comp _ _

/-- Time-shifted physical stereographic chart. -/
def shiftedCanonicalInteriorStereographicPhysicalMap
    (shift : Real)
    (pole : StandardSphere)
    (coordinate : CanonicalInteriorStereographicCoordinates period) :
    EffectiveQuotient period hPeriod :=
  effectiveTimeFlow period hPeriod shift
    (canonicalInteriorStereographicPhysicalMap
      period hPeriod pole coordinate)

theorem shiftedCanonicalInteriorStereographicPhysicalMap_isOpenEmbedding
    (shift : Real)
    (pole : StandardSphere) :
    Topology.IsOpenEmbedding
      (shiftedCanonicalInteriorStereographicPhysicalMap
        period hPeriod shift pole) := by
  exact
    (effectiveTimeFlowDiffeomorph
      period hPeriod shift).toHomeomorph.isOpenEmbedding.comp
        (canonicalInteriorStereographicPhysicalMap_isOpenEmbedding
          period hPeriod pole)

theorem shiftedCanonicalInteriorStereographicPhysicalMap_measurePreserving
    (shift : Real)
    (pole : StandardSphere) :
    MeasurePreserving
      (shiftedCanonicalInteriorStereographicPhysicalMap
        period hPeriod shift pole)
      (canonicalInteriorStereographicMeasure period pole)
      ((intrinsicCanonicalLorentzVolumeMeasure period hPeriod).restrict
        (Set.range
          (shiftedCanonicalInteriorStereographicPhysicalMap
            period hPeriod shift pole))) := by
  let chartRange :=
    Set.range
      (canonicalInteriorStereographicPhysicalMap
        period hPeriod pole)
  have hFlowRestricted :=
    (intrinsicCanonicalLorentzVolumeMeasure_timeTranslation_measurePreserving
      period hPeriod shift).restrict_image_emb
        (effectiveTimeFlowDiffeomorph
          period hPeriod shift).toHomeomorph.measurableEmbedding
        chartRange
  have hComposite := hFlowRestricted.comp
    (canonicalInteriorStereographicPhysicalMap_measurePreserving
      period hPeriod pole)
  convert hComposite using 1
  · funext coordinate
    rfl
  · congr 2
    exact Set.range_comp _ _

/-- Inclusion of subtype-valued time coordinates into the ambient product
coordinate space used by Euclidean Rellich. -/
def canonicalInteriorStereographicCoordinateInclusion
    (coordinate : CanonicalInteriorStereographicCoordinates period) :
    EuclideanSpace Real (Fin 3) × Real :=
  (coordinate.1, coordinate.2.1)

theorem canonicalInteriorStereographicCoordinateInclusion_isOpenEmbedding :
    Topology.IsOpenEmbedding
      (canonicalInteriorStereographicCoordinateInclusion period) := by
  have hTimeOpen :
      IsOpen (canonicalLorentzInteriorTime period) := by
    exact isOpen_Ioo
  have hProduct :=
    (Topology.IsOpenEmbedding.id :
      Topology.IsOpenEmbedding
        (id : EuclideanSpace Real (Fin 3) →
          EuclideanSpace Real (Fin 3))).prodMap
      hTimeOpen.isOpenEmbedding_subtypeVal
  convert hProduct using 1
  funext coordinate
  rfl

theorem canonicalInteriorStereographicCoordinateInclusion_range :
    Set.range (canonicalInteriorStereographicCoordinateInclusion period) =
      (Set.univ : Set (EuclideanSpace Real (Fin 3))) ×ˢ
        canonicalLorentzInteriorTime period := by
  ext coordinate
  constructor
  · rintro ⟨source, rfl⟩
    exact ⟨Set.mem_univ _, source.2.2⟩
  · rintro ⟨_, hTime⟩
    exact ⟨(coordinate.1, ⟨coordinate.2, hTime⟩), rfl⟩

theorem canonicalInteriorStereographicCoordinateInclusion_measurePreserving
    (pole : StandardSphere) :
    MeasurePreserving
      (canonicalInteriorStereographicCoordinateInclusion period)
      (canonicalInteriorStereographicMeasure period pole)
      ((stereographicProductCoordinateMeasure pole).restrict
        (Set.range
          (canonicalInteriorStereographicCoordinateInclusion period))) := by
  have hProduct := MeasurePreserving.prod
    (MeasurePreserving.id
      (stereographicSurfaceCoordinateMeasure pole))
    (canonicalLorentzInteriorTimeInclusion_measurePreserving period)
  have hTimeRange :
      (volume : Measure Real).restrict
          (canonicalLatitudeTimeInterval period) =
        (volume : Measure Real).restrict
          (canonicalLorentzInteriorTime period) := by
    calc
      (volume : Measure Real).restrict
          (canonicalLatitudeTimeInterval period) =
        Measure.map
          (Subtype.val :
            canonicalLorentzInteriorTime period → Real)
          (canonicalLorentzInteriorTimeMeasure period) :=
        (canonicalLorentzInteriorTimeInclusion_measurePreserving
          period).map_eq.symm
      _ = (volume : Measure Real).restrict
          (canonicalLorentzInteriorTime period) := by
        unfold canonicalLorentzInteriorTimeMeasure
        exact map_comap_subtype_coe measurableSet_Ioo volume
  convert hProduct using 1
  · funext coordinate
    rfl
  · rfl
  · rw [canonicalInteriorStereographicCoordinateInclusion_range]
    change
      ((stereographicSurfaceCoordinateMeasure pole).prod
        (volume : Measure Real)).restrict
          (Set.univ ×ˢ canonicalLorentzInteriorTime period) =
        (stereographicSurfaceCoordinateMeasure pole).prod
          ((volume : Measure Real).restrict
            (canonicalLatitudeTimeInterval period))
    rw [hTimeRange, ← Measure.prod_restrict]
    simp

/-- The inverse stereographic chart covers the sphere minus its pole. -/
theorem stereographicInverseSphere_range
    (pole : StandardSphere) :
    Set.range (stereographicInverseSphere pole) = {pole}ᶜ := by
  rw [stereographicInverseSphere_eq_stereographic_symm]
  apply Set.Subset.antisymm
  · rintro point ⟨coordinate, rfl⟩
    have hTarget :
        coordinate ∈ (stereographic' 3 pole).target := by
      simp
    have hSource :=
      (stereographic' 3 pole).map_target hTarget
    simpa using hSource
  · simpa using
      (stereographic' 3 pole).symm.target_subset_range

theorem stereographicInverseSphere_contMDiff
    (pole : StandardSphere) :
    ContMDiff (𝓡 3) (𝓡 3) ω
      (stereographicInverseSphere pole) := by
  rw [stereographicInverseSphere_eq_stereographic_symm]
  have hChartEq :
      chartAt (EuclideanSpace Real (Fin 3)) (-pole) =
        stereographic' 3 pole := by
    change stereographic' 3 (- -pole) = stereographic' 3 pole
    rw [neg_neg]
  have hChartAt :
      chartAt (EuclideanSpace Real (Fin 3)) (-pole) ∈
        IsManifold.maximalAtlas (𝓡 3) ω StandardSphere :=
    IsManifold.chart_mem_maximalAtlas
      (I := 𝓡 3) (-pole)
  rw [hChartEq] at hChartAt
  have hChart :
      stereographic' 3 pole ∈
        IsManifold.maximalAtlas (𝓡 3) ω StandardSphere :=
    hChartAt
  have hSmooth :=
    contMDiffOn_symm_of_mem_maximalAtlas hChart
  rw [stereographic'_target] at hSmooth
  exact contMDiffOn_univ.mp hSmooth

theorem canonicalLorentzFundamentalDomainMap_contMDiff :
    ContMDiff coverModelWithCorners coverModelWithCorners ω
      (canonicalLorentzFundamentalDomainMap period hPeriod) := by
  have hSphere :
      ContMDiff (𝓡 3) (𝓡 3) ω
        unitThreeSphereHomeomorph.symm :=
    chartedSpacePullback_invFun_contMDiff
      (𝓡 3) ω unitThreeSphereHomeomorph
  have hProduct :
      ContMDiff coverModelWithCorners coverModelWithCorners ω
        (fun parameter : StandardSphere × Real =>
          (unitThreeSphereHomeomorph.symm parameter.1,
            parameter.2)) :=
    (hSphere.comp contMDiff_fst).prodMk contMDiff_snd
  have hCover :
      ContMDiff coverModelWithCorners coverModelWithCorners ω
        (fun parameter : StandardSphere × Real =>
          (coverHomeomorphProd
            (sphereData period hPeriod)).symm
              (unitThreeSphereHomeomorph.symm parameter.1,
                parameter.2)) :=
    (chartedSpacePullback_invFun_contMDiff
      coverModelWithCorners ω
        (coverHomeomorphProd
          (sphereData period hPeriod))).comp hProduct
  exact
    (reflectedSphere_projection_isLocalDiffeomorph
      period hPeriod).contMDiff.comp hCover

/-- Ambient version of a shifted stereographic chart.  It is defined for all
real times; restriction to the open fundamental interval is the measured
embedding above. -/
def shiftedStereographicPhysicalMapAmbient
    (shift : Real)
    (pole : StandardSphere)
    (coordinate : EuclideanSpace Real (Fin 3) × Real) :
    EffectiveQuotient period hPeriod :=
  effectiveTimeFlow period hPeriod shift
    (canonicalLorentzFundamentalDomainMap period hPeriod
      (stereographicInverseSphere pole coordinate.1, coordinate.2))

theorem shiftedStereographicPhysicalMapAmbient_contMDiff
    (shift : Real)
    (pole : StandardSphere) :
    ContMDiff coverModelWithCorners coverModelWithCorners ω
      (shiftedStereographicPhysicalMapAmbient
        period hPeriod shift pole) := by
  have hParameter :
      ContMDiff coverModelWithCorners coverModelWithCorners ω
        (fun coordinate : EuclideanSpace Real (Fin 3) × Real =>
          (stereographicInverseSphere pole coordinate.1,
            coordinate.2)) :=
    ((stereographicInverseSphere_contMDiff pole).comp
      contMDiff_fst).prodMk contMDiff_snd
  exact
    (effectiveTimeFlow_contMDiff
      period hPeriod shift).comp
        (canonicalLorentzFundamentalDomainMap_contMDiff
          period hPeriod |>.comp hParameter)

theorem shiftedStereographicPhysicalMapAmbient_agrees
    (shift : Real)
    (pole : StandardSphere)
    (coordinate : CanonicalInteriorStereographicCoordinates period) :
    shiftedStereographicPhysicalMapAmbient
        period hPeriod shift pole
        (canonicalInteriorStereographicCoordinateInclusion
          period coordinate) =
      shiftedCanonicalInteriorStereographicPhysicalMap
        period hPeriod shift pole coordinate :=
  rfl

private theorem sphere_ne_neg_self
    (point : StandardSphere) :
    point ≠ -point := by
  intro hEqual
  have hVector :
      (point : EuclideanR4) = -(point : EuclideanR4) :=
    congrArg Subtype.val hEqual
  have hAdd :
      (point : EuclideanR4) + point = 0 :=
    eq_neg_iff_add_eq_zero.mp hVector
  have hSmul :
      (2 : Real) • (point : EuclideanR4) = 0 := by
    simpa [two_smul] using hAdd
  have hPointZero : (point : EuclideanR4) = 0 :=
    (smul_eq_zero.mp hSmul).resolve_left (by norm_num)
  have hNorm : ‖(point : EuclideanR4)‖ = 1 :=
    norm_eq_of_mem_sphere point
  rw [hPointZero, norm_zero] at hNorm
  norm_num at hNorm

/-- Shifted stereographic fundamental-strip charts form an open cover of the
entire mapping torus.  The shift and pole may be selected pointwise; compact
sets therefore admit a finite such subcover. -/
theorem exists_shiftedStereographicChart_mem
    (point : EffectiveQuotient period hPeriod) :
    ∃ shift : Real, ∃ pole : StandardSphere,
      point ∈ Set.range
        (shiftedCanonicalInteriorStereographicPhysicalMap
          period hPeriod shift pole) := by
  obtain ⟨anchor, hAnchor⟩ :=
    mappingTorusMk_surjective
      (sphereData period hPeriod) point
  let spherePoint : StandardSphere :=
    unitThreeSphereHomeomorph anchor.fiber
  let midpoint : Real :=
    (min 0 period + max 0 period) / 2
  have hEndpoints : min 0 period < max 0 period := by
    rcases lt_or_gt_of_ne hPeriod with hNegative | hPositive
    · simp [min_eq_right hNegative.le,
        max_eq_left hNegative.le, hNegative]
    · simp [min_eq_left hPositive.le,
        max_eq_right hPositive.le, hPositive]
  have hMidpoint :
      midpoint ∈ canonicalLorentzInteriorTime period := by
    unfold midpoint canonicalLorentzInteriorTime
    constructor <;> linarith
  let interiorTime : canonicalLorentzInteriorTime period :=
    ⟨midpoint, hMidpoint⟩
  let shift : Real := anchor.time - midpoint
  let pole : StandardSphere := -spherePoint
  have hSphereRange :
      spherePoint ∈ Set.range
        (stereographicInverseSphere pole) := by
    rw [stereographicInverseSphere_range]
    exact sphere_ne_neg_self spherePoint
  obtain ⟨spatialCoordinate, hSpatialCoordinate⟩ :=
    hSphereRange
  refine ⟨shift, pole, ⟨(spatialCoordinate, interiorTime), ?_⟩⟩
  change
    effectiveTimeFlow period hPeriod shift
        (mappingTorusMk (sphereData period hPeriod)
          ((coverHomeomorphProd
            (sphereData period hPeriod)).symm
              (unitThreeSphereHomeomorph.symm
                (stereographicInverseSphere pole spatialCoordinate),
                midpoint))) =
      point
  rw [effectiveTimeFlow_mk]
  calc
    mappingTorusMk (sphereData period hPeriod)
        (coverTimeTranslation (sphereData period hPeriod) shift
          ((coverHomeomorphProd
            (sphereData period hPeriod)).symm
              (unitThreeSphereHomeomorph.symm
                (stereographicInverseSphere pole spatialCoordinate),
                midpoint))) =
      mappingTorusMk (sphereData period hPeriod) anchor := by
        congr 1
        apply MappingTorusCover.ext
        · change unitThreeSphereHomeomorph.symm
            (stereographicInverseSphere pole spatialCoordinate) =
              anchor.fiber
          rw [hSpatialCoordinate]
          exact unitThreeSphereHomeomorph.symm_apply_apply anchor.fiber
        · change midpoint + shift = anchor.time
          simp [shift]
    _ = point := hAnchor

/-- Every compact quotient subset is covered by finitely many explicit
shifted measured stereographic charts. -/
theorem exists_finite_shiftedStereographicChart_cover
    {support : Set (EffectiveQuotient period hPeriod)}
    (hSupport : IsCompact support) :
    ∃ charts : Finset (Real × StandardSphere),
      support ⊆
        ⋃ chart ∈ charts,
          Set.range
            (shiftedCanonicalInteriorStereographicPhysicalMap
              period hPeriod chart.1 chart.2) := by
  classical
  apply hSupport.elim_finite_subcover
  · intro chart
    exact
      (shiftedCanonicalInteriorStereographicPhysicalMap_isOpenEmbedding
        period hPeriod chart.1 chart.2).isOpen_range
  · intro point hPoint
    obtain ⟨shift, pole, hChart⟩ :=
      exists_shiftedStereographicChart_mem
        period hPeriod point
    exact Set.mem_iUnion_of_mem (shift, pole) hChart

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarLocalVolumeTransport4D
end JanusFormal
