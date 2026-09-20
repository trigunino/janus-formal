import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLorentzInteriorDenseParametrization4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalThroatStereographicVolumeComparison4D

/-!
# Local canonical throat-volume transport

The open fundamental strip is an injective measured parametrization of the
actual throat away from its null seam.  Stereographic coordinates on `S^2`
then give explicit three-dimensional measured charts.  Time translates of
these charts cover the compact throat.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalThroatLocalVolumeTransport4D

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLorentzInteriorDenseParametrization4D
open P0EFTJanusMappingTorusCompleteTimeFlow4D
open P0EFTJanusMappingTorusCompleteIndependentFieldTimeAction4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusCanonicalThroatStereographicVolumeComparison4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev throatData := fixedEquatorData period hPeriod

private abbrev EffectiveThroat :=
  MappingTorus (throatData period hPeriod)

private abbrev StandardSphere :=
  Metric.sphere (0 : EuclideanR3) 1

local instance euclideanR3_finrank :
    Fact (Module.finrank Real EuclideanR3 = 2 + 1) :=
  ⟨by simp [EuclideanR3]⟩

local instance effectiveThroatCoverChartedSpace :
    ChartedSpace ThroatCoverModel
      (MappingTorusCover (throatData period hPeriod)) :=
  fixedThroatCoverChartedSpace period hPeriod

local instance effectiveThroatCoverIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (MappingTorusCover (throatData period hPeriod)) :=
  fixedThroatCover_isManifold period hPeriod

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance effectiveThroatMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) :=
  borel _

local instance effectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

/-! ## The measured open fundamental strip -/

/-- Round `S^2` points together with an interior fundamental time. -/
abbrev CanonicalThroatInteriorParameter :=
  StandardSphere × canonicalLorentzInteriorTime period

/-- Source product measure on the open throat strip. -/
def canonicalThroatInteriorMeasure :
    Measure (CanonicalThroatInteriorParameter period) :=
  (volume : Measure EuclideanR3).toSphere.prod
    (canonicalLorentzInteriorTimeMeasure period)

/-- Inclusion into the half-open source used to define the canonical throat
measure. -/
def canonicalThroatInteriorBaseInclusion
    (parameter : CanonicalThroatInteriorParameter period) :
    CanonicalLatitudeBase :=
  (parameter.1, parameter.2.1)

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

theorem canonicalThroatInteriorBaseInclusion_measurePreserving :
    MeasurePreserving
      (canonicalThroatInteriorBaseInclusion period)
      (canonicalThroatInteriorMeasure period)
      (canonicalLatitudeBaseMeasure period) := by
  change MeasurePreserving
    (Prod.map id
      (Subtype.val : canonicalLorentzInteriorTime period → Real))
    (((volume : Measure EuclideanR3).toSphere).prod
      (canonicalLorentzInteriorTimeMeasure period))
    (((volume : Measure EuclideanR3).toSphere).prod
      (volume.restrict (canonicalLatitudeTimeInterval period)))
  exact MeasurePreserving.prod
    (MeasurePreserving.id ((volume : Measure EuclideanR3).toSphere))
    (canonicalLorentzInteriorTimeInclusion_measurePreserving period)

/-- Open fundamental-strip parameters as points of the throat cover. -/
def canonicalThroatInteriorCoverMap
    (parameter : CanonicalThroatInteriorParameter period) :
    MappingTorusCover (throatData period hPeriod) :=
  (coverHomeomorphProd (throatData period hPeriod)).symm
    (equatorialTwoSphereHomeomorph.symm parameter.1, parameter.2.1)

theorem canonicalThroatInteriorCoverMap_isOpenEmbedding :
    Topology.IsOpenEmbedding
      (canonicalThroatInteriorCoverMap period hPeriod) := by
  have hProduct :
      Topology.IsOpenEmbedding
        (Prod.map equatorialTwoSphereHomeomorph.symm
          (Subtype.val :
            canonicalLorentzInteriorTime period → Real)) :=
    equatorialTwoSphereHomeomorph.symm.isOpenEmbedding.prodMap
      isOpen_Ioo.isOpenEmbedding_subtypeVal
  exact
    (coverHomeomorphProd
      (throatData period hPeriod)).symm.isOpenEmbedding.comp hProduct

/-- Open fundamental-strip map to the actual throat quotient. -/
def canonicalThroatInteriorPhysicalMap
    (parameter : CanonicalThroatInteriorParameter period) :
    EffectiveThroat period hPeriod :=
  canonicalLatitudeThroatMap period hPeriod
    (canonicalThroatInteriorBaseInclusion period parameter)

theorem canonicalThroatInteriorPhysicalMap_injective :
    Function.Injective
      (canonicalThroatInteriorPhysicalMap period hPeriod) := by
  intro first second hEqual
  change
    mappingTorusMk (throatData period hPeriod)
        ((coverHomeomorphProd (throatData period hPeriod)).symm
          (equatorialTwoSphereHomeomorph.symm first.1, first.2.1)) =
      mappingTorusMk (throatData period hPeriod)
        ((coverHomeomorphProd (throatData period hPeriod)).symm
          (equatorialTwoSphereHomeomorph.symm second.1, second.2.1)) at hEqual
  obtain ⟨winding, hWinding⟩ :=
    (mappingTorusMk_eq_iff_exists_vadd
      (throatData period hPeriod) _ _).1 hEqual
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
      (winding : Real) * period = first.2.1 - second.2.1 := by
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
      (coverHomeomorphProd (throatData period hPeriod)).symm
          (equatorialTwoSphereHomeomorph.symm second.1, second.2.1) =
        (coverHomeomorphProd (throatData period hPeriod)).symm
          (equatorialTwoSphereHomeomorph.symm first.1, first.2.1) := by
    simpa using hWinding
  have hProduct := congrArg
    (coverHomeomorphProd (throatData period hPeriod)) hCover
  change
    (equatorialTwoSphereHomeomorph.symm second.1, second.2.1) =
      (equatorialTwoSphereHomeomorph.symm first.1, first.2.1) at hProduct
  apply Prod.ext
  · exact equatorialTwoSphereHomeomorph.symm.injective
      (congrArg Prod.fst hProduct).symm
  · apply Subtype.ext
    exact (congrArg Prod.snd hProduct).symm

theorem canonicalThroatInteriorPhysicalMap_isOpenEmbedding :
    Topology.IsOpenEmbedding
      (canonicalThroatInteriorPhysicalMap period hPeriod) := by
  have hLocal :
      IsLocalHomeomorph
        (canonicalThroatInteriorPhysicalMap period hPeriod) := by
    change IsLocalHomeomorph
      (mappingTorusMk (throatData period hPeriod) ∘
        canonicalThroatInteriorCoverMap period hPeriod)
    exact
      (mappingTorusMk_isCoveringMap
        (throatData period hPeriod)).isLocalHomeomorph.comp
          (canonicalThroatInteriorCoverMap_isOpenEmbedding
            period hPeriod).isLocalHomeomorph
  exact hLocal.isOpenEmbedding_of_injective
    (canonicalThroatInteriorPhysicalMap_injective period hPeriod)

theorem canonicalThroatInteriorPhysicalMap_measurePreserving :
    MeasurePreserving
      (canonicalThroatInteriorPhysicalMap period hPeriod)
      (canonicalThroatInteriorMeasure period)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  have hThroat :
      MeasurePreserving
        (canonicalLatitudeThroatMap period hPeriod)
        (canonicalLatitudeBaseMeasure period)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
    rw [intrinsicCanonicalThroatVolumeMeasure_eq_latitudeBase]
    exact
      (canonicalLatitudeThroatMap_continuous
        period hPeriod).measurable.measurePreserving
          (canonicalLatitudeBaseMeasure period)
  exact hThroat.comp
    (canonicalThroatInteriorBaseInclusion_measurePreserving period)

theorem canonicalThroatInteriorPhysicalMap_compl_range_null :
    intrinsicCanonicalThroatVolumeMeasure period hPeriod
        (Set.range
          (canonicalThroatInteriorPhysicalMap period hPeriod))ᶜ = 0 := by
  rw [← (canonicalThroatInteriorPhysicalMap_measurePreserving
    period hPeriod).map_eq]
  rw [Measure.map_apply
    (canonicalThroatInteriorPhysicalMap_isOpenEmbedding
      period hPeriod).continuous.measurable
    (canonicalThroatInteriorPhysicalMap_isOpenEmbedding
      period hPeriod).isOpen_range.measurableSet.compl]
  simp

theorem intrinsicCanonicalThroatVolumeMeasure_comap_interior :
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod).comap
        (canonicalThroatInteriorPhysicalMap period hPeriod) =
      canonicalThroatInteriorMeasure period := by
  ext subset hSubset
  rw [(canonicalThroatInteriorPhysicalMap_isOpenEmbedding
      period hPeriod).measurableEmbedding.comap_apply]
  rw [← (canonicalThroatInteriorPhysicalMap_measurePreserving
    period hPeriod).map_eq]
  rw [(canonicalThroatInteriorPhysicalMap_isOpenEmbedding
      period hPeriod).measurableEmbedding.map_apply]
  rw [(canonicalThroatInteriorPhysicalMap_injective
    period hPeriod).preimage_image]

/-! ## Explicit measured stereographic charts -/

/-- Product coordinates for one stereographic chart of the open throat
strip. -/
abbrev ThroatInteriorStereographicCoordinates :=
  EuclideanSpace Real (Fin 2) × canonicalLorentzInteriorTime period

/-- Stereographic coordinates mapped into the open throat strip. -/
def throatInteriorStereographicParameterMap
    (pole : StandardSphere)
    (coordinate : ThroatInteriorStereographicCoordinates period) :
    CanonicalThroatInteriorParameter period :=
  (stereographicInverseSphere pole coordinate.1, coordinate.2)

/-- Exact source measure in throat stereographic space-time coordinates. -/
def throatInteriorStereographicMeasure
    (pole : StandardSphere) :
    Measure (ThroatInteriorStereographicCoordinates period) :=
  (stereographicSurfaceCoordinateMeasure pole).prod
    (canonicalLorentzInteriorTimeMeasure period)

local instance stereographicSurfaceCoordinateMeasure_isFinite
    (pole : StandardSphere) :
    IsFiniteMeasure (stereographicSurfaceCoordinateMeasure pole) := by
  constructor
  rw [stereographicSurfaceCoordinateMeasure_apply pole]
  exact measure_lt_top _ _

theorem throatInteriorStereographicParameterMap_isOpenEmbedding
    (pole : StandardSphere) :
    Topology.IsOpenEmbedding
      (throatInteriorStereographicParameterMap period pole) := by
  have hProduct :=
    (stereographicInverseSphere_isOpenEmbedding pole).prodMap
      (Topology.IsOpenEmbedding.id :
        Topology.IsOpenEmbedding
          (id : canonicalLorentzInteriorTime period →
            canonicalLorentzInteriorTime period))
  convert hProduct using 1
  funext coordinate
  rfl

theorem throatInteriorStereographicParameterMap_range
    (pole : StandardSphere) :
    Set.range (throatInteriorStereographicParameterMap period pole) =
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

theorem throatInteriorStereographicMeasure_measurePreserving
    (pole : StandardSphere) :
    MeasurePreserving
      (throatInteriorStereographicParameterMap period pole)
      (throatInteriorStereographicMeasure period pole)
      ((canonicalThroatInteriorMeasure period).restrict
        (Set.range
          (throatInteriorStereographicParameterMap period pole))) := by
  have hSphere :
      MeasurePreserving
        (stereographicInverseSphere pole)
        (stereographicSurfaceCoordinateMeasure pole)
        (((volume : Measure EuclideanR3).toSphere).restrict
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
  · rw [throatInteriorStereographicParameterMap_range]
    change
      (((volume : Measure EuclideanR3).toSphere).prod
        (canonicalLorentzInteriorTimeMeasure period)).restrict
          (Set.range (stereographicInverseSphere pole) ×ˢ Set.univ) =
        _
    rw [← Measure.prod_restrict]
    simp

/-- Unshifted measured stereographic chart on the actual throat. -/
def throatInteriorStereographicPhysicalMap
    (pole : StandardSphere)
    (coordinate : ThroatInteriorStereographicCoordinates period) :
    EffectiveThroat period hPeriod :=
  canonicalThroatInteriorPhysicalMap period hPeriod
    (throatInteriorStereographicParameterMap period pole coordinate)

theorem throatInteriorStereographicPhysicalMap_isOpenEmbedding
    (pole : StandardSphere) :
    Topology.IsOpenEmbedding
      (throatInteriorStereographicPhysicalMap
        period hPeriod pole) := by
  exact
    (canonicalThroatInteriorPhysicalMap_isOpenEmbedding
      period hPeriod).comp
        (throatInteriorStereographicParameterMap_isOpenEmbedding
          period pole)

theorem throatInteriorStereographicPhysicalMap_measurePreserving
    (pole : StandardSphere) :
    MeasurePreserving
      (throatInteriorStereographicPhysicalMap period hPeriod pole)
      (throatInteriorStereographicMeasure period pole)
      ((intrinsicCanonicalThroatVolumeMeasure period hPeriod).restrict
        (Set.range
          (throatInteriorStereographicPhysicalMap
            period hPeriod pole))) := by
  let parameterRange :=
    Set.range (throatInteriorStereographicParameterMap period pole)
  have hPhysicalRestricted :=
    (canonicalThroatInteriorPhysicalMap_measurePreserving
      period hPeriod).restrict_image_emb
        (canonicalThroatInteriorPhysicalMap_isOpenEmbedding
          period hPeriod).measurableEmbedding parameterRange
  have hComposite := hPhysicalRestricted.comp
    (throatInteriorStereographicMeasure_measurePreserving
      period pole)
  convert hComposite using 1
  · funext coordinate
    rfl
  · congr 2
    exact Set.range_comp _ _

/-- Time-shifted measured stereographic chart on the actual throat. -/
def shiftedThroatInteriorStereographicPhysicalMap
    (shift : Real)
    (pole : StandardSphere)
    (coordinate : ThroatInteriorStereographicCoordinates period) :
    EffectiveThroat period hPeriod :=
  throatTimeFlow period hPeriod shift
    (throatInteriorStereographicPhysicalMap
      period hPeriod pole coordinate)

theorem shiftedThroatInteriorStereographicPhysicalMap_isOpenEmbedding
    (shift : Real)
    (pole : StandardSphere) :
    Topology.IsOpenEmbedding
      (shiftedThroatInteriorStereographicPhysicalMap
        period hPeriod shift pole) := by
  exact
    (throatTimeFlowDiffeomorph
      period hPeriod shift).toHomeomorph.isOpenEmbedding.comp
        (throatInteriorStereographicPhysicalMap_isOpenEmbedding
          period hPeriod pole)

theorem shiftedThroatInteriorStereographicPhysicalMap_measurePreserving
    (shift : Real)
    (pole : StandardSphere) :
    MeasurePreserving
      (shiftedThroatInteriorStereographicPhysicalMap
        period hPeriod shift pole)
      (throatInteriorStereographicMeasure period pole)
      ((intrinsicCanonicalThroatVolumeMeasure period hPeriod).restrict
        (Set.range
          (shiftedThroatInteriorStereographicPhysicalMap
            period hPeriod shift pole))) := by
  let chartRange :=
    Set.range
      (throatInteriorStereographicPhysicalMap
        period hPeriod pole)
  have hFlowRestricted :=
    (intrinsicCanonicalThroatVolumeMeasure_timeTranslation_measurePreserving
      period hPeriod shift).restrict_image_emb
        (throatTimeFlowDiffeomorph
          period hPeriod shift).toHomeomorph.measurableEmbedding
        chartRange
  have hComposite := hFlowRestricted.comp
    (throatInteriorStereographicPhysicalMap_measurePreserving
      period hPeriod pole)
  convert hComposite using 1
  · funext coordinate
    rfl
  · congr 2
    exact Set.range_comp _ _

/-- Inclusion into the ambient coordinate space used by Euclidean Rellich. -/
def throatInteriorStereographicCoordinateInclusion
    (coordinate : ThroatInteriorStereographicCoordinates period) :
    ThroatCoverCoordinates :=
  (coordinate.1, coordinate.2.1)

theorem throatInteriorStereographicCoordinateInclusion_isOpenEmbedding :
    Topology.IsOpenEmbedding
      (throatInteriorStereographicCoordinateInclusion period) := by
  have hTimeOpen :
      IsOpen (canonicalLorentzInteriorTime period) := by
    exact isOpen_Ioo
  have hProduct :=
    (Topology.IsOpenEmbedding.id :
      Topology.IsOpenEmbedding
        (id : EuclideanSpace Real (Fin 2) →
          EuclideanSpace Real (Fin 2))).prodMap
      hTimeOpen.isOpenEmbedding_subtypeVal
  convert hProduct using 1
  funext coordinate
  rfl

theorem throatInteriorStereographicCoordinateInclusion_range :
    Set.range (throatInteriorStereographicCoordinateInclusion period) =
      (Set.univ : Set (EuclideanSpace Real (Fin 2))) ×ˢ
        canonicalLorentzInteriorTime period := by
  ext coordinate
  constructor
  · rintro ⟨source, rfl⟩
    exact ⟨Set.mem_univ _, source.2.2⟩
  · rintro ⟨_, hTime⟩
    exact ⟨(coordinate.1, ⟨coordinate.2, hTime⟩), rfl⟩

theorem throatInteriorStereographicCoordinateInclusion_measurePreserving
    (pole : StandardSphere) :
    MeasurePreserving
      (throatInteriorStereographicCoordinateInclusion period)
      (throatInteriorStereographicMeasure period pole)
      ((stereographicProductCoordinateMeasure pole).restrict
        (Set.range
          (throatInteriorStereographicCoordinateInclusion period))) := by
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
  · rw [throatInteriorStereographicCoordinateInclusion_range]
    change
      ((stereographicSurfaceCoordinateMeasure pole).prod
        (volume : Measure Real)).restrict
          (Set.univ ×ˢ canonicalLorentzInteriorTime period) =
        (stereographicSurfaceCoordinateMeasure pole).prod
          ((volume : Measure Real).restrict
            (canonicalLatitudeTimeInterval period))
    rw [hTimeRange, ← Measure.prod_restrict]
    simp

/-! ## Smooth ambient charts and a finite shifted cover -/

/-- The inverse stereographic chart covers the two-sphere minus its pole. -/
theorem stereographicInverseSphere_range
    (pole : StandardSphere) :
    Set.range (stereographicInverseSphere pole) = {pole}ᶜ := by
  rw [stereographicInverseSphere_eq_stereographic_symm]
  apply Set.Subset.antisymm
  · rintro point ⟨coordinate, rfl⟩
    have hTarget :
        coordinate ∈ (stereographic' 2 pole).target := by
      simp
    have hSource :=
      (stereographic' 2 pole).map_target hTarget
    simpa using hSource
  · simpa using
      (stereographic' 2 pole).symm.target_subset_range

theorem stereographicInverseSphere_contMDiff
    (pole : StandardSphere) :
    ContMDiff (𝓡 2) (𝓡 2) ω
      (stereographicInverseSphere pole) := by
  rw [stereographicInverseSphere_eq_stereographic_symm]
  have hChartEq :
      chartAt (EuclideanSpace Real (Fin 2)) (-pole) =
        stereographic' 2 pole := by
    change stereographic' 2 (- -pole) = stereographic' 2 pole
    rw [neg_neg]
  have hChartAt :
      chartAt (EuclideanSpace Real (Fin 2)) (-pole) ∈
        IsManifold.maximalAtlas (𝓡 2) ω StandardSphere :=
    IsManifold.chart_mem_maximalAtlas
      (I := 𝓡 2) (-pole)
  rw [hChartEq] at hChartAt
  have hSmooth :=
    contMDiffOn_symm_of_mem_maximalAtlas hChartAt
  rw [stereographic'_target] at hSmooth
  exact contMDiffOn_univ.mp hSmooth

/-- Smoothness of the public fundamental-domain map to the throat. -/
theorem canonicalLatitudeThroatMap_contMDiff :
    ContMDiff throatCoverModelWithCorners
      throatCoverModelWithCorners ω
      (canonicalLatitudeThroatMap period hPeriod) := by
  have hSphere :
      ContMDiff (𝓡 2) (𝓡 2) ω
        equatorialTwoSphereHomeomorph.symm :=
    chartedSpacePullback_invFun_contMDiff
      (𝓡 2) ω equatorialTwoSphereHomeomorph
  have hProduct :
      ContMDiff throatCoverModelWithCorners
        throatCoverModelWithCorners ω
        (fun parameter : StandardSphere × Real =>
          (equatorialTwoSphereHomeomorph.symm parameter.1,
            parameter.2)) :=
    (hSphere.comp contMDiff_fst).prodMk contMDiff_snd
  have hCover :
      ContMDiff throatCoverModelWithCorners
        throatCoverModelWithCorners ω
        (fun parameter : StandardSphere × Real =>
          (coverHomeomorphProd
            (throatData period hPeriod)).symm
              (equatorialTwoSphereHomeomorph.symm parameter.1,
                parameter.2)) :=
    (chartedSpacePullback_invFun_contMDiff
      throatCoverModelWithCorners ω
        (coverHomeomorphProd
          (throatData period hPeriod))).comp hProduct
  exact
    (fixedThroat_projection_isLocalDiffeomorph
      period hPeriod).contMDiff.comp hCover

/-- Ambient version of a shifted measured chart, defined for all real time
coordinates. -/
def shiftedThroatStereographicPhysicalMapAmbient
    (shift : Real)
    (pole : StandardSphere)
    (coordinate : ThroatCoverCoordinates) :
    EffectiveThroat period hPeriod :=
  throatTimeFlow period hPeriod shift
    (canonicalLatitudeThroatMap period hPeriod
      (stereographicInverseSphere pole coordinate.1, coordinate.2))

theorem shiftedThroatStereographicPhysicalMapAmbient_contMDiff
    (shift : Real)
    (pole : StandardSphere) :
    ContMDiff throatCoverModelWithCorners
      throatCoverModelWithCorners ω
      (shiftedThroatStereographicPhysicalMapAmbient
        period hPeriod shift pole) := by
  have hParameter :
      ContMDiff throatCoverModelWithCorners
        throatCoverModelWithCorners ω
        (fun coordinate : ThroatCoverCoordinates =>
          (stereographicInverseSphere pole coordinate.1,
            coordinate.2)) :=
    ((stereographicInverseSphere_contMDiff pole).comp
      contMDiff_fst).prodMk contMDiff_snd
  exact
    (throatTimeFlow_contMDiff
      period hPeriod shift).comp
        (canonicalLatitudeThroatMap_contMDiff
          period hPeriod |>.comp hParameter)

theorem shiftedThroatStereographicPhysicalMapAmbient_agrees
    (shift : Real)
    (pole : StandardSphere)
    (coordinate : ThroatInteriorStereographicCoordinates period) :
    shiftedThroatStereographicPhysicalMapAmbient
        period hPeriod shift pole
        (throatInteriorStereographicCoordinateInclusion
          period coordinate) =
      shiftedThroatInteriorStereographicPhysicalMap
        period hPeriod shift pole coordinate :=
  rfl

private theorem sphere_ne_neg_self
    (point : StandardSphere) :
    point ≠ -point := by
  intro hEqual
  have hVector :
      (point : EuclideanR3) = -(point : EuclideanR3) :=
    congrArg Subtype.val hEqual
  have hAdd :
      (point : EuclideanR3) + point = 0 :=
    eq_neg_iff_add_eq_zero.mp hVector
  have hSmul :
      (2 : Real) • (point : EuclideanR3) = 0 := by
    simpa [two_smul] using hAdd
  have hPointZero : (point : EuclideanR3) = 0 :=
    (smul_eq_zero.mp hSmul).resolve_left (by norm_num)
  have hNorm : ‖(point : EuclideanR3)‖ = 1 :=
    norm_eq_of_mem_sphere point
  rw [hPointZero, norm_zero] at hNorm
  norm_num at hNorm

/-- Shifted measured stereographic charts cover every point of the actual
throat quotient. -/
theorem exists_shiftedThroatStereographicChart_mem
    (point : EffectiveThroat period hPeriod) :
    ∃ shift : Real, ∃ pole : StandardSphere,
      point ∈ Set.range
        (shiftedThroatInteriorStereographicPhysicalMap
          period hPeriod shift pole) := by
  obtain ⟨anchor, hAnchor⟩ :=
    mappingTorusMk_surjective
      (throatData period hPeriod) point
  let spherePoint : StandardSphere :=
    equatorialTwoSphereHomeomorph anchor.fiber
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
    throatTimeFlow period hPeriod shift
        (mappingTorusMk (throatData period hPeriod)
          ((coverHomeomorphProd
            (throatData period hPeriod)).symm
              (equatorialTwoSphereHomeomorph.symm
                (stereographicInverseSphere pole spatialCoordinate),
                midpoint))) =
      point
  rw [throatTimeFlow_mk]
  calc
    mappingTorusMk (throatData period hPeriod)
        (coverTimeTranslation (throatData period hPeriod) shift
          ((coverHomeomorphProd
            (throatData period hPeriod)).symm
              (equatorialTwoSphereHomeomorph.symm
                (stereographicInverseSphere pole spatialCoordinate),
                midpoint))) =
      mappingTorusMk (throatData period hPeriod) anchor := by
        congr 1
        apply MappingTorusCover.ext
        · change equatorialTwoSphereHomeomorph.symm
            (stereographicInverseSphere pole spatialCoordinate) =
              anchor.fiber
          rw [hSpatialCoordinate]
          exact equatorialTwoSphereHomeomorph.symm_apply_apply anchor.fiber
        · change midpoint + shift = anchor.time
          simp [shift]
    _ = point := hAnchor

/-- Every compact throat subset admits a finite cover by explicit shifted
measured stereographic charts. -/
theorem exists_finite_shiftedThroatStereographicChart_cover
    {support : Set (EffectiveThroat period hPeriod)}
    (hSupport : IsCompact support) :
    ∃ charts : Finset (Real × StandardSphere),
      support ⊆
        ⋃ chart ∈ charts,
          Set.range
            (shiftedThroatInteriorStereographicPhysicalMap
              period hPeriod chart.1 chart.2) := by
  classical
  apply hSupport.elim_finite_subcover
  · intro chart
    exact
      (shiftedThroatInteriorStereographicPhysicalMap_isOpenEmbedding
        period hPeriod chart.1 chart.2).isOpen_range
  · intro point hPoint
    obtain ⟨shift, pole, hChart⟩ :=
      exists_shiftedThroatStereographicChart_mem
        period hPeriod point
    exact Set.mem_iUnion_of_mem (shift, pole) hChart

end
end P0EFTJanusMappingTorusCanonicalThroatLocalVolumeTransport4D
end JanusFormal
