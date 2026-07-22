import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeCoareaClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeMinimalDeckInvariantCutoff4D

/-!
# The global latitude throat has zero physical volume

The exact equatorial coarea formula identifies round `S³` surface measure as the
pushforward of `cos² ν dν dσ₂`.  The equator corresponds, inside the latitude
strip, to the singleton `ν = 0`; hence it has zero surface measure.

The physical Lorentz volume is the pushforward of round `S³` measure times one
fundamental time interval.  The zero set of the descended squared normal
coordinate is therefore null.  This is the almost-everywhere input needed for
the shrinking global cutoff convergence.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLatitudeGlobalThroatNull4D

set_option autoImplicit false
noncomputable section

open scoped ENNReal Manifold ContDiff
open MeasureTheory Set Filter Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMeasureToSphereEquatorialCoarea4D
open P0EFTJanusMappingTorusCanonicalLatitudeCoareaClosure4D
open P0EFTJanusMappingTorusCanonicalLatitudeMinimalCutoffProfile4D
open P0EFTJanusMappingTorusCanonicalLatitudeMinimalDeckInvariantCutoff4D

private abbrev StandardSphere2 := Metric.sphere (0 : EuclideanR3) 1
private abbrev StandardSphere3 := Metric.sphere (0 : EuclideanR4) 1
private abbrev LatitudeAngle := Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)

/-- First Cartesian coordinate on the standard unit three-sphere. -/
def standardSphereFirstCoordinate (point : StandardSphere3) : Real :=
  (EuclideanSpace.equiv (Fin 4) Real point.1) 0

/-- Continuity of the first standard sphere coordinate. -/
theorem standardSphereFirstCoordinate_continuous :
    Continuous standardSphereFirstCoordinate :=
  (continuous_apply (0 : Fin 4)).comp
    ((EuclideanSpace.equiv (Fin 4) Real).continuous.comp continuous_subtype_val)

/-- The standard equator. -/
def standardSphereEquator : Set StandardSphere3 :=
  {point | standardSphereFirstCoordinate point = 0}

/-- The standard equator is closed and measurable. -/
theorem standardSphereEquator_isClosed :
    IsClosed standardSphereEquator := by
  unfold standardSphereEquator
  exact isClosed_eq standardSphereFirstCoordinate_continuous continuous_const

/-- First coordinate of the standard latitude parametrization. -/
@[simp] theorem standardEquatorialLatitude_firstCoordinate
    (parameter : StandardSphere2 × Real) :
    standardSphereFirstCoordinate (standardEquatorialLatitude parameter) =
      Real.sin parameter.2 := by
  rfl

/-- Unweighted latitude source measure before installing the Jacobian density. -/
def standardLatitudeUnweightedMeasure :
    Measure (StandardSphere2 × Real) :=
  (volume : Measure EuclideanR3).toSphere.prod
    (volume.restrict LatitudeAngle)

/-- Inside the supported latitude strip, the preimage of the equator is the
single slice `ν = 0`. -/
theorem standardLatitude_equator_preimage_subset :
    standardEquatorialLatitude ⁻¹' standardSphereEquator ⊆
      ((Set.univ : Set StandardSphere2) ×ˢ ({0} : Set Real)) ∪
        ((Set.univ : Set StandardSphere2) ×ˢ LatitudeAngleᶜ) := by
  intro parameter hParameter
  by_cases hLatitude : parameter.2 ∈ LatitudeAngle
  · left
    have hSin : Real.sin parameter.2 = Real.sin 0 := by
      simpa [standardSphereEquator] using hParameter
    have hParameterIcc : parameter.2 ∈
        Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨hLatitude.1.le, hLatitude.2.le⟩
    have hZeroIcc : (0 : Real) ∈
        Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> nlinarith [Real.pi_pos]
    have hZero : parameter.2 = 0 :=
      Real.injOn_sin hParameterIcc hZeroIcc hSin
    simp [hZero]
  · right
    simp [hLatitude]

/-- The unweighted latitude source gives zero mass to the equator preimage. -/
theorem standardLatitudeUnweightedMeasure_equator_preimage :
    standardLatitudeUnweightedMeasure
        (standardEquatorialLatitude ⁻¹' standardSphereEquator) = 0 := by
  have hSlice : standardLatitudeUnweightedMeasure
      ((Set.univ : Set StandardSphere2) ×ˢ ({0} : Set Real)) = 0 := by
    unfold standardLatitudeUnweightedMeasure
    rw [Measure.prod_prod]
    simp
  have hOutside : standardLatitudeUnweightedMeasure
      ((Set.univ : Set StandardSphere2) ×ˢ LatitudeAngleᶜ) = 0 := by
    unfold standardLatitudeUnweightedMeasure
    rw [Measure.prod_prod]
    simp [LatitudeAngle, Measure.restrict_apply, measurableSet_Ioo]
  apply measure_mono_null standardLatitude_equator_preimage_subset
  exact measure_union_null hSlice hOutside

/-- The weighted latitude source also gives zero mass to the equator preimage. -/
theorem standardLatitudeParameterMeasure_equator_preimage :
    standardLatitudeParameterMeasure
        (standardEquatorialLatitude ⁻¹' standardSphereEquator) = 0 := by
  have hMeasurable : MeasurableSet
      (standardEquatorialLatitude ⁻¹' standardSphereEquator) :=
    (standardSphereEquator_isClosed.measurableSet.preimage
      standardEquatorialLatitude_continuous.measurable)
  unfold standardLatitudeParameterMeasure
  rw [withDensity_apply _ hMeasurable]
  exact setLIntegral_measure_zero _ _
    standardLatitudeUnweightedMeasure_equator_preimage

/-- The equator has zero round `S³` surface measure. -/
theorem standardSphereEquator_measure_zero :
    (volume : Measure EuclideanR4).toSphere standardSphereEquator = 0 := by
  rw [← standardEquatorialLatitude_weighted_map]
  rw [Measure.map_apply standardEquatorialLatitude_continuous.measurable
    standardSphereEquator_isClosed.measurableSet]
  exact standardLatitudeParameterMeasure_equator_preimage

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- Public source measure for the canonical Lorentz fundamental-domain map. -/
def canonicalLorentzFundamentalProductMeasure :
    Measure (StandardSphere3 × Real) :=
  (volume : Measure EuclideanR4).toSphere.prod
    (volume.restrict (canonicalLatitudeTimeInterval period))

/-- The equatorial source cylinder has zero product measure. -/
theorem canonicalLorentzFundamentalProductMeasure_equator :
    canonicalLorentzFundamentalProductMeasure period
      (standardSphereEquator ×ˢ (Set.univ : Set Real)) = 0 := by
  unfold canonicalLorentzFundamentalProductMeasure
  rw [Measure.prod_prod, standardSphereEquator_measure_zero]
  simp

/-- The descended squared normal on the fundamental domain is the square of the
first standard sphere coordinate. -/
theorem canonicalLatitudeQuotientNormalSquare_fundamentalDomain
    (parameter : StandardSphere3 × Real) :
    canonicalLatitudeQuotientNormalSquare period hPeriod
        (canonicalLorentzFundamentalDomainMap period hPeriod parameter) =
      standardSphereFirstCoordinate parameter.1 ^ 2 := by
  unfold canonicalLorentzFundamentalDomainMap
  rw [canonicalLatitudeQuotientNormalSquare_mk]
  rfl

/-- The global cutoff on the fundamental domain is the local profile of the first
standard sphere coordinate. -/
theorem canonicalLatitudeMinimalQuotientCutoff_fundamentalDomain
    (index : Nat) (parameter : StandardSphere3 × Real) :
    canonicalLatitudeMinimalQuotientCutoff period hPeriod index
        (canonicalLorentzFundamentalDomainMap period hPeriod parameter) =
      canonicalLatitudeMinimalCutoffProfile index
        (standardSphereFirstCoordinate parameter.1) := by
  unfold canonicalLorentzFundamentalDomainMap
  rw [canonicalLatitudeMinimalQuotientCutoff_mk]
  rfl

/-- The fundamental-domain preimage of the global throat is the equatorial
cylinder. -/
theorem canonicalLorentzFundamentalDomainMap_preimage_throat :
    canonicalLorentzFundamentalDomainMap period hPeriod ⁻¹'
        canonicalLatitudeGlobalThroatSet period hPeriod =
      standardSphereEquator ×ˢ (Set.univ : Set Real) := by
  ext parameter
  rw [Set.mem_preimage, Set.mem_prod]
  simp only [Set.mem_univ, and_true]
  unfold canonicalLatitudeGlobalThroatSet standardSphereEquator
  change canonicalLatitudeQuotientNormalSquare period hPeriod
      (canonicalLorentzFundamentalDomainMap period hPeriod parameter) = 0 ↔
    standardSphereFirstCoordinate parameter.1 = 0
  rw [canonicalLatitudeQuotientNormalSquare_fundamentalDomain]
  exact sq_eq_zero_iff

/-- The global throat has zero canonical physical Lorentz volume. -/
theorem canonicalLatitudeGlobalThroatSet_measure_zero :
    intrinsicCanonicalLorentzVolumeMeasure period hPeriod
        (canonicalLatitudeGlobalThroatSet period hPeriod) = 0 := by
  rw [intrinsicCanonicalLorentzVolumeMeasure_eq_publicMap]
  rw [Measure.map_apply
    (canonicalLorentzFundamentalDomainMap_continuous period hPeriod).measurable
    (canonicalLatitudeGlobalThroatSet_isClosed
      period hPeriod).measurableSet]
  rw [canonicalLorentzFundamentalDomainMap_preimage_throat]
  exact canonicalLorentzFundamentalProductMeasure_equator period

/-- Almost every physical bulk point lies off the throat. -/
theorem ae_not_mem_canonicalLatitudeGlobalThroatSet :
    ∀ᵐ point ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod,
      point ∉ canonicalLatitudeGlobalThroatSet period hPeriod := by
  rw [ae_iff]
  simpa using canonicalLatitudeGlobalThroatSet_measure_zero period hPeriod

/-- Almost-everywhere pointwise convergence of the global shrinking cutoffs. -/
theorem ae_canonicalLatitudeMinimalQuotientCutoff_tendsto_one :
    ∀ᵐ point ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod,
      Tendsto
        (fun index : Nat =>
          canonicalLatitudeMinimalQuotientCutoff period hPeriod index point)
        atTop (𝓝 1) := by
  filter_upwards
    [ae_not_mem_canonicalLatitudeGlobalThroatSet period hPeriod]
    with point hPoint
  exact canonicalLatitudeMinimalQuotientCutoff_tendsto_one
    period hPeriod point hPoint

/-- Null-throat certificate. -/
theorem canonicalLatitudeGlobalThroatNull_certificate :
    (volume : Measure EuclideanR4).toSphere standardSphereEquator = 0 ∧
      intrinsicCanonicalLorentzVolumeMeasure period hPeriod
          (canonicalLatitudeGlobalThroatSet period hPeriod) = 0 ∧
      (∀ᵐ point ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod,
        Tendsto
          (fun index : Nat =>
            canonicalLatitudeMinimalQuotientCutoff period hPeriod index point)
          atTop (𝓝 1)) :=
  ⟨standardSphereEquator_measure_zero,
    canonicalLatitudeGlobalThroatSet_measure_zero period hPeriod,
    ae_canonicalLatitudeMinimalQuotientCutoff_tendsto_one period hPeriod⟩

end
end P0EFTJanusMappingTorusCanonicalLatitudeGlobalThroatNull4D
end JanusFormal
