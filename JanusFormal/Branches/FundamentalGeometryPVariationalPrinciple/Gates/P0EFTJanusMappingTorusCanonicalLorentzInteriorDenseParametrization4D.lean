import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetCoareaMap4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerDenseParametrizationClosure4D

/-!
# Open fundamental-strip parametrization of the physical Lorentz volume

The canonical Lorentz volume is the pushforward of round `S³` surface measure
times Lebesgue measure on one half-open period.  Replacing that half-open time
interval by its interior removes only one endpoint, hence does not change the
measure.  The resulting source has an open-positive measure because it is a
product of:

* Mathlib's open-positive round sphere measure;
* the pullback of Lebesgue measure to an open interval.

Therefore continuity, measure preservation and source open positivity of the
natural open fundamental-strip parametrization are automatic.  The only
remaining topological statement needed for physical full support is density of
its range in the mapping torus.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLorentzInteriorDenseParametrization4D

set_option autoImplicit false
noncomputable section

open Set Topology MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeGlobalThroatNull4D
open P0EFTJanusMappingTorusCanonicalLatitudeCoareaClosure4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetCoareaMap4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerDenseParametrizationClosure4D

private abbrev StandardSphere3 := Metric.sphere (0 : EuclideanR4) 1

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- Interior of the canonical half-open fundamental time interval. -/
def canonicalLorentzInteriorTime : Set Real :=
  Set.Ioo (min 0 period) (max 0 period)

/-- Round-sphere points together with an interior fundamental time. -/
abbrev CanonicalLorentzInteriorParameter :=
  StandardSphere3 × canonicalLorentzInteriorTime period

/-- Lebesgue measure pulled back to the open fundamental interval. -/
def canonicalLorentzInteriorTimeMeasure :
    Measure (canonicalLorentzInteriorTime period) :=
  (volume : Measure Real).comap Subtype.val

/-- Open fundamental-strip source measure. -/
def canonicalLorentzInteriorMeasure :
    Measure (CanonicalLorentzInteriorParameter period) :=
  (volume : Measure EuclideanR4).toSphere.prod
    (canonicalLorentzInteriorTimeMeasure period)

/-- Inclusion of the open fundamental strip into the public sphere-time source. -/
def canonicalLorentzInteriorFundamentalInclusion
    (parameter : CanonicalLorentzInteriorParameter period) :
    StandardSphere3 × Real :=
  (parameter.1, parameter.2.1)

/-- Physical point represented by an interior fundamental-domain parameter. -/
def canonicalLorentzInteriorPhysicalMap
    (parameter : CanonicalLorentzInteriorParameter period) :
    EffectiveQuotient period hPeriod :=
  canonicalLorentzFundamentalDomainMap period hPeriod
    (canonicalLorentzInteriorFundamentalInclusion period parameter)

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

/-- The pulled-back interval measure is positive on every nonempty open subset
of the open interval. -/
theorem canonicalLorentzInteriorTimeMeasure_isOpenPosMeasure :
    (canonicalLorentzInteriorTimeMeasure period).IsOpenPosMeasure := by
  unfold canonicalLorentzInteriorTimeMeasure
  letI : (volume : Measure Real).IsOpenPosMeasure := inferInstance
  exact Measure.IsOpenPosMeasure.comap (volume : Measure Real)
    isOpen_Ioo.isOpenEmbedding_subtypeVal

/-- The whole open fundamental-strip source measure is open-positive. -/
theorem canonicalLorentzInteriorMeasure_isOpenPosMeasure :
    (canonicalLorentzInteriorMeasure period).IsOpenPosMeasure := by
  letI : (canonicalLorentzInteriorTimeMeasure period).IsOpenPosMeasure :=
    canonicalLorentzInteriorTimeMeasure_isOpenPosMeasure period
  unfold canonicalLorentzInteriorMeasure
  infer_instance

/-- The interior time inclusion sends the pulled-back measure to the same
half-open restricted Lebesgue measure used in the physical volume definition. -/
theorem canonicalLorentzInteriorTimeInclusion_measurePreserving :
    MeasurePreserving
      (Subtype.val : canonicalLorentzInteriorTime period → Real)
      (canonicalLorentzInteriorTimeMeasure period)
      (volume.restrict (canonicalLatitudeTimeInterval period)) := by
  refine ⟨measurable_subtype_coe, ?_⟩
  unfold canonicalLorentzInteriorTimeMeasure canonicalLorentzInteriorTime
    canonicalLatitudeTimeInterval
  rw [map_comap_subtype_coe measurableSet_Ioo]
  exact MeasureTheory.restrict_Ioo_eq_restrict_Ioc

/-- Inclusion of the open strip preserves the full sphere-time fundamental
product measure. -/
theorem canonicalLorentzInteriorFundamentalInclusion_measurePreserving :
    MeasurePreserving
      (canonicalLorentzInteriorFundamentalInclusion period)
      (canonicalLorentzInteriorMeasure period)
      (canonicalLorentzFundamentalProductMeasure period) := by
  change MeasurePreserving
    (Prod.map id
      (Subtype.val : canonicalLorentzInteriorTime period → Real))
    ((volume : Measure EuclideanR4).toSphere.prod
      (canonicalLorentzInteriorTimeMeasure period))
    ((volume : Measure EuclideanR4).toSphere.prod
      (volume.restrict (canonicalLatitudeTimeInterval period)))
  exact MeasurePreserving.prod
    (MeasurePreserving.id ((volume : Measure EuclideanR4).toSphere))
    (canonicalLorentzInteriorTimeInclusion_measurePreserving period)

/-- Continuity of the open fundamental-strip inclusion. -/
theorem canonicalLorentzInteriorFundamentalInclusion_continuous :
    Continuous (canonicalLorentzInteriorFundamentalInclusion period) :=
  continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)

/-- Continuity of the physical open-strip parametrization. -/
theorem canonicalLorentzInteriorPhysicalMap_continuous :
    Continuous (canonicalLorentzInteriorPhysicalMap period hPeriod) :=
  (canonicalLorentzFundamentalDomainMap_continuous period hPeriod).comp
    (canonicalLorentzInteriorFundamentalInclusion_continuous period)

/-- Exact preservation of the physical Lorentz volume. -/
theorem canonicalLorentzInteriorPhysicalMap_measurePreserving :
    MeasurePreserving
      (canonicalLorentzInteriorPhysicalMap period hPeriod)
      (canonicalLorentzInteriorMeasure period)
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  (canonicalLorentzFundamentalDomainMap_measurePreserving period hPeriod).comp
    (canonicalLorentzInteriorFundamentalInclusion_measurePreserving period)

/-- The sole remaining topological datum for this concrete full-support route:
the open fundamental strip has dense image in the mapping torus. -/
structure CanonicalLorentzInteriorDenseRangeData where
  denseRange : DenseRange
    (canonicalLorentzInteriorPhysicalMap period hPeriod)

namespace CanonicalLorentzInteriorDenseRangeData

/-- Conversion to the general dense-parametrization package used by the faithful
Euler construction. -/
def toEulerDenseParametrizationData
    (data : CanonicalLorentzInteriorDenseRangeData period hPeriod) :
    CanonicalPhysicalScalarEulerDenseParametrizationData
      period hPeriod
      (CanonicalLorentzInteriorParameter period)
      (canonicalLorentzInteriorMeasure period) where
  sourceOpenPositive :=
    canonicalLorentzInteriorMeasure_isOpenPosMeasure period
  parameterization := canonicalLorentzInteriorPhysicalMap period hPeriod
  continuous := canonicalLorentzInteriorPhysicalMap_continuous period hPeriod
  denseRange := data.denseRange
  measurePreserving :=
    canonicalLorentzInteriorPhysicalMap_measurePreserving period hPeriod

/-- Interior-parametrization certificate. -/
theorem certificate
    (data : CanonicalLorentzInteriorDenseRangeData period hPeriod) :
    (canonicalLorentzInteriorMeasure period).IsOpenPosMeasure ∧
      MeasurePreserving
        (canonicalLorentzInteriorPhysicalMap period hPeriod)
        (canonicalLorentzInteriorMeasure period)
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) ∧
      DenseRange (canonicalLorentzInteriorPhysicalMap period hPeriod) :=
  ⟨canonicalLorentzInteriorMeasure_isOpenPosMeasure period,
    canonicalLorentzInteriorPhysicalMap_measurePreserving period hPeriod,
    data.denseRange⟩

end CanonicalLorentzInteriorDenseRangeData

end
end P0EFTJanusMappingTorusCanonicalLorentzInteriorDenseParametrization4D
end JanusFormal
