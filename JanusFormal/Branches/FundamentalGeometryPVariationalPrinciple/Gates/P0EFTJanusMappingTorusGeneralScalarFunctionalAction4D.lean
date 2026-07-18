import Mathlib.MeasureTheory.Integral.Bochner.Basic
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusCompactQuotient
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D

/-!
# Regular general-metric scalar functional space on D8

This gate isolates explicit smooth regularity data for a general Lorentz
metric: its sharp map, a varying tangent frame, and the metric volume in that
frame.  Holonomic scalar covectors and their sharp contractions carry matching
smooth representatives.  These primitive certificates imply smoothness and
finite-measure integrability of the previously defined intrinsic density.
The integrated scalar action and its exact affine variation are then derived.

No diffeomorphism action on this functional space is assumed.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

open scoped Manifold ContDiff
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D

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

private abbrev TangentFiber (point : EffectiveQuotient period hPeriod) :=
  TangentSpace coverModelWithCorners point

private abbrev CotangentFiber (point : EffectiveQuotient period hPeriod) :=
  TangentFiber period hPeriod point →L[Real] Real

private abbrev CotangentModel := CoverCoordinates →L[Real] Real
private abbrev SharpModel := CotangentModel →L[Real] CoverCoordinates

/-- Smooth tangent vector fields. -/
abbrev SmoothTangentField :=
  ContMDiffSection coverModelWithCorners CoverCoordinates ∞
    (TangentFiber period hPeriod)

/-- Smooth cotangent fields. -/
abbrev SmoothCotangentField :=
  ContMDiffSection coverModelWithCorners CotangentModel ∞
    (CotangentFiber period hPeriod)

/-- Smooth families of sharp maps. -/
abbrev SmoothSharpField :=
  ContMDiffSection coverModelWithCorners SharpModel ∞
    (fun point => CotangentFiber period hPeriod point →L[Real]
      TangentFiber period hPeriod point)

private def coefficientBasis (index : Fin 4) : Fin 4 → Real :=
  fun j => if j = index then 1 else 0

/-- A regular general Lorentz metric.  Every regularity witness is tied by an
equality to the underlying intrinsic metric; none is an action or invariance
hypothesis. -/
structure RegularGeneralLorentzMetric where
  metric : SmoothGeneralLorentzMetric period hPeriod
  sharp : SmoothSharpField period hPeriod
  sharp_eq : ∀ point,
    sharp point = inverseMetricSharp period hPeriod metric point
  frame : Fin 4 → SmoothTangentField period hPeriod
  frameEquiv : ∀ point, (Fin 4 → Real) ≃L[Real]
    TangentFiber period hPeriod point
  frame_eq : ∀ point index,
    frame index point = frameEquiv point (coefficientBasis index)
  volume : SmoothScalarField period hPeriod
  volume_eq : ∀ point,
    volume point = metricVolumeDensity period hPeriod metric point
      (fun index => frame index point)

/-- A smooth scalar together with a smooth representative of its genuine
manifold differential. -/
structure RegularHolonomicScalar where
  field : SmoothScalarField period hPeriod
  differential : SmoothCotangentField period hPeriod
  differential_eq : ∀ point,
    differential point = scalarDifferential period hPeriod field point

/-- Regularity data needed for a scalar line `field + ε variation` coupled to
one fixed regular metric.  The four smooth contractions are primitive
pairings of the certified sharp and certified holonomic covectors. -/
structure RegularScalarVariation
    (metric : RegularGeneralLorentzMetric period hPeriod) where
  field : RegularHolonomicScalar period hPeriod
  variation : RegularHolonomicScalar period hPeriod
  fieldContraction : SmoothScalarField period hPeriod
  variationContraction : SmoothScalarField period hPeriod
  variationFieldContraction : SmoothScalarField period hPeriod
  fieldVariationContraction : SmoothScalarField period hPeriod
  fieldContraction_eq : ∀ point,
    fieldContraction point =
      field.differential point (metric.sharp point (field.differential point))
  variationContraction_eq : ∀ point,
    variationContraction point = variation.differential point
      (metric.sharp point (variation.differential point))
  variationFieldContraction_eq : ∀ point,
    variationFieldContraction point = variation.differential point
      (metric.sharp point (field.differential point))
  fieldVariationContraction_eq : ∀ point,
    fieldVariationContraction point = field.differential point
      (metric.sharp point (variation.differential point))

/-- Smooth representative of the intrinsic base density. -/
def regularDensityField
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : RegularScalarVariation period hPeriod metric) :
    SmoothScalarField period hPeriod where
  toFun := fun point => metric.volume point *
    (1 / 2 * data.fieldContraction point -
      1 / 2 * massSquared * (data.field.field point) ^ 2)
  contMDiff_toFun := metric.volume.contMDiff_toFun.mul
    ((contMDiff_const.mul data.fieldContraction.contMDiff_toFun).sub
      ((contMDiff_const.mul contMDiff_const).mul
        (data.field.field.contMDiff_toFun.pow 2)))

/-- Smooth representative of the pointwise first variation. -/
def regularFirstVariationField
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : RegularScalarVariation period hPeriod metric) :
    SmoothScalarField period hPeriod where
  toFun := fun point => metric.volume point *
    (1 / 2 * (data.variationFieldContraction point +
        data.fieldVariationContraction point) -
      massSquared * data.field.field point * data.variation.field point)
  contMDiff_toFun := metric.volume.contMDiff_toFun.mul
    ((contMDiff_const.mul
      (data.variationFieldContraction.contMDiff_toFun.add
        data.fieldVariationContraction.contMDiff_toFun)).sub
      ((contMDiff_const.mul data.field.field.contMDiff_toFun).mul
        data.variation.field.contMDiff_toFun))

/-- Smooth representative of the quadratic remainder. -/
def regularQuadraticRemainderField
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : RegularScalarVariation period hPeriod metric) :
    SmoothScalarField period hPeriod where
  toFun := fun point => metric.volume point *
    (1 / 2 * data.variationContraction point -
      1 / 2 * massSquared * (data.variation.field point) ^ 2)
  contMDiff_toFun := metric.volume.contMDiff_toFun.mul
    ((contMDiff_const.mul data.variationContraction.contMDiff_toFun).sub
      ((contMDiff_const.mul contMDiff_const).mul
        (data.variation.field.contMDiff_toFun.pow 2)))

@[simp]
theorem regularDensityField_eq
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : RegularScalarVariation period hPeriod metric)
    (point : EffectiveQuotient period hPeriod) :
    regularDensityField period hPeriod metric massSquared data point =
      holonomicScalarDensity period hPeriod metric.metric massSquared
        data.field.field point (fun index => metric.frame index point) := by
  change metric.volume point *
      (1 / 2 * data.fieldContraction point -
        1 / 2 * massSquared * (data.field.field point) ^ 2) =
    metricVolumeDensity period hPeriod metric.metric point
        (fun index => metric.frame index point) *
      (1 / 2 * inverseMetricContraction period hPeriod metric.metric point
          (scalarDifferential period hPeriod data.field.field point)
          (scalarDifferential period hPeriod data.field.field point) -
        1 / 2 * massSquared * (data.field.field point) ^ 2)
  rw [metric.volume_eq point,
    data.fieldContraction_eq point, data.field.differential_eq point,
    metric.sharp_eq point]
  rfl

@[simp]
theorem regularFirstVariationField_eq
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : RegularScalarVariation period hPeriod metric)
    (point : EffectiveQuotient period hPeriod) :
    regularFirstVariationField period hPeriod metric massSquared data point =
      holonomicScalarDensityFirstVariation period hPeriod metric.metric
        massSquared data.field.field data.variation.field point
        (fun index => metric.frame index point) := by
  change metric.volume point *
      (1 / 2 * (data.variationFieldContraction point +
          data.fieldVariationContraction point) -
        massSquared * data.field.field point * data.variation.field point) =
    metricVolumeDensity period hPeriod metric.metric point
        (fun index => metric.frame index point) *
      (1 / 2 *
          (inverseMetricContraction period hPeriod metric.metric point
              (scalarDifferential period hPeriod data.variation.field point)
              (scalarDifferential period hPeriod data.field.field point) +
            inverseMetricContraction period hPeriod metric.metric point
              (scalarDifferential period hPeriod data.field.field point)
              (scalarDifferential period hPeriod data.variation.field point)) -
        massSquared * data.field.field point * data.variation.field point)
  rw [metric.volume_eq point, data.variationFieldContraction_eq point,
    data.fieldVariationContraction_eq point,
    data.field.differential_eq point, data.variation.differential_eq point,
    metric.sharp_eq point]
  rfl

@[simp]
theorem regularQuadraticRemainderField_eq
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : RegularScalarVariation period hPeriod metric)
    (point : EffectiveQuotient period hPeriod) :
    regularQuadraticRemainderField period hPeriod metric massSquared data point =
      holonomicScalarDensityQuadraticRemainder period hPeriod metric.metric
        massSquared data.variation.field point
        (fun index => metric.frame index point) := by
  change metric.volume point *
      (1 / 2 * data.variationContraction point -
        1 / 2 * massSquared * (data.variation.field point) ^ 2) =
    metricVolumeDensity period hPeriod metric.metric point
        (fun index => metric.frame index point) *
      (1 / 2 * inverseMetricContraction period hPeriod metric.metric point
          (scalarDifferential period hPeriod data.variation.field point)
          (scalarDifferential period hPeriod data.variation.field point) -
        1 / 2 * massSquared * (data.variation.field point) ^ 2)
  rw [metric.volume_eq point,
    data.variationContraction_eq point, data.variation.differential_eq point,
    metric.sharp_eq point]
  rfl

/-- Smoothness of the actual intrinsic density follows from the primitive
regularity certificates. -/
theorem holonomicScalarDensity_contMDiff
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : RegularScalarVariation period hPeriod metric) :
    ContMDiff coverModelWithCorners 𝓘(Real, Real) ∞
      (fun point => holonomicScalarDensity period hPeriod metric.metric
        massSquared data.field.field point
        (fun index => metric.frame index point)) := by
  rw [show (fun point => holonomicScalarDensity period hPeriod metric.metric
      massSquared data.field.field point
      (fun index => metric.frame index point)) =
    (regularDensityField period hPeriod metric massSquared data).toFun by
      funext point
      exact (regularDensityField_eq period hPeriod metric massSquared data point).symm]
  exact (regularDensityField period hPeriod metric massSquared data).contMDiff_toFun

theorem holonomicScalarFirstVariation_contMDiff
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : RegularScalarVariation period hPeriod metric) :
    ContMDiff coverModelWithCorners 𝓘(Real, Real) ∞
      (fun point => holonomicScalarDensityFirstVariation period hPeriod
        metric.metric massSquared data.field.field data.variation.field point
        (fun index => metric.frame index point)) := by
  rw [show (fun point => holonomicScalarDensityFirstVariation period hPeriod
      metric.metric massSquared data.field.field data.variation.field point
      (fun index => metric.frame index point)) =
    (regularFirstVariationField period hPeriod metric massSquared data).toFun by
      funext point
      exact (regularFirstVariationField_eq period hPeriod metric massSquared
        data point).symm]
  exact (regularFirstVariationField period hPeriod metric massSquared data).contMDiff_toFun

theorem holonomicScalarQuadraticRemainder_contMDiff
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : RegularScalarVariation period hPeriod metric) :
    ContMDiff coverModelWithCorners 𝓘(Real, Real) ∞
      (fun point => holonomicScalarDensityQuadraticRemainder period hPeriod
        metric.metric massSquared data.variation.field point
        (fun index => metric.frame index point)) := by
  rw [show (fun point => holonomicScalarDensityQuadraticRemainder period hPeriod
      metric.metric massSquared data.variation.field point
      (fun index => metric.frame index point)) =
    (regularQuadraticRemainderField period hPeriod metric massSquared data).toFun by
      funext point
      exact (regularQuadraticRemainderField_eq period hPeriod metric massSquared
        data point).symm]
  exact (regularQuadraticRemainderField period hPeriod metric massSquared
    data).contMDiff_toFun

theorem holonomicScalarDensity_continuous
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : RegularScalarVariation period hPeriod metric) :
    Continuous (fun point => holonomicScalarDensity period hPeriod metric.metric
      massSquared data.field.field point
      (fun index => metric.frame index point)) :=
  (holonomicScalarDensity_contMDiff period hPeriod metric massSquared data).continuous

theorem holonomicScalarFirstVariation_continuous
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : RegularScalarVariation period hPeriod metric) :
    Continuous (fun point => holonomicScalarDensityFirstVariation period hPeriod
      metric.metric massSquared data.field.field data.variation.field point
      (fun index => metric.frame index point)) :=
  (holonomicScalarFirstVariation_contMDiff period hPeriod metric massSquared
    data).continuous

theorem holonomicScalarQuadraticRemainder_continuous
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : RegularScalarVariation period hPeriod metric) :
    Continuous (fun point => holonomicScalarDensityQuadraticRemainder period hPeriod
      metric.metric massSquared data.variation.field point
      (fun index => metric.frame index point)) :=
  (holonomicScalarQuadraticRemainder_contMDiff period hPeriod metric massSquared
    data).continuous

/-- Compactness of D8 and finiteness of the Borel measure make the intrinsic
density integrable. -/
theorem holonomicScalarDensity_integrable
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : RegularScalarVariation period hPeriod metric)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure] :
    Integrable (fun point => holonomicScalarDensity period hPeriod metric.metric
      massSquared data.field.field point
      (fun index => metric.frame index point)) measure := by
  exact (holonomicScalarDensity_continuous period hPeriod metric massSquared
    data).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

theorem holonomicScalarFirstVariation_integrable
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : RegularScalarVariation period hPeriod metric)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure] :
    Integrable (fun point => holonomicScalarDensityFirstVariation period hPeriod
      metric.metric massSquared data.field.field data.variation.field point
      (fun index => metric.frame index point)) measure := by
  exact (holonomicScalarFirstVariation_continuous period hPeriod metric
    massSquared data).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

theorem holonomicScalarQuadraticRemainder_integrable
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : RegularScalarVariation period hPeriod metric)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure] :
    Integrable (fun point => holonomicScalarDensityQuadraticRemainder period hPeriod
      metric.metric massSquared data.variation.field point
      (fun index => metric.frame index point)) measure := by
  exact (holonomicScalarQuadraticRemainder_continuous period hPeriod metric
    massSquared data).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- Integrated action for a chosen finite Borel measure. -/
def generalHolonomicScalarAction
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod)) : Real :=
  ∫ point, holonomicScalarDensity period hPeriod metric.metric massSquared field
    point (fun index => metric.frame index point) ∂measure

/-- Integrated scalar first variation. -/
def generalHolonomicScalarFirstVariation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (field variation : SmoothScalarField period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod)) : Real :=
  ∫ point, holonomicScalarDensityFirstVariation period hPeriod metric.metric
    massSquared field variation point (fun index => metric.frame index point)
      ∂measure

def generalHolonomicScalarQuadraticRemainder
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (variation : SmoothScalarField period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod)) : Real :=
  ∫ point, holonomicScalarDensityQuadraticRemainder period hPeriod metric.metric
    massSquared variation point (fun index => metric.frame index point) ∂measure

/-- Exact integrated quadratic expansion, obtained from the already proved
pointwise holonomic expansion and automatic integrability. -/
theorem generalHolonomicScalarAction_line_expansion
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : RegularScalarVariation period hPeriod metric)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (epsilon : Real) :
    generalHolonomicScalarAction period hPeriod metric massSquared
        (scalarFieldLine period hPeriod data.field.field data.variation.field epsilon)
        measure =
      generalHolonomicScalarAction period hPeriod metric massSquared
          data.field.field measure +
        epsilon * generalHolonomicScalarFirstVariation period hPeriod metric
          massSquared data.field.field data.variation.field measure +
        epsilon ^ 2 * generalHolonomicScalarQuadraticRemainder period hPeriod
          metric massSquared data.variation.field measure := by
  unfold generalHolonomicScalarAction generalHolonomicScalarFirstVariation
    generalHolonomicScalarQuadraticRemainder
  simp_rw [holonomicScalarDensity_line_expansion period hPeriod metric.metric
    massSquared data.field.field data.variation.field]
  have hBase := holonomicScalarDensity_integrable period hPeriod metric
    massSquared data measure
  have hFirst := (holonomicScalarFirstVariation_integrable period hPeriod metric
    massSquared data measure).const_mul epsilon
  have hQuadratic :=
    (holonomicScalarQuadraticRemainder_integrable period hPeriod metric
      massSquared data measure).const_mul (epsilon ^ 2)
  calc
    ∫ point,
          holonomicScalarDensity period hPeriod metric.metric massSquared
              data.field.field point (fun index => metric.frame index point) +
            epsilon * holonomicScalarDensityFirstVariation period hPeriod
              metric.metric massSquared data.field.field data.variation.field
              point (fun index => metric.frame index point) +
            epsilon ^ 2 * holonomicScalarDensityQuadraticRemainder period hPeriod
              metric.metric massSquared data.variation.field point
              (fun index => metric.frame index point) ∂measure =
        ∫ point,
          holonomicScalarDensity period hPeriod metric.metric massSquared
              data.field.field point (fun index => metric.frame index point) +
            (epsilon * holonomicScalarDensityFirstVariation period hPeriod
                metric.metric massSquared data.field.field data.variation.field
                point (fun index => metric.frame index point) +
              epsilon ^ 2 * holonomicScalarDensityQuadraticRemainder period hPeriod
                metric.metric massSquared data.variation.field point
                (fun index => metric.frame index point)) ∂measure := by
          congr 1
          funext point
          ring
    _ = (∫ point, holonomicScalarDensity period hPeriod metric.metric massSquared
          data.field.field point (fun index => metric.frame index point) ∂measure) +
        ∫ point,
          epsilon * holonomicScalarDensityFirstVariation period hPeriod
              metric.metric massSquared data.field.field data.variation.field
              point (fun index => metric.frame index point) +
            epsilon ^ 2 * holonomicScalarDensityQuadraticRemainder period hPeriod
              metric.metric massSquared data.variation.field point
              (fun index => metric.frame index point) ∂measure :=
      integral_add hBase (hFirst.add hQuadratic)
    _ = _ := by
      rw [integral_add hFirst hQuadratic, integral_const_mul, integral_const_mul]
      ring

/-- The integrated action has the integrated pointwise first variation as its
derivative along every certified regular scalar line. -/
theorem generalHolonomicScalarAction_line_hasDerivAt
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : RegularScalarVariation period hPeriod metric)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure] :
    HasDerivAt
      (fun epsilon : Real => generalHolonomicScalarAction period hPeriod metric
        massSquared
        (scalarFieldLine period hPeriod data.field.field data.variation.field epsilon)
        measure)
      (generalHolonomicScalarFirstVariation period hPeriod metric massSquared
        data.field.field data.variation.field measure) 0 := by
  rw [show (fun epsilon : Real => generalHolonomicScalarAction period hPeriod
      metric massSquared
      (scalarFieldLine period hPeriod data.field.field data.variation.field epsilon)
      measure) =
    (fun epsilon : Real =>
      generalHolonomicScalarAction period hPeriod metric massSquared
          data.field.field measure +
        epsilon * generalHolonomicScalarFirstVariation period hPeriod metric
          massSquared data.field.field data.variation.field measure +
        epsilon ^ 2 * generalHolonomicScalarQuadraticRemainder period hPeriod
          metric massSquared data.variation.field measure) by
      funext epsilon
      exact generalHolonomicScalarAction_line_expansion period hPeriod metric
        massSquared data measure epsilon]
  have hLinear := ((hasDerivAt_id (𝕜 := Real) 0).mul_const
    (generalHolonomicScalarFirstVariation period hPeriod metric massSquared
      data.field.field data.variation.field measure)).const_add
    (generalHolonomicScalarAction period hPeriod metric massSquared
      data.field.field measure)
  have hQuadratic := ((hasDerivAt_id (𝕜 := Real) 0).pow 2).mul_const
    (generalHolonomicScalarQuadraticRemainder period hPeriod metric massSquared
      data.variation.field measure)
  change HasDerivAt
    ((fun epsilon : Real =>
        generalHolonomicScalarAction period hPeriod metric massSquared
            data.field.field measure +
          epsilon * generalHolonomicScalarFirstVariation period hPeriod metric
            massSquared data.field.field data.variation.field measure) +
      (fun epsilon : Real => epsilon ^ 2 *
        generalHolonomicScalarQuadraticRemainder period hPeriod metric
          massSquared data.variation.field measure)) _ 0
  exact (hLinear.add hQuadratic).congr_deriv (by norm_num)

/-- Constant scalars provide an unconditional regular scalar branch over any
regular general metric. -/
private def constantScalarField (value : Real) :
    SmoothScalarField period hPeriod where
  toFun := fun _ => value
  contMDiff_toFun := contMDiff_const

def constantRegularHolonomicScalar (value : Real) :
    RegularHolonomicScalar period hPeriod where
  field := constantScalarField period hPeriod value
  differential := 0
  differential_eq := by
    intro point
    apply ContinuousLinearMap.ext
    intro tangent
    simp only [scalarDifferential, constantScalarField, mfderiv_const]
    change (0 : Real) = 0
    rfl

def constantRegularScalarVariation
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (fieldValue variationValue : Real) :
    RegularScalarVariation period hPeriod metric where
  field := constantRegularHolonomicScalar period hPeriod fieldValue
  variation := constantRegularHolonomicScalar period hPeriod variationValue
  fieldContraction := constantScalarField period hPeriod 0
  variationContraction := constantScalarField period hPeriod 0
  variationFieldContraction := constantScalarField period hPeriod 0
  fieldVariationContraction := constantScalarField period hPeriod 0
  fieldContraction_eq := by intro point; simp [constantRegularHolonomicScalar,
    constantScalarField]
  variationContraction_eq := by intro point; simp [constantRegularHolonomicScalar,
    constantScalarField]
  variationFieldContraction_eq := by intro point; simp [constantRegularHolonomicScalar,
    constantScalarField]
  fieldVariationContraction_eq := by intro point; simp [constantRegularHolonomicScalar,
    constantScalarField]

theorem regularScalarVariation_nonempty
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    Nonempty (RegularScalarVariation period hPeriod metric) :=
  ⟨constantRegularScalarVariation period hPeriod metric 0 0⟩

end

end P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
end JanusFormal
