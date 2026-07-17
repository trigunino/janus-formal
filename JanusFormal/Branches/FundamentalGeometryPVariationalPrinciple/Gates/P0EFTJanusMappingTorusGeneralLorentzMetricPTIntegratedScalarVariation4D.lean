import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricPTIntegratedScalarAction4D

/-!
# Integrated scalar variation at fixed general Lorentz metric

For an affine scalar-field line, the existing holonomic density has an exact
quadratic expansion.  This gate integrates that identity against the
canonical quotient Lorentz measure under the three explicit integrability
hypotheses actually used, and identifies the derivative of the action.
The metric and ordered tangent-vector family remain fixed along the line.

The first variation is also covariant under coherent analytic PT pullback.
No metric variation or curved Euler equation is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGeneralLorentzMetricPTIntegratedScalarVariation4D

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusPTInvolution
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothPTInvolution
open P0EFTJanusMappingTorusDiagonalDiffeomorphismAction4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricPTScalarAction4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusD8NonabelianGhostSmoothSpacetimeBVPTCovariance4D
open P0EFTJanusMappingTorusGeneralLorentzMetricPTIntegratedScalarAction4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- Pointwise first variation in a supplied ordered tangent-vector family. -/
def generalLorentzHolonomicScalarFirstVariation
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (field variation : SmoothScalarField period hPeriod)
    (frame : OrderedTangentVectorFamily period hPeriod)
    (point : EffectiveQuotient period hPeriod) : Real :=
  holonomicScalarDensityFirstVariation period hPeriod metric massSquared
    field variation point (frame point)

/-- Pointwise quadratic remainder in a supplied ordered tangent-vector
family. -/
def generalLorentzHolonomicScalarQuadraticRemainder
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (variation : SmoothScalarField period hPeriod)
    (frame : OrderedTangentVectorFamily period hPeriod)
    (point : EffectiveQuotient period hPeriod) : Real :=
  holonomicScalarDensityQuadraticRemainder period hPeriod metric massSquared
    variation point (frame point)

/-- Exact pointwise quadratic expansion at fixed metric and fixed tangent
family. -/
theorem generalLorentzHolonomicScalarDensity_line_expansion
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (field variation : SmoothScalarField period hPeriod)
    (frame : OrderedTangentVectorFamily period hPeriod)
    (epsilon : Real)
    (point : EffectiveQuotient period hPeriod) :
    generalLorentzHolonomicScalarDensity period hPeriod metric massSquared
        (scalarFieldLine period hPeriod field variation epsilon) frame point =
      generalLorentzHolonomicScalarDensity period hPeriod metric massSquared
          field frame point +
        epsilon * generalLorentzHolonomicScalarFirstVariation period hPeriod
          metric massSquared field variation frame point +
        epsilon ^ 2 *
          generalLorentzHolonomicScalarQuadraticRemainder period hPeriod
            metric massSquared variation frame point := by
  exact holonomicScalarDensity_line_expansion period hPeriod metric massSquared
    field variation epsilon point (frame point)

/-- The pointwise first coefficient is the derivative along the affine scalar
line. -/
theorem generalLorentzHolonomicScalarDensity_line_hasDerivAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (field variation : SmoothScalarField period hPeriod)
    (frame : OrderedTangentVectorFamily period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    HasDerivAt
      (fun epsilon : Real =>
        generalLorentzHolonomicScalarDensity period hPeriod metric massSquared
          (scalarFieldLine period hPeriod field variation epsilon) frame point)
      (generalLorentzHolonomicScalarFirstVariation period hPeriod metric
        massSquared field variation frame point) 0 := by
  rw [show (fun epsilon : Real =>
      generalLorentzHolonomicScalarDensity period hPeriod metric massSquared
        (scalarFieldLine period hPeriod field variation epsilon) frame point) =
    (fun epsilon : Real =>
      generalLorentzHolonomicScalarDensity period hPeriod metric massSquared
          field frame point +
        epsilon * generalLorentzHolonomicScalarFirstVariation period hPeriod
          metric massSquared field variation frame point +
        epsilon ^ 2 *
          generalLorentzHolonomicScalarQuadraticRemainder period hPeriod
            metric massSquared variation frame point) by
      funext epsilon
      exact generalLorentzHolonomicScalarDensity_line_expansion period hPeriod
        metric massSquared field variation frame epsilon point]
  have hLinear := ((hasDerivAt_id' (x := (0 : Real))).mul_const
    (generalLorentzHolonomicScalarFirstVariation period hPeriod metric
      massSquared field variation frame point)).const_add
    (generalLorentzHolonomicScalarDensity period hPeriod metric massSquared
      field frame point)
  have hQuadratic := ((hasDerivAt_id' (x := (0 : Real))).pow 2).mul_const
    (generalLorentzHolonomicScalarQuadraticRemainder period hPeriod metric
      massSquared variation frame point)
  exact (hLinear.add hQuadratic).congr_deriv (by norm_num)

/-- Integrated first variation against the canonical quotient Lorentz
measure. -/
def canonicalGeneralLorentzHolonomicScalarFirstVariation
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (field variation : SmoothScalarField period hPeriod)
    (frame : OrderedTangentVectorFamily period hPeriod) : Real :=
  ∫ point,
      generalLorentzHolonomicScalarFirstVariation period hPeriod metric
        massSquared field variation frame point
    ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)

/-- Integrated quadratic remainder against the canonical quotient Lorentz
measure. -/
def canonicalGeneralLorentzHolonomicScalarQuadraticRemainder
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (variation : SmoothScalarField period hPeriod)
    (frame : OrderedTangentVectorFamily period hPeriod) : Real :=
  ∫ point,
      generalLorentzHolonomicScalarQuadraticRemainder period hPeriod metric
        massSquared variation frame point
    ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)

/-- Minimal reusable integrability contract for the fixed-metric scalar
variation.  It contains exactly the base, linear, and quadratic terms split
by the integral proof. -/
structure CanonicalGeneralLorentzScalarVariationIntegrable
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (field variation : SmoothScalarField period hPeriod)
    (frame : OrderedTangentVectorFamily period hPeriod) : Prop where
  base : Integrable
    (generalLorentzHolonomicScalarDensity period hPeriod metric massSquared
      field frame)
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
  first : Integrable
    (generalLorentzHolonomicScalarFirstVariation period hPeriod metric
      massSquared field variation frame)
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
  quadratic : Integrable
    (generalLorentzHolonomicScalarQuadraticRemainder period hPeriod metric
      massSquared variation frame)
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)

/-- The explicit three-term contract makes every scalar line integrable. -/
theorem generalLorentzHolonomicScalarDensity_line_integrable
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (field variation : SmoothScalarField period hPeriod)
    (frame : OrderedTangentVectorFamily period hPeriod)
    (hIntegrable : CanonicalGeneralLorentzScalarVariationIntegrable period
      hPeriod metric massSquared field variation frame)
    (epsilon : Real) :
    Integrable
      (generalLorentzHolonomicScalarDensity period hPeriod metric massSquared
        (scalarFieldLine period hPeriod field variation epsilon) frame)
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  rw [show generalLorentzHolonomicScalarDensity period hPeriod metric
      massSquared (scalarFieldLine period hPeriod field variation epsilon)
      frame =
    fun point =>
      generalLorentzHolonomicScalarDensity period hPeriod metric massSquared
          field frame point +
        epsilon * generalLorentzHolonomicScalarFirstVariation period hPeriod
          metric massSquared field variation frame point +
        epsilon ^ 2 *
          generalLorentzHolonomicScalarQuadraticRemainder period hPeriod
            metric massSquared variation frame point by
    funext point
    exact generalLorentzHolonomicScalarDensity_line_expansion period hPeriod
      metric massSquared field variation frame epsilon point]
  exact (hIntegrable.base.add (hIntegrable.first.const_mul epsilon)).add
    (hIntegrable.quadratic.const_mul (epsilon ^ 2))

/-- Exact integrated quadratic expansion under the explicit minimal
integrability contract. -/
theorem canonicalGeneralLorentzHolonomicScalarAction_line_expansion
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (field variation : SmoothScalarField period hPeriod)
    (frame : OrderedTangentVectorFamily period hPeriod)
    (hIntegrable : CanonicalGeneralLorentzScalarVariationIntegrable period
      hPeriod metric massSquared field variation frame)
    (epsilon : Real) :
    canonicalGeneralLorentzHolonomicScalarAction period hPeriod metric
        massSquared (scalarFieldLine period hPeriod field variation epsilon)
        frame =
      canonicalGeneralLorentzHolonomicScalarAction period hPeriod metric
          massSquared field frame +
        epsilon * canonicalGeneralLorentzHolonomicScalarFirstVariation period
          hPeriod metric massSquared field variation frame +
        epsilon ^ 2 *
          canonicalGeneralLorentzHolonomicScalarQuadraticRemainder period
            hPeriod metric massSquared variation frame := by
  unfold canonicalGeneralLorentzHolonomicScalarAction
    canonicalGeneralLorentzHolonomicScalarFirstVariation
    canonicalGeneralLorentzHolonomicScalarQuadraticRemainder
  simp_rw [generalLorentzHolonomicScalarDensity_line_expansion period hPeriod
    metric massSquared field variation frame]
  have hFirst := hIntegrable.first.const_mul epsilon
  have hQuadratic := hIntegrable.quadratic.const_mul (epsilon ^ 2)
  calc
    (∫ point,
        generalLorentzHolonomicScalarDensity period hPeriod metric massSquared
            field frame point +
          epsilon * generalLorentzHolonomicScalarFirstVariation period hPeriod
            metric massSquared field variation frame point +
          epsilon ^ 2 *
            generalLorentzHolonomicScalarQuadraticRemainder period hPeriod
              metric massSquared variation frame point
      ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) =
      (∫ point,
          generalLorentzHolonomicScalarDensity period hPeriod metric
              massSquared field frame point +
            epsilon * generalLorentzHolonomicScalarFirstVariation period hPeriod
              metric massSquared field variation frame point
        ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) +
        ∫ point,
          epsilon ^ 2 *
            generalLorentzHolonomicScalarQuadraticRemainder period hPeriod
              metric massSquared variation frame point
          ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
      integral_add (hIntegrable.base.add hFirst) hQuadratic
    _ = _ := by
      rw [integral_add hIntegrable.base hFirst, integral_const_mul,
        integral_const_mul]

/-- The integrated first variation is the derivative of the canonical action
along the certified scalar line. -/
theorem canonicalGeneralLorentzHolonomicScalarAction_line_hasDerivAt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (field variation : SmoothScalarField period hPeriod)
    (frame : OrderedTangentVectorFamily period hPeriod)
    (hIntegrable : CanonicalGeneralLorentzScalarVariationIntegrable period
      hPeriod metric massSquared field variation frame) :
    HasDerivAt
      (fun epsilon : Real =>
        canonicalGeneralLorentzHolonomicScalarAction period hPeriod metric
          massSquared (scalarFieldLine period hPeriod field variation epsilon)
          frame)
      (canonicalGeneralLorentzHolonomicScalarFirstVariation period hPeriod
        metric massSquared field variation frame) 0 := by
  rw [show (fun epsilon : Real =>
      canonicalGeneralLorentzHolonomicScalarAction period hPeriod metric
        massSquared (scalarFieldLine period hPeriod field variation epsilon)
        frame) =
    (fun epsilon : Real =>
      canonicalGeneralLorentzHolonomicScalarAction period hPeriod metric
          massSquared field frame +
        epsilon * canonicalGeneralLorentzHolonomicScalarFirstVariation period
          hPeriod metric massSquared field variation frame +
        epsilon ^ 2 *
          canonicalGeneralLorentzHolonomicScalarQuadraticRemainder period
            hPeriod metric massSquared variation frame) by
      funext epsilon
      exact canonicalGeneralLorentzHolonomicScalarAction_line_expansion period
        hPeriod metric massSquared field variation frame hIntegrable epsilon]
  have hLinear := ((hasDerivAt_id' (x := (0 : Real))).mul_const
    (canonicalGeneralLorentzHolonomicScalarFirstVariation period hPeriod
      metric massSquared field variation frame)).const_add
    (canonicalGeneralLorentzHolonomicScalarAction period hPeriod metric
      massSquared field frame)
  have hQuadratic := ((hasDerivAt_id' (x := (0 : Real))).pow 2).mul_const
    (canonicalGeneralLorentzHolonomicScalarQuadraticRemainder period hPeriod
      metric massSquared variation frame)
  exact (hLinear.add hQuadratic).congr_deriv (by norm_num)

/-- Pullback commutes exactly with affine scalar lines. -/
theorem pullbackSmoothField_scalarFieldLine
    (field variation : SmoothScalarField period hPeriod)
    (epsilon : Real) :
    pullbackSmoothField period hPeriod Real
        (reflectedSpherePTDiffeomorph period hPeriod)
        (scalarFieldLine period hPeriod field variation epsilon) =
      scalarFieldLine period hPeriod
        (pullbackSmoothField period hPeriod Real
          (reflectedSpherePTDiffeomorph period hPeriod) field)
        (pullbackSmoothField period hPeriod Real
          (reflectedSpherePTDiffeomorph period hPeriod) variation)
        epsilon := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  simp

/-- Exact pointwise PT covariance of the scalar first variation. -/
theorem generalLorentzHolonomicScalarFirstVariation_pt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (field variation : SmoothScalarField period hPeriod)
    (frame : OrderedTangentVectorFamily period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalLorentzHolonomicScalarFirstVariation period hPeriod
        (smoothGeneralLorentzMetricPTPullback period hPeriod metric)
        massSquared
        (pullbackSmoothField period hPeriod Real
          (reflectedSpherePTDiffeomorph period hPeriod) field)
        (pullbackSmoothField period hPeriod Real
          (reflectedSpherePTDiffeomorph period hPeriod) variation)
        (analyticPTOrderedFramePullback period hPeriod frame) point =
      generalLorentzHolonomicScalarFirstVariation period hPeriod metric
        massSquared field variation frame
        (reflectedSpherePT period hPeriod point) := by
  have hSource := generalLorentzHolonomicScalarDensity_line_hasDerivAt
    period hPeriod
    (smoothGeneralLorentzMetricPTPullback period hPeriod metric) massSquared
    (pullbackSmoothField period hPeriod Real
      (reflectedSpherePTDiffeomorph period hPeriod) field)
    (pullbackSmoothField period hPeriod Real
      (reflectedSpherePTDiffeomorph period hPeriod) variation)
    (analyticPTOrderedFramePullback period hPeriod frame) point
  have hTarget := generalLorentzHolonomicScalarDensity_line_hasDerivAt
    period hPeriod metric massSquared field variation frame
      (reflectedSpherePT period hPeriod point)
  have hFunctions :
      (fun epsilon : Real =>
        generalLorentzHolonomicScalarDensity period hPeriod
          (smoothGeneralLorentzMetricPTPullback period hPeriod metric)
          massSquared
          (scalarFieldLine period hPeriod
            (pullbackSmoothField period hPeriod Real
              (reflectedSpherePTDiffeomorph period hPeriod) field)
            (pullbackSmoothField period hPeriod Real
              (reflectedSpherePTDiffeomorph period hPeriod) variation)
            epsilon)
          (analyticPTOrderedFramePullback period hPeriod frame) point) =
      (fun epsilon : Real =>
        generalLorentzHolonomicScalarDensity period hPeriod metric massSquared
          (scalarFieldLine period hPeriod field variation epsilon) frame
          (reflectedSpherePT period hPeriod point)) := by
    funext epsilon
    rw [← pullbackSmoothField_scalarFieldLine period hPeriod field variation
      epsilon]
    exact generalLorentzHolonomicScalarDensity_pt period hPeriod metric
      massSquared (scalarFieldLine period hPeriod field variation epsilon)
      frame point
  rw [hFunctions] at hSource
  exact hSource.unique hTarget

/-- PT transports integrability of the first variation in both directions. -/
theorem generalLorentzHolonomicScalarFirstVariation_pt_integrable_iff
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (field variation : SmoothScalarField period hPeriod)
    (frame : OrderedTangentVectorFamily period hPeriod) :
    Integrable
        (generalLorentzHolonomicScalarFirstVariation period hPeriod
          (smoothGeneralLorentzMetricPTPullback period hPeriod metric)
          massSquared
          (pullbackSmoothField period hPeriod Real
            (reflectedSpherePTDiffeomorph period hPeriod) field)
          (pullbackSmoothField period hPeriod Real
            (reflectedSpherePTDiffeomorph period hPeriod) variation)
          (analyticPTOrderedFramePullback period hPeriod frame))
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) ↔
      Integrable
        (generalLorentzHolonomicScalarFirstVariation period hPeriod metric
          massSquared field variation frame)
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  rw [show generalLorentzHolonomicScalarFirstVariation period hPeriod
      (smoothGeneralLorentzMetricPTPullback period hPeriod metric)
      massSquared
      (pullbackSmoothField period hPeriod Real
        (reflectedSpherePTDiffeomorph period hPeriod) field)
      (pullbackSmoothField period hPeriod Real
        (reflectedSpherePTDiffeomorph period hPeriod) variation)
      (analyticPTOrderedFramePullback period hPeriod frame) =
        generalLorentzHolonomicScalarFirstVariation period hPeriod metric
          massSquared field variation frame ∘
            (reflectedSpherePTMeasurableEquiv period hPeriod) by
    funext point
    exact generalLorentzHolonomicScalarFirstVariation_pt period hPeriod metric
      massSquared field variation frame point]
  exact (intrinsicCanonicalLorentzVolumeMeasure_pt_measurePreserving
    period hPeriod).integrable_comp_emb
      (reflectedSpherePTMeasurableEquiv period hPeriod).measurableEmbedding

/-- Integrated PT invariance of the fixed-metric scalar first variation. -/
theorem canonicalGeneralLorentzHolonomicScalarFirstVariation_pt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (field variation : SmoothScalarField period hPeriod)
    (frame : OrderedTangentVectorFamily period hPeriod) :
    canonicalGeneralLorentzHolonomicScalarFirstVariation period hPeriod
        (smoothGeneralLorentzMetricPTPullback period hPeriod metric)
        massSquared
        (pullbackSmoothField period hPeriod Real
          (reflectedSpherePTDiffeomorph period hPeriod) field)
        (pullbackSmoothField period hPeriod Real
          (reflectedSpherePTDiffeomorph period hPeriod) variation)
        (analyticPTOrderedFramePullback period hPeriod frame) =
      canonicalGeneralLorentzHolonomicScalarFirstVariation period hPeriod
        metric massSquared field variation frame := by
  unfold canonicalGeneralLorentzHolonomicScalarFirstVariation
  calc
    (∫ point, generalLorentzHolonomicScalarFirstVariation period hPeriod
        (smoothGeneralLorentzMetricPTPullback period hPeriod metric)
        massSquared
        (pullbackSmoothField period hPeriod Real
          (reflectedSpherePTDiffeomorph period hPeriod) field)
        (pullbackSmoothField period hPeriod Real
          (reflectedSpherePTDiffeomorph period hPeriod) variation)
        (analyticPTOrderedFramePullback period hPeriod frame) point
      ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) =
      ∫ point, generalLorentzHolonomicScalarFirstVariation period hPeriod
          metric massSquared field variation frame
          (reflectedSpherePT period hPeriod point)
        ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall
            (generalLorentzHolonomicScalarFirstVariation_pt period hPeriod
              metric massSquared field variation frame)
    _ = _ := intrinsicCanonicalLorentzVolumeMeasure_integral_pt period hPeriod
      (generalLorentzHolonomicScalarFirstVariation period hPeriod metric
        massSquared field variation frame)

end

end P0EFTJanusMappingTorusGeneralLorentzMetricPTIntegratedScalarVariation4D
end JanusFormal
