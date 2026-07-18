import Mathlib.Dynamics.Ergodic.MeasurePreserving
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricPTIntegratedScalarAction4D

/-!
# Diffeomorphism covariance of the general Lorentz scalar action

An arbitrary smooth self-diffeomorphism transports the scalar field, ordered
tangent-vector family, and integration measure.  The only residual geometric
input is an explicit smooth general-metric pullback certificate: the existing
general pointwise naturality theorem determines its musical map exactly, but
the dependent smooth tensor pullback has only been constructed
unconditionally for analytic PT.

Under that exact certificate, density covariance, iff integrability transport,
single-sector action invariance, and the direct two-sector exchange corollary
are proved.  No infinitesimal metric derivative or Noether identity is claimed.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGeneralLorentzMetricDiffeomorphismScalarAction4D

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusDiagonalDiffeomorphismAction4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarDensityFrameCovariance4D
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

/-- Exact residual contract for a smooth pullback of a general Lorentz metric
by an arbitrary D8 self-diffeomorphism.  The pulled metric is tied pointwise to
the genuine derivative pullback of the original musical equivalence. -/
structure SmoothGeneralLorentzMetricDiffeomorphismPullback
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) where
  pulledMetric : SmoothGeneralLorentzMetric period hPeriod
  musical_eq : ∀ point,
    pulledMetric.musical point =
      pullbackMusical period hPeriod
        (diffeomorphismDerivative period hPeriod diffeomorphism point)
        (metric.musical (diffeomorphism point))

/-- The musical certificate forces the covariant tensor itself to be the
genuine double derivative pullback. -/
theorem smoothGeneralLorentzMetricDiffeomorphismPullback_tensor_apply
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (pullback : SmoothGeneralLorentzMetricDiffeomorphismPullback period hPeriod
      diffeomorphism metric)
    (point : EffectiveQuotient period hPeriod)
    (first second : TangentSpace coverModelWithCorners point) :
    pullback.pulledMetric.tensor.tensor point first second =
      metric.tensor.tensor (diffeomorphism point)
        (mfderiv coverModelWithCorners coverModelWithCorners diffeomorphism
          point first)
        (mfderiv coverModelWithCorners coverModelWithCorners diffeomorphism
          point second) := by
  rw [← DFunLike.congr_fun
    (DFunLike.congr_fun
      (pullback.pulledMetric.musical_eq_tensor point) first) second]
  rw [pullback.musical_eq]
  change metric.musical (diffeomorphism point)
      (diffeomorphismDerivative period hPeriod diffeomorphism point first)
      (diffeomorphismDerivative period hPeriod diffeomorphism point second) = _
  calc
    _ = metric.tensor.tensor (diffeomorphism point)
        (diffeomorphismDerivative period hPeriod diffeomorphism point first)
        (diffeomorphismDerivative period hPeriod diffeomorphism point second) :=
      DFunLike.congr_fun
        (DFunLike.congr_fun
          (metric.musical_eq_tensor (diffeomorphism point)) _) _
    _ = _ := rfl

/-- Pullback of the supplied ordered tangent-vector family by the inverse
derivative. -/
def diffeomorphismOrderedTangentVectorPullback
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (frame : OrderedTangentVectorFamily period hPeriod) :
    OrderedTangentVectorFamily period hPeriod :=
  fun point index =>
    (diffeomorphismDerivative period hPeriod diffeomorphism point).symm
      (frame (diffeomorphism point) index)

@[simp]
theorem diffeomorphismDerivative_orderedTangentVectorPullback
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (frame : OrderedTangentVectorFamily period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (index : Fin 4) :
    diffeomorphismDerivative period hPeriod diffeomorphism point
        (diffeomorphismOrderedTangentVectorPullback period hPeriod
          diffeomorphism frame point index) =
      frame (diffeomorphism point) index := by
  simp [diffeomorphismOrderedTangentVectorPullback]

/-- Exact density covariance under simultaneous transport of metric, scalar,
and tangent-vector family. -/
theorem generalLorentzHolonomicScalarDensity_diffeomorphism
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (pullback : SmoothGeneralLorentzMetricDiffeomorphismPullback period hPeriod
      diffeomorphism metric)
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod)
    (frame : OrderedTangentVectorFamily period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalLorentzHolonomicScalarDensity period hPeriod pullback.pulledMetric
        massSquared
        (pullbackSmoothField period hPeriod Real diffeomorphism field)
        (diffeomorphismOrderedTangentVectorPullback period hPeriod
          diffeomorphism frame) point =
      generalLorentzHolonomicScalarDensity period hPeriod metric massSquared
        field frame (diffeomorphism point) := by
  unfold generalLorentzHolonomicScalarDensity
  rw [holonomicScalarDensity_eq_fiber]
  rw [pullback.musical_eq]
  simp only [pullbackSmoothField_apply]
  simpa only [diffeomorphismDerivative_orderedTangentVectorPullback] using
    holonomicScalarDensity_diffeomorphism period hPeriod diffeomorphism metric
      massSquared field point
      (diffeomorphismOrderedTangentVectorPullback period hPeriod
        diffeomorphism frame point)

/-- The smooth self-diffeomorphism viewed as a measurable equivalence of the
Borel quotient. -/
def spacetimeDiffeomorphismMeasurableEquiv
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod) :
    EffectiveQuotient period hPeriod ≃ᵐ EffectiveQuotient period hPeriod :=
  diffeomorphism.toHomeomorph.toMeasurableEquiv

@[simp]
theorem spacetimeDiffeomorphismMeasurableEquiv_apply
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    spacetimeDiffeomorphismMeasurableEquiv period hPeriod diffeomorphism point =
      diffeomorphism point :=
  rfl

/-- Pullback of a target measure by a self-diffeomorphism, represented as the
pushforward along its inverse. -/
def diffeomorphismMeasurePullback
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod)) :
    Measure (EffectiveQuotient period hPeriod) :=
  Measure.map
    (spacetimeDiffeomorphismMeasurableEquiv period hPeriod diffeomorphism).symm
    measure

/-- The diffeomorphism sends its pulled measure exactly back to the target
measure. -/
theorem diffeomorphismMeasurePullback_measurePreserving
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod)) :
    MeasurePreserving
      (spacetimeDiffeomorphismMeasurableEquiv period hPeriod diffeomorphism)
      (diffeomorphismMeasurePullback period hPeriod diffeomorphism measure)
      measure := by
  simpa [diffeomorphismMeasurePullback] using
    MeasurableEquiv.measurePreserving_symm measure
      (spacetimeDiffeomorphismMeasurableEquiv period hPeriod
        diffeomorphism).symm

/-- General Lorentz holonomic scalar action against an arbitrary supplied
Borel measure. -/
def measuredGeneralLorentzHolonomicScalarAction
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod)
    (frame : OrderedTangentVectorFamily period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod)) : Real :=
  ∫ point,
      generalLorentzHolonomicScalarDensity period hPeriod metric massSquared
        field frame point
    ∂measure

/-- Integrability is transported in both directions by the simultaneous
diffeomorphism pullback. -/
theorem generalLorentzHolonomicScalarDensity_diffeomorphism_integrable_iff
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (pullback : SmoothGeneralLorentzMetricDiffeomorphismPullback period hPeriod
      diffeomorphism metric)
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod)
    (frame : OrderedTangentVectorFamily period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod)) :
    Integrable
        (generalLorentzHolonomicScalarDensity period hPeriod
          pullback.pulledMetric massSquared
          (pullbackSmoothField period hPeriod Real diffeomorphism field)
          (diffeomorphismOrderedTangentVectorPullback period hPeriod
            diffeomorphism frame))
        (diffeomorphismMeasurePullback period hPeriod diffeomorphism measure) ↔
      Integrable
        (generalLorentzHolonomicScalarDensity period hPeriod metric massSquared
          field frame) measure := by
  rw [show generalLorentzHolonomicScalarDensity period hPeriod
      pullback.pulledMetric massSquared
      (pullbackSmoothField period hPeriod Real diffeomorphism field)
      (diffeomorphismOrderedTangentVectorPullback period hPeriod
        diffeomorphism frame) =
        generalLorentzHolonomicScalarDensity period hPeriod metric massSquared
          field frame ∘
            (spacetimeDiffeomorphismMeasurableEquiv period hPeriod
              diffeomorphism) by
    funext point
    exact generalLorentzHolonomicScalarDensity_diffeomorphism period hPeriod
      diffeomorphism metric pullback massSquared field frame point]
  exact (diffeomorphismMeasurePullback_measurePreserving period hPeriod
    diffeomorphism measure).integrable_comp_emb
      (spacetimeDiffeomorphismMeasurableEquiv period hPeriod
        diffeomorphism).measurableEmbedding

/-- The integrated action is invariant when metric, scalar, tangent family,
and measure are transported simultaneously. -/
theorem measuredGeneralLorentzHolonomicScalarAction_diffeomorphism
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (pullback : SmoothGeneralLorentzMetricDiffeomorphismPullback period hPeriod
      diffeomorphism metric)
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod)
    (frame : OrderedTangentVectorFamily period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod)) :
    measuredGeneralLorentzHolonomicScalarAction period hPeriod
        pullback.pulledMetric massSquared
        (pullbackSmoothField period hPeriod Real diffeomorphism field)
        (diffeomorphismOrderedTangentVectorPullback period hPeriod
          diffeomorphism frame)
        (diffeomorphismMeasurePullback period hPeriod diffeomorphism measure) =
      measuredGeneralLorentzHolonomicScalarAction period hPeriod metric
        massSquared field frame measure := by
  unfold measuredGeneralLorentzHolonomicScalarAction
  calc
    (∫ point, generalLorentzHolonomicScalarDensity period hPeriod
        pullback.pulledMetric massSquared
        (pullbackSmoothField period hPeriod Real diffeomorphism field)
        (diffeomorphismOrderedTangentVectorPullback period hPeriod
          diffeomorphism frame) point
      ∂(diffeomorphismMeasurePullback period hPeriod diffeomorphism measure)) =
      ∫ point, generalLorentzHolonomicScalarDensity period hPeriod metric
          massSquared field frame (diffeomorphism point)
        ∂(diffeomorphismMeasurePullback period hPeriod diffeomorphism
          measure) := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall
              (generalLorentzHolonomicScalarDensity_diffeomorphism period
                hPeriod diffeomorphism metric pullback massSquared field frame)
    _ = _ := (diffeomorphismMeasurePullback_measurePreserving period hPeriod
      diffeomorphism measure).integral_comp'
        (generalLorentzHolonomicScalarDensity period hPeriod metric massSquared
          field frame)

/-- Sum of two measured scalar sectors. -/
def measuredGeneralLorentzHolonomicScalarPairAction
    (firstMetric secondMetric : SmoothGeneralLorentzMetric period hPeriod)
    (firstMassSquared secondMassSquared : Real)
    (firstField secondField : SmoothScalarField period hPeriod)
    (firstFrame secondFrame : OrderedTangentVectorFamily period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod)) : Real :=
  measuredGeneralLorentzHolonomicScalarAction period hPeriod firstMetric
      firstMassSquared firstField firstFrame measure +
    measuredGeneralLorentzHolonomicScalarAction period hPeriod secondMetric
      secondMassSquared secondField secondFrame measure

/-- Direct two-sector corollary: diffeomorphism pullback combined with sector
exchange leaves the summed action invariant. -/
theorem measuredGeneralLorentzHolonomicScalarPairAction_diffeomorphism_exchange
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (firstMetric secondMetric : SmoothGeneralLorentzMetric period hPeriod)
    (firstPullback : SmoothGeneralLorentzMetricDiffeomorphismPullback period
      hPeriod diffeomorphism firstMetric)
    (secondPullback : SmoothGeneralLorentzMetricDiffeomorphismPullback period
      hPeriod diffeomorphism secondMetric)
    (firstMassSquared secondMassSquared : Real)
    (firstField secondField : SmoothScalarField period hPeriod)
    (firstFrame secondFrame : OrderedTangentVectorFamily period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod)) :
    measuredGeneralLorentzHolonomicScalarPairAction period hPeriod
        secondPullback.pulledMetric firstPullback.pulledMetric
        secondMassSquared firstMassSquared
        (pullbackSmoothField period hPeriod Real diffeomorphism secondField)
        (pullbackSmoothField period hPeriod Real diffeomorphism firstField)
        (diffeomorphismOrderedTangentVectorPullback period hPeriod
          diffeomorphism secondFrame)
        (diffeomorphismOrderedTangentVectorPullback period hPeriod
          diffeomorphism firstFrame)
        (diffeomorphismMeasurePullback period hPeriod diffeomorphism measure) =
      measuredGeneralLorentzHolonomicScalarPairAction period hPeriod
        firstMetric secondMetric firstMassSquared secondMassSquared
        firstField secondField firstFrame secondFrame measure := by
  unfold measuredGeneralLorentzHolonomicScalarPairAction
  rw [measuredGeneralLorentzHolonomicScalarAction_diffeomorphism period hPeriod
      diffeomorphism secondMetric secondPullback secondMassSquared secondField
      secondFrame measure,
    measuredGeneralLorentzHolonomicScalarAction_diffeomorphism period hPeriod
      diffeomorphism firstMetric firstPullback firstMassSquared firstField
      firstFrame measure]
  exact add_comm _ _

end

end P0EFTJanusMappingTorusGeneralLorentzMetricDiffeomorphismScalarAction4D
end JanusFormal
