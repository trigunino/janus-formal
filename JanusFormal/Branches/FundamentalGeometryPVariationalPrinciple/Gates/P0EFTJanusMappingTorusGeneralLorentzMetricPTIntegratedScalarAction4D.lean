import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricPTScalarAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusD8NonabelianGhostSmoothSpacetimeBVPTCovariance4D

/-!
# Integrated PT covariance of the general Lorentz scalar action

The pointwise holonomic density is evaluated in an ordered tangent-frame
field.  Pulling that frame back by the analytic PT derivative turns the
existing pointwise covariance theorem into composition by PT.  The canonical
quotient Lorentz measure is PT-preserving, so the corresponding integrated
action is invariant.  Integrability is transported exactly; no regularity of
an arbitrary frame field is silently assumed.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGeneralLorentzMetricPTIntegratedScalarAction4D

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

private abbrev TangentFiber (point : EffectiveQuotient period hPeriod) :=
  TangentSpace coverModelWithCorners point

/-- A pointwise ordered tangent-vector family, exactly matching the existing
holonomic-density input.  Neither linear independence nor global smoothness
is silently built into this minimal interface. -/
abbrev OrderedTangentVectorFamily :=
  ∀ point : EffectiveQuotient period hPeriod,
    Fin 4 → TangentFiber period hPeriod point

/-- Pullback of an ordered tangent frame by the inverse analytic PT
derivative. -/
def analyticPTOrderedFramePullback
    (frame : OrderedTangentVectorFamily period hPeriod) :
    OrderedTangentVectorFamily period hPeriod :=
  fun point index =>
    (analyticPTDerivative period hPeriod point).symm
      (frame (reflectedSpherePT period hPeriod point) index)

@[simp]
theorem analyticPTDerivative_orderedFramePullback
    (frame : OrderedTangentVectorFamily period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (index : Fin 4) :
    analyticPTDerivative period hPeriod point
        (analyticPTOrderedFramePullback period hPeriod frame point index) =
      frame (reflectedSpherePT period hPeriod point) index := by
  simp [analyticPTOrderedFramePullback]

/-- General holonomic scalar density in a supplied pointwise ordered frame. -/
def generalLorentzHolonomicScalarDensity
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod)
    (frame : OrderedTangentVectorFamily period hPeriod)
    (point : EffectiveQuotient period hPeriod) : Real :=
  holonomicScalarDensity period hPeriod metric massSquared field point
    (frame point)

/-- Exact pointwise PT covariance after the metric, scalar, and frame are
pulled back coherently. -/
theorem generalLorentzHolonomicScalarDensity_pt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod)
    (frame : OrderedTangentVectorFamily period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalLorentzHolonomicScalarDensity period hPeriod
        (smoothGeneralLorentzMetricPTPullback period hPeriod metric)
        massSquared
        (pullbackSmoothField period hPeriod Real
          (reflectedSpherePTDiffeomorph period hPeriod) field)
        (analyticPTOrderedFramePullback period hPeriod frame) point =
      generalLorentzHolonomicScalarDensity period hPeriod metric massSquared
        field frame (reflectedSpherePT period hPeriod point) := by
  unfold generalLorentzHolonomicScalarDensity
  rw [holonomicScalarDensity_pt]
  congr 1
  funext index
  exact analyticPTDerivative_orderedFramePullback period hPeriod frame point index

/-- The general-metric scalar action relative to the intrinsic canonical
quotient Lorentz measure. -/
def canonicalGeneralLorentzHolonomicScalarAction
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod)
    (frame : OrderedTangentVectorFamily period hPeriod) : Real :=
  ∫ point,
      generalLorentzHolonomicScalarDensity period hPeriod metric massSquared
        field frame point
    ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)

/-- PT transports integrability of the general scalar density in both
directions.  Thus the invariant action theorem does not hide a measurability
or integrability assumption on the supplied frame field. -/
theorem generalLorentzHolonomicScalarDensity_pt_integrable_iff
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod)
    (frame : OrderedTangentVectorFamily period hPeriod) :
    Integrable
        (generalLorentzHolonomicScalarDensity period hPeriod
          (smoothGeneralLorentzMetricPTPullback period hPeriod metric)
          massSquared
          (pullbackSmoothField period hPeriod Real
            (reflectedSpherePTDiffeomorph period hPeriod) field)
          (analyticPTOrderedFramePullback period hPeriod frame))
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) ↔
      Integrable
        (generalLorentzHolonomicScalarDensity period hPeriod metric massSquared
          field frame)
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  rw [show generalLorentzHolonomicScalarDensity period hPeriod
      (smoothGeneralLorentzMetricPTPullback period hPeriod metric)
      massSquared
      (pullbackSmoothField period hPeriod Real
        (reflectedSpherePTDiffeomorph period hPeriod) field)
      (analyticPTOrderedFramePullback period hPeriod frame) =
        generalLorentzHolonomicScalarDensity period hPeriod metric massSquared
          field frame ∘
            (reflectedSpherePTMeasurableEquiv period hPeriod) by
    funext point
    exact generalLorentzHolonomicScalarDensity_pt period hPeriod metric
      massSquared field frame point]
  exact (intrinsicCanonicalLorentzVolumeMeasure_pt_measurePreserving
    period hPeriod).integrable_comp_emb
      (reflectedSpherePTMeasurableEquiv period hPeriod).measurableEmbedding

/-- Integrated PT invariance for an arbitrary smooth general Lorentz metric.
The integral identity itself is unconditional; the preceding theorem gives
the exact integrability contract for interpreting it as a Bochner integral. -/
theorem canonicalGeneralLorentzHolonomicScalarAction_pt
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod)
    (frame : OrderedTangentVectorFamily period hPeriod) :
    canonicalGeneralLorentzHolonomicScalarAction period hPeriod
        (smoothGeneralLorentzMetricPTPullback period hPeriod metric)
        massSquared
        (pullbackSmoothField period hPeriod Real
          (reflectedSpherePTDiffeomorph period hPeriod) field)
        (analyticPTOrderedFramePullback period hPeriod frame) =
      canonicalGeneralLorentzHolonomicScalarAction period hPeriod metric
        massSquared field frame := by
  unfold canonicalGeneralLorentzHolonomicScalarAction
  calc
    (∫ point, generalLorentzHolonomicScalarDensity period hPeriod
        (smoothGeneralLorentzMetricPTPullback period hPeriod metric)
        massSquared
        (pullbackSmoothField period hPeriod Real
          (reflectedSpherePTDiffeomorph period hPeriod) field)
        (analyticPTOrderedFramePullback period hPeriod frame) point
      ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) =
      ∫ point, generalLorentzHolonomicScalarDensity period hPeriod metric
          massSquared field frame (reflectedSpherePT period hPeriod point)
        ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall
            (generalLorentzHolonomicScalarDensity_pt period hPeriod metric
              massSquared field frame)
    _ = _ := intrinsicCanonicalLorentzVolumeMeasure_integral_pt period hPeriod
      (generalLorentzHolonomicScalarDensity period hPeriod metric massSquared
        field frame)

end

end P0EFTJanusMappingTorusGeneralLorentzMetricPTIntegratedScalarAction4D
end JanusFormal
