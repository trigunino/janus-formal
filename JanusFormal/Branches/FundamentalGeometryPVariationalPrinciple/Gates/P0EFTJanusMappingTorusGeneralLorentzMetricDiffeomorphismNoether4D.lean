import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricDiffeomorphismScalarAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusMetricMatterGaugeNoetherOperator4D

/-!
# Infinitesimal Noether bridge for the general Lorentz scalar action

A supplied smooth one-parameter D8 diffeomorphism flow, together with smooth
general-metric pullback certificates at every parameter, defines the finite
orbit of the measured scalar action.  Finite covariance makes that real-valued
orbit exactly constant and hence gives derivative zero at the identity.

An explicit first-variation contract then identifies that derivative with the
existing scalar diffeomorphism Noether pairing.  The contract includes base
integrability to exclude the nonintegrable-zero convention of the Bochner
integral.  It does not construct a local current: deriving a divergence law
still needs a local first-variation/integration-by-parts theorem, enough test
ghosts, and boundary-flux control.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGeneralLorentzMetricDiffeomorphismNoether4D

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
open P0EFTJanusMappingTorusLinearizedDiffeomorphismBRST4D
open P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D
open P0EFTJanusMappingTorusMetricMatterGaugeNoetherOperator4D
open P0EFTJanusMappingTorusGeneralLorentzMetricPTIntegratedScalarAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricDiffeomorphismScalarAction4D

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

/-- One supplied smooth diffeomorphism orbit for a general Lorentz metric.
The underlying flow has smooth point-orbits and a genuine smooth infinitesimal
ghost.  Every finite-time metric pullback is supplied in the exact contract
used by the finite covariance gate. -/
structure SmoothGeneralLorentzScalarDiffeomorphismOrbit
    (metric : SmoothGeneralLorentzMetric period hPeriod) where
  flow : SmoothMetricPairPullbackFlow period hPeriod metric.tensor metric.tensor
  metricPullback : ∀ parameter,
    SmoothGeneralLorentzMetricDiffeomorphismPullback period hPeriod
      (flow.curve parameter) metric
  ghost : SmoothDiffeomorphismGhost period hPeriod
  generatesGhost : ∀ point,
    flow.velocityAt period hPeriod metric.tensor metric.tensor point =
      ghost point

/-- The measured scalar action evaluated on the fully transported finite
diffeomorphism orbit. -/
def smoothGeneralLorentzScalarDiffeomorphismOrbitAction
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (orbit : SmoothGeneralLorentzScalarDiffeomorphismOrbit period hPeriod metric)
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod)
    (frame : OrderedTangentVectorFamily period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (parameter : Real) : Real :=
  measuredGeneralLorentzHolonomicScalarAction period hPeriod
    (orbit.metricPullback parameter).pulledMetric massSquared
    (pullbackSmoothField period hPeriod Real (orbit.flow.curve parameter) field)
    (diffeomorphismOrderedTangentVectorPullback period hPeriod
      (orbit.flow.curve parameter) frame)
    (diffeomorphismMeasurePullback period hPeriod
      (orbit.flow.curve parameter) measure)

/-- Finite covariance makes every point of the supplied action orbit equal to
the original measured action. -/
theorem smoothGeneralLorentzScalarDiffeomorphismOrbitAction_eq
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (orbit : SmoothGeneralLorentzScalarDiffeomorphismOrbit period hPeriod metric)
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod)
    (frame : OrderedTangentVectorFamily period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (parameter : Real) :
    smoothGeneralLorentzScalarDiffeomorphismOrbitAction period hPeriod metric
        orbit massSquared field frame measure parameter =
      measuredGeneralLorentzHolonomicScalarAction period hPeriod metric
        massSquared field frame measure :=
  measuredGeneralLorentzHolonomicScalarAction_diffeomorphism period hPeriod
    (orbit.flow.curve parameter) metric (orbit.metricPullback parameter)
    massSquared field frame measure

/-- The real-valued action orbit has derivative zero at the identity.  This is
an unconditional consequence of finite covariance once the orbit pullback
certificates are supplied. -/
theorem smoothGeneralLorentzScalarDiffeomorphismOrbitAction_hasDerivAt_zero
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (orbit : SmoothGeneralLorentzScalarDiffeomorphismOrbit period hPeriod metric)
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod)
    (frame : OrderedTangentVectorFamily period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod)) :
    HasDerivAt
      (smoothGeneralLorentzScalarDiffeomorphismOrbitAction period hPeriod
        metric orbit massSquared field frame measure)
      0 0 := by
  rw [show smoothGeneralLorentzScalarDiffeomorphismOrbitAction period hPeriod
      metric orbit massSquared field frame measure =
    fun _ => measuredGeneralLorentzHolonomicScalarAction period hPeriod metric
      massSquared field frame measure by
    funext parameter
    exact smoothGeneralLorentzScalarDiffeomorphismOrbitAction_eq period hPeriod
      metric orbit massSquared field frame measure parameter]
  exact hasDerivAt_const (x := (0 : Real))
    (c := measuredGeneralLorentzHolonomicScalarAction period hPeriod metric
      massSquared field frame measure)

/-- Exact non-vacuity and first-variation contract for the Noether bridge.
The derivative of the fully transported action orbit is required to equal the
scalar Euler covector paired with the actual Lie derivative generated by the
orbit ghost.  This is precisely where the simultaneous metric/frame/measure
first variations must already have been accounted for. -/
structure GeneralLorentzScalarDiffeomorphismOrbitFirstVariationContract
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (orbit : SmoothGeneralLorentzScalarDiffeomorphismOrbit period hPeriod metric)
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod)
    (frame : OrderedTangentVectorFamily period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (euler : SmoothScalarField period hPeriod →ₗ[Real] Real) : Prop where
  base_integrable : Integrable
    (generalLorentzHolonomicScalarDensity period hPeriod metric massSquared
      field frame) measure
  action_hasDerivAt : HasDerivAt
    (smoothGeneralLorentzScalarDiffeomorphismOrbitAction period hPeriod metric
      orbit massSquared field frame measure)
    (euler (scalarLieDerivative period hPeriod orbit.ghost field)) 0

/-- The integrability component of the first-variation contract transports to
every finite point of the orbit. -/
theorem smoothGeneralLorentzScalarDiffeomorphismOrbit_integrable
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (orbit : SmoothGeneralLorentzScalarDiffeomorphismOrbit period hPeriod metric)
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod)
    (frame : OrderedTangentVectorFamily period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (euler : SmoothScalarField period hPeriod →ₗ[Real] Real)
    (contract :
      GeneralLorentzScalarDiffeomorphismOrbitFirstVariationContract period
        hPeriod metric orbit massSquared field frame measure euler)
    (parameter : Real) :
    Integrable
      (generalLorentzHolonomicScalarDensity period hPeriod
        (orbit.metricPullback parameter).pulledMetric massSquared
        (pullbackSmoothField period hPeriod Real
          (orbit.flow.curve parameter) field)
        (diffeomorphismOrderedTangentVectorPullback period hPeriod
          (orbit.flow.curve parameter) frame))
      (diffeomorphismMeasurePullback period hPeriod
        (orbit.flow.curve parameter) measure) := by
  exact (generalLorentzHolonomicScalarDensity_diffeomorphism_integrable_iff
    period hPeriod (orbit.flow.curve parameter) metric
    (orbit.metricPullback parameter) massSquared field frame measure).2
      contract.base_integrable

/-- Under the exact first-variation contract, the existing scalar Noether
pairing is literally the derivative of the finite action orbit. -/
theorem scalarDiffeomorphismNoetherOperator_apply_eq_orbitAction_deriv
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (orbit : SmoothGeneralLorentzScalarDiffeomorphismOrbit period hPeriod metric)
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod)
    (frame : OrderedTangentVectorFamily period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (euler : SmoothScalarField period hPeriod →ₗ[Real] Real)
    (contract :
      GeneralLorentzScalarDiffeomorphismOrbitFirstVariationContract period
        hPeriod metric orbit massSquared field frame measure euler) :
    scalarDiffeomorphismNoetherOperator period hPeriod field euler orbit.ghost =
      deriv
        (smoothGeneralLorentzScalarDiffeomorphismOrbitAction period hPeriod
          metric orbit massSquared field frame measure) 0 := by
  rw [scalarDiffeomorphismNoetherOperator_apply]
  exact contract.action_hasDerivAt.deriv.symm

/-- Infinitesimal integrated Noether identity along the supplied ghost orbit. -/
theorem scalarDiffeomorphismNoetherOperator_apply_eq_zero
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (orbit : SmoothGeneralLorentzScalarDiffeomorphismOrbit period hPeriod metric)
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod)
    (frame : OrderedTangentVectorFamily period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (euler : SmoothScalarField period hPeriod →ₗ[Real] Real)
    (contract :
      GeneralLorentzScalarDiffeomorphismOrbitFirstVariationContract period
        hPeriod metric orbit massSquared field frame measure euler) :
    scalarDiffeomorphismNoetherOperator period hPeriod field euler orbit.ghost =
      0 := by
  exact contract.action_hasDerivAt.unique
    (smoothGeneralLorentzScalarDiffeomorphismOrbitAction_hasDerivAt_zero
      period hPeriod metric orbit massSquared field frame measure)

end

end P0EFTJanusMappingTorusGeneralLorentzMetricDiffeomorphismNoether4D
end JanusFormal
