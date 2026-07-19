import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricDiffeomorphismPullback4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCompleteTimeFlow4D

/-!
# Same-configuration diagonal diffeomorphism Noether bridge on D8

The general Lorentz metric, scalar, ordered tangent family, and Borel measure
are assembled into one configuration space for the already constructed global
scalar action.  Simultaneous pullback of all four entries by any smooth D8
self-diffeomorphism leaves that same action unchanged.

Specializing to the explicit complete time-translation action gives a genuine
finite-to-infinitesimal Noether statement: the derivative of the global action
along its diagonal orbit is zero.  No first-variation contract assumes that
derivative.  This scalar-sector result does not identify an Euler adjoint,
local current, Bianchi identity, or the complete Program-P action.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGlobalScalarDiagonalDiffeomorphismNoether4D

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
open P0EFTJanusMappingTorusGeneralLorentzMetricPTIntegratedScalarAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricDiffeomorphismScalarAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricDiffeomorphismPullback4D
open P0EFTJanusMappingTorusCompleteTimeFlow4D

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

/-- All inputs of one general Lorentz scalar sector, on one actual D8
configuration space. -/
structure GlobalGeneralLorentzScalarConfiguration where
  metric : SmoothGeneralLorentzMetric period hPeriod
  massSquared : Real
  field : SmoothScalarField period hPeriod
  frame : OrderedTangentVectorFamily period hPeriod
  measure : Measure (EffectiveQuotient period hPeriod)

/-- The existing measured general Lorentz scalar action, now viewed as one
function on the common configuration space above. -/
def sameConfigurationGeneralLorentzScalarAction
    (configuration :
      GlobalGeneralLorentzScalarConfiguration period hPeriod) : Real :=
  measuredGeneralLorentzHolonomicScalarAction period hPeriod
    configuration.metric configuration.massSquared configuration.field
    configuration.frame configuration.measure

/-- Simultaneous diagonal pullback of every geometric entry of the same
configuration. -/
def diagonalDiffeomorphismPullback
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (configuration :
      GlobalGeneralLorentzScalarConfiguration period hPeriod) :
    GlobalGeneralLorentzScalarConfiguration period hPeriod where
  metric := smoothGeneralLorentzMetricDiffeomorphismPullback period hPeriod
    diffeomorphism configuration.metric
  massSquared := configuration.massSquared
  field := pullbackSmoothField period hPeriod Real diffeomorphism
    configuration.field
  frame := diffeomorphismOrderedTangentVectorPullback period hPeriod
    diffeomorphism configuration.frame
  measure := diffeomorphismMeasurePullback period hPeriod diffeomorphism
    configuration.measure

/-- Finite diagonal invariance of the same global action for every smooth D8
self-diffeomorphism. -/
@[simp] theorem sameConfigurationGeneralLorentzScalarAction_diagonal_invariant
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (configuration :
      GlobalGeneralLorentzScalarConfiguration period hPeriod) :
    sameConfigurationGeneralLorentzScalarAction period hPeriod
        (diagonalDiffeomorphismPullback period hPeriod diffeomorphism
          configuration) =
      sameConfigurationGeneralLorentzScalarAction period hPeriod
        configuration :=
  measuredGeneralLorentzHolonomicScalarAction_diffeomorphism_unconditional
    period hPeriod diffeomorphism configuration.metric
    configuration.massSquared configuration.field configuration.frame
    configuration.measure

/-- The same global action evaluated on the explicit complete time-translation
orbit in its common configuration space. -/
def completeTimeDiagonalScalarActionOrbit
    (configuration :
      GlobalGeneralLorentzScalarConfiguration period hPeriod)
    (parameter : Real) : Real :=
  sameConfigurationGeneralLorentzScalarAction period hPeriod
    (diagonalDiffeomorphismPullback period hPeriod
      (effectiveTimeFlowDiffeomorph period hPeriod parameter) configuration)

/-- Every finite point of the explicit diagonal orbit has the original action
value. -/
@[simp] theorem completeTimeDiagonalScalarActionOrbit_eq
    (configuration :
      GlobalGeneralLorentzScalarConfiguration period hPeriod)
    (parameter : Real) :
    completeTimeDiagonalScalarActionOrbit period hPeriod configuration
        parameter =
      sameConfigurationGeneralLorentzScalarAction period hPeriod
        configuration :=
  sameConfigurationGeneralLorentzScalarAction_diagonal_invariant period hPeriod
    (effectiveTimeFlowDiffeomorph period hPeriod parameter) configuration

/-- Genuine integrated Noether identity for the explicit complete diagonal
time-translation subgroup: the true global scalar action orbit has derivative
zero at the identity. -/
theorem completeTimeDiagonalScalarActionOrbit_hasDerivAt_zero
    (configuration :
      GlobalGeneralLorentzScalarConfiguration period hPeriod) :
    HasDerivAt
      (completeTimeDiagonalScalarActionOrbit period hPeriod configuration)
      0 0 := by
  rw [show completeTimeDiagonalScalarActionOrbit period hPeriod configuration =
      fun _ : Real =>
        sameConfigurationGeneralLorentzScalarAction period hPeriod
          configuration by
    funext parameter
    exact completeTimeDiagonalScalarActionOrbit_eq period hPeriod configuration
      parameter]
  exact hasDerivAt_const (x := (0 : Real))
    (c := sameConfigurationGeneralLorentzScalarAction period hPeriod
      configuration)

/-- Derivative form of the same integrated Noether identity. -/
theorem completeTimeDiagonalScalarActionOrbit_deriv_eq_zero
    (configuration :
      GlobalGeneralLorentzScalarConfiguration period hPeriod) :
    deriv (completeTimeDiagonalScalarActionOrbit period hPeriod configuration)
        0 = 0 :=
  (completeTimeDiagonalScalarActionOrbit_hasDerivAt_zero period hPeriod
    configuration).deriv

end

end P0EFTJanusMappingTorusGlobalScalarDiagonalDiffeomorphismNoether4D
end JanusFormal
