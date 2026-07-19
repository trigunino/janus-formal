import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalScalarDiagonalDiffeomorphismNoether4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D

/-!
# Diagonal diffeomorphism Noether identity for the actual matter multiplet

The existing global scalar invariance is summed over the eight genuine matter
coordinates extracted from one `IndependentFields`.  All components use one
common Lorentz metric, frame and measure.  The finite diagonal action is
invariant under every smooth D8 self-diffeomorphism, and the complete time-flow
orbit therefore has derivative zero.

This is the covariant eight-scalar matter block only.  It is not identified
with the separate diagonal-magnitude functional, and contains no Robin, LL,
Einstein--Hilbert, Maxwell, ghost or boundary term.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGlobalMatterMultipletDiagonalDiffeomorphismNoether4D

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusDiagonalDiffeomorphismAction4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricPTIntegratedScalarAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricDiffeomorphismScalarAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricDiffeomorphismPullback4D
open P0EFTJanusMappingTorusCompleteTimeFlow4D
open P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D
open P0EFTJanusMappingTorusGlobalScalarDiagonalDiffeomorphismNoether4D

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

/-- One common geometric background carrying all eight actual matter
coordinates. -/
structure GlobalGeneralLorentzMatterConfiguration where
  metric : SmoothGeneralLorentzMetric period hPeriod
  massSquared : MatterComponentIndex → Real
  fields : MatterComponentFamily period hPeriod
  frame : OrderedTangentVectorFamily period hPeriod
  measure : Measure (EffectiveQuotient period hPeriod)

/-- The component scalar configuration without copying any geometric input. -/
def scalarComponentConfiguration
    (configuration : GlobalGeneralLorentzMatterConfiguration period hPeriod)
    (index : MatterComponentIndex) :
    GlobalGeneralLorentzScalarConfiguration period hPeriod where
  metric := configuration.metric
  massSquared := configuration.massSquared index
  field := configuration.fields index
  frame := configuration.frame
  measure := configuration.measure

/-- The global covariant action of the eight-component matter multiplet. -/
def sameConfigurationGeneralLorentzMatterAction
    (configuration : GlobalGeneralLorentzMatterConfiguration period hPeriod) :
    Real :=
  ∑ index : MatterComponentIndex,
    sameConfigurationGeneralLorentzScalarAction period hPeriod
      (scalarComponentConfiguration period hPeriod configuration index)

/-- Simultaneous pullback of the common geometry and every matter component. -/
def matterDiagonalDiffeomorphismPullback
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (configuration : GlobalGeneralLorentzMatterConfiguration period hPeriod) :
    GlobalGeneralLorentzMatterConfiguration period hPeriod where
  metric := smoothGeneralLorentzMetricDiffeomorphismPullback period hPeriod
    diffeomorphism configuration.metric
  massSquared := configuration.massSquared
  fields := fun index => pullbackSmoothField period hPeriod Real diffeomorphism
    (configuration.fields index)
  frame := diffeomorphismOrderedTangentVectorPullback period hPeriod
    diffeomorphism configuration.frame
  measure := diffeomorphismMeasurePullback period hPeriod diffeomorphism
    configuration.measure

@[simp]
theorem scalarComponentConfiguration_diagonalPullback
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (configuration : GlobalGeneralLorentzMatterConfiguration period hPeriod)
    (index : MatterComponentIndex) :
    scalarComponentConfiguration period hPeriod
        (matterDiagonalDiffeomorphismPullback period hPeriod diffeomorphism
          configuration) index =
      diagonalDiffeomorphismPullback period hPeriod diffeomorphism
        (scalarComponentConfiguration period hPeriod configuration index) :=
  rfl

/-- Finite diagonal invariance of the same eight-component global action. -/
@[simp]
theorem sameConfigurationGeneralLorentzMatterAction_diagonal_invariant
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (configuration : GlobalGeneralLorentzMatterConfiguration period hPeriod) :
    sameConfigurationGeneralLorentzMatterAction period hPeriod
        (matterDiagonalDiffeomorphismPullback period hPeriod diffeomorphism
          configuration) =
      sameConfigurationGeneralLorentzMatterAction period hPeriod
        configuration := by
  unfold sameConfigurationGeneralLorentzMatterAction
  apply Finset.sum_congr rfl
  intro index _
  rw [scalarComponentConfiguration_diagonalPullback]
  exact sameConfigurationGeneralLorentzScalarAction_diagonal_invariant
    period hPeriod diffeomorphism
      (scalarComponentConfiguration period hPeriod configuration index)

/-- Specialization to the eight fields stored by one Program-P
`IndependentFields` value. -/
def independentMatterGeneralLorentzConfiguration
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : MatterComponentIndex → Real)
    (fields : IndependentFields period hPeriod)
    (frame : OrderedTangentVectorFamily period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod)) :
    GlobalGeneralLorentzMatterConfiguration period hPeriod where
  metric := metric
  massSquared := massSquared
  fields := independentMatterComponentFamily period hPeriod fields
  frame := frame
  measure := measure

@[simp]
theorem independentMatterGeneralLorentzConfiguration_field
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : MatterComponentIndex → Real)
    (fields : IndependentFields period hPeriod)
    (frame : OrderedTangentVectorFamily period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (index : MatterComponentIndex) :
    (independentMatterGeneralLorentzConfiguration period hPeriod metric
      massSquared fields frame measure).fields index =
      independentMatterComponentFamily period hPeriod fields index :=
  rfl

/-- The same action along the explicit complete diagonal time orbit. -/
def completeTimeDiagonalMatterActionOrbit
    (configuration : GlobalGeneralLorentzMatterConfiguration period hPeriod)
    (parameter : Real) : Real :=
  sameConfigurationGeneralLorentzMatterAction period hPeriod
    (matterDiagonalDiffeomorphismPullback period hPeriod
      (effectiveTimeFlowDiffeomorph period hPeriod parameter) configuration)

@[simp]
theorem completeTimeDiagonalMatterActionOrbit_eq
    (configuration : GlobalGeneralLorentzMatterConfiguration period hPeriod)
    (parameter : Real) :
    completeTimeDiagonalMatterActionOrbit period hPeriod configuration
        parameter =
      sameConfigurationGeneralLorentzMatterAction period hPeriod
        configuration :=
  sameConfigurationGeneralLorentzMatterAction_diagonal_invariant period hPeriod
    (effectiveTimeFlowDiffeomorph period hPeriod parameter) configuration

/-- Integrated Noether identity for the complete time-translation subgroup. -/
theorem completeTimeDiagonalMatterActionOrbit_hasDerivAt_zero
    (configuration : GlobalGeneralLorentzMatterConfiguration period hPeriod) :
    HasDerivAt
      (completeTimeDiagonalMatterActionOrbit period hPeriod configuration)
      0 0 := by
  rw [show completeTimeDiagonalMatterActionOrbit period hPeriod configuration =
      fun _ : Real =>
        sameConfigurationGeneralLorentzMatterAction period hPeriod
          configuration by
    funext parameter
    exact completeTimeDiagonalMatterActionOrbit_eq period hPeriod configuration
      parameter]
  exact hasDerivAt_const (x := (0 : Real))
    (c := sameConfigurationGeneralLorentzMatterAction period hPeriod
      configuration)

/-- Concrete specialization of the Noether derivative to the eight fields
extracted from one `IndependentFields`. -/
theorem independentMatter_completeTimeDiagonalAction_hasDerivAt_zero
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : MatterComponentIndex → Real)
    (fields : IndependentFields period hPeriod)
    (frame : OrderedTangentVectorFamily period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod)) :
    HasDerivAt
      (completeTimeDiagonalMatterActionOrbit period hPeriod
        (independentMatterGeneralLorentzConfiguration period hPeriod metric
          massSquared fields frame measure)) 0 0 :=
  completeTimeDiagonalMatterActionOrbit_hasDerivAt_zero period hPeriod _

end

end P0EFTJanusMappingTorusGlobalMatterMultipletDiagonalDiffeomorphismNoether4D
end JanusFormal
