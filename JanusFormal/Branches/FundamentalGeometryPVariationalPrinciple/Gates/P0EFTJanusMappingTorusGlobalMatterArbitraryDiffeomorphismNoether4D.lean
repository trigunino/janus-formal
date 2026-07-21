import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalMatterMultipletDiagonalDiffeomorphismNoether4D

/-! # Matter Noether identity along arbitrary D8 diffeomorphism paths -/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGlobalMatterArbitraryDiffeomorphismNoether4D

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusDiagonalDiffeomorphismAction4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricPTIntegratedScalarAction4D
open P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D
open P0EFTJanusMappingTorusGlobalMatterMultipletDiagonalDiffeomorphismNoether4D

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

/-- The actual covariant eight-scalar action along any supplied path of smooth
self-diffeomorphisms.  No flow law or regularity of the path is assumed. -/
def arbitraryDiffeomorphismMatterActionOrbit
    (configuration : GlobalGeneralLorentzMatterConfiguration period hPeriod)
    (curve : Real → SpacetimeDiffeomorphism period hPeriod)
    (parameter : Real) : Real :=
  sameConfigurationGeneralLorentzMatterAction period hPeriod
    (matterDiagonalDiffeomorphismPullback period hPeriod (curve parameter)
      configuration)

/-- Finite diagonal covariance makes the whole orbit exactly constant. -/
@[simp] theorem arbitraryDiffeomorphismMatterActionOrbit_eq
    (configuration : GlobalGeneralLorentzMatterConfiguration period hPeriod)
    (curve : Real → SpacetimeDiffeomorphism period hPeriod)
    (parameter : Real) :
    arbitraryDiffeomorphismMatterActionOrbit period hPeriod configuration curve
        parameter =
      sameConfigurationGeneralLorentzMatterAction period hPeriod
        configuration :=
  sameConfigurationGeneralLorentzMatterAction_diagonal_invariant period hPeriod
    (curve parameter) configuration

/-- Integrated matter Noether identity at every point of every diagonal
diffeomorphism path. -/
theorem arbitraryDiffeomorphismMatterActionOrbit_hasDerivAt_zero
    (configuration : GlobalGeneralLorentzMatterConfiguration period hPeriod)
    (curve : Real → SpacetimeDiffeomorphism period hPeriod)
    (parameter : Real) :
    HasDerivAt
      (arbitraryDiffeomorphismMatterActionOrbit period hPeriod configuration curve)
      0 parameter := by
  rw [show arbitraryDiffeomorphismMatterActionOrbit period hPeriod configuration
      curve = fun _ : Real =>
        sameConfigurationGeneralLorentzMatterAction period hPeriod configuration by
    funext value
    exact arbitraryDiffeomorphismMatterActionOrbit_eq period hPeriod configuration
      curve value]
  exact hasDerivAt_const (x := parameter)
    (c := sameConfigurationGeneralLorentzMatterAction period hPeriod configuration)

/-- Derivative form of the same arbitrary-path identity. -/
theorem arbitraryDiffeomorphismMatterActionOrbit_deriv_eq_zero
    (configuration : GlobalGeneralLorentzMatterConfiguration period hPeriod)
    (curve : Real → SpacetimeDiffeomorphism period hPeriod)
    (parameter : Real) :
    deriv
      (arbitraryDiffeomorphismMatterActionOrbit period hPeriod configuration curve)
      parameter = 0 :=
  (arbitraryDiffeomorphismMatterActionOrbit_hasDerivAt_zero period hPeriod
    configuration curve parameter).deriv

/-- Specialization to the eight fields extracted from one `IndependentFields`. -/
theorem independentMatter_arbitraryDiffeomorphismAction_hasDerivAt_zero
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : MatterComponentIndex → Real)
    (fields : IndependentFields period hPeriod)
    (frame : OrderedTangentVectorFamily period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (curve : Real → SpacetimeDiffeomorphism period hPeriod)
    (parameter : Real) :
    HasDerivAt
      (arbitraryDiffeomorphismMatterActionOrbit period hPeriod
        (independentMatterGeneralLorentzConfiguration period hPeriod metric
          massSquared fields frame measure) curve) 0 parameter :=
  arbitraryDiffeomorphismMatterActionOrbit_hasDerivAt_zero period hPeriod _
    curve parameter

/-- Derivative form for the actual eight-component independent-field packet. -/
theorem independentMatter_arbitraryDiffeomorphismAction_deriv_eq_zero
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : MatterComponentIndex → Real)
    (fields : IndependentFields period hPeriod)
    (frame : OrderedTangentVectorFamily period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (curve : Real → SpacetimeDiffeomorphism period hPeriod)
    (parameter : Real) :
    deriv
      (arbitraryDiffeomorphismMatterActionOrbit period hPeriod
        (independentMatterGeneralLorentzConfiguration period hPeriod metric
          massSquared fields frame measure) curve) parameter = 0 :=
  (independentMatter_arbitraryDiffeomorphismAction_hasDerivAt_zero period hPeriod
    metric massSquared fields frame measure curve parameter).deriv

end
end P0EFTJanusMappingTorusGlobalMatterArbitraryDiffeomorphismNoether4D
end JanusFormal
