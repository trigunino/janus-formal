import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGlobalMatterMultipletActualEulerHessian4D

namespace JanusFormal
namespace P0EFTJanusIndependentMatterMetricActionData4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothDiagonalLorentzFields4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusLinearizedDiffeomorphismBRST4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarAction4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarVariation4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarWeakJacobiRiesz4D
open P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

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

/-- Select the metric magnitude from the same plus/minus sector as a matter
coordinate of `IndependentFields`. -/
def independentMatterMagnitude
    (fields : IndependentFields period hPeriod) (sector : Fin 2) :
    SmoothQuotientField period hPeriod (Fin 4 → Real) :=
  if sector = 0 then fields.metrics.plusMagnitude
  else fields.metrics.minusMagnitude

theorem independentMatterMagnitude_pos
    (fields : IndependentFields period hPeriod) (sector : Fin 2)
    (point : EffectiveQuotient period hPeriod) (index : Fin 4) :
    0 < independentMatterMagnitude period hPeriod fields sector point index := by
  by_cases hSector : sector = 0
  · simp [independentMatterMagnitude, hSector, fields.metrics.plus_pos point index]
  · simp [independentMatterMagnitude, hSector, fields.metrics.minus_pos point index]

/-- Exact remaining analytic input for putting all eight matter coordinates
on the two metrics stored by one Program-P configuration. -/
structure IndependentMatterMetricActionContract
    (fields : IndependentFields period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod)) where
  massSquared : MatterComponentIndex → Real
  pair_integrable : ∀ (component : MatterComponentIndex)
      (first second : GlobalScalarTestSpace period hPeriod),
    Integrable
      (globalHolonomicScalarJacobiDensity period hPeriod
        (massSquared component)
        (independentMatterMagnitude period hPeriod fields component.1)
        first second) measure

/-- Canonical eight-component action data using the actual sector metric and
one common measure.  Only the displayed integrability contract is supplied. -/
def independentMatterMetricActionData
    (fields : IndependentFields period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (contract : IndependentMatterMetricActionContract period hPeriod fields
      measure) : MatterMultipletActionData period hPeriod :=
  fun component =>
    { massSquared := contract.massSquared component
      magnitude := independentMatterMagnitude period hPeriod fields component.1
      measure := measure
      pair_integrable := contract.pair_integrable component }

@[simp] theorem independentMatterMetricActionData_magnitude
    (fields : IndependentFields period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (contract : IndependentMatterMetricActionContract period hPeriod fields
      measure) (component : MatterComponentIndex) :
    (independentMatterMetricActionData period hPeriod fields measure contract
      component).magnitude =
      independentMatterMagnitude period hPeriod fields component.1 :=
  rfl

@[simp] theorem independentMatterMetricActionData_measure
    (fields : IndependentFields period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (contract : IndependentMatterMetricActionContract period hPeriod fields
      measure) (component : MatterComponentIndex) :
    (independentMatterMetricActionData period hPeriod fields measure contract
      component).measure = measure :=
  rfl

/-- The resulting action is literally the sum of the eight matter coordinates
with the metric selected from their own sector in the same configuration. -/
theorem globalIndependentMatterAction_eq_sectorMetric_sum
    (fields : IndependentFields period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (contract : IndependentMatterMetricActionContract period hPeriod fields
      measure) :
    globalIndependentMatterAction period hPeriod
        (independentMatterMetricActionData period hPeriod fields measure contract)
        fields =
      ∑ component : MatterComponentIndex,
        globalHolonomicScalarAction period hPeriod
          (contract.massSquared component)
          (independentMatterMagnitude period hPeriod fields component.1)
          (independentMatterScalar period hPeriod fields component.1 component.2)
          measure := by
  rfl

end

end P0EFTJanusIndependentMatterMetricActionData4D
end JanusFormal
