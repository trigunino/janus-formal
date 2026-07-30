import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCovariantAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D

/-!
# Global Candidate-A Abelian gauge-fixed action

This gate attaches the paired Abelian BRST gauge fermion to the genuine
Candidate-A metrics, Maxwell potentials and typed nonminimal fields.
No variational chart or analytic realization is added here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) :=
  borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- The two actual Candidate-A metrics, selected by physical outer sector. -/
def globalCandidateAMetricBySector
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace) :
    Sector → SmoothGeneralLorentzMetric period hPeriod
  | .plus => data.plusGravity.metric.metric
  | .minus => data.minusGravity.metric.metric

/-- The two actual intrinsic Maxwell potentials, selected by outer sector. -/
def globalCandidateAPotentialBySector
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace) :
    Sector → SmoothAbelianGaugePotential period hPeriod
  | .plus => data.plusMaxwell.potential
  | .minus => data.minusMaxwell.potential

theorem globalCandidateAMetricBySector_plus_eq
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace) :
    globalCandidateAMetricBySector period hPeriod data .plus =
      configuration.geometry.plusMetric :=
  data.plusMetric_eq

theorem globalCandidateAMetricBySector_minus_eq
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace) :
    globalCandidateAMetricBySector period hPeriod data .minus =
      configuration.geometry.minusMetric :=
  data.minusMetric_eq

/-- Faithful paired BRST state over one gauge-fixed Candidate-A field. -/
def globalCandidateAPairedAbelianBRSTState
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod
      configuration.physical couplings NonNullFace NullFace) :
    GlobalPairedAbelianBRSTState period hPeriod where
  potential := globalCandidateAPotentialBySector period hPeriod data
  nonminimal := configuration.nonminimal.abelian

@[simp]
theorem globalCandidateAPairedAbelianBRSTState_potential
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod
      configuration.physical couplings NonNullFace NullFace)
    (sector : Sector) :
    (globalCandidateAPairedAbelianBRSTState period hPeriod
      configuration data).potential sector =
      globalCandidateAPotentialBySector period hPeriod data sector :=
  rfl

@[simp]
theorem globalCandidateAPairedAbelianBRSTState_nonminimal
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod
      configuration.physical couplings NonNullFace NullFace)
    (sector : Sector) :
    (globalCandidateAPairedAbelianBRSTState period hPeriod
      configuration data).nonminimal sector =
      configuration.nonminimal.abelian sector :=
  by
    rfl

theorem globalCandidateAPairedAbelianBRSTState_plusGauge_eq
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod
      configuration.physical couplings NonNullFace NullFace)
    (point : EffectiveQuotient period hPeriod)
    (index : Fin 4) (component : Fin 2) :
    ((globalCandidateAPairedAbelianBRSTState period hPeriod
        configuration data).potential .plus).toFun component point
          (data.plusGravity.metric.frame index point) =
      configuration.physical.coefficientFields.gauge.1 point
        (index, component) :=
  by
    simpa [globalCandidateAPairedAbelianBRSTState,
      globalCandidateAPotentialBySector] using
      data.plusGauge_eq point index component

theorem globalCandidateAPairedAbelianBRSTState_minusGauge_eq
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod
      configuration.physical couplings NonNullFace NullFace)
    (point : EffectiveQuotient period hPeriod)
    (index : Fin 4) (component : Fin 2) :
    ((globalCandidateAPairedAbelianBRSTState period hPeriod
        configuration data).potential .minus).toFun component point
          (data.minusGravity.metric.frame index point) =
      configuration.physical.coefficientFields.gauge.2 point
        (index, component) :=
  by
    simpa [globalCandidateAPairedAbelianBRSTState,
      globalCandidateAPotentialBySector] using
      data.minusGauge_eq point index component

/-- Candidate-A covariant action plus its genuine paired Abelian `sΨ`. -/
def globalCandidateAAbelianGaugeFixedAction
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod
      configuration.physical couplings NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure] : Real :=
  globalCandidateACovariantAction period hPeriod data measure +
    globalPairedAbelianGaugeFermionBRSTAction period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
      (globalCandidateAPairedAbelianBRSTState period hPeriod
        configuration data)
      measure

theorem globalCandidateAAbelianGaugeFixedAction_eq
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod
      configuration.physical couplings NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure] :
    globalCandidateAAbelianGaugeFixedAction period hPeriod
        configuration data measure =
      globalCandidateACovariantAction period hPeriod data measure +
        globalPairedAbelianGaugeFermionBRSTAction period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          (globalCandidateAPairedAbelianBRSTState period hPeriod
            configuration data)
          measure :=
  rfl

end
end P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
end JanusFormal
