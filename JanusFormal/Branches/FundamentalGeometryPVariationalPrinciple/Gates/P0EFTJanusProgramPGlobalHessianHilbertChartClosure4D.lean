import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAMatterLLQuadraticChartBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateACommonHilbertChartTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAugmentedParametrix4D

/-!
# Terminal H14 route through one common Hilbert chart

When the physical local chart is continuously linearly equivalent to the
existing diagonal `L²` graph completion, H11 needs no separately supplied
seven-block extension.  The actual local physical Hessian transports directly
through the chart equivalence.  Together with the action-level H13 quadratic
identities and a finite-defect parametrix, this yields the terminal H14
certificate from one coherent chart packet.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianHilbertChartClosure4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 2400000

noncomputable section

open Set Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLQuadraticChartBridge4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateACommonHilbertChartTransport4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedFredholmSum4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedParametrix4D
open P0EFTJanusProgramPGlobalHessianClosure4D

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

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- H13 witness determined by the quadratic action identities. -/
def hilbertChartClosureSameAction
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (quadratic :
      ProgramPGlobalMinimalPhysicalLocalMatterLLQuadraticChartBridge4D period
        hPeriod configuration data analysis chart) :=
  programPGlobalMinimalPhysicalLocalMatterLLSameActionBridge_of_quadraticChart
    period hPeriod configuration data analysis chart quadratic

/-- H11 witness obtained by transporting the actual chart Hessian. -/
def hilbertChartClosurePhysical
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (quadratic :
      ProgramPGlobalMinimalPhysicalLocalMatterLLQuadraticChartBridge4D period
        hPeriod configuration data analysis chart)
    (hilbertChart : ProgramPGlobalMinimalPhysicalCommonHilbertChart4D period
      hPeriod configuration data analysis chart
        (hilbertChartClosureSameAction period hPeriod configuration data analysis
          chart quadratic)) :=
  globalCandidateASevenPhysicalCommonDomainExtension_of_hilbertChart period
    hPeriod configuration data analysis chart
      (hilbertChartClosureSameAction period hPeriod configuration data analysis
        chart quadratic) hilbertChart

/-- Compact terminal input packet for the common-Hilbert-chart route. -/
structure GlobalCandidateAHessianHilbertChartClosureInputs4D
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure) where
  quadraticChart :
    ProgramPGlobalMinimalPhysicalLocalMatterLLQuadraticChartBridge4D period
      hPeriod configuration data analysis chart
  hilbertChart :
    ProgramPGlobalMinimalPhysicalCommonHilbertChart4D period hPeriod
      configuration data analysis chart
        (hilbertChartClosureSameAction period hPeriod configuration data analysis
          chart quadraticChart)
  parametrix :
    GlobalCandidateAFaithfulAugmentedFiniteDefectParametrix4D period hPeriod
      configuration data analysis chart
        (hilbertChartClosureSameAction period hPeriod configuration data analysis
          chart quadraticChart)
        (hilbertChartClosurePhysical period hPeriod configuration data analysis
          chart quadraticChart hilbertChart)

/-- H12 estimate package extracted from the finite-defect parametrix. -/
def GlobalCandidateAHessianHilbertChartClosureInputs4D.estimates
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure}
    (inputs : GlobalCandidateAHessianHilbertChartClosureInputs4D period hPeriod
      configuration data analysis chart) :=
  globalCandidateAFaithfulAugmentedFredholmEstimates_of_parametrix period hPeriod
    configuration data analysis chart
      (hilbertChartClosureSameAction period hPeriod configuration data analysis
        chart inputs.quadraticChart)
      (hilbertChartClosurePhysical period hPeriod configuration data analysis
        chart inputs.quadraticChart inputs.hilbertChart)
      inputs.parametrix

/-- Terminal closure through one action-level quadratic chart, one common
Hilbert equivalence, and one finite-defect parametrix. -/
theorem global_candidateA_hessian_hilbertChart_closure_gate
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (einsteinScale : Real)
    (hBoundaryTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (inputs : GlobalCandidateAHessianHilbertChartClosureInputs4D period hPeriod
      configuration data analysis chart) :
    GlobalCandidateAHessianClosureCertificate4D period hPeriod configuration
      data analysis chart einsteinScale
        (hilbertChartClosureSameAction period hPeriod configuration data analysis
          chart inputs.quadraticChart)
        (hilbertChartClosurePhysical period hPeriod configuration data analysis
          chart inputs.quadraticChart inputs.hilbertChart)
        inputs.estimates :=
  global_candidateA_hessian_closure_gate period hPeriod configuration data
    analysis chart einsteinScale hBoundaryTransverse
      (hilbertChartClosureSameAction period hPeriod configuration data analysis
        chart inputs.quadraticChart)
      (hilbertChartClosurePhysical period hPeriod configuration data analysis
        chart inputs.quadraticChart inputs.hilbertChart)
      inputs.estimates

end
end P0EFTJanusProgramPGlobalHessianHilbertChartClosure4D
end JanusFormal
