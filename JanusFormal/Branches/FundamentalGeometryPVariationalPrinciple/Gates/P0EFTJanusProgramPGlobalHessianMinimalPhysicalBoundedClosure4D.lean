import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCMatterSmoothSpectralGraph4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamily4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateASevenPhysicalBoundedExtension4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAugmentedParametrix4D

/-!
# Minimal-physical H14 closure from one seven-block estimate

This route avoids both a supplied H11 form and a continuous equivalence between
the smooth physical tangent and its completion.  The seven physical blocks are
extended uniquely from one product bound on the existing dense diagonal core.

The terminal inputs are now:

* weighted Fourier--monopole data for smooth primitive SpinC fields;
* the reduced open Candidate-A family on the D10-free minimal tangent,
  including the two matter/LL graph-norm bounds;
* one product estimate for the seven physical Hessian blocks on the dense core;
* one finite-defect parametrix for the resulting augmented operator.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianMinimalPhysicalBoundedClosure4D

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
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedFredholmSum4D
open P0EFTJanusProgramPGlobalHessianClosure4D
open P0EFTJanusProgramPPrimitiveSpinCMatterSmoothSpectralGraph4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamily4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBoundedExtension4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedParametrix4D

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

/-- Spectral construction of the smooth matter graph realization. -/
def minimalBoundedClosureMatterRealization
    (massSquared : Real)
    (spectral : ProgramPPrimitiveSpinCMatterSmoothSpectralGraphData4D period
      hPeriod massSquared) :=
  programPPrimitiveSpinCMatterSmoothGraphRealization_of_spectral period hPeriod
    massSquared spectral

/-- Concrete chart data from the reduced local family. -/
def minimalBoundedClosureChartData
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (spectral : ProgramPPrimitiveSpinCMatterSmoothSpectralGraphData4D period
      hPeriod couplings.matterMassSquared)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyReducedData4D period
      hPeriod (measure := measure) configuration data analysis
        (minimalBoundedClosureMatterRealization period hPeriod
          couplings.matterMassSquared spectral)) :=
  globalCandidateAMinimalPhysicalActionChartData_of_reducedFamily period hPeriod
    (measure := measure) configuration data analysis
      (minimalBoundedClosureMatterRealization period hPeriod
        couplings.matterMassSquared spectral) family

/-- Actual minimal-physical local chart. -/
def minimalBoundedClosureChart
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (spectral : ProgramPPrimitiveSpinCMatterSmoothSpectralGraphData4D period
      hPeriod couplings.matterMassSquared)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyReducedData4D period
      hPeriod (measure := measure) configuration data analysis
        (minimalBoundedClosureMatterRealization period hPeriod
          couplings.matterMassSquared spectral)) :=
  globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
    configuration data analysis
      (minimalBoundedClosureChartData period hPeriod (measure := measure)
        configuration data analysis spectral family)

/-- H13 same-action witness constructed from the same local family. -/
def minimalBoundedClosureSameAction
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (spectral : ProgramPPrimitiveSpinCMatterSmoothSpectralGraphData4D period
      hPeriod couplings.matterMassSquared)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyReducedData4D period
      hPeriod (measure := measure) configuration data analysis
        (minimalBoundedClosureMatterRealization period hPeriod
          couplings.matterMassSquared spectral)) :=
  globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
    configuration data analysis
      (minimalBoundedClosureChartData period hPeriod (measure := measure)
        configuration data analysis spectral family)

/-- Complete terminal inputs after deriving every aggregate contract possible. -/
structure GlobalCandidateAHessianMinimalPhysicalBoundedInputs4D
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) where
  spectral : ProgramPPrimitiveSpinCMatterSmoothSpectralGraphData4D period
    hPeriod couplings.matterMassSquared
  family : ProgramPGlobalMinimalPhysicalLocalActionFamilyReducedData4D period
    hPeriod (measure := measure) configuration data analysis
      (minimalBoundedClosureMatterRealization period hPeriod
        couplings.matterMassSquared spectral)
  physicalBound :
    GlobalCandidateASevenPhysicalCoreBound4D period hPeriod configuration data
      analysis
        (minimalBoundedClosureChart period hPeriod (measure := measure)
          configuration data analysis spectral family)
        (minimalBoundedClosureSameAction period hPeriod (measure := measure)
          configuration data analysis spectral family)
  parametrix :
    GlobalCandidateAFaithfulAugmentedFiniteDefectParametrix4D period hPeriod
      configuration data analysis
        (minimalBoundedClosureChart period hPeriod (measure := measure)
          configuration data analysis spectral family)
        (minimalBoundedClosureSameAction period hPeriod (measure := measure)
          configuration data analysis spectral family)
        (globalCandidateASevenPhysicalCommonDomainExtension_of_bound period
          hPeriod (measure := measure) configuration data analysis
          (minimalBoundedClosureChart period hPeriod (measure := measure)
            configuration data analysis spectral family)
          (minimalBoundedClosureSameAction period hPeriod (measure := measure)
            configuration data analysis spectral family)
          physicalBound)

/-- Canonical H11 extension produced by the one dense-core estimate. -/
def GlobalCandidateAHessianMinimalPhysicalBoundedInputs4D.physical
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    (inputs : GlobalCandidateAHessianMinimalPhysicalBoundedInputs4D period
      hPeriod (measure := measure) configuration data analysis) :=
  globalCandidateASevenPhysicalCommonDomainExtension_of_bound period hPeriod
    (measure := measure) configuration data analysis
      (minimalBoundedClosureChart period hPeriod (measure := measure)
        configuration data analysis inputs.spectral inputs.family)
      (minimalBoundedClosureSameAction period hPeriod (measure := measure)
        configuration data analysis inputs.spectral inputs.family)
      inputs.physicalBound

/-- H12 estimate package derived from the finite-defect parametrix. -/
def GlobalCandidateAHessianMinimalPhysicalBoundedInputs4D.estimates
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    (inputs : GlobalCandidateAHessianMinimalPhysicalBoundedInputs4D period
      hPeriod (measure := measure) configuration data analysis) :=
  globalCandidateAFaithfulAugmentedFredholmEstimates_of_parametrix period hPeriod
    (measure := measure) configuration data analysis
      (minimalBoundedClosureChart period hPeriod (measure := measure)
        configuration data analysis inputs.spectral inputs.family)
      (minimalBoundedClosureSameAction period hPeriod (measure := measure)
        configuration data analysis inputs.spectral inputs.family)
      inputs.physical inputs.parametrix

/-- Terminal H14 certificate from spectral decay, the reduced local family,
one seven-block bound and one parametrix. -/
theorem global_candidateA_hessian_minimalPhysical_bounded_closure_gate
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (einsteinScale : Real)
    (hBoundaryTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (inputs : GlobalCandidateAHessianMinimalPhysicalBoundedInputs4D period
      hPeriod (measure := measure) configuration data analysis) :
    GlobalCandidateAHessianClosureCertificate4D period hPeriod configuration
      data analysis
        (minimalBoundedClosureChart period hPeriod (measure := measure)
          configuration data analysis inputs.spectral inputs.family)
        einsteinScale
        (minimalBoundedClosureSameAction period hPeriod (measure := measure)
          configuration data analysis inputs.spectral inputs.family)
        inputs.physical inputs.estimates :=
  global_candidateA_hessian_closure_gate period hPeriod configuration data
    analysis
      (minimalBoundedClosureChart period hPeriod (measure := measure)
        configuration data analysis inputs.spectral inputs.family)
      einsteinScale hBoundaryTransverse
      (minimalBoundedClosureSameAction period hPeriod (measure := measure)
        configuration data analysis inputs.spectral inputs.family)
      inputs.physical inputs.estimates

end
end P0EFTJanusProgramPGlobalHessianMinimalPhysicalBoundedClosure4D
end JanusFormal
