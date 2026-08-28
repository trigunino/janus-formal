import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCMatterSmoothSpectralGraph4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChartConstructor4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalHilbertChart4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAugmentedParametrix4D

/-!
# Minimal-physical constructive closure of the global Hessian

This is the most concrete H14 interface currently available.  The local chart
model is the corrected D10-free minimal physical tangent itself.  Its matter
projection is constructed from geometric Fourier decay, its LL projection is
the existing three-slot smooth graph embedding, its seven physical blocks are
transported through the common Hilbert norm, and Fredholmness is obtained from
a finite-defect parametrix.

The remaining inputs are therefore genuine analytic theorems rather than
aggregate Hessian contracts:

* weighted Fourier--monopole decay for smooth primitive SpinC sections;
* an open `C²` Candidate-A family on the minimal physical tangent with exact
  matter and LL action identities;
* identification of that tangent norm with the unique common graph Hilbert
  norm;
* a finite-defect parametrix for the augmented operator.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianMinimalPhysicalConstructiveClosure4D

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
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedFredholmSum4D
open P0EFTJanusProgramPGlobalHessianClosure4D
open P0EFTJanusProgramPPrimitiveSpinCMatterSmoothSpectralGraph4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChartConstructor4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalHilbertChart4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedParametrix4D

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

/-- Canonical smooth matter graph realization obtained from the spectral data. -/
def minimalPhysicalClosureMatterRealization
    (massSquared : Real)
    (spectral : ProgramPPrimitiveSpinCMatterSmoothSpectralGraphData4D period
      hPeriod massSquared) :=
  programPPrimitiveSpinCMatterSmoothGraphRealization_of_spectral period hPeriod
    massSquared spectral

/-- Concrete chart data assembled from the local family and spectral graph. -/
def minimalPhysicalClosureChartData
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
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyData4D period hPeriod
      (measure := measure) configuration data analysis
        (minimalPhysicalClosureMatterRealization period hPeriod
          couplings.matterMassSquared spectral)) :=
  globalCandidateAMinimalPhysicalActionChartData_of_family period hPeriod
    (measure := measure) configuration data analysis
      (minimalPhysicalClosureMatterRealization period hPeriod
        couplings.matterMassSquared spectral)
      family

/-- The resulting local variational chart. -/
def minimalPhysicalClosureChart
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
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyData4D period hPeriod
      (measure := measure) configuration data analysis
        (minimalPhysicalClosureMatterRealization period hPeriod
          couplings.matterMassSquared spectral)) :=
  globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
    configuration data analysis
      (minimalPhysicalClosureChartData period hPeriod configuration data analysis
        spectral family)

/-- H13 same-action witness determined by the same minimal physical family. -/
def minimalPhysicalClosureSameAction
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
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyData4D period hPeriod
      (measure := measure) configuration data analysis
        (minimalPhysicalClosureMatterRealization period hPeriod
          couplings.matterMassSquared spectral)) :=
  globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
    configuration data analysis
      (minimalPhysicalClosureChartData period hPeriod configuration data analysis
        spectral family)

/-- Complete analytic input packet after all formal reductions. -/
structure GlobalCandidateAHessianMinimalPhysicalConstructiveInputs4D
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
  family : ProgramPGlobalMinimalPhysicalLocalActionFamilyData4D period hPeriod
    (measure := measure) configuration data analysis
      (minimalPhysicalClosureMatterRealization period hPeriod
        couplings.matterMassSquared spectral)
  hilbert : ProgramPGlobalMinimalPhysicalHilbertModel4D period hPeriod
    (measure := measure) configuration data analysis
      (minimalPhysicalClosureChart period hPeriod configuration data analysis
        spectral family)
      (minimalPhysicalClosureSameAction period hPeriod configuration data
        analysis spectral family)
  parametrix :
    GlobalCandidateAFaithfulAugmentedFiniteDefectParametrix4D period hPeriod
      configuration data analysis
        (minimalPhysicalClosureChart period hPeriod configuration data analysis
          spectral family)
        (minimalPhysicalClosureSameAction period hPeriod configuration data
          analysis spectral family)
        (globalCandidateAMinimalPhysicalSevenBlockExtension period hPeriod
          configuration data analysis
          (minimalPhysicalClosureChartData period hPeriod configuration data
            analysis spectral family)
          (minimalPhysicalClosureSameAction period hPeriod configuration data
            analysis spectral family)
          hilbert)

/-- H11 extension canonically extracted from the common Hilbert norm. -/
def GlobalCandidateAHessianMinimalPhysicalConstructiveInputs4D.physical
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    (inputs : GlobalCandidateAHessianMinimalPhysicalConstructiveInputs4D period
      hPeriod (measure := measure) configuration data analysis) :=
  globalCandidateAMinimalPhysicalSevenBlockExtension period hPeriod
    configuration data analysis
      (minimalPhysicalClosureChartData period hPeriod configuration data analysis
        inputs.spectral inputs.family)
      (minimalPhysicalClosureSameAction period hPeriod configuration data
        analysis inputs.spectral inputs.family)
      inputs.hilbert

/-- H12 estimates obtained from the displayed finite-defect parametrix. -/
def GlobalCandidateAHessianMinimalPhysicalConstructiveInputs4D.estimates
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    (inputs : GlobalCandidateAHessianMinimalPhysicalConstructiveInputs4D period
      hPeriod (measure := measure) configuration data analysis) :=
  globalCandidateAFaithfulAugmentedFredholmEstimates_of_parametrix period hPeriod
    configuration data analysis
      (minimalPhysicalClosureChart period hPeriod configuration data analysis
        inputs.spectral inputs.family)
      (minimalPhysicalClosureSameAction period hPeriod configuration data
        analysis inputs.spectral inputs.family)
      inputs.physical
      inputs.parametrix

/-- Terminal H14 certificate from the four remaining analytic inputs. -/
theorem global_candidateA_hessian_minimalPhysical_constructive_closure_gate
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
    (inputs : GlobalCandidateAHessianMinimalPhysicalConstructiveInputs4D period
      hPeriod (measure := measure) configuration data analysis) :
    GlobalCandidateAHessianClosureCertificate4D period hPeriod configuration
      data analysis
        (minimalPhysicalClosureChart period hPeriod configuration data analysis
          inputs.spectral inputs.family)
        einsteinScale
        (minimalPhysicalClosureSameAction period hPeriod configuration data
          analysis inputs.spectral inputs.family)
        inputs.physical inputs.estimates :=
  global_candidateA_hessian_closure_gate period hPeriod configuration data
    analysis
      (minimalPhysicalClosureChart period hPeriod configuration data analysis
        inputs.spectral inputs.family)
      einsteinScale hBoundaryTransverse
      (minimalPhysicalClosureSameAction period hPeriod configuration data
        analysis inputs.spectral inputs.family)
      inputs.physical inputs.estimates

end
end P0EFTJanusProgramPGlobalHessianMinimalPhysicalConstructiveClosure4D
end JanusFormal
