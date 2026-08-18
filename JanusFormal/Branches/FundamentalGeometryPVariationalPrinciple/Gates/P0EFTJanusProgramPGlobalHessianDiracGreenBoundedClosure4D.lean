import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianMaximalDomainBoundedClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCDiracGreenClosure4D

/-!
# Terminal H14 closure after unconditional SpinC Green symmetry

The global primitive SpinC Green identity is now a theorem of the implemented
throat geometry.  It constructs, for every real mass, the maximal matter graph,
operator agreement, Parseval identity and same-action pairing.  The H14
terminal interface therefore no longer accepts any SpinC analytic input.

Only three work packets remain:

* the reduced open Candidate-A family on the actual D10-free tangent;
* one common-domain bound for the seven retained physical blocks;
* one finite-defect parametrix for the augmented stationary operator.

No action, completion, field, coupling, boundary condition or D10 direction is
introduced in this reduction.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianDiracGreenBoundedClosure4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
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
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamily4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBoundedExtension4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedParametrix4D
open P0EFTJanusProgramPGlobalHessianMaximalDomainBoundedClosure4D
open P0EFTJanusProgramPPrimitiveSpinCDiracGreenClosure4D

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

/-- Canonical maximal-domain package produced by the geometric Green theorem. -/
def diracGreenClosureSpinCDomain
    (massSquared : Real) :=
  maximalDomainClosureSpinCDomain period hPeriod massSquared
    (programPPrimitiveSpinCSmoothDiracFormalSymmetryData4D period hPeriod)

/-- Canonical smooth matter graph for one mass. -/
def diracGreenClosureMatterRealization
    (massSquared : Real) :=
  maximalDomainClosureMatterRealization period hPeriod massSquared
    (diracGreenClosureSpinCDomain period hPeriod massSquared)

/-- Concrete local chart data from the reduced Candidate-A family. -/
def diracGreenClosureChartData
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyReducedData4D period
      hPeriod (measure := measure) configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared)) :=
  maximalDomainClosureChartData period hPeriod configuration data analysis
    (measure := measure)
    (diracGreenClosureSpinCDomain period hPeriod couplings.matterMassSquared)
    family

/-- Actual local chart on the D10-free minimal physical tangent. -/
def diracGreenClosureChart
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyReducedData4D period
      hPeriod (measure := measure) configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared)) :=
  maximalDomainClosureChart period hPeriod configuration data analysis
    (measure := measure)
    (diracGreenClosureSpinCDomain period hPeriod couplings.matterMassSquared)
    family

/-- H13 same-action bridge generated from the same local family. -/
def diracGreenClosureMatterLLSameAction
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyReducedData4D period
      hPeriod (measure := measure) configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared)) :=
  maximalDomainClosureMatterLLSameAction period hPeriod configuration data
    analysis (measure := measure)
      (diracGreenClosureSpinCDomain period hPeriod couplings.matterMassSquared)
      family

/-- Fully reduced terminal input package.  There is no SpinC field: all SpinC
objects are theorems of the geometric Green closure. -/
structure GlobalCandidateAHessianDiracGreenBoundedInputs4D
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) where
  family : ProgramPGlobalMinimalPhysicalLocalActionFamilyReducedData4D period
    hPeriod (measure := measure) configuration data analysis
      (diracGreenClosureMatterRealization period hPeriod
        couplings.matterMassSquared)
  physicalBound :
    GlobalCandidateASevenPhysicalCoreBound4D period hPeriod configuration data
      analysis
        (diracGreenClosureChart period hPeriod configuration data analysis
          family)
        (diracGreenClosureMatterLLSameAction period hPeriod configuration data
          analysis family)
  parametrix :
    GlobalCandidateAFaithfulAugmentedFiniteDefectParametrix4D period hPeriod
      configuration data analysis
        (diracGreenClosureChart period hPeriod configuration data analysis
          family)
        (diracGreenClosureMatterLLSameAction period hPeriod configuration data
          analysis family)
        (globalCandidateASevenPhysicalCommonDomainExtension_of_bound period
          hPeriod configuration data analysis
          (diracGreenClosureChart period hPeriod configuration data analysis
            family)
          (diracGreenClosureMatterLLSameAction period hPeriod configuration data
            analysis family)
          physicalBound)

/-- Repackage the three remaining fields into the preceding maximal-domain
terminal interface. -/
def GlobalCandidateAHessianDiracGreenBoundedInputs4D.maximalInputs
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    (inputs : GlobalCandidateAHessianDiracGreenBoundedInputs4D period hPeriod
      (measure := measure) configuration data analysis) :
    GlobalCandidateAHessianMaximalDomainBoundedInputs4D period hPeriod
      (measure := measure) configuration data analysis where
  spinCDiracSymmetry :=
    programPPrimitiveSpinCSmoothDiracFormalSymmetryData4D period hPeriod
  family := inputs.family
  physicalBound := inputs.physicalBound
  parametrix := inputs.parametrix

/-- H11 physical extension produced from the stored dense-core bound. -/
def GlobalCandidateAHessianDiracGreenBoundedInputs4D.physical
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    (inputs : GlobalCandidateAHessianDiracGreenBoundedInputs4D period hPeriod
      (measure := measure) configuration data analysis) :=
  (inputs.maximalInputs period hPeriod).physical period hPeriod

/-- H12 Fredholm estimate package produced from the finite-defect
parametrix. -/
def GlobalCandidateAHessianDiracGreenBoundedInputs4D.estimates
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    (inputs : GlobalCandidateAHessianDiracGreenBoundedInputs4D period hPeriod
      (measure := measure) configuration data analysis) :=
  (inputs.maximalInputs period hPeriod).estimates period hPeriod

/-- Preferred H14 terminal gate after complete removal of the SpinC input. -/
theorem global_candidateA_hessian_diracGreen_bounded_closure_gate
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
    (inputs : GlobalCandidateAHessianDiracGreenBoundedInputs4D period hPeriod
      (measure := measure) configuration data analysis) :
    GlobalCandidateAHessianClosureCertificate4D period hPeriod configuration
      data analysis
        (diracGreenClosureChart period hPeriod configuration data analysis
          inputs.family)
        einsteinScale
        (diracGreenClosureMatterLLSameAction period hPeriod configuration data
          analysis inputs.family)
        inputs.physical inputs.estimates :=
  global_candidateA_hessian_maximalDomain_bounded_closure_gate period hPeriod
    configuration data analysis einsteinScale hBoundaryTransverse
      (inputs.maximalInputs period hPeriod)

end
end P0EFTJanusProgramPGlobalHessianDiracGreenBoundedClosure4D
end JanusFormal
