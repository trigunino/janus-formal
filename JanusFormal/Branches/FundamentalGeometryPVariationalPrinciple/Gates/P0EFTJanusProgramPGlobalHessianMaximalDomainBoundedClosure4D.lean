import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCMatterDiracGreenMaximalDomain4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamily4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateASevenPhysicalBoundedExtension4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAugmentedParametrix4D

/-!
# Terminal H14 closure from the smooth SpinC maximal domain

This gate aligns the preferred terminal interface with the geometric SpinC
frontier.  It no longer accepts an independently supplied spectral coefficient
map, a maximal-domain package, or a separate same-action witness.  The smooth
matter graph realization is constructed from the single Green/formal-symmetry
identity for the smooth `2D + m²` expression; coefficient intertwining,
maximal-domain membership, operator agreement, Parseval and the same-action
pairing are all derived canonically.

The remaining H13, H11 and H12 inputs are the reduced minimal-physical local
family, one seven-block core bound, and one finite-defect parametrix.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianMaximalDomainBoundedClosure4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 2400000

noncomputable section

open Set Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedFredholmSum4D
open P0EFTJanusProgramPGlobalHessianClosure4D
open P0EFTJanusProgramPPrimitiveSpinCMatterSmoothMaximalDomain4D
open P0EFTJanusProgramPPrimitiveSpinCMatterDiracGreenMaximalDomain4D
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

/-- Canonical maximal-domain package derived from the single smooth
first-order Dirac Green/formal-symmetry identity. -/
def maximalDomainClosureSpinCDomain
    (massSquared : Real)
    (diracSymmetry :
      ProgramPPrimitiveSpinCSmoothDiracFormalSymmetryData4D period hPeriod) :=
  programPPrimitiveSpinCSmoothMaximalDomainData_of_diracFormalSymmetry
    period hPeriod massSquared diracSymmetry

/-- Canonical smooth matter graph realization from maximal-domain data alone. -/
def maximalDomainClosureMatterRealization
    (massSquared : Real)
    (domain : ProgramPPrimitiveSpinCSmoothMaximalDomainData4D period hPeriod
      massSquared) :=
  programPPrimitiveSpinCMatterSmoothGraphRealization_of_maximalDomain period
    hPeriod massSquared domain
      (programPPrimitiveSpinCMatterSmoothMaximalSameActionData_of_domain period
        hPeriod massSquared domain)

/-- Concrete chart data from the reduced local family. -/
def maximalDomainClosureChartData
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (domain : ProgramPPrimitiveSpinCSmoothMaximalDomainData4D period hPeriod
      couplings.matterMassSquared)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyReducedData4D period
      hPeriod configuration data analysis
        (maximalDomainClosureMatterRealization period hPeriod
          couplings.matterMassSquared domain)) :=
  globalCandidateAMinimalPhysicalActionChartData_of_reducedFamily period hPeriod
    configuration data analysis
      (maximalDomainClosureMatterRealization period hPeriod
        couplings.matterMassSquared domain) family

/-- Actual local chart on the D10-free minimal physical tangent. -/
def maximalDomainClosureChart
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (domain : ProgramPPrimitiveSpinCSmoothMaximalDomainData4D period hPeriod
      couplings.matterMassSquared)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyReducedData4D period
      hPeriod configuration data analysis
        (maximalDomainClosureMatterRealization period hPeriod
          couplings.matterMassSquared domain)) :=
  globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
    configuration data analysis
      (maximalDomainClosureChartData period hPeriod configuration data analysis
        domain family)

/-- H13 same-action bridge generated by the same local family. -/
def maximalDomainClosureMatterLLSameAction
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (domain : ProgramPPrimitiveSpinCSmoothMaximalDomainData4D period hPeriod
      couplings.matterMassSquared)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyReducedData4D period
      hPeriod configuration data analysis
        (maximalDomainClosureMatterRealization period hPeriod
          couplings.matterMassSquared domain)) :=
  globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
    configuration data analysis
      (maximalDomainClosureChartData period hPeriod configuration data analysis
        domain family)

/-- Fully aligned terminal inputs.  The former coefficient, maximal-domain
and same-action SpinC fields have disappeared: they are theorems of one smooth
first-order Dirac Green/formal-symmetry identity. -/
structure GlobalCandidateAHessianMaximalDomainBoundedInputs4D
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) where
  spinCDiracSymmetry :
    ProgramPPrimitiveSpinCSmoothDiracFormalSymmetryData4D period hPeriod
  family : ProgramPGlobalMinimalPhysicalLocalActionFamilyReducedData4D period
    hPeriod configuration data analysis
      (maximalDomainClosureMatterRealization period hPeriod
        couplings.matterMassSquared
        (maximalDomainClosureSpinCDomain period hPeriod
          couplings.matterMassSquared spinCDiracSymmetry))
  physicalBound :
    GlobalCandidateASevenPhysicalCoreBound4D period hPeriod configuration data
      analysis
        (maximalDomainClosureChart period hPeriod configuration data analysis
          (maximalDomainClosureSpinCDomain period hPeriod
            couplings.matterMassSquared spinCDiracSymmetry) family)
        (maximalDomainClosureMatterLLSameAction period hPeriod configuration data
          analysis
          (maximalDomainClosureSpinCDomain period hPeriod
            couplings.matterMassSquared spinCDiracSymmetry) family)
  parametrix :
    GlobalCandidateAFaithfulAugmentedFiniteDefectParametrix4D period hPeriod
      configuration data analysis
        (maximalDomainClosureChart period hPeriod configuration data analysis
          (maximalDomainClosureSpinCDomain period hPeriod
            couplings.matterMassSquared spinCDiracSymmetry) family)
        (maximalDomainClosureMatterLLSameAction period hPeriod configuration data
          analysis
          (maximalDomainClosureSpinCDomain period hPeriod
            couplings.matterMassSquared spinCDiracSymmetry) family)
        (globalCandidateASevenPhysicalCommonDomainExtension_of_bound period
          hPeriod configuration data analysis
          (maximalDomainClosureChart period hPeriod configuration data analysis
            (maximalDomainClosureSpinCDomain period hPeriod
              couplings.matterMassSquared spinCDiracSymmetry) family)
          (maximalDomainClosureMatterLLSameAction period hPeriod configuration
            data analysis
            (maximalDomainClosureSpinCDomain period hPeriod
              couplings.matterMassSquared spinCDiracSymmetry) family)
          physicalBound)

/-- Maximal-domain package canonically reconstructed from the stored smooth
first-order Dirac Green/formal-symmetry theorem. -/
def GlobalCandidateAHessianMaximalDomainBoundedInputs4D.spinCDomain
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    (inputs : GlobalCandidateAHessianMaximalDomainBoundedInputs4D period hPeriod
      configuration data analysis) :=
  maximalDomainClosureSpinCDomain period hPeriod couplings.matterMassSquared
    inputs.spinCDiracSymmetry

/-- H11 extension canonically obtained from the single dense-core bound. -/
def GlobalCandidateAHessianMaximalDomainBoundedInputs4D.physical
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    (inputs : GlobalCandidateAHessianMaximalDomainBoundedInputs4D period hPeriod
      configuration data analysis) :=
  globalCandidateASevenPhysicalCommonDomainExtension_of_bound period hPeriod
    configuration data analysis
      (maximalDomainClosureChart period hPeriod configuration data analysis
        inputs.spinCDomain inputs.family)
      (maximalDomainClosureMatterLLSameAction period hPeriod configuration data
        analysis inputs.spinCDomain inputs.family)
      inputs.physicalBound

/-- H12 estimates canonically obtained from the finite-defect parametrix. -/
def GlobalCandidateAHessianMaximalDomainBoundedInputs4D.estimates
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    (inputs : GlobalCandidateAHessianMaximalDomainBoundedInputs4D period hPeriod
      configuration data analysis) :=
  globalCandidateAFaithfulAugmentedFredholmEstimates_of_parametrix period hPeriod
    configuration data analysis
      (maximalDomainClosureChart period hPeriod configuration data analysis
        inputs.spinCDomain inputs.family)
      (maximalDomainClosureMatterLLSameAction period hPeriod configuration data
        analysis inputs.spinCDomain inputs.family)
      inputs.physical inputs.parametrix

/-- Preferred fully aligned H14 terminal gate. -/
theorem global_candidateA_hessian_maximalDomain_bounded_closure_gate
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
    (inputs : GlobalCandidateAHessianMaximalDomainBoundedInputs4D period hPeriod
      configuration data analysis) :
    GlobalCandidateAHessianClosureCertificate4D period hPeriod configuration
      data analysis
        (maximalDomainClosureChart period hPeriod configuration data analysis
          inputs.spinCDomain inputs.family)
        einsteinScale
        (maximalDomainClosureMatterLLSameAction period hPeriod configuration data
          analysis inputs.spinCDomain inputs.family)
        inputs.physical inputs.estimates :=
  global_candidateA_hessian_closure_gate period hPeriod configuration data
    analysis
      (maximalDomainClosureChart period hPeriod configuration data analysis
        inputs.spinCDomain inputs.family)
      einsteinScale hBoundaryTransverse
      (maximalDomainClosureMatterLLSameAction period hPeriod configuration data
        analysis inputs.spinCDomain inputs.family)
      inputs.physical inputs.estimates

end
end P0EFTJanusProgramPGlobalHessianMaximalDomainBoundedClosure4D
end JanusFormal
