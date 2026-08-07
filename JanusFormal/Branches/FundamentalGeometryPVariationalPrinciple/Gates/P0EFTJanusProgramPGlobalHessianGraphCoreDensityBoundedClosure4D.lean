import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianMaximalDomainBoundedClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCMatterFiniteDiracGreen4D

/-!
# Terminal H14 closure from SpinC graph-core density

The preceding maximal-domain terminal gate still accepted the global smooth
Dirac Green identity as one analytic input.  The finite signed Fourier core is
now proved formally symmetric without assumptions, so the preferred SpinC
input is the sharper graph-core statement: every smooth primitive section is
a simultaneous `L²` limit of finite signed packets before and after applying
`2D + m²`.

This file derives the global Green identity, maximal-domain membership,
operator agreement and same-action matter graph from that one density theorem,
then reuses the existing H13/H11/H12 terminal assembly unchanged.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianGraphCoreDensityBoundedClosure4D

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
open P0EFTJanusProgramPPrimitiveSpinCMatterDiracGreenMaximalDomain4D
open P0EFTJanusProgramPPrimitiveSpinCMatterFiniteDiracGreen4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamily4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBoundedExtension4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedParametrix4D
open P0EFTJanusProgramPGlobalHessianMaximalDomainBoundedClosure4D

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

/-- Formal-symmetry datum canonically obtained from graph-core density. -/
def graphCoreDensityClosureDiracSymmetry
    (massSquared : Real)
    (density : ProgramPPrimitiveSpinCSmoothDiracGraphCoreDensityData4D period
      hPeriod massSquared) :=
  programPPrimitiveSpinCSmoothDiracFormalSymmetryData_of_graphCoreDensity
    period hPeriod massSquared density

/-- Matter graph realization obtained from the same graph-core density input. -/
def graphCoreDensityClosureMatterRealization
    (massSquared : Real)
    (density : ProgramPPrimitiveSpinCSmoothDiracGraphCoreDensityData4D period
      hPeriod massSquared) :=
  maximalDomainClosureMatterRealization period hPeriod massSquared
    (graphCoreDensityClosureDiracSymmetry period hPeriod massSquared density)

/-- Local chart data induced by the reduced Candidate-A family and the
canonical matter realization above. -/
def graphCoreDensityClosureChartData
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (density : ProgramPPrimitiveSpinCSmoothDiracGraphCoreDensityData4D period
      hPeriod couplings.matterMassSquared)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyReducedData4D period
      hPeriod configuration data analysis
        (graphCoreDensityClosureMatterRealization period hPeriod
          couplings.matterMassSquared density)) :=
  maximalDomainClosureChartData period hPeriod configuration data analysis
    (graphCoreDensityClosureDiracSymmetry period hPeriod
      couplings.matterMassSquared density) family

/-- Actual local chart on the D10-free minimal physical tangent. -/
def graphCoreDensityClosureChart
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (density : ProgramPPrimitiveSpinCSmoothDiracGraphCoreDensityData4D period
      hPeriod couplings.matterMassSquared)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyReducedData4D period
      hPeriod configuration data analysis
        (graphCoreDensityClosureMatterRealization period hPeriod
          couplings.matterMassSquared density)) :=
  maximalDomainClosureChart period hPeriod configuration data analysis
    (graphCoreDensityClosureDiracSymmetry period hPeriod
      couplings.matterMassSquared density) family

/-- H13 same-action bridge generated by the same local family. -/
def graphCoreDensityClosureMatterLLSameAction
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (density : ProgramPPrimitiveSpinCSmoothDiracGraphCoreDensityData4D period
      hPeriod couplings.matterMassSquared)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyReducedData4D period
      hPeriod configuration data analysis
        (graphCoreDensityClosureMatterRealization period hPeriod
          couplings.matterMassSquared density)) :=
  maximalDomainClosureMatterLLSameAction period hPeriod configuration data
    analysis
      (graphCoreDensityClosureDiracSymmetry period hPeriod
        couplings.matterMassSquared density) family

/-- Fully reduced terminal inputs.  The SpinC field is now one graph-core
density theorem rather than a global Green identity. -/
structure GlobalCandidateAHessianGraphCoreDensityBoundedInputs4D
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) where
  spinCGraphCoreDensity :
    ProgramPPrimitiveSpinCSmoothDiracGraphCoreDensityData4D period hPeriod
      couplings.matterMassSquared
  family : ProgramPGlobalMinimalPhysicalLocalActionFamilyReducedData4D period
    hPeriod configuration data analysis
      (graphCoreDensityClosureMatterRealization period hPeriod
        couplings.matterMassSquared spinCGraphCoreDensity)
  physicalBound :
    GlobalCandidateASevenPhysicalCoreBound4D period hPeriod configuration data
      analysis
        (graphCoreDensityClosureChart period hPeriod configuration data analysis
          spinCGraphCoreDensity family)
        (graphCoreDensityClosureMatterLLSameAction period hPeriod configuration
          data analysis spinCGraphCoreDensity family)
  parametrix :
    GlobalCandidateAFaithfulAugmentedFiniteDefectParametrix4D period hPeriod
      configuration data analysis
        (graphCoreDensityClosureChart period hPeriod configuration data analysis
          spinCGraphCoreDensity family)
        (graphCoreDensityClosureMatterLLSameAction period hPeriod configuration
          data analysis spinCGraphCoreDensity family)
        (globalCandidateASevenPhysicalCommonDomainExtension_of_bound period
          hPeriod configuration data analysis
          (graphCoreDensityClosureChart period hPeriod configuration data
            analysis spinCGraphCoreDensity family)
          (graphCoreDensityClosureMatterLLSameAction period hPeriod
            configuration data analysis spinCGraphCoreDensity family)
          physicalBound)

/-- Repackage the reduced inputs for the already established maximal-domain
terminal gate. -/
def GlobalCandidateAHessianGraphCoreDensityBoundedInputs4D.maximalInputs
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    (inputs : GlobalCandidateAHessianGraphCoreDensityBoundedInputs4D period
      hPeriod configuration data analysis) :
    GlobalCandidateAHessianMaximalDomainBoundedInputs4D period hPeriod
      configuration data analysis where
  spinCDiracSymmetry :=
    graphCoreDensityClosureDiracSymmetry period hPeriod
      couplings.matterMassSquared inputs.spinCGraphCoreDensity
  family := inputs.family
  physicalBound := inputs.physicalBound
  parametrix := inputs.parametrix

/-- Preferred H14 terminal gate from graph-core density, one reduced local
family, one seven-block estimate and one finite-defect parametrix. -/
theorem global_candidateA_hessian_graphCoreDensity_bounded_closure_gate
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
    (inputs : GlobalCandidateAHessianGraphCoreDensityBoundedInputs4D period
      hPeriod configuration data analysis) :
    GlobalCandidateAHessianClosureCertificate4D period hPeriod configuration
      data analysis
        (graphCoreDensityClosureChart period hPeriod configuration data analysis
          inputs.spinCGraphCoreDensity inputs.family)
        einsteinScale
        (graphCoreDensityClosureMatterLLSameAction period hPeriod configuration
          data analysis inputs.spinCGraphCoreDensity inputs.family)
        (inputs.maximalInputs period hPeriod).physical
        (inputs.maximalInputs period hPeriod).estimates :=
  global_candidateA_hessian_maximalDomain_bounded_closure_gate period hPeriod
    configuration data analysis einsteinScale hBoundaryTransverse
      (inputs.maximalInputs period hPeriod)

end
end P0EFTJanusProgramPGlobalHessianGraphCoreDensityBoundedClosure4D
end JanusFormal
