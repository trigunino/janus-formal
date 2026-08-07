import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianGraphCoreDensityBoundedClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCMatterFirstOrderGraphCoreDensity4D

/-!
# Terminal H14 closure from the first-order SpinC graph core

The preceding graph-core terminal gate still indexed its SpinC input by the
matter mass because it approximated the complete Hessian `2D + m²`.  The
first-order reduction proves that a single mass-independent core theorem for
`D` produces that datum for every mass.  This file transports that reduction
through the existing H13/H11/H12 assembly.

The preferred SpinC input is now independent of the Candidate-A couplings.  No
new action, completion, boundary condition or D10 direction is introduced.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianFirstOrderGraphCoreDensityBoundedClosure4D

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
open P0EFTJanusProgramPPrimitiveSpinCMatterFirstOrderGraphCoreDensity4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamily4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBoundedExtension4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedParametrix4D
open P0EFTJanusProgramPGlobalHessianGraphCoreDensityBoundedClosure4D

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

/-- Specialize the one first-order density theorem to the complete Hessian at
an arbitrary real mass. -/
def firstOrderGraphCoreMassDensity
    (massSquared : Real)
    (density :
      ProgramPPrimitiveSpinCSmoothFirstOrderDiracGraphCoreDensityData4D period
        hPeriod) :=
  programPPrimitiveSpinCSmoothDiracGraphCoreDensityData_of_firstOrder period
    hPeriod massSquared density

/-- Matter graph realization constructed from the mass-independent input. -/
def firstOrderGraphCoreMatterRealization
    (massSquared : Real)
    (density :
      ProgramPPrimitiveSpinCSmoothFirstOrderDiracGraphCoreDensityData4D period
        hPeriod) :=
  graphCoreDensityClosureMatterRealization period hPeriod massSquared
    (firstOrderGraphCoreMassDensity period hPeriod massSquared density)

/-- Concrete local chart produced by the same first-order SpinC input and the
reduced Candidate-A family. -/
def firstOrderGraphCoreClosureChart
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (density :
      ProgramPPrimitiveSpinCSmoothFirstOrderDiracGraphCoreDensityData4D period
        hPeriod)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyReducedData4D period
      hPeriod configuration data analysis
        (firstOrderGraphCoreMatterRealization period hPeriod
          couplings.matterMassSquared density)) :=
  graphCoreDensityClosureChart period hPeriod configuration data analysis
    (firstOrderGraphCoreMassDensity period hPeriod couplings.matterMassSquared
      density) family

/-- H13 same-action bridge obtained from the same mass-independent SpinC core
and local family. -/
def firstOrderGraphCoreClosureMatterLLSameAction
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (density :
      ProgramPPrimitiveSpinCSmoothFirstOrderDiracGraphCoreDensityData4D period
        hPeriod)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyReducedData4D period
      hPeriod configuration data analysis
        (firstOrderGraphCoreMatterRealization period hPeriod
          couplings.matterMassSquared density)) :=
  graphCoreDensityClosureMatterLLSameAction period hPeriod configuration data
    analysis
      (firstOrderGraphCoreMassDensity period hPeriod couplings.matterMassSquared
        density) family

/-- Fully reduced terminal inputs with a single mass-independent SpinC field. -/
structure GlobalCandidateAHessianFirstOrderGraphCoreDensityBoundedInputs4D
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) where
  spinCFirstOrderGraphCoreDensity :
    ProgramPPrimitiveSpinCSmoothFirstOrderDiracGraphCoreDensityData4D period
      hPeriod
  family : ProgramPGlobalMinimalPhysicalLocalActionFamilyReducedData4D period
    hPeriod configuration data analysis
      (firstOrderGraphCoreMatterRealization period hPeriod
        couplings.matterMassSquared spinCFirstOrderGraphCoreDensity)
  physicalBound :
    GlobalCandidateASevenPhysicalCoreBound4D period hPeriod configuration data
      analysis
        (firstOrderGraphCoreClosureChart period hPeriod configuration data
          analysis spinCFirstOrderGraphCoreDensity family)
        (firstOrderGraphCoreClosureMatterLLSameAction period hPeriod
          configuration data analysis spinCFirstOrderGraphCoreDensity family)
  parametrix :
    GlobalCandidateAFaithfulAugmentedFiniteDefectParametrix4D period hPeriod
      configuration data analysis
        (firstOrderGraphCoreClosureChart period hPeriod configuration data
          analysis spinCFirstOrderGraphCoreDensity family)
        (firstOrderGraphCoreClosureMatterLLSameAction period hPeriod
          configuration data analysis spinCFirstOrderGraphCoreDensity family)
        (globalCandidateASevenPhysicalCommonDomainExtension_of_bound period
          hPeriod configuration data analysis
          (firstOrderGraphCoreClosureChart period hPeriod configuration data
            analysis spinCFirstOrderGraphCoreDensity family)
          (firstOrderGraphCoreClosureMatterLLSameAction period hPeriod
            configuration data analysis spinCFirstOrderGraphCoreDensity family)
          physicalBound)

/-- Repackage the mass-independent input into the preceding graph-core terminal
interface. -/
def GlobalCandidateAHessianFirstOrderGraphCoreDensityBoundedInputs4D.graphInputs
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    (inputs :
      GlobalCandidateAHessianFirstOrderGraphCoreDensityBoundedInputs4D period
        hPeriod configuration data analysis) :
    GlobalCandidateAHessianGraphCoreDensityBoundedInputs4D period hPeriod
      configuration data analysis where
  spinCGraphCoreDensity :=
    firstOrderGraphCoreMassDensity period hPeriod couplings.matterMassSquared
      inputs.spinCFirstOrderGraphCoreDensity
  family := inputs.family
  physicalBound := inputs.physicalBound
  parametrix := inputs.parametrix

/-- Preferred H14 terminal gate from one mass-independent first-order SpinC
core theorem, the reduced local family, one H11 bound and one H12 parametrix. -/
theorem global_candidateA_hessian_firstOrderGraphCoreDensity_bounded_closure_gate
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
    (inputs :
      GlobalCandidateAHessianFirstOrderGraphCoreDensityBoundedInputs4D period
        hPeriod configuration data analysis) :
    GlobalCandidateAHessianClosureCertificate4D period hPeriod configuration
      data analysis
        (firstOrderGraphCoreClosureChart period hPeriod configuration data
          analysis inputs.spinCFirstOrderGraphCoreDensity inputs.family)
        einsteinScale
        (firstOrderGraphCoreClosureMatterLLSameAction period hPeriod
          configuration data analysis inputs.spinCFirstOrderGraphCoreDensity
          inputs.family)
        ((inputs.graphInputs period hPeriod).maximalInputs period hPeriod).physical
        ((inputs.graphInputs period hPeriod).maximalInputs period hPeriod).estimates :=
  global_candidateA_hessian_graphCoreDensity_bounded_closure_gate period hPeriod
    configuration data analysis einsteinScale hBoundaryTransverse
      (inputs.graphInputs period hPeriod)

end
end P0EFTJanusProgramPGlobalHessianFirstOrderGraphCoreDensityBoundedClosure4D
end JanusFormal
