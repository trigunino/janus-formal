import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChartConstructor4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphCoreCompatibility4D

/-!
# Reduced local Candidate-A family data on the minimal physical tangent

The matter/LL diagonal-core compatibility is now a theorem of the existing
typed slot injections.  It must not remain an input of the H13 chart.  This
file defines the reduced local family data and constructs the earlier chart
package by inserting the derived compatibility certificate.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamily4D

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
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphCoreCompatibility4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChartConstructor4D

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

private abbrev ReducedFamilyModel
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) :=
  GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical

/-- Reduced geometric/analytic input for the actual local Candidate-A family.
The diagonal-core compatibility no longer appears because it is derived. -/
structure ProgramPGlobalMinimalPhysicalLocalActionFamilyReducedData4D
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared) where
  [normedAddCommGroup : NormedAddCommGroup
    (ReducedFamilyModel period hPeriod configuration)]
  [normedSpace : NormedSpace Real
    (ReducedFamilyModel period hPeriod configuration)]
  toAddCommGroup_eq : normedAddCommGroup.toAddCommGroup =
    Submodule.addCommGroup (ReducedFamilyModel period hPeriod configuration)
  toSMul_eq : normedSpace.toModule.toSMul =
    Submodule.smul (ReducedFamilyModel period hPeriod configuration)
  bounds : @GlobalMinimalPhysicalMatterLLGraphBounds4D period hPeriod
    couplings NonNullFace NullFace _ _ configuration data analysis realization
      normedAddCommGroup normedSpace
  domain : Set (ReducedFamilyModel period hPeriod configuration)
  isOpen_domain : IsOpen domain
  zero_mem_domain : (0 : ReducedFamilyModel period hPeriod configuration) ∈
    domain
  datumAt : ∀ point : ReducedFamilyModel period hPeriod configuration,
    point ∈ domain →
      GlobalCandidateALocalActionDatum period hPeriod couplings
        NonNullFace NullFace
  datumAt_zero_configuration :
    (datumAt 0 zero_mem_domain).1 = configuration.physical
  blocksC2Within : ∀ point (hPoint : point ∈ domain),
    let family : GlobalCandidateALocalActionFamily period hPeriod
        (ReducedFamilyModel period hPeriod configuration) couplings
        NonNullFace NullFace :=
      { domain := domain
        datumAt := datumAt }
    FullCoupledC2WithinAt
      (globalCandidateAActionBlocks period hPeriod
        (family.toActionFamily period hPeriod 0 zero_mem_domain) measure)
      domain point
  matterConstant : Real
  llConstant : Real
  matterAction_eq :
    let family : GlobalCandidateALocalActionFamily period hPeriod
        (ReducedFamilyModel period hPeriod configuration) couplings
        NonNullFace NullFace :=
      { domain := domain
        datumAt := datumAt }
    (globalCandidateAActionBlocks period hPeriod
      (family.toActionFamily period hPeriod 0 zero_mem_domain) measure).matter =
      fun state => matterConstant +
        programPPrimitiveSpinCMatterGraphAction period hPeriod
          couplings.matterMassSquared
          (@globalMinimalPhysicalMatterGraphCLM period hPeriod couplings
            NonNullFace NullFace _ _ configuration data analysis realization
            normedAddCommGroup normedSpace bounds state)
  llAction_eq :
    let family : GlobalCandidateALocalActionFamily period hPeriod
        (ReducedFamilyModel period hPeriod configuration) couplings
        NonNullFace NullFace :=
      { domain := domain
        datumAt := datumAt }
    (globalCandidateAActionBlocks period hPeriod
      (family.toActionFamily period hPeriod 0 zero_mem_domain) measure).ll =
      fun state => llConstant +
        globalCandidateAFullLLGraphAction period hPeriod data analysis
          (@globalMinimalPhysicalLLGraphCLM period hPeriod couplings
            NonNullFace NullFace _ _ configuration data analysis realization
            normedAddCommGroup normedSpace bounds state)

/-- Insert the derived core compatibility and recover the earlier constructor
input. -/
def ProgramPGlobalMinimalPhysicalLocalActionFamilyReducedData4D.toFull
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared}
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyReducedData4D
      period hPeriod (measure := measure) configuration data analysis
        realization) :
    ProgramPGlobalMinimalPhysicalLocalActionFamilyData4D period hPeriod
      (measure := measure) configuration data analysis realization where
  normedAddCommGroup := family.normedAddCommGroup
  normedSpace := family.normedSpace
  toAddCommGroup_eq := family.toAddCommGroup_eq
  toSMul_eq := family.toSMul_eq
  bounds := family.bounds
  coreCompatibility :=
    globalMinimalPhysicalMatterLLGraphCoreCompatibility period hPeriod
      configuration data analysis realization
  domain := family.domain
  isOpen_domain := family.isOpen_domain
  zero_mem_domain := family.zero_mem_domain
  datumAt := family.datumAt
  datumAt_zero_configuration := family.datumAt_zero_configuration
  blocksC2Within := family.blocksC2Within
  matterConstant := family.matterConstant
  llConstant := family.llConstant
  matterAction_eq := family.matterAction_eq
  llAction_eq := family.llAction_eq

/-- Concrete chart data from the reduced family packet. -/
def globalCandidateAMinimalPhysicalActionChartData_of_reducedFamily
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyReducedData4D period
      hPeriod (measure := measure) configuration data analysis realization) :=
  globalCandidateAMinimalPhysicalActionChartData_of_family period hPeriod
    configuration data analysis realization family.toFull

/-- H13 from the reduced local family data. -/
theorem global_candidateA_h13_minimalPhysical_reducedFamily_gate
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyReducedData4D period
      hPeriod (measure := measure) configuration data analysis realization) :
    GlobalCandidateAH13MatterLLSameActionCertificate period hPeriod
      configuration data analysis
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis
            (globalCandidateAMinimalPhysicalActionChartData_of_reducedFamily
              period hPeriod configuration data analysis realization family))
        (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
          configuration data analysis
            (globalCandidateAMinimalPhysicalActionChartData_of_reducedFamily
              period hPeriod configuration data analysis realization family)) :=
  global_candidateA_h13_minimalPhysical_family_gate period hPeriod configuration
    data analysis realization family.toFull

end
end P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamily4D
end JanusFormal
