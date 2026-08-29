import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D

/-!
# Constructor of the minimal physical H13 chart

This gate combines the canonical matter/LL graph projections with an actual
open local Candidate-A family on the corrected D10-free tangent.  The family
supplies the physical configuration and `C²` action blocks; the graph
realization and its two norm estimates supply the only nontrivial analytic
projections.  The result is the complete H13 quadratic chart and same-action
certificate.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChartConstructor4D

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

private abbrev ConstructorModel
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) :=
  GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical

/-- The genuinely geometric part of the local chart construction.  It is an
open family of the existing Candidate-A action over the corrected physical
tangent, together with the exact matter and LL action identities after using
the canonical graph projections. -/
structure ProgramPGlobalMinimalPhysicalLocalActionFamilyData4D
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
    (ConstructorModel period hPeriod configuration)]
  [normedSpace : NormedSpace Real
    (ConstructorModel period hPeriod configuration)]
  toAddCommGroup_eq : normedAddCommGroup.toAddCommGroup =
    Submodule.addCommGroup (ConstructorModel period hPeriod configuration)
  toSMul_eq : normedSpace.toModule.toSMul =
    Submodule.smul (ConstructorModel period hPeriod configuration)
  bounds : @GlobalMinimalPhysicalMatterLLGraphBounds4D period hPeriod
    couplings NonNullFace NullFace _ _ configuration data analysis realization
      normedAddCommGroup normedSpace
  coreCompatibility :
    GlobalMinimalPhysicalMatterLLGraphCoreCompatibility4D period hPeriod
      configuration data analysis realization
  domain : Set (ConstructorModel period hPeriod configuration)
  isOpen_domain : IsOpen domain
  zero_mem_domain : (0 : ConstructorModel period hPeriod configuration) ∈ domain
  datumAt : ∀ point : ConstructorModel period hPeriod configuration,
    point ∈ domain →
      GlobalCandidateALocalActionDatum period hPeriod couplings
        NonNullFace NullFace
  datumAt_zero_configuration :
    (datumAt 0 zero_mem_domain).1 = configuration.physical
  blocksC2Within : ∀ point (hPoint : point ∈ domain),
    let family : GlobalCandidateALocalActionFamily period hPeriod
        (ConstructorModel period hPeriod configuration) couplings
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
        (ConstructorModel period hPeriod configuration) couplings
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
        (ConstructorModel period hPeriod configuration) couplings
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

/-- Assemble the concrete chart data expected by the minimal-physical chart
gate. -/
def globalCandidateAMinimalPhysicalActionChartData_of_family
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
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyData4D period hPeriod
      (measure := measure) configuration data analysis realization) :
    ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod configuration
      (measure := measure) data analysis where
  normedAddCommGroup := family.normedAddCommGroup
  normedSpace := family.normedSpace
  toAddCommGroup_eq := family.toAddCommGroup_eq
  toSMul_eq := family.toSMul_eq
  domain := family.domain
  isOpen_domain := family.isOpen_domain
  zero_mem_domain := family.zero_mem_domain
  datumAt := family.datumAt
  datumAt_zero_configuration := family.datumAt_zero_configuration
  blocksC2Within := family.blocksC2Within
  matterProjection := @globalMinimalPhysicalMatterGraphCLM period hPeriod
    couplings NonNullFace NullFace _ _ configuration data analysis realization
      family.normedAddCommGroup family.normedSpace family.bounds
  llProjection := @globalMinimalPhysicalLLGraphCLM period hPeriod couplings
    NonNullFace NullFace _ _ configuration data analysis realization
      family.normedAddCommGroup family.normedSpace family.bounds
  matterConstant := family.matterConstant
  llConstant := family.llConstant
  matterAction_eq := family.matterAction_eq
  llAction_eq := family.llAction_eq
  matterProjection_diagonalCore := by
    intro core
    exact family.coreCompatibility.matter core
  llProjection_diagonalCore := by
    intro core
    exact family.coreCompatibility.ll core

/-- The open family, smooth matter graph realization and two graph estimates
construct the complete H13 certificate. -/
theorem global_candidateA_h13_minimalPhysical_family_gate
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
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyData4D period hPeriod
      (measure := measure) configuration data analysis realization) :
    GlobalCandidateAH13MatterLLSameActionCertificate period hPeriod
      configuration data analysis
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis
            (globalCandidateAMinimalPhysicalActionChartData_of_family period
              hPeriod configuration data analysis realization family))
        (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
          configuration data analysis
            (globalCandidateAMinimalPhysicalActionChartData_of_family period
              hPeriod configuration data analysis realization family)) :=
  global_candidateA_h13_minimalPhysical_actionChart_gate period hPeriod
    configuration data analysis
      (globalCandidateAMinimalPhysicalActionChartData_of_family period hPeriod
        configuration data analysis realization family)

end
end P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChartConstructor4D
end JanusFormal
