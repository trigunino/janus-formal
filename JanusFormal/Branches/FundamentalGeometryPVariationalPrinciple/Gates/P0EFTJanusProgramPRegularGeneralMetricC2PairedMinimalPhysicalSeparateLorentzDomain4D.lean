import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricCoreProjection4D

/-!
# Open separate-Lorentz domain on the minimal physical tangent

Pulling back the product of the two fixed-base Lorentz domains through the
continuous paired metric-core projection gives a genuine open neighborhood of
zero.  It supplies the first two fields of paired admissibility; only the
joint relative-root condition remains separate.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalSeparateLorentzDomain4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 2400000

noncomputable section

open Set
open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricCoreProjection4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

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

local instance c2ScalarNormedAddCommGroup :
    NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule
    period hPeriod).normedAddCommGroup

local instance c2ScalarNormedSpace :
    NormedSpace Real (C2Scalar period hPeriod) :=
  inferInstance

local instance c2ScalarCompleteSpace :
    CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

private local instance minimalModelAddCommGroup
    (configuration : GlobalFieldConfiguration period hPeriod) :
    AddCommGroup (GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration) :=
  Submodule.addCommGroup
    (GlobalMinimalPhysicalFieldTangent period hPeriod configuration)

private local instance minimalModelModule
    (configuration : GlobalFieldConfiguration period hPeriod) :
    Module Real (GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration) :=
  Submodule.module
    (GlobalMinimalPhysicalFieldTangent period hPeriod configuration)

/-- Directions for which both independently varied metrics lie in their
fixed-base regular Lorentz charts. -/
def regularGeneralMetricC2PairedMinimalPhysicalSeparateLorentzDomain
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :
    Set (GlobalMinimalPhysicalFieldTangent period hPeriod configuration) :=
  {direction |
    (globalMinimalPhysicalPairedMetricCoreLinearMap period hPeriod
        configuration plusBase minusBase direction).1 ∈
        regularGeneralMetricC2LorentzChartDomain period hPeriod plusBase ∧
      (globalMinimalPhysicalPairedMetricCoreLinearMap period hPeriod
        configuration plusBase minusBase direction).2 ∈
        regularGeneralMetricC2LorentzChartDomain period hPeriod minusBase}

/-- The separate-Lorentz domain is open for the metric graph-adapted norm. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalSeparateLorentzDomain_isOpen
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :
    letI := globalMinimalPhysicalPairedMetricCoreNormedAddCommGroup period
      hPeriod configuration data analysis realization plusBase minusBase
    letI := globalMinimalPhysicalPairedMetricCoreNormedSpace period hPeriod
      configuration data analysis realization plusBase minusBase
    IsOpen (regularGeneralMetricC2PairedMinimalPhysicalSeparateLorentzDomain
      period hPeriod configuration.physical plusBase minusBase) := by
  letI := globalMinimalPhysicalPairedMetricCoreNormedAddCommGroup period
    hPeriod configuration data analysis realization plusBase minusBase
  letI := globalMinimalPhysicalPairedMetricCoreNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
  change IsOpen ((globalMinimalPhysicalPairedMetricCoreCLM period hPeriod
      configuration data analysis realization plusBase minusBase) ⁻¹'
    (regularGeneralMetricC2LorentzChartDomain period hPeriod plusBase ×ˢ
      regularGeneralMetricC2LorentzChartDomain period hPeriod minusBase))
  exact ((regularGeneralMetricC2LorentzChartDomain_isOpen period hPeriod
      plusBase).prod
    (regularGeneralMetricC2LorentzChartDomain_isOpen period hPeriod minusBase)
      ).preimage
    (globalMinimalPhysicalPairedMetricCoreCLM period hPeriod configuration data
      analysis realization plusBase minusBase).continuous

/-- Zero belongs to the separate-Lorentz domain. -/
theorem zero_mem_regularGeneralMetricC2PairedMinimalPhysicalSeparateLorentzDomain
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :
    (0 : GlobalMinimalPhysicalFieldTangent period hPeriod configuration) ∈
      regularGeneralMetricC2PairedMinimalPhysicalSeparateLorentzDomain
        period hPeriod configuration plusBase minusBase := by
  change
    (globalMinimalPhysicalPairedMetricCoreLinearMap period hPeriod configuration
        plusBase minusBase 0).1 ∈
        regularGeneralMetricC2LorentzChartDomain period hPeriod plusBase ∧
      (globalMinimalPhysicalPairedMetricCoreLinearMap period hPeriod configuration
        plusBase minusBase 0).2 ∈
        regularGeneralMetricC2LorentzChartDomain period hPeriod minusBase
  rw [(globalMinimalPhysicalPairedMetricCoreLinearMap period hPeriod
    configuration plusBase minusBase).map_zero]
  exact ⟨zero_mem_regularGeneralMetricC2LorentzChartDomain period hPeriod
      plusBase,
    zero_mem_regularGeneralMetricC2LorentzChartDomain period hPeriod minusBase⟩

/-- Membership supplies exactly the two independent fixed-base chart
conditions used by paired admissibility. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalSeparateLorentzDomain_mem
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    {direction : GlobalMinimalPhysicalFieldTangent period hPeriod configuration}
    (hDirection : direction ∈
      regularGeneralMetricC2PairedMinimalPhysicalSeparateLorentzDomain
        period hPeriod configuration plusBase minusBase) :
    regularGeneralMetricSmoothC2Variation period hPeriod plusBase
        (direction.1.completeVariation.fullMetricPerturbation .plus) ∈
        regularGeneralMetricC2LorentzChartDomain period hPeriod plusBase ∧
      regularGeneralMetricSmoothC2Variation period hPeriod minusBase
        (direction.1.completeVariation.fullMetricPerturbation .minus) ∈
        regularGeneralMetricC2LorentzChartDomain period hPeriod minusBase :=
  hDirection

/-- Gate marker: a genuine open zero-neighborhood now discharges the two
separate Lorentz conditions of the paired chart. -/
theorem regular_general_metric_c2_paired_minimal_physical_separate_lorentz_domain_gate
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :
    letI := globalMinimalPhysicalPairedMetricCoreNormedAddCommGroup period
      hPeriod configuration data analysis realization plusBase minusBase
    letI := globalMinimalPhysicalPairedMetricCoreNormedSpace period hPeriod
      configuration data analysis realization plusBase minusBase
    IsOpen (regularGeneralMetricC2PairedMinimalPhysicalSeparateLorentzDomain
        period hPeriod configuration.physical plusBase minusBase) ∧
      (0 : GlobalMinimalPhysicalFieldTangent period hPeriod
        configuration.physical) ∈
        regularGeneralMetricC2PairedMinimalPhysicalSeparateLorentzDomain
          period hPeriod configuration.physical plusBase minusBase := by
  letI := globalMinimalPhysicalPairedMetricCoreNormedAddCommGroup period
    hPeriod configuration data analysis realization plusBase minusBase
  letI := globalMinimalPhysicalPairedMetricCoreNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
  exact ⟨
    regularGeneralMetricC2PairedMinimalPhysicalSeparateLorentzDomain_isOpen
      period hPeriod configuration data analysis realization plusBase minusBase,
    zero_mem_regularGeneralMetricC2PairedMinimalPhysicalSeparateLorentzDomain
      period hPeriod configuration.physical plusBase minusBase⟩

end

end P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalSeparateLorentzDomain4D
end JanusFormal
