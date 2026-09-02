import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalMatterLLExtraGraphAdaptedNorm4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D

/-!
# Continuous paired metric-core projection on the minimal physical tangent

The two smooth metric slots are embedded into their fixed-base completed C²
cores.  Adding this linear projection to the existing matter/LL graph-adapted
norm makes it a continuous linear contraction.  This supplies the topology
needed to pull back the two fixed-base Lorentz domains.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricCoreProjection4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 2400000

noncomputable section

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
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartGeometry4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalMatterLLExtraGraphAdaptedNorm4D

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

/-- Product of the two fixed-base completed C² metric cores. -/
abbrev RegularGeneralMetricC2PairedCore
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :=
  RegularGeneralMetricC2Core period hPeriod plusBase ×
    RegularGeneralMetricC2Core period hPeriod minusBase

/-- Algebraic projection from the minimal physical tangent to the two
fixed-base completed metric cores. -/
def globalMinimalPhysicalPairedMetricCoreLinearMap
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :
    GlobalMinimalPhysicalFieldTangent period hPeriod configuration →ₗ[Real]
      RegularGeneralMetricC2PairedCore period hPeriod plusBase minusBase where
  toFun direction :=
    (regularGeneralMetricSmoothC2Variation period hPeriod plusBase
        (direction.1.completeVariation.fullMetricPerturbation .plus),
      regularGeneralMetricSmoothC2Variation period hPeriod minusBase
        (direction.1.completeVariation.fullMetricPerturbation .minus))
  map_add' first second := by
    apply Prod.ext
    · exact (smoothToGeneralMetricRelativeC2Core period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod plusBase)
        plusBase.metric).map_add
          (first.1.completeVariation.fullMetricPerturbation .plus)
          (second.1.completeVariation.fullMetricPerturbation .plus)
    · exact (smoothToGeneralMetricRelativeC2Core period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod minusBase)
        minusBase.metric).map_add
          (first.1.completeVariation.fullMetricPerturbation .minus)
          (second.1.completeVariation.fullMetricPerturbation .minus)
  map_smul' scalar direction := by
    apply Prod.ext
    · exact (smoothToGeneralMetricRelativeC2Core period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod plusBase)
        plusBase.metric).map_smul scalar
          (direction.1.completeVariation.fullMetricPerturbation .plus)
    · exact (smoothToGeneralMetricRelativeC2Core period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod minusBase)
        minusBase.metric).map_smul scalar
          (direction.1.completeVariation.fullMetricPerturbation .minus)

/-- Graph-adapted norm which controls matter, LL and the paired completed
metric projection simultaneously. -/
@[reducible] def globalMinimalPhysicalPairedMetricCoreNormedAddCommGroup
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
    NormedAddCommGroup (GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration.physical) :=
  globalMinimalPhysicalMatterLLExtraGraphNormedAddCommGroup period hPeriod
    configuration data analysis realization
      (globalMinimalPhysicalPairedMetricCoreLinearMap period hPeriod
        configuration.physical plusBase minusBase)

/-- The paired graph-adapted norm respects the original real scalar action. -/
@[reducible] def globalMinimalPhysicalPairedMetricCoreNormedSpace
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
    NormedSpace Real (GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration.physical) := by
  letI := globalMinimalPhysicalPairedMetricCoreNormedAddCommGroup period
    hPeriod configuration data analysis realization plusBase minusBase
  exact globalMinimalPhysicalMatterLLExtraGraphNormedSpace period hPeriod
    configuration data analysis realization
      (globalMinimalPhysicalPairedMetricCoreLinearMap period hPeriod
        configuration.physical plusBase minusBase)

/-- Continuous paired metric projection for the graph-adapted norm. -/
def globalMinimalPhysicalPairedMetricCoreCLM
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
    GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical
      →L[Real]
        RegularGeneralMetricC2PairedCore period hPeriod plusBase minusBase := by
  letI := globalMinimalPhysicalPairedMetricCoreNormedAddCommGroup period
    hPeriod configuration data analysis realization plusBase minusBase
  letI := globalMinimalPhysicalPairedMetricCoreNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
  exact globalMinimalPhysicalMatterLLExtraGraphExtraCLM period hPeriod
    configuration data analysis realization
      (globalMinimalPhysicalPairedMetricCoreLinearMap period hPeriod
        configuration.physical plusBase minusBase)

/-- Gate marker: the exact two metric slots are a continuous linear projection
in a norm that still controls the established matter and LL graphs. -/
theorem regular_general_metric_c2_paired_minimal_physical_metric_core_projection_gate
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
    Nonempty (GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration.physical →L[Real]
        RegularGeneralMetricC2PairedCore period hPeriod plusBase minusBase) := by
  letI := globalMinimalPhysicalPairedMetricCoreNormedAddCommGroup period
    hPeriod configuration data analysis realization plusBase minusBase
  letI := globalMinimalPhysicalPairedMetricCoreNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
  exact ⟨globalMinimalPhysicalPairedMetricCoreCLM period hPeriod configuration
    data analysis realization plusBase minusBase⟩

end

end P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricCoreProjection4D
end JanusFormal
