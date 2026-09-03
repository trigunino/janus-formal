import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2FixedVolumeMaxwellActionBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalRelativeMetricCoreProjection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameGaugePotentialReconstruction4D

/-! # Joint metric and gauge C² graph projection -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricGaugeCoreProjection4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 2400000

noncomputable section

open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalMatterLLExtraGraphAdaptedNorm4D
open P0EFTJanusCompleteVariationGaugeFunctionalTypeBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularFrameGaugePotentialReconstruction4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalRelativeMetricCoreProjection4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
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

/-- The eight C² frame coefficients of one Abelian potential. -/
abbrev RegularGeneralMetricC2GaugeCoefficientCore :=
  Fin 4 → Fin 2 → C2Scalar period hPeriod

/-- C² coefficient packets for the two sectors. -/
abbrev RegularGeneralMetricC2PairedGaugeCoefficientCore :=
  RegularGeneralMetricC2GaugeCoefficientCore period hPeriod ×
    RegularGeneralMetricC2GaugeCoefficientCore period hPeriod

/-- The relative metric core and both gauge coefficient packets. -/
abbrev RegularGeneralMetricC2PairedMetricGaugeCore
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :=
  RegularGeneralMetricC2PairedRelativeCore
      period hPeriod plusBase minusBase ×
    RegularGeneralMetricC2PairedGaugeCoefficientCore period hPeriod

/-- Componentwise exact-smooth lift into the completed C² coefficient core. -/
def smoothGaugeCoefficientC2CoreLinearMap :
    SmoothQuotientField period hPeriod GaugeFiber →ₗ[Real]
      RegularGeneralMetricC2GaugeCoefficientCore period hPeriod where
  toFun coefficients frameIndex component :=
    smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
      (regularFrameGaugeCoefficient period hPeriod coefficients
        (frameIndex, component))
  map_add' first second := by
    funext frameIndex component
    exact (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod).map_add
      (regularFrameGaugeCoefficient period hPeriod first
        (frameIndex, component))
      (regularFrameGaugeCoefficient period hPeriod second
        (frameIndex, component))
  map_smul' scalar coefficients := by
    funext frameIndex component
    exact (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod).map_smul
      scalar (regularFrameGaugeCoefficient period hPeriod coefficients
        (frameIndex, component))

@[simp]
theorem smoothGaugeCoefficientC2CoreLinearMap_apply
    (coefficients : SmoothQuotientField period hPeriod GaugeFiber)
    (frameIndex : Fin 4) (component : Fin 2) :
    smoothGaugeCoefficientC2CoreLinearMap period hPeriod coefficients
        frameIndex component =
      smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
        (regularFrameGaugeCoefficient period hPeriod coefficients
          (frameIndex, component)) :=
  rfl

/-- Componentwise lift for the two independent sector packets. -/
def smoothGaugeVariationPairC2CoreLinearMap :
    GaugeVariationPair period hPeriod →ₗ[Real]
      RegularGeneralMetricC2PairedGaugeCoefficientCore period hPeriod where
  toFun coefficients :=
    (smoothGaugeCoefficientC2CoreLinearMap period hPeriod coefficients.1,
      smoothGaugeCoefficientC2CoreLinearMap period hPeriod coefficients.2)
  map_add' first second := by
    apply Prod.ext
    · exact (smoothGaugeCoefficientC2CoreLinearMap period hPeriod).map_add
        first.1 second.1
    · exact (smoothGaugeCoefficientC2CoreLinearMap period hPeriod).map_add
        first.2 second.2
  map_smul' scalar coefficients := by
    apply Prod.ext
    · exact (smoothGaugeCoefficientC2CoreLinearMap period hPeriod).map_smul
        scalar coefficients.1
    · exact (smoothGaugeCoefficientC2CoreLinearMap period hPeriod).map_smul
        scalar coefficients.2

/-- Algebraic extraction of the independent gauge direction. -/
def globalMinimalPhysicalGaugeCoefficientLinearMap
    (configuration : GlobalFieldConfiguration period hPeriod) :
    GlobalMinimalPhysicalFieldTangent period hPeriod configuration →ₗ[Real]
      GaugeVariationPair period hPeriod where
  toFun direction :=
    (GlobalPhysicalFieldTangent.completeVariation period hPeriod
      direction.1).independent.gauge
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The paired gauge coefficient C² core read from a minimal direction. -/
def globalMinimalPhysicalPairedGaugeCoefficientC2CoreLinearMap
    (configuration : GlobalFieldConfiguration period hPeriod) :
    GlobalMinimalPhysicalFieldTangent period hPeriod configuration →ₗ[Real]
      RegularGeneralMetricC2PairedGaugeCoefficientCore period hPeriod :=
  (smoothGaugeVariationPairC2CoreLinearMap period hPeriod).comp
    (globalMinimalPhysicalGaugeCoefficientLinearMap period hPeriod
      configuration)

/-- Joint linear coordinate controlling every metric and gauge input needed
by the paired Maxwell blocks. -/
def globalMinimalPhysicalPairedMetricGaugeCoreLinearMap
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :
    GlobalMinimalPhysicalFieldTangent period hPeriod configuration →ₗ[Real]
      RegularGeneralMetricC2PairedMetricGaugeCore
        period hPeriod plusBase minusBase where
  toFun direction :=
    (globalMinimalPhysicalPairedRelativeMetricCoreLinearMap period hPeriod
        configuration plusBase minusBase direction,
      globalMinimalPhysicalPairedGaugeCoefficientC2CoreLinearMap period hPeriod
        configuration direction)
  map_add' first second := by
    apply Prod.ext
    · exact (globalMinimalPhysicalPairedRelativeMetricCoreLinearMap period
        hPeriod configuration plusBase minusBase).map_add first second
    · exact (globalMinimalPhysicalPairedGaugeCoefficientC2CoreLinearMap
        period hPeriod configuration).map_add first second
  map_smul' scalar direction := by
    apply Prod.ext
    · exact (globalMinimalPhysicalPairedRelativeMetricCoreLinearMap period
        hPeriod configuration plusBase minusBase).map_smul scalar direction
    · exact (globalMinimalPhysicalPairedGaugeCoefficientC2CoreLinearMap
        period hPeriod configuration).map_smul scalar direction

@[simp]
theorem globalMinimalPhysicalPairedMetricGaugeCoreLinearMap_metric
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration) :
    (globalMinimalPhysicalPairedMetricGaugeCoreLinearMap period hPeriod
      configuration plusBase minusBase direction).1 =
      globalMinimalPhysicalPairedRelativeMetricCoreLinearMap period hPeriod
        configuration plusBase minusBase direction :=
  rfl

@[simp]
theorem globalMinimalPhysicalPairedMetricGaugeCoreLinearMap_gauge
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration) :
    (globalMinimalPhysicalPairedMetricGaugeCoreLinearMap period hPeriod
      configuration plusBase minusBase direction).2 =
      smoothGaugeVariationPairC2CoreLinearMap period hPeriod
        direction.1.completeVariation.independent.gauge :=
  rfl

/-- Graph topology simultaneously controlling the paired relative metric and
the two gauge coefficient packets. -/
@[reducible] def globalMinimalPhysicalPairedMetricGaugeCoreNormedAddCommGroup
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
      (globalMinimalPhysicalPairedMetricGaugeCoreLinearMap period hPeriod
        configuration.physical plusBase minusBase)

@[reducible] def globalMinimalPhysicalPairedMetricGaugeCoreNormedSpace
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
    letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
    NormedSpace Real (GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration.physical) := by
  letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
  exact globalMinimalPhysicalMatterLLExtraGraphNormedSpace period hPeriod
    configuration data analysis realization
      (globalMinimalPhysicalPairedMetricGaugeCoreLinearMap period hPeriod
        configuration.physical plusBase minusBase)

/-- Continuous joint projection for the upgraded graph norm. -/
def globalMinimalPhysicalPairedMetricGaugeCoreCLM
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
    letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
    letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedSpace period hPeriod
      configuration data analysis realization plusBase minusBase
    GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical
      →L[Real] RegularGeneralMetricC2PairedMetricGaugeCore
        period hPeriod plusBase minusBase := by
  letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
  letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
  exact globalMinimalPhysicalMatterLLExtraGraphExtraCLM period hPeriod
    configuration data analysis realization
      (globalMinimalPhysicalPairedMetricGaugeCoreLinearMap period hPeriod
        configuration.physical plusBase minusBase)

/-- The metric coordinate remains continuous in the joint topology. -/
def globalMinimalPhysicalPairedMetricGaugeCoreMetricCLM
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
    letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
    letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedSpace period hPeriod
      configuration data analysis realization plusBase minusBase
    GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical
      →L[Real] RegularGeneralMetricC2PairedRelativeCore
        period hPeriod plusBase minusBase := by
  letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
  letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
  exact (ContinuousLinearMap.fst Real
    (RegularGeneralMetricC2PairedRelativeCore
      period hPeriod plusBase minusBase)
    (RegularGeneralMetricC2PairedGaugeCoefficientCore period hPeriod)).comp
      (globalMinimalPhysicalPairedMetricGaugeCoreCLM period hPeriod
        configuration data analysis realization plusBase minusBase)

/-- The gauge coefficient coordinate is continuous in the joint topology. -/
def globalMinimalPhysicalPairedMetricGaugeCoreGaugeCLM
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
    letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
    letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedSpace period hPeriod
      configuration data analysis realization plusBase minusBase
    GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical
      →L[Real] RegularGeneralMetricC2PairedGaugeCoefficientCore
        period hPeriod := by
  letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
  letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
  exact (ContinuousLinearMap.snd Real
    (RegularGeneralMetricC2PairedRelativeCore
      period hPeriod plusBase minusBase)
    (RegularGeneralMetricC2PairedGaugeCoefficientCore period hPeriod)).comp
      (globalMinimalPhysicalPairedMetricGaugeCoreCLM period hPeriod
        configuration data analysis realization plusBase minusBase)

/-- Gate marker: one Banach topology now controls all metric and gauge
coordinates needed by the paired Maxwell action. -/
theorem regular_general_metric_c2_paired_minimal_physical_metric_gauge_core_projection_gate
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
    letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
    letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedSpace period hPeriod
      configuration data analysis realization plusBase minusBase
    Nonempty (GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration.physical →L[Real]
        RegularGeneralMetricC2PairedMetricGaugeCore
          period hPeriod plusBase minusBase) := by
  letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
  letI := globalMinimalPhysicalPairedMetricGaugeCoreNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
  exact ⟨globalMinimalPhysicalPairedMetricGaugeCoreCLM period hPeriod
    configuration data analysis realization plusBase minusBase⟩

end

end P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricGaugeCoreProjection4D
end JanusFormal
