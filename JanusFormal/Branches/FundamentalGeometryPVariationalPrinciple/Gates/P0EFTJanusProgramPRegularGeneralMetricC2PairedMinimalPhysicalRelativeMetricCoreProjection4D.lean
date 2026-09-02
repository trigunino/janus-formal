import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootInverseCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricCoreProjection4D

/-!
# Cross-base metric projection on the minimal physical tangent

Besides the two native fixed-base metric cores, the paired relative chart
needs the minus perturbation expressed in the fixed plus-base core.  Adding
that cross projection to the graph norm makes the full relative linear core
continuous without changing the algebraic tangent space.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalRelativeMetricCoreProjection4D

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
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootLift4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalMatterLLExtraGraphAdaptedNorm4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricCoreProjection4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

private abbrev C2Matrix :=
  C2FiniteMatrix period hPeriod 4

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

/-- Native paired cores together with the plus perturbation and the relative
perturbation, both measured from the fixed plus base. -/
abbrev RegularGeneralMetricC2PairedRelativeCore
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :=
  RegularGeneralMetricC2PairedCore period hPeriod plusBase minusBase ×
    (C2Matrix period hPeriod × C2Matrix period hPeriod)

/-- The minus metric perturbation embedded in the fixed plus-base C² core. -/
def globalMinimalPhysicalMinusMetricAtPlusBaseC2MatrixLinearMap
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase : RegularGeneralLorentzMetric period hPeriod) :
    GlobalMinimalPhysicalFieldTangent period hPeriod configuration →ₗ[Real]
      C2Matrix period hPeriod where
  toFun direction :=
    regularGeneralMetricC2VariationMatrix period hPeriod plusBase
      (direction.1.completeVariation.fullMetricPerturbation .minus)
  map_add' first second :=
    congrArg Subtype.val
      ((smoothToGeneralMetricRelativeC2Core period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod plusBase)
        plusBase.metric).map_add
          (first.1.completeVariation.fullMetricPerturbation .minus)
          (second.1.completeVariation.fullMetricPerturbation .minus))
  map_smul' scalar direction :=
    congrArg Subtype.val
      ((smoothToGeneralMetricRelativeC2Core period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod plusBase)
        plusBase.metric).map_smul scalar
          (direction.1.completeVariation.fullMetricPerturbation .minus))

/-- The plus metric perturbation as an ambient fixed-plus C² matrix. -/
def globalMinimalPhysicalPlusMetricC2MatrixLinearMap
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase : RegularGeneralLorentzMetric period hPeriod) :
    GlobalMinimalPhysicalFieldTangent period hPeriod configuration →ₗ[Real]
      C2Matrix period hPeriod where
  toFun direction :=
    regularGeneralMetricC2VariationMatrix period hPeriod plusBase
      (direction.1.completeVariation.fullMetricPerturbation .plus)
  map_add' first second :=
    congrArg Subtype.val
      ((smoothToGeneralMetricRelativeC2Core period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod plusBase)
        plusBase.metric).map_add
          (first.1.completeVariation.fullMetricPerturbation .plus)
          (second.1.completeVariation.fullMetricPerturbation .plus))
  map_smul' scalar direction :=
    congrArg Subtype.val
      ((smoothToGeneralMetricRelativeC2Core period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod plusBase)
        plusBase.metric).map_smul scalar
          (direction.1.completeVariation.fullMetricPerturbation .plus))

/-- Full linear metric core used by the paired relative chart.  Its last two
components are the fixed-plus representations of `h₊` and `h₋ - h₊`. -/
def globalMinimalPhysicalPairedRelativeMetricCoreLinearMap
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :
    GlobalMinimalPhysicalFieldTangent period hPeriod configuration →ₗ[Real]
      RegularGeneralMetricC2PairedRelativeCore
        period hPeriod plusBase minusBase where
  toFun direction :=
    let paired := globalMinimalPhysicalPairedMetricCoreLinearMap period hPeriod
      configuration plusBase minusBase direction
    (paired,
      (globalMinimalPhysicalPlusMetricC2MatrixLinearMap period hPeriod
          configuration plusBase direction,
        globalMinimalPhysicalMinusMetricAtPlusBaseC2MatrixLinearMap period hPeriod
            configuration plusBase direction -
          globalMinimalPhysicalPlusMetricC2MatrixLinearMap period hPeriod
            configuration plusBase direction))
  map_add' first second := by
    apply Prod.ext
    · exact (globalMinimalPhysicalPairedMetricCoreLinearMap period hPeriod
        configuration plusBase minusBase).map_add first second
    · apply Prod.ext
      · exact (globalMinimalPhysicalPlusMetricC2MatrixLinearMap period hPeriod
          configuration plusBase).map_add first second
      · change
          globalMinimalPhysicalMinusMetricAtPlusBaseC2MatrixLinearMap period hPeriod
                configuration plusBase (first + second) -
              globalMinimalPhysicalPlusMetricC2MatrixLinearMap period hPeriod
                configuration plusBase (first + second) =
            (globalMinimalPhysicalMinusMetricAtPlusBaseC2MatrixLinearMap period hPeriod
                configuration plusBase first -
              globalMinimalPhysicalPlusMetricC2MatrixLinearMap period hPeriod
                configuration plusBase first) +
            (globalMinimalPhysicalMinusMetricAtPlusBaseC2MatrixLinearMap period hPeriod
                configuration plusBase second -
              globalMinimalPhysicalPlusMetricC2MatrixLinearMap period hPeriod
                configuration plusBase second)
        rw [(globalMinimalPhysicalMinusMetricAtPlusBaseC2MatrixLinearMap period
            hPeriod configuration plusBase).map_add,
          (globalMinimalPhysicalPlusMetricC2MatrixLinearMap period hPeriod
            configuration plusBase).map_add]
        abel
  map_smul' scalar direction := by
    apply Prod.ext
    · exact (globalMinimalPhysicalPairedMetricCoreLinearMap period hPeriod
        configuration plusBase minusBase).map_smul scalar direction
    · apply Prod.ext
      · exact (globalMinimalPhysicalPlusMetricC2MatrixLinearMap period hPeriod
          configuration plusBase).map_smul scalar direction
      · change
          globalMinimalPhysicalMinusMetricAtPlusBaseC2MatrixLinearMap period hPeriod
                configuration plusBase (scalar • direction) -
              globalMinimalPhysicalPlusMetricC2MatrixLinearMap period hPeriod
                configuration plusBase (scalar • direction) =
            scalar •
              (globalMinimalPhysicalMinusMetricAtPlusBaseC2MatrixLinearMap period
                  hPeriod configuration plusBase direction -
                globalMinimalPhysicalPlusMetricC2MatrixLinearMap period hPeriod
                  configuration plusBase direction)
        rw [(globalMinimalPhysicalMinusMetricAtPlusBaseC2MatrixLinearMap period
            hPeriod configuration plusBase).map_smul,
          (globalMinimalPhysicalPlusMetricC2MatrixLinearMap period hPeriod
            configuration plusBase).map_smul]
        exact (smul_sub scalar _ _).symm

@[simp]
theorem globalMinimalPhysicalPairedRelativeMetricCoreLinearMap_paired
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration) :
    (globalMinimalPhysicalPairedRelativeMetricCoreLinearMap period hPeriod
      configuration plusBase minusBase direction).1 =
      globalMinimalPhysicalPairedMetricCoreLinearMap period hPeriod
        configuration plusBase minusBase direction :=
  rfl

@[simp]
theorem globalMinimalPhysicalPairedRelativeMetricCoreLinearMap_plus
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration) :
    (globalMinimalPhysicalPairedRelativeMetricCoreLinearMap period hPeriod
      configuration plusBase minusBase direction).2.1 =
      regularGeneralMetricC2VariationMatrix period hPeriod plusBase
        (direction.1.completeVariation.fullMetricPerturbation .plus) :=
  rfl

@[simp]
theorem globalMinimalPhysicalPairedRelativeMetricCoreLinearMap_cross
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration) :
    (globalMinimalPhysicalPairedRelativeMetricCoreLinearMap period hPeriod
      configuration plusBase minusBase direction).2.2 =
      regularGeneralMetricC2VariationMatrix period hPeriod plusBase
          (direction.1.completeVariation.fullMetricPerturbation .minus) -
        regularGeneralMetricC2VariationMatrix period hPeriod plusBase
          (direction.1.completeVariation.fullMetricPerturbation .plus) :=
  rfl

/-- Graph norm controlling native paired cores and the cross-base relative
metric core simultaneously. -/
@[reducible] def globalMinimalPhysicalPairedRelativeMetricCoreNormedAddCommGroup
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
      (globalMinimalPhysicalPairedRelativeMetricCoreLinearMap period hPeriod
        configuration.physical plusBase minusBase)

@[reducible] def globalMinimalPhysicalPairedRelativeMetricCoreNormedSpace
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
    letI := globalMinimalPhysicalPairedRelativeMetricCoreNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
    NormedSpace Real (GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration.physical) := by
  letI := globalMinimalPhysicalPairedRelativeMetricCoreNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
  exact globalMinimalPhysicalMatterLLExtraGraphNormedSpace period hPeriod
    configuration data analysis realization
      (globalMinimalPhysicalPairedRelativeMetricCoreLinearMap period hPeriod
        configuration.physical plusBase minusBase)

/-- Continuous full paired-relative projection for the upgraded graph norm. -/
def globalMinimalPhysicalPairedRelativeMetricCoreCLM
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
    letI := globalMinimalPhysicalPairedRelativeMetricCoreNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
    letI := globalMinimalPhysicalPairedRelativeMetricCoreNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
    GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical
      →L[Real]
        RegularGeneralMetricC2PairedRelativeCore
          period hPeriod plusBase minusBase := by
  letI := globalMinimalPhysicalPairedRelativeMetricCoreNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
  letI := globalMinimalPhysicalPairedRelativeMetricCoreNormedSpace period
    hPeriod configuration data analysis realization plusBase minusBase
  exact globalMinimalPhysicalMatterLLExtraGraphExtraCLM period hPeriod
    configuration data analysis realization
      (globalMinimalPhysicalPairedRelativeMetricCoreLinearMap period hPeriod
        configuration.physical plusBase minusBase)

/-- Gate marker: the minimal tangent topology now controls the cross-base
relative metric variation required by the paired root chart. -/
theorem regular_general_metric_c2_paired_minimal_physical_relative_metric_core_projection_gate
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
    letI := globalMinimalPhysicalPairedRelativeMetricCoreNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
    letI := globalMinimalPhysicalPairedRelativeMetricCoreNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
    Nonempty (GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration.physical →L[Real]
        RegularGeneralMetricC2PairedRelativeCore
          period hPeriod plusBase minusBase) := by
  letI := globalMinimalPhysicalPairedRelativeMetricCoreNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
  letI := globalMinimalPhysicalPairedRelativeMetricCoreNormedSpace period
    hPeriod configuration data analysis realization plusBase minusBase
  exact ⟨globalMinimalPhysicalPairedRelativeMetricCoreCLM period hPeriod
    configuration data analysis realization plusBase minusBase⟩

end

end P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalRelativeMetricCoreProjection4D
end JanusFormal
