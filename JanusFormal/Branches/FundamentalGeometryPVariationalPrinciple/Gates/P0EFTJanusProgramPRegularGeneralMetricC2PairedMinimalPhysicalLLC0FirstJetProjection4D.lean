import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMatterC24D

/-! # Strong LL first-jet projection on the paired minimal chart -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1200000

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalMatterLLExtraGraphAdaptedNorm4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricGaugeCoreProjection4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

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

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance effectiveThroatCompactSpace :
    CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance c2ScalarNormedAddCommGroup :
    NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule
    period hPeriod).normedAddCommGroup

local instance c2ScalarNormedSpace :
    NormedSpace Real (C2Scalar period hPeriod) := inferInstance

universe u

/-- Forget smoothness while retaining the continuous throat representative. -/
def smoothThroatFieldToContinuousLinearMap
    (Fiber : Type u) [NormedAddCommGroup Fiber] [NormedSpace Real Fiber] :
    SmoothThroatField period hPeriod Fiber →ₗ[Real]
      C(EffectiveThroat period hPeriod, Fiber) where
  toFun field := ⟨field, field.contMDiff_toFun.continuous⟩
  map_add' first second := by
    apply ContinuousMap.ext
    intro point
    rfl
  map_smul' scalar field := by
    apply ContinuousMap.ext
    intro point
    rfl

/-- The continuous value and generating-frame first derivative of an LL field. -/
def smoothLLFieldC0FirstJetLinearMap
    (frame : SmoothThroatGeneratingFrame period hPeriod) :
    SmoothThroatField period hPeriod LLFieldFiber →ₗ[Real]
      (C(EffectiveThroat period hPeriod, LLFieldFiber) ×
        C(EffectiveThroat period hPeriod, Fin frame.count → LLFieldFiber)) where
  toFun field :=
    (smoothThroatFieldToContinuousLinearMap period hPeriod LLFieldFiber field,
      ⟨throatFrameDerivative period hPeriod LLFieldFiber frame field,
        (throatFrameDerivative_contMDiff period hPeriod LLFieldFiber frame
          field).continuous⟩)
  map_add' first second := by
    apply Prod.ext
    · exact (smoothThroatFieldToContinuousLinearMap period hPeriod
        LLFieldFiber).map_add first second
    · apply ContinuousMap.ext
      intro point
      exact congrFun (throatFrameDerivative_add period hPeriod LLFieldFiber
        frame first second) point
  map_smul' scalar field := by
    apply Prod.ext
    · exact (smoothThroatFieldToContinuousLinearMap period hPeriod
        LLFieldFiber).map_smul scalar field
    · apply ContinuousMap.ext
      intro point
      exact congrFun (throatFrameDerivative_smul period hPeriod LLFieldFiber
        frame scalar field) point

/-- The three smooth LL coefficient fields before forgetting smoothness. -/
abbrev GlobalMinimalPhysicalLLSmoothCoefficientPacket :=
  SmoothThroatField period hPeriod LLMetricFiber ×
    (SmoothThroatField period hPeriod Real ×
      SmoothThroatField period hPeriod LLFieldFiber)

/-- One sup-norm packet controlling every pointwise input of the raw LL action. -/
abbrev GlobalMinimalPhysicalLLC0FirstJetSinglePacket
    (frame : SmoothThroatGeneratingFrame period hPeriod) :=
  C(EffectiveThroat period hPeriod, LLMetricFiber) ×
    (C(EffectiveThroat period hPeriod, Real) ×
      (C(EffectiveThroat period hPeriod, LLFieldFiber) ×
        C(EffectiveThroat period hPeriod, Fin frame.count → LLFieldFiber)))

/-- Forget smoothness while retaining one LL coefficient first jet. -/
def smoothLLCoefficientC0FirstJetLinearMap
    (frame : SmoothThroatGeneratingFrame period hPeriod) :
    GlobalMinimalPhysicalLLSmoothCoefficientPacket period hPeriod →ₗ[Real]
      GlobalMinimalPhysicalLLC0FirstJetSinglePacket period hPeriod frame where
  toFun fields :=
    (smoothThroatFieldToContinuousLinearMap period hPeriod LLMetricFiber fields.1,
      (smoothThroatFieldToContinuousLinearMap period hPeriod Real fields.2.1,
        smoothLLFieldC0FirstJetLinearMap period hPeriod frame fields.2.2))
  map_add' first second := by
    apply Prod.ext
    · exact (smoothThroatFieldToContinuousLinearMap period hPeriod
        LLMetricFiber).map_add first.1 second.1
    · apply Prod.ext
      · exact (smoothThroatFieldToContinuousLinearMap period hPeriod Real).map_add
          first.2.1 second.2.1
      · exact (smoothLLFieldC0FirstJetLinearMap period hPeriod frame).map_add
          first.2.2 second.2.2
  map_smul' scalar fields := by
    apply Prod.ext
    · exact (smoothThroatFieldToContinuousLinearMap period hPeriod
        LLMetricFiber).map_smul scalar fields.1
    · apply Prod.ext
      · exact (smoothThroatFieldToContinuousLinearMap period hPeriod Real).map_smul
          scalar fields.2.1
      · exact (smoothLLFieldC0FirstJetLinearMap period hPeriod frame).map_smul
          scalar fields.2.2

/-- Componentwise PT pullback of the three smooth LL coefficient fields. -/
def smoothLLCoefficientPTLinearMap :
    GlobalMinimalPhysicalLLSmoothCoefficientPacket period hPeriod →ₗ[Real]
      GlobalMinimalPhysicalLLSmoothCoefficientPacket period hPeriod where
  toFun fields :=
    (throatPTPullbackLinearMap period hPeriod LLMetricFiber fields.1,
      (throatPTPullbackLinearMap period hPeriod Real fields.2.1,
        throatPTPullbackLinearMap period hPeriod LLFieldFiber fields.2.2))
  map_add' first second := by
    apply Prod.ext
    · exact (throatPTPullbackLinearMap period hPeriod LLMetricFiber).map_add
        first.1 second.1
    · apply Prod.ext
      · exact (throatPTPullbackLinearMap period hPeriod Real).map_add
          first.2.1 second.2.1
      · exact (throatPTPullbackLinearMap period hPeriod LLFieldFiber).map_add
          first.2.2 second.2.2
  map_smul' scalar fields := by
    apply Prod.ext
    · exact (throatPTPullbackLinearMap period hPeriod LLMetricFiber).map_smul
        scalar fields.1
    · apply Prod.ext
      · exact (throatPTPullbackLinearMap period hPeriod Real).map_smul
          scalar fields.2.1
      · exact (throatPTPullbackLinearMap period hPeriod LLFieldFiber).map_smul
          scalar fields.2.2

/-- Algebraic extraction of the three smooth LL coefficient directions. -/
def globalMinimalPhysicalLLSmoothCoefficientLinearMap
    (configuration : GlobalFieldConfiguration period hPeriod)
    :
    GlobalMinimalPhysicalFieldTangent period hPeriod configuration
      →ₗ[Real] GlobalMinimalPhysicalLLSmoothCoefficientPacket period hPeriod where
  toFun direction :=
    (direction.1.completeVariation.independent.llAuxMetric,
      (direction.1.completeVariation.independent.llMeasure,
        direction.1.completeVariation.independent.llField))
  map_add' first second := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · rfl
  map_smul' scalar direction := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · rfl

/-- Direct and PT-transformed first jets used by the symmetrized LL action. -/
abbrev GlobalMinimalPhysicalLLC0FirstJetPacket
    (frame : SmoothThroatGeneratingFrame period hPeriod) :=
  GlobalMinimalPhysicalLLC0FirstJetSinglePacket period hPeriod frame ×
    GlobalMinimalPhysicalLLC0FirstJetSinglePacket period hPeriod frame

/-- Direct and PT-transformed strong packets of three smooth LL fields. -/
def smoothLLCoefficientPTC0FirstJetLinearMap
    (frame : SmoothThroatGeneratingFrame period hPeriod) :
    GlobalMinimalPhysicalLLSmoothCoefficientPacket period hPeriod →ₗ[Real]
      GlobalMinimalPhysicalLLC0FirstJetPacket period hPeriod frame where
  toFun fields :=
    (smoothLLCoefficientC0FirstJetLinearMap period hPeriod frame fields,
      smoothLLCoefficientC0FirstJetLinearMap period hPeriod frame
        (smoothLLCoefficientPTLinearMap period hPeriod fields))
  map_add' first second := by
    apply Prod.ext
    · exact (smoothLLCoefficientC0FirstJetLinearMap period hPeriod frame).map_add
        first second
    · exact ((smoothLLCoefficientC0FirstJetLinearMap period hPeriod frame).comp
        (smoothLLCoefficientPTLinearMap period hPeriod)).map_add first second
  map_smul' scalar fields := by
    apply Prod.ext
    · exact (smoothLLCoefficientC0FirstJetLinearMap period hPeriod frame).map_smul
        scalar fields
    · exact ((smoothLLCoefficientC0FirstJetLinearMap period hPeriod frame).comp
        (smoothLLCoefficientPTLinearMap period hPeriod)).map_smul scalar fields

/-- Algebraic projection of a minimal physical direction to both LL packets. -/
def globalMinimalPhysicalLLC0FirstJetLinearMap
    (configuration : GlobalFieldConfiguration period hPeriod)
    (frame : SmoothThroatGeneratingFrame period hPeriod) :
    GlobalMinimalPhysicalFieldTangent period hPeriod configuration
      →ₗ[Real] GlobalMinimalPhysicalLLC0FirstJetPacket period hPeriod frame where
  toFun direction :=
    smoothLLCoefficientPTC0FirstJetLinearMap period hPeriod frame
      (globalMinimalPhysicalLLSmoothCoefficientLinearMap period hPeriod
        configuration direction)
  map_add' first second := by
    exact ((smoothLLCoefficientPTC0FirstJetLinearMap period hPeriod frame).comp
      (globalMinimalPhysicalLLSmoothCoefficientLinearMap period hPeriod
        configuration)).map_add first second
  map_smul' scalar direction := by
    exact ((smoothLLCoefficientPTC0FirstJetLinearMap period hPeriod frame).comp
      (globalMinimalPhysicalLLSmoothCoefficientLinearMap period hPeriod
        configuration)).map_smul scalar direction

/-- Previous metric-gauge coordinates together with the strong LL packet. -/
abbrev RegularGeneralMetricC2PairedMetricGaugeLLStrongCore
    (plusBase minusBase :
      P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D.RegularGeneralLorentzMetric
        period hPeriod)
    (frame : SmoothThroatGeneratingFrame period hPeriod) :=
  RegularGeneralMetricC2PairedMetricGaugeCore period hPeriod plusBase minusBase ×
    GlobalMinimalPhysicalLLC0FirstJetPacket period hPeriod frame

/-- Algebraic joint coordinate used to strengthen the existing graph norm. -/
def globalMinimalPhysicalPairedMetricGaugeLLStrongCoreLinearMap
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase :
      P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D.RegularGeneralLorentzMetric
        period hPeriod)
    (frame : SmoothThroatGeneratingFrame period hPeriod) :
    GlobalMinimalPhysicalFieldTangent period hPeriod configuration →ₗ[Real]
      RegularGeneralMetricC2PairedMetricGaugeLLStrongCore period hPeriod
        plusBase minusBase frame where
  toFun direction :=
    (globalMinimalPhysicalPairedMetricGaugeCoreLinearMap period hPeriod
        configuration plusBase minusBase direction,
      globalMinimalPhysicalLLC0FirstJetLinearMap period hPeriod
        configuration frame direction)
  map_add' first second := by
    apply Prod.ext
    · exact (globalMinimalPhysicalPairedMetricGaugeCoreLinearMap period hPeriod
        configuration plusBase minusBase).map_add first second
    · exact (globalMinimalPhysicalLLC0FirstJetLinearMap period hPeriod
        configuration frame).map_add first second
  map_smul' scalar direction := by
    apply Prod.ext
    · exact (globalMinimalPhysicalPairedMetricGaugeCoreLinearMap period hPeriod
        configuration plusBase minusBase).map_smul scalar direction
    · exact (globalMinimalPhysicalLLC0FirstJetLinearMap period hPeriod
        configuration frame).map_smul scalar direction

/-- Graph topology controlling the old Hessian coordinates and the nonlinear LL inputs. -/
@[reducible] def globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (plusBase minusBase :
      P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D.RegularGeneralLorentzMetric
        period hPeriod)
    (frame : SmoothThroatGeneratingFrame period hPeriod) :
    NormedAddCommGroup (GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration.physical) :=
  globalMinimalPhysicalMatterLLExtraGraphNormedAddCommGroup period hPeriod
    configuration data analysis realization
      (globalMinimalPhysicalPairedMetricGaugeLLStrongCoreLinearMap period hPeriod
        configuration.physical plusBase minusBase frame)

@[reducible] def globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (plusBase minusBase :
      P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D.RegularGeneralLorentzMetric
        period hPeriod)
    (frame : SmoothThroatGeneratingFrame period hPeriod) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        frame
    NormedSpace Real (GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration.physical) := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      frame
  exact globalMinimalPhysicalMatterLLExtraGraphNormedSpace period hPeriod
    configuration data analysis realization
      (globalMinimalPhysicalPairedMetricGaugeLLStrongCoreLinearMap period hPeriod
        configuration.physical plusBase minusBase frame)

/-- The complete strong coordinate is continuous for its induced topology. -/
def globalMinimalPhysicalPairedMetricGaugeLLStrongCoreCLM
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (plusBase minusBase :
      P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D.RegularGeneralLorentzMetric
        period hPeriod)
    (frame : SmoothThroatGeneratingFrame period hPeriod) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        frame
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase frame
    GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical
      →L[Real] RegularGeneralMetricC2PairedMetricGaugeLLStrongCore period hPeriod
        plusBase minusBase frame := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      frame
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase frame
  exact globalMinimalPhysicalMatterLLExtraGraphExtraCLM period hPeriod
    configuration data analysis realization
      (globalMinimalPhysicalPairedMetricGaugeLLStrongCoreLinearMap period hPeriod
        configuration.physical plusBase minusBase frame)

/-- Continuous projection to the pointwise LL inputs needed by the nonlinear action. -/
def globalMinimalPhysicalPairedLLC0FirstJetCLM
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (plusBase minusBase :
      P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D.RegularGeneralLorentzMetric
        period hPeriod)
    (frame : SmoothThroatGeneratingFrame period hPeriod) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        frame
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase frame
    GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical
      →L[Real] GlobalMinimalPhysicalLLC0FirstJetPacket period hPeriod frame := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      frame
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase frame
  exact (ContinuousLinearMap.snd Real
    (RegularGeneralMetricC2PairedMetricGaugeCore period hPeriod plusBase minusBase)
    (GlobalMinimalPhysicalLLC0FirstJetPacket period hPeriod frame)).comp
      (globalMinimalPhysicalPairedMetricGaugeLLStrongCoreCLM period hPeriod
        configuration data analysis realization plusBase minusBase frame)

@[simp]
theorem globalMinimalPhysicalPairedLLC0FirstJetCLM_apply
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (plusBase minusBase :
      P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D.RegularGeneralLorentzMetric
        period hPeriod)
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration.physical) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        frame
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase frame
    globalMinimalPhysicalPairedLLC0FirstJetCLM period hPeriod configuration data
        analysis realization plusBase minusBase frame direction =
      globalMinimalPhysicalLLC0FirstJetLinearMap period hPeriod
        configuration.physical frame direction :=
  rfl

/-- Gate marker: one stronger graph topology controls every nonlinear LL input. -/
theorem regular_general_metric_c2_paired_minimal_physical_LL_c0_first_jet_gate
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (plusBase minusBase :
      P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D.RegularGeneralLorentzMetric
        period hPeriod)
    (frame : SmoothThroatGeneratingFrame period hPeriod) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        frame
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase frame
    Nonempty
      { projection :
          GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical
            →L[Real] GlobalMinimalPhysicalLLC0FirstJetPacket period hPeriod frame //
        ∀ direction,
          projection direction =
            globalMinimalPhysicalLLC0FirstJetLinearMap period hPeriod
              configuration.physical frame direction } :=
  ⟨⟨globalMinimalPhysicalPairedLLC0FirstJetCLM period hPeriod configuration data
      analysis realization plusBase minusBase frame,
    fun direction =>
      globalMinimalPhysicalPairedLLC0FirstJetCLM_apply period hPeriod
        configuration data analysis realization plusBase minusBase frame
          direction⟩⟩

end
end P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
end JanusFormal
