import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongSpinCSpectralAugmentedResidual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullLLVariationalAPI4D

/-! # Explicit weak first variation of the authentic strong LL block -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLLWeakFirstVariation4D

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 1200000

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSevenBulkSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSectorSystem4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalConstantBoundaryC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongComponentPDEBlockPairing4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLocalEuler4D
open P0EFTJanusFullMatterRobinLLDirections4D
open P0EFTJanusDifferentialLLFullCurveActionDecomposition4D
open P0EFTJanusFullLLVariationalAPI4D

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

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance effectiveThroatCompactSpace :
    CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance canonicalThroatMeasureIsFinite :
    IsFiniteMeasure (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod

local instance c2ScalarNormedAddCommGroup :
    NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup

local instance c2ScalarNormedSpace :
    NormedSpace Real (C2Scalar period hPeriod) := inferInstance

local instance globalMinimalPhysicalBulkTangentAddCommGroup :
    AddCommGroup (GlobalMinimalPhysicalBulkTangent period hPeriod) :=
  Submodule.addCommGroup (GlobalMinimalPhysicalBulkTangent period hPeriod)

local instance globalMinimalPhysicalBulkTangentModule :
    Module Real (GlobalMinimalPhysicalBulkTangent period hPeriod) :=
  Submodule.module (GlobalMinimalPhysicalBulkTangent period hPeriod)

/-- The three genuinely variable LL test slots. -/
abbrev RegularGeneralMetricC2PairedMinimalPhysicalStrongLLTest :=
  SmoothThroatField period hPeriod LLMetricFiber ×
    (SmoothThroatField period hPeriod Real ×
      SmoothThroatField period hPeriod LLFieldFiber)

/-- The same three-slot test in the already proved physical LL variational API. -/
def regularGeneralMetricC2PairedMinimalPhysicalStrongLLAPIDirection
    (test : RegularGeneralMetricC2PairedMinimalPhysicalStrongLLTest period hPeriod) :
    FullMatterRobinLLDirections period hPeriod where
  common :=
    { metric := 0
      matter := 0
      gauge := 0
      ghost := 0
      auxiliary := 0
      ll := test.2.2 }
  robin := 0
  llAuxMetric := test.1
  llMeasure := test.2.1

/-- Pure three-slot LL direction in the authentic strong tangent. -/
def regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection
    (configuration : GlobalFieldConfiguration period hPeriod)
    (test : RegularGeneralMetricC2PairedMinimalPhysicalStrongLLTest period hPeriod) :
    GlobalMinimalPhysicalFieldTangent period hPeriod configuration :=
  regularGeneralMetricC2PairedMinimalPhysicalStrongSevenBulkDirection period
    hPeriod configuration
      (0, (0, (0, (0, (test.1, (test.2.1, test.2.2))))))

section

variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*}
variable [Fintype NonNullFace] [Fintype NullFace]
variable (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
variable (data : GlobalCandidateAActionData period hPeriod
  configuration.physical couplings NonNullFace NullFace)
variable (analysis : GlobalAnalysisData period hPeriod configuration.physical)
variable (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
  period hPeriod couplings.matterMassSquared)
variable (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)

/-- Translating a strong point along a pure LL test is exactly the old
three-slot affine LL curve. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalLLFieldsInput_strongLLLine
    (point : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration.physical)
    (test : RegularGeneralMetricC2PairedMinimalPhysicalStrongLLTest period hPeriod)
    (t : Real) :
    regularGeneralMetricC2PairedMinimalPhysicalLLFieldsInput period hPeriod
        configuration.physical
        (point + t • regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection
          period hPeriod configuration.physical test) =
      differentialLLFullCurve period hPeriod
        (regularGeneralMetricC2PairedMinimalPhysicalLLFieldsInput period hPeriod
          configuration.physical point)
        test.1 test.2.1 test.2.2 t := by
  apply IndependentFields.ext <;>
    simp [regularGeneralMetricC2PairedMinimalPhysicalLLFieldsInput,
      differentialLLFullCurve,
      regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection,
      regularGeneralMetricC2PairedMinimalPhysicalStrongSevenBulkDirection,
      globalMinimalPhysicalSevenBulkEquiv,
      globalMinimalPhysicalTangentSectorEquiv,
      GlobalPhysicalFieldTangent.completeVariation, add_assoc]
  · change
      (GlobalPhysicalFieldTangent.completeVariation period hPeriod point.1).independent.llAuxMetric +
          t • test.1 =
        (GlobalPhysicalFieldTangent.completeVariation period hPeriod point.1).independent.llAuxMetric +
          t • test.1
    rfl
  · change
      (GlobalPhysicalFieldTangent.completeVariation period hPeriod point.1).independent.llMeasure +
          t • test.2.1 =
        (GlobalPhysicalFieldTangent.completeVariation period hPeriod point.1).independent.llMeasure +
          t • test.2.1
    rfl
  · change
      (GlobalPhysicalFieldTangent.completeVariation period hPeriod point.1).independent.llField +
          t • test.2.2 =
        (GlobalPhysicalFieldTangent.completeVariation period hPeriod point.1).independent.llField +
          t • test.2.2
    rfl

/-- The Fréchet derivative of the authentic nonlinear LL block is its already
proved explicit weak first-variation integral on every pure LL test. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalLLAction_fderiv_apply_strongLLDirection
    (point : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration.physical)
    (test : RegularGeneralMetricC2PairedMinimalPhysicalStrongLLTest period hPeriod) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    fderiv Real
        (regularGeneralMetricC2PairedMinimalPhysicalLLAction period hPeriod
          configuration.physical) point
        (regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection period
          hPeriod configuration.physical test) =
      fullLLEuler period hPeriod (canonicalDivergenceFreeLLFrame period hPeriod)
        (regularGeneralMetricC2PairedMinimalPhysicalLLFieldsInput period hPeriod
          configuration.physical point)
        (regularGeneralMetricC2PairedMinimalPhysicalStrongLLAPIDirection period
          hPeriod test)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  let action := regularGeneralMetricC2PairedMinimalPhysicalLLAction period hPeriod
    configuration.physical
  let direction := regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection
    period hPeriod configuration.physical test
  have hAction : HasFDerivAt action (fderiv Real action point) point :=
    (regularGeneralMetricC2PairedMinimalPhysicalLLAction_contDiff period hPeriod
      configuration data analysis realization plusBase minusBase).contDiffAt
        |>.differentiableAt (by norm_num) |>.hasFDerivAt
  have hLine : HasDerivAt (fun t : Real => point + t • direction) direction 0 := by
    have hConstant : HasDerivAt (fun _ : Real => point) 0 0 :=
      hasDerivAt_const (x := (0 : Real)) (c := point)
    have hLinear := (hasDerivAt_id (0 : Real)).smul_const direction
    exact (hConstant.add hLinear).congr_deriv (by simp)
  have hFrechet := hAction.comp_hasDerivAt_of_eq 0 hLine (by simp)
  have hExplicit := truePTAction_fullCurve_hasDerivAt_fullLLEuler period hPeriod
    (canonicalDivergenceFreeLLFrame period hPeriod)
    (regularGeneralMetricC2PairedMinimalPhysicalLLFieldsInput period hPeriod
      configuration.physical point)
    (regularGeneralMetricC2PairedMinimalPhysicalStrongLLAPIDirection period
      hPeriod test)
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
  have hFunctions :
      (fun t : Real => action (point + t • direction)) =
        (fun t : Real =>
          P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D.globalPTSymmetricDifferentialLLAction
            period hPeriod (canonicalDivergenceFreeLLFrame period hPeriod)
            (differentialLLFullCurve period hPeriod
              (regularGeneralMetricC2PairedMinimalPhysicalLLFieldsInput period
                hPeriod configuration.physical point)
              test.1 test.2.1 test.2.2 t)
            (intrinsicCanonicalThroatVolumeMeasure period hPeriod)) := by
    funext t
    rw [show action (point + t • direction) =
        regularGeneralMetricC2PairedMinimalPhysicalLLAction period hPeriod
          configuration.physical (point + t • direction) by rfl]
    rw [regularGeneralMetricC2PairedMinimalPhysicalLLAction_eq_physical]
    rw [regularGeneralMetricC2PairedMinimalPhysicalLLFieldsInput_strongLLLine
      period hPeriod configuration]
  have hFrechet' :
      HasDerivAt (fun t : Real => action (point + t • direction))
        (fderiv Real action point direction) 0 := by
    simpa [Function.comp_def] using hFrechet
  rw [hFunctions] at hFrechet'
  exact hFrechet'.unique hExplicit

/-- Gate: on the open admissible strong chart, the authentic LL action block
has the explicit three-slot weak Euler variation. -/
theorem regular_general_metric_c2_paired_minimal_physical_strong_LL_weak_first_variation_gate
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (point : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration.physical)
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (test : RegularGeneralMetricC2PairedMinimalPhysicalStrongLLTest period hPeriod) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    actionGradient
        (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
          period hPeriod configuration.physical couplings data plusBase minusBase
            hBase measure).ll point
        (regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection period
          hPeriod configuration.physical test) =
      fullLLEuler period hPeriod (canonicalDivergenceFreeLLFrame period hPeriod)
        (regularGeneralMetricC2PairedMinimalPhysicalLLFieldsInput period hPeriod
          configuration.physical point)
        (regularGeneralMetricC2PairedMinimalPhysicalStrongLLAPIDirection period
          hPeriod test)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  let blocks :=
    regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
      period hPeriod configuration.physical couplings data plusBase minusBase
        hBase measure
  have hOpen :=
    regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain_strong_isOpen
      period hPeriod configuration data analysis realization plusBase minusBase
  have hEventually :
      blocks.ll =ᶠ[nhds point]
        regularGeneralMetricC2PairedMinimalPhysicalLLAction period hPeriod
          configuration.physical := by
    filter_upwards [hOpen.mem_nhds hPoint] with direction hDirection
    exact regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_ll_eq
      period hPeriod configuration.physical data plusBase minusBase hBase measure
        direction hDirection
  change fderiv Real blocks.ll point
      (regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection period
        hPeriod configuration.physical test) = _
  rw [hEventually.fderiv_eq]
  exact
    regularGeneralMetricC2PairedMinimalPhysicalLLAction_fderiv_apply_strongLLDirection
      period hPeriod configuration data analysis realization plusBase minusBase
        point test

end

end
end P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLLWeakFirstVariation4D
end JanusFormal
