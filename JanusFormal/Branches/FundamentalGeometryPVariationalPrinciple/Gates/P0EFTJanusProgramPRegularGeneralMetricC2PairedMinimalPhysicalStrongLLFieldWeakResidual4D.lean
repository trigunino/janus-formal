import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLLWeakFirstVariation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusPTSymmetricLLWeakEulerJacobiOperator4D

/-! # Weak LL-field residual of the authentic strong LL block -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldWeakResidual4D

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 1200000

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusConvexHelmholtzReconstruction
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
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
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
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLLWeakFirstVariation4D
open P0EFTJanusDifferentialLLFullCurveActionDecomposition4D
open P0EFTJanusFullLLVariationalAPI4D
open P0EFTJanusMappingTorusPTSymmetricLLWeakEulerJacobiOperator4D

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

/-- A pure weak test of the physical LL flux field. -/
abbrev RegularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldTest :=
  LLWeakTestSpace period hPeriod

/-- Embed a weak LL-field test into the three authentic LL slots. -/
def regularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldThreeSlotTest
    (test : RegularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldTest
      period hPeriod) :
    RegularGeneralMetricC2PairedMinimalPhysicalStrongLLTest period hPeriod :=
  (0, (0, test))

/-- Pure LL-field direction in the authentic strong tangent. -/
def regularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldDirection
    (configuration : GlobalFieldConfiguration period hPeriod)
    (test : RegularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldTest
      period hPeriod) :
    GlobalMinimalPhysicalFieldTangent period hPeriod configuration :=
  regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection period hPeriod
    configuration
      (regularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldThreeSlotTest
        period hPeriod test)

/-- On a pure flux-field test, the full three-slot LL first variation is the
existing weak LL Euler functional. -/
theorem fullLLEuler_pureStrongLLField_eq_weakLLEulerOperator
    (fields : IndependentFields period hPeriod)
    (test : RegularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldTest
      period hPeriod) :
    fullLLEuler period hPeriod (canonicalDivergenceFreeLLFrame period hPeriod)
        fields
        (regularGeneralMetricC2PairedMinimalPhysicalStrongLLAPIDirection period
          hPeriod
          (regularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldThreeSlotTest
            period hPeriod test))
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) =
      weakLLEulerOperator period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod) fields
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) test := by
  have hFull := truePTAction_fullCurve_hasDerivAt_fullLLEuler period hPeriod
    (canonicalDivergenceFreeLLFrame period hPeriod) fields
    (regularGeneralMetricC2PairedMinimalPhysicalStrongLLAPIDirection period
      hPeriod
      (regularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldThreeSlotTest
        period hPeriod test))
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
  have hWeak :=
    globalPTSymmetricDifferentialLLAction_fluxCurve_hasDerivAt_weakEuler
      period hPeriod (canonicalDivergenceFreeLLFrame period hPeriod) fields test
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
  have hFull' :
      HasDerivAt (fun t : Real =>
        globalPTSymmetricDifferentialLLAction period hPeriod
          (canonicalDivergenceFreeLLFrame period hPeriod)
          (differentialLLFluxCurve period hPeriod fields test t)
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod))
        (fullLLEuler period hPeriod
          (canonicalDivergenceFreeLLFrame period hPeriod) fields
          (regularGeneralMetricC2PairedMinimalPhysicalStrongLLAPIDirection period
            hPeriod
            (regularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldThreeSlotTest
              period hPeriod test))
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod)) 0 := by
    simpa [regularGeneralMetricC2PairedMinimalPhysicalStrongLLAPIDirection,
      regularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldThreeSlotTest,
      differentialLLFullCurve, differentialLLFluxCurve] using hFull
  exact hFull'.unique hWeak

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

/-- Gate: the pure LL-field component of the authentic strong LL block is
exactly its pre-existing weak Euler residual. -/
theorem regular_general_metric_c2_paired_minimal_physical_strong_LL_field_weak_residual_gate
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (point : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration.physical)
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (test : RegularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldTest
      period hPeriod) :
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
        (regularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldDirection period
          hPeriod configuration.physical test) =
      weakLLEulerOperator period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod)
        (regularGeneralMetricC2PairedMinimalPhysicalLLFieldsInput period hPeriod
          configuration.physical point)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) test := by
  rw [regularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldDirection]
  rw [regular_general_metric_c2_paired_minimal_physical_strong_LL_weak_first_variation_gate
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase measure point hPoint
      (regularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldThreeSlotTest
        period hPeriod test)]
  exact fullLLEuler_pureStrongLLField_eq_weakLLEulerOperator period hPeriod
    (regularGeneralMetricC2PairedMinimalPhysicalLLFieldsInput period hPeriod
      configuration.physical point) test

end

end
end P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldWeakResidual4D
end JanusFormal
