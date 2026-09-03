import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongSpinCSpectralAugmentedResidual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldWeakResidual4D

/-! # Weakly anchored augmented residual for the authentic LL-field equation -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldWeakAugmentedResidual4D

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 1200000

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusPTSymmetricLLWeakEulerJacobiOperator4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSeparatingPDEResidual4D
open P0EFTJanusProgramPStateDependentAugmentedGraphRieszResidual4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalConstantBoundaryC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLocalEuler4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongEightSectorEuler4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongComponentwisePDEResidual4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongSpinCSpectralAugmentedResidual4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldWeakResidual4D

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
variable (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
  period hPeriod plusBase minusBase)
variable (measure : Measure (EffectiveQuotient period hPeriod))
variable [IsFiniteMeasure measure]
variable (point : GlobalMinimalPhysicalFieldTangent period hPeriod
  configuration.physical)

/-- The authentic weak LL Euler functional is the base scalar coordinate;
all other full-action contributions are retained exactly as the remainder. -/
def regularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldWeakAugmentedGraphData :
    StateDependentAugmentedGraphRieszData
      (Test := RegularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldTest
        period hPeriod)
      (Base := Real) where
  baseMap :=
    weakLLEulerOperator period hPeriod
      (canonicalDivergenceFreeLLFrame period hPeriod)
      (regularGeneralMetricC2PairedMinimalPhysicalLLFieldsInput period hPeriod
        configuration.physical point)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
  remainder :=
    regularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldEulerCovectorAt
        period hPeriod configuration data analysis realization plusBase
          minusBase hBase measure point -
      weakLLEulerOperator period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod)
        (regularGeneralMetricC2PairedMinimalPhysicalLLFieldsInput period hPeriod
          configuration.physical point)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
  baseCovector := ContinuousLinearMap.id Real Real

/-- The augmented total covector is exactly the complete authentic LL-field
sector covector. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldWeakAugmented_totalCovector :
    stateDependentAugmentedTotalCovector
        (regularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldWeakAugmentedGraphData
          period hPeriod configuration data analysis realization plusBase
            minusBase hBase measure point) =
      regularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldEulerCovectorAt
        period hPeriod configuration data analysis realization plusBase
          minusBase hBase measure point := by
  apply LinearMap.ext
  intro test
  simp [stateDependentAugmentedTotalCovector,
    regularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldWeakAugmentedGraphData]

/-- Separating residual representation with the physical weak LL Euler
functional as base and the exact coupled remainder. -/
def regularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldWeakAugmentedResidualRepresentation :
    SeparatingPDEResidualRepresentation
      (regularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldEulerCovectorAt
        period hPeriod configuration data analysis realization plusBase
          minusBase hBase measure point) := by
  rw [← regularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldWeakAugmented_totalCovector
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase measure point]
  exact stateDependentAugmentedGraphResidualRepresentation
    (regularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldWeakAugmentedGraphData
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point)

/-- On the admissible chart, the base coordinate is exactly the derivative of
the unchanged physical LL action block along a pure LL-field test. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldWeakAugmented_baseMap_apply
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
    (regularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldWeakAugmentedGraphData
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point).baseMap test =
      actionGradient
        (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
          period hPeriod configuration.physical couplings data plusBase minusBase
            hBase measure).ll point
        (regularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldDirection
          period hPeriod configuration.physical test) := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  exact (regular_general_metric_c2_paired_minimal_physical_strong_LL_field_weak_residual_gate
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase measure point hPoint test).symm

/-- The SpinC-spectral PDE data upgraded by the authentic weak LL-field base
and its exact coupled remainder. -/
def regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCSpectralLLFieldWeakAugmentedPDEDataAt :
    RegularGeneralMetricC2PairedMinimalPhysicalStrongComponentwisePDEDataAt
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point :=
  { regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCSpectralGraphPDEDataAt
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point with
    llField :=
      regularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldWeakAugmentedResidualRepresentation
        period hPeriod configuration data analysis realization plusBase
          minusBase hBase measure point }

/-- Eight residual equations retaining the SpinC spectral anchor and adding
the authentic weak LL-field anchor. -/
def RegularGeneralMetricC2PairedMinimalPhysicalStrongSpinCSpectralLLFieldWeakAugmentedSystemAt :
    Prop :=
  RegularGeneralMetricC2PairedMinimalPhysicalComponentwiseStrongPDESystemAt
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase measure point
        (regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCSpectralLLFieldWeakAugmentedPDEDataAt
          period hPeriod configuration data analysis realization plusBase
            minusBase hBase measure point)

/-- Euler vanishing is equivalent to the eight residual equations with both
the SpinC spectral and weak LL-field anchors. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongEuler_eq_zero_iff_spinCSpectralLLFieldWeakAugmentedSystem :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLagrangeOperator
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase measure point = 0 ↔
      RegularGeneralMetricC2PairedMinimalPhysicalStrongSpinCSpectralLLFieldWeakAugmentedSystemAt
        period hPeriod configuration data analysis realization plusBase
          minusBase hBase measure point :=
  regularGeneralMetricC2PairedMinimalPhysicalStrongEuler_eq_zero_iff_componentwiseStrongPDE
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase measure point
        (regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCSpectralLLFieldWeakAugmentedPDEDataAt
          period hPeriod configuration data analysis realization plusBase
            minusBase hBase measure point)

/-- Gate marker: the complete Euler system retains the SpinC spectral anchor
and has the authentic weak LL-field Euler functional as a second physical
base, with every coupled contribution preserved. -/
theorem regular_general_metric_c2_paired_minimal_physical_strong_LL_field_weak_augmented_residual_gate
    (_hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLagrangeOperator
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase measure point = 0 ↔
      RegularGeneralMetricC2PairedMinimalPhysicalStrongSpinCSpectralLLFieldWeakAugmentedSystemAt
        period hPeriod configuration data analysis realization plusBase
          minusBase hBase measure point :=
  regularGeneralMetricC2PairedMinimalPhysicalStrongEuler_eq_zero_iff_spinCSpectralLLFieldWeakAugmentedSystem
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase measure point

end

end
end P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldWeakAugmentedResidual4D
end JanusFormal
