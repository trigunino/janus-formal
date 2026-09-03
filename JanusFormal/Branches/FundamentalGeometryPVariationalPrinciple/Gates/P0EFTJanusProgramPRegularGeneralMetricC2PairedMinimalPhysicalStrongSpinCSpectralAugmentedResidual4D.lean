import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongScalarGraphRieszResidual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMatterGraphMaximalSpectralResidual4D

/-! # Spectrally anchored residual for the authentic strong SpinC equation -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongSpinCSpectralAugmentedResidual4D

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
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalEulerLagrangeMatterGraphMaximalSpectralResidual4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSeparatingPDEResidual4D
open P0EFTJanusProgramPStateDependentAugmentedGraphRieszResidual4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMatterC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLocalEuler4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongEightSectorEuler4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongComponentwisePDEResidual4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongScalarGraphRieszResidual4D

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

local instance c2ScalarNormedAddCommGroup :
    NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup

local instance c2ScalarNormedSpace :
    NormedSpace Real (C2Scalar period hPeriod) := inferInstance

local instance programPPrimitiveSpinCMatterHilbertRealInnerProductSpace :
    InnerProductSpace Real ProgramPPrimitiveSpinCMatterHilbert :=
  InnerProductSpace.complexToReal

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

/-- The translated maximal-graph state carried by the authentic matter block. -/
def regularGeneralMetricC2PairedMinimalPhysicalStrongMatterGraphState :
    ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
      couplings.matterMassSquared :=
  regularGeneralMetricC2PairedMinimalPhysicalMatterGraphInput period hPeriod
    configuration couplings.matterMassSquared realization point

/-- The spectral graph form is the base coordinate; every other SpinC
contribution is retained exactly as the remainder. -/
def regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCSpectralAugmentedGraphData :
    StateDependentAugmentedGraphRieszData
      (Test := ProgramPPrimitiveSpinCMatterSmoothField period hPeriod)
      (Base := ProgramPPrimitiveSpinCMatterHilbert) where
  baseMap :=
    (programPPrimitiveSpinCMatterGraphFstRealCLM period hPeriod
      couplings.matterMassSquared).toLinearMap.comp realization.toGraph
  remainder :=
    regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterEulerCovectorAt
        period hPeriod configuration data analysis realization plusBase
          minusBase hBase measure point -
      (innerSL Real
        (programPPrimitiveSpinCMatterGraphMaximalSpectralResidual period hPeriod
          couplings.matterMassSquared
          (regularGeneralMetricC2PairedMinimalPhysicalStrongMatterGraphState
            period hPeriod configuration realization point))).toLinearMap.comp
        ((programPPrimitiveSpinCMatterGraphFstRealCLM period hPeriod
          couplings.matterMassSquared).toLinearMap.comp realization.toGraph)
  baseCovector := innerSL Real
    (programPPrimitiveSpinCMatterGraphMaximalSpectralResidual period hPeriod
      couplings.matterMassSquared
        (regularGeneralMetricC2PairedMinimalPhysicalStrongMatterGraphState period
          hPeriod configuration realization point))

/-- The augmented total covector is definitionally the complete authentic
SpinC sector covector, with no dropped cross-block. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCSpectralAugmented_totalCovector :
    stateDependentAugmentedTotalCovector
        (regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCSpectralAugmentedGraphData
          period hPeriod configuration data analysis realization plusBase
            minusBase hBase measure point) =
      regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterEulerCovectorAt
        period hPeriod configuration data analysis realization plusBase
          minusBase hBase measure point := by
  apply LinearMap.ext
  intro test
  simp [stateDependentAugmentedTotalCovector,
    regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCSpectralAugmentedGraphData]

/-- Separating residual representation with an explicit SpinC spectral base
and an exact interaction remainder. -/
def regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCSpectralAugmentedResidualRepresentation :
    SeparatingPDEResidualRepresentation
      (regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterEulerCovectorAt
        period hPeriod configuration data analysis realization plusBase
          minusBase hBase measure point) := by
  rw [← regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCSpectralAugmented_totalCovector
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase measure point]
  exact stateDependentAugmentedGraphResidualRepresentation
    (regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCSpectralAugmentedGraphData
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point)

/-- The spectral anchor remains the explicit multiplier `(2D + m²)c`. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongMatterGraphState_spectralResidual_apply
    (mode : ProgramPPrimitiveSpinCMatterMode) :
    programPPrimitiveSpinCMatterGraphMaximalSpectralResidual period hPeriod
        couplings.matterMassSquared
        (regularGeneralMetricC2PairedMinimalPhysicalStrongMatterGraphState
          period hPeriod configuration realization point) mode =
      ((programPPrimitiveSpinCMatterHessianWeight period hPeriod
        couplings.matterMassSquared mode : Real) : Complex) *
        (regularGeneralMetricC2PairedMinimalPhysicalStrongMatterGraphState
          period hPeriod configuration realization point).1.1 mode :=
  programPPrimitiveSpinCMatterGraphMaximalSpectralResidual_apply period hPeriod
    couplings.matterMassSquared
      (regularGeneralMetricC2PairedMinimalPhysicalStrongMatterGraphState period
        hPeriod configuration realization point) mode

/-- Componentwise data upgraded from a scalar SpinC graph to the genuine
spectral graph form plus exact interaction remainder. -/
def regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCSpectralGraphPDEDataAt :
    RegularGeneralMetricC2PairedMinimalPhysicalStrongComponentwisePDEDataAt
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point :=
  { regularGeneralMetricC2PairedMinimalPhysicalStrongScalarGraphPDEDataAt
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point with
    spinC :=
      regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCSpectralAugmentedResidualRepresentation
        period hPeriod configuration data analysis realization plusBase
          minusBase hBase measure point }

def RegularGeneralMetricC2PairedMinimalPhysicalStrongSpinCSpectralGraphRieszSystemAt :
    Prop :=
  RegularGeneralMetricC2PairedMinimalPhysicalComponentwiseStrongPDESystemAt
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase measure point
        (regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCSpectralGraphPDEDataAt
          period hPeriod configuration data analysis realization plusBase
            minusBase hBase measure point)

/-- Euler vanishing is equivalent to the eight residual equations with the
SpinC equation spectrally anchored. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongEuler_eq_zero_iff_spinCSpectralGraphRieszSystem :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLagrangeOperator
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase measure point = 0 ↔
      RegularGeneralMetricC2PairedMinimalPhysicalStrongSpinCSpectralGraphRieszSystemAt
        period hPeriod configuration data analysis realization plusBase
          minusBase hBase measure point :=
  regularGeneralMetricC2PairedMinimalPhysicalStrongEuler_eq_zero_iff_componentwiseStrongPDE
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase measure point
        (regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCSpectralGraphPDEDataAt
          period hPeriod configuration data analysis realization plusBase
            minusBase hBase measure point)

/-- Gate marker: the complete SpinC Euler equation has an explicit spectral
base and retains every coupled remainder. -/
theorem regular_general_metric_c2_paired_minimal_physical_strong_spinc_spectral_augmented_residual_gate
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
      RegularGeneralMetricC2PairedMinimalPhysicalStrongSpinCSpectralGraphRieszSystemAt
        period hPeriod configuration data analysis realization plusBase
          minusBase hBase measure point :=
  regularGeneralMetricC2PairedMinimalPhysicalStrongEuler_eq_zero_iff_spinCSpectralGraphRieszSystem
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase measure point

end

end
end P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongSpinCSpectralAugmentedResidual4D
end JanusFormal
