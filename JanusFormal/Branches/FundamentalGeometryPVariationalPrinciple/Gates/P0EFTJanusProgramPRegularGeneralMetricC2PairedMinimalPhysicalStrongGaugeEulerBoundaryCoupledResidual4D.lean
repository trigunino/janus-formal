import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongGaugeCoupledResidual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellCanonicalEulerBoundary4D

/-! # Euler--boundary form of the coupled strong gauge residual -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongGaugeEulerBoundaryCoupledResidual4D

set_option autoImplicit false
set_option maxHeartbeats 400000
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
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartMaxwell4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartRegularMetric4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalConstantBoundaryC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongEightSectorEuler4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongGaugeCoupledResidual4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellCanonicalEulerBoundary4D
open P0EFTJanusProgramPRegularFrameGaugePotentialReconstruction4D

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

/-- The two Maxwell terms of the coupled gauge residual written globally as
integrals of their canonical local Euler-minus-boundary densities. -/
def regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeEulerBoundaryCoupledResidual
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (test : GlobalMinimalPhysicalGaugeTest period hPeriod) : Real :=
  let plusMetric := regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
    plusBase (point.1.completeVariation.fullMetricPerturbation .plus)
      hPoint.plus_mem
  let minusMetric := regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
    minusBase (point.1.completeVariation.fullMetricPerturbation .minus)
      hPoint.minus_mem
  let plusPotential := regularFrameGaugePotentialFromCoefficients period hPeriod
    plusMetric (configuration.physical.coefficientFields.gauge.1 +
      point.1.completeVariation.independent.gauge.1)
  let minusPotential := regularFrameGaugePotentialFromCoefficients period hPeriod
    minusMetric (configuration.physical.coefficientFields.gauge.2 +
      point.1.completeVariation.independent.gauge.2)
  let plusVariation := regularFrameGaugePotentialFromCoefficients period hPeriod
    plusMetric test.1
  let minusVariation := regularFrameGaugePotentialFromCoefficients period hPeriod
    minusMetric test.2
  couplings.plusMaxwellScale *
      canonicalRegularMaxwellEulerBoundaryResidualIntegral period hPeriod
        plusMetric plusPotential plusVariation measure +
    couplings.minusMaxwellScale *
      canonicalRegularMaxwellEulerBoundaryResidualIntegral period hPeriod
        minusMetric minusPotential minusVariation measure +
    regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeCoupledRemainder
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point test

omit [IsFiniteMeasure measure] in
/-- The weak coupled residual and its canonical Euler--boundary form agree
exactly, with no boundary cancellation assumption. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeWeakCoupledResidual_eq_eulerBoundaryCoupledResidual
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (test : GlobalMinimalPhysicalGaugeTest period hPeriod) :
    regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeWeakCoupledResidual
        period hPeriod configuration data analysis realization plusBase
          minusBase hBase measure point hPoint test =
      regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeEulerBoundaryCoupledResidual
        period hPeriod configuration data analysis realization plusBase
          minusBase hBase measure point hPoint test := by
  unfold regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeWeakCoupledResidual
    regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeEulerBoundaryCoupledResidual
  dsimp only
  rw [← canonicalRegularMaxwellEulerBoundaryResidualIntegral_eq_intrinsicMaxwellFirstVariation,
    ← canonicalRegularMaxwellEulerBoundaryResidualIntegral_eq_intrinsicMaxwellFirstVariation]

/-- The total strong gauge covector is the canonical integral of the two
local Maxwell Euler-minus-boundary densities plus every coupled remainder. -/
theorem regular_general_metric_c2_paired_minimal_physical_strong_gauge_euler_boundary_coupled_residual_gate
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (test : GlobalMinimalPhysicalGaugeTest period hPeriod) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeEulerCovectorAt period
        hPeriod configuration data analysis realization plusBase minusBase hBase
          measure point test =
      regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeEulerBoundaryCoupledResidual
        period hPeriod configuration data analysis realization plusBase
          minusBase hBase measure point hPoint test := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
    hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  calc
    _ = regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeWeakCoupledResidual
          period hPeriod configuration data analysis realization plusBase
            minusBase hBase measure point hPoint test :=
      regular_general_metric_c2_paired_minimal_physical_strong_gauge_coupled_residual_gate
        period hPeriod configuration data analysis realization plusBase
          minusBase hBase measure point hPoint test
    _ = _ :=
      regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeWeakCoupledResidual_eq_eulerBoundaryCoupledResidual
        period hPeriod configuration data analysis realization plusBase
          minusBase hBase measure point hPoint test

/-- Strong gauge stationarity is exactly the vanishing of the canonical
Euler--boundary coupled residual on every paired gauge test. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeEuler_eq_zero_iff_eulerBoundaryCoupledResidual
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeEulerCovectorAt period
        hPeriod configuration data analysis realization plusBase minusBase hBase
          measure point = 0 ↔
      ∀ test : GlobalMinimalPhysicalGaugeTest period hPeriod,
        regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeEulerBoundaryCoupledResidual
          period hPeriod configuration data analysis realization plusBase
            minusBase hBase measure point hPoint test = 0 := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
    hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  constructor
  · intro hStationary test
    rw [← regular_general_metric_c2_paired_minimal_physical_strong_gauge_euler_boundary_coupled_residual_gate
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point hPoint test]
    rw [hStationary]
    rfl
  · intro hResidual
    apply LinearMap.ext
    intro test
    rw [regular_general_metric_c2_paired_minimal_physical_strong_gauge_euler_boundary_coupled_residual_gate
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point hPoint test]
    simpa using hResidual test

end

end
end P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongGaugeEulerBoundaryCoupledResidual4D
end JanusFormal
