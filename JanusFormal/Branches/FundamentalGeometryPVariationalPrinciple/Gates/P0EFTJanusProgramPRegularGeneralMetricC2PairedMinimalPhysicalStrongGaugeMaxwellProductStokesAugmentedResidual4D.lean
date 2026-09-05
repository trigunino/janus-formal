import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongGaugeMaxwellWeightedAugmentedResidual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameMaxwellProductStokesWeakStrong4D

/-! # Product-Stokes Maxwell residual in the full strong PDE system -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongGaugeMaxwellProductStokesAugmentedResidual4D

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
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProductCoarea4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSeparatingPDEResidual4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartRegularMetric4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartMaxwell4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLocalEuler4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongEightSectorEuler4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongComponentwisePDEResidual4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongGaugeMaxwellWeightedAugmentedResidual4D
open P0EFTJanusProgramPRegularFrameGaugePotentialReconstruction4D
open P0EFTJanusProgramPRegularFrameMaxwellCanonicalWeightedEulerBoundary4D
open P0EFTJanusProgramPRegularFrameMaxwellProductStokesWeakStrong4D

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

local instance intrinsicCanonicalLorentzVolumeMeasureIsFinite :
    IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

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
variable (point : GlobalMinimalPhysicalFieldTangent period hPeriod
  configuration.physical)

/-- Product Stokes data for the two authentic Maxwell sectors at one physical
configuration point. -/
structure RegularGeneralMetricC2PairedStrongGaugeMaxwellProductStokesData
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) where
  plus : RegularFrameMaxwellProductStokesData period hPeriod
    (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod plusBase
      (point.1.completeVariation.fullMetricPerturbation .plus) hPoint.plus_mem)
    (regularFrameGaugePotentialFromCoefficients period hPeriod
      (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod plusBase
        (point.1.completeVariation.fullMetricPerturbation .plus) hPoint.plus_mem)
      (configuration.physical.coefficientFields.gauge.1 +
        point.1.completeVariation.independent.gauge.1))
  minus : RegularFrameMaxwellProductStokesData period hPeriod
    (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod minusBase
      (point.1.completeVariation.fullMetricPerturbation .minus) hPoint.minus_mem)
    (regularFrameGaugePotentialFromCoefficients period hPeriod
      (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod minusBase
        (point.1.completeVariation.fullMetricPerturbation .minus) hPoint.minus_mem)
      (configuration.physical.coefficientFields.gauge.2 +
        point.1.completeVariation.independent.gauge.2))

/-- Boundary-free product residual obtained from the two weighted strong
Maxwell pairings. -/
def regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeMaxwellProductResidual
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
      (∫ parameter,
        canonicalRegularMaxwellProductWeightedStrongDensity period hPeriod
          plusMetric plusPotential plusVariation parameter
        ∂canonicalLatitudeCauchyJetProductMeasure period) +
    couplings.minusMaxwellScale *
      ∫ parameter,
        canonicalRegularMaxwellProductWeightedStrongDensity period hPeriod
          minusMetric minusPotential minusVariation parameter
        ∂canonicalLatitudeCauchyJetProductMeasure period

/-- For the canonical physical measure, paired product Stokes removes the two
boundary divergences from the exact weighted gauge residual. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeMaxwellWeightedResidual_eq_product
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (stokes : RegularGeneralMetricC2PairedStrongGaugeMaxwellProductStokesData
      period hPeriod configuration plusBase minusBase point hPoint)
    (test : GlobalMinimalPhysicalGaugeTest period hPeriod) :
    regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeMaxwellWeightedResidual
        period hPeriod (couplings := couplings) configuration plusBase minusBase
          (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) point hPoint
            test =
      regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeMaxwellProductResidual
        period hPeriod (couplings := couplings) configuration plusBase minusBase
          point hPoint test := by
  unfold
    regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeMaxwellWeightedResidual
    regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeMaxwellProductResidual
  dsimp only
  rw [canonicalRegularMaxwellWeightedStrongBoundaryResidualIntegral_eq_firstVariation,
    canonicalRegularMaxwellWeightedStrongBoundaryResidualIntegral_eq_firstVariation,
    intrinsicMaxwellFirstVariation_eq_integral_productWeightedStrong
      period hPeriod _ _ _ stokes.plus,
    intrinsicMaxwellFirstVariation_eq_integral_productWeightedStrong
      period hPeriod _ _ _ stokes.minus]

/-- The gauge Euler covector is exactly the boundary-free product strong
Maxwell residual under paired Stokes. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeEuler_eq_productMaxwell
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (stokes : RegularGeneralMetricC2PairedStrongGaugeMaxwellProductStokesData
      period hPeriod configuration plusBase minusBase point hPoint)
    (test : GlobalMinimalPhysicalGaugeTest period hPeriod) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeEulerCovectorAt period
        hPeriod configuration data analysis realization plusBase minusBase hBase
          (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) point test =
      regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeMaxwellProductResidual
        period hPeriod (couplings := couplings) configuration plusBase minusBase
          point hPoint test := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
    hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  rw [regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeEuler_eq_weightedMaxwell
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) point hPoint
        test,
    regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeMaxwellWeightedResidual_eq_product
      period hPeriod configuration plusBase minusBase point hPoint stokes test]

/-- Separating representation whose gauge coordinate is the boundary-free
product Maxwell residual. -/
def regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeMaxwellProductResidualRepresentation
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (stokes : RegularGeneralMetricC2PairedStrongGaugeMaxwellProductStokesData
      period hPeriod configuration plusBase minusBase point hPoint) :
    SeparatingPDEResidualRepresentation
      (regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeEulerCovectorAt
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) point) := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
    hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  exact
    { Residual := GlobalMinimalPhysicalGaugeTest period hPeriod → Real
      zeroResidual := 0
      residual := fun test ↦
        regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeMaxwellProductResidual
          period hPeriod (couplings := couplings) configuration plusBase minusBase
            point hPoint test
      pairing := fun residual test ↦ residual test
      represents := fun test ↦
        regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeEuler_eq_productMaxwell
          period hPeriod configuration data analysis realization plusBase minusBase
            hBase point hPoint stokes test
      separates := by
        constructor
        · intro hZero
          funext test
          exact hZero test
        · intro hZero test
          rw [hZero]
          rfl }

/-- Eight-sector data with the canonical-measure gauge coordinate reduced to
the boundary-free product Maxwell residual. -/
def regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCSpectralLLFieldGaugeMaxwellProductStokesAugmentedPDEDataAt
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (stokes : RegularGeneralMetricC2PairedStrongGaugeMaxwellProductStokesData
      period hPeriod configuration plusBase minusBase point hPoint) :
    RegularGeneralMetricC2PairedMinimalPhysicalStrongComponentwisePDEDataAt
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) point :=
  { regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCSpectralLLFieldGaugeMaxwellWeightedAugmentedPDEDataAt
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) point hPoint with
    gauge :=
      regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeMaxwellProductResidualRepresentation
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase point hPoint stokes }

/-- Complete canonical-measure system with its boundary-free product Maxwell
gauge coordinate. -/
def RegularGeneralMetricC2PairedMinimalPhysicalStrongSpinCSpectralLLFieldGaugeMaxwellProductStokesAugmentedSystemAt
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (stokes : RegularGeneralMetricC2PairedStrongGaugeMaxwellProductStokesData
      period hPeriod configuration plusBase minusBase point hPoint) : Prop :=
  RegularGeneralMetricC2PairedMinimalPhysicalComponentwiseStrongPDESystemAt
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) point
        (regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCSpectralLLFieldGaugeMaxwellProductStokesAugmentedPDEDataAt
          period hPeriod configuration data analysis realization plusBase minusBase
            hBase point hPoint stokes)

/-- The full Euler operator is equivalent to the canonical-measure system
whose Maxwell gauge coordinate is boundary-free under paired Stokes. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongEuler_eq_zero_iff_productStokesAugmentedSystem
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (stokes : RegularGeneralMetricC2PairedStrongGaugeMaxwellProductStokesData
      period hPeriod configuration plusBase minusBase point hPoint) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLagrangeOperator period
        hPeriod configuration data analysis realization plusBase minusBase hBase
          (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) point = 0 ↔
      RegularGeneralMetricC2PairedMinimalPhysicalStrongSpinCSpectralLLFieldGaugeMaxwellProductStokesAugmentedSystemAt
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase point hPoint stokes :=
  regularGeneralMetricC2PairedMinimalPhysicalStrongEuler_eq_zero_iff_componentwiseStrongPDE
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) point
        (regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCSpectralLLFieldGaugeMaxwellProductStokesAugmentedPDEDataAt
          period hPeriod configuration data analysis realization plusBase minusBase
            hBase point hPoint stokes)

/-- Gate marker for the full canonical-measure product-Stokes Maxwell
reduction. -/
theorem regular_general_metric_c2_paired_minimal_physical_strong_gauge_maxwell_product_stokes_augmented_residual_gate
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (stokes : RegularGeneralMetricC2PairedStrongGaugeMaxwellProductStokesData
      period hPeriod configuration plusBase minusBase point hPoint) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLagrangeOperator period
        hPeriod configuration data analysis realization plusBase minusBase hBase
          (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) point = 0 ↔
      RegularGeneralMetricC2PairedMinimalPhysicalStrongSpinCSpectralLLFieldGaugeMaxwellProductStokesAugmentedSystemAt
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase point hPoint stokes :=
  regularGeneralMetricC2PairedMinimalPhysicalStrongEuler_eq_zero_iff_productStokesAugmentedSystem
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase point hPoint stokes

end

end
end P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongGaugeMaxwellProductStokesAugmentedResidual4D
end JanusFormal
