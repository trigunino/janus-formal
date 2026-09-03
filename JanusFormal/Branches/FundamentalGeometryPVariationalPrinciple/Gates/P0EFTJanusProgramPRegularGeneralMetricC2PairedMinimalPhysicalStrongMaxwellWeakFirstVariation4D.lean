import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldWeakResidual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedGaugeCoefficientMaxwellAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusFrameFreeMaxwellPotentialHessian4D

/-! # Explicit weak first variation of the authentic Maxwell blocks -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellWeakFirstVariation4D

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 1200000

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusD8NonabelianGhostThroatBRST4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D
open P0EFTJanusMappingTorusFrameFreeMaxwellPotentialHessian4D
open P0EFTJanusMappingTorusConformalFrameFreeMaxwellHessian4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSectorSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSevenBulkSystem4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartRegularMetric4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartGeometry4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartMaxwell4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomainOpen4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalConstantBoundaryC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricGaugeCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedGaugeCoefficientMaxwellAction4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalNineBlockC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongComponentPDEBlockPairing4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLocalEuler4D
open P0EFTJanusProgramPRegularFrameGaugePotentialReconstruction4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D

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

local instance globalMinimalPhysicalBulkTangentAddCommGroup :
    AddCommGroup (GlobalMinimalPhysicalBulkTangent period hPeriod) :=
  Submodule.addCommGroup (GlobalMinimalPhysicalBulkTangent period hPeriod)

local instance globalMinimalPhysicalBulkTangentModule :
    Module Real (GlobalMinimalPhysicalBulkTangent period hPeriod) :=
  Submodule.module (GlobalMinimalPhysicalBulkTangent period hPeriod)

/-- Pure paired-gauge direction in the authentic strong tangent. -/
def regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeDirection
    (configuration : GlobalFieldConfiguration period hPeriod)
    (test : GlobalMinimalPhysicalGaugeTest period hPeriod) :
    GlobalMinimalPhysicalFieldTangent period hPeriod configuration :=
  regularGeneralMetricC2PairedMinimalPhysicalStrongSevenBulkDirection period
    hPeriod configuration (0, (test, (0, (0, (0, (0, 0))))))

@[simp]
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeDirection_fullMetricPerturbation
    (configuration : GlobalFieldConfiguration period hPeriod)
    (test : GlobalMinimalPhysicalGaugeTest period hPeriod) :
    ((regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeDirection period
      hPeriod configuration) test).1.completeVariation.fullMetricPerturbation = 0 :=
  rfl

@[simp]
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeDirection_gauge
    (configuration : GlobalFieldConfiguration period hPeriod)
    (test : GlobalMinimalPhysicalGaugeTest period hPeriod) :
    ((regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeDirection period
      hPeriod configuration) test).1.completeVariation.independent.gauge = test :=
  rfl

theorem regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeLine_mem
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (point : GlobalMinimalPhysicalFieldTangent period hPeriod configuration)
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration plusBase minusBase)
    (test : GlobalMinimalPhysicalGaugeTest period hPeriod) (t : Real) :
    point + t •
        (regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeDirection period
          hPeriod configuration) test ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration plusBase minusBase := by
  change GlobalMetricPerturbationPairLorentzChartAdmissible period hPeriod
    plusBase minusBase point.1.completeVariation.fullMetricPerturbation at hPoint
  change GlobalMetricPerturbationPairLorentzChartAdmissible period hPeriod
    plusBase minusBase
      ((point + t •
        (regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeDirection period
          hPeriod configuration) test).1.completeVariation.fullMetricPerturbation)
  change GlobalMetricPerturbationPairLorentzChartAdmissible period hPeriod
    plusBase minusBase
      (point.1.completeVariation.fullMetricPerturbation + t • 0)
  simpa using hPoint

private theorem regularFrameGaugePotentialFromCoefficients_add_smul
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (base direction : SmoothQuotientField period hPeriod GaugeFiber)
    (t : Real) :
    regularFrameGaugePotentialFromCoefficients period hPeriod metric
        (base + t • direction) =
      gaugePotentialLine period hPeriod
        (regularFrameGaugePotentialFromCoefficients period hPeriod metric base)
        (regularFrameGaugePotentialFromCoefficients period hPeriod metric direction) t := by
  apply gaugePotentialFrameCoefficientsLinearMap_injective period hPeriod metric
  change gaugePotentialFrameCoefficients period hPeriod metric
      (regularFrameGaugePotentialFromCoefficients period hPeriod metric
        (base + t • direction)) =
    gaugePotentialFrameCoefficients period hPeriod metric
      (gaugePotentialLine period hPeriod
        (regularFrameGaugePotentialFromCoefficients period hPeriod metric base)
        (regularFrameGaugePotentialFromCoefficients period hPeriod metric direction) t)
  rw [gaugePotentialFrameCoefficients_reconstructed]
  unfold gaugePotentialLine
  change base + t • direction =
    (gaugePotentialFrameCoefficientsLinearMap period hPeriod metric)
      (regularFrameGaugePotentialFromCoefficients period hPeriod metric base +
        t • regularFrameGaugePotentialFromCoefficients period hPeriod metric direction)
  rw [map_add, map_smul]
  simp [gaugePotentialFrameCoefficientsLinearMap]

private def regularIntrinsicMaxwellPairingLine
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (data : RegularIntrinsicMaxwellLine period hPeriod metric)
    (t : Real) : SmoothScalarField period hPeriod where
  toFun := fun point =>
    data.basePairing point + t * data.mixedPairing point +
      t ^ 2 * data.variationPairing point
  contMDiff_toFun :=
    data.basePairing.contMDiff_toFun.add
      (contMDiff_const.mul data.mixedPairing.contMDiff_toFun) |>.add
      (contMDiff_const.mul data.variationPairing.contMDiff_toFun)

private theorem globalSmoothMaxwellPairing_gaugePotentialLine_self
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (potential variation : SmoothAbelianGaugePotential period hPeriod)
    (t : Real) :
    globalSmoothMaxwellPairing period hPeriod metric.metric
        (gaugePotentialLine period hPeriod potential variation t)
        (gaugePotentialLine period hPeriod potential variation t) =
      regularIntrinsicMaxwellPairingLine period hPeriod metric
        (regularIntrinsicMaxwellLineOfPotentials period hPeriod metric
          potential variation) t := by
  apply SmoothQuotientField.ext
  intro point
  change globalMaxwellPairing period hPeriod metric.metric
      (potential + t • variation) (potential + t • variation) point = _
  rw [globalMaxwellPairing_add_left, globalMaxwellPairing_add_right,
    globalMaxwellPairing_add_right, globalMaxwellPairing_smul_left,
    globalMaxwellPairing_smul_right, globalMaxwellPairing_smul_right,
    globalMaxwellPairing_smul_left]
  simp only [regularIntrinsicMaxwellPairingLine,
    regularIntrinsicMaxwellLineOfPotentials, globalSmoothMaxwellPairing]
  change _ =
    globalMaxwellPairing period hPeriod metric.metric potential potential point +
      t * (globalMaxwellPairing period hPeriod metric.metric variation potential point +
        globalMaxwellPairing period hPeriod metric.metric potential variation point) +
      t ^ 2 * globalMaxwellPairing period hPeriod metric.metric variation variation point
  ring

private theorem regularGeneralMetricC2LorentzChartRegularMetric_congr
    (base : RegularGeneralLorentzMetric period hPeriod)
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hFirst : regularGeneralMetricSmoothC2Variation period hPeriod base first ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod base)
    (hSecond : regularGeneralMetricSmoothC2Variation period hPeriod base second ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod base)
    (h : first = second) :
    regularGeneralMetricC2LorentzChartRegularMetric period hPeriod base first hFirst =
      regularGeneralMetricC2LorentzChartRegularMetric period hPeriod base second hSecond := by
  subst second
  rfl

/-- Along a pure gauge line, the plus auxiliary action is the intrinsic
Maxwell quadratic line at the fixed varied metric. -/
theorem regularGeneralMetricC2PairedPlusFixedVolumeMaxwellAction_strongGaugeLine
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (point : GlobalMinimalPhysicalFieldTangent period hPeriod configuration)
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration plusBase minusBase)
    (test : GlobalMinimalPhysicalGaugeTest period hPeriod) (t : Real) :
    regularGeneralMetricC2PairedPlusFixedVolumeMaxwellAction period hPeriod
        configuration plusBase minusBase measure
          (globalMinimalPhysicalPairedMetricGaugeCoreLinearMap period hPeriod
            configuration plusBase minusBase
              (point + t •
                regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeDirection
                  period hPeriod configuration test)) =
      let metric := regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
        plusBase (point.1.completeVariation.fullMetricPerturbation .plus)
          hPoint.plus_mem
      let potential := regularFrameGaugePotentialFromCoefficients period hPeriod
        metric (configuration.coefficientFields.gauge.1 +
          point.1.completeVariation.independent.gauge.1)
      let variation := regularFrameGaugePotentialFromCoefficients period hPeriod
        metric test.1
      intrinsicMaxwellAction period hPeriod metric
        (regularIntrinsicMaxwellPairingLine period hPeriod metric
          (regularIntrinsicMaxwellLineOfPotentials period hPeriod metric
            potential variation) t) measure := by
  let direction :=
    regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeDirection period
      hPeriod configuration test
  let hLine :=
    regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeLine_mem period hPeriod
      configuration plusBase minusBase point hPoint test t
  rw [regularGeneralMetricC2PairedPlusFixedVolumeMaxwellAction_projected_smooth
    period hPeriod configuration plusBase minusBase measure
      (point + t • direction) hLine]
  dsimp only
  have hFull :
      (point + t • direction).1.completeVariation.fullMetricPerturbation =
        point.1.completeVariation.fullMetricPerturbation := by
    change point.1.completeVariation.fullMetricPerturbation + t • 0 = _
    simp
  have hMetric :=
    regularGeneralMetricC2LorentzChartRegularMetric_congr period hPeriod plusBase
      ((point + t • direction).1.completeVariation.fullMetricPerturbation .plus)
      (point.1.completeVariation.fullMetricPerturbation .plus)
      hLine.plus_mem hPoint.plus_mem (congrFun hFull .plus)
  rw [hMetric]
  have hGauge :
      configuration.coefficientFields.gauge.1 +
          (point + t • direction).1.completeVariation.independent.gauge.1 =
        (configuration.coefficientFields.gauge.1 +
          point.1.completeVariation.independent.gauge.1) + t • test.1 := by
    change configuration.coefficientFields.gauge.1 +
        (point.1.completeVariation.independent.gauge.1 + t • test.1) = _
    abel
  rw [hGauge,
    regularFrameGaugePotentialFromCoefficients_add_smul period hPeriod,
    globalSmoothMaxwellPairing_gaugePotentialLine_self period hPeriod]

/-- Along a pure gauge line, the minus auxiliary action is the intrinsic
Maxwell quadratic line at the fixed varied metric. -/
theorem regularGeneralMetricC2PairedMinusFixedVolumeMaxwellAction_strongGaugeLine
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (point : GlobalMinimalPhysicalFieldTangent period hPeriod configuration)
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration plusBase minusBase)
    (test : GlobalMinimalPhysicalGaugeTest period hPeriod) (t : Real) :
    regularGeneralMetricC2PairedMinusFixedVolumeMaxwellAction period hPeriod
        configuration plusBase minusBase measure
          (globalMinimalPhysicalPairedMetricGaugeCoreLinearMap period hPeriod
            configuration plusBase minusBase
              (point + t •
                regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeDirection
                  period hPeriod configuration test)) =
      let metric := regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
        minusBase (point.1.completeVariation.fullMetricPerturbation .minus)
          hPoint.minus_mem
      let potential := regularFrameGaugePotentialFromCoefficients period hPeriod
        metric (configuration.coefficientFields.gauge.2 +
          point.1.completeVariation.independent.gauge.2)
      let variation := regularFrameGaugePotentialFromCoefficients period hPeriod
        metric test.2
      intrinsicMaxwellAction period hPeriod metric
        (regularIntrinsicMaxwellPairingLine period hPeriod metric
          (regularIntrinsicMaxwellLineOfPotentials period hPeriod metric
            potential variation) t) measure := by
  let direction :=
    regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeDirection period
      hPeriod configuration test
  let hLine :=
    regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeLine_mem period hPeriod
      configuration plusBase minusBase point hPoint test t
  rw [regularGeneralMetricC2PairedMinusFixedVolumeMaxwellAction_projected_smooth
    period hPeriod configuration plusBase minusBase measure
      (point + t • direction) hLine]
  dsimp only
  have hFull :
      (point + t • direction).1.completeVariation.fullMetricPerturbation =
        point.1.completeVariation.fullMetricPerturbation := by
    change point.1.completeVariation.fullMetricPerturbation + t • 0 = _
    simp
  have hMetric :=
    regularGeneralMetricC2LorentzChartRegularMetric_congr period hPeriod minusBase
      ((point + t • direction).1.completeVariation.fullMetricPerturbation .minus)
      (point.1.completeVariation.fullMetricPerturbation .minus)
      hLine.minus_mem hPoint.minus_mem (congrFun hFull .minus)
  rw [hMetric]
  have hGauge :
      configuration.coefficientFields.gauge.2 +
          (point + t • direction).1.completeVariation.independent.gauge.2 =
        (configuration.coefficientFields.gauge.2 +
          point.1.completeVariation.independent.gauge.2) + t • test.2 := by
    change configuration.coefficientFields.gauge.2 +
        (point.1.completeVariation.independent.gauge.2 + t • test.2) = _
    abel
  rw [hGauge,
    regularFrameGaugePotentialFromCoefficients_add_smul period hPeriod,
    globalSmoothMaxwellPairing_gaugePotentialLine_self period hPeriod]

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

/-- The authentic plus Maxwell block has its exact intrinsic weak first
variation on every pure plus/minus gauge test. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalMaxwellPlus_fderiv_apply_strongGaugeDirection
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (point : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration.physical)
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
    fderiv Real
        (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
          period hPeriod configuration.physical couplings data plusBase minusBase
            hBase measure).maxwellPlus point
        (regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeDirection period
          hPeriod configuration.physical test) =
      let metric := regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
        plusBase (point.1.completeVariation.fullMetricPerturbation .plus)
          hPoint.plus_mem
      let potential := regularFrameGaugePotentialFromCoefficients period hPeriod
        metric (configuration.physical.coefficientFields.gauge.1 +
          point.1.completeVariation.independent.gauge.1)
      let variation := regularFrameGaugePotentialFromCoefficients period hPeriod
        metric test.1
      couplings.plusMaxwellScale *
        intrinsicMaxwellFirstVariation period hPeriod metric
          (regularIntrinsicMaxwellLineOfPotentials period hPeriod metric
            potential variation) measure := by
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
  let action := blocks.maxwellPlus
  let direction :=
    regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeDirection period
      hPeriod configuration.physical test
  let metric := regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
    plusBase (point.1.completeVariation.fullMetricPerturbation .plus)
      hPoint.plus_mem
  let potential := regularFrameGaugePotentialFromCoefficients period hPeriod
    metric (configuration.physical.coefficientFields.gauge.1 +
      point.1.completeVariation.independent.gauge.1)
  let variation := regularFrameGaugePotentialFromCoefficients period hPeriod
    metric test.1
  let line := regularIntrinsicMaxwellLineOfPotentials period hPeriod metric
    potential variation
  have hOpen :=
    regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain_strong_isOpen
      period hPeriod configuration data analysis realization plusBase minusBase
  have hSmooth :=
    (regularGeneralMetricC2PairedMinimalPhysicalActionBlocks_maxwell_strong_contDiffWithinAt
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point hPoint).1
  have hAction : HasFDerivAt action (fderiv Real action point) point :=
    (hSmooth.contDiffAt (hOpen.mem_nhds hPoint)).differentiableAt
      (by norm_num) |>.hasFDerivAt
  have hAffine : HasDerivAt (fun t : Real => point + t • direction) direction 0 := by
    exact ((hasDerivAt_const (x := (0 : Real)) (c := point)).add
      ((hasDerivAt_id (0 : Real)).smul_const direction)).congr_deriv (by simp)
  have hFrechet := hAction.comp_hasDerivAt_of_eq 0 hAffine (by simp)
  have hIntrinsic : HasDerivAt
      (fun t : Real => intrinsicMaxwellAction period hPeriod metric
        (regularIntrinsicMaxwellPairingLine period hPeriod metric line t) measure)
      (intrinsicMaxwellFirstVariation period hPeriod metric line measure) 0 := by
    simpa only [regularIntrinsicMaxwellPairingLine] using
      (intrinsicMaxwellAction_line_hasDerivAt period hPeriod metric line measure)
  have hExplicit := hIntrinsic.const_mul couplings.plusMaxwellScale
  have hFunctions :
      (fun t : Real => action (point + t • direction)) =
        (fun t : Real => couplings.plusMaxwellScale *
          intrinsicMaxwellAction period hPeriod metric
            (regularIntrinsicMaxwellPairingLine period hPeriod metric line t)
              measure) := by
    funext t
    let hLine :=
      regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeLine_mem period
        hPeriod configuration.physical plusBase minusBase point hPoint test t
    rw [show action (point + t • direction) =
        blocks.maxwellPlus (point + t • direction) by rfl]
    rw [regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_maxwellPlus_eq
      period hPeriod configuration.physical couplings data plusBase minusBase
        hBase measure (point + t • direction) hLine]
    rw [regularGeneralMetricC2PairedPlusFixedVolumeMaxwellAction_strongGaugeLine
      period hPeriod configuration.physical plusBase minusBase measure point
        hPoint test t]
  have hFrechet' : HasDerivAt (fun t : Real => action (point + t • direction))
      (fderiv Real action point direction) 0 := by
    simpa [Function.comp_def] using hFrechet
  rw [hFunctions] at hFrechet'
  exact hFrechet'.unique hExplicit

/-- The authentic minus Maxwell block has its exact intrinsic weak first
variation on every pure plus/minus gauge test. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalMaxwellMinus_fderiv_apply_strongGaugeDirection
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (point : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration.physical)
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
    fderiv Real
        (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
          period hPeriod configuration.physical couplings data plusBase minusBase
            hBase measure).maxwellMinus point
        (regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeDirection period
          hPeriod configuration.physical test) =
      let metric := regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
        minusBase (point.1.completeVariation.fullMetricPerturbation .minus)
          hPoint.minus_mem
      let potential := regularFrameGaugePotentialFromCoefficients period hPeriod
        metric (configuration.physical.coefficientFields.gauge.2 +
          point.1.completeVariation.independent.gauge.2)
      let variation := regularFrameGaugePotentialFromCoefficients period hPeriod
        metric test.2
      couplings.minusMaxwellScale *
        intrinsicMaxwellFirstVariation period hPeriod metric
          (regularIntrinsicMaxwellLineOfPotentials period hPeriod metric
            potential variation) measure := by
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
  let action := blocks.maxwellMinus
  let direction :=
    regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeDirection period
      hPeriod configuration.physical test
  let metric := regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
    minusBase (point.1.completeVariation.fullMetricPerturbation .minus)
      hPoint.minus_mem
  let potential := regularFrameGaugePotentialFromCoefficients period hPeriod
    metric (configuration.physical.coefficientFields.gauge.2 +
      point.1.completeVariation.independent.gauge.2)
  let variation := regularFrameGaugePotentialFromCoefficients period hPeriod
    metric test.2
  let line := regularIntrinsicMaxwellLineOfPotentials period hPeriod metric
    potential variation
  have hOpen :=
    regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain_strong_isOpen
      period hPeriod configuration data analysis realization plusBase minusBase
  have hSmooth :=
    (regularGeneralMetricC2PairedMinimalPhysicalActionBlocks_maxwell_strong_contDiffWithinAt
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point hPoint).2
  have hAction : HasFDerivAt action (fderiv Real action point) point :=
    (hSmooth.contDiffAt (hOpen.mem_nhds hPoint)).differentiableAt
      (by norm_num) |>.hasFDerivAt
  have hAffine : HasDerivAt (fun t : Real => point + t • direction) direction 0 := by
    exact ((hasDerivAt_const (x := (0 : Real)) (c := point)).add
      ((hasDerivAt_id (0 : Real)).smul_const direction)).congr_deriv (by simp)
  have hFrechet := hAction.comp_hasDerivAt_of_eq 0 hAffine (by simp)
  have hIntrinsic : HasDerivAt
      (fun t : Real => intrinsicMaxwellAction period hPeriod metric
        (regularIntrinsicMaxwellPairingLine period hPeriod metric line t) measure)
      (intrinsicMaxwellFirstVariation period hPeriod metric line measure) 0 := by
    simpa only [regularIntrinsicMaxwellPairingLine] using
      (intrinsicMaxwellAction_line_hasDerivAt period hPeriod metric line measure)
  have hExplicit := hIntrinsic.const_mul couplings.minusMaxwellScale
  have hFunctions :
      (fun t : Real => action (point + t • direction)) =
        (fun t : Real => couplings.minusMaxwellScale *
          intrinsicMaxwellAction period hPeriod metric
            (regularIntrinsicMaxwellPairingLine period hPeriod metric line t)
              measure) := by
    funext t
    let hLine :=
      regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeLine_mem period
        hPeriod configuration.physical plusBase minusBase point hPoint test t
    rw [show action (point + t • direction) =
        blocks.maxwellMinus (point + t • direction) by rfl]
    rw [regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_maxwellMinus_eq
      period hPeriod configuration.physical couplings data plusBase minusBase
        hBase measure (point + t • direction) hLine]
    rw [regularGeneralMetricC2PairedMinusFixedVolumeMaxwellAction_strongGaugeLine
      period hPeriod configuration.physical plusBase minusBase measure point
        hPoint test t]
  have hFrechet' : HasDerivAt (fun t : Real => action (point + t • direction))
      (fderiv Real action point direction) 0 := by
    simpa [Function.comp_def] using hFrechet
  rw [hFunctions] at hFrechet'
  exact hFrechet'.unique hExplicit

/-- Gate: both authentic Maxwell blocks have the exact intrinsic weak first
variation in the paired strong gauge direction. -/
theorem regular_general_metric_c2_paired_minimal_physical_strong_maxwell_weak_first_variation_gate
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (point : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration.physical)
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
    let blocks :=
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
        period hPeriod configuration.physical couplings data plusBase minusBase
          hBase measure
    let direction :=
      regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeDirection period
        hPeriod configuration.physical test
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
    actionGradient blocks.maxwellPlus point direction =
        couplings.plusMaxwellScale *
          intrinsicMaxwellFirstVariation period hPeriod plusMetric
            (regularIntrinsicMaxwellLineOfPotentials period hPeriod plusMetric
              plusPotential plusVariation) measure ∧
      actionGradient blocks.maxwellMinus point direction =
        couplings.minusMaxwellScale *
          intrinsicMaxwellFirstVariation period hPeriod minusMetric
            (regularIntrinsicMaxwellLineOfPotentials period hPeriod minusMetric
              minusPotential minusVariation) measure := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  constructor
  · exact
      regularGeneralMetricC2PairedMinimalPhysicalMaxwellPlus_fderiv_apply_strongGaugeDirection
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase measure point hPoint test
  · exact
      regularGeneralMetricC2PairedMinimalPhysicalMaxwellMinus_fderiv_apply_strongGaugeDirection
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase measure point hPoint test

end

end
end P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellWeakFirstVariation4D
end JanusFormal
