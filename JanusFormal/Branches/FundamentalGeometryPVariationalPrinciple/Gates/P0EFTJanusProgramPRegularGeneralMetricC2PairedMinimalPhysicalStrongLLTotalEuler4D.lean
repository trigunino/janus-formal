import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongGaugeReducedCoupledResidual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldStrongEquation4D

/-! # Total LL Euler equation in the concrete strong chart -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLLTotalEuler4D

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
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLStrongEquation4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalBoundaryCompletion4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalEulerLagrangeBlockDecomposition4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSevenBulkSystem4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartRegularMetric4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartMaxwell4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedGaugeCoefficientMaxwellAction4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomainOpen4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalConstantBoundaryC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalInteractionC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMatterC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricGaugeCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalRelativeMetricCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedFixedVolumeEinsteinHilbertC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedEinsteinHilbertActionBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalNineBlockC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongComponentPDEBlockPairing4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongEightSectorEuler4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongEulerNineBlockDecomposition4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLocalEuler4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongGaugeReducedCoupledResidual4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLLWeakFirstVariation4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldWeakResidual4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldStrongEquation4D
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
    BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl

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

private theorem actionGradient_comp_apply_eq_zero
    {Model Core : Type*}
    [NormedAddCommGroup Model] [NormedSpace Real Model]
    [NormedAddCommGroup Core] [NormedSpace Real Core]
    (outer : Core → Real) (projection : Model →L[Real] Core)
    (base direction : Model)
    (hOuter : DifferentiableAt Real outer (projection base))
    (hDirection : projection direction = 0) :
    actionGradient (fun current => outer (projection current)) base direction =
      0 := by
  change fderiv Real (outer ∘ projection) base direction = 0
  rw [fderiv_comp base hOuter projection.differentiableAt]
  simp [hDirection]

omit data analysis realization hBase measure point plusBase minusBase
    [IsFiniteMeasure measure] in
@[simp]
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection_fullMetricPerturbation
    (test : RegularGeneralMetricC2PairedMinimalPhysicalStrongLLTest period hPeriod) :
    (regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection period hPeriod
      configuration.physical test).1.completeVariation.fullMetricPerturbation =
      0 :=
  rfl

omit data analysis realization hBase measure point plusBase minusBase
    [IsFiniteMeasure measure] in
@[simp]
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection_gauge
    (test : RegularGeneralMetricC2PairedMinimalPhysicalStrongLLTest period hPeriod) :
    (regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection period hPeriod
      configuration.physical test).1.completeVariation.independent.gauge = 0 :=
  rfl

omit data analysis realization hBase measure point plusBase minusBase
    [IsFiniteMeasure measure] in
@[simp]
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection_spinCMatter
    (test : RegularGeneralMetricC2PairedMinimalPhysicalStrongLLTest period hPeriod) :
    (regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection period hPeriod
      configuration.physical test).1.2 = 0 :=
  rfl

omit data analysis realization hBase measure point [IsFiniteMeasure measure] in
@[simp]
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection_relativeMetricCore
    (test : RegularGeneralMetricC2PairedMinimalPhysicalStrongLLTest period hPeriod) :
    globalMinimalPhysicalPairedRelativeMetricCoreLinearMap period hPeriod
        configuration.physical plusBase minusBase
        (regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection period
          hPeriod configuration.physical test) = 0 := by
  have hMetric :=
    regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection_fullMetricPerturbation
      period hPeriod configuration test
  have hMetricPlus := congrFun hMetric (.plus)
  have hMetricMinus := congrFun hMetric (.minus)
  apply Prod.ext
  · rw [globalMinimalPhysicalPairedRelativeMetricCoreLinearMap_paired]
    apply Prod.ext
    · change regularGeneralMetricSmoothC2Variation period hPeriod plusBase
          _ = 0
      rw [hMetricPlus]
      exact map_zero _
    · change regularGeneralMetricSmoothC2Variation period hPeriod minusBase
          _ = 0
      rw [hMetricMinus]
      exact map_zero _
  · apply Prod.ext
    · rw [globalMinimalPhysicalPairedRelativeMetricCoreLinearMap_plus,
        hMetricPlus]
      exact map_zero _
    · rw [globalMinimalPhysicalPairedRelativeMetricCoreLinearMap_cross,
        hMetricPlus, hMetricMinus]
      simp

omit hBase measure point [IsFiniteMeasure measure] in
@[simp]
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection_oldCoreCLM
    (test : RegularGeneralMetricC2PairedMinimalPhysicalStrongLLTest period hPeriod) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    globalMinimalPhysicalPairedMetricGaugeLLStrongOldCoreCLM period hPeriod
        configuration data analysis realization plusBase minusBase
        (regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection period
          hPeriod configuration.physical test) = 0 := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  rw [globalMinimalPhysicalPairedMetricGaugeLLStrongOldCoreCLM_apply]
  apply Prod.ext
  · exact
      regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection_relativeMetricCore
        period hPeriod configuration plusBase minusBase test
  · rw [globalMinimalPhysicalPairedMetricGaugeCoreLinearMap_gauge,
      regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection_gauge]
    exact map_zero _

omit hBase measure point [IsFiniteMeasure measure] in
@[simp]
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection_metricCLM
    (test : RegularGeneralMetricC2PairedMinimalPhysicalStrongLLTest period hPeriod) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    globalMinimalPhysicalPairedMetricGaugeLLStrongMetricCLM period hPeriod
        configuration data analysis realization plusBase minusBase
        (regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection period
          hPeriod configuration.physical test) = 0 := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  rw [globalMinimalPhysicalPairedMetricGaugeLLStrongMetricCLM_apply]
  exact
    regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection_relativeMetricCore
      period hPeriod configuration plusBase minusBase test

omit hBase measure point [IsFiniteMeasure measure] in
@[simp]
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection_matterCLM
    (test : RegularGeneralMetricC2PairedMinimalPhysicalStrongLLTest period hPeriod) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    globalMinimalPhysicalPairedMetricGaugeLLStrongMatterCLM period hPeriod
        configuration data analysis realization plusBase minusBase
        (regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection period
          hPeriod configuration.physical test) = 0 := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  rw [globalMinimalPhysicalPairedMetricGaugeLLStrongMatterCLM_apply]
  unfold globalMinimalPhysicalMatterGraphLinearMap
    globalMinimalPhysicalSpinCMatterLinearMap
  change realization.toGraph
      (regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection period
        hPeriod configuration.physical test).1.2 = 0
  rw [regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection_spinCMatter]
  exact map_zero _

/-- The interaction block depends only on metric coordinates, hence has no
pure LL variation. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalCandidateA_actionGradient_strongLL_eq_zero
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
            hBase measure).candidateA point
        (regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection period
          hPeriod configuration.physical test) = 0 := by
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
  let projection :=
    globalMinimalPhysicalPairedMetricGaugeLLStrongMetricCLM period hPeriod
      configuration data analysis realization plusBase minusBase
  let outer :=
    regularGeneralMetricC2PairedInteractionC2Action period hPeriod plusBase
      minusBase measure couplings.interactionScale
        couplings.interactionCoefficients
  have hOpen :=
    regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain_strong_isOpen
      period hPeriod configuration data analysis realization plusBase minusBase
  have hEventually :
      blocks.candidateA =ᶠ[nhds point]
        fun current => outer (projection current) := by
    filter_upwards [hOpen.mem_nhds hPoint] with current hCurrent
    simpa [outer, projection] using
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_candidateA_eq
        period hPeriod configuration.physical couplings data plusBase minusBase
          hBase measure current hCurrent)
  have hTarget : projection point ∈
      regularGeneralMetricC2PairedLorentzMatrixDomain period hPeriod plusBase
        minusBase := by
    change globalMinimalPhysicalPairedRelativeMetricCoreLinearMap period hPeriod
        configuration.physical plusBase minusBase point ∈ _
    exact
      (globalMetricPerturbationPairLorentzChartAdmissible_iff_mem_matrixDomain
        period hPeriod configuration.physical plusBase minusBase point).1 hPoint
  have hOuter : DifferentiableAt Real outer (projection point) :=
    ((regularGeneralMetricC2PairedInteractionC2Action_contDiffOn period hPeriod
      plusBase minusBase measure couplings.interactionScale
        couplings.interactionCoefficients).contDiffAt
      ((regularGeneralMetricC2PairedLorentzMatrixDomain_isOpen period
        hPeriod plusBase minusBase).mem_nhds hTarget)).differentiableAt (by
          norm_num)
  change fderiv Real blocks.candidateA point
      (regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection period
        hPeriod configuration.physical test) = 0
  rw [hEventually.fderiv_eq]
  exact actionGradient_comp_apply_eq_zero outer projection point
    (regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection period
      hPeriod configuration.physical test) hOuter
    (regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection_metricCLM
      period hPeriod configuration data analysis realization plusBase minusBase
        test)

/-- Both Einstein--Hilbert blocks depend only on metric coordinates. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalEinsteinHilbert_actionGradient_strongLL_eq_zero
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
    let blocks :=
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
        period hPeriod configuration.physical couplings data plusBase minusBase
          hBase measure
    let direction :=
      regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection period
        hPeriod configuration.physical test
    actionGradient blocks.einsteinHilbertPlus point direction = 0 ∧
      actionGradient blocks.einsteinHilbertMinus point direction = 0 := by
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
  let projection :=
    globalMinimalPhysicalPairedMetricGaugeLLStrongMetricCLM period hPeriod
      configuration data analysis realization plusBase minusBase
  let plusOuter :=
    regularGeneralMetricC2PairedPlusFixedVolumeEinsteinHilbertAction period
      hPeriod plusBase minusBase measure couplings.plusEinstein
  let minusOuter :=
    regularGeneralMetricC2PairedMinusFixedVolumeEinsteinHilbertAction period
      hPeriod plusBase minusBase measure couplings.minusEinstein
  let direction :=
    regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection period
      hPeriod configuration.physical test
  have hOpen :=
    regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain_strong_isOpen
      period hPeriod configuration data analysis realization plusBase minusBase
  have hPlusEventually :
      blocks.einsteinHilbertPlus =ᶠ[nhds point]
        fun current => plusOuter (projection current) := by
    filter_upwards [hOpen.mem_nhds hPoint] with current hCurrent
    simpa [plusOuter, projection] using
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_einsteinHilbertPlus_eq
        period hPeriod configuration.physical couplings data plusBase minusBase
          hBase measure current hCurrent)
  have hMinusEventually :
      blocks.einsteinHilbertMinus =ᶠ[nhds point]
        fun current => minusOuter (projection current) := by
    filter_upwards [hOpen.mem_nhds hPoint] with current hCurrent
    simpa [minusOuter, projection] using
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_einsteinHilbertMinus_eq
        period hPeriod configuration.physical couplings data plusBase minusBase
          hBase measure current hCurrent)
  have hTarget : projection point ∈
      regularGeneralMetricC2PairedLorentzMatrixDomain period hPeriod plusBase
        minusBase := by
    change globalMinimalPhysicalPairedRelativeMetricCoreLinearMap period hPeriod
        configuration.physical plusBase minusBase point ∈ _
    exact
      (globalMetricPerturbationPairLorentzChartAdmissible_iff_mem_matrixDomain
        period hPeriod configuration.physical plusBase minusBase point).1 hPoint
  have hTargetNhds :=
    (regularGeneralMetricC2PairedLorentzMatrixDomain_isOpen period hPeriod
      plusBase minusBase).mem_nhds hTarget
  have hPlusOuter : DifferentiableAt Real plusOuter (projection point) :=
    ((regularGeneralMetricC2PairedPlusFixedVolumeEinsteinHilbertAction_contDiffOn
      period hPeriod plusBase minusBase measure couplings.plusEinstein).contDiffAt
        hTargetNhds).differentiableAt (by norm_num)
  have hMinusOuter : DifferentiableAt Real minusOuter (projection point) :=
    ((regularGeneralMetricC2PairedMinusFixedVolumeEinsteinHilbertAction_contDiffOn
      period hPeriod plusBase minusBase measure couplings.minusEinstein).contDiffAt
        hTargetNhds).differentiableAt (by norm_num)
  have hDirection : projection direction = 0 :=
    regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection_metricCLM
      period hPeriod configuration data analysis realization plusBase minusBase
        test
  constructor
  · change fderiv Real blocks.einsteinHilbertPlus point direction = 0
    rw [hPlusEventually.fderiv_eq]
    exact actionGradient_comp_apply_eq_zero plusOuter projection point direction
      hPlusOuter hDirection
  · change fderiv Real blocks.einsteinHilbertMinus point direction = 0
    rw [hMinusEventually.fderiv_eq]
    exact actionGradient_comp_apply_eq_zero minusOuter projection point direction
      hMinusOuter hDirection

/-- Both Maxwell blocks depend only on metric and gauge coordinates. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalMaxwell_actionGradient_strongLL_eq_zero
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
    let blocks :=
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
        period hPeriod configuration.physical couplings data plusBase minusBase
          hBase measure
    let direction :=
      regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection period
        hPeriod configuration.physical test
    actionGradient blocks.maxwellPlus point direction = 0 ∧
      actionGradient blocks.maxwellMinus point direction = 0 := by
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
  let projection :=
    globalMinimalPhysicalPairedMetricGaugeLLStrongOldCoreCLM period hPeriod
      configuration data analysis realization plusBase minusBase
  let plusOuter := fun current => couplings.plusMaxwellScale *
    regularGeneralMetricC2PairedPlusFixedVolumeMaxwellAction period hPeriod
      configuration.physical plusBase minusBase measure current
  let minusOuter := fun current => couplings.minusMaxwellScale *
    regularGeneralMetricC2PairedMinusFixedVolumeMaxwellAction period hPeriod
      configuration.physical plusBase minusBase measure current
  let direction :=
    regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection period
      hPeriod configuration.physical test
  have hOpen :=
    regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain_strong_isOpen
      period hPeriod configuration data analysis realization plusBase minusBase
  have hPlusEventually :
      blocks.maxwellPlus =ᶠ[nhds point]
        fun current => plusOuter (projection current) := by
    filter_upwards [hOpen.mem_nhds hPoint] with current hCurrent
    simpa [plusOuter, projection] using
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_maxwellPlus_eq
        period hPeriod configuration.physical couplings data plusBase minusBase
          hBase measure current hCurrent)
  have hMinusEventually :
      blocks.maxwellMinus =ᶠ[nhds point]
        fun current => minusOuter (projection current) := by
    filter_upwards [hOpen.mem_nhds hPoint] with current hCurrent
    simpa [minusOuter, projection] using
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_maxwellMinus_eq
        period hPeriod configuration.physical couplings data plusBase minusBase
          hBase measure current hCurrent)
  have hTarget : projection point ∈
      regularGeneralMetricC2PairedMetricGaugeMaxwellDomain period hPeriod
        plusBase minusBase := by
    exact ⟨
      (globalMetricPerturbationPairLorentzChartAdmissible_iff_mem_matrixDomain
        period hPeriod configuration.physical plusBase minusBase point).1 hPoint,
      Set.mem_univ _⟩
  have hTargetNhds :
      regularGeneralMetricC2PairedMetricGaugeMaxwellDomain period hPeriod
          plusBase minusBase ∈ nhds (projection point) :=
    ((regularGeneralMetricC2PairedLorentzMatrixDomain_isOpen period hPeriod
      plusBase minusBase).prod isOpen_univ).mem_nhds hTarget
  have hPlusOuter : DifferentiableAt Real plusOuter (projection point) :=
    ((contDiffOn_const.mul
      (regularGeneralMetricC2PairedPlusFixedVolumeMaxwellAction_contDiffOn_two
        period hPeriod configuration.physical plusBase minusBase measure)).contDiffAt
          hTargetNhds).differentiableAt (by norm_num)
  have hMinusOuter : DifferentiableAt Real minusOuter (projection point) :=
    ((contDiffOn_const.mul
      (regularGeneralMetricC2PairedMinusFixedVolumeMaxwellAction_contDiffOn_two
        period hPeriod configuration.physical plusBase minusBase measure)).contDiffAt
          hTargetNhds).differentiableAt (by norm_num)
  have hDirection : projection direction = 0 :=
    regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection_oldCoreCLM
      period hPeriod configuration data analysis realization plusBase minusBase
        test
  constructor
  · change fderiv Real blocks.maxwellPlus point direction = 0
    rw [hPlusEventually.fderiv_eq]
    exact actionGradient_comp_apply_eq_zero plusOuter projection point direction
      hPlusOuter hDirection
  · change fderiv Real blocks.maxwellMinus point direction = 0
    rw [hMinusEventually.fderiv_eq]
    exact actionGradient_comp_apply_eq_zero minusOuter projection point direction
      hMinusOuter hDirection

omit [IsFiniteMeasure measure] in
/-- The primitive SpinC block depends only on the SpinC graph coordinate. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalMatter_actionGradient_strongLL_eq_zero
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
            hBase measure).matter point
        (regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection period
          hPeriod configuration.physical test) = 0 := by
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
  let projection :=
    globalMinimalPhysicalPairedMetricGaugeLLStrongMatterCLM period hPeriod
      configuration data analysis realization plusBase minusBase
  let outer := fun current =>
    programPPrimitiveSpinCMatterGraphAction period hPeriod
      couplings.matterMassSquared
      (realization.toGraph configuration.physical.spinCMatter + current)
  have hOpen :=
    regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain_strong_isOpen
      period hPeriod configuration data analysis realization plusBase minusBase
  have hEventually :
      blocks.matter =ᶠ[nhds point]
        fun current => outer (projection current) := by
    filter_upwards [hOpen.mem_nhds hPoint] with current hCurrent
    simpa [outer, projection,
      regularGeneralMetricC2PairedMinimalPhysicalMatterGraphInput] using
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_matter_eq
        period hPeriod configuration data realization plusBase minusBase hBase
          measure current hCurrent)
  have hOuter : DifferentiableAt Real outer (projection point) := by
    have hInput : ContDiff Real 2 (fun current =>
        realization.toGraph configuration.physical.spinCMatter + current) :=
      contDiff_const.add contDiff_id
    exact (((programPPrimitiveSpinCMatterGraphAction_contDiff_two period hPeriod
      couplings.matterMassSquared).comp hInput).differentiable (by
        norm_num)).differentiableAt
  change fderiv Real blocks.matter point
      (regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection period
        hPeriod configuration.physical test) = 0
  rw [hEventually.fderiv_eq]
  exact actionGradient_comp_apply_eq_zero outer projection point
    (regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection period
      hPeriod configuration.physical test) hOuter
    (regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection_matterCLM
      period hPeriod configuration data analysis realization plusBase minusBase
        test)

/-- In a pure LL direction the complete nine-block Euler sum is exactly the
authentic LL-block Euler covector. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalFullBlockSum_strongLL_eq_LL
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
    let blocks :=
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
        period hPeriod configuration.physical couplings data plusBase minusBase
          hBase measure
    let direction :=
      regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection period
        hPeriod configuration.physical test
    fullCoupledEulerBlockSum blocks point direction =
      actionGradient blocks.ll point direction := by
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
  let direction :=
    regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection period
      hPeriod configuration.physical test
  have hCandidate : actionGradient blocks.candidateA point direction = 0 := by
    simpa [blocks, direction] using
      (regularGeneralMetricC2PairedMinimalPhysicalCandidateA_actionGradient_strongLL_eq_zero
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase measure point hPoint test)
  have hMatter : actionGradient blocks.matter point direction = 0 := by
    simpa [blocks, direction] using
      (regularGeneralMetricC2PairedMinimalPhysicalMatter_actionGradient_strongLL_eq_zero
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase measure point hPoint test)
  have hRobinCLM : actionGradient blocks.robin point = 0 := by
    simpa [blocks] using
      (regularGeneralMetricC2PairedMinimalPhysicalRobin_actionGradient_eq_zero
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase measure point hPoint)
  have hRobin : actionGradient blocks.robin point direction = 0 := by
    rw [hRobinCLM]
    rfl
  have hEinstein :=
    regularGeneralMetricC2PairedMinimalPhysicalEinsteinHilbert_actionGradient_strongLL_eq_zero
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point hPoint test
  have hEinsteinPlus :
      actionGradient blocks.einsteinHilbertPlus point direction = 0 := by
    simpa [blocks, direction] using hEinstein.1
  have hEinsteinMinus :
      actionGradient blocks.einsteinHilbertMinus point direction = 0 := by
    simpa [blocks, direction] using hEinstein.2
  have hMaxwell :=
    regularGeneralMetricC2PairedMinimalPhysicalMaxwell_actionGradient_strongLL_eq_zero
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point hPoint test
  have hMaxwellPlus :
      actionGradient blocks.maxwellPlus point direction = 0 := by
    simpa [blocks, direction] using hMaxwell.1
  have hMaxwellMinus :
      actionGradient blocks.maxwellMinus point direction = 0 := by
    simpa [blocks, direction] using hMaxwell.2
  have hFiniteCLM : actionGradient blocks.finiteBV point = 0 := by
    simpa [blocks] using
      (regularGeneralMetricC2PairedMinimalPhysicalFiniteBV_actionGradient_eq_zero
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase measure point hPoint)
  have hFinite : actionGradient blocks.finiteBV point direction = 0 := by
    rw [hFiniteCLM]
    rfl
  unfold fullCoupledEulerBlockSum
  dsimp only
  simp only [add_apply]
  rw [hCandidate, hMatter, hRobin, hEinsteinPlus, hEinsteinMinus,
    hMaxwellPlus, hMaxwellMinus, hFinite]
  norm_num

/-- The complete strong Euler operator, not merely the isolated LL block,
restricts to the authentic LL first variation. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongEuler_strongLL_eq_LLBlock
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
    let blocks :=
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
        period hPeriod configuration.physical couplings data plusBase minusBase
          hBase measure
    let direction :=
      regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection period
        hPeriod configuration.physical test
    regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLagrangeOperator
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase measure point direction =
      actionGradient blocks.ll point direction := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  rw [regularGeneralMetricC2PairedMinimalPhysicalStrongEuler_eq_nineBlockSum
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase measure point hPoint]
  exact
    regularGeneralMetricC2PairedMinimalPhysicalFullBlockSum_strongLL_eq_LL
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point hPoint test

/-- Gate444: the total Candidate-A Euler operator has the explicit three-slot
LL weak variation, with every cross-block proved zero. -/
theorem regular_general_metric_c2_paired_minimal_physical_total_strong_LL_weak_variation_gate
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
    regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLagrangeOperator
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase measure point
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
  rw [regularGeneralMetricC2PairedMinimalPhysicalStrongEuler_strongLL_eq_LLBlock
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase measure point hPoint test]
  exact
    regular_general_metric_c2_paired_minimal_physical_strong_LL_weak_first_variation_gate
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point hPoint test

/-- The total Euler operator and isolated LL block agree on pure LL-field
directions. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongEuler_strongLLField_eq_LLBlock
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
    let blocks :=
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
        period hPeriod configuration.physical couplings data plusBase minusBase
          hBase measure
    regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLagrangeOperator
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase measure point
        (regularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldDirection period
          hPeriod configuration.physical test) =
      actionGradient blocks.ll point
        (regularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldDirection period
          hPeriod configuration.physical test) := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  simpa [regularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldDirection] using
    (regularGeneralMetricC2PairedMinimalPhysicalStrongEuler_strongLL_eq_LLBlock
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point hPoint
        (regularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldThreeSlotTest
          period hPeriod test))

/-- Gate444: stationarity of the complete Candidate-A Euler operator in every
LL-field direction is exactly the canonical pointwise strong LL PDE. -/
theorem regular_general_metric_c2_paired_minimal_physical_total_strong_LL_field_stationary_iff_strong_equation_gate
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    (∀ test : RegularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldTest
        period hPeriod,
      regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLagrangeOperator
          period hPeriod configuration data analysis realization plusBase
            minusBase hBase measure point
          (regularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldDirection
            period hPeriod configuration.physical test) = 0) ↔
      SatisfiesPTSymmetricStrongDifferentialLLEquation period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod)
        (smoothLLStrongRegularity period hPeriod
          (canonicalDivergenceFreeLLFrame period hPeriod))
        (regularGeneralMetricC2PairedMinimalPhysicalLLFieldsInput period hPeriod
          configuration.physical point) := by
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
  constructor
  · intro hTotal
    apply
      (regular_general_metric_c2_paired_minimal_physical_strong_LL_field_stationary_iff_strong_equation_gate
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase measure point hPoint).1
    intro test
    rw [← regularGeneralMetricC2PairedMinimalPhysicalStrongEuler_strongLLField_eq_LLBlock
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point hPoint test]
    exact hTotal test
  · intro hStrong test
    rw [regularGeneralMetricC2PairedMinimalPhysicalStrongEuler_strongLLField_eq_LLBlock
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point hPoint test]
    exact
      (regular_general_metric_c2_paired_minimal_physical_strong_LL_field_stationary_iff_strong_equation_gate
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase measure point hPoint).2 hStrong test

end

end
end P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLLTotalEuler4D
end JanusFormal
