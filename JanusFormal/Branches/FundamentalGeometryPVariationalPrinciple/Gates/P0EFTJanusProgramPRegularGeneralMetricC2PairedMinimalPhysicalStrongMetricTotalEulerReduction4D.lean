import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongSpinCTotalEuler4D

/-! # Total metric Euler reduction in the concrete strong chart -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMetricTotalEulerReduction4D

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
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D
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


/-- Pure metric direction in the authentic strong chart. -/
def regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection
    (configuration : GlobalFieldConfiguration period hPeriod) :
    GlobalMinimalPhysicalMetricTest period hPeriod →ₗ[Real]
      GlobalMinimalPhysicalFieldTangent period hPeriod configuration :=
  (regularGeneralMetricC2PairedMinimalPhysicalStrongSevenBulkDirection period
    hPeriod configuration).comp
      (globalMinimalPhysicalMetricTestInclusion period hPeriod)

omit data analysis realization hBase measure point plusBase minusBase
    [IsFiniteMeasure measure] in
@[simp]
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection_spinCMatter
    (test : GlobalMinimalPhysicalMetricTest period hPeriod) :
    (regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection period
      hPeriod configuration.physical test).1.2 = 0 := rfl

omit data analysis realization hBase measure point plusBase minusBase
    [IsFiniteMeasure measure] in
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection_ll_eq_zero
    (test : GlobalMinimalPhysicalMetricTest period hPeriod) :
    let direction :=
      regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection period
        hPeriod configuration.physical test
    direction.1.completeVariation.independent.llAuxMetric = 0 ∧
      direction.1.completeVariation.independent.llMeasure = 0 ∧
      direction.1.completeVariation.independent.llField = 0 := by
  exact ⟨rfl, rfl, rfl⟩

omit hBase measure point [IsFiniteMeasure measure] in
@[simp]
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection_matterCLM
    (test : GlobalMinimalPhysicalMetricTest period hPeriod) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    globalMinimalPhysicalPairedMetricGaugeLLStrongMatterCLM period hPeriod
        configuration data analysis realization plusBase minusBase
        (regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection period
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
      (regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection period
        hPeriod configuration.physical test).1.2 = 0
  rw [regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection_spinCMatter]
  exact map_zero _

omit hBase measure point [IsFiniteMeasure measure] in
@[simp]
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection_strongLLCLM
    (test : GlobalMinimalPhysicalMetricTest period hPeriod) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    globalMinimalPhysicalPairedLLC0FirstJetCLM period hPeriod configuration data
        analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
        (regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection period
          hPeriod configuration.physical test) = 0 := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  rw [globalMinimalPhysicalPairedLLC0FirstJetCLM_apply]
  unfold globalMinimalPhysicalLLC0FirstJetLinearMap
    globalMinimalPhysicalLLSmoothCoefficientLinearMap
  have hLL :=
    regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection_ll_eq_zero
      period hPeriod configuration test
  change smoothLLCoefficientPTC0FirstJetLinearMap period hPeriod
      (canonicalDivergenceFreeLLFrame period hPeriod) (_, (_, _)) = 0
  rw [hLL.1, hLL.2.1, hLL.2.2]
  exact map_zero _
omit [IsFiniteMeasure measure] in
/-- The primitive SpinC block depends only on the SpinC graph coordinate. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalMatter_actionGradient_strongMetric_eq_zero
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (test : GlobalMinimalPhysicalMetricTest period hPeriod) :
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
        (regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection period
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
      (regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection period
        hPeriod configuration.physical test) = 0
  rw [hEventually.fderiv_eq]
  exact actionGradient_comp_apply_eq_zero outer projection point
    (regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection period
      hPeriod configuration.physical test) hOuter
    (regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection_matterCLM
      period hPeriod configuration data analysis realization plusBase minusBase
        test)

omit [IsFiniteMeasure measure] in
/-- The nonlinear LL block has no pure metric variation. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalLL_actionGradient_strongMetric_eq_zero
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (test : GlobalMinimalPhysicalMetricTest period hPeriod) :
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
        (regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection period
          hPeriod configuration.physical test) = 0 := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
    hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  let frame := canonicalDivergenceFreeLLFrame period hPeriod
  let blocks :=
    regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
      period hPeriod configuration.physical couplings data plusBase minusBase
        hBase measure
  let projection :=
    globalMinimalPhysicalPairedLLC0FirstJetCLM period hPeriod configuration data
      analysis realization plusBase minusBase frame
  let basePacket :=
    smoothLLCoefficientPTC0FirstJetLinearMap period hPeriod frame
      (configuration.physical.coefficientFields.llAuxMetric,
        (configuration.physical.coefficientFields.llMeasure,
          configuration.physical.coefficientFields.llField))
  let outer := fun current =>
    regularGeneralMetricC0LLPTAction period hPeriod frame
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
        (basePacket + current)
  have hOpen :=
    regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain_strong_isOpen
      period hPeriod configuration data analysis realization plusBase minusBase
  have hEventually :
      blocks.ll =ᶠ[nhds point]
        fun current => outer (projection current) := by
    filter_upwards [hOpen.mem_nhds hPoint] with current hCurrent
    calc
      blocks.ll current =
          regularGeneralMetricC2PairedMinimalPhysicalLLAction period hPeriod
            configuration.physical current :=
        regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_ll_eq
          period hPeriod configuration.physical data plusBase minusBase hBase
            measure current hCurrent
      _ = outer (projection current) := by
        unfold regularGeneralMetricC2PairedMinimalPhysicalLLAction
        rw [regularGeneralMetricC2PairedMinimalPhysicalLLPacketInput_eq_affine]
        rfl
  have hOuter : DifferentiableAt Real outer (projection point) := by
    have hTranslate : ContDiff Real ∞ (fun current => basePacket + current) :=
      contDiff_const.add contDiff_id
    exact (((regularGeneralMetricC0LLPTAction_contDiff period hPeriod frame
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod)).comp
        hTranslate).differentiable (by simp)).differentiableAt
  change fderiv Real blocks.ll point
      (regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection period
        hPeriod configuration.physical test) = 0
  rw [hEventually.fderiv_eq]
  exact actionGradient_comp_apply_eq_zero outer projection point
    (regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection period
      hPeriod configuration.physical test) hOuter
    (regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection_strongLLCLM
      period hPeriod configuration data analysis realization plusBase minusBase
        test)

omit [IsFiniteMeasure measure] in
/-- On a pure metric direction the complete nine-block sum reduces exactly to
the interaction, two Einstein--Hilbert, and two Maxwell metric variations. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalFullBlockSum_strongMetric_eq_metricBlocks
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (test : GlobalMinimalPhysicalMetricTest period hPeriod) :
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
      regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection period
        hPeriod configuration.physical test
    fullCoupledEulerBlockSum blocks point direction =
      ((((actionGradient blocks.candidateA point direction +
          actionGradient blocks.einsteinHilbertPlus point direction) +
          actionGradient blocks.einsteinHilbertMinus point direction) +
          actionGradient blocks.maxwellPlus point direction) +
          actionGradient blocks.maxwellMinus point direction) := by
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
    regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection period
      hPeriod configuration.physical test
  have hMatter : actionGradient blocks.matter point direction = 0 := by
    simpa [blocks, direction] using
      (regularGeneralMetricC2PairedMinimalPhysicalMatter_actionGradient_strongMetric_eq_zero
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
  have hLL : actionGradient blocks.ll point direction = 0 := by
    simpa [blocks, direction] using
      (regularGeneralMetricC2PairedMinimalPhysicalLL_actionGradient_strongMetric_eq_zero
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase measure point hPoint test)
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
  rw [hMatter, hRobin, hLL, hFinite]
  norm_num

/-- The authentic total Euler operator has exactly five active metric blocks
on every pure metric test. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongEuler_strongMetric_eq_metricBlocks
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (test : GlobalMinimalPhysicalMetricTest period hPeriod) :
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
      regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection period
        hPeriod configuration.physical test
    regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLagrangeOperator
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase measure point direction =
      ((((actionGradient blocks.candidateA point direction +
          actionGradient blocks.einsteinHilbertPlus point direction) +
          actionGradient blocks.einsteinHilbertMinus point direction) +
          actionGradient blocks.maxwellPlus point direction) +
          actionGradient blocks.maxwellMinus point direction) := by
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
    regularGeneralMetricC2PairedMinimalPhysicalFullBlockSum_strongMetric_eq_metricBlocks
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point hPoint test

/-- Gate marker: the complete strong metric Euler equation contains precisely
the five genuine metric-dependent action blocks. -/
theorem regular_general_metric_c2_paired_minimal_physical_total_strong_metric_reduction_gate
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (test : GlobalMinimalPhysicalMetricTest period hPeriod) :
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
      regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection period
        hPeriod configuration.physical test
    regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLagrangeOperator
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase measure point direction =
      ((((actionGradient blocks.candidateA point direction +
          actionGradient blocks.einsteinHilbertPlus point direction) +
          actionGradient blocks.einsteinHilbertMinus point direction) +
          actionGradient blocks.maxwellPlus point direction) +
          actionGradient blocks.maxwellMinus point direction) :=
  regularGeneralMetricC2PairedMinimalPhysicalStrongEuler_strongMetric_eq_metricBlocks
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase measure point hPoint test


end

end
end P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMetricTotalEulerReduction4D
end JanusFormal
