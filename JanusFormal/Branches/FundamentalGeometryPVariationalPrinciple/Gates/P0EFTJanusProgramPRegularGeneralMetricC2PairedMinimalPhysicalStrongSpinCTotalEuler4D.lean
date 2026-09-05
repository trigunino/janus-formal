import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLLAuxMeasureTotalEuler4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongSpinCSpectralAugmentedResidual4D

/-! # Total SpinC Euler equation in the concrete strong chart -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongSpinCTotalEuler4D

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
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSeparatingPDEResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSevenBulkSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeMatterGraphMaximalSpectralResidual4D
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
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongSpinCSpectralAugmentedResidual4D
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
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection_fullMetricPerturbation
    (test : ProgramPPrimitiveSpinCMatterSmoothField period hPeriod) :
    (regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection period hPeriod
      configuration.physical test).1.completeVariation.fullMetricPerturbation =
      0 :=
  rfl

omit data analysis realization hBase measure point plusBase minusBase
    [IsFiniteMeasure measure] in
@[simp]
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection_gauge
    (test : ProgramPPrimitiveSpinCMatterSmoothField period hPeriod) :
    (regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection period hPeriod
      configuration.physical test).1.completeVariation.independent.gauge = 0 :=
  rfl

omit data analysis realization hBase measure point plusBase minusBase
    [IsFiniteMeasure measure] in
@[simp]
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection_spinCMatter
    (test : ProgramPPrimitiveSpinCMatterSmoothField period hPeriod) :
    (regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection period hPeriod
      configuration.physical test).1.2 = test :=
  rfl

omit data analysis realization hBase measure point [IsFiniteMeasure measure] in
@[simp]
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection_relativeMetricCore
    (test : ProgramPPrimitiveSpinCMatterSmoothField period hPeriod) :
    globalMinimalPhysicalPairedRelativeMetricCoreLinearMap period hPeriod
        configuration.physical plusBase minusBase
        (regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection period
          hPeriod configuration.physical test) = 0 := by
  have hMetric :=
    regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection_fullMetricPerturbation
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
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection_oldCoreCLM
    (test : ProgramPPrimitiveSpinCMatterSmoothField period hPeriod) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    globalMinimalPhysicalPairedMetricGaugeLLStrongOldCoreCLM period hPeriod
        configuration data analysis realization plusBase minusBase
        (regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection period
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
      regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection_relativeMetricCore
        period hPeriod configuration plusBase minusBase test
  · rw [globalMinimalPhysicalPairedMetricGaugeCoreLinearMap_gauge,
      regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection_gauge]
    exact map_zero _

omit hBase measure point [IsFiniteMeasure measure] in
@[simp]
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection_metricCLM
    (test : ProgramPPrimitiveSpinCMatterSmoothField period hPeriod) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    globalMinimalPhysicalPairedMetricGaugeLLStrongMetricCLM period hPeriod
        configuration data analysis realization plusBase minusBase
        (regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection period
          hPeriod configuration.physical test) = 0 := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  rw [globalMinimalPhysicalPairedMetricGaugeLLStrongMetricCLM_apply]
  exact
    regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection_relativeMetricCore
      period hPeriod configuration plusBase minusBase test

omit hBase measure point [IsFiniteMeasure measure] in
@[simp]
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection_matterCLM
    (test : ProgramPPrimitiveSpinCMatterSmoothField period hPeriod) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    globalMinimalPhysicalPairedMetricGaugeLLStrongMatterCLM period hPeriod
        configuration data analysis realization plusBase minusBase
        (regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection period
          hPeriod configuration.physical test) = realization.toGraph test := by
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
      (regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection period
        hPeriod configuration.physical test).1.2 = realization.toGraph test
  rw [regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection_spinCMatter]

omit data analysis realization hBase measure point plusBase minusBase
    [IsFiniteMeasure measure] in
/-- A pure strong SpinC direction has no LL coefficient component. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection_ll_eq_zero
    (test : ProgramPPrimitiveSpinCMatterSmoothField period hPeriod) :
    let direction :=
      regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection period
        hPeriod configuration.physical test
    direction.1.completeVariation.independent.llAuxMetric = 0 ∧
      direction.1.completeVariation.independent.llMeasure = 0 ∧
      direction.1.completeVariation.independent.llField = 0 := by
  exact ⟨rfl, rfl, rfl⟩

/-- The strong LL first-jet projection kills a pure SpinC direction. -/
@[simp]
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection_strongLLCLM
    (test : ProgramPPrimitiveSpinCMatterSmoothField period hPeriod) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    globalMinimalPhysicalPairedLLC0FirstJetCLM period hPeriod configuration data
        analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
        (regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection period
          hPeriod configuration.physical test) = 0 := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
    hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  rw [globalMinimalPhysicalPairedLLC0FirstJetCLM_apply]
  unfold globalMinimalPhysicalLLC0FirstJetLinearMap
    globalMinimalPhysicalLLSmoothCoefficientLinearMap
  have hLL :=
    regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection_ll_eq_zero
      period hPeriod configuration test
  change smoothLLCoefficientPTC0FirstJetLinearMap period hPeriod
      (canonicalDivergenceFreeLLFrame period hPeriod)
      (_, (_, _)) = 0
  rw [hLL.1, hLL.2.1, hLL.2.2]
  exact map_zero _

/-- The interaction block depends only on metric coordinates, hence has no
pure SpinC variation. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalCandidateA_actionGradient_strongSpinC_eq_zero
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (test : ProgramPPrimitiveSpinCMatterSmoothField period hPeriod) :
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
        (regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection period
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
      (regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection period
        hPeriod configuration.physical test) = 0
  rw [hEventually.fderiv_eq]
  exact actionGradient_comp_apply_eq_zero outer projection point
    (regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection period
      hPeriod configuration.physical test) hOuter
    (regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection_metricCLM
      period hPeriod configuration data analysis realization plusBase minusBase
        test)

/-- Both Einstein--Hilbert blocks depend only on metric coordinates. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalEinsteinHilbert_actionGradient_strongSpinC_eq_zero
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (test : ProgramPPrimitiveSpinCMatterSmoothField period hPeriod) :
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
      regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection period
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
    regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection period
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
    regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection_metricCLM
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
theorem regularGeneralMetricC2PairedMinimalPhysicalMaxwell_actionGradient_strongSpinC_eq_zero
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (test : ProgramPPrimitiveSpinCMatterSmoothField period hPeriod) :
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
      regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection period
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
    regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection period
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
    regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection_oldCoreCLM
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
/-- The nonlinear LL block has no pure SpinC variation. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalLL_actionGradient_strongSpinC_eq_zero
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (test : ProgramPPrimitiveSpinCMatterSmoothField period hPeriod) :
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
        (regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection period
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
      (regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection period
        hPeriod configuration.physical test) = 0
  rw [hEventually.fderiv_eq]
  exact actionGradient_comp_apply_eq_zero outer projection point
    (regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection period
      hPeriod configuration.physical test) hOuter
    (regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection_strongLLCLM
      period hPeriod configuration data analysis realization plusBase minusBase
        test)

omit [IsFiniteMeasure measure] in
/-- The active matter block is exactly the maximal SpinC graph form. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalMatter_actionGradient_strongSpinC_eq_graphForm
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (test : ProgramPPrimitiveSpinCMatterSmoothField period hPeriod) :
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
        (regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection
          period hPeriod configuration.physical test) =
      programPPrimitiveSpinCMatterGraphForm period hPeriod
        couplings.matterMassSquared
        (regularGeneralMetricC2PairedMinimalPhysicalStrongMatterGraphState
          period hPeriod configuration realization point)
        (realization.toGraph test) := by
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
  let base := realization.toGraph configuration.physical.spinCMatter
  have hOpen :=
    regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain_strong_isOpen
      period hPeriod configuration data analysis realization plusBase minusBase
  have hEventually :
      blocks.matter =ᶠ[nhds point]
        fun current => programPPrimitiveSpinCMatterGraphAction period hPeriod
          couplings.matterMassSquared (base + projection current) := by
    filter_upwards [hOpen.mem_nhds hPoint] with current hCurrent
    simpa [blocks, base, projection,
      regularGeneralMetricC2PairedMinimalPhysicalMatterGraphInput] using
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_matter_eq
        period hPeriod configuration data realization plusBase minusBase hBase
          measure current hCurrent)
  have hInput : HasFDerivAt (fun current => base + projection current)
      projection point :=
    projection.hasFDerivAt.const_add base
  have hDerivative :=
    (programPPrimitiveSpinCMatterGraphAction_hasFDerivAt period hPeriod
      couplings.matterMassSquared (base + projection point)).comp point hInput
  have hProjection : projection
      (regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection
        period hPeriod configuration.physical test) = realization.toGraph test :=
    regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection_matterCLM
      period hPeriod configuration data analysis realization plusBase minusBase
        test
  change fderiv Real blocks.matter point
      (regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection
        period hPeriod configuration.physical test) = _
  rw [hEventually.fderiv_eq]
  change fderiv Real
      (programPPrimitiveSpinCMatterGraphAction period hPeriod
        couplings.matterMassSquared ∘ fun current => base + projection current)
      point _ = _
  rw [hDerivative.fderiv]
  simp only [ContinuousLinearMap.comp_apply, hProjection]
  rfl

/-- On a pure SpinC direction the complete nine-block sum is exactly the
primitive matter block. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalFullBlockSum_strongSpinC_eq_matter
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (test : ProgramPPrimitiveSpinCMatterSmoothField period hPeriod) :
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
      regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection
        period hPeriod configuration.physical test
    fullCoupledEulerBlockSum blocks point direction =
      actionGradient blocks.matter point direction := by
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
    regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection
      period hPeriod configuration.physical test
  have hCandidate : actionGradient blocks.candidateA point direction = 0 := by
    simpa [blocks, direction] using
      (regularGeneralMetricC2PairedMinimalPhysicalCandidateA_actionGradient_strongSpinC_eq_zero
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
      (regularGeneralMetricC2PairedMinimalPhysicalLL_actionGradient_strongSpinC_eq_zero
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase measure point hPoint test)
  have hEinstein :=
    regularGeneralMetricC2PairedMinimalPhysicalEinsteinHilbert_actionGradient_strongSpinC_eq_zero
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point hPoint test
  have hEinsteinPlus :
      actionGradient blocks.einsteinHilbertPlus point direction = 0 := by
    simpa [blocks, direction] using hEinstein.1
  have hEinsteinMinus :
      actionGradient blocks.einsteinHilbertMinus point direction = 0 := by
    simpa [blocks, direction] using hEinstein.2
  have hMaxwell :=
    regularGeneralMetricC2PairedMinimalPhysicalMaxwell_actionGradient_strongSpinC_eq_zero
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
  rw [hCandidate, hRobin, hLL, hEinsteinPlus, hEinsteinMinus,
    hMaxwellPlus, hMaxwellMinus, hFinite]
  norm_num

/-- The complete strong Euler operator restricts to the exact SpinC graph
form, with no coupled remainder. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongEuler_strongSpinC_eq_graphForm
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (test : ProgramPPrimitiveSpinCMatterSmoothField period hPeriod) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLagrangeOperator
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase measure point
        (regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection
          period hPeriod configuration.physical test) =
      programPPrimitiveSpinCMatterGraphForm period hPeriod
        couplings.matterMassSquared
        (regularGeneralMetricC2PairedMinimalPhysicalStrongMatterGraphState
          period hPeriod configuration realization point)
        (realization.toGraph test) := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  rw [regularGeneralMetricC2PairedMinimalPhysicalStrongEuler_eq_nineBlockSum
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase measure point hPoint]
  rw [regularGeneralMetricC2PairedMinimalPhysicalFullBlockSum_strongSpinC_eq_matter
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase measure point hPoint test]
  exact
    regularGeneralMetricC2PairedMinimalPhysicalMatter_actionGradient_strongSpinC_eq_graphForm
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point hPoint test

/-- Pair the total SpinC residual with an authentic smooth test through its
maximal-graph realization. -/
def regularGeneralMetricC2PairedMinimalPhysicalSpinCTotalSpectralResidualPairing
    (residual : ProgramPPrimitiveSpinCMatterHilbert)
    (test : ProgramPPrimitiveSpinCMatterSmoothField period hPeriod) : Real :=
  programPPrimitiveSpinCMatterGraphMaximalSpectralResidualPairing period hPeriod
    couplings.matterMassSquared residual (realization.toGraph test)

/-- The total SpinC Euler equation is represented by the explicit maximal
spectral residual. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongEuler_strongSpinC_eq_spectralResidualPairing
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (test : ProgramPPrimitiveSpinCMatterSmoothField period hPeriod) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLagrangeOperator
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase measure point
        (regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection
          period hPeriod configuration.physical test) =
      regularGeneralMetricC2PairedMinimalPhysicalSpinCTotalSpectralResidualPairing
        period hPeriod realization
        (programPPrimitiveSpinCMatterGraphMaximalSpectralResidual period hPeriod
          couplings.matterMassSquared
          (regularGeneralMetricC2PairedMinimalPhysicalStrongMatterGraphState
            period hPeriod configuration realization point)) test := by
  rw [regularGeneralMetricC2PairedMinimalPhysicalStrongEuler_strongSpinC_eq_graphForm
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase measure point hPoint test]
  exact programPPrimitiveSpinCMatterGraphForm_eq_maximalResidualPairing period
    hPeriod couplings.matterMassSquared
      (regularGeneralMetricC2PairedMinimalPhysicalStrongMatterGraphState period
        hPeriod configuration realization point) (realization.toGraph test)

/-- Smooth SpinC tests separate every ambient spectral residual because the
finite Fourier graph core lies in the realization image. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalSpinCTotalSpectralResidualPairing_separates
    (residual : ProgramPPrimitiveSpinCMatterHilbert) :
    (∀ test : ProgramPPrimitiveSpinCMatterSmoothField period hPeriod,
      regularGeneralMetricC2PairedMinimalPhysicalSpinCTotalSpectralResidualPairing
        period hPeriod realization residual test = 0) ↔ residual = 0 := by
  classical
  constructor
  · intro hPairing
    ext mode
    let coefficients : ProgramPPrimitiveSpinCMatterFiniteCoefficients :=
      Finsupp.single mode (residual mode)
    let test := programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
      coefficients
    have hMode := hPairing test
    unfold regularGeneralMetricC2PairedMinimalPhysicalSpinCTotalSpectralResidualPairing
      at hMode
    rw [realization.finite_compatibility coefficients] at hMode
    change inner Real
      (programPPrimitiveSpinCMatterFiniteHilbertEmbedding coefficients)
      residual = 0 at hMode
    have hSingle :
        programPPrimitiveSpinCMatterFiniteHilbertEmbedding coefficients =
          (lp.single 2 mode (residual mode) :
            ProgramPPrimitiveSpinCMatterHilbert) := by
      ext other
      rw [programPPrimitiveSpinCMatterFiniteHilbertEmbedding_apply]
      change (Finsupp.single mode (residual mode)) other =
        (lp.single 2 mode (residual mode) :
          ProgramPPrimitiveSpinCMatterHilbert) other
      by_cases hOther : other = mode
      · subst other
        simp
      · rw [Finsupp.single_eq_of_ne hOther]
        simp [hOther]
    rw [hSingle, real_inner_eq_re_inner, lp.inner_single_left] at hMode
    rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow,
      RCLike.ofReal_re] at hMode
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hMode)
  · intro hResidual test
    rw [hResidual]
    simp [regularGeneralMetricC2PairedMinimalPhysicalSpinCTotalSpectralResidualPairing,
      programPPrimitiveSpinCMatterGraphMaximalSpectralResidualPairing]

/-- Separating representation of the complete SpinC Euler covector. -/
def regularGeneralMetricC2PairedMinimalPhysicalSpinCTotalSpectralResidualRepresentation
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) :
    SeparatingPDEResidualRepresentation
      (regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterEulerCovectorAt
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase measure point) where
  Residual := ProgramPPrimitiveSpinCMatterHilbert
  zeroResidual := 0
  residual := programPPrimitiveSpinCMatterGraphMaximalSpectralResidual period
    hPeriod couplings.matterMassSquared
      (regularGeneralMetricC2PairedMinimalPhysicalStrongMatterGraphState period
        hPeriod configuration realization point)
  pairing :=
    regularGeneralMetricC2PairedMinimalPhysicalSpinCTotalSpectralResidualPairing
      period hPeriod realization
  represents := by
    intro test
    change regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLagrangeOperator
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase measure point
        (regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection
          period hPeriod configuration.physical test) = _
    exact
      regularGeneralMetricC2PairedMinimalPhysicalStrongEuler_strongSpinC_eq_spectralResidualPairing
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase measure point hPoint test
  separates :=
    regularGeneralMetricC2PairedMinimalPhysicalSpinCTotalSpectralResidualPairing_separates
      period hPeriod realization _

/-- Vanishing of the complete SpinC covector is exactly vanishing of its
maximal spectral residual. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterEuler_eq_zero_iff_spectralResidual
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) :
    regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterEulerCovectorAt
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase measure point = 0 ↔
      programPPrimitiveSpinCMatterGraphMaximalSpectralResidual period hPeriod
          couplings.matterMassSquared
          (regularGeneralMetricC2PairedMinimalPhysicalStrongMatterGraphState
            period hPeriod configuration realization point) = 0 :=
  separatingPDEResidualRepresentation_covector_eq_zero_iff
    (regularGeneralMetricC2PairedMinimalPhysicalSpinCTotalSpectralResidualRepresentation
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point hPoint)

/-- The maximal residual equation is the modewise multiplier equation
`(2D + m²) ψ = 0`. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalSpinCTotalSpectralResidual_eq_zero_iff_modewise
    :
    programPPrimitiveSpinCMatterGraphMaximalSpectralResidual period hPeriod
        couplings.matterMassSquared
        (regularGeneralMetricC2PairedMinimalPhysicalStrongMatterGraphState
          period hPeriod configuration realization point) = 0 ↔
      ∀ mode : ProgramPPrimitiveSpinCMatterMode,
        ((programPPrimitiveSpinCMatterHessianWeight period hPeriod
          couplings.matterMassSquared mode : Real) : Complex) *
          (regularGeneralMetricC2PairedMinimalPhysicalStrongMatterGraphState
            period hPeriod configuration realization point).1.1 mode = 0 := by
  constructor
  · intro hResidual mode
    have hMode := congrArg
      (fun residual : ProgramPPrimitiveSpinCMatterHilbert => residual mode)
      hResidual
    rw [programPPrimitiveSpinCMatterGraphMaximalSpectralResidual_apply]
      at hMode
    simpa using hMode
  · intro hMode
    ext mode
    rw [programPPrimitiveSpinCMatterGraphMaximalSpectralResidual_apply]
    simpa using hMode mode

/-- Stationarity of the total action in every authentic SpinC direction is
equivalent to the explicit modewise strong SpinC PDE. -/
theorem regular_general_metric_c2_paired_minimal_physical_total_strong_spinc_stationary_iff_modewise_equation_gate
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    (∀ test : ProgramPPrimitiveSpinCMatterSmoothField period hPeriod,
      regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLagrangeOperator
          period hPeriod configuration data analysis realization plusBase
            minusBase hBase measure point
          (regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection
            period hPeriod configuration.physical test) = 0) ↔
      ∀ mode : ProgramPPrimitiveSpinCMatterMode,
        ((programPPrimitiveSpinCMatterHessianWeight period hPeriod
          couplings.matterMassSquared mode : Real) : Complex) *
          (regularGeneralMetricC2PairedMinimalPhysicalStrongMatterGraphState
            period hPeriod configuration realization point).1.1 mode = 0 := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  rw [←
    regularGeneralMetricC2PairedMinimalPhysicalSpinCTotalSpectralResidual_eq_zero_iff_modewise
      period hPeriod configuration realization point]
  constructor
  · intro hEuler
    apply
      (regularGeneralMetricC2PairedMinimalPhysicalSpinCTotalSpectralResidualPairing_separates
        period hPeriod realization _).mp
    intro test
    rw [←
      regularGeneralMetricC2PairedMinimalPhysicalStrongEuler_strongSpinC_eq_spectralResidualPairing
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase measure point hPoint test]
    exact hEuler test
  · intro hResidual test
    rw [regularGeneralMetricC2PairedMinimalPhysicalStrongEuler_strongSpinC_eq_spectralResidualPairing
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point hPoint test]
    exact
      (regularGeneralMetricC2PairedMinimalPhysicalSpinCTotalSpectralResidualPairing_separates
        period hPeriod realization _).mpr hResidual test


end

end
end P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongSpinCTotalEuler4D
end JanusFormal
