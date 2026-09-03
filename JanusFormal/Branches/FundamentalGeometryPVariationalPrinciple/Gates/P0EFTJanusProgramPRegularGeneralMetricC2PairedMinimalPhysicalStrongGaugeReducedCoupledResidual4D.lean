import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongGaugeEulerBoundaryAugmentedResidual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricStrongMaxwellPDE4D

/-! # Reduced non-Maxwell remainder of the strong gauge equation -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongGaugeReducedCoupledResidual4D

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
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPGlobalEulerLagrangeBlockDecomposition4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSevenBulkSystem4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartRegularMetric4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartMaxwell4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomainOpen4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalConstantBoundaryC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalInteractionC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMatterC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalRelativeMetricCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedFixedVolumeEinsteinHilbertC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedEinsteinHilbertActionBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalNineBlockC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongComponentPDEBlockPairing4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongEightSectorEuler4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLocalEuler4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellWeakFirstVariation4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongGaugeCoupledResidual4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellCanonicalEulerBoundary4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongGaugeEulerBoundaryCoupledResidual4D
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

local instance canonicalThroatMeasureIsFinite :
    IsFiniteMeasure (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod

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

omit data analysis realization hBase measure point [IsFiniteMeasure measure] in
/-- The algebraic paired relative-metric projection kills a pure gauge direction. -/
@[simp]
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeDirection_relativeMetricCoreLinearMap
    (test : GlobalMinimalPhysicalGaugeTest period hPeriod) :
    globalMinimalPhysicalPairedRelativeMetricCoreLinearMap period hPeriod
        configuration.physical plusBase minusBase
        (regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeDirection period
          hPeriod configuration.physical test) = 0 := by
  have hMetric :=
    regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeDirection_fullMetricPerturbation
      period hPeriod configuration.physical test
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

/-- The continuous metric projection of the strong chart kills a pure gauge
direction. -/
@[simp]
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeDirection_strongMetricCLM
    (test : GlobalMinimalPhysicalGaugeTest period hPeriod) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    globalMinimalPhysicalPairedMetricGaugeLLStrongMetricCLM period hPeriod
        configuration data analysis realization plusBase minusBase
        (regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeDirection period
          hPeriod configuration.physical test) = 0 := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
    hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  rw [globalMinimalPhysicalPairedMetricGaugeLLStrongMetricCLM_apply]
  exact
    regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeDirection_relativeMetricCoreLinearMap
      period hPeriod configuration plusBase minusBase test

omit data analysis realization hBase measure point plusBase minusBase
    [IsFiniteMeasure measure] in
/-- A pure strong gauge direction has no primitive SpinC component. -/
@[simp]
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeDirection_spinCMatter
    (test : GlobalMinimalPhysicalGaugeTest period hPeriod) :
    (regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeDirection period
      hPeriod configuration.physical test).1.2 = 0 :=
  rfl

/-- The continuous matter projection of the strong chart kills a pure gauge
direction. -/
@[simp]
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeDirection_strongMatterCLM
    (test : GlobalMinimalPhysicalGaugeTest period hPeriod) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    globalMinimalPhysicalPairedMetricGaugeLLStrongMatterCLM period hPeriod
        configuration data analysis realization plusBase minusBase
        (regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeDirection period
          hPeriod configuration.physical test) = 0 := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
    hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  rw [globalMinimalPhysicalPairedMetricGaugeLLStrongMatterCLM_apply]
  unfold globalMinimalPhysicalMatterGraphLinearMap
    globalMinimalPhysicalSpinCMatterLinearMap
  change realization.toGraph
      (regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeDirection period
        hPeriod configuration.physical test).1.2 = 0
  rw [regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeDirection_spinCMatter]
  exact map_zero _

omit data analysis realization hBase measure point plusBase minusBase
    [IsFiniteMeasure measure] in
/-- A pure strong gauge direction has no LL coefficient component. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeDirection_ll_eq_zero
    (test : GlobalMinimalPhysicalGaugeTest period hPeriod) :
    let direction :=
      regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeDirection period
        hPeriod configuration.physical test
    direction.1.completeVariation.independent.llAuxMetric = 0 ∧
      direction.1.completeVariation.independent.llMeasure = 0 ∧
      direction.1.completeVariation.independent.llField = 0 := by
  exact ⟨rfl, rfl, rfl⟩

/-- The strong LL first-jet projection kills a pure gauge direction. -/
@[simp]
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeDirection_strongLLCLM
    (test : GlobalMinimalPhysicalGaugeTest period hPeriod) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    globalMinimalPhysicalPairedLLC0FirstJetCLM period hPeriod configuration data
        analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
        (regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeDirection period
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
    regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeDirection_ll_eq_zero
      period hPeriod configuration test
  change smoothLLCoefficientPTC0FirstJetLinearMap period hPeriod
      (canonicalDivergenceFreeLLFrame period hPeriod)
      (_, (_, _)) = 0
  rw [hLL.1, hLL.2.1, hLL.2.2]
  exact map_zero _

/-- The Candidate-A interaction block has no pure gauge variation. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalCandidateA_actionGradient_strongGauge_eq_zero
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
    actionGradient
        (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
          period hPeriod configuration.physical couplings data plusBase minusBase
            hBase measure).candidateA point
        (regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeDirection period
          hPeriod configuration.physical test) = 0 := by
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
      (regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeDirection period
        hPeriod configuration.physical test) = 0
  rw [hEventually.fderiv_eq]
  exact actionGradient_comp_apply_eq_zero outer projection point
    (regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeDirection period
      hPeriod configuration.physical test) hOuter
    (regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeDirection_strongMetricCLM
      period hPeriod configuration data analysis realization plusBase minusBase
        test)

/-- The two Einstein--Hilbert blocks have no pure gauge variation. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalEinsteinHilbert_actionGradient_strongGauge_eq_zero
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
    actionGradient blocks.einsteinHilbertPlus point direction = 0 ∧
      actionGradient blocks.einsteinHilbertMinus point direction = 0 := by
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
    regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeDirection period
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
    regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeDirection_strongMetricCLM
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

omit [IsFiniteMeasure measure] in
/-- The primitive SpinC matter block has no pure gauge variation. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalMatter_actionGradient_strongGauge_eq_zero
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
    actionGradient
        (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
          period hPeriod configuration.physical couplings data plusBase minusBase
            hBase measure).matter point
        (regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeDirection period
          hPeriod configuration.physical test) = 0 := by
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
      (regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeDirection period
        hPeriod configuration.physical test) = 0
  rw [hEventually.fderiv_eq]
  exact actionGradient_comp_apply_eq_zero outer projection point
    (regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeDirection period
      hPeriod configuration.physical test) hOuter
    (regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeDirection_strongMatterCLM
      period hPeriod configuration data analysis realization plusBase minusBase
        test)

omit [IsFiniteMeasure measure] in
/-- The nonlinear LL block has no pure gauge variation. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalLL_actionGradient_strongGauge_eq_zero
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
    actionGradient
        (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
          period hPeriod configuration.physical couplings data plusBase minusBase
            hBase measure).ll point
        (regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeDirection period
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
      (regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeDirection period
        hPeriod configuration.physical test) = 0
  rw [hEventually.fderiv_eq]
  exact actionGradient_comp_apply_eq_zero outer projection point
    (regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeDirection period
      hPeriod configuration.physical test) hOuter
    (regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeDirection_strongLLCLM
      period hPeriod configuration data analysis realization plusBase minusBase
        test)

omit [IsFiniteMeasure measure] in
/-- The constant Robin block has zero gradient at every admissible point. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalRobin_actionGradient_eq_zero
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    actionGradient
        (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
          period hPeriod configuration.physical couplings data plusBase minusBase
            hBase measure).robin point = 0 := by
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
  have hOpen :=
    regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain_strong_isOpen
      period hPeriod configuration data analysis realization plusBase minusBase
  have hEventually :
      blocks.robin =ᶠ[nhds point]
        fun _ => globalCandidateAGHYAction period hPeriod data := by
    filter_upwards [hOpen.mem_nhds hPoint] with direction hDirection
    exact
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_robin_eq
        period hPeriod configuration.physical couplings data plusBase minusBase
          hBase measure direction hDirection
  change fderiv Real blocks.robin point = 0
  rw [hEventually.fderiv_eq]
  simp

omit [IsFiniteMeasure measure] in
/-- The constant finite-BV block has zero gradient at every admissible point. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalFiniteBV_actionGradient_eq_zero
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    actionGradient
        (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
          period hPeriod configuration.physical couplings data plusBase minusBase
            hBase measure).finiteBV point = 0 := by
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
  have hOpen :=
    regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain_strong_isOpen
      period hPeriod configuration data analysis realization plusBase minusBase
  have hEventually :
      blocks.finiteBV =ᶠ[nhds point]
        fun _ => globalCandidateANullBoundaryAction period hPeriod data := by
    filter_upwards [hOpen.mem_nhds hPoint] with direction hDirection
    exact
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_finiteBV_eq
        period hPeriod configuration.physical couplings data plusBase minusBase
          hBase measure direction hDirection
  change fderiv Real blocks.finiteBV point = 0
  rw [hEventually.fderiv_eq]
  simp

/-- Every non-Maxwell block is inactive in a pure strong gauge direction. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeCoupledRemainder_eq_zero
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (test : GlobalMinimalPhysicalGaugeTest period hPeriod) :
    regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeCoupledRemainder
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point test = 0 := by
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
  have hCandidate : actionGradient blocks.candidateA point direction = 0 := by
    simpa [blocks, direction] using
      (regularGeneralMetricC2PairedMinimalPhysicalCandidateA_actionGradient_strongGauge_eq_zero
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase measure point hPoint test)
  have hMatter : actionGradient blocks.matter point direction = 0 := by
    simpa [blocks, direction] using
      (regularGeneralMetricC2PairedMinimalPhysicalMatter_actionGradient_strongGauge_eq_zero
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
      (regularGeneralMetricC2PairedMinimalPhysicalLL_actionGradient_strongGauge_eq_zero
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase measure point hPoint test)
  have hEinstein :=
    regularGeneralMetricC2PairedMinimalPhysicalEinsteinHilbert_actionGradient_strongGauge_eq_zero
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point hPoint test
  have hEinsteinPlus :
      actionGradient blocks.einsteinHilbertPlus point direction = 0 := by
    simpa [blocks, direction] using hEinstein.1
  have hEinsteinMinus :
      actionGradient blocks.einsteinHilbertMinus point direction = 0 := by
    simpa [blocks, direction] using hEinstein.2
  have hFiniteCLM : actionGradient blocks.finiteBV point = 0 := by
    simpa [blocks] using
      (regularGeneralMetricC2PairedMinimalPhysicalFiniteBV_actionGradient_eq_zero
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase measure point hPoint)
  have hFinite : actionGradient blocks.finiteBV point direction = 0 := by
    rw [hFiniteCLM]
    rfl
  unfold
    regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeCoupledRemainder
  dsimp only
  rw [hCandidate, hMatter, hRobin, hLL, hEinsteinPlus, hEinsteinMinus,
    hFinite]
  norm_num

/-- The authentic strong gauge residual after eliminating all seven inactive
non-Maxwell blocks. -/
def regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeMaxwellEulerBoundaryResidual
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
        minusMetric minusPotential minusVariation measure

/-- Gate418's coupled residual is exactly its two Maxwell terms. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeEulerBoundaryCoupledResidual_eq_maxwell
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (test : GlobalMinimalPhysicalGaugeTest period hPeriod) :
    regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeEulerBoundaryCoupledResidual
        period hPeriod configuration data analysis realization plusBase
          minusBase hBase measure point hPoint test =
      regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeMaxwellEulerBoundaryResidual
        period hPeriod (couplings := couplings) configuration plusBase minusBase
          measure point hPoint test := by
  unfold
    regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeEulerBoundaryCoupledResidual
    regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeMaxwellEulerBoundaryResidual
  dsimp only
  rw [regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeCoupledRemainder_eq_zero
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase measure point hPoint test]
  ring

/-- The total gauge Euler covector is exhausted by the two Maxwell
Euler--boundary integrals. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeEuler_eq_maxwellEulerBoundary
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
      regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeMaxwellEulerBoundaryResidual
        period hPeriod (couplings := couplings) configuration plusBase minusBase
          measure point hPoint test := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
    hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  rw [regular_general_metric_c2_paired_minimal_physical_strong_gauge_euler_boundary_coupled_residual_gate
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase measure point hPoint test]
  exact
    regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeEulerBoundaryCoupledResidual_eq_maxwell
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point hPoint test

/-- Strong gauge stationarity is now exactly the vanishing of the two Maxwell
Euler--boundary integrals on every paired test. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeEuler_eq_zero_iff_maxwellEulerBoundary
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
        regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeMaxwellEulerBoundaryResidual
          period hPeriod (couplings := couplings) configuration plusBase minusBase
            measure point hPoint test = 0 := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
    hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  constructor
  · intro hStationary test
    have hCoupled :=
      (regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeEuler_eq_zero_iff_eulerBoundaryCoupledResidual
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase measure point hPoint).mp hStationary test
    rwa [regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeEulerBoundaryCoupledResidual_eq_maxwell
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point hPoint test] at hCoupled
  · intro hResidual
    apply
      (regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeEuler_eq_zero_iff_eulerBoundaryCoupledResidual
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase measure point hPoint).mpr
    intro test
    rw [regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeEulerBoundaryCoupledResidual_eq_maxwell
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point hPoint test]
    exact hResidual test

/-- Summary gate: the seven-block remainder vanishes, and the authentic gauge
equation contains precisely the two Maxwell first variations. -/
theorem regular_general_metric_c2_paired_minimal_physical_strong_gauge_reduced_coupled_residual_gate
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) :
    (∀ test : GlobalMinimalPhysicalGaugeTest period hPeriod,
      regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeCoupledRemainder
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase measure point test = 0) ∧
      (letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
        period hPeriod configuration data analysis realization plusBase minusBase
          (canonicalDivergenceFreeLLFrame period hPeriod)
       letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
        hPeriod configuration data analysis realization plusBase minusBase
          (canonicalDivergenceFreeLLFrame period hPeriod)
       regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeEulerCovectorAt
          period hPeriod configuration data analysis realization plusBase
            minusBase hBase measure point = 0 ↔
        ∀ test : GlobalMinimalPhysicalGaugeTest period hPeriod,
          regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeMaxwellEulerBoundaryResidual
            period hPeriod (couplings := couplings) configuration plusBase
              minusBase measure point hPoint test = 0) := by
  exact ⟨fun test =>
      regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeCoupledRemainder_eq_zero
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase measure point hPoint test,
    regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeEuler_eq_zero_iff_maxwellEulerBoundary
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point hPoint⟩

end

end

end P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongGaugeReducedCoupledResidual4D
end JanusFormal
