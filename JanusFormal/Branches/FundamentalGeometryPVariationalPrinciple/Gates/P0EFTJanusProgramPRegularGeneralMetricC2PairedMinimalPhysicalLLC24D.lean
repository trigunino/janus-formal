import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D

/-! # C² regularity of the genuine paired minimal-physical LL block -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC24D

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 1200000

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusGlobalLLWorldvolume4D
open P0EFTJanusMappingTorusGlobalLLCovariance4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusGeneralLorentzIndependentFieldPacket4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalConfigurationAt4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomainOpen4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalConstantBoundaryC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricGaugeCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D

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

local instance effectiveThroatMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance effectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

attribute [local instance 2000]
  NonUnitalNormedRing.toNormedAddCommGroup NormedAlgebra.toNormedSpace

local instance c2ScalarNormedAddCommGroup :
    NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule
    period hPeriod).normedAddCommGroup

local instance c2ScalarNormedSpace :
    NormedSpace Real (C2Scalar period hPeriod) := inferInstance

section PolynomialDensity

variable {Index : Type*} [Fintype Index]

/-- A Euclidean coordinate, lifted pointwise to continuous fields. -/
def continuousEuclideanCoordinateCLM
    (index : Index) :
    C(EffectiveThroat period hPeriod, EuclideanSpace Real Index) →L[Real]
      C(EffectiveThroat period hPeriod, Real) :=
  (EuclideanSpace.proj index).compLeftContinuous Real
    (EffectiveThroat period hPeriod)

/-- Pointwise Euclidean norm square, expressed polynomially in coordinates. -/
def continuousEuclideanNormSq
    (field : C(EffectiveThroat period hPeriod,
      EuclideanSpace Real Index)) :
    C(EffectiveThroat period hPeriod, Real) :=
  ∑ index : Index,
    (continuousEuclideanCoordinateCLM period hPeriod index field) ^ 2

theorem continuousEuclideanNormSq_contDiff :
    ContDiff Real ∞
      (continuousEuclideanNormSq period hPeriod (Index := Index)) := by
  unfold continuousEuclideanNormSq
  apply ContDiff.sum
  intro index _
  exact (continuousEuclideanCoordinateCLM period hPeriod index).contDiff.pow 2

@[simp]
theorem continuousEuclideanNormSq_apply
    (field : C(EffectiveThroat period hPeriod,
      EuclideanSpace Real Index))
    (point : EffectiveThroat period hPeriod) :
    continuousEuclideanNormSq period hPeriod field point = ‖field point‖ ^ 2 := by
  simp [continuousEuclideanNormSq, continuousEuclideanCoordinateCLM]
  exact (EuclideanSpace.real_norm_sq_eq (field point)).symm

end PolynomialDensity

/-- One coordinate of the stored frame derivative of the LL flux. -/
def continuousLLDerivativeCoordinateCLM
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (frameIndex : Fin frame.count) (component : Fin 4) :
    C(EffectiveThroat period hPeriod, Fin frame.count → LLFieldFiber) →L[Real]
      C(EffectiveThroat period hPeriod, Real) :=
  ((EuclideanSpace.proj component).comp
    (ContinuousLinearMap.proj frameIndex)).compLeftContinuous Real
      (EffectiveThroat period hPeriod)

/-- Pointwise sum of the Euclidean squares of all stored frame derivatives. -/
def continuousLLDerivativeEnergy
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (derivative :
      C(EffectiveThroat period hPeriod, Fin frame.count → LLFieldFiber)) :
    C(EffectiveThroat period hPeriod, Real) :=
  ∑ frameIndex : Fin frame.count, ∑ component : Fin 4,
    (continuousLLDerivativeCoordinateCLM period hPeriod frame frameIndex
      component derivative) ^ 2

theorem continuousLLDerivativeEnergy_contDiff
    (frame : SmoothThroatGeneratingFrame period hPeriod) :
    ContDiff Real ∞
      (continuousLLDerivativeEnergy period hPeriod frame) := by
  unfold continuousLLDerivativeEnergy
  apply ContDiff.sum
  intro frameIndex _
  apply ContDiff.sum
  intro component _
  exact (continuousLLDerivativeCoordinateCLM period hPeriod frame frameIndex
    component).contDiff.pow 2

@[simp]
theorem continuousLLDerivativeEnergy_apply
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (derivative :
      C(EffectiveThroat period hPeriod, Fin frame.count → LLFieldFiber))
    (point : EffectiveThroat period hPeriod) :
    continuousLLDerivativeEnergy period hPeriod frame derivative point =
      ∑ frameIndex : Fin frame.count, ‖derivative point frameIndex‖ ^ 2 := by
  simp [continuousLLDerivativeEnergy,
    continuousLLDerivativeCoordinateCLM]
  apply Finset.sum_congr rfl
  intro frameIndex _
  exact (EuclideanSpace.real_norm_sq_eq
    (derivative point frameIndex)).symm

/-- Polynomial extension of the raw LL density to the strong C⁰ first-jet packet. -/
def regularGeneralMetricC0LLDensity
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (packet : GlobalMinimalPhysicalLLC0FirstJetSinglePacket period hPeriod frame) :
    C(EffectiveThroat period hPeriod, Real) :=
  ContinuousMap.const (EffectiveThroat period hPeriod) (1 / 2 : Real) *
      (((1 : C(EffectiveThroat period hPeriod, Real)) +
        continuousEuclideanNormSq period hPeriod
          (Index := Fin 3 × Fin 3) packet.1) *
        continuousLLDerivativeEnergy period hPeriod frame packet.2.2.2) +
    packet.2.1 * continuousEuclideanNormSq period hPeriod
      (Index := Fin 4) packet.2.2.1

theorem regularGeneralMetricC0LLDensity_contDiff
    (frame : SmoothThroatGeneratingFrame period hPeriod) :
    ContDiff Real ∞ (regularGeneralMetricC0LLDensity period hPeriod frame) := by
  let Packet := GlobalMinimalPhysicalLLC0FirstJetSinglePacket period hPeriod frame
  have hHalf : ContDiff Real ∞ (fun _ : Packet =>
      ContinuousMap.const (EffectiveThroat period hPeriod) (1 / 2 : Real)) :=
    contDiff_const
  have hOne : ContDiff Real ∞ (fun _ : Packet =>
      (1 : C(EffectiveThroat period hPeriod, Real))) := contDiff_const
  have hAux : ContDiff Real ∞ (fun packet : Packet =>
      continuousEuclideanNormSq period hPeriod
        (Index := Fin 3 × Fin 3) packet.1) :=
    (continuousEuclideanNormSq_contDiff period hPeriod
      (Index := Fin 3 × Fin 3)).comp contDiff_fst
  have hDerivative : ContDiff Real ∞ (fun packet : Packet =>
      continuousLLDerivativeEnergy period hPeriod frame packet.2.2.2) :=
    (continuousLLDerivativeEnergy_contDiff period hPeriod frame).comp
      (contDiff_snd.snd.snd)
  have hMeasure : ContDiff Real ∞ (fun packet : Packet => packet.2.1) :=
    contDiff_snd.fst
  have hField : ContDiff Real ∞ (fun packet : Packet =>
      continuousEuclideanNormSq period hPeriod
        (Index := Fin 4) packet.2.2.1) :=
    (continuousEuclideanNormSq_contDiff period hPeriod
      (Index := Fin 4)).comp (contDiff_snd.snd.fst)
  unfold regularGeneralMetricC0LLDensity
  exact (hHalf.mul ((hOne.add hAux).mul hDerivative)).add
    (hMeasure.mul hField)

/-- Continuous integration on the compact throat. -/
def continuousThroatIntegralCLM
    (measure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure measure] :
    C(EffectiveThroat period hPeriod, Real) →L[Real] Real :=
  (L1.integralCLM
      (α := EffectiveThroat period hPeriod)
      (E := Real) (μ := measure)).comp
      (ContinuousMap.toLp (1 : ENNReal) measure Real)

theorem continuousThroatIntegralCLM_apply
    (measure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure measure]
    (field : C(EffectiveThroat period hPeriod, Real)) :
    continuousThroatIntegralCLM period hPeriod measure field =
      ∫ point, field point ∂measure := by
  unfold continuousThroatIntegralCLM
  rw [ContinuousLinearMap.comp_apply, ← L1.integral_eq,
    L1.integral_eq_integral]
  exact integral_congr_ae
    (ContinuousMap.coeFn_toLp (p := (1 : ENNReal))
      (𝕜 := Real) measure field)

/-- Raw LL action on one continuous first-jet packet. -/
def regularGeneralMetricC0LLRawAction
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (measure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure measure]
    (packet : GlobalMinimalPhysicalLLC0FirstJetSinglePacket period hPeriod frame) :
    Real :=
  continuousThroatIntegralCLM period hPeriod measure
    (regularGeneralMetricC0LLDensity period hPeriod frame packet)

theorem regularGeneralMetricC0LLRawAction_contDiff
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (measure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure measure] :
    ContDiff Real ∞
      (regularGeneralMetricC0LLRawAction period hPeriod frame measure) :=
  (continuousThroatIntegralCLM period hPeriod measure).contDiff.comp
    (regularGeneralMetricC0LLDensity_contDiff period hPeriod frame)

/-- On smooth first jets, the polynomial density is the original LL density. -/
theorem regularGeneralMetricC0LLDensity_smooth_apply
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    regularGeneralMetricC0LLDensity period hPeriod frame
        (smoothLLCoefficientC0FirstJetLinearMap period hPeriod frame
          (fields.llAuxMetric, (fields.llMeasure, fields.llField))) point =
      differentialLLDensity period hPeriod frame fields point := by
  simp [regularGeneralMetricC0LLDensity,
    smoothLLCoefficientC0FirstJetLinearMap,
    smoothThroatFieldToContinuousLinearMap,
    smoothLLFieldC0FirstJetLinearMap,
    differentialLLDensity, llAuxiliaryKineticWeight,
    throatDerivativeEnergy, llWorldvolumeDensity, llFlux]
  ring

/-- The raw packet action exactly recovers the original smooth LL action. -/
theorem regularGeneralMetricC0LLRawAction_smooth
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (measure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure measure]
    (fields : IndependentFields period hPeriod) :
    regularGeneralMetricC0LLRawAction period hPeriod frame measure
        (smoothLLCoefficientC0FirstJetLinearMap period hPeriod frame
          (fields.llAuxMetric, (fields.llMeasure, fields.llField))) =
      globalDifferentialLLAction period hPeriod frame fields measure := by
  unfold regularGeneralMetricC0LLRawAction globalDifferentialLLAction
  rw [continuousThroatIntegralCLM_apply]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun point =>
    regularGeneralMetricC0LLDensity_smooth_apply period hPeriod frame fields point

/-- The averaged polynomial action on the direct and PT first-jet packets. -/
def regularGeneralMetricC0LLPTAction
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (measure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure measure]
    (packet : GlobalMinimalPhysicalLLC0FirstJetPacket period hPeriod frame) : Real :=
  (1 / 2 : Real) *
    (regularGeneralMetricC0LLRawAction period hPeriod frame measure packet.1 +
      regularGeneralMetricC0LLRawAction period hPeriod frame measure packet.2)

theorem regularGeneralMetricC0LLPTAction_contDiff
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (measure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure measure] :
    ContDiff Real ∞
      (regularGeneralMetricC0LLPTAction period hPeriod frame measure) := by
  unfold regularGeneralMetricC0LLPTAction
  exact contDiff_const.mul
    (((regularGeneralMetricC0LLRawAction_contDiff period hPeriod frame measure).comp
      contDiff_fst).add
      ((regularGeneralMetricC0LLRawAction_contDiff period hPeriod frame measure).comp
        contDiff_snd))

/-- On smooth LL coefficients, the packet average is the genuine PT action. -/
theorem regularGeneralMetricC0LLPTAction_smooth
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (measure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure measure]
    (fields : IndependentFields period hPeriod) :
    regularGeneralMetricC0LLPTAction period hPeriod frame measure
        (smoothLLCoefficientPTC0FirstJetLinearMap period hPeriod frame
          (fields.llAuxMetric, (fields.llMeasure, fields.llField))) =
      globalPTSymmetricDifferentialLLAction period hPeriod frame fields measure := by
  have hDirect := regularGeneralMetricC0LLRawAction_smooth period hPeriod frame
    measure fields
  have hPT := regularGeneralMetricC0LLRawAction_smooth period hPeriod frame
    measure (llPTPullback period hPeriod fields)
  simpa [regularGeneralMetricC0LLPTAction,
    smoothLLCoefficientPTC0FirstJetLinearMap,
    smoothLLCoefficientPTLinearMap, throatPTPullbackLinearMap, llPTPullback,
    globalPTSymmetricDifferentialLLAction] using congrArg₂
      (fun direct pt : Real => (1 / 2 : Real) * (direct + pt)) hDirect hPT

local instance canonicalThroatMeasureIsFinite :
    IsFiniteMeasure (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod

/-- The actual translated LL fields of one minimal-physical direction. -/
def regularGeneralMetricC2PairedMinimalPhysicalLLFieldsInput
    (configuration : GlobalFieldConfiguration period hPeriod)
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod configuration) :
    IndependentFields period hPeriod :=
  { diagonalScaffold period hPeriod configuration.coefficientFields with
    llAuxMetric := configuration.coefficientFields.llAuxMetric +
      direction.1.completeVariation.independent.llAuxMetric
    llMeasure := configuration.coefficientFields.llMeasure +
      direction.1.completeVariation.independent.llMeasure
    llField := configuration.coefficientFields.llField +
      direction.1.completeVariation.independent.llField }

/-- Direct/PT first jets of the genuinely translated LL fields. -/
def regularGeneralMetricC2PairedMinimalPhysicalLLPacketInput
    (configuration : GlobalFieldConfiguration period hPeriod)
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod configuration) :
    GlobalMinimalPhysicalLLC0FirstJetPacket period hPeriod frame :=
  let fields := regularGeneralMetricC2PairedMinimalPhysicalLLFieldsInput
    period hPeriod configuration direction
  smoothLLCoefficientPTC0FirstJetLinearMap period hPeriod frame
    (fields.llAuxMetric, (fields.llMeasure, fields.llField))

theorem regularGeneralMetricC2PairedMinimalPhysicalLLPacketInput_eq_affine
    (configuration : GlobalFieldConfiguration period hPeriod)
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod configuration) :
    regularGeneralMetricC2PairedMinimalPhysicalLLPacketInput period hPeriod
        configuration frame direction =
      smoothLLCoefficientPTC0FirstJetLinearMap period hPeriod frame
          (configuration.coefficientFields.llAuxMetric,
            (configuration.coefficientFields.llMeasure,
              configuration.coefficientFields.llField)) +
        globalMinimalPhysicalLLC0FirstJetLinearMap period hPeriod configuration
          frame direction := by
  simpa [regularGeneralMetricC2PairedMinimalPhysicalLLPacketInput,
    regularGeneralMetricC2PairedMinimalPhysicalLLFieldsInput,
    globalMinimalPhysicalLLC0FirstJetLinearMap,
    globalMinimalPhysicalLLSmoothCoefficientLinearMap] using
      (smoothLLCoefficientPTC0FirstJetLinearMap period hPeriod frame).map_add
        (configuration.coefficientFields.llAuxMetric,
          (configuration.coefficientFields.llMeasure,
            configuration.coefficientFields.llField))
        (direction.1.completeVariation.independent.llAuxMetric,
          (direction.1.completeVariation.independent.llMeasure,
            direction.1.completeVariation.independent.llField))

/-- The exact translated LL action in the canonical throat geometry. -/
def regularGeneralMetricC2PairedMinimalPhysicalLLAction
    (configuration : GlobalFieldConfiguration period hPeriod)
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod configuration) :
    Real :=
  regularGeneralMetricC0LLPTAction period hPeriod
    (canonicalDivergenceFreeLLFrame period hPeriod)
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
    (regularGeneralMetricC2PairedMinimalPhysicalLLPacketInput period hPeriod
      configuration (canonicalDivergenceFreeLLFrame period hPeriod) direction)

theorem regularGeneralMetricC2PairedMinimalPhysicalLLAction_contDiff
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (plusBase minusBase :
      P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D.RegularGeneralLorentzMetric
        period hPeriod) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    ContDiff Real ∞
      (regularGeneralMetricC2PairedMinimalPhysicalLLAction period hPeriod
        configuration.physical) := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  let frame := canonicalDivergenceFreeLLFrame period hPeriod
  have hInput : ContDiff Real ∞
      (regularGeneralMetricC2PairedMinimalPhysicalLLPacketInput period hPeriod
        configuration.physical frame) := by
    rw [funext (regularGeneralMetricC2PairedMinimalPhysicalLLPacketInput_eq_affine
      period hPeriod configuration.physical frame)]
    exact contDiff_const.add
      (globalMinimalPhysicalPairedLLC0FirstJetCLM period hPeriod configuration
        data analysis realization plusBase minusBase frame).contDiff
  exact (regularGeneralMetricC0LLPTAction_contDiff period hPeriod frame
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod)).comp hInput

theorem regularGeneralMetricC2PairedMinimalPhysicalLLAction_eq_physical
    (configuration : GlobalFieldConfiguration period hPeriod)
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod configuration) :
    regularGeneralMetricC2PairedMinimalPhysicalLLAction period hPeriod
        configuration direction =
      globalPTSymmetricDifferentialLLAction period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod)
        (regularGeneralMetricC2PairedMinimalPhysicalLLFieldsInput period hPeriod
          configuration direction)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  unfold regularGeneralMetricC2PairedMinimalPhysicalLLAction
    regularGeneralMetricC2PairedMinimalPhysicalLLPacketInput
  exact regularGeneralMetricC0LLPTAction_smooth period hPeriod
    (canonicalDivergenceFreeLLFrame period hPeriod)
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
    (regularGeneralMetricC2PairedMinimalPhysicalLLFieldsInput period hPeriod
      configuration direction)

set_option maxRecDepth 4000 in
/-- On the admissible paired domain, the actual LL block is the translated action. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_ll_eq
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod configuration)
    (hDirection : direction ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration plusBase minusBase) :
    (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
      period hPeriod configuration couplings data plusBase minusBase hBase
        measure).ll direction =
      regularGeneralMetricC2PairedMinimalPhysicalLLAction period hPeriod
        configuration direction := by
  let family :=
    regularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily
      period hPeriod configuration couplings data plusBase minusBase
  let hZero :=
    zero_mem_regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain
      period hPeriod configuration plusBase minusBase hBase
  have hDirection' : direction ∈ family.domain := hDirection
  change globalCandidateALLAction period hPeriod
      (family.datumAtTotal period hPeriod 0 hZero direction).2 = _
  rw [family.datumAtTotal_of_mem period hPeriod 0 hZero direction hDirection']
  rw [regularGeneralMetricC2PairedMinimalPhysicalLLAction_eq_physical]
  rfl

/-- The ninth genuine action block is C² within the exact paired domain. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_ll_contDiffWithinAt
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (point : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration.physical)
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    ContDiffWithinAt Real 2
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
        period hPeriod configuration.physical couplings data plusBase minusBase
          hBase measure).ll
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) point := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  have hAction : ContDiff Real 2
      (regularGeneralMetricC2PairedMinimalPhysicalLLAction period hPeriod
        configuration.physical) :=
    (regularGeneralMetricC2PairedMinimalPhysicalLLAction_contDiff period hPeriod
      configuration data analysis realization plusBase minusBase).of_le
        (show (2 : ℕ∞) ≤ ∞ by
          exact WithTop.coe_le_coe.mpr le_top)
  exact hAction.contDiffWithinAt.congr_of_mem
    (fun direction hDirection =>
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_ll_eq
        period hPeriod configuration.physical data plusBase minusBase hBase
          measure direction hDirection)
    hPoint

/-- Gate marker: the authentic nonlinear LL block is C² in the strong chart. -/
theorem regular_general_metric_c2_paired_minimal_physical_LL_c2_gate
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (point : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration.physical)
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    ContDiffWithinAt Real 2
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
        period hPeriod configuration.physical couplings data plusBase minusBase
          hBase measure).ll
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) point :=
  regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_ll_contDiffWithinAt
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase measure point hPoint

end
end P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC24D
end JanusFormal
