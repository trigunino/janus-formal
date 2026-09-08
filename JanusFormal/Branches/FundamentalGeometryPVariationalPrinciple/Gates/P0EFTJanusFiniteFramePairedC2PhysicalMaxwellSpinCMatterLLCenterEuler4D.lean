import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D

/-! # Genuine LL augmentation at the finite physical center -/

namespace JanusFormal
namespace P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCenterEuler4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 600000
noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusGlobalGeneralMetricDeDonder4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalBoundaryCompletion4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDensity4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterRegularity4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartGeometry4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalRelativeMetricCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomainOpen4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC24D
open P0EFTJanusFiniteFramePairedC2PhysicalAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterCenterEuler4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D
open P0EFTJanusFiniteFrameRegularC2RootDerivativeSylvesterBridge4D
open P0EFTJanusFiniteFrameRegularC2PhysicalMetricResidualBridge4D
open P0EFTJanusFiniteFrameRegularC2PhysicalDiffeomorphismDeDonderResidual4D
open P0EFTJanusPairedInteractionSmoothMetricResidual4D
open P0EFTJanusReciprocalBimetricPotential

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance : IsManifold coverModelWithCorners ω
    (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance : IsManifold throatCoverModelWithCorners ω
    (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance : CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance : BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

local instance :
    IsFiniteMeasure (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod

local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup

local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance

local instance : CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

local instance : InnerProductSpace Real ProgramPPrimitiveSpinCMatterHilbert :=
  InnerProductSpace.complexToReal

attribute [local instance 2000]
  NonUnitalNormedRing.toNormedAddCommGroup NormedAlgebra.toNormedSpace

section LLDerivativeCenter

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

section LLPolynomialCenter

variable {Index : Type*} [Fintype Index]

/-- The coordinate polynomial defining the Euclidean norm square has no
linear part at the origin. -/
theorem continuousEuclideanNormSq_hasFDerivAt_zero :
    HasFDerivAt
      (continuousEuclideanNormSq period hPeriod (Index := Index))
      (0 : C(EffectiveThroat period hPeriod, EuclideanSpace Real Index) →L[Real]
        C(EffectiveThroat period hPeriod, Real)) 0 := by
  let Source := C(EffectiveThroat period hPeriod, EuclideanSpace Real Index)
  let Target := C(EffectiveThroat period hPeriod, Real)
  let action := continuousEuclideanNormSq period hPeriod (Index := Index)
  let derivative := fderiv Real action (0 : Source)
  have hAction : HasFDerivAt action derivative 0 :=
    ((continuousEuclideanNormSq_contDiff period hPeriod (Index := Index)).differentiable
      (by simp)).differentiableAt.hasFDerivAt
  have hNegMap : HasFDerivAt (fun field : Source => -field)
      (-(ContinuousLinearMap.id Real Source)) 0 :=
    (hasFDerivAt_id (0 : Source)).neg
  have hAtNeg : HasFDerivAt action derivative (-(0 : Source)) := by
    simpa using hAction
  have hNeg := hAtNeg.comp (0 : Source) hNegMap
  have hEven : (fun field : Source => action (-field)) = action := by
    funext field
    apply ContinuousMap.ext
    intro point
    change continuousEuclideanNormSq period hPeriod (-field) point =
      continuousEuclideanNormSq period hPeriod field point
    rw [continuousEuclideanNormSq_apply, continuousEuclideanNormSq_apply]
    change ‖-(field point)‖ ^ 2 = ‖field point‖ ^ 2
    rw [norm_neg]
  change HasFDerivAt (fun field : Source => action (-field)) _ 0 at hNeg
  rw [hEven] at hNeg
  have hDerivative : derivative = 0 := by
    apply ContinuousLinearMap.ext
    intro field
    have hValue := DFunLike.congr_fun (hNeg.unique hAction) field
    change derivative (-field) = derivative field at hValue
    rw [map_neg] at hValue
    apply ContinuousMap.ext
    intro point
    have hPoint := congrArg (fun value : Target => value point) hValue
    change -(derivative field point) = derivative field point at hPoint
    have hZero : derivative field point = 0 := by linarith
    simpa using hZero
  simpa [action, derivative, hDerivative] using hAction

end LLPolynomialCenter

/-- The polynomial energy of the stored LL derivative has no linear part at
the origin. -/
theorem continuousLLDerivativeEnergy_hasFDerivAt_zero
    (frame : SmoothThroatGeneratingFrame period hPeriod) :
    HasFDerivAt
      (continuousLLDerivativeEnergy period hPeriod frame)
      (0 : C(EffectiveThroat period hPeriod, Fin frame.count → LLFieldFiber) →L[Real]
        C(EffectiveThroat period hPeriod, Real)) 0 := by
  let Source := C(EffectiveThroat period hPeriod, Fin frame.count → LLFieldFiber)
  let Target := C(EffectiveThroat period hPeriod, Real)
  let action := continuousLLDerivativeEnergy period hPeriod frame
  let derivative := fderiv Real action (0 : Source)
  have hAction : HasFDerivAt action derivative 0 :=
    ((continuousLLDerivativeEnergy_contDiff period hPeriod frame).differentiable
      (by simp)).differentiableAt.hasFDerivAt
  have hNegMap : HasFDerivAt (fun field : Source => -field)
      (-(ContinuousLinearMap.id Real Source)) 0 :=
    (hasFDerivAt_id (0 : Source)).neg
  have hAtNeg : HasFDerivAt action derivative (-(0 : Source)) := by
    simpa using hAction
  have hNeg := hAtNeg.comp (0 : Source) hNegMap
  have hEven : (fun field : Source => action (-field)) = action := by
    funext field
    apply ContinuousMap.ext
    intro point
    change continuousLLDerivativeEnergy period hPeriod frame (-field) point =
      continuousLLDerivativeEnergy period hPeriod frame field point
    rw [continuousLLDerivativeEnergy_apply, continuousLLDerivativeEnergy_apply]
    apply Finset.sum_congr rfl
    intro frameIndex _
    change ‖-(field point frameIndex)‖ ^ 2 = ‖field point frameIndex‖ ^ 2
    rw [norm_neg]
  change HasFDerivAt (fun field : Source => action (-field)) _ 0 at hNeg
  rw [hEven] at hNeg
  have hDerivative : derivative = 0 := by
    apply ContinuousLinearMap.ext
    intro field
    have hValue := DFunLike.congr_fun (hNeg.unique hAction) field
    change derivative (-field) = derivative field at hValue
    rw [map_neg] at hValue
    apply ContinuousMap.ext
    intro point
    have hPoint := congrArg (fun value : Target => value point) hValue
    change -(derivative field point) = derivative field point at hPoint
    have hZero : derivative field point = 0 := by linarith
    simpa using hZero
  simpa [action, derivative, hDerivative] using hAction

attribute [local instance 100] NormedAlgebra.toNormedSpace

/-- Every monomial of the raw LL density has degree at least two at the zero
first-jet packet. -/
theorem regularGeneralMetricC0LLDensity_hasFDerivAt_zero
    (frame : SmoothThroatGeneratingFrame period hPeriod) :
    HasFDerivAt
      (regularGeneralMetricC0LLDensity period hPeriod frame)
      (0 : GlobalMinimalPhysicalLLC0FirstJetSinglePacket period hPeriod frame →L[Real]
        C(EffectiveThroat period hPeriod, Real)) 0 := by
  let Packet := GlobalMinimalPhysicalLLC0FirstJetSinglePacket period hPeriod frame
  let Target := C(EffectiveThroat period hPeriod, Real)
  have hAuxProjection : DifferentiableAt Real
      (fun packet : GlobalMinimalPhysicalLLC0FirstJetSinglePacket period hPeriod frame =>
        packet.1) 0 := by
    fun_prop
  have hAux : HasFDerivAt
      (fun packet : Packet => continuousEuclideanNormSq period hPeriod
        (Index := Fin 3 × Fin 3) packet.1)
      (0 : Packet →L[Real] Target) (0 : Packet) := by
    convert
      (continuousEuclideanNormSq_hasFDerivAt_zero period hPeriod
        (Index := Fin 3 × Fin 3)).comp (0 : Packet) hAuxProjection.hasFDerivAt using 1 <;>
      simp [Function.comp_def]
  have hDerivativeProjection : DifferentiableAt Real
      (fun packet : GlobalMinimalPhysicalLLC0FirstJetSinglePacket period hPeriod frame =>
        packet.2.2.2) 0 := by
    fun_prop
  have hDerivative : HasFDerivAt
      (fun packet : Packet => continuousLLDerivativeEnergy period hPeriod frame
        packet.2.2.2) (0 : Packet →L[Real] Target) (0 : Packet) := by
    convert
      (continuousLLDerivativeEnergy_hasFDerivAt_zero period hPeriod frame).comp
        (0 : Packet) hDerivativeProjection.hasFDerivAt using 1 <;>
      simp [Function.comp_def]
  have hMeasure : DifferentiableAt Real (fun packet : Packet => packet.2.1) 0 := by
    fun_prop
  have hFieldProjection : DifferentiableAt Real
      (fun packet : GlobalMinimalPhysicalLLC0FirstJetSinglePacket period hPeriod frame =>
        packet.2.2.1) 0 := by
    fun_prop
  have hField : HasFDerivAt
      (fun packet : Packet => continuousEuclideanNormSq period hPeriod
        (Index := Fin 4) packet.2.2.1)
      (0 : Packet →L[Real] Target) (0 : Packet) := by
    convert
      (continuousEuclideanNormSq_hasFDerivAt_zero period hPeriod
        (Index := Fin 4)).comp (0 : Packet) hFieldProjection.hasFDerivAt using 1 <;>
      simp [Function.comp_def]
  have hDensity :=
    (((hAux.const_add (1 : Target)).mul hDerivative).const_mul
      (ContinuousMap.const (EffectiveThroat period hPeriod) (1 / 2 : Real))).add
        (hMeasure.hasFDerivAt.mul hField)
  change HasFDerivAt
    (fun packet : Packet =>
      ContinuousMap.const (EffectiveThroat period hPeriod) (1 / 2 : Real) *
          (((1 : Target) + continuousEuclideanNormSq period hPeriod
            (Index := Fin 3 × Fin 3) packet.1) *
            continuousLLDerivativeEnergy period hPeriod frame packet.2.2.2) +
        packet.2.1 * continuousEuclideanNormSq period hPeriod
          (Index := Fin 4) packet.2.2.1) 0 0
  change HasFDerivAt
    (fun packet : Packet =>
      ContinuousMap.const (EffectiveThroat period hPeriod) (1 / 2 : Real) *
          (((1 : Target) + continuousEuclideanNormSq period hPeriod
            (Index := Fin 3 × Fin 3) packet.1) *
            continuousLLDerivativeEnergy period hPeriod frame packet.2.2.2) +
        packet.2.1 * continuousEuclideanNormSq period hPeriod
          (Index := Fin 4) packet.2.2.1) _ 0 at hDensity
  simpa [continuousEuclideanNormSq] using hDensity

attribute [local instance 2000] NormedAlgebra.toNormedSpace

/-- Continuous integration preserves the vanishing linear part of the raw LL
density. -/
theorem regularGeneralMetricC0LLRawAction_hasFDerivAt_zero
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (measure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure measure] :
    HasFDerivAt
      (regularGeneralMetricC0LLRawAction period hPeriod frame measure)
      (0 : GlobalMinimalPhysicalLLC0FirstJetSinglePacket period hPeriod frame →L[Real]
        Real) 0 := by
  have hIntegral : HasFDerivAt
      (continuousThroatIntegralCLM period hPeriod measure)
      (continuousThroatIntegralCLM period hPeriod measure)
      (regularGeneralMetricC0LLDensity period hPeriod frame 0) :=
    (continuousThroatIntegralCLM period hPeriod measure).hasFDerivAt
  change HasFDerivAt
    (fun packet : GlobalMinimalPhysicalLLC0FirstJetSinglePacket period hPeriod frame =>
      continuousThroatIntegralCLM period hPeriod measure
        (regularGeneralMetricC0LLDensity period hPeriod frame packet)) 0 0
  simpa [Function.comp_def] using
    hIntegral.comp
      (0 : GlobalMinimalPhysicalLLC0FirstJetSinglePacket period hPeriod frame)
      (regularGeneralMetricC0LLDensity_hasFDerivAt_zero period hPeriod frame)

/-- The averaged direct/PT LL action has zero first derivative at the zero
packet. -/
theorem regularGeneralMetricC0LLPTAction_hasFDerivAt_zero
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (measure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure measure] :
    HasFDerivAt
      (regularGeneralMetricC0LLPTAction period hPeriod frame measure)
      (0 : GlobalMinimalPhysicalLLC0FirstJetPacket period hPeriod frame →L[Real] Real)
      0 := by
  let Packet := GlobalMinimalPhysicalLLC0FirstJetPacket period hPeriod frame
  have hRaw := regularGeneralMetricC0LLRawAction_hasFDerivAt_zero period hPeriod
    frame measure
  have hDirect := hRaw.comp (0 : Packet) (hasFDerivAt_fst (𝕜 := Real))
  have hPT := hRaw.comp (0 : Packet) (hasFDerivAt_snd (𝕜 := Real))
  have hSum : HasFDerivAt
      (fun packet : Packet =>
        regularGeneralMetricC0LLRawAction period hPeriod frame measure packet.1 +
          regularGeneralMetricC0LLRawAction period hPeriod frame measure packet.2)
      (0 : Packet →L[Real] Real) 0 := by
    convert hDirect.add hPT using 1
    · funext packet
      rfl
    · simp
  change HasFDerivAt
    (fun packet : Packet => (1 / 2 : Real) *
      (regularGeneralMetricC0LLRawAction period hPeriod frame measure packet.1 +
        regularGeneralMetricC0LLRawAction period hPeriod frame measure packet.2)) 0 0
  simpa [Packet] using
    hSum.const_mul (1 / 2 : Real)

end LLDerivativeCenter

attribute [local instance 100]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

/-- Explicit zero value of the LL first variation used by the finite product
Euler. -/
@[simp]
theorem regularGeneralMetricC0LLPTAction_fderiv_zero
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (measure : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure measure] :
    fderiv Real (regularGeneralMetricC0LLPTAction period hPeriod frame measure) 0 = 0 :=
  (regularGeneralMetricC0LLPTAction_hasFDerivAt_zero period hPeriod frame measure).fderiv

variable (geometry : GlobalCandidateAGeometry period hPeriod)
  (frame : SmoothD8Frame period hPeriod)
  (hRegular : ∀ point, Function.Bijective
    (intrinsicCandidateASylvesterAt period hPeriod geometry point))
  (couplings : GlobalCandidateAActionCouplings)

local notation "OldInput" =>
  FiniteFramePairedC2PhysicalMaxwellSpinCMatterCore period hPeriod geometry frame couplings

local notation "LLInput" =>
  GlobalMinimalPhysicalLLC0FirstJetPacket period hPeriod
    (canonicalDivergenceFreeLLFrame period hPeriod)

local instance : NormedSpace Real OldInput := Prod.normedSpace

local instance : NormedSpace Real LLInput := Prod.normedSpace

local instance : ContinuousSMul Real LLInput := by
  apply Prod.continuousSMul

local notation "Input" =>
  FiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCore period hPeriod geometry frame couplings

local instance : NormedSpace Real Input := Prod.normedSpace

local instance : ContinuousSMul Real Input := by
  apply Prod.continuousSMul

/-- At every admissible point, the product Euler is the old
physical/Maxwell/SpinC Euler plus the LL first derivative. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLEuler_eq_old_add_ll
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLDomain period hPeriod geometry
        frame hRegular couplings) :
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLEuler period hPeriod geometry frame
        hRegular couplings interactionScale coefficients input =
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterEuler period hPeriod geometry frame
        hRegular couplings interactionScale coefficients input.1).comp
          (ContinuousLinearMap.fst Real OldInput LLInput) +
        (fderiv Real
          (regularGeneralMetricC0LLPTAction period hPeriod
            (canonicalDivergenceFreeLLFrame period hPeriod)
            (intrinsicCanonicalThroatVolumeMeasure period hPeriod)) input.2).comp
          (ContinuousLinearMap.snd Real OldInput LLInput) := by
  have hFst : HasFDerivAt (fun current : Input => current.1)
      (ContinuousLinearMap.fst Real OldInput LLInput) input := by
    fun_prop
  have hSnd : HasFDerivAt (fun current : Input => current.2)
      (ContinuousLinearMap.snd Real OldInput LLInput) input := by
    fun_prop
  have hOld :=
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterAction_hasFDerivAt period hPeriod
      geometry frame hRegular couplings interactionScale coefficients input.1
        hInput.1).comp input hFst
  have hLLBase : HasFDerivAt
      (regularGeneralMetricC0LLPTAction period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod))
      (fderiv Real
        (regularGeneralMetricC0LLPTAction period hPeriod
          (canonicalDivergenceFreeLLFrame period hPeriod)
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod)) input.2) input.2 :=
    ((regularGeneralMetricC0LLPTAction_contDiff period hPeriod
      (canonicalDivergenceFreeLLFrame period hPeriod)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod)).differentiable
        (by simp) input.2).hasFDerivAt
  have hLL := hLLBase.comp input hSnd
  exact (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLAction_hasFDerivAt period
    hPeriod geometry frame hRegular couplings interactionScale coefficients input
      hInput).unique (hOld.add hLL)

/-- At the zero LL packet, the enlarged Euler is the prior Euler extended by
the first projection. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLEuler_zero_eq_maxwellSpinCMatter
    (hMinusCenter : finiteFramePairedC2MinusCenter period hPeriod geometry frame ∈
      generalMetricRelativeC2VolumeDomain period hPeriod frame geometry.plusMetric)
    (interactionScale : Real) (coefficients : PotentialCoefficients) :
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLEuler period hPeriod geometry frame
        hRegular couplings interactionScale coefficients 0 =
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterEuler period hPeriod geometry frame
        hRegular couplings interactionScale coefficients 0).comp
          (ContinuousLinearMap.fst Real OldInput LLInput) := by
  have hCenter :=
    zero_mem_finiteFramePairedC2PhysicalMaxwellSpinCMatterLLDomain period hPeriod
      geometry frame hRegular couplings hMinusCenter
  rw [finiteFramePairedC2PhysicalMaxwellSpinCMatterLLEuler_eq_old_add_ll period hPeriod
    geometry frame hRegular couplings interactionScale coefficients 0 hCenter]
  simp

/-- Adding a zero LL packet preserves physical/Maxwell/SpinC stationarity. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLEuler_zero_iff_maxwellSpinCMatter
    (hMinusCenter : finiteFramePairedC2MinusCenter period hPeriod geometry frame ∈
      generalMetricRelativeC2VolumeDomain period hPeriod frame geometry.plusMetric)
    (interactionScale : Real) (coefficients : PotentialCoefficients) :
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLEuler period hPeriod geometry frame
        hRegular couplings interactionScale coefficients 0 = 0 ↔
      finiteFramePairedC2PhysicalMaxwellSpinCMatterEuler period hPeriod geometry frame
        hRegular couplings interactionScale coefficients 0 = 0 := by
  rw [finiteFramePairedC2PhysicalMaxwellSpinCMatterLLEuler_zero_eq_maxwellSpinCMatter
    period hPeriod geometry frame hRegular couplings hMinusCenter interactionScale
      coefficients]
  constructor
  · intro hComposite
    apply ContinuousLinearMap.ext
    intro direction
    have hValue := congrArg
      (fun derivative : Input →L[Real] Real =>
        derivative (direction, (0 : LLInput))) hComposite
    simpa using hValue
  · intro hOld
    simp [hOld]

/-- Adding the zero LL packet preserves the complete finite center criterion:
mobile metric residual plus global De Donder. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLEuler_zero_iff_residual_and_globalDeDonder
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hPlusCanonicalVolume : plusBase.volume =
      globalSmoothMetricVolumeRatio period hPeriod plusBase.metric)
    (hMinusCanonicalVolume : minusBase.volume =
      globalSmoothMetricVolumeRatio period hPeriod minusBase.metric)
    (hChart : regularGeneralMetricSmoothC2Variation period hPeriod plusBase
        (minusBase.metric.tensor - plusBase.metric.tensor) ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod plusBase)
    (frame : SmoothD8Frame period hPeriod)
    (hShift : smoothToGeneralMetricRelativeC2Core period hPeriod frame plusBase.metric
        (minusBase.metric.tensor - plusBase.metric.tensor) ∈
      generalMetricRelativeC2VolumeDomain period hPeriod frame plusBase.metric)
    (hZero : (0 : RegularGeneralMetricC2PairedRelativeCore period hPeriod plusBase minusBase) ∈
      regularGeneralMetricC2PairedLorentzMatrixDomain period hPeriod plusBase minusBase)
    (couplings : GlobalCandidateAActionCouplings)
    (interactionScale : Real) (coefficients : PotentialCoefficients) :
    let geometry := regularGeneralMetricC2LorentzChartGeometry period hPeriod plusBase
      (minusBase.metric.tensor - plusBase.metric.tensor) hChart
    let hFiniteRegular :=
      regularGeneralMetricC2LorentzChartGeometry_intrinsicSylvester_bijective period hPeriod
        plusBase (minusBase.metric.tensor - plusBase.metric.tensor) hChart
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLEuler period hPeriod geometry frame
        hFiniteRegular couplings interactionScale coefficients 0 = 0 ↔
      regularFramePairedMobileEinsteinHilbertInteractionResidual period hPeriod
          plusBase minusBase
          (pairedInteractionCenter_rootAdmissible period hPeriod plusBase minusBase hZero)
          couplings interactionScale coefficients = 0 ∧
        globalGeneralMetricDeDonderLinearMap period hPeriod minusBase.metric
          (minusBase.metric.tensor - plusBase.metric.tensor) = 0 := by
  dsimp only
  let geometry := regularGeneralMetricC2LorentzChartGeometry period hPeriod plusBase
    (minusBase.metric.tensor - plusBase.metric.tensor) hChart
  let hFiniteRegular :=
    regularGeneralMetricC2LorentzChartGeometry_intrinsicSylvester_bijective period hPeriod
      plusBase (minusBase.metric.tensor - plusBase.metric.tensor) hChart
  have hGeometryMinusTensor : geometry.minusMetric.tensor = minusBase.metric.tensor := by
    dsimp only [geometry]
    rw [regularGeneralMetricC2LorentzChartGeometry_minusMetric,
      regularGeneralMetricC2LorentzChartMetric_tensor]
    abel
  have hCenter : finiteFramePairedC2MinusCenter period hPeriod geometry frame =
      smoothToGeneralMetricRelativeC2Core period hPeriod frame plusBase.metric
        (minusBase.metric.tensor - plusBase.metric.tensor) := by
    unfold finiteFramePairedC2MinusCenter
    change smoothToGeneralMetricRelativeC2Core period hPeriod frame plusBase.metric
      (geometry.minusMetric.tensor - plusBase.metric.tensor) = _
    rw [hGeometryMinusTensor]
  have hMinusCenter : finiteFramePairedC2MinusCenter period hPeriod geometry frame ∈
      generalMetricRelativeC2VolumeDomain period hPeriod frame geometry.plusMetric := by
    rw [hCenter]
    exact hShift
  rw [finiteFramePairedC2PhysicalMaxwellSpinCMatterLLEuler_zero_iff_maxwellSpinCMatter
    period hPeriod geometry frame hFiniteRegular couplings hMinusCenter interactionScale
      coefficients]
  exact
    finiteFramePairedC2PhysicalMaxwellSpinCMatterEuler_zero_iff_residual_and_globalDeDonder
      period hPeriod plusBase minusBase hPlusCanonicalVolume hMinusCanonicalVolume hChart
        frame hShift hZero couplings interactionScale coefficients

end
end P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCenterEuler4D
end JanusFormal
