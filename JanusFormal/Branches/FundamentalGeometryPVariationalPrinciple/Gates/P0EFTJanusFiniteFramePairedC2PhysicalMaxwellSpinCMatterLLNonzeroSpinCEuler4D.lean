import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLFixedBoundaryAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMatterGraphMaximalSpectralResidual4D

/-! # Nonzero SpinC Euler equation in the fixed-boundary finite action -/

namespace JanusFormal
namespace P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLNonzeroSpinCEuler4D

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
open P0EFTJanusProgramPGlobalEulerLagrangeMatterGraphMaximalSpectralResidual4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartGeometry4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalRelativeMetricCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomainOpen4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC24D
open P0EFTJanusFiniteFramePairedC2PhysicalAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellCenterEuler4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterCenterEuler4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCenterEuler4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLFixedBoundaryAction4D
open P0EFTJanusFiniteFrameRegularC2RootDerivativeSylvesterBridge4D
open P0EFTJanusFiniteFrameRegularC2PhysicalMetricResidualBridge4D
open P0EFTJanusFiniteFrameRegularC2PhysicalDiffeomorphismDeDonderResidual4D
open P0EFTJanusPairedInteractionSmoothMetricResidual4D
open P0EFTJanusReciprocalBimetricPotential

attribute [local instance 2000]
  NonUnitalNormedRing.toNormedAddCommGroup NormedAlgebra.toNormedSpace

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

variable (geometry : GlobalCandidateAGeometry period hPeriod)
  (frame : SmoothD8Frame period hPeriod)
  (hRegular : ∀ point, Function.Bijective
    (intrinsicCandidateASylvesterAt period hPeriod geometry point))
  (couplings : GlobalCandidateAActionCouplings)

local notation "PhysicalInput" =>
  FiniteFramePairedC2PhysicalCore period hPeriod geometry frame

local notation "MatterInput" =>
  ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod couplings.matterMassSquared

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

/-- With a general SpinC graph state and zero LL packet, the fixed-boundary
Euler map is the sum of the Maxwell and SpinC Euler covectors. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLFixedBoundaryEuler_zeroLL_eq_maxwell_add_spinC
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (hMinusCenter : finiteFramePairedC2MinusCenter period hPeriod geometry frame ∈
      generalMetricRelativeC2VolumeDomain period hPeriod frame geometry.plusMetric)
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (matterState : MatterInput) :
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLFixedBoundaryEuler period hPeriod
        geometry frame hRegular couplings data interactionScale coefficients
        ((0, matterState), (0 : LLInput)) =
      ((finiteFramePairedC2PhysicalMaxwellEuler period hPeriod geometry frame hRegular
          couplings interactionScale coefficients 0).comp
          (ContinuousLinearMap.fst Real PhysicalInput MatterInput) +
        (programPPrimitiveSpinCMatterGraphForm period hPeriod couplings.matterMassSquared
          matterState).comp
          (ContinuousLinearMap.snd Real PhysicalInput MatterInput)).comp
        (ContinuousLinearMap.fst Real OldInput LLInput) := by
  have hOldInput : (0, matterState) ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterDomain period hPeriod geometry frame
        hRegular couplings :=
    ⟨zero_mem_finiteFramePairedC2PhysicalDomain period hPeriod geometry frame hRegular
      hMinusCenter, Set.mem_univ _⟩
  have hInput : ((0, matterState), (0 : LLInput)) ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLDomain period hPeriod geometry frame
        hRegular couplings :=
    ⟨hOldInput, Set.mem_univ _⟩
  rw [finiteFramePairedC2PhysicalMaxwellSpinCMatterLLFixedBoundaryEuler_eq_ll period
    hPeriod geometry frame hRegular couplings data interactionScale coefficients
      ((0, matterState), (0 : LLInput)) hInput]
  rw [finiteFramePairedC2PhysicalMaxwellSpinCMatterLLEuler_eq_old_add_ll period hPeriod
    geometry frame hRegular couplings interactionScale coefficients
      ((0, matterState), (0 : LLInput)) hInput]
  simp only [regularGeneralMetricC0LLPTAction_fderiv_zero,
    ContinuousLinearMap.zero_comp, add_zero]
  rw [finiteFramePairedC2PhysicalMaxwellSpinCMatterEuler_eq_maxwell_add_matter period
    hPeriod geometry frame hRegular couplings interactionScale coefficients
      (0, matterState) hOldInput]

/-- At a general SpinC graph state and zero LL packet, stationarity is exactly
Maxwell center stationarity plus the maximal SpinC spectral equation. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLFixedBoundaryEuler_zeroLL_iff_maxwell_and_spinCResidual
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (hMinusCenter : finiteFramePairedC2MinusCenter period hPeriod geometry frame ∈
      generalMetricRelativeC2VolumeDomain period hPeriod frame geometry.plusMetric)
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (matterState : MatterInput) :
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLFixedBoundaryEuler period hPeriod
        geometry frame hRegular couplings data interactionScale coefficients
        ((0, matterState), (0 : LLInput)) = 0 ↔
      finiteFramePairedC2PhysicalMaxwellEuler period hPeriod geometry frame hRegular
          couplings interactionScale coefficients 0 = 0 ∧
        programPPrimitiveSpinCMatterGraphMaximalSpectralResidual period hPeriod
          couplings.matterMassSquared matterState = 0 := by
  rw [finiteFramePairedC2PhysicalMaxwellSpinCMatterLLFixedBoundaryEuler_zeroLL_eq_maxwell_add_spinC
    period hPeriod geometry frame hRegular couplings data hMinusCenter interactionScale
      coefficients matterState]
  constructor
  · intro hEuler
    constructor
    · apply ContinuousLinearMap.ext
      intro direction
      have hValue := congrArg
        (fun derivative : Input →L[Real] Real =>
          derivative (((direction, (0 : MatterInput)), (0 : LLInput)))) hEuler
      simpa using hValue
    · apply
        (programPPrimitiveSpinCMatterGraphAction_fderiv_eq_zero_iff_maximalResidual
          period hPeriod couplings.matterMassSquared matterState).mp
      rw [programPPrimitiveSpinCMatterGraphAction_fderiv]
      apply ContinuousLinearMap.ext
      intro direction
      have hValue := congrArg
        (fun derivative : Input →L[Real] Real =>
          derivative ((((0 : PhysicalInput), direction), (0 : LLInput)))) hEuler
      simpa using hValue
  · rintro ⟨hMaxwell, hResidual⟩
    have hMatter : programPPrimitiveSpinCMatterGraphForm period hPeriod
        couplings.matterMassSquared matterState = 0 := by
      rw [← programPPrimitiveSpinCMatterGraphAction_fderiv]
      exact
        (programPPrimitiveSpinCMatterGraphAction_fderiv_eq_zero_iff_maximalResidual
          period hPeriod couplings.matterMassSquared matterState).mpr hResidual
    simp [hMaxwell, hMatter]

/-- The general SpinC criterion combines the mobile metric residual, global
De Donder condition and maximal SpinC spectral residual. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLFixedBoundaryEuler_zeroLL_iff_residuals_and_globalDeDonder
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
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (matterState : ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
      couplings.matterMassSquared) :
    let geometry := regularGeneralMetricC2LorentzChartGeometry period hPeriod plusBase
      (minusBase.metric.tensor - plusBase.metric.tensor) hChart
    let hFiniteRegular :=
      regularGeneralMetricC2LorentzChartGeometry_intrinsicSylvester_bijective period hPeriod
        plusBase (minusBase.metric.tensor - plusBase.metric.tensor) hChart
    let hRoot := pairedInteractionCenter_rootAdmissible period hPeriod plusBase minusBase hZero
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLFixedBoundaryEuler period hPeriod
        geometry frame hFiniteRegular couplings data interactionScale coefficients
        ((0, matterState),
          (0 : GlobalMinimalPhysicalLLC0FirstJetPacket period hPeriod
            (canonicalDivergenceFreeLLFrame period hPeriod))) = 0 ↔
      (regularFramePairedMobileEinsteinHilbertInteractionResidual period hPeriod
          plusBase minusBase hRoot couplings interactionScale coefficients = 0 ∧
        globalGeneralMetricDeDonderLinearMap period hPeriod minusBase.metric
          (minusBase.metric.tensor - plusBase.metric.tensor) = 0) ∧
        programPPrimitiveSpinCMatterGraphMaximalSpectralResidual period hPeriod
          couplings.matterMassSquared matterState = 0 := by
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
  rw [finiteFramePairedC2PhysicalMaxwellSpinCMatterLLFixedBoundaryEuler_zeroLL_iff_maxwell_and_spinCResidual
    period hPeriod geometry frame hFiniteRegular couplings data hMinusCenter
      interactionScale coefficients matterState]
  have hMaxwell :=
    finiteFramePairedC2PhysicalMaxwellEuler_zero_iff_residual_and_globalDeDonder
      period hPeriod plusBase minusBase hPlusCanonicalVolume hMinusCanonicalVolume hChart
        frame hShift hZero couplings interactionScale coefficients
  dsimp only at hMaxwell
  exact and_congr hMaxwell Iff.rfl

end
end P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLNonzeroSpinCEuler4D
end JanusFormal
