import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCenterEuler4D

/-! # Fixed Candidate-A boundary completion of the finite physical action -/

namespace JanusFormal
namespace P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLFixedBoundaryAction4D

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
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCenterEuler4D
open P0EFTJanusFiniteFrameRegularC2RootDerivativeSylvesterBridge4D
open P0EFTJanusFiniteFrameRegularC2PhysicalMetricResidualBridge4D
open P0EFTJanusFiniteFrameRegularC2PhysicalDiffeomorphismDeDonderResidual4D
open P0EFTJanusPairedInteractionSmoothMetricResidual4D
open P0EFTJanusReciprocalBimetricPotential

attribute [local instance 2000]
  NonUnitalNormedRing.toNormedAddCommGroup NormedAlgebra.toNormedSpace

attribute [local instance 100]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

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

local notation "OldInput" =>
  FiniteFramePairedC2PhysicalMaxwellSpinCMatterCore period hPeriod geometry frame couplings

local notation "LLInput" =>
  GlobalMinimalPhysicalLLC0FirstJetPacket period hPeriod
    (canonicalDivergenceFreeLLFrame period hPeriod)

local instance : NormedSpace Real OldInput := Prod.normedSpace

local notation "Input" =>
  FiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCore period hPeriod geometry frame couplings

local instance : NormedSpace Real LLInput := Prod.normedSpace

local instance : NormedSpace Real Input := Prod.normedSpace

local instance : ContinuousSMul Real LLInput := by
  apply Prod.continuousSMul

local instance : ContinuousSMul Real Input := by
  apply Prod.continuousSMul

/-- Add the two Candidate-A boundary values while holding their data fixed on
the finite variational chart. -/
def finiteFramePairedC2PhysicalMaxwellSpinCMatterLLFixedBoundaryAction
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (input : Input) : Real :=
  finiteFramePairedC2PhysicalMaxwellSpinCMatterLLAction period hPeriod geometry frame
      hRegular couplings interactionScale coefficients input +
    globalCandidateAGHYAction period hPeriod data +
    globalCandidateANullBoundaryAction period hPeriod data

/-- Fixed GHY and null-boundary values preserve C² regularity on the exact
finite LL product domain. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLFixedBoundaryAction_contDiffOn_two
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (interactionScale : Real) (coefficients : PotentialCoefficients) :
    ContDiffOn Real 2
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLFixedBoundaryAction period hPeriod
        geometry frame hRegular couplings data interactionScale coefficients)
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLDomain period hPeriod geometry
        frame hRegular couplings) := by
  unfold finiteFramePairedC2PhysicalMaxwellSpinCMatterLLFixedBoundaryAction
  exact
    ((finiteFramePairedC2PhysicalMaxwellSpinCMatterLLAction_contDiffOn_two period
      hPeriod geometry frame hRegular couplings interactionScale coefficients).add
        contDiffOn_const).add contDiffOn_const

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

def finiteFramePairedC2PhysicalMaxwellSpinCMatterLLFixedBoundaryEuler
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (input : Input) : Input →L[Real] Real :=
  fderiv Real
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLFixedBoundaryAction period hPeriod
      geometry frame hRegular couplings data interactionScale coefficients) input

/-- The fixed boundary completion has exactly the same Euler map as the LL
finite action at every admissible point. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLFixedBoundaryEuler_eq_ll
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLDomain period hPeriod geometry
        frame hRegular couplings) :
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLFixedBoundaryEuler period hPeriod
        geometry frame hRegular couplings data interactionScale coefficients input =
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLEuler period hPeriod geometry frame
        hRegular couplings interactionScale coefficients input := by
  have hOld :=
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLAction_hasFDerivAt period hPeriod
      geometry frame hRegular couplings interactionScale coefficients input hInput
  have hFixed :=
    (hOld.add_const (globalCandidateAGHYAction period hPeriod data)).add_const
      (globalCandidateANullBoundaryAction period hPeriod data)
  unfold finiteFramePairedC2PhysicalMaxwellSpinCMatterLLFixedBoundaryEuler
  unfold finiteFramePairedC2PhysicalMaxwellSpinCMatterLLFixedBoundaryAction
  exact hFixed.fderiv

theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLFixedBoundaryAction_hasFDerivAt
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLDomain period hPeriod geometry
        frame hRegular couplings) :
    HasFDerivAt
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLFixedBoundaryAction period hPeriod
        geometry frame hRegular couplings data interactionScale coefficients)
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLFixedBoundaryEuler period hPeriod
        geometry frame hRegular couplings data interactionScale coefficients input)
      input := by
  rw [finiteFramePairedC2PhysicalMaxwellSpinCMatterLLFixedBoundaryEuler_eq_ll period
    hPeriod geometry frame hRegular couplings data interactionScale coefficients input
      hInput]
  unfold finiteFramePairedC2PhysicalMaxwellSpinCMatterLLFixedBoundaryAction
  exact ((finiteFramePairedC2PhysicalMaxwellSpinCMatterLLAction_hasFDerivAt period hPeriod
      geometry frame hRegular couplings interactionScale coefficients input hInput
      ).add_const (globalCandidateAGHYAction period hPeriod data)).add_const
        (globalCandidateANullBoundaryAction period hPeriod data)

/-- On the smooth Candidate-A LL packet, the enlarged value contains exactly
the LL, GHY and null-boundary Candidate-A summands. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLFixedBoundaryAction_global_ll
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (oldInput : OldInput) :
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLFixedBoundaryAction period hPeriod
        geometry frame hRegular couplings data interactionScale coefficients
        (oldInput, smoothLLCoefficientPTC0FirstJetLinearMap period hPeriod
          (canonicalDivergenceFreeLLFrame period hPeriod)
          ((data.boundary.llFields period hPeriod).llAuxMetric,
            ((data.boundary.llFields period hPeriod).llMeasure,
              (data.boundary.llFields period hPeriod).llField))) =
      finiteFramePairedC2PhysicalMaxwellSpinCMatterAction period hPeriod geometry
          frame hRegular couplings interactionScale coefficients oldInput +
        globalCandidateALLAction period hPeriod data +
        globalCandidateAGHYAction period hPeriod data +
        globalCandidateANullBoundaryAction period hPeriod data := by
  unfold finiteFramePairedC2PhysicalMaxwellSpinCMatterLLFixedBoundaryAction
  rw [finiteFramePairedC2PhysicalMaxwellSpinCMatterLLAction_global_ll]

/-- Holding the boundary data fixed preserves the zero-center stationarity
criterion of the finite LL action. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLFixedBoundaryEuler_zero_iff_ll
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (hMinusCenter : finiteFramePairedC2MinusCenter period hPeriod geometry frame ∈
      generalMetricRelativeC2VolumeDomain period hPeriod frame geometry.plusMetric)
    (interactionScale : Real) (coefficients : PotentialCoefficients) :
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLFixedBoundaryEuler period hPeriod
        geometry frame hRegular couplings data interactionScale coefficients 0 = 0 ↔
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLEuler period hPeriod geometry frame
        hRegular couplings interactionScale coefficients 0 = 0 := by
  rw [finiteFramePairedC2PhysicalMaxwellSpinCMatterLLFixedBoundaryEuler_eq_ll period
    hPeriod geometry frame hRegular couplings data interactionScale coefficients 0
      (zero_mem_finiteFramePairedC2PhysicalMaxwellSpinCMatterLLDomain period hPeriod
        geometry frame hRegular couplings hMinusCenter)]

/-- The fixed Candidate-A boundary completion preserves the complete center
criterion: mobile metric residual plus global De Donder. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLFixedBoundaryEuler_zero_iff_residual_and_globalDeDonder
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
    (interactionScale : Real) (coefficients : PotentialCoefficients) :
    let geometry := regularGeneralMetricC2LorentzChartGeometry period hPeriod plusBase
      (minusBase.metric.tensor - plusBase.metric.tensor) hChart
    let hFiniteRegular :=
      regularGeneralMetricC2LorentzChartGeometry_intrinsicSylvester_bijective period hPeriod
        plusBase (minusBase.metric.tensor - plusBase.metric.tensor) hChart
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLFixedBoundaryEuler period hPeriod
        geometry frame hFiniteRegular couplings data interactionScale coefficients 0 = 0 ↔
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
  rw [finiteFramePairedC2PhysicalMaxwellSpinCMatterLLFixedBoundaryEuler_zero_iff_ll
    period hPeriod geometry frame hFiniteRegular couplings data hMinusCenter
      interactionScale coefficients]
  exact
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLEuler_zero_iff_residual_and_globalDeDonder
      period hPeriod plusBase minusBase hPlusCanonicalVolume hMinusCanonicalVolume hChart
        frame hShift hZero couplings interactionScale coefficients

end
end P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLFixedBoundaryAction4D
end JanusFormal
