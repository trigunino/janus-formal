import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2PhysicalMaxwellCenterEuler4D

/-! # Primitive SpinC matter augmentation at the finite physical center -/

namespace JanusFormal
namespace P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterCenterEuler4D

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusGlobalGeneralMetricDeDonder4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDensity4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterRegularity4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartGeometry4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalRelativeMetricCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomainOpen4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusFiniteFramePairedC2PhysicalAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellCenterEuler4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterAction4D
open P0EFTJanusFiniteFrameRegularC2RootDerivativeSylvesterBridge4D
open P0EFTJanusFiniteFrameRegularC2PhysicalMetricResidualBridge4D
open P0EFTJanusFiniteFrameRegularC2PhysicalDiffeomorphismDeDonderResidual4D
open P0EFTJanusPairedInteractionSmoothMetricResidual4D
open P0EFTJanusReciprocalBimetricPotential

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance : IsManifold coverModelWithCorners ω
    (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

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

local notation "Input" =>
  FiniteFramePairedC2PhysicalMaxwellSpinCMatterCore period hPeriod geometry frame couplings

local instance : NormedSpace Real Input := Prod.normedSpace

/-- At every admissible point, the product Euler is the Maxwell-augmented
physical Euler plus the closed-graph SpinC form. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterEuler_eq_maxwell_add_matter
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (input : Input)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterDomain period hPeriod geometry frame
        hRegular couplings) :
    finiteFramePairedC2PhysicalMaxwellSpinCMatterEuler period hPeriod geometry frame
        hRegular couplings interactionScale coefficients input =
      (finiteFramePairedC2PhysicalMaxwellEuler period hPeriod geometry frame hRegular
        couplings interactionScale coefficients input.1).comp
          (ContinuousLinearMap.fst Real PhysicalInput MatterInput) +
        (programPPrimitiveSpinCMatterGraphForm period hPeriod couplings.matterMassSquared
          input.2).comp (ContinuousLinearMap.snd Real PhysicalInput MatterInput) := by
  have hFst : HasFDerivAt (fun current : Input => current.1)
      (ContinuousLinearMap.fst Real PhysicalInput MatterInput) input := by
    fun_prop
  have hSnd : HasFDerivAt (fun current : Input => current.2)
      (ContinuousLinearMap.snd Real PhysicalInput MatterInput) input := by
    fun_prop
  have hPhysical :=
    (finiteFramePairedC2PhysicalMaxwellAction_hasFDerivAt period hPeriod geometry frame
      hRegular couplings interactionScale coefficients input.1 hInput.1).comp input hFst
  have hMatter :=
    (programPPrimitiveSpinCMatterGraphAction_hasFDerivAt period hPeriod
      couplings.matterMassSquared input.2).comp input hSnd
  unfold finiteFramePairedC2PhysicalMaxwellSpinCMatterEuler
  change fderiv Real
      (fun current : Input =>
        finiteFramePairedC2PhysicalMaxwellAction period hPeriod geometry frame hRegular
            couplings interactionScale coefficients current.1 +
          programPPrimitiveSpinCMatterGraphAction period hPeriod
            couplings.matterMassSquared current.2) input = _
  exact (hPhysical.add hMatter).fderiv

/-- The SpinC Euler form vanishes at the zero graph state. -/
@[simp]
theorem finiteFrameSpinCMatterGraphForm_zero (massSquared : Real) :
    programPPrimitiveSpinCMatterGraphForm period hPeriod massSquared
        (0 : ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod massSquared) = 0 :=
  (programPPrimitiveSpinCMatterGraphForm period hPeriod massSquared).map_zero

/-- At zero matter state, the product Euler is the Maxwell Euler extended by
the first projection. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterEuler_zero_eq_maxwell
    (hMinusCenter : finiteFramePairedC2MinusCenter period hPeriod geometry frame ∈
      generalMetricRelativeC2VolumeDomain period hPeriod frame geometry.plusMetric)
    (interactionScale : Real) (coefficients : PotentialCoefficients) :
    finiteFramePairedC2PhysicalMaxwellSpinCMatterEuler period hPeriod geometry frame
        hRegular couplings interactionScale coefficients 0 =
      (finiteFramePairedC2PhysicalMaxwellEuler period hPeriod geometry frame hRegular
        couplings interactionScale coefficients 0).comp
          (ContinuousLinearMap.fst Real PhysicalInput MatterInput) := by
  have hCenter :=
    zero_mem_finiteFramePairedC2PhysicalMaxwellSpinCMatterDomain period hPeriod geometry
      frame hRegular couplings hMinusCenter
  rw [finiteFramePairedC2PhysicalMaxwellSpinCMatterEuler_eq_maxwell_add_matter
    period hPeriod geometry frame hRegular couplings interactionScale coefficients 0 hCenter]
  simp

/-- Product stationarity at zero matter is exactly Maxwell-augmented physical
stationarity. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterEuler_zero_iff_maxwell
    (hMinusCenter : finiteFramePairedC2MinusCenter period hPeriod geometry frame ∈
      generalMetricRelativeC2VolumeDomain period hPeriod frame geometry.plusMetric)
    (interactionScale : Real) (coefficients : PotentialCoefficients) :
    finiteFramePairedC2PhysicalMaxwellSpinCMatterEuler period hPeriod geometry frame
        hRegular couplings interactionScale coefficients 0 = 0 ↔
      finiteFramePairedC2PhysicalMaxwellEuler period hPeriod geometry frame hRegular
        couplings interactionScale coefficients 0 = 0 := by
  rw [finiteFramePairedC2PhysicalMaxwellSpinCMatterEuler_zero_eq_maxwell period hPeriod
    geometry frame hRegular couplings hMinusCenter interactionScale coefficients]
  constructor
  · intro hComposite
    apply ContinuousLinearMap.ext
    intro direction
    have hValue := congrArg
      (fun derivative : Input →L[Real] Real =>
        derivative (direction, (0 : MatterInput))) hComposite
    simpa using hValue
  · intro hMaxwell
    simp [hMaxwell]

/-- Adding a zero SpinC graph state preserves the complete finite center
criterion: mobile metric residual plus global De Donder. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterEuler_zero_iff_residual_and_globalDeDonder
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
    let hRoot := pairedInteractionCenter_rootAdmissible period hPeriod plusBase minusBase hZero
    finiteFramePairedC2PhysicalMaxwellSpinCMatterEuler period hPeriod geometry frame
        hFiniteRegular couplings interactionScale coefficients 0 = 0 ↔
      regularFramePairedMobileEinsteinHilbertInteractionResidual period hPeriod
          plusBase minusBase hRoot couplings interactionScale coefficients = 0 ∧
        globalGeneralMetricDeDonderLinearMap period hPeriod minusBase.metric
          (minusBase.metric.tensor - plusBase.metric.tensor) = 0 := by
  dsimp only
  let geometry := regularGeneralMetricC2LorentzChartGeometry period hPeriod plusBase
    (minusBase.metric.tensor - plusBase.metric.tensor) hChart
  let hFiniteRegular :=
    regularGeneralMetricC2LorentzChartGeometry_intrinsicSylvester_bijective period hPeriod plusBase
      (minusBase.metric.tensor - plusBase.metric.tensor) hChart
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
  rw [finiteFramePairedC2PhysicalMaxwellSpinCMatterEuler_zero_iff_maxwell period hPeriod
    geometry frame hFiniteRegular couplings hMinusCenter interactionScale coefficients]
  exact
    finiteFramePairedC2PhysicalMaxwellEuler_zero_iff_residual_and_globalDeDonder period
      hPeriod plusBase minusBase hPlusCanonicalVolume hMinusCanonicalVolume hChart frame hShift
        hZero couplings interactionScale coefficients

end
end P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterCenterEuler4D
end JanusFormal
