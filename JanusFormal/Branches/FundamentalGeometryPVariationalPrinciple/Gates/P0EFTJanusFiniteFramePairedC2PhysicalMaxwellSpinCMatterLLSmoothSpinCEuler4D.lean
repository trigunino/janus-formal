import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLNonzeroSpinCEuler4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCDiracGreenClosure4D

/-! # Smooth SpinC realization in the finite fixed-boundary Euler equation -/

namespace JanusFormal
namespace P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLSmoothSpinCEuler4D

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
open P0EFTJanusProgramPPrimitiveSpinCDiracGreenClosure4D
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
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLNonzeroSpinCEuler4D
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

local notation "LLInput" =>
  GlobalMinimalPhysicalLLC0FirstJetPacket period hPeriod
    (canonicalDivergenceFreeLLFrame period hPeriod)

/-- On the canonical Green graph and the smooth LL packet, the finite action
contains exactly the smooth global matter, LL, GHY and null-boundary values. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLFixedBoundaryAction_global_smooth_spinC_ll
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (physicalInput : PhysicalInput) :
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLFixedBoundaryAction period hPeriod
        geometry frame hRegular couplings data interactionScale coefficients
        ((physicalInput,
            (programPPrimitiveSpinCMatterSmoothGraphRealization_of_geometricGreen
              period hPeriod couplings.matterMassSquared).toGraph
              configuration.spinCMatter),
          smoothLLCoefficientPTC0FirstJetLinearMap period hPeriod
            (canonicalDivergenceFreeLLFrame period hPeriod)
            ((data.boundary.llFields period hPeriod).llAuxMetric,
              ((data.boundary.llFields period hPeriod).llMeasure,
                (data.boundary.llFields period hPeriod).llField))) =
      finiteFramePairedC2PhysicalMaxwellAction period hPeriod geometry frame hRegular
          couplings interactionScale coefficients physicalInput +
        globalCandidateAMatterAction period hPeriod configuration couplings +
        globalCandidateALLAction period hPeriod data +
        globalCandidateAGHYAction period hPeriod data +
        globalCandidateANullBoundaryAction period hPeriod data := by
  rw [finiteFramePairedC2PhysicalMaxwellSpinCMatterLLFixedBoundaryAction_global_ll]
  unfold finiteFramePairedC2PhysicalMaxwellSpinCMatterAction
  rw [(programPPrimitiveSpinCMatterSmoothGraphRealization_of_geometricGreen period
    hPeriod couplings.matterMassSquared).action_agreement]
  rfl

/-- For every genuine smooth SpinC field, fixed-boundary stationarity at zero
LL packet is Maxwell center stationarity plus its maximal spectral residual. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLFixedBoundaryEuler_smoothSpinC_zeroLL_iff_maxwell_and_spinCResidual
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (hMinusCenter : finiteFramePairedC2MinusCenter period hPeriod geometry frame ∈
      generalMetricRelativeC2VolumeDomain period hPeriod frame geometry.plusMetric)
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (field : ProgramPPrimitiveSpinCMatterSmoothField period hPeriod) :
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLFixedBoundaryEuler period hPeriod
        geometry frame hRegular couplings data interactionScale coefficients
        ((0, (programPPrimitiveSpinCMatterSmoothGraphRealization_of_geometricGreen
          period hPeriod couplings.matterMassSquared).toGraph field),
          (0 : LLInput)) = 0 ↔
      finiteFramePairedC2PhysicalMaxwellEuler period hPeriod geometry frame hRegular
          couplings interactionScale coefficients 0 = 0 ∧
        programPPrimitiveSpinCMatterGraphMaximalSpectralResidual period hPeriod
          couplings.matterMassSquared
          ((programPPrimitiveSpinCMatterSmoothGraphRealization_of_geometricGreen
            period hPeriod couplings.matterMassSquared).toGraph field) = 0 :=
  finiteFramePairedC2PhysicalMaxwellSpinCMatterLLFixedBoundaryEuler_zeroLL_iff_maxwell_and_spinCResidual
    period hPeriod geometry frame hRegular couplings data hMinusCenter interactionScale
      coefficients
      ((programPPrimitiveSpinCMatterSmoothGraphRealization_of_geometricGreen period
        hPeriod couplings.matterMassSquared).toGraph field)

/-- On the regular paired metric chart, every genuine smooth SpinC field obeys
the complete metric, De Donder and maximal spectral stationarity criterion. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLFixedBoundaryEuler_smoothSpinC_zeroLL_iff_residuals_and_globalDeDonder
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
    (field : ProgramPPrimitiveSpinCMatterSmoothField period hPeriod) :
    let geometry := regularGeneralMetricC2LorentzChartGeometry period hPeriod plusBase
      (minusBase.metric.tensor - plusBase.metric.tensor) hChart
    let hFiniteRegular :=
      regularGeneralMetricC2LorentzChartGeometry_intrinsicSylvester_bijective period hPeriod
        plusBase (minusBase.metric.tensor - plusBase.metric.tensor) hChart
    let hRoot := pairedInteractionCenter_rootAdmissible period hPeriod plusBase minusBase hZero
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLFixedBoundaryEuler period hPeriod
        geometry frame hFiniteRegular couplings data interactionScale coefficients
        ((0, (programPPrimitiveSpinCMatterSmoothGraphRealization_of_geometricGreen
          period hPeriod couplings.matterMassSquared).toGraph field),
          (0 : GlobalMinimalPhysicalLLC0FirstJetPacket period hPeriod
            (canonicalDivergenceFreeLLFrame period hPeriod))) = 0 ↔
      (regularFramePairedMobileEinsteinHilbertInteractionResidual period hPeriod
          plusBase minusBase hRoot couplings interactionScale coefficients = 0 ∧
        globalGeneralMetricDeDonderLinearMap period hPeriod minusBase.metric
          (minusBase.metric.tensor - plusBase.metric.tensor) = 0) ∧
        programPPrimitiveSpinCMatterGraphMaximalSpectralResidual period hPeriod
          couplings.matterMassSquared
          ((programPPrimitiveSpinCMatterSmoothGraphRealization_of_geometricGreen
            period hPeriod couplings.matterMassSquared).toGraph field) = 0 :=
  finiteFramePairedC2PhysicalMaxwellSpinCMatterLLFixedBoundaryEuler_zeroLL_iff_residuals_and_globalDeDonder
    period hPeriod plusBase minusBase hPlusCanonicalVolume hMinusCanonicalVolume hChart
      frame hShift hZero couplings data interactionScale coefficients
      ((programPPrimitiveSpinCMatterSmoothGraphRealization_of_geometricGreen period
        hPeriod couplings.matterMassSquared).toGraph field)

end
end P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLSmoothSpinCEuler4D
end JanusFormal
