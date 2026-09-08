import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLNonzeroSpinCEuler4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFullLLVariationalAPI4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCDiracGreenClosure4D

/-! # Smooth SpinC realization in the finite fixed-boundary Euler equation -/

namespace JanusFormal
namespace P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLSmoothFirstVariation4D

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
open P0EFTJanusFullMatterRobinLLDirections4D
open P0EFTJanusDifferentialLLFullCurveActionDecomposition4D
open P0EFTJanusFullLLVariationalAPI4D
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

local instance : NormedSpace Real LLInput := Prod.normedSpace

local instance : ContinuousSMul Real LLInput := by
  apply Prod.continuousSMul

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

/-- On packets induced by genuine smooth fields, the Fréchet derivative of
the C⁰ LL action evaluates to the already derived full LL first variation. -/
theorem regularGeneralMetricC0LLPTAction_fderiv_apply_smooth
    (fields : IndependentFields period hPeriod)
    (direction : FullMatterRobinLLDirections period hPeriod) :
    fderiv Real
        (regularGeneralMetricC0LLPTAction period hPeriod
          (canonicalDivergenceFreeLLFrame period hPeriod)
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod))
        (smoothLLCoefficientPTC0FirstJetLinearMap period hPeriod
          (canonicalDivergenceFreeLLFrame period hPeriod)
          (fields.llAuxMetric, (fields.llMeasure, fields.llField)))
        (smoothLLCoefficientPTC0FirstJetLinearMap period hPeriod
          (canonicalDivergenceFreeLLFrame period hPeriod)
          (direction.llAuxMetric, (direction.llMeasure, direction.common.ll))) =
      fullLLEuler period hPeriod (canonicalDivergenceFreeLLFrame period hPeriod)
        fields direction (intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  let action := regularGeneralMetricC0LLPTAction period hPeriod
    (canonicalDivergenceFreeLLFrame period hPeriod)
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
  let packet : LLInput :=
    smoothLLCoefficientPTC0FirstJetLinearMap period hPeriod
      (canonicalDivergenceFreeLLFrame period hPeriod)
      (fields.llAuxMetric, (fields.llMeasure, fields.llField))
  let packetDirection : LLInput :=
    smoothLLCoefficientPTC0FirstJetLinearMap period hPeriod
      (canonicalDivergenceFreeLLFrame period hPeriod)
      (direction.llAuxMetric, (direction.llMeasure, direction.common.ll))
  have hAction : HasFDerivAt action (fderiv Real action packet) packet :=
    ((regularGeneralMetricC0LLPTAction_contDiff period hPeriod
      (canonicalDivergenceFreeLLFrame period hPeriod)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod)).differentiable
        (by simp) packet).hasFDerivAt
  have hLine : HasDerivAt (fun t : Real => packet + t • packetDirection)
      packetDirection 0 := by
    have hConstant : HasDerivAt (fun _ : Real => packet) 0 0 :=
      hasDerivAt_const (x := (0 : Real)) (c := packet)
    have hLinear := (hasDerivAt_id (0 : Real)).smul_const packetDirection
    exact (hConstant.add hLinear).congr_deriv (by simp)
  have hFrechet := hAction.comp_hasDerivAt_of_eq 0 hLine (by simp)
  have hExplicit := truePTAction_fullCurve_hasDerivAt_fullLLEuler period hPeriod
    (canonicalDivergenceFreeLLFrame period hPeriod) fields direction
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
  have hPacketLine (t : Real) :
      packet + t • packetDirection =
        smoothLLCoefficientPTC0FirstJetLinearMap period hPeriod
          (canonicalDivergenceFreeLLFrame period hPeriod)
          ((differentialLLFullCurve period hPeriod fields direction.llAuxMetric
              direction.llMeasure direction.common.ll t).llAuxMetric,
            ((differentialLLFullCurve period hPeriod fields direction.llAuxMetric
                direction.llMeasure direction.common.ll t).llMeasure,
              (differentialLLFullCurve period hPeriod fields direction.llAuxMetric
                direction.llMeasure direction.common.ll t).llField)) := by
    change
      smoothLLCoefficientPTC0FirstJetLinearMap period hPeriod
          (canonicalDivergenceFreeLLFrame period hPeriod)
          (fields.llAuxMetric, (fields.llMeasure, fields.llField)) +
        t • smoothLLCoefficientPTC0FirstJetLinearMap period hPeriod
          (canonicalDivergenceFreeLLFrame period hPeriod)
          (direction.llAuxMetric, (direction.llMeasure, direction.common.ll)) = _
    rw [← map_smul, ← map_add]
    rfl
  have hFunctions :
      (fun t : Real => action (packet + t • packetDirection)) =
        (fun t : Real => globalPTSymmetricDifferentialLLAction period hPeriod
          (canonicalDivergenceFreeLLFrame period hPeriod)
          (differentialLLFullCurve period hPeriod fields direction.llAuxMetric
            direction.llMeasure direction.common.ll t)
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod)) := by
    funext t
    rw [hPacketLine]
    exact regularGeneralMetricC0LLPTAction_smooth period hPeriod
      (canonicalDivergenceFreeLLFrame period hPeriod)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
      (differentialLLFullCurve period hPeriod fields direction.llAuxMetric
        direction.llMeasure direction.common.ll t)
  have hFrechet' : HasDerivAt (fun t : Real => action
      (packet + t • packetDirection))
      (fderiv Real action packet packetDirection) 0 := by
    simpa [Function.comp_def] using hFrechet
  rw [hFunctions] at hFrechet'
  exact hFrechet'.unique hExplicit

/-- C⁰ stationarity implies every smooth full LL weak equation. -/
theorem regularGeneralMetricC0LLPTAction_fderiv_eq_zero_implies_fullLLEuler_smooth
    (fields : IndependentFields period hPeriod)
    (hStationary : fderiv Real
      (regularGeneralMetricC0LLPTAction period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod))
      (smoothLLCoefficientPTC0FirstJetLinearMap period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod)
        (fields.llAuxMetric, (fields.llMeasure, fields.llField))) = 0)
    (direction : FullMatterRobinLLDirections period hPeriod) :
    fullLLEuler period hPeriod (canonicalDivergenceFreeLLFrame period hPeriod)
        fields direction (intrinsicCanonicalThroatVolumeMeasure period hPeriod) = 0 := by
  rw [← regularGeneralMetricC0LLPTAction_fderiv_apply_smooth period hPeriod fields
    direction, hStationary]
  rfl

end
end P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLSmoothFirstVariation4D
end JanusFormal

