import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYSmoothBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLSmoothSpinCEuler4D

/-! # Smooth SpinC and GHY same-action value ledger -/

namespace JanusFormal
namespace P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYSmoothSpinCSameAction4D

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
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalBoundaryCompletion4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusReciprocalBimetricPotential
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterRegularity4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPPrimitiveSpinCDiracGreenClosure4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC3MetricCore4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzPositiveGHYDomain4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzPositiveGHYActionBridge4D
open P0EFTJanusFiniteFramePairedC2PhysicalAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLSmoothSpinCEuler4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYProductEuler4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYSmoothBridge4D

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
  (boundaryBase : RegularGeneralLorentzMetric period hPeriod)

local notation "PhysicalInput" =>
  FiniteFramePairedC2PhysicalCore period hPeriod geometry frame

local notation "OldInput" =>
  FiniteFramePairedC2PhysicalMaxwellSpinCMatterCore period hPeriod geometry frame
    couplings

local notation "LLInput" =>
  GlobalMinimalPhysicalLLC0FirstJetPacket period hPeriod
    (canonicalDivergenceFreeLLFrame period hPeriod)

local notation "BulkInput" =>
  FiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCore period hPeriod geometry frame
    couplings

local notation "GHYCore" =>
  CandidateANormalBoundaryFunctionalCore period hPeriod boundaryBase

local notation "GHYInput" => Prod GHYCore Real

local notation "Input" =>
  FiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYCore period hPeriod
    geometry frame couplings boundaryBase

local instance : NormedSpace Real OldInput := Prod.normedSpace

local instance : NormedSpace Real LLInput := Prod.normedSpace

local instance : NormedSpace Real BulkInput := Prod.normedSpace

local instance mobileGHYFunctionalCoreNormedAddCommGroup :
    NormedAddCommGroup GHYCore :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.candidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    period hPeriod boundaryBase

local instance mobileGHYFunctionalCoreNormedSpace :
    NormedSpace Real GHYCore :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.candidateANormalBoundaryFunctionalCoreNormedSpace
    period hPeriod boundaryBase

local instance : NormedSpace Real GHYInput := Prod.normedSpace

local instance mobileGHYInputSMul : SMul Real Input := Prod.instSMul

local instance : ContinuousSMul Real LLInput := by
  apply Prod.continuousSMul

local instance : ContinuousSMul Real BulkInput := by
  apply Prod.continuousSMul

local instance : ContinuousSMul Real GHYInput := by
  apply Prod.continuousSMul

local instance : ContinuousSMul Real Input := by
  apply Prod.continuousSMul

local instance : NormedSpace Real Input := Prod.normedSpace

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

/-- On the canonical smooth SpinC graph, the smooth LL packet and a genuine
smooth normal displacement, the mobile product contains each current
Candidate-A matter, LL, GHY and null-boundary value exactly once. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYAction_global_smooth_spinC_ll_ghy
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients)
    (physicalInput : PhysicalInput)
    (hTransverse : HasNoTangentialRadical period hPeriod
      boundaryBase.metric)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (hCurrent :
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod
          boundaryBase (tensor, displacement), parameter) ∈
        candidateANormalBoundaryLorentzPositiveGHYDomain period hPeriod
          boundaryBase) :
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYAction period hPeriod
        geometry frame hRegular couplings boundaryBase data einsteinScale
          interactionScale coefficients
        (((physicalInput,
            (programPPrimitiveSpinCMatterSmoothGraphRealization_of_geometricGreen
              period hPeriod couplings.matterMassSquared).toGraph
                configuration.spinCMatter),
          smoothLLCoefficientPTC0FirstJetLinearMap period hPeriod
            (canonicalDivergenceFreeLLFrame period hPeriod)
            ((data.boundary.llFields period hPeriod).llAuxMetric,
              ((data.boundary.llFields period hPeriod).llMeasure,
                (data.boundary.llFields period hPeriod).llField))),
          (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod
            boundaryBase (tensor, displacement), parameter)) =
      finiteFramePairedC2PhysicalMaxwellAction period hPeriod geometry frame
          hRegular couplings interactionScale coefficients physicalInput +
        globalCandidateAMatterAction period hPeriod configuration couplings +
        globalCandidateALLAction period hPeriod data +
        globalCandidateAGHYAction period hPeriod
          (candidateANormalBoundaryLorentzPositiveGHYActionData period hPeriod
            data einsteinScale boundaryBase tensor displacement parameter hCurrent) +
        globalCandidateANullBoundaryAction period hPeriod data := by
  rw [finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYAction_smooth_ghy
    (hTransverse := hTransverse)]
  rw [finiteFramePairedC2PhysicalMaxwellSpinCMatterLLAction_global_ll]
  unfold finiteFramePairedC2PhysicalMaxwellSpinCMatterAction
  rw [(programPPrimitiveSpinCMatterSmoothGraphRealization_of_geometricGreen period
    hPeriod couplings.matterMassSquared).action_agreement]
  rfl

end
end P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYSmoothSpinCSameAction4D
end JanusFormal
