import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYProductEuler4D

/-! # Smooth value bridge for the independent mobile GHY product -/

namespace JanusFormal
namespace P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYSmoothBridge4D

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
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalBoundaryCompletion4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusReciprocalBimetricPotential
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterRegularity4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC3MetricCore4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzPositiveGHYDomain4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzPositiveGHYActionBridge4D
open P0EFTJanusFiniteFramePairedC2PhysicalAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYProductEuler4D

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
  (boundaryBase : RegularGeneralLorentzMetric period hPeriod)

local notation "BulkInput" =>
  FiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCore period hPeriod geometry frame
    couplings

/-- On a genuine smooth normal displacement, the mobile GHY factor is exactly
the Candidate-A GHY value for the canonically substituted boundary datum.  The
null-face value remains the fixed datum selected by the finite product. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYAction_smooth_ghy
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients)
    (bulkInput : BulkInput)
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
        (bulkInput,
          (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod
            boundaryBase (tensor, displacement), parameter)) =
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLAction period hPeriod
          geometry frame hRegular couplings interactionScale coefficients
            bulkInput +
        globalCandidateAGHYAction period hPeriod
          (candidateANormalBoundaryLorentzPositiveGHYActionData period hPeriod
            data einsteinScale boundaryBase tensor displacement parameter
              hCurrent) +
        globalCandidateANullBoundaryAction period hPeriod data := by
  unfold finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYAction
  rw [candidateANormalBoundaryTwoSheetGHYActionFiberEvaluation_eq_globalCandidateA_lorentzPositiveGHY
    period hPeriod data einsteinScale boundaryBase hTransverse tensor
      displacement parameter hCurrent]

end
end P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYSmoothBridge4D
end JanusFormal
