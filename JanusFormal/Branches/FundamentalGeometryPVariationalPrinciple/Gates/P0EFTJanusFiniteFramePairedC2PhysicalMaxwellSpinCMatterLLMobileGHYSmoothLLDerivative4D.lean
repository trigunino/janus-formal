import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYEulerSplit4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLSmoothFirstVariation4D

/-! # Smooth LL first variation inside the mobile GHY product -/

namespace JanusFormal
namespace P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYSmoothLLDerivative4D

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
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusReciprocalBimetricPotential
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDensity4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterRegularity4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzPositiveGHYDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC24D
open P0EFTJanusFullMatterRobinLLDirections4D
open P0EFTJanusFullLLVariationalAPI4D
open P0EFTJanusFiniteFramePairedC2PhysicalAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCenterEuler4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLSmoothFirstVariation4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYProductEuler4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYEulerSplit4D

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

/-- At a packet induced by genuine smooth LL fields, the total mobile-GHY
Euler evaluated on a pure smooth LL direction is exactly the previously
derived full LL first variation. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYEuler_apply_pure_smooth_ll
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients)
    (hTransverse : HasNoTangentialRadical period hPeriod
      boundaryBase.metric)
    (oldInput : OldInput)
    (fields : IndependentFields period hPeriod)
    (ghyInput : GHYInput)
    (hInput :
      ((oldInput,
          smoothLLCoefficientPTC0FirstJetLinearMap period hPeriod
            (canonicalDivergenceFreeLLFrame period hPeriod)
            (fields.llAuxMetric, (fields.llMeasure, fields.llField))),
        ghyInput) ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYDomain period
        hPeriod geometry frame hRegular couplings boundaryBase)
    (direction : FullMatterRobinLLDirections period hPeriod) :
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYEuler period hPeriod
        geometry frame hRegular couplings boundaryBase data einsteinScale
          interactionScale coefficients
        ((oldInput,
            smoothLLCoefficientPTC0FirstJetLinearMap period hPeriod
              (canonicalDivergenceFreeLLFrame period hPeriod)
              (fields.llAuxMetric, (fields.llMeasure, fields.llField))),
          ghyInput)
        (((0 : OldInput),
            smoothLLCoefficientPTC0FirstJetLinearMap period hPeriod
              (canonicalDivergenceFreeLLFrame period hPeriod)
              (direction.llAuxMetric,
                (direction.llMeasure, direction.common.ll))),
          (0 : GHYInput)) =
      fullLLEuler period hPeriod (canonicalDivergenceFreeLLFrame period hPeriod)
        fields direction (intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  have hTotalSplit := congrArg
    (fun derivative : Input →L[Real] Real =>
      derivative
        (((0 : OldInput),
            smoothLLCoefficientPTC0FirstJetLinearMap period hPeriod
              (canonicalDivergenceFreeLLFrame period hPeriod)
              (direction.llAuxMetric,
                (direction.llMeasure, direction.common.ll))),
          (0 : GHYInput)))
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYEuler_eq_bulk_add_ghy
      period hPeriod geometry frame hRegular couplings boundaryBase data
        einsteinScale interactionScale coefficients hTransverse _ hInput)
  have hBulkSplit := congrArg
    (fun derivative : BulkInput →L[Real] Real =>
      derivative
        ((0 : OldInput),
          smoothLLCoefficientPTC0FirstJetLinearMap period hPeriod
            (canonicalDivergenceFreeLLFrame period hPeriod)
            (direction.llAuxMetric,
              (direction.llMeasure, direction.common.ll))))
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLEuler_eq_old_add_ll period
      hPeriod geometry frame hRegular couplings interactionScale coefficients
      (oldInput,
        smoothLLCoefficientPTC0FirstJetLinearMap period hPeriod
          (canonicalDivergenceFreeLLFrame period hPeriod)
          (fields.llAuxMetric, (fields.llMeasure, fields.llField))) hInput.1)
  calc
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYEuler period hPeriod
          geometry frame hRegular couplings boundaryBase data einsteinScale
            interactionScale coefficients
          ((oldInput,
              smoothLLCoefficientPTC0FirstJetLinearMap period hPeriod
                (canonicalDivergenceFreeLLFrame period hPeriod)
                (fields.llAuxMetric, (fields.llMeasure, fields.llField))),
            ghyInput)
          (((0 : OldInput),
              smoothLLCoefficientPTC0FirstJetLinearMap period hPeriod
                (canonicalDivergenceFreeLLFrame period hPeriod)
                (direction.llAuxMetric,
                  (direction.llMeasure, direction.common.ll))),
            (0 : GHYInput)) =
        finiteFramePairedC2PhysicalMaxwellSpinCMatterLLEuler period hPeriod
          geometry frame hRegular couplings interactionScale coefficients
          (oldInput,
            smoothLLCoefficientPTC0FirstJetLinearMap period hPeriod
              (canonicalDivergenceFreeLLFrame period hPeriod)
              (fields.llAuxMetric, (fields.llMeasure, fields.llField)))
          ((0 : OldInput),
            smoothLLCoefficientPTC0FirstJetLinearMap period hPeriod
              (canonicalDivergenceFreeLLFrame period hPeriod)
              (direction.llAuxMetric,
                (direction.llMeasure, direction.common.ll))) := by
          simpa using hTotalSplit
    _ = fderiv Real
          (regularGeneralMetricC0LLPTAction period hPeriod
            (canonicalDivergenceFreeLLFrame period hPeriod)
            (intrinsicCanonicalThroatVolumeMeasure period hPeriod))
          (smoothLLCoefficientPTC0FirstJetLinearMap period hPeriod
            (canonicalDivergenceFreeLLFrame period hPeriod)
            (fields.llAuxMetric, (fields.llMeasure, fields.llField)))
          (smoothLLCoefficientPTC0FirstJetLinearMap period hPeriod
            (canonicalDivergenceFreeLLFrame period hPeriod)
            (direction.llAuxMetric,
              (direction.llMeasure, direction.common.ll))) := by
          simpa using hBulkSplit
    _ = fullLLEuler period hPeriod
          (canonicalDivergenceFreeLLFrame period hPeriod) fields direction
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
      regularGeneralMetricC0LLPTAction_fderiv_apply_smooth period hPeriod fields
        direction

end
end P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYSmoothLLDerivative4D
end JanusFormal
