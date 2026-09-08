import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYSmoothLLResidualPairings4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIntegratedPTFullLLFirstVariationZero4D

/-! # LL equations implied by stationary mobile GHY Euler data -/

namespace JanusFormal
namespace P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYStationaryLLSystem4D

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
open P0EFTJanusMappingTorusGlobalLLVariation4D
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
open P0EFTJanusFullMatterRobinLLDirections4D
open P0EFTJanusFullLLVariationalAPI4D
open P0EFTJanusIntegratedPTFullLLHessianAssembly4D
open P0EFTJanusIntegratedPTFullLLHessianVariation4D
open P0EFTJanusIntegratedPTLLWorldvolumeHessianVariation4D
open P0EFTJanusPTSymmetricDifferentialLLKineticSimultaneousVariation4D
open P0EFTJanusIntegratedPTFullLLFirstVariationZero4D
open P0EFTJanusFiniteFramePairedC2PhysicalAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCenterEuler4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYProductEuler4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYEulerSplit4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYSmoothLLDerivative4D

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

private abbrev StationaryOldInput
    (period : Real) (hPeriod : period ≠ 0)
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (couplings : GlobalCandidateAActionCouplings) :=
  FiniteFramePairedC2PhysicalMaxwellSpinCMatterCore period hPeriod geometry frame
    couplings

private abbrev StationaryGHYInput
    (period : Real) (hPeriod : period ≠ 0)
    (boundaryBase : RegularGeneralLorentzMetric period hPeriod) :=
  CandidateANormalBoundaryFunctionalCore period hPeriod boundaryBase × Real

private abbrev StationaryInput
    (period : Real) (hPeriod : period ≠ 0)
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (couplings : GlobalCandidateAActionCouplings)
    (boundaryBase : RegularGeneralLorentzMetric period hPeriod) :=
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

/-- A pure direction in the three smooth LL slots. -/
def mobileGHYPureLLDirection
    (llAuxMetric : SmoothThroatField period hPeriod LLMetricFiber)
    (llMeasure : SmoothThroatField period hPeriod Real)
    (llField : SmoothThroatField period hPeriod LLFieldFiber) :
    FullMatterRobinLLDirections period hPeriod where
  common :=
    { metric :=
        P0EFTJanusProgramPCommonLLActionVariation4D.zeroSmoothDiagonalMetricVariation
          period hPeriod
      matter := 0
      gauge := 0
      ghost := 0
      auxiliary := 0
      ll := llField }
  robin := 0
  llAuxMetric := llAuxMetric
  llMeasure := llMeasure

/-- The measure/field pair carried by a pure smooth LL direction. -/
def mobileGHYLLVariation
    (llMeasure : SmoothThroatField period hPeriod Real)
    (llField : SmoothThroatField period hPeriod LLFieldFiber) :
    LLVariation period hPeriod where
  measureDirection := llMeasure
  fieldDirection := llField

section

variable {configuration : GlobalFieldConfiguration period hPeriod}
variable {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
variable (data : GlobalCandidateAActionData period hPeriod configuration couplings
  NonNullFace NullFace)
variable (einsteinScale interactionScale : Real)
variable (coefficients : PotentialCoefficients)
variable (hTransverse : HasNoTangentialRadical period hPeriod boundaryBase.metric)
variable (oldInput : StationaryOldInput period hPeriod geometry frame couplings)
variable (fields : IndependentFields period hPeriod)
variable (ghyInput : StationaryGHYInput period hPeriod boundaryBase)
variable (hInput :
  ((oldInput,
      smoothLLCoefficientPTC0FirstJetLinearMap period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod)
        (fields.llAuxMetric, (fields.llMeasure, fields.llField))),
    ghyInput) ∈
  finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYDomain period
    hPeriod geometry frame hRegular couplings boundaryBase)
variable (hStationary :
  finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYEuler period hPeriod
      geometry frame hRegular couplings boundaryBase data einsteinScale
        interactionScale coefficients
      ((oldInput,
          smoothLLCoefficientPTC0FirstJetLinearMap period hPeriod
            (canonicalDivergenceFreeLLFrame period hPeriod)
            (fields.llAuxMetric, (fields.llMeasure, fields.llField))),
        ghyInput) = 0)

include geometry frame hRegular couplings boundaryBase data einsteinScale
  interactionScale coefficients hTransverse oldInput fields ghyInput hInput
  hStationary

/-- Total stationarity annihilates every genuinely smooth three-slot LL
direction. -/
private theorem mobileGHYEuler_eq_zero_implies_fullLLEuler
    (direction : FullMatterRobinLLDirections period hPeriod) :
    fullLLEuler period hPeriod (canonicalDivergenceFreeLLFrame period hPeriod)
      fields direction (intrinsicCanonicalThroatVolumeMeasure period hPeriod) = 0 := by
  have hValue := congrArg
    (fun derivative :
        StationaryInput period hPeriod geometry frame couplings boundaryBase
          →L[Real] Real =>
      derivative
        (((0 : StationaryOldInput period hPeriod geometry frame couplings),
            smoothLLCoefficientPTC0FirstJetLinearMap period hPeriod
              (canonicalDivergenceFreeLLFrame period hPeriod)
              (direction.llAuxMetric,
                (direction.llMeasure, direction.common.ll))),
          (0 : StationaryGHYInput period hPeriod boundaryBase)))
    hStationary
  have hPure :
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYEuler period hPeriod
          geometry frame hRegular couplings boundaryBase data einsteinScale
            interactionScale coefficients
          ((oldInput,
              smoothLLCoefficientPTC0FirstJetLinearMap period hPeriod
                (canonicalDivergenceFreeLLFrame period hPeriod)
                (fields.llAuxMetric, (fields.llMeasure, fields.llField))),
            ghyInput)
          (((0 : StationaryOldInput period hPeriod geometry frame couplings),
              smoothLLCoefficientPTC0FirstJetLinearMap period hPeriod
                (canonicalDivergenceFreeLLFrame period hPeriod)
                (direction.llAuxMetric,
                  (direction.llMeasure, direction.common.ll))),
            (0 : StationaryGHYInput period hPeriod boundaryBase)) = 0 := by
    simpa using hValue
  exact
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYEuler_apply_pure_smooth_ll
      period hPeriod geometry frame hRegular couplings boundaryBase data
        einsteinScale interactionScale coefficients hTransverse oldInput fields
          ghyInput hInput direction).symm.trans hPure

/-- Stationarity implies the explicit auxiliary-metric LL equation for every
smooth auxiliary-metric test. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYEuler_eq_zero_implies_llAuxMetric_equation
    (llAuxMetric : SmoothThroatField period hPeriod LLMetricFiber) :
    (∫ point,
      ptSymmetricDifferentialLLKineticFirstVariation period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod) fields.llAuxMetric
          fields.llField llAuxMetric 0 point
      ∂intrinsicCanonicalThroatVolumeMeasure period hPeriod) = 0 := by
  have hLL := mobileGHYEuler_eq_zero_implies_fullLLEuler
    (period := period) (hPeriod := hPeriod) (geometry := geometry)
    (frame := frame) (hRegular := hRegular) (couplings := couplings)
    (boundaryBase := boundaryBase) data einsteinScale interactionScale
    coefficients hTransverse oldInput fields ghyInput hInput hStationary
    (mobileGHYPureLLDirection period hPeriod llAuxMetric 0 0)
  change
    (∫ point,
      ptSymmetricDifferentialLLKineticFirstVariation period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod) fields.llAuxMetric
          fields.llField llAuxMetric 0 point
      ∂intrinsicCanonicalThroatVolumeMeasure period hPeriod) +
      globalPTLLFirstVariation period hPeriod fields
        (mobileGHYLLVariation period hPeriod 0 0)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) = 0 at hLL
  have hWorldvolumeZero :
      globalPTLLFirstVariation period hPeriod fields
        (mobileGHYLLVariation period hPeriod 0 0)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) = 0 := by
    simpa [mobileGHYLLVariation, zeroLLVariation] using
      (globalPTLLFirstVariation_zero period hPeriod fields
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod))
  simpa [hWorldvolumeZero] using hLL

/-- Stationarity implies the explicit LL-measure equation for every smooth
measure test. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYEuler_eq_zero_implies_llMeasure_equation
    (llMeasure : SmoothThroatField period hPeriod Real) :
    globalPTLLFirstVariation period hPeriod fields
      (mobileGHYLLVariation period hPeriod llMeasure 0)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) = 0 := by
  have hLL := mobileGHYEuler_eq_zero_implies_fullLLEuler
    (period := period) (hPeriod := hPeriod) (geometry := geometry)
    (frame := frame) (hRegular := hRegular) (couplings := couplings)
    (boundaryBase := boundaryBase) data einsteinScale interactionScale
    coefficients hTransverse oldInput fields ghyInput hInput hStationary
    (mobileGHYPureLLDirection period hPeriod 0 llMeasure 0)
  change
    (∫ point,
      ptSymmetricDifferentialLLKineticFirstVariation period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod) fields.llAuxMetric
          fields.llField 0 0 point
      ∂intrinsicCanonicalThroatVolumeMeasure period hPeriod) +
      globalPTLLFirstVariation period hPeriod fields
        (mobileGHYLLVariation period hPeriod llMeasure 0)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) = 0 at hLL
  simpa using hLL

/-- Stationarity implies the explicit LL-field equation for every smooth
field test. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYEuler_eq_zero_implies_llField_equation
    (llField : SmoothThroatField period hPeriod LLFieldFiber) :
    (∫ point,
      ptSymmetricDifferentialLLKineticFirstVariation period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod) fields.llAuxMetric
          fields.llField 0 llField point
      ∂intrinsicCanonicalThroatVolumeMeasure period hPeriod) +
      globalPTLLFirstVariation period hPeriod fields
        (mobileGHYLLVariation period hPeriod 0 llField)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) = 0 := by
  have hLL := mobileGHYEuler_eq_zero_implies_fullLLEuler
    (period := period) (hPeriod := hPeriod) (geometry := geometry)
    (frame := frame) (hRegular := hRegular) (couplings := couplings)
    (boundaryBase := boundaryBase) data einsteinScale interactionScale
    coefficients hTransverse oldInput fields ghyInput hInput hStationary
    (mobileGHYPureLLDirection period hPeriod 0 0 llField)
  change
    (∫ point,
      ptSymmetricDifferentialLLKineticFirstVariation period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod) fields.llAuxMetric
          fields.llField 0 llField point
      ∂intrinsicCanonicalThroatVolumeMeasure period hPeriod) +
      globalPTLLFirstVariation period hPeriod fields
        (mobileGHYLLVariation period hPeriod 0 llField)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) = 0 at hLL
  exact hLL

end

end
end P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYStationaryLLSystem4D
end JanusFormal
