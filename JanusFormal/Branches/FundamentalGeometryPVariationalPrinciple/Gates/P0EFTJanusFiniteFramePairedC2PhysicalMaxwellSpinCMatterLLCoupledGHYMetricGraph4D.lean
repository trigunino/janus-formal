import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullReparametrizationEuler4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzPositiveEinsteinMaxwellGHYAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameRegularC2RootDerivativeSylvesterBridge4D

/-! # Metric-coupled mobile GHY graph

The mobile GHY metric current is constrained to equal the plus bulk metric
coordinate after the canonical boundary `C³` to bulk `C²` projection.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCoupledGHYMetricGraph4D

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
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalBoundaryCompletion4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusReciprocalBimetricPotential
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDensity4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterRegularity4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartGeometry4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalRelativeMetricCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomainOpen4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC24D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC3MetricCore4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzGHYDomain4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzPositiveGHYDomain4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzPositiveGHYActionBridge4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzPositiveEinsteinMaxwellGHYAction4D
open P0EFTJanusFiniteFrameDiffeomorphismC2Core4D
open P0EFTJanusFiniteFramePairedC2FullBRSTGaugeAction4D
open P0EFTJanusFiniteFrameRegularC2RootDerivativeSylvesterBridge4D
open P0EFTJanusFiniteFramePairedC2PhysicalAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYProductEuler4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYEulerSplit4D

attribute [local instance 100]
  NonUnitalNormedRing.toNormedAddCommGroup NormedAlgebra.toNormedSpace

attribute [local instance 2000]
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

variable (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
  (hChart : regularGeneralMetricSmoothC2Variation period hPeriod plusBase
      (minusBase.metric.tensor - plusBase.metric.tensor) ∈
    regularGeneralMetricC2LorentzChartDomain period hPeriod plusBase)
  (couplings : GlobalCandidateAActionCouplings)

local notation "Frame" =>
  regularGeneralLorentzMetricSmoothD8Frame period hPeriod plusBase

local notation "Geometry" =>
  regularGeneralMetricC2LorentzChartGeometry period hPeriod plusBase
    (minusBase.metric.tensor - plusBase.metric.tensor) hChart

local notation "MetricCore" =>
  RegularGeneralMetricC2Core period hPeriod plusBase

local notation "PhysicalInput" =>
  FiniteFramePairedC2PhysicalCore period hPeriod Geometry Frame

local notation "MatterInput" =>
  ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
    couplings.matterMassSquared

local notation "OldInput" =>
  FiniteFramePairedC2PhysicalMaxwellSpinCMatterCore period hPeriod Geometry
    Frame couplings

local notation "LLInput" =>
  GlobalMinimalPhysicalLLC0FirstJetPacket period hPeriod
    (canonicalDivergenceFreeLLFrame period hPeriod)

local notation "BulkInput" =>
  FiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCore period hPeriod Geometry
    Frame couplings

local notation "GHYCore" =>
  CandidateANormalBoundaryFunctionalCore period hPeriod plusBase

local notation "GHYInput" => Prod GHYCore Real

local notation "AmbientInput" =>
  FiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYCore period hPeriod
    Geometry Frame couplings plusBase

local instance metricCoreNormedAddCommGroup :
    NormedAddCommGroup MetricCore :=
  (generalMetricRelativeC2CoreSubmodule period hPeriod Frame
    plusBase.metric).normedAddCommGroup

local instance metricCoreNormedSpace : NormedSpace Real MetricCore :=
  Submodule.normedSpace
    (generalMetricRelativeC2CoreSubmodule period hPeriod Frame plusBase.metric)

local instance : NormedSpace Real OldInput := Prod.normedSpace

local instance : NormedSpace Real LLInput := Prod.normedSpace

local instance : NormedSpace Real BulkInput := Prod.normedSpace

local instance coupledGHYFunctionalCoreNormedAddCommGroup :
    NormedAddCommGroup GHYCore :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.candidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    period hPeriod plusBase

local instance coupledGHYFunctionalCoreNormedSpace :
    NormedSpace Real GHYCore :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.candidateANormalBoundaryFunctionalCoreNormedSpace
    period hPeriod plusBase

local instance : NormedSpace Real GHYInput := Prod.normedSpace

local instance : NormedSpace Real AmbientInput := Prod.normedSpace

/-- Plus-metric coordinate of the finite physical bulk packet. -/
def finiteFramePairedC2PhysicalMaxwellSpinCMatterLLBulkPlusMetricProjection :
    BulkInput →L[Real] MetricCore :=
  let oldProjection := ContinuousLinearMap.fst Real OldInput LLInput
  let physicalProjection :=
    (ContinuousLinearMap.fst Real PhysicalInput MatterInput).comp oldProjection
  let metricPairProjection :=
    (ContinuousLinearMap.fst Real
      (MetricCore × MetricCore)
      (FiniteFramePairedC2AbelianGaugeFields period hPeriod Frame Frame ×
        FiniteFrameDiffeomorphismNonminimalC2Core period hPeriod Frame)).comp
      physicalProjection
  (ContinuousLinearMap.fst Real MetricCore MetricCore).comp metricPairProjection

@[simp]
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLBulkPlusMetricProjection_apply
    (input : BulkInput) :
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLBulkPlusMetricProjection
        period hPeriod plusBase minusBase hChart couplings input =
      input.1.1.1.1 :=
  rfl

/-- Metric coordinate of the GHY current after the canonical `C³` to `C²`
forgetful map. -/
def finiteFramePairedC2PhysicalMaxwellSpinCMatterLLGHYMetricProjection :
    GHYInput →L[Real] MetricCore :=
  candidateANormalBoundaryMetricC2Projection period hPeriod plusBase

@[simp]
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLGHYMetricProjection_smooth
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) :
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLGHYMetricProjection
        period hPeriod plusBase
        (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod plusBase
          (tensor, displacement), parameter) =
      regularGeneralMetricSmoothC2Variation period hPeriod plusBase tensor :=
  candidateANormalBoundaryMetricC2Projection_smooth period hPeriod plusBase
    tensor displacement parameter

/-- Linear mismatch between the plus bulk metric and the mobile GHY metric. -/
def finiteFramePairedC2PhysicalMaxwellSpinCMatterLLGHYMetricMismatch :
    AmbientInput →L[Real] MetricCore :=
  (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLBulkPlusMetricProjection
      period hPeriod plusBase minusBase hChart couplings).comp
      (ContinuousLinearMap.fst Real BulkInput GHYInput) -
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLGHYMetricProjection
      period hPeriod plusBase).comp
      (ContinuousLinearMap.snd Real BulkInput GHYInput)

@[simp]
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLGHYMetricMismatch_apply
    (input : AmbientInput) :
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLGHYMetricMismatch period
        hPeriod plusBase minusBase hChart couplings input =
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLBulkPlusMetricProjection
          period hPeriod plusBase minusBase hChart couplings input.1 -
        finiteFramePairedC2PhysicalMaxwellSpinCMatterLLGHYMetricProjection
          period hPeriod plusBase input.2 :=
  rfl

/-- Closed linear graph on which the bulk and GHY metric coordinates agree. -/
abbrev FiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCoupledGHYMetricGraphCore :=
  (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLGHYMetricMismatch period
    hPeriod plusBase minusBase hChart couplings).ker

local notation "CoupledInput" =>
  FiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCoupledGHYMetricGraphCore
    period hPeriod plusBase minusBase hChart couplings

local instance coupledInputNormedAddCommGroup : NormedAddCommGroup CoupledInput :=
  (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLGHYMetricMismatch period
    hPeriod plusBase minusBase hChart couplings).ker.normedAddCommGroup

local instance coupledInputNormedSpace : NormedSpace Real CoupledInput :=
  Submodule.normedSpace
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLGHYMetricMismatch period
      hPeriod plusBase minusBase hChart couplings).ker

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

/-- Exact admissible domain obtained by pulling the mobile product domain back
to the metric graph. -/
def finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCoupledGHYMetricGraphDomain :
    Set CoupledInput :=
  (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLGHYMetricMismatch period
      hPeriod plusBase minusBase hChart couplings).ker.subtypeL ⁻¹'
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYDomain period
      hPeriod Geometry Frame
        (regularGeneralMetricC2LorentzChartGeometry_intrinsicSylvester_bijective
          period hPeriod plusBase
            (minusBase.metric.tensor - plusBase.metric.tensor) hChart)
      couplings plusBase

theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCoupledGHYMetricGraphDomain_isOpen :
    IsOpen
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCoupledGHYMetricGraphDomain
        period hPeriod plusBase minusBase hChart couplings) :=
  (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYDomain_isOpen period
      hPeriod Geometry Frame
        (regularGeneralMetricC2LorentzChartGeometry_intrinsicSylvester_bijective
          period hPeriod plusBase
            (minusBase.metric.tensor - plusBase.metric.tensor) hChart)
      couplings plusBase).preimage
    ((finiteFramePairedC2PhysicalMaxwellSpinCMatterLLGHYMetricMismatch period
      hPeriod plusBase minusBase hChart couplings).ker.subtypeL.continuous)

theorem zero_mem_finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCoupledGHYMetricGraphDomain
    (hMinusCenter :
      finiteFramePairedC2MinusCenter period hPeriod Geometry Frame ∈
        generalMetricRelativeC2VolumeDomain period hPeriod Frame
          (regularGeneralMetricC2LorentzChartGeometry period hPeriod plusBase
            (minusBase.metric.tensor - plusBase.metric.tensor) hChart).plusMetric)
    (hTransverse : HasNoTangentialRadical period hPeriod plusBase.metric) :
    (0 : CoupledInput) ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCoupledGHYMetricGraphDomain
        period hPeriod plusBase minusBase hChart couplings := by
  change (0 : AmbientInput) ∈
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYDomain period
      hPeriod Geometry Frame
        (regularGeneralMetricC2LorentzChartGeometry_intrinsicSylvester_bijective
          period hPeriod plusBase
            (minusBase.metric.tensor - plusBase.metric.tensor) hChart)
      couplings plusBase
  exact
    zero_mem_finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYDomain
      period hPeriod Geometry Frame
        (regularGeneralMetricC2LorentzChartGeometry_intrinsicSylvester_bijective
          period hPeriod plusBase
            (minusBase.metric.tensor - plusBase.metric.tensor) hChart)
      couplings plusBase hMinusCenter hTransverse

/-- The graph equation is precisely the required bulk/GHY `C²` compatibility. -/
theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCoupledGHYMetricGraph_compatible
    (input : CoupledInput) :
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLBulkPlusMetricProjection
        period hPeriod plusBase minusBase hChart couplings input.1.1 =
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLGHYMetricProjection
        period hPeriod plusBase input.1.2 := by
  have hMismatch := input.2
  change
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLBulkPlusMetricProjection
        period hPeriod plusBase minusBase hChart couplings input.1.1 -
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLGHYMetricProjection
        period hPeriod plusBase input.1.2 = 0
    at hMismatch
  exact sub_eq_zero.mp hMismatch

/-- The mobile bulk-plus-GHY action restricted to the metric graph. -/
def finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCoupledGHYMetricGraphAction
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients)
    (input : CoupledInput) : Real :=
  finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYAction period hPeriod
    Geometry Frame
      (regularGeneralMetricC2LorentzChartGeometry_intrinsicSylvester_bijective
        period hPeriod plusBase
          (minusBase.metric.tensor - plusBase.metric.tensor) hChart)
    couplings plusBase data einsteinScale interactionScale coefficients
      ((finiteFramePairedC2PhysicalMaxwellSpinCMatterLLGHYMetricMismatch period
        hPeriod plusBase minusBase hChart couplings).ker.subtypeL input)

/-- Pullback of the mobile Euler covector to compatible directions. -/
def finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCoupledGHYMetricGraphEuler
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients)
    (input : CoupledInput) : CoupledInput →L[Real] Real :=
  (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYEuler period hPeriod
    Geometry Frame
      (regularGeneralMetricC2LorentzChartGeometry_intrinsicSylvester_bijective
        period hPeriod plusBase
          (minusBase.metric.tensor - plusBase.metric.tensor) hChart)
    couplings plusBase data einsteinScale interactionScale coefficients
      ((finiteFramePairedC2PhysicalMaxwellSpinCMatterLLGHYMetricMismatch period
        hPeriod plusBase minusBase hChart couplings).ker.subtypeL input)).comp
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLGHYMetricMismatch period
      hPeriod plusBase minusBase hChart couplings).ker.subtypeL

theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCoupledGHYMetricGraphAction_hasFDerivAt
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients)
    (hTransverse : HasNoTangentialRadical period hPeriod plusBase.metric)
    (input : CoupledInput)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCoupledGHYMetricGraphDomain
        period hPeriod plusBase minusBase hChart couplings) :
    HasFDerivAt
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCoupledGHYMetricGraphAction
        period hPeriod plusBase minusBase hChart couplings data einsteinScale
          interactionScale coefficients)
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCoupledGHYMetricGraphEuler
        period hPeriod plusBase minusBase hChart couplings data einsteinScale
          interactionScale coefficients input)
      input := by
  have hAmbient :
      (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLGHYMetricMismatch period
        hPeriod plusBase minusBase hChart couplings).ker.subtypeL input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYDomain period
        hPeriod Geometry Frame
          (regularGeneralMetricC2LorentzChartGeometry_intrinsicSylvester_bijective
            period hPeriod plusBase
              (minusBase.metric.tensor - plusBase.metric.tensor) hChart)
        couplings plusBase :=
    hInput
  have hAction :=
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYAction_hasFDerivAt
      period hPeriod Geometry Frame
        (regularGeneralMetricC2LorentzChartGeometry_intrinsicSylvester_bijective
          period hPeriod plusBase
            (minusBase.metric.tensor - plusBase.metric.tensor) hChart)
      couplings plusBase data einsteinScale interactionScale coefficients
        hTransverse
          ((finiteFramePairedC2PhysicalMaxwellSpinCMatterLLGHYMetricMismatch
            period hPeriod plusBase minusBase hChart couplings).ker.subtypeL input)
          hAmbient
  let inclusion : CoupledInput →L[Real] AmbientInput :=
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLGHYMetricMismatch period
      hPeriod plusBase minusBase hChart couplings).ker.subtypeL
  have hInclusion : HasFDerivAt inclusion inclusion input :=
    ContinuousLinearMap.hasFDerivAt (𝕜 := Real) inclusion (x := input)
  unfold finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCoupledGHYMetricGraphAction
  unfold finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCoupledGHYMetricGraphEuler
  exact hAction.comp input hInclusion

theorem finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCoupledGHYMetricGraphAction_fderiv
    {configuration : GlobalFieldConfiguration period hPeriod}
    {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (einsteinScale interactionScale : Real)
    (coefficients : PotentialCoefficients)
    (hTransverse : HasNoTangentialRadical period hPeriod plusBase.metric)
    (input : CoupledInput)
    (hInput : input ∈
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCoupledGHYMetricGraphDomain
        period hPeriod plusBase minusBase hChart couplings) :
    fderiv Real
        (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCoupledGHYMetricGraphAction
          period hPeriod plusBase minusBase hChart couplings data einsteinScale
            interactionScale coefficients) input =
      finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCoupledGHYMetricGraphEuler
        period hPeriod plusBase minusBase hChart couplings data einsteinScale
          interactionScale coefficients input :=
  (finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCoupledGHYMetricGraphAction_hasFDerivAt
    period hPeriod plusBase minusBase hChart couplings data einsteinScale
      interactionScale coefficients hTransverse input hInput).fderiv

end
end P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCoupledGHYMetricGraph4D
end JanusFormal
