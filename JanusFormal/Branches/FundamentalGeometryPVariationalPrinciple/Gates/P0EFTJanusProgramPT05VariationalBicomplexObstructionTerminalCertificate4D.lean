import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT05CanonicalVerticalIntegrationEvaluation4D

/-!
# Terminal variational-bicomplex obstruction certificate for T05

The terminal criterion certified here is the literal relative variational
bicomplex obstruction statement built in Gate 819.  Its horizontal and
vertical differentials are nonzero and obey the bicomplex and incidence laws;
the exact first variation has a nonzero Euler obstruction cochain which is a
horizontal boundary, hence represents the zero horizontal-cohomology class.
The distinguished cochains evaluate to the exact T03 action and Euler
covector, and Gate 841 supplies the commuting vertical-evaluation square.

Geometric supports for the incidence maps, vertical differentials of every
local sector, differentiation under their integrals, atlas naturality and
gluing, and global geometric exactness/vanishing are stronger follow-up
objectives.  They are deliberately not assumptions of this certificate.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT05VariationalBicomplexObstructionTerminalCertificate4D

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 900000
set_option maxRecDepth 2000
noncomputable section

attribute [local instance 2000]
  NonUnitalNormedRing.toNormedAddCommGroup NormedAlgebra.toNormedSpace

attribute [local instance 100]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

open Set MeasureTheory
open scoped Manifold ContDiff BigOperators InnerProductSpace Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLStrongEquation4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalBoundaryCompletion4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartGeometry4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLLAuxMeasureTotalEuler4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC3MetricCore4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC2LorentzGHYDomain4D
open P0EFTJanusNullJointReparametrizationCancellation
open P0EFTJanusFiniteNullFaceAction
open P0EFTJanusProgramPGlobalBoundaryReparametrizationHilbertHessian4D
open P0EFTJanusFiniteFramePairedC2PhysicalAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYProductEuler4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalProductEuler4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCoupledGHYMetricGraph4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCompletion4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalCoveredAtlas4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSeparatingPDEResidual4D
open P0EFTJanusProgramPT03FullEulerLagrangeTerminalCertificate4D
open P0EFTJanusProgramPRelativeJetVariationalBicomplexCore4D
open P0EFTJanusProgramPRelativeJetVariationalBicomplexCore4D.RelativeJetStratum4D
open P0EFTJanusProgramPRelativeVariationalObstructionExactness4D
open P0EFTJanusProgramPRelativeVariationalObstructionExactness4D.RelativeFirstVariationData
open P0EFTJanusProgramPT05ExactT03RelativeVariationalRealization4D
open P0EFTJanusProgramPT05CanonicalVerticalIntegrationEvaluation4D
open P0EFTJanusProgramPT04FullBRSTC2Helmholtz4D
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusReciprocalBimetricPotential
open P0EFTJanusFiniteNullFaceMobileCanonicalFaithfulness4D

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

local instance : Measure.IsOpenPosMeasure
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isOpenPosMeasure period hPeriod

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

local notation "OldInput" =>
  FiniteFramePairedC2PhysicalMaxwellSpinCMatterCore period hPeriod Geometry
    Frame couplings

local notation "LLInput" =>
  GlobalMinimalPhysicalLLC0FirstJetPacket period hPeriod
    (canonicalDivergenceFreeLLFrame period hPeriod)

local notation "CompatibleLL" => CompatibleLLCompletion period hPeriod

local notation "BulkInput" =>
  FiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCore period hPeriod Geometry
    Frame couplings

local notation "GHYCore" =>
  CandidateANormalBoundaryFunctionalCore period hPeriod plusBase

local notation "GHYInput" => GHYCore × Real

local notation "AmbientInput" =>
  FiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYCore period hPeriod
    Geometry Frame couplings plusBase

local notation "MetricBoundaryAmbient" => OldInput × GHYInput

local notation "MetricBoundary" =>
  FiniteFramePairedC2PhysicalMaxwellSpinCMatterMetricBoundaryGraphCore period
    hPeriod plusBase minusBase hChart couplings

local notation "CompletedCoupled" =>
  FiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYCore
    period hPeriod plusBase minusBase hChart couplings

local instance metricCoreNormedAddCommGroup : NormedAddCommGroup MetricCore :=
  (generalMetricRelativeC2CoreSubmodule period hPeriod Frame
    plusBase.metric).normedAddCommGroup

local instance metricCoreNormedSpace : NormedSpace Real MetricCore :=
  Submodule.normedSpace
    (generalMetricRelativeC2CoreSubmodule period hPeriod Frame plusBase.metric)

local instance : NormedSpace Real OldInput := Prod.normedSpace
local instance : NormedSpace Real LLInput := Prod.normedSpace
local instance : NormedSpace Real BulkInput := Prod.normedSpace

local instance frontierGHYCoreNormedAddCommGroup : NormedAddCommGroup GHYCore :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.candidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    period hPeriod plusBase

local instance frontierGHYCoreNormedSpace : NormedSpace Real GHYCore :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.candidateANormalBoundaryFunctionalCoreNormedSpace
    period hPeriod plusBase

local instance : NormedSpace Real GHYInput := Prod.normedSpace
local instance terminalMetricBoundaryAmbientSMul : SMul Real MetricBoundaryAmbient :=
  Prod.instSMul
local instance : ContinuousSMul Real MetricBoundaryAmbient := by
  apply Prod.continuousSMul
local instance : NormedSpace Real MetricBoundaryAmbient := Prod.normedSpace
local instance terminalAmbientInputSMul : SMul Real AmbientInput := Prod.instSMul
local instance : ContinuousSMul Real LLInput := by apply Prod.continuousSMul
local instance : ContinuousSMul Real BulkInput := by apply Prod.continuousSMul
local instance : ContinuousSMul Real GHYInput := by apply Prod.continuousSMul
local instance : ContinuousSMul Real AmbientInput := by apply Prod.continuousSMul
local instance : NormedSpace Real AmbientInput := Prod.normedSpace

local instance terminalCompatibleLLNormedAddCommGroup :
    NormedAddCommGroup CompatibleLL :=
  (compatibleLLCompletionSubmodule period hPeriod).normedAddCommGroup

local instance terminalCompatibleLLNormedSpace : NormedSpace Real CompatibleLL :=
  Submodule.normedSpace (compatibleLLCompletionSubmodule period hPeriod)

local instance terminalMetricBoundarySMul : SMul Real MetricBoundary :=
  SetLike.smul
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterOldGHYMetricMismatch period
      hPeriod plusBase minusBase hChart couplings).ker

local instance terminalMetricBoundaryNormedAddCommGroup :
    NormedAddCommGroup MetricBoundary :=
  (finiteFramePairedC2PhysicalMaxwellSpinCMatterOldGHYMetricMismatch period
    hPeriod plusBase minusBase hChart couplings).ker.normedAddCommGroup

local instance terminalMetricBoundaryNormedSpace : NormedSpace Real MetricBoundary :=
  Submodule.normedSpace
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterOldGHYMetricMismatch period
      hPeriod plusBase minusBase hChart couplings).ker

local instance terminalMetricBoundaryContinuousSMul :
    ContinuousSMul Real MetricBoundary :=
  SMulMemClass.continuousSMul
    (finiteFramePairedC2PhysicalMaxwellSpinCMatterOldGHYMetricMismatch period
      hPeriod plusBase minusBase hChart couplings).ker

local instance : NormedSpace Real CompletedCoupled := Prod.normedSpace
local instance : ContinuousSMul Real CompletedCoupled := by
  apply Prod.continuousSMul

universe uNull

section

variable {NullFace : Type uNull} [Fintype NullFace]
  (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)

local notation "Model" => faithful.toPhysicalActionRealization.toActionModel

local notation "NullNormalization" =>
  GlobalCandidateABoundaryReparametrizationHilbert NullFace

local notation "PriorInput" => CompletedCoupled × NullNormalization

local notation "Input" =>
  FiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalCore
    period hPeriod plusBase minusBase hChart couplings (NullFace := NullFace)

local instance terminalPriorInputSMul : SMul Real PriorInput := Prod.instSMul
local instance : NormedSpace Real PriorInput := Prod.normedSpace
local instance : ContinuousSMul Real PriorInput := by apply Prod.continuousSMul
local instance terminalInputSMul : SMul Real Input := Prod.instSMul
local instance : NormedSpace Real Input := Prod.normedSpace
local instance : ContinuousSMul Real Input := by apply Prod.continuousSMul

variable {configuration : GlobalFieldConfiguration period hPeriod}
  {NonNullFace : Type*} [Fintype NonNullFace]
  (data : GlobalCandidateAActionData period hPeriod configuration couplings
    NonNullFace NullFace)
  (einsteinScale interactionScale : Real)
  (coefficients : PotentialCoefficients)

local notation "Bicomplex" => programPT05ExactT03RelativeBicomplex
local notation "JetComponent" => ProgramPT05PhysicalJetComponent
local notation "Lagrangian" => programPT05RelativeLagrangian
local notation "BoundaryPotential" => programPT05RelativeBoundaryPotential
local notation "EulerCochain" => programPT05RelativeEuler

local notation "ExactAction" =>
  finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalAction
    period hPeriod plusBase minusBase hChart couplings data Model einsteinScale
      interactionScale coefficients

local notation "ExactEuler" =>
  finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalEuler
    period hPeriod plusBase minusBase hChart couplings data Model einsteinScale
      interactionScale coefficients

local notation "Domain" =>
  finiteFramePairedC2PhysicalMaxwellSpinCMatterLLCompatibleCoupledGHYNullPhysicalDomain
    period hPeriod plusBase minusBase hChart couplings Model

/-- The exact terminal T05 criterion on Gate 819's fixed relative
variational bicomplex and the exact T03 action/Euler pair. -/
structure ProgramPT05VariationalBicomplexObstructionTerminalCertificate4D : Prop where
  horizontal_differential_ne_zero : (Bicomplex).dH 0 0 ≠ 0
  vertical_differential_ne_zero : (Bicomplex).dV 0 0 ≠ 0
  horizontal_squared :
    ∀ (p q : Nat) (cochain : RelativeJetCochain JetComponent p q),
      (Bicomplex).dH (p + 1) q ((Bicomplex).dH p q cochain) = 0
  vertical_squared :
    ∀ (p q : Nat) (cochain : RelativeJetCochain JetComponent p q),
      (Bicomplex).dV p (q + 1) ((Bicomplex).dV p q cochain) = 0
  mixed_anticommutes :
    ∀ (p q : Nat) (cochain : RelativeJetCochain JetComponent p q),
      (Bicomplex).dV (p + 1) q ((Bicomplex).dH p q cochain) +
          (Bicomplex).dH p (q + 1) ((Bicomplex).dV p q cochain) = 0
  horizontal_respects_incidence :
    ∀ (p q : Nat) (source : RelativeJetStratum4D)
      (cochain : RelativeJetCochain JetComponent p q),
      cochain.SupportedOn source →
      ∀ target : RelativeJetStratum4D,
        ¬ RelativeJetStratum4D.HorizontalIncidenceAllowed source target →
        (Bicomplex).dH p q cochain target = 0
  vertical_preserves_stratum :
    ∀ (p q : Nat) (source : RelativeJetStratum4D)
      (cochain : RelativeJetCochain JetComponent p q),
      cochain.SupportedOn source →
      ∀ target : RelativeJetStratum4D,
        target ≠ source → (Bicomplex).dV p q cochain target = 0
  first_variation :
    (Bicomplex).dV 4 0 Lagrangian =
      EulerCochain + (Bicomplex).dH 3 1 BoundaryPotential
  obstruction_is_horizontal_boundary :
    (Bicomplex).dV 4 1 EulerCochain =
      (Bicomplex).dH 3 2 ((Bicomplex).dV 3 1 BoundaryPotential)
  obstruction_cochain_ne_zero : (Bicomplex).dV 4 1 EulerCochain ≠ 0
  obstruction_class_eq_zero :
    programPT05ExactT03RelativeFirstVariation.eulerObstructionClass = 0
  lagrangian_evaluates_to_exact_action :
    ∀ input : Input,
      programPT05ExactT03ActionEvaluation period hPeriod plusBase minusBase
          hChart couplings data Model einsteinScale interactionScale
            coefficients input Lagrangian =
        ExactAction input
  dV_lagrangian_evaluates_to_exact_euler :
    ∀ (input direction : Input),
      programPT05ExactT03EulerEvaluation period hPeriod plusBase minusBase
          hChart couplings data Model einsteinScale interactionScale
            coefficients input direction ((Bicomplex).dV 4 0 Lagrangian) =
        ExactEuler input direction
  euler_cochain_evaluates_to_exact_euler :
    ∀ (input direction : Input),
      programPT05ExactT03EulerEvaluation period hPeriod plusBase minusBase
          hChart couplings data Model einsteinScale interactionScale
            coefficients input direction EulerCochain =
        ExactEuler input direction
  euler_eq_actionGradient :
    ∀ input : Input, input ∈ Domain →
      ExactEuler input = actionGradient ExactAction input
  canonical_evaluation_commutes_dV :
    ∀ (input : Input) (_hInput : input ∈ Domain) (direction : Input),
      fderiv Real
          (fun varied : Input ↦
            programPT05ExactT03ActionEvaluation period hPeriod plusBase
              minusBase hChart couplings data Model einsteinScale
                interactionScale coefficients varied Lagrangian)
          input direction =
        programPT05ExactT03EulerEvaluation period hPeriod plusBase minusBase
          hChart couplings data Model einsteinScale interactionScale
            coefficients input direction ((Bicomplex).dV 4 0 Lagrangian)

/-- Public terminal T05 theorem for the exact relative variational obstruction
criterion. -/
theorem program_p_t05_variational_bicomplex_obstruction_terminal_gate
    (hTransverse : HasNoTangentialRadical period hPeriod plusBase.metric) :
    ProgramPT05VariationalBicomplexObstructionTerminalCertificate4D period
      hPeriod plusBase minusBase hChart couplings faithful data einsteinScale
        interactionScale coefficients where
  horizontal_differential_ne_zero :=
    programPT05RelativeHorizontalDifferential_ne_zero
  vertical_differential_ne_zero :=
    programPT05RelativeVerticalDifferential_ne_zero
  horizontal_squared := (Bicomplex).dH_dH
  vertical_squared := (Bicomplex).dV_dV
  mixed_anticommutes := (Bicomplex).mixed_anticommutes
  horizontal_respects_incidence := (Bicomplex).dH_respects_incidence
  vertical_preserves_stratum := (Bicomplex).dV_preserves_stratum
  first_variation := programPT05CanonicalRelativeFirstVariation
  obstruction_is_horizontal_boundary :=
    programPT05ExactT03RelativeFirstVariation.euler_obstruction_eq_horizontal_boundary
  obstruction_cochain_ne_zero := programPT05RelativeEulerObstruction_ne_zero
  obstruction_class_eq_zero :=
    programPT05ExactT03RelativeObstructionClass_eq_zero
  lagrangian_evaluates_to_exact_action := by
    intro input
    exact programPT05RelativeLagrangian_evaluates_to_exactT03Action period
      hPeriod plusBase minusBase hChart couplings data Model einsteinScale
        interactionScale coefficients input
  dV_lagrangian_evaluates_to_exact_euler := by
    intro input direction
    exact programPT05_dV_lagrangian_evaluates_to_exactT03Euler period hPeriod
      plusBase minusBase hChart couplings data Model einsteinScale
        interactionScale coefficients input direction
  euler_cochain_evaluates_to_exact_euler := by
    intro input direction
    exact programPT05RelativeEuler_evaluates_to_exactT03Euler period hPeriod
      plusBase minusBase hChart couplings data Model einsteinScale
        interactionScale coefficients input direction
  euler_eq_actionGradient := by
    intro input hInput
    exact programPT05ExactT03Euler_eq_actionGradient period hPeriod plusBase
      minusBase hChart couplings Model data einsteinScale interactionScale
        coefficients hTransverse input hInput
  canonical_evaluation_commutes_dV := by
    intro input hInput direction
    exact programPT05CanonicalLagrangianEvaluation_commutes_dV period hPeriod
      plusBase minusBase hChart couplings data Model einsteinScale
        interactionScale coefficients hTransverse input hInput direction

end

end
end P0EFTJanusProgramPT05VariationalBicomplexObstructionTerminalCertificate4D
end JanusFormal
