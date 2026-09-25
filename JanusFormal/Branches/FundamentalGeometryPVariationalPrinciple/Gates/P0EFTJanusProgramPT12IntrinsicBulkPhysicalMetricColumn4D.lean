import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBulkGaugeMatterHessianSplit4D

/-! The full native physical metric column factors through the two actual C² metric slots. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkPhysicalMetricColumn4D
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff

private theorem zero_left_tail {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (H : E →L[Real] E →L[Real] Real) (first second third : E) :
    H first second + H 0 third = H first second := by simp

private theorem zero_pair {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (H : E →L[Real] E →L[Real] Real) (value : E) : H value 0 + H 0 value = 0 := by simp

private theorem drop_right {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (H : E →L[Real] E →L[Real] Real) (first test metric potential : E)
    (hTest : test = metric + potential) (hZero : H first potential = 0) :
    H first test = H first metric := by rw [hTest, map_add, hZero, add_zero]

open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusProgramPGlobalCovariantAction4D P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusFiniteFrameDiffeomorphismC2Core4D
open P0EFTJanusFiniteFrameC2AbelianOperators4D P0EFTJanusFiniteFrameC2AbelianBRSTAction4D
open P0EFTJanusFiniteFramePairedC2FullBRSTGaugeAction4D P0EFTJanusFiniteFramePairedC2PhysicalAction4D
open P0EFTJanusFiniteFrameC2MobileMaxwellAction4D P0EFTJanusFiniteFramePairedC2PhysicalMaxwellAction4D
open P0EFTJanusProgramPT12IntrinsicBulkGeometry4D P0EFTJanusProgramPT12IntrinsicBulkActionCore4D
open P0EFTJanusProgramPT12IntrinsicBulkPhysicalProjection4D
open P0EFTJanusProgramPT12IntrinsicBulkAbelianLorenz4D P0EFTJanusProgramPT12IntrinsicBulkAbelianBARestriction4D
open P0EFTJanusProgramPT12FrameFreeMaxwellBilinear4D
open P0EFTJanusProgramPT12FrameFreeMaxwellMetricPotentialHessian4D
open P0EFTJanusReciprocalBimetricPotential
attribute [local instance 2000]
  NonUnitalNormedRing.toNormedAddCommGroup NormedAlgebra.toNormedSpace

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev Q := MappingTorus (reflectedSphereData period hPeriod)
private abbrev Throat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace CoverModel (Q period hPeriod) := reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (Q period hPeriod) := reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (Q period hPeriod) := reflectedSphereQuotientCompactSpace period hPeriod
local instance : ChartedSpace ThroatCoverModel (Throat period hPeriod) := fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (Throat period hPeriod) := fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (Throat period hPeriod) := fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (Throat period hPeriod) := borel _
local instance : BorelSpace (Throat period hPeriod) where measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod
local instance : NormedAddCommGroup (CanonicalPhysicalScalarC2JetCore period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (CanonicalPhysicalScalarC2JetCore period hPeriod) := inferInstance
local instance : CompleteSpace (CanonicalPhysicalScalarC2JetCore period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod
local instance : InnerProductSpace Real ProgramPPrimitiveSpinCMatterHilbert := InnerProductSpace.complexToReal
local notation "frame" => finiteSmoothTangentFrame period hPeriod
local notation "metric" => GlobalCandidateAGeometry.plusMetric (intrinsicBulkGeometry period hPeriod)
local notation "Metric" => GeneralMetricRelativeC2Core period hPeriod frame metric
local notation "Gauge" => FiniteFrameAbelianGaugeC2Core period hPeriod frame
local notation "Nonminimal" => FiniteFrameAbelianNonminimalC2Core period hPeriod
local notation "Diffeomorphism" => FiniteFrameDiffeomorphismNonminimalC2Core period hPeriod frame
local notation "PhysicalCore" => FiniteFramePairedC2PhysicalCore period hPeriod (intrinsicBulkGeometry period hPeriod) frame
local notation "Fields" => FiniteFramePairedC2AbelianGaugeFields period hPeriod frame frame
local instance : NormedAddCommGroup Metric := inferInstance
local instance : NormedSpace Real Metric := Submodule.normedSpace (GeneralMetricRelativeC2Core period hPeriod frame metric)
local instance : NormedAddCommGroup (Metric × Metric) := inferInstance
local instance : NormedAddCommGroup Gauge := inferInstance
local instance : NormedSpace Real Gauge := inferInstance
local instance : NormedAddCommGroup Nonminimal := inferInstance
local instance : NormedAddCommGroup Diffeomorphism := inferInstance
variable (couplings : GlobalCandidateAActionCouplings)
local notation "Core" => IntrinsicBulkCore period hPeriod couplings
local notation "ACore" => IntrinsicBulkAbelianACore period hPeriod
local instance coreNormedAddCommGroup : NormedAddCommGroup Core := inferInstance
local instance : AddZeroClass Core := (coreNormedAddCommGroup period hPeriod couplings).toAddCommGroup.toAddZeroClass
local instance coreNormedSpace : NormedSpace Real Core :=
  P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D.instNormedSpaceRealFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCore
    period hPeriod (intrinsicBulkGeometry period hPeriod) frame couplings
local instance coreModule : Module Real Core := (coreNormedSpace period hPeriod couplings).toModule
local instance coreMulAction : MulAction Real Core :=
  (coreModule period hPeriod couplings).toDistribMulAction.toMulAction
local instance : SMul Real Core := (coreMulAction period hPeriod couplings).toSMul
local instance metricPairNormedSpace : NormedSpace Real (Metric × Metric) := inferInstance
local instance metricPairModule : Module Real (Metric × Metric) := (metricPairNormedSpace period hPeriod).toModule
local instance metricPairMulAction : MulAction Real (Metric × Metric) :=
  (metricPairModule period hPeriod).toDistribMulAction.toMulAction
local instance : SMul Real (Metric × Metric) := (metricPairMulAction period hPeriod).toSMul
local instance nonminimalNormedSpace : NormedSpace Real Nonminimal := inferInstance
local instance nonminimalModule : Module Real Nonminimal := (nonminimalNormedSpace period hPeriod).toModule
local instance nonminimalMulAction : MulAction Real Nonminimal :=
  (nonminimalModule period hPeriod).toDistribMulAction.toMulAction
local instance : SMul Real Nonminimal := (nonminimalMulAction period hPeriod).toSMul
local instance diffeomorphismNormedSpace : NormedSpace Real Diffeomorphism := inferInstance
local instance diffeomorphismModule : Module Real Diffeomorphism := (diffeomorphismNormedSpace period hPeriod).toModule
local instance diffeomorphismMulAction : MulAction Real Diffeomorphism :=
  (diffeomorphismModule period hPeriod).toDistribMulAction.toMulAction
local instance : SMul Real Diffeomorphism := (diffeomorphismMulAction period hPeriod).toSMul
local instance : NormedAddCommGroup (Gauge × Nonminimal) := inferInstance
local instance : NormedSpace Real (Gauge × Nonminimal) := Prod.normedSpace
local instance : NormedAddCommGroup Fields := inferInstance
local instance : NormedSpace Real Fields := Prod.normedSpace
local instance : NormedAddCommGroup (Fields × Diffeomorphism) := inferInstance
local instance : NormedSpace Real (Fields × Diffeomorphism) := Prod.normedSpace
local instance : NormedAddCommGroup PhysicalCore := inferInstance
local instance : NormedSpace Real PhysicalCore := Prod.normedSpace
local notation "Matter" => ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod couplings.matterMassSquared
local instance : NormedAddCommGroup Matter := inferInstance
local instance : NormedSpace Real Matter := inferInstance
local instance : NormedAddCommGroup (PhysicalCore × Matter) := inferInstance
local instance : NormedSpace Real (PhysicalCore × Matter) := Prod.normedSpace
local instance : NormedAddCommGroup ACore := inferInstance
local instance : NormedSpace Real ACore := inferInstance
local instance : NormedAddCommGroup (Gauge →L[Real] Real) := inferInstance
local instance : NormedSpace Real (Gauge →L[Real] Real) := inferInstance
local instance : NormedAddCommGroup (Gauge →L[Real] Gauge →L[Real] Real) := inferInstance
local instance : NormedSpace Real (Gauge →L[Real] Gauge →L[Real] Real) := inferInstance

open P0EFTJanusProgramPT12IntrinsicBulkPhysicalHessian4D
open P0EFTJanusProgramPT12IntrinsicBulkBRSTDecomposition4D

open P0EFTJanusProgramPT12IntrinsicBulkGaugeMatterHessianSplit4D
open P0EFTJanusProgramPT12IntrinsicBulkMaxwellRestriction4D
open P0EFTJanusProgramPT12IntrinsicBulkMaxwellColumn4D
local notation "Metrics" => Metric × Metric
local instance : NormedSpace Real Metrics := Prod.normedSpace

def intrinsicBulkMetricInsertion : Metrics →L[Real] Core :=
  let p : Metrics →L[Real] PhysicalCore := (ContinuousLinearMap.id Real Metrics).prod 0
  (p.prod 0).prod 0

def intrinsicBulkMetricReadout : Core →L[Real] Metrics :=
  (ContinuousLinearMap.fst Real _ _).comp
    ((ContinuousLinearMap.fst Real PhysicalCore Matter).comp (ContinuousLinearMap.fst Real _ _))

@[simp] theorem intrinsicBulkMetricInsertion_apply (fields : Metrics) :
    intrinsicBulkMetricInsertion period hPeriod couplings fields = (((fields, 0), 0), 0) := rfl

@[simp] theorem intrinsicBulkMetricReadout_apply (test : Core) :
    intrinsicBulkMetricReadout period hPeriod couplings test = test.1.1.1 := rfl

local notation "insert" => intrinsicBulkMetricInsertion period hPeriod couplings
local notation "readout" => intrinsicBulkMetricReadout period hPeriod couplings
local notation "potInsert" => intrinsicBulkAbelianAInsertion period hPeriod couplings
local notation "potReadout" => intrinsicBulkAbelianPotentialReadout period hPeriod couplings
local notation "gaugePart" => intrinsicBulkGaugePart period hPeriod couplings
local notation "physical" => intrinsicBulkPhysicalProjection period hPeriod couplings

private theorem test_split (test : Core) :
    physical (gaugePart test) = insert (readout test) + potInsert (potReadout test) := by
  simp only [intrinsicBulkPhysicalProjection_apply, intrinsicBulkGaugePart_apply,
    intrinsicBulkMetricInsertion_apply, intrinsicBulkMetricReadout_apply,
    intrinsicBulkAbelianAInsertion_apply, intrinsicBulkAbelianAFields,
    intrinsicBulkAbelianPotentialReadout_apply, Prod.mk_add_mk,
    zero_add, add_zero]
  rfl

variable (interactionScale : Real) (coefficients : PotentialCoefficients)
local notation "hessian" => intrinsicBulkPhysicalHessian period hPeriod couplings interactionScale coefficients

private theorem metric_potential_zero (fields : Metrics) (potential : ACore) :
    hessian (insert fields) (potInsert potential) = 0 :=
  (intrinsicBulkPhysicalHessian_symmetric period hPeriod couplings interactionScale coefficients _ _).trans
    ((intrinsicBulkPhysicalHessian_potential_column period hPeriod couplings interactionScale coefficients potential
      (insert fields)).trans (zero_pair (intrinsicBulkMaxwellPairing period hPeriod couplings) potential))

/-- Matter, LL, Abelian and nonminimal test slots are eliminated by proved identities. -/
theorem intrinsicBulkPhysicalHessian_metric_test_projection (fields : Metrics) (test : Core) :
    hessian (insert fields) test = hessian (insert fields) (insert (readout test)) := by
  have hSplit := intrinsicBulkPhysicalHessian_gauge_matter_split period hPeriod couplings
    interactionScale coefficients (insert fields) test
  have hGauge : hessian (insert fields) test = hessian (insert fields) (gaugePart test) :=
    hSplit.trans (zero_left_tail hessian (insert fields) (gaugePart test)
      (intrinsicBulkMatterLLPart period hPeriod couplings test))
  have hPhysical : hessian (insert fields) (gaugePart test) = hessian (insert fields) (physical (gaugePart test)) :=
    (intrinsicBulkPhysicalHessian_apply period hPeriod couplings interactionScale coefficients _ _).trans
      (intrinsicBulkPhysicalHessian_apply period hPeriod couplings interactionScale coefficients
        (insert fields) (physical (gaugePart test))).symm
  exact hGauge.trans (hPhysical.trans (drop_right hessian (insert fields) _ _ _
    (test_split period hPeriod couplings test)
    (metric_potential_zero period hPeriod couplings interactionScale coefficients fields (potReadout test))))

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkPhysicalMetricColumn4D
