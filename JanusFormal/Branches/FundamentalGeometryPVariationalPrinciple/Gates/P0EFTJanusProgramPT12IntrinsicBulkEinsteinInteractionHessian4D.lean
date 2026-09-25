import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBulkPhysicalMetricColumn4D

/-! The remaining physical metric column is exactly the native Einstein--interaction Hessian. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkEinsteinInteractionHessian4D
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusProgramPT12AffineHessianPullback4D

private theorem bilinear_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (B : E →L[Real] E →L[Real] Real) : B 0 0 = 0 := by simp

private theorem constant_restriction_hessian {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E] [NormedAddCommGroup F] [NormedSpace Real F]
    (f : E → Real) (g : F → Real) (j : F →L[Real] E) (c : Real)
    (hf : ContDiffAt Real 2 f 0) (hRestrict : ∀ x, f (j x) = g x + c) (first second : F) :
    fderiv Real (fderiv Real f) 0 (j first) (j second) =
      fderiv Real (fderiv Real g) 0 first second := by
  have hPull : fderiv Real (fderiv Real (fun x => f (j x))) 0 first second =
      fderiv Real (fderiv Real f) 0 (j first) (j second) := by
    simpa only [one_mul, zero_add] using scaledAffineHessian f 0 j 1 hf first second
  have hAction : (fun x => f (j x)) = (fun x => g x + c) := funext hRestrict
  have hGradient : fderiv Real (fun x => g x + c) = fderiv Real g :=
    funext fun x => fderiv_add_const (𝕜 := Real) (f := g) (x := x) c
  rw [hAction, hGradient] at hPull
  exact hPull.symm

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

open P0EFTJanusProgramPT12IntrinsicBulkPhysicalMetricColumn4D
open P0EFTJanusFiniteFrameC2EinsteinHilbertAction4D
open P0EFTJanusFiniteFramePairedC2InteractionAction4D
local notation "insert" => intrinsicBulkMetricInsertion period hPeriod couplings
local notation "readout" => intrinsicBulkMetricReadout period hPeriod couplings
variable (interactionScale : Real) (coefficients : PotentialCoefficients)
local notation "action" => intrinsicBulkPhysicalAction period hPeriod couplings interactionScale coefficients
local notation "physicalHessian" => intrinsicBulkPhysicalHessian period hPeriod couplings interactionScale coefficients

/-- The two actual Einstein actions and the actual reciprocal interaction; no Riesz hypothesis. -/
def intrinsicBulkEinsteinInteractionAction (fields : Metrics) : Real :=
  finiteFramePairedC2EinsteinHilbertAction period hPeriod frame frame metric metric
    couplings.plusEinstein couplings.minusEinstein fields +
  pairedFiniteFrameC2InteractionAction period hPeriod (intrinsicBulkGeometry period hPeriod) frame
    (intrinsicBulkGeometry_sylvester_bijective period hPeriod) interactionScale coefficients fields
local notation "geometric" => intrinsicBulkEinsteinInteractionAction period hPeriod couplings interactionScale coefficients

theorem intrinsicBulkPhysicalAction_metric_restriction (fields : Metrics) :
    action (insert fields) = geometric fields + (action 0 - geometric 0) := by
  simp only [intrinsicBulkEinsteinInteractionAction, intrinsicBulkPhysicalAction_eq_summands,
    intrinsicBulkMetricInsertion_apply, finiteFramePairedC2PhysicalMaxwellProjection_apply,
    finiteFramePairedC2MobileMaxwellAction, Prod.fst_zero, Prod.snd_zero,
    frameFreeMobileMaxwellAction_eq_bilinear, bilinear_zero, mul_zero, add_zero]
  ring

theorem intrinsicBulkEinsteinInteractionAction_contDiffAt_zero : ContDiffAt Real 2 geometric 0 := by
  have hBase : ContDiffAt Real 2 action (insert 0) := by
    change ContDiffAt Real 2 action 0
    exact intrinsicBulkPhysicalAction_contDiffAt_zero period hPeriod couplings interactionScale coefficients
  have hComposition := hBase.comp 0 (insert).contDiff.contDiffAt
  have hAction : geometric = (fun fields => action (insert fields) - (action 0 - geometric 0)) := by
    funext fields
    exact (eq_sub_iff_add_eq.mpr
      (intrinsicBulkPhysicalAction_metric_restriction period hPeriod couplings interactionScale coefficients fields).symm)
  rw [hAction]
  exact hComposition.sub contDiffAt_const

def intrinsicBulkEinsteinInteractionHessian : Metrics →L[Real] Metrics →L[Real] Real :=
  fderiv Real (fderiv Real geometric) 0

theorem intrinsicBulkPhysicalHessian_metric_metric (first second : Metrics) :
    physicalHessian (insert first) (insert second) =
      intrinsicBulkEinsteinInteractionHessian period hPeriod couplings interactionScale coefficients first second :=
  constant_restriction_hessian action geometric insert (action 0 - geometric 0)
    (intrinsicBulkPhysicalAction_contDiffAt_zero period hPeriod couplings interactionScale coefficients)
    (intrinsicBulkPhysicalAction_metric_restriction period hPeriod couplings interactionScale coefficients)
    first second

/-- Against every bulk test, only the two C² metric readouts enter the physical metric column. -/
theorem intrinsicBulkPhysicalHessian_metric_column (first : Metrics) (test : Core) :
    physicalHessian (insert first) test =
      intrinsicBulkEinsteinInteractionHessian period hPeriod couplings interactionScale coefficients first (readout test) :=
  (intrinsicBulkPhysicalHessian_metric_test_projection period hPeriod couplings
    interactionScale coefficients first test).trans
      (intrinsicBulkPhysicalHessian_metric_metric period hPeriod couplings interactionScale coefficients first (readout test))

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkEinsteinInteractionHessian4D
