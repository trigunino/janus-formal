import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBulkMaxwellColumn4D

/-! Exact separation of the native physical metric/gauge and matter/LL Hessian blocks. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkGaugeMatterHessianSplit4D
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Manifold ContDiff Topology
open P0EFTJanusProgramPT12AffineHessianPullback4D
private theorem contDiffAt_linear_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (f : E → Real) (projection : E →L[Real] E) (hf : ContDiffAt Real 2 f 0) :
    ContDiffAt Real 2 (fun x => f (projection x)) 0 := by
  have hAt : ContDiffAt Real 2 f (projection 0) := by
    simpa only [projection.map_zero] using hf
  exact hAt.comp 0 projection.contDiff.contDiffAt

private theorem second_fderiv_of_add
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (f p g : E → Real) (hSplit : ∀ x, f x = p x + g x)
    (hp : ContDiffAt Real 2 p 0) (hg : ContDiffAt Real 2 g 0) :
    fderiv Real (fderiv Real f) 0 =
      fderiv Real (fderiv Real p) 0 + fderiv Real (fderiv Real g) 0 := by
  have hFunction : f = fun x => p x + g x := funext hSplit
  have hNearP : ∀ᶠ x in 𝓝 (0 : E), DifferentiableAt Real p x :=
    (hp.eventually (by norm_num)).mono (fun _ h => h.differentiableAt (by norm_num))
  have hNearG : ∀ᶠ x in 𝓝 (0 : E), DifferentiableAt Real g x :=
    (hg.eventually (by norm_num)).mono (fun _ h => h.differentiableAt (by norm_num))
  have hGradient : fderiv Real f =ᶠ[𝓝 (0 : E)]
      (fun x => fderiv Real p x + fderiv Real g x) := by
    filter_upwards [hNearP, hNearG] with x hP hG
    rw [hFunction]
    exact (hP.hasFDerivAt.add hG.hasFDerivAt).fderiv
  have hSecondP := (hp.fderiv_right (show (1 : ℕ∞ω) + 1 ≤ 2 by norm_num)).differentiableAt
    (by norm_num)
  have hSecondG := (hg.fderiv_right (show (1 : ℕ∞ω) + 1 ≤ 2 by norm_num)).differentiableAt
    (by norm_num)
  exact hGradient.fderiv_eq.trans (hSecondP.hasFDerivAt.add hSecondG.hasFDerivAt).fderiv

private theorem separated_hessian {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (f : E → Real) (P Q : E →L[Real] E) (hf : ContDiffAt Real 2 f 0)
    (hSplit : ∀ x, f x = f (P x) + (f (Q x) - f 0)) (first second : E) :
    fderiv Real (fderiv Real f) 0 first second =
      fderiv Real (fderiv Real f) 0 (P first) (P second) +
        fderiv Real (fderiv Real f) 0 (Q first) (Q second) := by
  have hP := contDiffAt_linear_zero f P hf
  have hQ := contDiffAt_linear_zero f Q hf
  have h := second_fderiv_of_add f (fun x => f (P x)) (fun x => f (Q x) - f 0)
    hSplit hP (hQ.sub contDiffAt_const)
  have hGradient : fderiv Real (fun x => f (Q x) - f 0) = fderiv Real (fun x => f (Q x)) :=
    funext fun x => fderiv_sub_const (𝕜 := Real) (f := fun y => f (Q y)) (x := x) (f 0)
  rw [hGradient] at h
  have hPull (R : E →L[Real] E) :
      fderiv Real (fderiv Real (fun x => f (R x))) 0 first second =
        fderiv Real (fderiv Real f) 0 (R first) (R second) := by
    simpa only [one_mul, zero_add] using scaledAffineHessian f 0 R 1 hf first second
  exact (congrArg (fun form : E →L[Real] E →L[Real] Real => form first second) h).trans
    (congrArg₂ (fun x y : Real => x + y) (hPull P) (hPull Q))

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

def intrinsicBulkGaugePart : Core →L[Real] Core :=
  let p : Core →L[Real] PhysicalCore :=
    (ContinuousLinearMap.fst Real PhysicalCore Matter).comp (ContinuousLinearMap.fst Real _ _)
  (p.prod 0).prod 0

def intrinsicBulkMatterLLPart : Core →L[Real] Core :=
  let p : Core →L[Real] Matter :=
    (ContinuousLinearMap.snd Real PhysicalCore Matter).comp (ContinuousLinearMap.fst Real _ _)
  ((0 : Core →L[Real] PhysicalCore).prod p).prod (ContinuousLinearMap.snd Real _ _)

@[simp] theorem intrinsicBulkGaugePart_apply (input : Core) :
    intrinsicBulkGaugePart period hPeriod couplings input = ((input.1.1, 0), 0) := rfl

@[simp] theorem intrinsicBulkMatterLLPart_apply (input : Core) :
    intrinsicBulkMatterLLPart period hPeriod couplings input = ((0, input.1.2), input.2) := rfl

variable (interactionScale : Real) (coefficients : PotentialCoefficients)
local notation "action" => intrinsicBulkPhysicalAction period hPeriod couplings interactionScale coefficients
local notation "hessian" => intrinsicBulkPhysicalHessian period hPeriod couplings interactionScale coefficients
local notation "gaugePart" => intrinsicBulkGaugePart period hPeriod couplings
local notation "matterPart" => intrinsicBulkMatterLLPart period hPeriod couplings

theorem intrinsicBulkPhysicalAction_gauge_matter_split (input : Core) :
    action input = action (gaugePart input) + (action (matterPart input) - action 0) := by
  simp only [intrinsicBulkPhysicalAction_eq_summands, intrinsicBulkGaugePart_apply,
    intrinsicBulkMatterLLPart_apply, Prod.fst_zero, Prod.snd_zero]
  ring

theorem intrinsicBulkPhysicalHessian_gauge_matter_split (first second : Core) :
    hessian first second = hessian (gaugePart first) (gaugePart second) +
      hessian (matterPart first) (matterPart second) :=
  separated_hessian action gaugePart matterPart
    (intrinsicBulkPhysicalAction_contDiffAt_zero period hPeriod couplings interactionScale coefficients)
    (intrinsicBulkPhysicalAction_gauge_matter_split period hPeriod couplings interactionScale coefficients)
    first second

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkGaugeMatterHessianSplit4D
