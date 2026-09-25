import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeMaxwellBilinear4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeMaxwellMetricPotentialHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBulkBRSTDecomposition4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBulkAbelianBARestriction4D

/-! Native Maxwell restriction of the physical bulk action and its exact
potential reflection. All other physical fields retain their original values. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkMaxwellRestriction4D
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff

private def weightedPair {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (B : E →L[Real] E →L[Real] Real) (plus minus : Real) :
    (E × E) →L[Real] (E × E) →L[Real] Real :=
  plus • B.bilinearComp (ContinuousLinearMap.fst Real E E) (ContinuousLinearMap.fst Real E E) +
    minus • B.bilinearComp (ContinuousLinearMap.snd Real E E) (ContinuousLinearMap.snd Real E E)

private theorem sub_two_smul {E : Type*} [AddCommGroup E] [Module Real E] (x : E) :
    x - (2 : Real) • x = -x := by
  rw [two_smul, sub_add_eq_sub_sub, sub_self, zero_sub]

private theorem scalar_quadratic_split (e i q s l : Real) :
    e + i + q + s + l = (e + i + s + l) + q := by ring

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

def intrinsicBulkAbelianPotentialReadout : Core →L[Real] ACore :=
  let physical : Core →L[Real] PhysicalCore :=
    (ContinuousLinearMap.fst Real PhysicalCore Matter).comp (ContinuousLinearMap.fst Real _ _)
  let fields : Core →L[Real] Fields :=
    (ContinuousLinearMap.fst Real Fields Diffeomorphism).comp
      ((ContinuousLinearMap.snd Real (Metric × Metric) (Fields × Diffeomorphism)).comp physical)
  ((ContinuousLinearMap.fst Real Gauge Nonminimal).comp
    ((ContinuousLinearMap.fst Real (Gauge × Nonminimal) (Gauge × Nonminimal)).comp fields)).prod
    ((ContinuousLinearMap.fst Real Gauge Nonminimal).comp
      ((ContinuousLinearMap.snd Real (Gauge × Nonminimal) (Gauge × Nonminimal)).comp fields))

@[simp] theorem intrinsicBulkAbelianPotentialReadout_apply (input : IntrinsicBulkCore period hPeriod couplings) :
    intrinsicBulkAbelianPotentialReadout period hPeriod couplings input =
      (input.1.1.2.1.1.1, input.1.1.2.1.2.1) := rfl

def intrinsicBulkPotentialReflection : Core →L[Real] Core :=
  let abelian : Gauge × Nonminimal →L[Real] Gauge × Nonminimal :=
    (-ContinuousLinearMap.fst Real Gauge Nonminimal).prod (ContinuousLinearMap.snd Real Gauge Nonminimal)
  let physical : PhysicalCore →L[Real] PhysicalCore :=
    (ContinuousLinearMap.id Real (Metric × Metric)).prodMap
      ((abelian.prodMap abelian).prodMap (ContinuousLinearMap.id Real Diffeomorphism))
  (physical.prodMap (ContinuousLinearMap.id Real Matter)).prodMap (ContinuousLinearMap.id Real _)

@[simp] theorem intrinsicBulkPotentialReflection_apply (input : IntrinsicBulkCore period hPeriod couplings) :
    intrinsicBulkPotentialReflection period hPeriod couplings input =
      (((input.1.1.1, (((-input.1.1.2.1.1.1, input.1.1.2.1.1.2),
        (-input.1.1.2.1.2.1, input.1.1.2.1.2.2)), input.1.1.2.2)), input.1.2), input.2) := rfl

theorem intrinsicBulkPotentialReflection_sub (input : IntrinsicBulkCore period hPeriod couplings) :
    intrinsicBulkPotentialReflection period hPeriod couplings input = input - (2 : Real) •
      intrinsicBulkAbelianAInsertion period hPeriod couplings
        (intrinsicBulkAbelianPotentialReadout period hPeriod couplings input) := by
  change (((input.1.1.1, (((-input.1.1.2.1.1.1, input.1.1.2.1.1.2),
      (-input.1.1.2.1.2.1, input.1.1.2.1.2.2)), input.1.1.2.2)), input.1.2), input.2) =
    (((input.1.1.1 - (2 : Real) • 0,
      (((input.1.1.2.1.1.1 - (2 : Real) • input.1.1.2.1.1.1, input.1.1.2.1.1.2 - (2 : Real) • 0),
        (input.1.1.2.1.2.1 - (2 : Real) • input.1.1.2.1.2.1, input.1.1.2.1.2.2 - (2 : Real) • 0)),
        input.1.1.2.2 - (2 : Real) • 0)), input.1.2 - (2 : Real) • 0), input.2 - (2 : Real) • 0)
  simp only [smul_zero, sub_zero, sub_two_smul]

theorem intrinsicBulkPotentialReflection_insert (potential : IntrinsicBulkAbelianACore period hPeriod) :
    intrinsicBulkPotentialReflection period hPeriod couplings
      (intrinsicBulkAbelianAInsertion period hPeriod couplings potential) =
      -intrinsicBulkAbelianAInsertion period hPeriod couplings potential := by
  have hReflection := intrinsicBulkPotentialReflection_sub period hPeriod couplings
    (intrinsicBulkAbelianAInsertion period hPeriod couplings potential)
  change intrinsicBulkPotentialReflection period hPeriod couplings
      (intrinsicBulkAbelianAInsertion period hPeriod couplings potential) =
    intrinsicBulkAbelianAInsertion period hPeriod couplings potential - (2 : Real) •
      intrinsicBulkAbelianAInsertion period hPeriod couplings potential at hReflection
  exact hReflection.trans (sub_two_smul (intrinsicBulkAbelianAInsertion period hPeriod couplings potential))

theorem intrinsicBulkPhysicalAction_potential_reflection (interactionScale : Real)
    (coefficients : PotentialCoefficients) (input : IntrinsicBulkCore period hPeriod couplings) :
    intrinsicBulkPhysicalAction period hPeriod couplings interactionScale coefficients
      (intrinsicBulkPotentialReflection period hPeriod couplings input) =
      intrinsicBulkPhysicalAction period hPeriod couplings interactionScale coefficients input := by
  simp only [intrinsicBulkPhysicalAction_eq_summands, intrinsicBulkPotentialReflection_apply,
    finiteFramePairedC2PhysicalMaxwellProjection_apply, finiteFramePairedC2MobileMaxwellAction,
    finiteFrameMobileMaxwellAction_potential_neg]

def intrinsicBulkMaxwellPairing : ACore →L[Real] ACore →L[Real] Real :=
  weightedPair (frameFreeMaxwellBilinear period hPeriod frame metric 0)
    couplings.plusMaxwellScale couplings.minusMaxwellScale

theorem intrinsicBulkPhysicalAction_potential_restriction (interactionScale : Real)
    (coefficients : PotentialCoefficients) (potential : IntrinsicBulkAbelianACore period hPeriod) :
    intrinsicBulkPhysicalAction period hPeriod couplings interactionScale coefficients
      (intrinsicBulkAbelianAInsertion period hPeriod couplings potential) =
      intrinsicBulkPhysicalAction period hPeriod couplings interactionScale coefficients 0 +
        intrinsicBulkMaxwellPairing period hPeriod couplings potential potential := by
  have hZero : frameFreeMaxwellBilinear period hPeriod frame metric 0 0 0 = 0 :=
    (frameFreeMaxwellBilinear period hPeriod frame metric 0 0).map_zero
  simp only [intrinsicBulkPhysicalAction_eq_summands, intrinsicBulkAbelianAInsertion_apply,
    intrinsicBulkAbelianAFields, finiteFramePairedC2PhysicalMaxwellProjection_apply,
    finiteFramePairedC2MobileMaxwellAction, intrinsicBulkMaxwellPairing, weightedPair,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    ContinuousLinearMap.bilinearComp_apply, zero_apply, Prod.fst_zero, Prod.snd_zero,
    _root_.add_apply, smul_apply, smul_eq_mul, frameFreeMobileMaxwellAction_eq_bilinear,
    hZero, mul_zero, add_zero]
  exact scalar_quadratic_split _ _ _ _ _

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkMaxwellRestriction4D
