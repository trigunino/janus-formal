import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBulkActionCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2FullBRSTMetricCenterVanishing4D

/-! Erase only the nonminimal BRST packets and identify the remaining physical
bulk action. Boundary GHY terms are not part of this bulk core. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkPhysicalProjection4D
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusFiniteFrameC2AbelianOperators4D P0EFTJanusFiniteFrameC2AbelianBRSTAction4D
open P0EFTJanusFiniteFrameDiffeomorphismBRSTDensity4D
open P0EFTJanusFiniteFrameDiffeomorphismC2Core4D
open P0EFTJanusFiniteFrameDiffeomorphismBRSTSmoothFeatures4D
open P0EFTJanusFiniteFramePairedC2FullBRSTGaugeAction4D
open P0EFTJanusFiniteFramePairedC2FullBRSTMetricCenterVanishing4D
open P0EFTJanusFiniteFramePairedC2EinsteinBRSTAction4D P0EFTJanusFiniteFramePairedC2PhysicalAction4D
open P0EFTJanusFiniteFrameC2EinsteinHilbertAction4D P0EFTJanusFiniteFramePairedC2InteractionAction4D
open P0EFTJanusFiniteFrameC2MobileMaxwellAction4D P0EFTJanusFiniteFramePairedC2PhysicalMaxwellAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC24D
open P0EFTJanusProgramPT12IntrinsicBulkGeometry4D P0EFTJanusProgramPT12IntrinsicBulkActionCore4D
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
local notation "geometry" => intrinsicBulkGeometry period hPeriod
local notation "metric" => P0EFTJanusProgramPGlobalCandidateAGeometry4D.GlobalCandidateAGeometry.plusMetric
  (intrinsicBulkGeometry period hPeriod)
local notation "Metric" => GeneralMetricRelativeC2Core period hPeriod frame metric
local notation "Gauge" => FiniteFrameAbelianGaugeC2Core period hPeriod frame
local notation "Nonminimal" => FiniteFrameAbelianNonminimalC2Core period hPeriod
local notation "Diffeomorphism" => FiniteFrameDiffeomorphismNonminimalC2Core period hPeriod frame
local notation "PhysicalCore" => FiniteFramePairedC2PhysicalCore period hPeriod geometry frame

variable (couplings : GlobalCandidateAActionCouplings)
local notation "Core" => IntrinsicBulkCore period hPeriod couplings
local instance coreNormedAddCommGroup : NormedAddCommGroup Core := inferInstance
local instance : AddZeroClass Core :=
  (coreNormedAddCommGroup period hPeriod couplings).toAddCommGroup.toAddZeroClass
local instance : NormedSpace Real Core :=
  P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D.instNormedSpaceRealFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCore
    period hPeriod geometry frame couplings

def intrinsicBulkPhysicalProjection : Core →L[Real] Core :=
  let abelian : Gauge × Nonminimal →L[Real] Gauge × Nonminimal :=
    (ContinuousLinearMap.fst Real Gauge Nonminimal).prod 0
  let physical : PhysicalCore →L[Real] PhysicalCore :=
    (ContinuousLinearMap.id Real (Metric × Metric)).prodMap
      ((abelian.prodMap abelian).prodMap (0 : Diffeomorphism →L[Real] Diffeomorphism))
  (physical.prodMap (ContinuousLinearMap.id Real _)).prodMap (ContinuousLinearMap.id Real _)

@[simp] theorem intrinsicBulkPhysicalProjection_apply (input : Core) :
    intrinsicBulkPhysicalProjection period hPeriod couplings input =
      (((input.1.1.1, (((input.1.1.2.1.1.1, 0), (input.1.1.2.1.2.1, 0)), 0)), input.1.2),
        input.2) := rfl

theorem intrinsicBulkPhysicalProjection_idempotent (input : Core) :
    intrinsicBulkPhysicalProjection period hPeriod couplings
      (intrinsicBulkPhysicalProjection period hPeriod couplings input) =
        intrinsicBulkPhysicalProjection period hPeriod couplings input := rfl

private theorem abelianAction_zero_nonminimal (variation : Metric) (potential : Gauge) :
    finiteFrameC2AbelianBRSTAction period hPeriod frame metric (variation, (potential, 0)) = 0 := by
  have hDensity : finiteFrameC2AbelianBRSTDensity period hPeriod frame metric
      (variation, (potential, 0)) = 0 := by
    unfold finiteFrameC2AbelianBRSTDensity
    apply Finset.sum_eq_zero
    intro component _
    simp only [Prod.fst_zero, Prod.snd_zero,
      (finiteFrameAbelianScalarC2Readout period hPeriod component).map_zero,
      zero_mul, smul_zero, sub_zero, add_zero]
  unfold finiteFrameC2AbelianBRSTAction
  rw [hDensity, (finiteFrameBRSTCanonicalIntegralCLM period hPeriod).map_zero]

private theorem fullBRSTAction_zero_nonminimal (metrics : Metric × Metric) (potentials : Gauge × Gauge) :
    finiteFramePairedC2FullBRSTGaugeAction period hPeriod frame frame frame metric metric couplings
      (metrics, (((potentials.1, 0), (potentials.2, 0)), 0)) = 0 := by
  simp only [finiteFramePairedC2FullBRSTGaugeAction,
    finiteFramePairedC2FullBRSTGaugeAbelianProjection_apply,
    finiteFramePairedC2FullBRSTGaugeDiffeomorphismProjection_apply,
    finiteFramePairedC2AbelianBRSTAction]
  rw [abelianAction_zero_nonminimal period hPeriod metrics.1 potentials.1,
    abelianAction_zero_nonminimal period hPeriod metrics.2 potentials.2,
    finiteFramePairedDiffeomorphismBRSTAction_zero_nonminimal period hPeriod
      frame frame frame metric metric metrics couplings]
  simp only [zero_add]

def intrinsicBulkPhysicalAction (interactionScale : Real) (coefficients : PotentialCoefficients) : Core → Real :=
  fun input => intrinsicBulkAction period hPeriod couplings interactionScale coefficients
    (intrinsicBulkPhysicalProjection period hPeriod couplings input)

/-- Actual physical summands, with arbitrary potentials and unchanged SpinC/LL fields. -/
theorem intrinsicBulkPhysicalAction_eq_summands (interactionScale : Real)
    (coefficients : PotentialCoefficients) (input : Core) :
    intrinsicBulkPhysicalAction period hPeriod couplings interactionScale coefficients input =
      finiteFramePairedC2EinsteinHilbertAction period hPeriod frame frame metric metric
        couplings.plusEinstein couplings.minusEinstein input.1.1.1 +
      pairedFiniteFrameC2InteractionAction period hPeriod geometry frame
        (intrinsicBulkGeometry_sylvester_bijective period hPeriod) interactionScale coefficients input.1.1.1 +
      finiteFramePairedC2MobileMaxwellAction period hPeriod frame frame metric metric
        couplings.plusMaxwellScale couplings.minusMaxwellScale
        (finiteFramePairedC2PhysicalMaxwellProjection period hPeriod geometry frame input.1.1) +
      programPPrimitiveSpinCMatterGraphAction period hPeriod couplings.matterMassSquared input.1.2 +
      regularGeneralMetricC0LLPTAction period hPeriod (canonicalDivergenceFreeLLFrame period hPeriod)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) input.2 := by
  simp only [intrinsicBulkPhysicalAction, intrinsicBulkAction,
    finiteFramePairedC2PhysicalMaxwellSpinCMatterLLAction,
    finiteFramePairedC2PhysicalMaxwellSpinCMatterAction, finiteFramePairedC2PhysicalMaxwellAction,
    finiteFramePairedC2PhysicalAction, finiteFramePairedC2EinsteinBRSTAction,
    intrinsicBulkPhysicalProjection_apply, finiteFramePairedC2PhysicalRecenter,
    intrinsicBulkMinusCenter_eq_zero, zero_add, finiteFramePairedC2PhysicalMaxwellProjection_apply]
  rw [fullBRSTAction_zero_nonminimal period hPeriod couplings input.1.1.1
    (input.1.1.2.1.1.1, input.1.1.2.1.2.1), add_zero]

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkPhysicalProjection4D
