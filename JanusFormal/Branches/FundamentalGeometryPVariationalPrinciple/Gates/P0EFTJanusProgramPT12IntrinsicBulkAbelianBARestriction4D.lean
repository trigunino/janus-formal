import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBulkAbelianLorenz4D

/-! Exact B--A restriction of the same bulk action, with all other summands retained. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkAbelianBARestriction4D
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusFiniteFrameC2AbelianOperators4D P0EFTJanusFiniteFrameC2AbelianBRSTAction4D
open P0EFTJanusFiniteFrameDiffeomorphismBRSTSmoothFeatures4D
open P0EFTJanusFiniteFramePairedC2FullBRSTGaugeAction4D
open P0EFTJanusFiniteFramePairedC2EinsteinBRSTAction4D P0EFTJanusFiniteFramePairedC2PhysicalAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D
open P0EFTJanusProgramPT12IntrinsicBulkGeometry4D P0EFTJanusProgramPT12IntrinsicBulkActionCore4D
open P0EFTJanusProgramPT12IntrinsicBulkAbelianBRestriction4D P0EFTJanusProgramPT12IntrinsicBulkAbelianLorenz4D
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
local notation "Gauge" => FiniteFrameAbelianGaugeC2Core period hPeriod frame
local notation "Ghost" => FiniteFrameAbelianGhostC2Core period hPeriod
local notation "ACore" => IntrinsicBulkAbelianACore period hPeriod
local notation "BCore" => IntrinsicBulkAbelianBCore period hPeriod

def intrinsicBulkAbelianAFields : ACore →L[Real] FiniteFramePairedC2AbelianGaugeFields period hPeriod frame frame :=
  ((ContinuousLinearMap.fst Real Gauge Gauge).prod 0).prod
    ((ContinuousLinearMap.snd Real Gauge Gauge).prod 0)

variable (couplings : GlobalCandidateAActionCouplings)
local instance : NormedSpace Real (IntrinsicBulkCore period hPeriod couplings) :=
  P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D.instNormedSpaceRealFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCore
    period hPeriod geometry frame couplings

def intrinsicBulkAbelianAInsertion : ACore →L[Real] IntrinsicBulkCore period hPeriod couplings :=
  let physical : ACore →L[Real] FiniteFramePairedC2PhysicalCore period hPeriod geometry frame :=
    (0 : ACore →L[Real] _).prod ((intrinsicBulkAbelianAFields period hPeriod).prod 0)
  (physical.prod 0).prod 0

@[simp] theorem intrinsicBulkAbelianAInsertion_apply (potential : ACore) :
    intrinsicBulkAbelianAInsertion period hPeriod couplings potential =
      (((0, (intrinsicBulkAbelianAFields period hPeriod potential, 0)), 0), 0) := rfl

private theorem abelianAction_BA_split (potential : Gauge) (field : Ghost) :
    finiteFrameC2AbelianBRSTAction period hPeriod frame metric (0, (potential, (field, 0))) =
      finiteFrameC2AbelianBRSTAction period hPeriod frame metric (0, (0, (field, 0))) +
        finiteFrameBRSTCanonicalIntegralCLM period hPeriod
          (intrinsicBulkAbelianSectorBAPairingDensity period hPeriod field potential) := by
  have hDensity : finiteFrameC2AbelianBRSTDensity period hPeriod frame metric
      (0, (potential, (field, 0))) =
      finiteFrameC2AbelianBRSTDensity period hPeriod frame metric (0, (0, (field, 0))) +
        intrinsicBulkAbelianSectorBAPairingDensity period hPeriod field potential := by
    simp only [finiteFrameC2AbelianBRSTDensity, ← intrinsicBulkAbelianLorenzComponent_apply,
      intrinsicBulkAbelianSectorBAPairingDensity, sum_apply,
      ContinuousLinearMap.bilinearComp_apply, ContinuousLinearMap.mul_apply',
      Prod.fst_zero, Prod.snd_zero]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro component _
    rw [(finiteFrameAbelianScalarC2Readout period hPeriod component).map_zero,
      (intrinsicBulkAbelianLorenzComponent period hPeriod component).map_zero]
    simp only [zero_mul, mul_zero, add_zero, zero_sub]
    abel
  unfold finiteFrameC2AbelianBRSTAction
  rw [hDensity, map_add]

private theorem abelianAction_A_zero (potential : Gauge) :
    finiteFrameC2AbelianBRSTAction period hPeriod frame metric (0, (potential, 0)) =
      finiteFrameC2AbelianBRSTAction period hPeriod frame metric (0, 0) := by
  change finiteFrameC2AbelianBRSTAction period hPeriod frame metric
      (0, (potential, ((0 : Ghost), 0))) =
    finiteFrameC2AbelianBRSTAction period hPeriod frame metric (0, (0, ((0 : Ghost), 0)))
  rw [abelianAction_BA_split,
    (intrinsicBulkAbelianSectorBAPairingDensity period hPeriod).map_zero,
    zero_apply, (finiteFrameBRSTCanonicalIntegralCLM period hPeriod).map_zero, add_zero]

private theorem abelianBAPairing_apply (field : BCore) (potential : ACore) :
    intrinsicBulkAbelianBAPairing period hPeriod field potential =
      finiteFrameBRSTCanonicalIntegralCLM period hPeriod
        (intrinsicBulkAbelianSectorBAPairingDensity period hPeriod field.1 potential.1 +
          intrinsicBulkAbelianSectorBAPairingDensity period hPeriod field.2 potential.2) := rfl

private theorem scalar_BA_split
    (e d i m m0 s ll ab1 ab2 a1 a2 b1 b2 z l1 l2 pairing : Real)
    (hAB1 : ab1 = b1 + l1) (hAB2 : ab2 = b2 + l2)
    (hA1 : a1 = z) (hA2 : a2 = z) (hPairing : pairing = l1 + l2) :
    e + (ab1 + ab2 + d) + i + m + s + ll =
      (e + (a1 + a2 + d) + i + m + s + ll) +
      (e + (b1 + b2 + d) + i + m0 + s + ll) -
      (e + (z + z + d) + i + m0 + s + ll) + pairing := by
  rw [hAB1, hAB2, hA1, hA2, hPairing]
  ring

private theorem intrinsicBulkAction_abelianBA_split (interactionScale : Real)
    (coefficients : PotentialCoefficients) (potential : ACore) (field : BCore) :
    intrinsicBulkAction period hPeriod couplings interactionScale coefficients
      (intrinsicBulkAbelianAInsertion period hPeriod couplings potential +
        intrinsicBulkAbelianBInsertion period hPeriod couplings field) =
      intrinsicBulkAction period hPeriod couplings interactionScale coefficients
        (intrinsicBulkAbelianAInsertion period hPeriod couplings potential) +
      intrinsicBulkAction period hPeriod couplings interactionScale coefficients
        (intrinsicBulkAbelianBInsertion period hPeriod couplings field) -
      intrinsicBulkAction period hPeriod couplings interactionScale coefficients 0 +
        intrinsicBulkAbelianBAPairing period hPeriod field potential := by
  simp only [intrinsicBulkAction, finiteFramePairedC2PhysicalMaxwellSpinCMatterLLAction,
      finiteFramePairedC2PhysicalMaxwellSpinCMatterAction, finiteFramePairedC2PhysicalMaxwellAction,
      finiteFramePairedC2PhysicalAction, finiteFramePairedC2EinsteinBRSTAction,
      finiteFramePairedC2FullBRSTGaugeAction, finiteFramePairedC2AbelianBRSTAction,
      intrinsicBulkAbelianAInsertion_apply, intrinsicBulkAbelianBInsertion_apply,
      intrinsicBulkAbelianAFields, intrinsicBulkAbelianBFields,
      finiteFramePairedC2PhysicalRecenter, intrinsicBulkMinusCenter_eq_zero,
      finiteFramePairedC2PhysicalMaxwellProjection_apply,
      finiteFramePairedC2FullBRSTGaugeAbelianProjection_apply,
      finiteFramePairedC2FullBRSTGaugeDiffeomorphismProjection_apply,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      zero_apply, Prod.fst_zero, Prod.snd_zero,
      Prod.mk_add_mk, zero_add, add_zero]
  apply scalar_BA_split
  · exact abelianAction_BA_split period hPeriod potential.1 field.1
  · exact abelianAction_BA_split period hPeriod potential.2 field.2
  · exact abelianAction_A_zero period hPeriod potential.1
  · exact abelianAction_A_zero period hPeriod potential.2
  · exact (abelianBAPairing_apply period hPeriod field potential).trans
      ((finiteFrameBRSTCanonicalIntegralCLM period hPeriod).map_add _ _)

private theorem scalar_BA_restriction (a b z l p : Real) (hB : b = z - p) :
    a + b - z + l = a + l - p := by
  rw [hB]
  ring

theorem intrinsicBulkAction_abelianBA_restriction (interactionScale : Real)
    (coefficients : PotentialCoefficients) (potential : ACore) (field : BCore) :
    intrinsicBulkAction period hPeriod couplings interactionScale coefficients
      (intrinsicBulkAbelianAInsertion period hPeriod couplings potential +
        intrinsicBulkAbelianBInsertion period hPeriod couplings field) =
    intrinsicBulkAction period hPeriod couplings interactionScale coefficients
      (intrinsicBulkAbelianAInsertion period hPeriod couplings potential) +
      intrinsicBulkAbelianBAPairing period hPeriod field potential -
        (1 / 2 : Real) * intrinsicBulkAbelianBPairing period hPeriod field field := by
  exact (intrinsicBulkAction_abelianBA_split period hPeriod couplings
    interactionScale coefficients potential field).trans
      (scalar_BA_restriction _ _ _ _ _
        (intrinsicBulkAction_abelianB_restriction period hPeriod couplings
          interactionScale coefficients field))

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkAbelianBARestriction4D
