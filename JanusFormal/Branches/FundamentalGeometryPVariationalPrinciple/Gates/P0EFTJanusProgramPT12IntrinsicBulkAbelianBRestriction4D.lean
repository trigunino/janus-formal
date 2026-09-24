import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBulkHessian4D

/-! Exact restriction of the intrinsic bulk action to its two genuine Abelian B fields. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkAbelianBRestriction4D
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusFiniteFrameC2AbelianOperators4D P0EFTJanusFiniteFrameC2AbelianBRSTAction4D
open P0EFTJanusFiniteFrameDiffeomorphismBRSTSmoothFeatures4D
open P0EFTJanusFiniteFramePairedC2FullBRSTGaugeAction4D
open P0EFTJanusFiniteFramePairedC2EinsteinBRSTAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D
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
local instance : MeasurableSpace (Q period hPeriod) := borel _
local instance : BorelSpace (Q period hPeriod) where measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
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
local notation "Ghost" => FiniteFrameAbelianGhostC2Core period hPeriod
local notation "C0" => C(Q period hPeriod, Real)

abbrev IntrinsicBulkAbelianBCore := Ghost × Ghost
local notation "BCore" => IntrinsicBulkAbelianBCore period hPeriod

def intrinsicBulkAbelianBFields : BCore →L[Real] FiniteFramePairedC2AbelianGaugeFields period hPeriod frame frame :=
  ((0 : BCore →L[Real] FiniteFrameAbelianGaugeC2Core period hPeriod frame).prod
    ((ContinuousLinearMap.fst Real Ghost Ghost).prod 0)).prod
  ((0 : BCore →L[Real] FiniteFrameAbelianGaugeC2Core period hPeriod frame).prod
    ((ContinuousLinearMap.snd Real Ghost Ghost).prod 0))

variable (couplings : GlobalCandidateAActionCouplings)
local instance : NormedSpace Real (IntrinsicBulkCore period hPeriod couplings) :=
  P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D.instNormedSpaceRealFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCore
    period hPeriod geometry frame couplings

def intrinsicBulkAbelianBInsertion : BCore →L[Real] IntrinsicBulkCore period hPeriod couplings :=
  let physical : BCore →L[Real] FiniteFramePairedC2PhysicalCore period hPeriod geometry frame :=
    (0 : BCore →L[Real] _).prod ((intrinsicBulkAbelianBFields period hPeriod).prod 0)
  (physical.prod 0).prod 0

@[simp] theorem intrinsicBulkAbelianBInsertion_apply (field : BCore) :
    intrinsicBulkAbelianBInsertion period hPeriod couplings field =
      (((0, (intrinsicBulkAbelianBFields period hPeriod field, 0)), 0), 0) := rfl

private def ghostPairingDensity : Ghost →L[Real] Ghost →L[Real] C0 :=
  ∑ component : Fin 2, (ContinuousLinearMap.mul Real C0).bilinearComp
    (finiteFrameAbelianScalarC2Readout period hPeriod component)
    (finiteFrameAbelianScalarC2Readout period hPeriod component)

def intrinsicBulkAbelianBPairingDensity : BCore →L[Real] BCore →L[Real] C0 :=
  (ghostPairingDensity period hPeriod).bilinearComp
      (ContinuousLinearMap.fst Real Ghost Ghost) (ContinuousLinearMap.fst Real Ghost Ghost) +
    (ghostPairingDensity period hPeriod).bilinearComp
      (ContinuousLinearMap.snd Real Ghost Ghost) (ContinuousLinearMap.snd Real Ghost Ghost)

def intrinsicBulkAbelianBPairing : BCore →L[Real] BCore →L[Real] Real :=
  (ContinuousLinearMap.compL Real BCore C0 Real (finiteFrameBRSTCanonicalIntegralCLM period hPeriod)).comp
    (intrinsicBulkAbelianBPairingDensity period hPeriod)

theorem intrinsicBulkAbelianBPairing_apply (first second : BCore) :
    intrinsicBulkAbelianBPairing period hPeriod first second =
    ∫ point, (∑ component : Fin 2,
      finiteFrameAbelianScalarC2Readout period hPeriod component first.1 point *
        finiteFrameAbelianScalarC2Readout period hPeriod component second.1 point) +
      (∑ component : Fin 2,
      finiteFrameAbelianScalarC2Readout period hPeriod component first.2 point *
        finiteFrameAbelianScalarC2Readout period hPeriod component second.2 point)
      ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  change finiteFrameBRSTCanonicalIntegralCLM period hPeriod _ = _
  rw [finiteFrameBRSTCanonicalIntegralCLM_apply]
  rfl

theorem intrinsicBulkAbelianBPairing_symmetric (first second : BCore) :
    intrinsicBulkAbelianBPairing period hPeriod first second =
      intrinsicBulkAbelianBPairing period hPeriod second first := by
  rw [intrinsicBulkAbelianBPairing_apply, intrinsicBulkAbelianBPairing_apply]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun point => by
    dsimp only
    apply congrArg₂ (fun x y : Real => x + y)
    · apply Finset.sum_congr rfl
      intro component _
      exact mul_comm _ _
    · apply Finset.sum_congr rfl
      intro component _
      exact mul_comm _ _

private theorem abelianAction_pureB (field : Ghost) :
    finiteFrameC2AbelianBRSTAction period hPeriod frame (intrinsicBulkGeometry period hPeriod).plusMetric
      (0, (0, (field, 0))) =
      (- (1 / 2 : Real)) * finiteFrameBRSTCanonicalIntegralCLM period hPeriod
        (ghostPairingDensity period hPeriod field field) := by
  have hDensity : finiteFrameC2AbelianBRSTDensity period hPeriod frame (intrinsicBulkGeometry period hPeriod).plusMetric
      (0, (0, (field, 0))) =
      (- (1 / 2 : Real)) • ghostPairingDensity period hPeriod field field := by
    simp [finiteFrameC2AbelianBRSTDensity, finiteFrameC2AbelianLorenzComponentExpression,
      finiteFrameC2AbelianLorenzExpression, ghostPairingDensity]; abel
  unfold finiteFrameC2AbelianBRSTAction
  rw [hDensity, map_smul]
  rfl

private theorem abelianAction_zero :
    finiteFrameC2AbelianBRSTAction period hPeriod frame (intrinsicBulkGeometry period hPeriod).plusMetric
      (0, 0) = 0 := by
  change finiteFrameC2AbelianBRSTAction period hPeriod frame
    (intrinsicBulkGeometry period hPeriod).plusMetric (0, (0, ((0 : Ghost), 0))) = 0
  rw [abelianAction_pureB]
  rw [(ghostPairingDensity period hPeriod (0 : Ghost)).map_zero,
    (finiteFrameBRSTCanonicalIntegralCLM period hPeriod).map_zero, mul_zero]

/-- The untouched bulk summands retain their actual value at zero. -/
theorem intrinsicBulkAction_abelianB_restriction (interactionScale : Real)
    (coefficients : PotentialCoefficients) (field : BCore) :
    intrinsicBulkAction period hPeriod couplings interactionScale coefficients
      (intrinsicBulkAbelianBInsertion period hPeriod couplings field) =
    intrinsicBulkAction period hPeriod couplings interactionScale coefficients 0 -
      (1 / 2 : Real) * intrinsicBulkAbelianBPairing period hPeriod field field := by
  simp only [intrinsicBulkAction, finiteFramePairedC2PhysicalMaxwellSpinCMatterLLAction,
    finiteFramePairedC2PhysicalMaxwellSpinCMatterAction, finiteFramePairedC2PhysicalMaxwellAction,
    finiteFramePairedC2PhysicalAction, finiteFramePairedC2EinsteinBRSTAction,
    finiteFramePairedC2FullBRSTGaugeAction, finiteFramePairedC2AbelianBRSTAction,
    intrinsicBulkAbelianBInsertion_apply, intrinsicBulkAbelianBFields,
    finiteFramePairedC2PhysicalRecenter, intrinsicBulkMinusCenter_eq_zero,
    finiteFramePairedC2PhysicalMaxwellProjection_apply,
    finiteFramePairedC2FullBRSTGaugeAbelianProjection_apply,
    finiteFramePairedC2FullBRSTGaugeDiffeomorphismProjection_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', zero_apply, Prod.fst_zero, Prod.snd_zero,
    zero_add]
  rw [abelianAction_pureB period hPeriod field.1, abelianAction_pureB period hPeriod field.2,
    abelianAction_zero]
  simp only [zero_add, add_zero]
  change _ = _ - (1 / 2 : Real) * finiteFrameBRSTCanonicalIntegralCLM period hPeriod
    (ghostPairingDensity period hPeriod field.1 field.1 + ghostPairingDensity period hPeriod field.2 field.2)
  rw [map_add]
  ring

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkAbelianBRestriction4D
