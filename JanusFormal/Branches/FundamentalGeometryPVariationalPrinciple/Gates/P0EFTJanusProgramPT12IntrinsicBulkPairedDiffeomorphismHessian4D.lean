import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBulkBRSTDecomposition4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBulkSmoothBRSTCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeDiffeomorphismBilinearFamily4D

/-! The native bulk BRST Hessian on both metric perturbations and the shared
diffeomorphism packet. Each de Donder tensor remains its own metric perturbation. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkPairedDiffeomorphismHessian4D
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusProgramPT12AffineHessianPullback4D P0EFTJanusProgramPT12BilinearSecondJetFreeze4D

section Transport
variable {E F X : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [NormedAddCommGroup F] [NormedSpace Real F] [NormedAddCommGroup X] [NormedSpace Real X]
local instance : NormedAddCommGroup (E →L[Real] Real) := inferInstance
local instance : NormedSpace Real (E →L[Real] Real) := inferInstance
local instance : NormedAddCommGroup (F →L[Real] Real) := inferInstance
local instance : NormedSpace Real (F →L[Real] Real) := inferInstance
local instance : NormedAddCommGroup (F →L[Real] F →L[Real] Real) := inferInstance
local instance : NormedSpace Real (F →L[Real] F →L[Real] Real) := inferInstance
local instance : NormedAddCommGroup (E →L[Real] F →L[Real] Real) := inferInstance
local instance : NormedSpace Real (E →L[Real] F →L[Real] Real) := inferInstance
local instance : NormedAddCommGroup (F →L[Real] E →L[Real] Real) := inferInstance
local instance : NormedSpace Real (F →L[Real] E →L[Real] Real) := inferInstance
local instance : NormedAddCommGroup (E →L[Real] E →L[Real] Real) := inferInstance
local instance : NormedSpace Real (E →L[Real] E →L[Real] Real) := inferInstance

private theorem bilinear_pullback_contDiffAt (projection : E →L[Real] F)
    {coefficient : X → F →L[Real] F →L[Real] Real}
    (hCoefficient : ContDiffAt Real 2 coefficient 0) :
    ContDiffAt Real 2 (fun x => (coefficient x).bilinearComp projection projection) 0 := by
  have hFirst := hCoefficient.clm_comp
    (show ContDiffAt Real 2 (fun _ : X => projection) 0 from contDiffAt_const)
  have hFlip := (ContinuousLinearMap.flipₗᵢ Real E F Real).contDiff.comp_contDiffAt 0 hFirst
  have hSecond := hFlip.clm_comp
    (show ContDiffAt Real 2 (fun _ : X => projection) 0 from contDiffAt_const)
  exact (ContinuousLinearMap.flipₗᵢ Real E E Real).contDiff.comp_contDiffAt 0 hSecond

private theorem bilinear_restriction_hessian
    (f : E → Real) (insertion : F →L[Real] E) (coefficient : F → F →L[Real] F →L[Real] Real)
    (hf : ContDiffAt Real 2 f 0) (hCoefficient : ContDiffAt Real 2 coefficient 0)
    (hRestriction : ∀ x, f (insertion x) = coefficient x x x) (first second : F) :
    fderiv Real (fderiv Real f) 0 (insertion first) (insertion second) =
      coefficient 0 first second + coefficient 0 second first := by
  have hPull : fderiv Real (fderiv Real (fun x : F => f (insertion x))) 0 first second =
      fderiv Real (fderiv Real f) 0 (insertion first) (insertion second) := by
    simpa only [one_mul, zero_add] using scaledAffineHessian f 0 insertion 1 hf first second
  have hAction : (fun x : F => f (insertion x)) = (fun x : F => coefficient x x x) := funext hRestriction
  rw [hAction] at hPull
  exact hPull.symm.trans (bilinearCoefficient_second_fderiv_zero coefficient
    (ContinuousLinearMap.id Real F) (ContinuousLinearMap.id Real F) hCoefficient first second)
end Transport

open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusProgramPGlobalCovariantAction4D P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D P0EFTJanusProgramPGeneralMetricC2VolumeDensity4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPCandidateADiagonalDiffeomorphismKineticAdjointBridge4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusFiniteFrameC2DiffeomorphismBRSTAction4D P0EFTJanusFiniteFramePairedDiffeomorphismBRSTAction4D
open P0EFTJanusFiniteFramePairedC2FullBRSTGaugeAction4D
open P0EFTJanusFiniteFramePairedC2FullBRSTMetricCenterVanishing4D P0EFTJanusFiniteFramePairedC2PhysicalAction4D
open P0EFTJanusProgramPT12IntrinsicBulkGeometry4D P0EFTJanusProgramPT12IntrinsicBulkActionCore4D
open P0EFTJanusProgramPT12IntrinsicBulkBRSTDecomposition4D P0EFTJanusProgramPT12IntrinsicBulkSmoothBRSTCore4D
open P0EFTJanusProgramPT12FrameFreeDiffeomorphismBilinearFamily4D
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
local instance : CompleteSpace (CanonicalPhysicalScalarC2JetCore period hPeriod) := canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod
local instance : InnerProductSpace Real ProgramPPrimitiveSpinCMatterHilbert := InnerProductSpace.complexToReal
local notation "frame" => finiteSmoothTangentFrame period hPeriod
local notation "metric" => GlobalCandidateAGeometry.plusMetric (intrinsicBulkGeometry period hPeriod)
local notation "MonoFields" => FrameFreeDiffeomorphismBRSTFields period hPeriod frame metric

abbrev IntrinsicBulkPairedDiffeomorphismCore :=
  FiniteFramePairedDiffeomorphismBRSTCore period hPeriod frame frame frame metric metric
local notation "Fields" => IntrinsicBulkPairedDiffeomorphismCore period hPeriod
local instance : NormedAddCommGroup (GeneralMetricRelativeC2Core period hPeriod frame metric) := inferInstance
local instance : NormedSpace Real (GeneralMetricRelativeC2Core period hPeriod frame metric) :=
  Submodule.normedSpace (GeneralMetricRelativeC2Core period hPeriod frame metric)
local instance : NormedAddCommGroup
    (P0EFTJanusFiniteFrameDiffeomorphismC2Core4D.FiniteFrameDiffeomorphismNonminimalC2Core period hPeriod frame) :=
  inferInstance
local instance : NormedSpace Real
    (P0EFTJanusFiniteFrameDiffeomorphismC2Core4D.FiniteFrameDiffeomorphismNonminimalC2Core period hPeriod frame) :=
  inferInstance
local instance : NormedAddCommGroup Fields := inferInstance
local instance : NormedSpace Real Fields := inferInstance
local instance : NormedAddCommGroup MonoFields := inferInstance
local instance : NormedSpace Real MonoFields := inferInstance
local instance : NormedAddCommGroup (MonoFields →L[Real] Real) := inferInstance
local instance : NormedSpace Real (MonoFields →L[Real] Real) := inferInstance
local instance : NormedAddCommGroup (MonoFields →L[Real] MonoFields →L[Real] Real) := inferInstance
local instance : NormedSpace Real (MonoFields →L[Real] MonoFields →L[Real] Real) := inferInstance
local instance : NormedAddCommGroup (Fields →L[Real] Real) := inferInstance
local instance : NormedSpace Real (Fields →L[Real] Real) := inferInstance
local instance : NormedAddCommGroup (Fields →L[Real] Fields →L[Real] Real) := inferInstance
local instance : NormedSpace Real (Fields →L[Real] Fields →L[Real] Real) := inferInstance

private def plusFields : Fields →L[Real] MonoFields :=
  (ContinuousLinearMap.snd Real _ _).comp
    (finiteFramePairedDiffeomorphismBRSTPlusInput period hPeriod frame frame frame metric metric)
private def minusFields : Fields →L[Real] MonoFields :=
  (ContinuousLinearMap.snd Real _ _).comp
    (finiteFramePairedDiffeomorphismBRSTMinusInput period hPeriod frame frame frame metric metric)

variable (couplings : GlobalCandidateAActionCouplings)
def intrinsicBulkPairedDiffeomorphismBilinearFamily (point : Fields) : Fields →L[Real] Fields →L[Real] Real :=
  candidateAPlusEinsteinKineticWeight couplings •
    (frameFreeDiffeomorphismBRSTBilinearCoefficient period hPeriod frame metric point.1.1).bilinearComp
      (plusFields period hPeriod) (plusFields period hPeriod) +
  candidateAMinusEinsteinKineticWeight couplings •
    (frameFreeDiffeomorphismBRSTBilinearCoefficient period hPeriod frame metric point.1.2).bilinearComp
      (minusFields period hPeriod) (minusFields period hPeriod)

theorem intrinsicBulkPairedDiffeomorphismBilinearFamily_contDiffAt_zero :
    ContDiffAt Real 2 (intrinsicBulkPairedDiffeomorphismBilinearFamily period hPeriod couplings) 0 := by
  have hZero := zero_mem_generalMetricRelativeC2VolumeDomain period hPeriod frame metric
  have hK : ContDiffAt Real 2 (frameFreeDiffeomorphismBRSTBilinearCoefficient period hPeriod frame metric) 0 :=
    ((frameFreeDiffeomorphismBRSTBilinearCoefficient_contDiffOn_two period hPeriod frame metric) 0 hZero).contDiffAt
      ((generalMetricRelativeC2VolumeDomain_isOpen period hPeriod frame metric).mem_nhds hZero)
  have hPlus := hK.comp 0 (show ContDiffAt Real 2 (fun point : Fields => point.1.1) 0 from contDiff_fst.fst.contDiffAt)
  have hMinus := hK.comp 0 (show ContDiffAt Real 2 (fun point : Fields => point.1.2) 0 from contDiff_fst.snd.contDiffAt)
  exact ((bilinear_pullback_contDiffAt (plusFields period hPeriod) hPlus).const_smul
    (candidateAPlusEinsteinKineticWeight couplings)).add
    ((bilinear_pullback_contDiffAt (minusFields period hPeriod) hMinus).const_smul
      (candidateAMinusEinsteinKineticWeight couplings))

local instance coreNormedAddCommGroup : NormedAddCommGroup (IntrinsicBulkCore period hPeriod couplings) := inferInstance
local instance : AddZeroClass (IntrinsicBulkCore period hPeriod couplings) :=
  (coreNormedAddCommGroup period hPeriod couplings).toAddCommGroup.toAddZeroClass
local instance : NormedSpace Real (IntrinsicBulkCore period hPeriod couplings) :=
  P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D.instNormedSpaceRealFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCore
    period hPeriod (intrinsicBulkGeometry period hPeriod) frame couplings

/-- Both metric perturbations and exactly one shared total nonminimal packet. -/
def intrinsicBulkPairedDiffeomorphismInsertion : Fields →L[Real] IntrinsicBulkCore period hPeriod couplings :=
  let physical : Fields →L[Real] FiniteFramePairedC2PhysicalCore period hPeriod (intrinsicBulkGeometry period hPeriod) frame :=
    (ContinuousLinearMap.fst Real _ _).prod
      ((0 : Fields →L[Real] _).prod (ContinuousLinearMap.snd Real _ _))
  (physical.prod 0).prod 0

theorem intrinsicBulkBRSTAction_pairedDiffeomorphism_restriction (fields : Fields) :
    intrinsicBulkBRSTAction period hPeriod couplings (intrinsicBulkPairedDiffeomorphismInsertion period hPeriod couplings fields) =
      intrinsicBulkPairedDiffeomorphismBilinearFamily period hPeriod couplings fields fields fields := by
  change finiteFramePairedC2FullBRSTGaugeAction period hPeriod frame frame frame metric metric couplings
    (fields.1, (0, fields.2)) = _
  simp only [finiteFramePairedC2FullBRSTGaugeAction,
    finiteFramePairedC2FullBRSTGaugeAbelianProjection_apply,
    finiteFramePairedC2FullBRSTGaugeDiffeomorphismProjection_apply, Prod.fst_zero, Prod.snd_zero]
  have hDrop := congrArg (fun x : Real => x +
      finiteFramePairedDiffeomorphismBRSTAction period hPeriod frame frame frame metric metric couplings fields)
    (finiteFramePairedC2AbelianBRSTAction_zero_fields period hPeriod frame frame metric metric fields.1)
  have hPair := congrArg₂ (fun x y : Real => candidateAPlusEinsteinKineticWeight couplings * x +
      candidateAMinusEinsteinKineticWeight couplings * y)
    (frameFreeDiffeomorphismBRSTAction_eq_bilinear period hPeriod frame metric fields.1.1
      (plusFields period hPeriod fields))
    (frameFreeDiffeomorphismBRSTAction_eq_bilinear period hPeriod frame metric fields.1.2
      (minusFields period hPeriod fields))
  exact (hDrop.trans (zero_add _)).trans hPair

theorem intrinsicBulkBRSTHessian_pairedDiffeomorphism (first second : Fields) :
    intrinsicBulkBRSTHessian period hPeriod couplings
      (intrinsicBulkPairedDiffeomorphismInsertion period hPeriod couplings first)
      (intrinsicBulkPairedDiffeomorphismInsertion period hPeriod couplings second) =
      intrinsicBulkPairedDiffeomorphismBilinearFamily period hPeriod couplings 0 first second +
        intrinsicBulkPairedDiffeomorphismBilinearFamily period hPeriod couplings 0 second first :=
  bilinear_restriction_hessian (intrinsicBulkBRSTAction period hPeriod couplings)
    (intrinsicBulkPairedDiffeomorphismInsertion period hPeriod couplings)
    (intrinsicBulkPairedDiffeomorphismBilinearFamily period hPeriod couplings)
    (intrinsicBulkBRSTAction_contDiffAt_zero period hPeriod couplings 0 ⟨0, 0, 0, 0, 0⟩)
    (intrinsicBulkPairedDiffeomorphismBilinearFamily_contDiffAt_zero period hPeriod couplings)
    (intrinsicBulkBRSTAction_pairedDiffeomorphism_restriction period hPeriod couplings) first second

def intrinsicBulkSmoothPairedDiffeomorphismFields (state : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) : Fields :=
  finiteFrameSmoothPairedDiffeomorphismBRSTCore period hPeriod frame frame frame metric metric metric
    (state.metricPerturbation .plus) (state.metricPerturbation .minus) state.nonminimal

theorem intrinsicBulkPairedDiffeomorphismInsertion_smooth
    (state : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    intrinsicBulkPairedDiffeomorphismInsertion period hPeriod couplings
      (intrinsicBulkSmoothPairedDiffeomorphismFields period hPeriod state) =
      intrinsicBulkSmoothBRSTInsertion period hPeriod couplings state := rfl

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkPairedDiffeomorphismHessian4D
