import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBulkBRSTDecomposition4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBulkSmoothAbelianBRSTCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeAbelianBilinearFamily4D

/-! The complete paired Abelian sector of the native intrinsic bulk BRST
Hessian, with the genuine smooth insertion retained. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkPairedAbelianHessian4D
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusProgramPT12AffineHessianPullback4D
open P0EFTJanusProgramPT12BilinearSecondJetFreeze4D

section Quadratic
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [NormedAddCommGroup F] [NormedSpace Real F]
local instance : NormedAddCommGroup (E →L[Real] Real) := inferInstance
local instance : NormedSpace Real (E →L[Real] Real) := inferInstance
local instance : NormedAddCommGroup (F →L[Real] Real) := inferInstance
local instance : NormedSpace Real (F →L[Real] Real) := inferInstance
local instance : NormedAddCommGroup (F →L[Real] F →L[Real] Real) := inferInstance
local instance : NormedSpace Real (F →L[Real] F →L[Real] Real) := inferInstance

private def pairedBilinear (B : F →L[Real] F →L[Real] Real) :
    (F × F) →L[Real] (F × F) →L[Real] Real :=
  B.bilinearComp (ContinuousLinearMap.fst Real F F) (ContinuousLinearMap.fst Real F F) +
    B.bilinearComp (ContinuousLinearMap.snd Real F F) (ContinuousLinearMap.snd Real F F)

private theorem quadratic_restriction_hessian
    (f : E → Real) (j : F →L[Real] E) (B : F →L[Real] F →L[Real] Real)
    (hf : ContDiffAt Real 2 f 0) (hRestriction : ∀ x, f (j x) = B x x) (first second : F) :
    fderiv Real (fderiv Real f) 0 (j first) (j second) = B first second + B second first := by
  have hPull : fderiv Real (fderiv Real (fun x : F => f (j x))) 0 first second =
      fderiv Real (fderiv Real f) 0 (j first) (j second) := by
    simpa only [one_mul, zero_add] using scaledAffineHessian f 0 j 1 hf first second
  have hAction : (fun x : F => f (j x)) = (fun x : F => B x x) := funext hRestriction
  rw [hAction] at hPull
  exact hPull.symm.trans (bilinearCoefficient_second_fderiv_zero
    (fun _ : F => B) (ContinuousLinearMap.id Real F) (ContinuousLinearMap.id Real F)
    (show ContDiffAt Real 2 (fun _ : F => B) 0 from contDiffAt_const) first second)
end Quadratic

open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusProgramPGlobalCovariantAction4D P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusFiniteFrameC2AbelianBRSTAction4D
open P0EFTJanusFiniteFramePairedC2FullBRSTGaugeAction4D
open P0EFTJanusFiniteFramePairedC2FullBRSTMetricCenterVanishing4D
open P0EFTJanusFiniteFramePairedC2PhysicalAction4D
open P0EFTJanusProgramPT12IntrinsicBulkGeometry4D P0EFTJanusProgramPT12IntrinsicBulkActionCore4D
open P0EFTJanusProgramPT12IntrinsicBulkBRSTDecomposition4D
open P0EFTJanusProgramPT12IntrinsicBulkSmoothAbelianBRSTCore4D
open P0EFTJanusProgramPT12FrameFreeAbelianBilinearFamily4D
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

abbrev IntrinsicBulkPairedAbelianCore := FiniteFramePairedC2AbelianGaugeFields period hPeriod frame frame
local notation "Fields" => IntrinsicBulkPairedAbelianCore period hPeriod
local instance : NormedAddCommGroup Fields := inferInstance
local instance : NormedSpace Real Fields := inferInstance
local instance : NormedAddCommGroup (Fields →L[Real] Real) := inferInstance
local instance : NormedSpace Real (Fields →L[Real] Real) := inferInstance
local instance : NormedAddCommGroup (Fields →L[Real] Fields →L[Real] Real) := inferInstance
local instance : NormedSpace Real (Fields →L[Real] Fields →L[Real] Real) := inferInstance

def intrinsicBulkPairedAbelianBilinear : Fields →L[Real] Fields →L[Real] Real :=
  pairedBilinear (frameFreeAbelianBRSTBilinearCoefficient period hPeriod frame metric 0)

variable (couplings : GlobalCandidateAActionCouplings)
local instance coreNormedAddCommGroup : NormedAddCommGroup (IntrinsicBulkCore period hPeriod couplings) := inferInstance
local instance : AddZeroClass (IntrinsicBulkCore period hPeriod couplings) :=
  (coreNormedAddCommGroup period hPeriod couplings).toAddCommGroup.toAddZeroClass
local instance : NormedSpace Real (IntrinsicBulkCore period hPeriod couplings) :=
  P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D.instNormedSpaceRealFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCore
    period hPeriod (intrinsicBulkGeometry period hPeriod) frame couplings

/-- Both complete Abelian packets, with zero metric, diffeomorphism, matter and LL fields. -/
def intrinsicBulkPairedAbelianInsertion : Fields →L[Real] IntrinsicBulkCore period hPeriod couplings :=
  let physical : Fields →L[Real] FiniteFramePairedC2PhysicalCore period hPeriod
      (intrinsicBulkGeometry period hPeriod) frame :=
    (0 : Fields →L[Real] _).prod ((ContinuousLinearMap.id Real Fields).prod 0)
  (physical.prod 0).prod 0

theorem intrinsicBulkBRSTAction_pairedAbelian_restriction
    (fields : IntrinsicBulkPairedAbelianCore period hPeriod) :
    intrinsicBulkBRSTAction period hPeriod couplings
      (intrinsicBulkPairedAbelianInsertion period hPeriod couplings fields) =
      intrinsicBulkPairedAbelianBilinear period hPeriod fields fields := by
  change finiteFramePairedC2FullBRSTGaugeAction period hPeriod frame frame frame metric metric couplings
    (0, (fields, 0)) = _
  simp only [finiteFramePairedC2FullBRSTGaugeAction,
    finiteFramePairedC2FullBRSTGaugeAbelianProjection_apply,
    finiteFramePairedC2FullBRSTGaugeDiffeomorphismProjection_apply,
    finiteFramePairedC2AbelianBRSTAction, Prod.fst_zero, Prod.snd_zero]
  rw [finiteFramePairedDiffeomorphismBRSTAction_zero_nonminimal period hPeriod
    frame frame frame metric metric 0 couplings, add_zero,
    frameFreeAbelianBRSTAction_eq_bilinear, frameFreeAbelianBRSTAction_eq_bilinear]
  rfl

theorem intrinsicBulkBRSTHessian_pairedAbelian
    (first second : IntrinsicBulkPairedAbelianCore period hPeriod) :
    intrinsicBulkBRSTHessian period hPeriod couplings
      (intrinsicBulkPairedAbelianInsertion period hPeriod couplings first)
      (intrinsicBulkPairedAbelianInsertion period hPeriod couplings second) =
      intrinsicBulkPairedAbelianBilinear period hPeriod first second +
        intrinsicBulkPairedAbelianBilinear period hPeriod second first :=
  quadratic_restriction_hessian (intrinsicBulkBRSTAction period hPeriod couplings)
    (intrinsicBulkPairedAbelianInsertion period hPeriod couplings)
    (intrinsicBulkPairedAbelianBilinear period hPeriod)
    (intrinsicBulkBRSTAction_contDiffAt_zero period hPeriod couplings 0 ⟨0, 0, 0, 0, 0⟩)
    (intrinsicBulkBRSTAction_pairedAbelian_restriction period hPeriod couplings) first second

def intrinsicBulkSmoothPairedAbelianFields (state : GlobalPairedAbelianBRSTState period hPeriod) :
    IntrinsicBulkPairedAbelianCore period hPeriod :=
  ((finiteFrameSmoothAbelianBRSTCore period hPeriod frame metric 0
      (state.potential .plus) (state.nonminimal .plus)).2,
   (finiteFrameSmoothAbelianBRSTCore period hPeriod frame metric 0
      (state.potential .minus) (state.nonminimal .minus)).2)

theorem intrinsicBulkPairedAbelianInsertion_smooth
    (state : GlobalPairedAbelianBRSTState period hPeriod) :
    intrinsicBulkPairedAbelianInsertion period hPeriod couplings
      (intrinsicBulkSmoothPairedAbelianFields period hPeriod state) =
      intrinsicBulkSmoothAbelianBRSTInsertion period hPeriod couplings state := by
  unfold intrinsicBulkSmoothAbelianBRSTInsertion
  dsimp only [finiteFrameSmoothAbelianBRSTCore]
  rw [(smoothToGeneralMetricRelativeC2Core period hPeriod frame metric).map_zero]
  rfl

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkPairedAbelianHessian4D
