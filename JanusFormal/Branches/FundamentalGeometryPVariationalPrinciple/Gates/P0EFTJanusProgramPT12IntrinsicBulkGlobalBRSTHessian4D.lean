import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBulkPairedDiffeomorphismHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeAbelianBilinearFamily4D

/-! Global BRST pairing against arbitrary native bulk tests. The coefficient
family retains all four native actions before its second jet is frozen. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkGlobalBRSTHessian4D
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusProgramPT12BilinearSecondJetFreeze4D

section Pullback
variable {E F X : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [NormedAddCommGroup F] [NormedSpace Real F] [NormedAddCommGroup X] [NormedSpace Real X]
local instance : NormedAddCommGroup (F →L[Real] Real) := inferInstance
local instance : NormedSpace Real (F →L[Real] Real) := inferInstance
local instance : NormedAddCommGroup (E →L[Real] Real) := inferInstance
local instance : NormedSpace Real (E →L[Real] Real) := inferInstance
local instance : NormedAddCommGroup (F →L[Real] F →L[Real] Real) := inferInstance
local instance : NormedSpace Real (F →L[Real] F →L[Real] Real) := inferInstance
local instance : NormedAddCommGroup (E →L[Real] F →L[Real] Real) := inferInstance
local instance : NormedSpace Real (E →L[Real] F →L[Real] Real) := inferInstance
local instance : NormedAddCommGroup (F →L[Real] E →L[Real] Real) := inferInstance
local instance : NormedSpace Real (F →L[Real] E →L[Real] Real) := inferInstance
local instance : NormedAddCommGroup (E →L[Real] E →L[Real] Real) := inferInstance
local instance : NormedSpace Real (E →L[Real] E →L[Real] Real) := inferInstance

private theorem coefficientPullback_contDiffAt_zero
    (coefficient : X → F →L[Real] F →L[Real] Real)
    (metricProjection : E →L[Real] X) (fieldsProjection : E →L[Real] F)
    (hCoefficient : ContDiffAt Real 2 coefficient 0) :
    ContDiffAt Real 2 (fun x =>
      (coefficient (metricProjection x)).bilinearComp fieldsProjection fieldsProjection) 0 := by
  have hAt : ContDiffAt Real 2 coefficient (metricProjection 0) := by
    simpa only [map_zero] using hCoefficient
  have hComposition := hAt.comp 0 metricProjection.contDiff.contDiffAt
  have hFirst := hComposition.clm_comp
    (show ContDiffAt Real 2 (fun _ : E => fieldsProjection) 0 from contDiffAt_const)
  have hFlip := (ContinuousLinearMap.flipₗᵢ Real E F Real).contDiff.comp_contDiffAt 0 hFirst
  have hSecond := hFlip.clm_comp
    (show ContDiffAt Real 2 (fun _ : E => fieldsProjection) 0 from contDiffAt_const)
  exact (ContinuousLinearMap.flipₗᵢ Real E E Real).contDiff.comp_contDiffAt 0 hSecond

private theorem actionHessian_eq_frozenCoefficient
    (action : E → Real) (coefficient : E → E →L[Real] E →L[Real] Real)
    (hAction : ∀ x, action x = coefficient x x x)
    (hCoefficient : ContDiffAt Real 2 coefficient 0) (first second : E) :
    fderiv Real (fderiv Real action) 0 first second =
      coefficient 0 first second + coefficient 0 second first := by
  have hFreeze := bilinearCoefficient_second_fderiv_zero coefficient
    (ContinuousLinearMap.id Real E) (ContinuousLinearMap.id Real E) hCoefficient first second
  exact (congrArg (fun f : E → Real => fderiv Real (fderiv Real f) 0 first second)
    (funext hAction)).trans hFreeze

private theorem threeFamilies_contDiffAt_zero (first second third : E → F)
    (hFirst : ContDiffAt Real 2 first 0) (hSecond : ContDiffAt Real 2 second 0)
    (hThird : ContDiffAt Real 2 third 0) :
    ContDiffAt Real 2 (fun x => first x + second x + third x) 0 :=
  (hFirst.add hSecond).add hThird

private theorem bilinear_eq_symmetrization (H K : E →L[Real] E →L[Real] Real)
    (hPairing : ∀ first second, H first second = K first second + K second first) :
    H = K + K.flip := by
  ext first second
  exact hPairing first second
end Pullback

open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusProgramPGlobalCovariantAction4D P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPCandidateADiagonalDiffeomorphismKineticAdjointBridge4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusFiniteFrameC2AbelianBRSTAction4D P0EFTJanusFiniteFramePairedDiffeomorphismBRSTAction4D
open P0EFTJanusFiniteFramePairedC2FullBRSTGaugeAction4D
open P0EFTJanusProgramPT12IntrinsicBulkGeometry4D P0EFTJanusProgramPT12IntrinsicBulkActionCore4D
open P0EFTJanusProgramPT12IntrinsicBulkBRSTDecomposition4D
open P0EFTJanusProgramPT12FrameFreeAbelianBilinearFamily4D
open P0EFTJanusProgramPT12FrameFreeDiffeomorphismBilinearFamily4D
open P0EFTJanusProgramPT12IntrinsicBulkPairedDiffeomorphismHessian4D
open P0EFTJanusProgramPT12BilinearSecondJetFreeze4D
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
local notation "AbelianInput" => FiniteFrameC2AbelianBRSTCore period hPeriod frame metric
local notation "AbelianFields" => FrameFreeAbelianBRSTFields period hPeriod frame
local notation "DiffeomorphismInput" => IntrinsicBulkPairedDiffeomorphismCore period hPeriod
local notation "GaugeInput" => FiniteFramePairedC2FullBRSTGaugeCore period hPeriod frame frame frame metric metric
local instance : NormedAddCommGroup (GeneralMetricRelativeC2Core period hPeriod frame metric) := inferInstance
local instance : NormedSpace Real (GeneralMetricRelativeC2Core period hPeriod frame metric) :=
  Submodule.normedSpace (GeneralMetricRelativeC2Core period hPeriod frame metric)
local instance : NormedAddCommGroup
    (P0EFTJanusFiniteFrameDiffeomorphismC2Core4D.FiniteFrameDiffeomorphismNonminimalC2Core period hPeriod frame) :=
  inferInstance
local instance : NormedSpace Real
    (P0EFTJanusFiniteFrameDiffeomorphismC2Core4D.FiniteFrameDiffeomorphismNonminimalC2Core period hPeriod frame) :=
  inferInstance
local instance : NormedAddCommGroup AbelianFields := inferInstance
local instance : NormedSpace Real AbelianFields := inferInstance
local instance : NormedAddCommGroup AbelianInput := inferInstance
local instance : NormedSpace Real AbelianInput := inferInstance
local instance : NormedAddCommGroup DiffeomorphismInput := inferInstance
local instance : NormedSpace Real DiffeomorphismInput := inferInstance
local instance : NormedAddCommGroup GaugeInput := inferInstance
local instance : NormedSpace Real GaugeInput := inferInstance

variable (couplings : GlobalCandidateAActionCouplings)
local notation "Bulk" => IntrinsicBulkCore period hPeriod couplings
local instance coreNormedAddCommGroup : NormedAddCommGroup Bulk := inferInstance
local instance : AddZeroClass Bulk := (coreNormedAddCommGroup period hPeriod couplings).toAddCommGroup.toAddZeroClass
local instance : NormedSpace Real Bulk :=
  P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D.instNormedSpaceRealFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCore
    period hPeriod (intrinsicBulkGeometry period hPeriod) frame couplings
local instance : NormedAddCommGroup (Bulk →L[Real] Real) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace Real (Bulk →L[Real] Real) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (Bulk →L[Real] Bulk →L[Real] Real) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace Real (Bulk →L[Real] Bulk →L[Real] Real) :=
  ContinuousLinearMap.toNormedSpace

def intrinsicBulkBRSTGaugeProjection : Bulk →L[Real] GaugeInput :=
  (ContinuousLinearMap.fst Real _ _).comp (ContinuousLinearMap.fst Real _ _)

def intrinsicBulkBRSTAbelianPlusInput : Bulk →L[Real] AbelianInput :=
  (ContinuousLinearMap.fst Real _ _).comp
    ((finiteFramePairedC2FullBRSTGaugeAbelianProjection period hPeriod frame frame frame metric metric).comp
      (intrinsicBulkBRSTGaugeProjection period hPeriod couplings))

def intrinsicBulkBRSTAbelianMinusInput : Bulk →L[Real] AbelianInput :=
  (ContinuousLinearMap.snd Real _ _).comp
    ((finiteFramePairedC2FullBRSTGaugeAbelianProjection period hPeriod frame frame frame metric metric).comp
      (intrinsicBulkBRSTGaugeProjection period hPeriod couplings))

def intrinsicBulkBRSTDiffeomorphismInput : Bulk →L[Real] DiffeomorphismInput :=
  (finiteFramePairedC2FullBRSTGaugeDiffeomorphismProjection period hPeriod frame frame frame metric metric).comp
    (intrinsicBulkBRSTGaugeProjection period hPeriod couplings)

private def abelianCoefficientPullback (projection : Bulk →L[Real] AbelianInput) (point : Bulk) :
    Bulk →L[Real] Bulk →L[Real] Real :=
  (frameFreeAbelianBRSTBilinearCoefficient period hPeriod frame metric (projection point).1).bilinearComp
    ((ContinuousLinearMap.snd Real _ _).comp projection)
    ((ContinuousLinearMap.snd Real _ _).comp projection)

private theorem abelianCoefficientPullback_contDiffAt_zero (projection : Bulk →L[Real] AbelianInput) :
    ContDiffAt Real 2 (abelianCoefficientPullback period hPeriod couplings projection) 0 := by
  have hZero := zero_mem_generalMetricRelativeC2OpenDomain period hPeriod frame metric
  have hK : ContDiffAt Real 2 (frameFreeAbelianBRSTBilinearCoefficient period hPeriod frame metric) 0 :=
    ((frameFreeAbelianBRSTBilinearCoefficient_contDiffOn_two period hPeriod frame metric) 0 hZero).contDiffAt
      ((generalMetricRelativeC2OpenDomain_isOpen period hPeriod frame metric).mem_nhds hZero)
  exact coefficientPullback_contDiffAt_zero
    (frameFreeAbelianBRSTBilinearCoefficient period hPeriod frame metric)
    ((ContinuousLinearMap.fst Real _ _).comp projection)
    ((ContinuousLinearMap.snd Real _ _).comp projection) hK

private def diffeomorphismCoefficientPullback (point : Bulk) : Bulk →L[Real] Bulk →L[Real] Real :=
  (intrinsicBulkPairedDiffeomorphismBilinearFamily period hPeriod couplings
    (intrinsicBulkBRSTDiffeomorphismInput period hPeriod couplings point)).bilinearComp
      (intrinsicBulkBRSTDiffeomorphismInput period hPeriod couplings)
      (intrinsicBulkBRSTDiffeomorphismInput period hPeriod couplings)

private theorem diffeomorphismCoefficientPullback_contDiffAt_zero :
    ContDiffAt Real 2 (diffeomorphismCoefficientPullback period hPeriod couplings) 0 := by
  have h := coefficientPullback_contDiffAt_zero
    (intrinsicBulkPairedDiffeomorphismBilinearFamily period hPeriod couplings)
    (intrinsicBulkBRSTDiffeomorphismInput period hPeriod couplings)
    (intrinsicBulkBRSTDiffeomorphismInput period hPeriod couplings)
    (intrinsicBulkPairedDiffeomorphismBilinearFamily_contDiffAt_zero period hPeriod couplings)
  exact h

/-- Both Abelian sectors and the weighted diagonal diffeomorphism sectors,
with their shared varying metrics and full native field projections. -/
def intrinsicBulkGlobalBRSTBilinearFamily (point : Bulk) : Bulk →L[Real] Bulk →L[Real] Real :=
  abelianCoefficientPullback period hPeriod couplings (intrinsicBulkBRSTAbelianPlusInput period hPeriod couplings) point +
    abelianCoefficientPullback period hPeriod couplings (intrinsicBulkBRSTAbelianMinusInput period hPeriod couplings) point +
    diffeomorphismCoefficientPullback period hPeriod couplings point

theorem intrinsicBulkGlobalBRSTBilinearFamily_contDiffAt_zero :
    ContDiffAt Real 2 (intrinsicBulkGlobalBRSTBilinearFamily period hPeriod couplings) 0 :=
  threeFamilies_contDiffAt_zero
    (abelianCoefficientPullback period hPeriod couplings (intrinsicBulkBRSTAbelianPlusInput period hPeriod couplings))
    (abelianCoefficientPullback period hPeriod couplings (intrinsicBulkBRSTAbelianMinusInput period hPeriod couplings))
    (diffeomorphismCoefficientPullback period hPeriod couplings)
    (abelianCoefficientPullback_contDiffAt_zero period hPeriod couplings
      (intrinsicBulkBRSTAbelianPlusInput period hPeriod couplings))
    (abelianCoefficientPullback_contDiffAt_zero period hPeriod couplings
      (intrinsicBulkBRSTAbelianMinusInput period hPeriod couplings))
    (diffeomorphismCoefficientPullback_contDiffAt_zero period hPeriod couplings)

private theorem abelianAction_eq_coefficientPullback
    (projection : Bulk →L[Real] AbelianInput) (point : Bulk) :
    finiteFrameC2AbelianBRSTAction period hPeriod frame metric (projection point) =
      abelianCoefficientPullback period hPeriod couplings projection point point point :=
  frameFreeAbelianBRSTAction_eq_bilinear period hPeriod frame metric
    (projection point).1 (projection point).2

private theorem diffeomorphismAction_eq_coefficientPullback (point : Bulk) :
    finiteFramePairedDiffeomorphismBRSTAction period hPeriod frame frame frame metric metric couplings
        (intrinsicBulkBRSTDiffeomorphismInput period hPeriod couplings point) =
      intrinsicBulkPairedDiffeomorphismBilinearFamily period hPeriod couplings
        (intrinsicBulkBRSTDiffeomorphismInput period hPeriod couplings point)
        (intrinsicBulkBRSTDiffeomorphismInput period hPeriod couplings point)
        (intrinsicBulkBRSTDiffeomorphismInput period hPeriod couplings point) := by
  let fields := intrinsicBulkBRSTDiffeomorphismInput period hPeriod couplings point
  let plus := finiteFramePairedDiffeomorphismBRSTPlusInput period hPeriod frame frame frame metric metric fields
  let minus := finiteFramePairedDiffeomorphismBRSTMinusInput period hPeriod frame frame frame metric metric fields
  exact congrArg₂ (fun x y : Real => candidateAPlusEinsteinKineticWeight couplings * x +
    candidateAMinusEinsteinKineticWeight couplings * y)
      (frameFreeDiffeomorphismBRSTAction_eq_bilinear period hPeriod frame metric plus.1 plus.2)
      (frameFreeDiffeomorphismBRSTAction_eq_bilinear period hPeriod frame metric minus.1 minus.2)

theorem intrinsicBulkBRSTAction_eq_globalBilinear (point : Bulk) :
    intrinsicBulkBRSTAction period hPeriod couplings point =
      intrinsicBulkGlobalBRSTBilinearFamily period hPeriod couplings point point point :=
  congrArg₂ (fun x y : Real => x + y)
    (congrArg₂ (fun x y : Real => x + y)
      (abelianAction_eq_coefficientPullback period hPeriod couplings
        (intrinsicBulkBRSTAbelianPlusInput period hPeriod couplings) point)
      (abelianAction_eq_coefficientPullback period hPeriod couplings
        (intrinsicBulkBRSTAbelianMinusInput period hPeriod couplings) point))
    (diffeomorphismAction_eq_coefficientPullback period hPeriod couplings point)

/-- The formula holds for every pair of native bulk tests, without any
sector restriction or assumed vanishing of cross terms. -/
theorem intrinsicBulkBRSTHessian_eq_globalBilinear (first second : Bulk) :
    intrinsicBulkBRSTHessian period hPeriod couplings first second =
      intrinsicBulkGlobalBRSTBilinearFamily period hPeriod couplings 0 first second +
        intrinsicBulkGlobalBRSTBilinearFamily period hPeriod couplings 0 second first :=
  actionHessian_eq_frozenCoefficient (intrinsicBulkBRSTAction period hPeriod couplings)
    (intrinsicBulkGlobalBRSTBilinearFamily period hPeriod couplings)
    (intrinsicBulkBRSTAction_eq_globalBilinear period hPeriod couplings)
    (intrinsicBulkGlobalBRSTBilinearFamily_contDiffAt_zero period hPeriod couplings) first second

theorem intrinsicBulkBRSTHessian_eq_globalBilinear_symmetrization :
    intrinsicBulkBRSTHessian period hPeriod couplings =
      intrinsicBulkGlobalBRSTBilinearFamily period hPeriod couplings 0 +
        (intrinsicBulkGlobalBRSTBilinearFamily period hPeriod couplings 0).flip :=
  bilinear_eq_symmetrization (intrinsicBulkBRSTHessian period hPeriod couplings)
    (intrinsicBulkGlobalBRSTBilinearFamily period hPeriod couplings 0)
    (intrinsicBulkBRSTHessian_eq_globalBilinear period hPeriod couplings)

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkGlobalBRSTHessian4D
