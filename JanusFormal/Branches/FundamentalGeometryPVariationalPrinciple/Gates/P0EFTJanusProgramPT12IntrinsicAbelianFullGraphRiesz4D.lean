import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicAbelianFullGraph4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBulkAbelianGraphPairing4D

/-! Bounded self-adjoint realization of the complete Abelian Hessian:
physical Maxwell plus the unchanged off-shell BRST form, on their joint graph. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianFullGraphRiesz4D
set_option autoImplicit false
noncomputable section

private def combinedPullback {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    [NormedAddCommGroup G] [NormedSpace Real G]
    (p : E →L[Real] F) (q : E →L[Real] G)
    (A : F →L[Real] F →L[Real] Real) (B : G →L[Real] G →L[Real] Real) :
    E →L[Real] E →L[Real] Real := A.bilinearComp p p + B.bilinearComp q q

private theorem real_pairing_comm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace Real E] [CompleteSpace E] (T : E →L[Real] E) (hT : IsSelfAdjoint T)
    (first second : E) : inner Real (T first) second = inner Real (T second) first :=
  ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT) first second).trans (real_inner_comm _ _)

private theorem riesz_selfAdjoint {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace Real E] [CompleteSpace E] (B : E →L[Real] E →L[Real] Real)
    (hB : ∀ first second, B first second = B second first) :
    IsSelfAdjoint (InnerProductSpace.continuousLinearMapOfBilin B) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro first second
  exact (InnerProductSpace.continuousLinearMapOfBilin_apply B first second).trans
    ((hB first second).trans
      ((InnerProductSpace.continuousLinearMapOfBilin_apply B second first).symm.trans (real_inner_comm _ _)))

open P0EFTJanusProgramPT12IntrinsicAbelianFullGraph4D
open P0EFTJanusProgramPT12IntrinsicAbelianMaxwellGraphRiesz4D
open P0EFTJanusProgramPT12IntrinsicBulkAbelianGraphPairing4D
open P0EFTJanusProgramPT12IntrinsicBulkPairedAbelianHessian4D
open P0EFTJanusProgramPT12IntrinsicBulkMaxwellColumn4D
open P0EFTJanusProgramPT12IntrinsicBulkMaxwellRestriction4D
open P0EFTJanusProgramPT12IntrinsicBulkHessian4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusReciprocalBimetricPotential
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPT12IntrinsicBulkGeometry4D
open P0EFTJanusProgramPT12IntrinsicAbelianMaxwellLorenzGraph4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev Q := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (Q period hPeriod) := reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (Q period hPeriod) := reflectedSphereQuotient_isManifold period hPeriod
local instance : MeasureTheory.IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
local notation "base" => GlobalCandidateAGeometry.plusMetric (intrinsicBulkGeometry period hPeriod)
local notation "State" => GlobalPairedAbelianBRSTState period hPeriod
local notation "Maxwell" => IntrinsicAbelianMaxwellLorenzGraph period hPeriod
local notation "BRST" => GlobalPairedAbelianOffShellGraphHilbert period hPeriod (fun _ => base)
local instance maxwellGroup : NormedAddCommGroup Maxwell := inferInstance
local instance : SeminormedAddCommGroup Maxwell := (maxwellGroup period hPeriod).toSeminormedAddCommGroup
local instance : InnerProductSpace Real Maxwell :=
  P0EFTJanusProgramPT12IntrinsicAbelianMaxwellGraphRiesz4D.graphInnerProductSpace period hPeriod
local instance : NormedSpace Real Maxwell := (inferInstance : InnerProductSpace Real Maxwell).toNormedSpace
local instance brstGroup : NormedAddCommGroup BRST := inferInstance
local instance : SeminormedAddCommGroup BRST := (brstGroup period hPeriod).toSeminormedAddCommGroup
local instance : InnerProductSpace Real BRST := inferInstance
local instance : NormedSpace Real BRST := (inferInstance : InnerProductSpace Real BRST).toNormedSpace
local instance : CompleteSpace BRST := globalPairedAbelianOffShellGraphCompleteSpace period hPeriod (fun _ => base)

local notation "Graph" => IntrinsicAbelianFullGraph period hPeriod
local instance graphGroup : NormedAddCommGroup Graph := inferInstance
local instance : SeminormedAddCommGroup Graph := (graphGroup period hPeriod).toSeminormedAddCommGroup
local instance : InnerProductSpace Real Graph := intrinsicAbelianFullGraphInnerProductSpace period hPeriod
local instance : CompleteSpace Graph := intrinsicAbelianFullGraph_complete period hPeriod
local instance graphNormedSpace : NormedSpace Real Graph := (intrinsicAbelianFullGraphInnerProductSpace period hPeriod).toNormedSpace
local instance : Module Real Graph := (graphNormedSpace period hPeriod).toModule
local instance : Star (Graph →L[Real] Graph) := ⟨ContinuousLinearMap.adjoint⟩
local instance : NormedAddCommGroup (Graph →L[Real] Real) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace Real (Graph →L[Real] Real) := ContinuousLinearMap.toNormedSpace
variable (couplings : GlobalCandidateAActionCouplings)

def intrinsicAbelianFullGraphHessian : Graph →L[Real] Graph →L[Real] Real :=
  combinedPullback (intrinsicAbelianFullMaxwell period hPeriod) (intrinsicAbelianFullBRST period hPeriod)
    ((innerSL Real).comp (intrinsicAbelianMaxwellGraphRiesz period hPeriod couplings))
    (globalPairedAbelianOffShellHessian period hPeriod (fun _ => base))

theorem intrinsicAbelianFullGraphHessian_comm (first second : Graph) :
    intrinsicAbelianFullGraphHessian period hPeriod couplings first second =
      intrinsicAbelianFullGraphHessian period hPeriod couplings second first :=
  congrArg₂ (fun left right : Real => left + right)
    (real_pairing_comm (intrinsicAbelianMaxwellGraphRiesz period hPeriod couplings)
      (intrinsicAbelianMaxwellGraphRiesz_selfAdjoint period hPeriod couplings)
      (intrinsicAbelianFullMaxwell period hPeriod first) (intrinsicAbelianFullMaxwell period hPeriod second))
    (globalPairedAbelianOffShellHessian_comm period hPeriod (fun _ => base)
      (intrinsicAbelianFullBRST period hPeriod first) (intrinsicAbelianFullBRST period hPeriod second))

def intrinsicAbelianFullGraphRiesz : Graph →L[Real] Graph :=
  InnerProductSpace.continuousLinearMapOfBilin (intrinsicAbelianFullGraphHessian period hPeriod couplings)

theorem intrinsicAbelianFullGraphRiesz_selfAdjoint :
    IsSelfAdjoint (intrinsicAbelianFullGraphRiesz period hPeriod couplings) :=
  riesz_selfAdjoint _ (intrinsicAbelianFullGraphHessian_comm period hPeriod couplings)

theorem intrinsicAbelianFullGraphRiesz_pairing (first second : Graph) :
    inner Real (intrinsicAbelianFullGraphRiesz period hPeriod couplings first) second =
      inner Real (intrinsicAbelianMaxwellGraphRiesz period hPeriod couplings
        (intrinsicAbelianFullMaxwell period hPeriod first)) (intrinsicAbelianFullMaxwell period hPeriod second) +
      globalPairedAbelianOffShellHessian period hPeriod (fun _ => base)
        (intrinsicAbelianFullBRST period hPeriod first) (intrinsicAbelianFullBRST period hPeriod second) :=
  InnerProductSpace.continuousLinearMapOfBilin_apply _ first second

private theorem brst_smooth_pairing (first second : State) :
    globalPairedAbelianOffShellHessian period hPeriod (fun _ => base)
      (globalPairedAbelianOffShellSmoothEmbedding period hPeriod (fun _ => base) first)
      (globalPairedAbelianOffShellSmoothEmbedding period hPeriod (fun _ => base) second) =
    intrinsicBulkPairedAbelianBilinear period hPeriod
      (intrinsicBulkSmoothPairedAbelianFields period hPeriod first) (intrinsicBulkSmoothPairedAbelianFields period hPeriod second) +
    intrinsicBulkPairedAbelianBilinear period hPeriod
      (intrinsicBulkSmoothPairedAbelianFields period hPeriod second) (intrinsicBulkSmoothPairedAbelianFields period hPeriod first) := by
  have hGraph := (globalPairedAbelianOffShellHessian_smooth_eq_BRST period hPeriod
    (fun _ => base) first second).trans
      (globalPairedAbelianGaugeFermionBRSTPolarizationAction_eq_mixed period hPeriod
        (fun _ => base) first second (intrinsicCanonicalLorentzVolumeMeasure period hPeriod))
  exact hGraph.trans (congrArg₂ (fun left right : Real => left + right)
    (intrinsicBulkPairedAbelianBilinear_smooth_eq_mixed period hPeriod first second).symm
    (intrinsicBulkPairedAbelianBilinear_smooth_eq_mixed period hPeriod second first).symm)

theorem intrinsicAbelianFullGraphRiesz_smooth_pairing (first second : State) :
    inner Real (intrinsicAbelianFullGraphRiesz period hPeriod couplings
      (intrinsicAbelianFullSmooth period hPeriod first)) (intrinsicAbelianFullSmooth period hPeriod second) =
    (intrinsicBulkMaxwellPairing period hPeriod couplings
      ((intrinsicBulkSmoothPairedAbelianFields period hPeriod first).1.1, (intrinsicBulkSmoothPairedAbelianFields period hPeriod first).2.1)
      ((intrinsicBulkSmoothPairedAbelianFields period hPeriod second).1.1, (intrinsicBulkSmoothPairedAbelianFields period hPeriod second).2.1) +
    intrinsicBulkMaxwellPairing period hPeriod couplings
      ((intrinsicBulkSmoothPairedAbelianFields period hPeriod second).1.1, (intrinsicBulkSmoothPairedAbelianFields period hPeriod second).2.1)
      ((intrinsicBulkSmoothPairedAbelianFields period hPeriod first).1.1, (intrinsicBulkSmoothPairedAbelianFields period hPeriod first).2.1)) +
    (intrinsicBulkPairedAbelianBilinear period hPeriod
      (intrinsicBulkSmoothPairedAbelianFields period hPeriod first) (intrinsicBulkSmoothPairedAbelianFields period hPeriod second) +
    intrinsicBulkPairedAbelianBilinear period hPeriod
      (intrinsicBulkSmoothPairedAbelianFields period hPeriod second) (intrinsicBulkSmoothPairedAbelianFields period hPeriod first)) :=
  (intrinsicAbelianFullGraphRiesz_pairing period hPeriod couplings
    (intrinsicAbelianFullSmooth period hPeriod first) (intrinsicAbelianFullSmooth period hPeriod second)).trans
      (congrArg₂ (fun physical brst : Real => physical + brst)
        (intrinsicAbelianMaxwellGraphRiesz_smooth_pairing period hPeriod couplings first.potential second.potential)
        (brst_smooth_pairing period hPeriod first second))

theorem intrinsicAbelianFullGraphRiesz_eq_bulkHessian
    (interactionScale : Real) (coefficients : PotentialCoefficients) (first second : State) :
    inner Real (intrinsicAbelianFullGraphRiesz period hPeriod couplings
      (intrinsicAbelianFullSmooth period hPeriod first)) (intrinsicAbelianFullSmooth period hPeriod second) =
    intrinsicBulkHessian period hPeriod couplings interactionScale coefficients
      (intrinsicBulkPairedAbelianInsertion period hPeriod couplings (intrinsicBulkSmoothPairedAbelianFields period hPeriod first))
      (intrinsicBulkPairedAbelianInsertion period hPeriod couplings (intrinsicBulkSmoothPairedAbelianFields period hPeriod second)) :=
  (intrinsicAbelianFullGraphRiesz_smooth_pairing period hPeriod couplings first second).trans
    (intrinsicBulkHessian_pairedAbelian period hPeriod couplings interactionScale coefficients
      (intrinsicBulkSmoothPairedAbelianFields period hPeriod first) (intrinsicBulkSmoothPairedAbelianFields period hPeriod second)).symm

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianFullGraphRiesz4D


