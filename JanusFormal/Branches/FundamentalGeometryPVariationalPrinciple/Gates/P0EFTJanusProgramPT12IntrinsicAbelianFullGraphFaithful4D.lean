import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicAbelianFullGraph4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicAbelianMaxwellGraphFaithful4D

/-! The joint completion is a faithful domain over the native off-shell BRST graph. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianFullGraphFaithful4D
set_option autoImplicit false
noncomputable section
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

open P0EFTJanusProgramPGlobalAbelianLorenzGraphRiesz4D
open P0EFTJanusProgramPT12IntrinsicAbelianFullGraph4D
open P0EFTJanusProgramPT12IntrinsicAbelianMaxwellGraphFaithful4D
local notation "Graph" => IntrinsicAbelianFullGraph period hPeriod
local notation "LorenzAmbient" => GlobalPairedAbelianLorenzGraphAmbient period hPeriod
local instance graphGroup : NormedAddCommGroup Graph := inferInstance
local instance : SeminormedAddCommGroup Graph := (graphGroup period hPeriod).toSeminormedAddCommGroup
local instance : InnerProductSpace Real Graph := intrinsicAbelianFullGraphInnerProductSpace period hPeriod
local instance : NormedSpace Real Graph := (inferInstance : InnerProductSpace Real Graph).toNormedSpace
local instance lorenzGroup : NormedAddCommGroup LorenzAmbient := inferInstance
local instance : SeminormedAddCommGroup LorenzAmbient := (lorenzGroup period hPeriod).toSeminormedAddCommGroup
local instance : NormedSpace Real LorenzAmbient := inferInstance
local instance : MetricSpace LorenzAmbient := (lorenzGroup period hPeriod).toMetricSpace

/-- Both copies of the potential and its Lorenz feature agree throughout the completion. -/
theorem intrinsicAbelianFullLorenz_agreement (point : Graph) :
    (intrinsicAbelianMaxwellLorenzForget period hPeriod
      (intrinsicAbelianFullMaxwell period hPeriod point)).val =
    globalPairedAbelianOffShellPotentialAmbientProjection period hPeriod (fun _ => base)
      (intrinsicAbelianFullBRST period hPeriod point) := by
  let left : Graph →L[Real] LorenzAmbient :=
    ((globalPairedAbelianLorenzGraphSubmodule period hPeriod (fun _ => base)).subtypeL.comp
      (intrinsicAbelianMaxwellLorenzForget period hPeriod)).comp (intrinsicAbelianFullMaxwell period hPeriod)
  let right : Graph →L[Real] LorenzAmbient :=
    (globalPairedAbelianOffShellPotentialAmbientProjection period hPeriod (fun _ => base)).comp
      (intrinsicAbelianFullBRST period hPeriod)
  have hClosed : IsClosed {point : Graph | left point = right point} := by
    have hNorm : IsClosed {point : Graph | ‖left point - right point‖ = (0 : Real)} :=
      isClosed_eq (left.continuous.sub right.continuous).norm continuous_const
    simpa only [norm_eq_zero, sub_eq_zero] using hNorm
  have hRange : Set.range (intrinsicAbelianFullSmooth period hPeriod) ⊆
      {point : Graph | left point = right point} := by
    rintro _ ⟨state, rfl⟩
    rfl
  exact closure_minimal hRange hClosed
    (by rw [(intrinsicAbelianFullSmooth_denseRange period hPeriod).closure_range]; trivial)

/-- Adding the Maxwell graph creates no vertical modes over the BRST graph. -/
theorem intrinsicAbelianFullBRST_injective :
    Function.Injective (intrinsicAbelianFullBRST period hPeriod) := by
  intro first second hBRST
  apply Subtype.ext
  apply WithLp.ofLp_injective 2
  refine Prod.ext ?_ hBRST
  apply intrinsicAbelianMaxwellLorenzForget_injective period hPeriod
  apply Subtype.ext
  change (intrinsicAbelianMaxwellLorenzForget period hPeriod
    (intrinsicAbelianFullMaxwell period hPeriod first)).val =
    (intrinsicAbelianMaxwellLorenzForget period hPeriod
      (intrinsicAbelianFullMaxwell period hPeriod second)).val
  rw [intrinsicAbelianFullLorenz_agreement, intrinsicAbelianFullLorenz_agreement, hBRST]

/-- Its image is dense in the original BRST graph, since it includes the native smooth core. -/
theorem intrinsicAbelianFullBRST_denseRange : DenseRange (intrinsicAbelianFullBRST period hPeriod) := by
  apply (globalPairedAbelianOffShellSmoothEmbedding_denseRange period hPeriod (fun _ => base)).mono
  rintro _ ⟨state, rfl⟩
  exact ⟨intrinsicAbelianFullSmooth period hPeriod state, rfl⟩

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianFullGraphFaithful4D
