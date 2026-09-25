import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicAbelianMaxwellStrongSmooth4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ClosedFeatureCore4D

/-! Minimal closed symmetric Maxwell Jacobi in physical potential L². -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianMaxwellStrongClosed4D
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalAbelianLorenzGraphRiesz4D
open P0EFTJanusFiniteFrameLorenzCovariantTrace4D P0EFTJanusFiniteFrameC2AbelianOperators4D
open P0EFTJanusFiniteFrameC2MaxwellCurvature4D
open P0EFTJanusProgramPT12IntrinsicBulkGeometry4D P0EFTJanusProgramPT12FrameFreeMaxwellBilinear4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev Q := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (Q period hPeriod) := reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (Q period hPeriod) := reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (Q period hPeriod) := reflectedSphereQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (Q period hPeriod) := borel _
local instance : BorelSpace (Q period hPeriod) where measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
open P0EFTJanusProgramPT12IntrinsicAbelianPotentialL2Core4D
open P0EFTJanusProgramPT12IntrinsicAbelianMaxwellLorenzGraph4D
open P0EFTJanusProgramPT12FrameFreeMaxwellCurvaturePairing4D
open P0EFTJanusProgramPT12FrameFreeFrameDerivativeAdjoint4D
open P0EFTJanusProgramPT12CanonicalFirstOrderColumn4D
open P0EFTJanusFiniteFrameKoszulCoefficients4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothApproximation4D
local notation "frame" => finiteSmoothTangentFrame period hPeriod
local notation "base" => GlobalCandidateAGeometry.plusMetric (intrinsicBulkGeometry period hPeriod)
local notation "Smooth" => GlobalPairedAbelianPotentialSmooth period hPeriod
local notation "Scalar" => SmoothQuotientField period hPeriod Real
local notation "Potential" => IntrinsicAbelianPotentialL2Core period hPeriod
local notation "Curvature" => IntrinsicAbelianCurvatureL2 period hPeriod
local instance potentialGroup : NormedAddCommGroup Potential := inferInstance
local instance : SeminormedAddCommGroup Potential := (potentialGroup period hPeriod).toSeminormedAddCommGroup
local instance : NormedSpace Real Potential := inferInstance
local instance curvatureGroup : NormedAddCommGroup Curvature := inferInstance
local instance : SeminormedAddCommGroup Curvature := (curvatureGroup period hPeriod).toSeminormedAddCommGroup
local instance : NormedSpace Real Curvature := inferInstance

open P0EFTJanusProgramPT12IntrinsicAbelianCurvatureL2Graph4D

open P0EFTJanusProgramPT12IntrinsicAbelianCurvatureClosed4D
local notation "H" => CanonicalPhysicalBulkL2 period hPeriod
local notation "Index" => IntrinsicAbelianCurvatureIndex period hPeriod
local instance : InnerProductSpace Real Potential :=
  Submodule.innerProductSpace (𝕜 := Real) (intrinsicAbelianPotentialL2Submodule period hPeriod)
local instance : InnerProductSpace Real Curvature := inferInstance
local instance : CompleteSpace Curvature := inferInstance

open P0EFTJanusProgramPT12IntrinsicAbelianCurvatureAdjointColumns4D
open P0EFTJanusProgramPT12IntrinsicAbelianCurvatureSmoothAdjoint4D
open P0EFTJanusProgramPT12SmoothMatrixL24D
open P0EFTJanusProgramPT12L2VolumeMultiplier4D

open P0EFTJanusProgramPT12IntrinsicAbelianCurvatureWeightColumns4D
open P0EFTJanusProgramPT12IntrinsicAbelianMaxwellSmoothWeight4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPT12IntrinsicAbelianMaxwellCurvatureWeight4D
open P0EFTJanusProgramPT12IntrinsicAbelianMaxwellGraphPairing4D
open P0EFTJanusProgramPT12IntrinsicAbelianMaxwellGraphRiesz4D
open P0EFTJanusFiniteFrameC2InverseMetricCoefficients4D
open P0EFTJanusFiniteFrameC2CanonicalVolume4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
local notation "μ" => intrinsicCanonicalLorentzVolumeMeasure period hPeriod
local notation "Graph" => IntrinsicAbelianMaxwellLorenzGraph period hPeriod
local instance : NormedAddCommGroup Graph := inferInstance
local instance : NormedSpace Real Graph := inferInstance
open P0EFTJanusProgramPT12IntrinsicAbelianMaxwellCurvatureFactor4D

open P0EFTJanusProgramPT12IntrinsicAbelianMaxwellStrongSmooth4D
open P0EFTJanusProgramPT12DenseAdjointGraphClosable4D
open P0EFTJanusProgramPT12ClosedFeatureOperator4D
open P0EFTJanusProgramPT12ClosedFeatureCore4D
variable (couplings : GlobalCandidateAActionCouplings)
local notation "inc" => intrinsicAbelianPotentialL2Smooth period hPeriod
local notation "action" => intrinsicAbelianMaxwellStrongSmooth period hPeriod couplings

private theorem graph_single :
    Function.Injective (fun point : linearFeatureGraphClosure inc action => point.val.1) :=
  linearFeatureGraphClosure_fst_injective inc action action
    (intrinsicAbelianPotentialL2Smooth_denseRange period hPeriod)
    (intrinsicAbelianMaxwellStrongSmooth_symmetric period hPeriod couplings)

/-- The minimal closed realization of the native strong Maxwell action. -/
def intrinsicAbelianMaxwellStrongMinimal : Potential →ₗ.[Real] Potential :=
  closedFeatureOperator inc action

theorem intrinsicAbelianMaxwellStrongMinimal_graph :
    (intrinsicAbelianMaxwellStrongMinimal period hPeriod couplings).graph =
      linearFeatureGraphClosure inc action :=
  closedFeatureOperator_graph inc action (graph_single period hPeriod couplings)

theorem intrinsicAbelianMaxwellStrongMinimal_isClosed :
    (intrinsicAbelianMaxwellStrongMinimal period hPeriod couplings).IsClosed :=
  closedFeatureOperator_isClosed inc action (graph_single period hPeriod couplings)

theorem intrinsicAbelianMaxwellStrongMinimal_smooth_mem (potential : Smooth) :
    inc potential ∈ (intrinsicAbelianMaxwellStrongMinimal period hPeriod couplings).domain :=
  closedFeatureOperator_smooth_mem inc action potential

theorem intrinsicAbelianMaxwellStrongMinimal_smooth_apply (potential : Smooth) :
    intrinsicAbelianMaxwellStrongMinimal period hPeriod couplings
      ⟨inc potential, intrinsicAbelianMaxwellStrongMinimal_smooth_mem period hPeriod couplings potential⟩ =
      action potential :=
  closedFeatureOperator_smooth_apply inc action (graph_single period hPeriod couplings) potential

theorem intrinsicAbelianMaxwellStrongMinimal_dense_domain :
    Dense ((intrinsicAbelianMaxwellStrongMinimal period hPeriod couplings).domain : Set Potential) :=
  closedFeatureOperator_dense_domain inc action (intrinsicAbelianPotentialL2Smooth_denseRange period hPeriod)

theorem intrinsicAbelianMaxwellStrongMinimal_hasCore :
    (intrinsicAbelianMaxwellStrongMinimal period hPeriod couplings).HasCore (inc).range :=
  closedFeatureOperator_hasCore inc action (graph_single period hPeriod couplings)

theorem intrinsicAbelianMaxwellStrongMinimal_le
    (extension : Potential →ₗ.[Real] Potential) (hClosed : extension.IsClosed)
    (hExtends : ∀ potential : Smooth, (inc potential, action potential) ∈ extension.graph) :
    intrinsicAbelianMaxwellStrongMinimal period hPeriod couplings ≤ extension :=
  closedFeatureOperator_minimal inc action (graph_single period hPeriod couplings) extension hClosed hExtends

/-- Symmetry persists under closure; this does not claim self-adjointness. -/
theorem intrinsicAbelianMaxwellStrongMinimal_symmetric :
    (intrinsicAbelianMaxwellStrongMinimal period hPeriod couplings).IsFormalAdjoint
      (intrinsicAbelianMaxwellStrongMinimal period hPeriod couplings) := by
  let J := intrinsicAbelianMaxwellStrongMinimal period hPeriod couplings
  have hGraph := intrinsicAbelianMaxwellStrongMinimal_graph period hPeriod couplings
  intro first second
  have hFirst : (first.val, J first) ∈ linearFeatureGraphClosure inc action := by
    rw [← hGraph]
    exact J.mem_graph first
  have hSecond : (second.val, J second) ∈ linearFeatureGraphClosure inc action := by
    rw [← hGraph]
    exact J.mem_graph second
  have hClosed : IsClosed {pair : Potential × Potential |
      inner Real (J first) pair.1 = inner Real first.val pair.2} :=
    isClosed_eq (by fun_prop) (by fun_prop)
  have hSubset : (((inc).prod action).range : Set (Potential × Potential)) ⊆
      {pair | inner Real (J first) pair.1 = inner Real first.val pair.2} := by
    rintro _ ⟨potential, rfl⟩
    exact linearFeatureGraphClosure_pairing inc action action
      (intrinsicAbelianMaxwellStrongSmooth_symmetric period hPeriod couplings)
      ⟨_, hFirst⟩ potential
  exact closure_minimal hSubset hClosed hSecond

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianMaxwellStrongClosed4D
