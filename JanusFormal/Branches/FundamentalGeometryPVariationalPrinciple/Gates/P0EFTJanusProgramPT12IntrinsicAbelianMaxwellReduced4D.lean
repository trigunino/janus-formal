import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicAbelianMaxwellStrongGaugeKernel4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ClosedNullPMapQuotient4D

/-! Native closed Maxwell Jacobi descended through the completed exact gauge sector. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianMaxwellReduced4D
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
open P0EFTJanusProgramPT12IntrinsicAbelianMaxwellStrongClosed4D
open P0EFTJanusProgramPT12IntrinsicAbelianCurvatureExactComplex4D
open P0EFTJanusProgramPT12DenseAdjointGraphClosable4D
variable (couplings : GlobalCandidateAActionCouplings)
local notation "Parameters" => Sector → SmoothQuotientField period hPeriod GaugeLieAlgebra
local notation "inc" => intrinsicAbelianPotentialL2Smooth period hPeriod
local notation "action" => intrinsicAbelianMaxwellStrongSmooth period hPeriod couplings
local notation "J" => intrinsicAbelianMaxwellStrongMinimal period hPeriod couplings

open P0EFTJanusProgramPT12IntrinsicAbelianMaxwellStrongGaugeKernel4D
open P0EFTJanusProgramPT12ClosedNullPMapQuotient4D
local notation "Exact" => intrinsicAbelianExactPotentialL2 period hPeriod
local instance : CompleteSpace Potential := inferInstance
local instance : IsClosed (Exact : Set Potential) := Submodule.isClosed_topologicalClosure _

abbrev IntrinsicAbelianMaxwellReducedL2 := Potential ⧸ Exact
local notation "Reduced" => IntrinsicAbelianMaxwellReducedL2 period hPeriod
local instance reducedGroup : NormedAddCommGroup Reduced := inferInstance
local instance : SeminormedAddCommGroup Reduced := (reducedGroup period hPeriod).toSeminormedAddCommGroup
local instance : NormedSpace Real Reduced := inferInstance
local instance : InnerProductSpace Real Reduced := inferInstance

private theorem gauge_null (potential : Potential) (hGauge : potential ∈ Exact) :
    (potential, 0) ∈ (J).graph :=
  intrinsicAbelianExactPotentialL2_le_maxwellZero period hPeriod couplings hGauge

/-- The reduced operator acts on the actual physical quotient by exact gauge directions. -/
def intrinsicAbelianMaxwellReduced : Reduced →ₗ.[Real] Reduced := quotientPMap J Exact

theorem intrinsicAbelianMaxwellReduced_isClosed :
    (intrinsicAbelianMaxwellReduced period hPeriod couplings).IsClosed :=
  quotientPMap_isClosed J Exact (intrinsicAbelianMaxwellStrongMinimal_isClosed period hPeriod couplings)

theorem intrinsicAbelianMaxwellReduced_symmetric :
    (intrinsicAbelianMaxwellReduced period hPeriod couplings).IsFormalAdjoint
      (intrinsicAbelianMaxwellReduced period hPeriod couplings) :=
  quotientPMap_symmetric J Exact (intrinsicAbelianMaxwellStrongMinimal_symmetric period hPeriod couplings)

theorem intrinsicAbelianMaxwellReduced_domain :
    (intrinsicAbelianMaxwellReduced period hPeriod couplings).domain = (J).domain.map (Exact).mkQ :=
  quotientPMap_domain J Exact (intrinsicAbelianMaxwellStrongMinimal_symmetric period hPeriod couplings)
    (gauge_null period hPeriod couplings)

theorem intrinsicAbelianMaxwellReduced_dense_domain :
    Dense ((intrinsicAbelianMaxwellReduced period hPeriod couplings).domain : Set Reduced) :=
  quotientPMap_denseDomain J Exact (intrinsicAbelianMaxwellStrongMinimal_symmetric period hPeriod couplings)
    (gauge_null period hPeriod couplings) (intrinsicAbelianMaxwellStrongMinimal_dense_domain period hPeriod couplings)

theorem intrinsicAbelianMaxwellReduced_graph_project (potential : (J).domain) :
    ((Exact).mkQ potential.val, (Exact).mkQ (J potential)) ∈
      (intrinsicAbelianMaxwellReduced period hPeriod couplings).graph :=
  quotientPMap_graph_project J Exact (intrinsicAbelianMaxwellStrongMinimal_symmetric period hPeriod couplings)
    (gauge_null period hPeriod couplings) potential

theorem intrinsicAbelianMaxwellReduced_smooth_graph (potential : Smooth) :
    ((Exact).mkQ (inc potential), (Exact).mkQ (action potential)) ∈
      (intrinsicAbelianMaxwellReduced period hPeriod couplings).graph := by
  have h := intrinsicAbelianMaxwellReduced_graph_project period hPeriod couplings
    ⟨_, intrinsicAbelianMaxwellStrongMinimal_smooth_mem period hPeriod couplings potential⟩
  simpa only [intrinsicAbelianMaxwellStrongMinimal_smooth_apply] using h

/-- The quotient preserves the original physical L² pairing on the full domain. -/
theorem intrinsicAbelianMaxwellReduced_pairing (potential : (J).domain) (test : Potential)
    (hDomain : (Exact).mkQ potential.val ∈ (intrinsicAbelianMaxwellReduced period hPeriod couplings).domain) :
    inner Real (intrinsicAbelianMaxwellReduced period hPeriod couplings ⟨(Exact).mkQ potential.val, hDomain⟩)
      ((Exact).mkQ test) = inner Real (J potential) test :=
  quotientPMap_pairing J Exact (intrinsicAbelianMaxwellStrongMinimal_symmetric period hPeriod couplings)
    (gauge_null period hPeriod couplings) potential test hDomain

/-- Quotienting these gauge directions cannot turn a nonzero Maxwell output into zero. -/
theorem intrinsicAbelianMaxwellReduced_zero_iff (potential : (J).domain)
    (hDomain : (Exact).mkQ potential.val ∈ (intrinsicAbelianMaxwellReduced period hPeriod couplings).domain) :
    intrinsicAbelianMaxwellReduced period hPeriod couplings ⟨(Exact).mkQ potential.val, hDomain⟩ = 0 ↔
      J potential = 0 :=
  quotientPMap_zero_iff J Exact (intrinsicAbelianMaxwellStrongMinimal_symmetric period hPeriod couplings)
    (gauge_null period hPeriod couplings) potential hDomain

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianMaxwellReduced4D
