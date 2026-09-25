import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicAbelianMaxwellStrongClosed4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicAbelianCurvatureExactComplex4D

/-! The completed exact gauge sector lies in the native closed Maxwell Jacobi kernel. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianMaxwellStrongGaugeKernel4D
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

/-- Exact smooth gauge potentials have zero native strong Maxwell Jacobi. -/
theorem intrinsicAbelianMaxwellStrongSmooth_exact (parameters : Parameters) :
    action (fun sector => exactGaugePotential period hPeriod (parameters sector)) = 0 := by
  apply (intrinsicAbelianPotentialL2Smooth_denseRange period hPeriod).eq_zero_of_inner_left (𝕜 := Real)
  intro test
  rw [intrinsicAbelianMaxwellStrongSmooth_smooth_pairing, intrinsicAbelianCurvatureL2_exact,
    map_zero, inner_zero_left]

/-- The kernel of the closed Jacobi as a closed physical L² subspace. -/
def intrinsicAbelianMaxwellStrongZeroL2 : Submodule Real Potential :=
  (J).graph.comap ((LinearMap.id : Potential →ₗ[Real] Potential).prod (0 : Potential →ₗ[Real] Potential))

theorem intrinsicAbelianMaxwellStrongZeroL2_isClosed :
    IsClosed (intrinsicAbelianMaxwellStrongZeroL2 period hPeriod couplings : Set Potential) :=
  (intrinsicAbelianMaxwellStrongMinimal_isClosed period hPeriod couplings).preimage
    (continuous_id.prodMk continuous_const)

/-- All completed exact gauge directions belong to the actual closed Jacobi domain and kernel. -/
theorem intrinsicAbelianExactPotentialL2_le_maxwellZero :
    intrinsicAbelianExactPotentialL2 period hPeriod ≤
      intrinsicAbelianMaxwellStrongZeroL2 period hPeriod couplings := by
  apply closure_minimal ?_ (intrinsicAbelianMaxwellStrongZeroL2_isClosed period hPeriod couplings)
  apply Submodule.span_le.mpr
  rintro _ ⟨parameters, rfl⟩
  change (inc (fun sector => exactGaugePotential period hPeriod (parameters sector)), 0) ∈ (J).graph
  rw [intrinsicAbelianMaxwellStrongMinimal_graph]
  have hRaw := ((inc).prod action).range.le_topologicalClosure
    ⟨(fun sector => exactGaugePotential period hPeriod (parameters sector)), rfl⟩
  change (inc (fun sector => exactGaugePotential period hPeriod (parameters sector)),
    action (fun sector => exactGaugePotential period hPeriod (parameters sector))) ∈
      linearFeatureGraphClosure inc action at hRaw
  rw [intrinsicAbelianMaxwellStrongSmooth_exact] at hRaw
  exact hRaw

theorem intrinsicAbelianExactPotentialL2_maxwell_graph
    (potential : intrinsicAbelianExactPotentialL2 period hPeriod) :
    (potential.val, 0) ∈ (J).graph :=
  intrinsicAbelianExactPotentialL2_le_maxwellZero period hPeriod couplings potential.property

/-- The full closed Jacobi output annihilates every completed exact gauge direction. -/
theorem intrinsicAbelianMaxwellStrongMinimal_exact_pairing
    (potential : (J).domain) (gauge : intrinsicAbelianExactPotentialL2 period hPeriod) :
    inner Real (J potential) gauge.val = 0 := by
  obtain ⟨vector, hInput, hOutput⟩ := (LinearPMap.mem_graph_iff _).mp
    (intrinsicAbelianExactPotentialL2_maxwell_graph period hPeriod couplings gauge)
  change vector.val = gauge.val at hInput
  change J vector = 0 at hOutput
  rw [← hInput, intrinsicAbelianMaxwellStrongMinimal_symmetric period hPeriod couplings,
    hOutput, inner_zero_right]

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianMaxwellStrongGaugeKernel4D
