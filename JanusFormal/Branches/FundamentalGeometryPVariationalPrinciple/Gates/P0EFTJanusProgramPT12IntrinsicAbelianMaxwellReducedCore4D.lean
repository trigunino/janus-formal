import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicAbelianMaxwellReduced4D

/-! The projected native smooth potentials form a core of the exact-gauge quotient Jacobi. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianMaxwellReducedCore4D
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

open P0EFTJanusProgramPT12IntrinsicAbelianMaxwellReduced4D
local notation "Reduced" => IntrinsicAbelianMaxwellReducedL2 period hPeriod
local instance reducedGroup : NormedAddCommGroup Reduced := inferInstance
local instance : SeminormedAddCommGroup Reduced := (reducedGroup period hPeriod).toSeminormedAddCommGroup
local instance : NormedSpace Real Reduced := inferInstance
local instance : InnerProductSpace Real Reduced := inferInstance

open P0EFTJanusProgramPT12ClosedFeatureOperator4D
open P0EFTJanusProgramPT12ClosedFeatureCore4D
local notation "QJ" => intrinsicAbelianMaxwellReduced period hPeriod couplings
private abbrev reducedSmooth : Smooth →ₗ[Real] Reduced := (Exact).mkQ.comp inc
private abbrev reducedAction : Smooth →ₗ[Real] Reduced := (Exact).mkQ.comp action
local notation "qinc" => reducedSmooth period hPeriod
local notation "qaction" => reducedAction period hPeriod couplings

/-- The quotient graph is exactly the closure of the projected native smooth graph. -/
theorem intrinsicAbelianMaxwellReduced_graph :
    (QJ).graph = linearFeatureGraphClosure qinc qaction := by
  apply le_antisymm
  · intro pair hPair
    rw [intrinsicAbelianMaxwellReduced, quotientPMap_graph] at hPair
    change (quotientLift Exact pair.1, quotientLift Exact pair.2) ∈ (J).graph at hPair
    rw [intrinsicAbelianMaxwellStrongMinimal_graph] at hPair
    have hClosed : IsClosed {pair : Potential × Potential |
        ((Exact).mkQ pair.1, (Exact).mkQ pair.2) ∈ linearFeatureGraphClosure qinc qaction} :=
      ((qinc).prod qaction).range.isClosed_topologicalClosure.preimage
        (((Exact).mkQL.continuous.comp continuous_fst).prodMk
          ((Exact).mkQL.continuous.comp continuous_snd))
    have hSubset : (((inc).prod action).range : Set (Potential × Potential)) ⊆
        {pair | ((Exact).mkQ pair.1, (Exact).mkQ pair.2) ∈ linearFeatureGraphClosure qinc qaction} := by
      rintro _ ⟨potential, rfl⟩
      exact ((qinc).prod qaction).range.le_topologicalClosure ⟨potential, rfl⟩
    have hProjected := closure_minimal hSubset hClosed hPair
    change ((Exact).mkQ (quotientLift Exact pair.1), (Exact).mkQ (quotientLift Exact pair.2)) ∈
      linearFeatureGraphClosure qinc qaction at hProjected
    simpa only [mk_quotientLift] using hProjected
  · apply closure_minimal ?_ (intrinsicAbelianMaxwellReduced_isClosed period hPeriod couplings)
    rintro _ ⟨potential, rfl⟩
    exact intrinsicAbelianMaxwellReduced_smooth_graph period hPeriod couplings potential

theorem intrinsicAbelianMaxwellReduced_smooth_mem (potential : Smooth) :
    (Exact).mkQ (inc potential) ∈ (QJ).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (intrinsicAbelianMaxwellReduced_smooth_graph period hPeriod couplings potential)

theorem intrinsicAbelianMaxwellReduced_smooth_apply (potential : Smooth) :
    QJ ⟨(Exact).mkQ (inc potential), intrinsicAbelianMaxwellReduced_smooth_mem period hPeriod couplings potential⟩ =
      (Exact).mkQ (action potential) :=
  (QJ).mem_graph_snd_inj ((QJ).mem_graph _) (intrinsicAbelianMaxwellReduced_smooth_graph period hPeriod couplings potential) rfl

/-- No extra quotient-core assumption is needed. -/
theorem intrinsicAbelianMaxwellReduced_hasCore :
    (QJ).HasCore (qinc).range := by
  have hSingle := featureClosure_injective_of_closed_extension qinc qaction QJ
    (intrinsicAbelianMaxwellReduced_isClosed period hPeriod couplings)
    (intrinsicAbelianMaxwellReduced_smooth_graph period hPeriod couplings)
  apply (smoothRange_hasCore_iff qinc qaction hSingle QJ
    (intrinsicAbelianMaxwellReduced_isClosed period hPeriod couplings)
    (intrinsicAbelianMaxwellReduced_smooth_mem period hPeriod couplings)
    (intrinsicAbelianMaxwellReduced_smooth_apply period hPeriod couplings)).mpr
  apply LinearPMap.eq_of_eq_graph
  exact (closedFeatureOperator_graph qinc qaction hSingle).trans
    (intrinsicAbelianMaxwellReduced_graph period hPeriod couplings).symm

/-- The native Maxwell Hessian is preserved after the physical gauge quotient. -/
theorem intrinsicAbelianMaxwellReduced_smooth_pairing (first second : Smooth) :
    inner Real (QJ ⟨(Exact).mkQ (inc first), intrinsicAbelianMaxwellReduced_smooth_mem period hPeriod couplings first⟩)
      ((Exact).mkQ (inc second)) =
      intrinsicAbelianMaxwellGraphHessian period hPeriod couplings
        (intrinsicAbelianMaxwellLorenzSmooth period hPeriod first)
        (intrinsicAbelianMaxwellLorenzSmooth period hPeriod second) := by
  exact (intrinsicAbelianMaxwellReduced_pairing period hPeriod couplings
    ⟨_, intrinsicAbelianMaxwellStrongMinimal_smooth_mem period hPeriod couplings first⟩ (inc second)
    (intrinsicAbelianMaxwellReduced_smooth_mem period hPeriod couplings first)).trans
      ((congrArg (fun value : Potential => inner Real value (inc second))
        (intrinsicAbelianMaxwellStrongMinimal_smooth_apply period hPeriod couplings first)).trans
          (intrinsicAbelianMaxwellStrongSmooth_eq_graphHessian period hPeriod couplings first second))

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianMaxwellReducedCore4D
