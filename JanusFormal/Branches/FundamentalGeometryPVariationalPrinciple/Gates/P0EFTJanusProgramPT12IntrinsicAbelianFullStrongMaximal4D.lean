import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicAbelianFullGraphPhysicalFaithful4D

/-! Maximal weak physical realization of the native Maxwell-BRST Jacobi. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianFullStrongMaximal4D
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
open P0EFTJanusProgramPT12CanonicalFrameDerivativeAdjoint4D
open P0EFTJanusFiniteFrameMetricContraction4D
open P0EFTJanusMappingTorusGlobalGeneralMetricAbelianLorenzCodifferential4D
open P0EFTJanusProgramPT12IntrinsicAbelianLorenzSmoothAdjoint4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
local notation "GaugeSmooth" => GlobalPairedGaugeLieSmooth period hPeriod
local notation "GaugeL2" => GlobalPairedGaugeLieL2 period hPeriod
local instance : NormedSpace Real GaugeL2 := inferInstance

open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupL2Residual4D
local notation "State" => GlobalPairedAbelianBRSTState period hPeriod
local instance gaugeGroup : NormedAddCommGroup GaugeL2 := inferInstance
local instance : SeminormedAddCommGroup GaugeL2 := (gaugeGroup period hPeriod).toSeminormedAddCommGroup
local instance : InnerProductSpace Real GaugeL2 := inferInstance

open P0EFTJanusProgramPT12IntrinsicAbelianFullL2Core4D
open P0EFTJanusProgramPT12IntrinsicAbelianLorenzAdjoint4D
open P0EFTJanusProgramPT12IntrinsicAbelianMaxwellStrongSmooth4D
open P0EFTJanusProgramPT12IntrinsicAbelianMaxwellGraphRiesz4D
open P0EFTJanusProgramPT12IntrinsicAbelianFullGraph4D
open P0EFTJanusProgramPT12IntrinsicAbelianFullGraphRiesz4D
open P0EFTJanusProgramPT12PairedFPCanonicalAdjoint4D
open P0EFTJanusProgramPT12FrameFreeFPCanonicalPairing4D
open P0EFTJanusProgramPGlobalCovariantAction4D
local notation "Full" => IntrinsicAbelianFullL2 period hPeriod
local instance fullGroup : NormedAddCommGroup Full := inferInstance
local instance : SeminormedAddCommGroup Full := (fullGroup period hPeriod).toSeminormedAddCommGroup
local instance : NormedSpace Real Full := inferInstance
local instance : InnerProductSpace Real Full := inferInstance
local notation "Maxwell" => IntrinsicAbelianMaxwellLorenzGraph period hPeriod
local instance maxwellGroup : NormedAddCommGroup Maxwell := inferInstance
local instance : SeminormedAddCommGroup Maxwell := (maxwellGroup period hPeriod).toSeminormedAddCommGroup
local instance : InnerProductSpace Real Maxwell := graphInnerProductSpace period hPeriod
local instance : NormedSpace Real Maxwell := inferInstance
local notation "FullGraph" => IntrinsicAbelianFullGraph period hPeriod
local instance graphGroup : NormedAddCommGroup FullGraph := inferInstance
local instance : SeminormedAddCommGroup FullGraph := (graphGroup period hPeriod).toSeminormedAddCommGroup
local instance : InnerProductSpace Real FullGraph := intrinsicAbelianFullGraphInnerProductSpace period hPeriod
local instance : CompleteSpace FullGraph := intrinsicAbelianFullGraph_complete period hPeriod
local instance : NormedSpace Real FullGraph := (intrinsicAbelianFullGraphInnerProductSpace period hPeriod).toNormedSpace

open P0EFTJanusProgramPT12IntrinsicAbelianFullStrongSmooth4D
open P0EFTJanusProgramPT12IntrinsicAbelianFullStrongClosed4D
open P0EFTJanusProgramPT12IntrinsicAbelianCurvatureGraphBridge4D
local notation "BRST" => GlobalPairedAbelianOffShellGraphHilbert period hPeriod (fun _ => base)
local instance brstGroup : NormedAddCommGroup BRST := inferInstance
local instance : SeminormedAddCommGroup BRST := (brstGroup period hPeriod).toSeminormedAddCommGroup
local instance : NormedSpace Real BRST := inferInstance

open P0EFTJanusProgramPT12IntrinsicAbelianFullStrongGraphBridge4D
open P0EFTJanusProgramPT12IntrinsicAbelianFullGraphFaithful4D

open P0EFTJanusProgramPT12DenseAdjointGraphClosable4D

private theorem adjoint_graph_iff_of_smooth_closure {D E : Type*}
    [AddCommGroup D] [Module Real D] [NormedAddCommGroup E]
    [InnerProductSpace Real E] [CompleteSpace E]
    (inclusion action : D →ₗ[Real] E) (operator : E →ₗ.[Real] E)
    (hDense : Dense (operator.domain : Set E))
    (hGraph : operator.graph = linearFeatureGraphClosure inclusion action) (field value : E) :
    (field, value) ∈ operator.adjoint.graph ↔
      ∀ test : D, inner Real (action test) field = inner Real (inclusion test) value := by
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint hDense, hGraph, Submodule.mem_adjoint_iff]
  constructor
  · intro h test
    exact sub_eq_zero.mp (h (inclusion test) (action test)
      ((inclusion.prod action).range.le_topologicalClosure ⟨test, rfl⟩))
  · intro h first second hPair
    apply sub_eq_zero.mpr
    have hClosed : IsClosed {pair : E × E | inner Real pair.2 field = inner Real pair.1 value} := by
      apply isClosed_eq <;> fun_prop
    exact closure_minimal (by rintro _ ⟨test, rfl⟩; exact h test) hClosed hPair

variable (couplings : GlobalCandidateAActionCouplings)
local notation "inc" => intrinsicAbelianFullL2Smooth period hPeriod
local notation "action" => intrinsicAbelianFullStrongSmooth period hPeriod couplings
local notation "minimal" => intrinsicAbelianFullStrongMinimal period hPeriod couplings

/-- The maximal weak Jacobi is the adjoint of the concrete minimal realization. -/
def intrinsicAbelianFullStrongMaximal : Full →ₗ.[Real] Full := (minimal).adjoint

theorem intrinsicAbelianFullStrongMaximal_isClosed :
    (intrinsicAbelianFullStrongMaximal period hPeriod couplings).IsClosed :=
  LinearPMap.adjoint_isClosed (intrinsicAbelianFullStrongMinimal_dense_domain period hPeriod couplings)

/-- Smooth native tests characterize the entire maximal physical graph. -/
theorem intrinsicAbelianFullStrongMaximal_graph_iff (field value : Full) :
    (field, value) ∈ (intrinsicAbelianFullStrongMaximal period hPeriod couplings).graph ↔
      ∀ test : State, inner Real (action test) field = inner Real (inc test) value :=
  adjoint_graph_iff_of_smooth_closure inc action minimal
    (intrinsicAbelianFullStrongMinimal_dense_domain period hPeriod couplings)
    (intrinsicAbelianFullStrongMinimal_graph period hPeriod couplings) field value

theorem intrinsicAbelianFullStrongMinimal_le_maximal :
    minimal ≤ intrinsicAbelianFullStrongMaximal period hPeriod couplings :=
  (intrinsicAbelianFullStrongMinimal_symmetric period hPeriod couplings).le_adjoint
    (intrinsicAbelianFullStrongMinimal_dense_domain period hPeriod couplings)

theorem intrinsicAbelianFullStrongMaximal_dense_domain :
    Dense ((intrinsicAbelianFullStrongMaximal period hPeriod couplings).domain : Set Full) :=
  (intrinsicAbelianFullStrongMinimal_dense_domain period hPeriod couplings).mono
    (intrinsicAbelianFullStrongMinimal_le_maximal period hPeriod couplings).1

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianFullStrongMaximal4D
