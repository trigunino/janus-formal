import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicAbelianFullStrongSmooth4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ClosedFeatureCore4D

/-! Minimal closed native Maxwell–BRST Jacobi and its physical same-action pairing. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianFullStrongClosed4D
set_option autoImplicit false
noncomputable section
open P0EFTJanusProgramPT12DenseAdjointGraphClosable4D
open P0EFTJanusProgramPT12ClosedFeatureOperator4D

private theorem closedFeature_symmetric {D H : Type*} [AddCommGroup D] [Module Real D]
    [NormedAddCommGroup H] [InnerProductSpace Real H] (inclusion operator : D →ₗ[Real] H)
    (hSingle : Function.Injective (fun point : linearFeatureGraphClosure inclusion operator => point.val.1))
    (hSym : ∀ first second, inner Real (operator first) (inclusion second) =
      inner Real (inclusion first) (operator second)) :
    (closedFeatureOperator inclusion operator).IsFormalAdjoint (closedFeatureOperator inclusion operator) := by
  let J := closedFeatureOperator inclusion operator
  have hGraph := closedFeatureOperator_graph inclusion operator hSingle
  intro first second
  have hFirst : (first.val, J first) ∈ linearFeatureGraphClosure inclusion operator := by
    rw [← hGraph]
    exact J.mem_graph first
  have hSecond : (second.val, J second) ∈ linearFeatureGraphClosure inclusion operator := by
    rw [← hGraph]
    exact J.mem_graph second
  have hClosed : IsClosed {pair : H × H |
      inner Real (J first) pair.1 = inner Real first.val pair.2} :=
    isClosed_eq (by fun_prop) (by fun_prop)
  have hSubset : ((inclusion.prod operator).range : Set (H × H)) ⊆
      {pair | inner Real (J first) pair.1 = inner Real first.val pair.2} := by
    rintro _ ⟨field, rfl⟩
    exact linearFeatureGraphClosure_pairing inclusion operator operator hSym ⟨_, hFirst⟩ field
  exact closure_minimal hSubset hClosed hSecond

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
open P0EFTJanusProgramPT12DenseAdjointGraphClosable4D
open P0EFTJanusProgramPT12ClosedFeatureOperator4D
open P0EFTJanusProgramPT12ClosedFeatureCore4D
variable (couplings : GlobalCandidateAActionCouplings)
local notation "inc" => intrinsicAbelianFullL2Smooth period hPeriod
local notation "action" => intrinsicAbelianFullStrongSmooth period hPeriod couplings

private theorem graph_single :
    Function.Injective (fun point : linearFeatureGraphClosure inc action => point.val.1) :=
  linearFeatureGraphClosure_fst_injective inc action action
    (intrinsicAbelianFullL2Smooth_denseRange period hPeriod)
    (intrinsicAbelianFullStrongSmooth_symmetric period hPeriod couplings)

/-- The minimal closed realization of all native Maxwell–BRST columns. -/
def intrinsicAbelianFullStrongMinimal : Full →ₗ.[Real] Full :=
  closedFeatureOperator inc action

theorem intrinsicAbelianFullStrongMinimal_graph :
    (intrinsicAbelianFullStrongMinimal period hPeriod couplings).graph =
      linearFeatureGraphClosure inc action :=
  closedFeatureOperator_graph inc action (graph_single period hPeriod couplings)

theorem intrinsicAbelianFullStrongMinimal_isClosed :
    (intrinsicAbelianFullStrongMinimal period hPeriod couplings).IsClosed :=
  closedFeatureOperator_isClosed inc action (graph_single period hPeriod couplings)

theorem intrinsicAbelianFullStrongMinimal_smooth_mem (potential : State) :
    inc potential ∈ (intrinsicAbelianFullStrongMinimal period hPeriod couplings).domain :=
  closedFeatureOperator_smooth_mem inc action potential

theorem intrinsicAbelianFullStrongMinimal_smooth_apply (potential : State) :
    intrinsicAbelianFullStrongMinimal period hPeriod couplings
      ⟨inc potential, intrinsicAbelianFullStrongMinimal_smooth_mem period hPeriod couplings potential⟩ =
      action potential :=
  closedFeatureOperator_smooth_apply inc action (graph_single period hPeriod couplings) potential

theorem intrinsicAbelianFullStrongMinimal_dense_domain :
    Dense ((intrinsicAbelianFullStrongMinimal period hPeriod couplings).domain : Set Full) :=
  closedFeatureOperator_dense_domain inc action (intrinsicAbelianFullL2Smooth_denseRange period hPeriod)

theorem intrinsicAbelianFullStrongMinimal_hasCore :
    (intrinsicAbelianFullStrongMinimal period hPeriod couplings).HasCore (inc).range :=
  closedFeatureOperator_hasCore inc action (graph_single period hPeriod couplings)

theorem intrinsicAbelianFullStrongMinimal_le
    (extension : Full →ₗ.[Real] Full) (hClosed : extension.IsClosed)
    (hExtends : ∀ potential : State, (inc potential, action potential) ∈ extension.graph) :
    intrinsicAbelianFullStrongMinimal period hPeriod couplings ≤ extension :=
  closedFeatureOperator_minimal inc action (graph_single period hPeriod couplings) extension hClosed hExtends

/-- Symmetry persists under closure; this does not claim self-adjointness. -/
theorem intrinsicAbelianFullStrongMinimal_symmetric :
    (intrinsicAbelianFullStrongMinimal period hPeriod couplings).IsFormalAdjoint
      (intrinsicAbelianFullStrongMinimal period hPeriod couplings) :=
  closedFeature_symmetric inc action (graph_single period hPeriod couplings)
    (intrinsicAbelianFullStrongSmooth_symmetric period hPeriod couplings)

open P0EFTJanusProgramPT12IntrinsicBulkPairedAbelianHessian4D
open P0EFTJanusProgramPT12IntrinsicBulkHessian4D
open P0EFTJanusReciprocalBimetricPotential

/-- The complete native Abelian bulk Hessian, including both ghost columns, has this physical L² representative. -/
theorem intrinsicAbelianFullStrongSmooth_eq_bulkHessian
    (interactionScale : Real) (coefficients : PotentialCoefficients) (first second : State) :
    inner Real (action first) (inc second) =
    intrinsicBulkHessian period hPeriod couplings interactionScale coefficients
      (intrinsicBulkPairedAbelianInsertion period hPeriod couplings (intrinsicBulkSmoothPairedAbelianFields period hPeriod first))
      (intrinsicBulkPairedAbelianInsertion period hPeriod couplings (intrinsicBulkSmoothPairedAbelianFields period hPeriod second)) := by
  have hGraph : inner Real (intrinsicAbelianFullGraphRiesz period hPeriod couplings
      (intrinsicAbelianFullSmooth period hPeriod first)) (intrinsicAbelianFullSmooth period hPeriod second) =
      intrinsicAbelianFullGraphHessian period hPeriod couplings
        (intrinsicAbelianFullSmooth period hPeriod first) (intrinsicAbelianFullSmooth period hPeriod second) :=
    InnerProductSpace.continuousLinearMapOfBilin_apply _ _ _
  exact (intrinsicAbelianFullStrongSmooth_eq_graphHessian period hPeriod couplings first second).trans
    (hGraph.symm.trans (intrinsicAbelianFullGraphRiesz_eq_bulkHessian period hPeriod couplings
      interactionScale coefficients first second))

/-- Exact same-action pairing on the certified smooth core of the closed physical realization. -/
theorem intrinsicAbelianFullStrongMinimal_eq_bulkHessian
    (interactionScale : Real) (coefficients : PotentialCoefficients) (first second : State) :
    inner Real (intrinsicAbelianFullStrongMinimal period hPeriod couplings
      ⟨inc first, intrinsicAbelianFullStrongMinimal_smooth_mem period hPeriod couplings first⟩) (inc second) =
    intrinsicBulkHessian period hPeriod couplings interactionScale coefficients
      (intrinsicBulkPairedAbelianInsertion period hPeriod couplings (intrinsicBulkSmoothPairedAbelianFields period hPeriod first))
      (intrinsicBulkPairedAbelianInsertion period hPeriod couplings (intrinsicBulkSmoothPairedAbelianFields period hPeriod second)) :=
  (congrArg (fun value : Full => inner Real value (inc second))
    (intrinsicAbelianFullStrongMinimal_smooth_apply period hPeriod couplings first)).trans
      (intrinsicAbelianFullStrongSmooth_eq_bulkHessian period hPeriod couplings interactionScale coefficients first second)

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianFullStrongClosed4D
