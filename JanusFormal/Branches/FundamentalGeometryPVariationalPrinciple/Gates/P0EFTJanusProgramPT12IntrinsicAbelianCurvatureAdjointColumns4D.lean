import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicAbelianCurvatureClosed4D

/-! Concrete L² adjoint columns of the native closed curvature operator. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianCurvatureAdjointColumns4D
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

def intrinsicAbelianPotentialCoordinate (index : GlobalPairedAbelianPotentialCoordinateIndex period hPeriod) :
    Potential →L[Real] H :=
  (PiLp.proj 2 (fun _ : GlobalPairedAbelianPotentialCoordinateIndex period hPeriod => H) index).comp
    (intrinsicAbelianPotentialL2Submodule period hPeriod).subtypeL

def intrinsicAbelianCurvatureCoordinate (index : Index) : Curvature →L[Real] H :=
  PiLp.proj 2 (fun _ : Index => H) index

def intrinsicAbelianCurvatureTest (index : Index) (test : Scalar) : Curvature :=
  (intrinsicAbelianCurvatureCoordinate period hPeriod index).adjoint
    (smoothToCanonicalPhysicalBulkL2 period hPeriod test)

/-- The physical potential representative of a single curvature test's formal adjoint. -/
def intrinsicAbelianCurvatureAdjointColumn (index : Index) (test : Scalar) : Potential :=
  (intrinsicAbelianPotentialCoordinate period hPeriod (index.1, index.2.1, index.2.2.2)).adjoint
    (smoothToCanonicalPhysicalBulkL2 period hPeriod
      (frameFreeFrameDerivativeAdjoint period hPeriod base frame index.2.2.1 test)) -
  (intrinsicAbelianPotentialCoordinate period hPeriod (index.1, index.2.1, index.2.2.1)).adjoint
    (smoothToCanonicalPhysicalBulkL2 period hPeriod
      (frameFreeFrameDerivativeAdjoint period hPeriod base frame index.2.2.2 test)) -
  ∑ upper : Fin (finiteSmoothTangentFrame period hPeriod).count,
    (intrinsicAbelianPotentialCoordinate period hPeriod (index.1, index.2.1, upper)).adjoint
      (smoothToCanonicalPhysicalBulkL2 period hPeriod
        (canonicalScalarMul period hPeriod
          (finiteFrameStructureCoefficient period hPeriod frame base index.2.2.1 index.2.2.2 upper) test))

theorem intrinsicAbelianCurvatureAdjointColumn_pairing
    (input : (intrinsicAbelianCurvatureMinimal period hPeriod).domain) (index : Index) (test : Scalar) :
    inner Real (intrinsicAbelianCurvatureMinimal period hPeriod input)
      (intrinsicAbelianCurvatureTest period hPeriod index test) =
    inner Real input.val (intrinsicAbelianCurvatureAdjointColumn period hPeriod index test) := by
  have hGraph := (intrinsicAbelianCurvatureMinimal period hPeriod).mem_graph input
  rw [intrinsicAbelianCurvatureMinimal_graph] at hGraph
  simp only [intrinsicAbelianCurvatureTest, intrinsicAbelianCurvatureAdjointColumn,
    inner_sub_right, inner_sum, ContinuousLinearMap.adjoint_inner_right]
  exact intrinsicAbelianCurvatureL2Graph_pairing period hPeriod ⟨_, hGraph⟩
    index.1 index.2.1 index.2.2.1 index.2.2.2 test

private theorem reverse_pairing
    (index : Index) (test : Scalar) (input : (intrinsicAbelianCurvatureMinimal period hPeriod).domain) :
    inner Real (intrinsicAbelianCurvatureAdjointColumn period hPeriod index test) input.val =
    inner Real (intrinsicAbelianCurvatureTest period hPeriod index test)
      (intrinsicAbelianCurvatureMinimal period hPeriod input) :=
  (real_inner_comm _ _).trans
    ((intrinsicAbelianCurvatureAdjointColumn_pairing period hPeriod input index test).symm.trans
      (real_inner_comm _ _))

theorem intrinsicAbelianCurvatureTest_mem_adjoint (index : Index) (test : Scalar) :
    intrinsicAbelianCurvatureTest period hPeriod index test ∈
      (intrinsicAbelianCurvatureMinimal period hPeriod).adjoint.domain :=
  LinearPMap.mem_adjoint_domain_of_exists _
    ⟨intrinsicAbelianCurvatureAdjointColumn period hPeriod index test, reverse_pairing period hPeriod index test⟩

theorem intrinsicAbelianCurvatureAdjoint_test_apply (index : Index) (test : Scalar) :
    (intrinsicAbelianCurvatureMinimal period hPeriod).adjoint
      ⟨intrinsicAbelianCurvatureTest period hPeriod index test,
        intrinsicAbelianCurvatureTest_mem_adjoint period hPeriod index test⟩ =
      intrinsicAbelianCurvatureAdjointColumn period hPeriod index test :=
  LinearPMap.adjoint_apply_eq (intrinsicAbelianCurvatureMinimal_dense_domain period hPeriod) _
    (reverse_pairing period hPeriod index test)

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicAbelianCurvatureAdjointColumns4D
