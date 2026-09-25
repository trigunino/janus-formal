import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeDiffeomorphismFPSmoothAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeDeDonderCore4D
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothApproximation4D

/-! The native physical de Donder adjoint on smooth tests and multipliers. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeDeDonderSmoothAdjoint4D
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open P0EFTJanusProgramPGlobalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphPairing4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusProgramPT12FPCanonicalFormalAdjoint4D
open P0EFTJanusProgramPT12CanonicalFrameDerivativeAdjoint4D
open P0EFTJanusProgramPT12CanonicalFirstOrderColumn4D P0EFTJanusProgramPT12SmoothMatrixL24D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev Q := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (Q period hPeriod) := reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (Q period hPeriod) := reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (Q period hPeriod) := reflectedSphereQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (Q period hPeriod) := borel _
local instance : BorelSpace (Q period hPeriod) where measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
local notation "frame" => finiteSmoothTangentFrame period hPeriod
private abbrev FrameIndex := Fin (finiteSmoothTangentFrame period hPeriod).count
local notation "N" => FrameIndex period hPeriod
local notation "Ghost" => CInfinityDiffeomorphismGhost period hPeriod
local notation "Scalar" => SmoothQuotientField period hPeriod Real
local notation "H" => CanonicalPhysicalBulkL2 period hPeriod
local notation "Ambient" => GlobalDiffeomorphismVectorL2 period hPeriod
variable (metric : SmoothGeneralLorentzMetric period hPeriod)

open P0EFTJanusMappingTorusMetricCartanGlobalAction4D
open P0EFTJanusFiniteFrameDiffeomorphismC2Core4D
open P0EFTJanusFiniteFrameC2CartanFirstJet4D
open P0EFTJanusFiniteFrameKoszulCoefficients4D
open P0EFTJanusMappingTorusH1GraphTrace4D
local notation "Tensor" => SmoothSymmetricCovariantTwoTensor period hPeriod
local notation "h" => generalMetricFrameCoefficient period hPeriod frame
local notation "bracket" => finiteFrameStructureCoefficient period hPeriod frame metric
local notation "deriv" => canonicalFrameDerivativeSmooth period hPeriod frame
local notation "mul" => canonicalScalarMul period hPeriod

open P0EFTJanusProgramPT12FrameFreeGhostL2Core4D
open P0EFTJanusProgramPT12FrameFreeCartanScalar4D
open P0EFTJanusProgramPT12FrameFreeFrameDerivativeAdjoint4D
open P0EFTJanusProgramPT12FrameFreeDeDonderAdjoint4D
open P0EFTJanusProgramPT12FrameTensorL2Equiv4D
local notation "Core" => FrameFreeGhostL2 period hPeriod metric
local instance ghostGroup : NormedAddCommGroup Core := inferInstance
local instance : SeminormedAddCommGroup Core := (ghostGroup period hPeriod metric).toSeminormedAddCommGroup
local instance : NormedSpace Real Core := inferInstance
local instance : InnerProductSpace Real Core := Submodule.innerProductSpace (𝕜 := Real) _
local notation "q" => frameFreeGhostCoordinate period hPeriod metric
local notation "inc" => frameFreeGhostL2Smooth period hPeriod metric
local notation "incl" => smoothToCanonicalPhysicalBulkL2 period hPeriod

open P0EFTJanusProgramPT12FrameFreeCartanAdjoint4D
open P0EFTJanusProgramPT12FrameFreeDeDonderScalar4D
open P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphCore4D
open P0EFTJanusMappingTorusGlobalGeneralMetricDeDonder4D
open P0EFTJanusProgramPGlobalGeneralMetricDiffeomorphismFaddeevPopov4D
open P0EFTJanusFiniteFrameMetricContraction4D
local notation "g" => finiteFrameInverseMetricCoefficient period hPeriod frame metric metric
local notation "Γ" => finiteFrameKoszulChristoffelCoefficient period hPeriod frame metric metric
local notation "derivAdj" => frameFreeFrameDerivativeAdjoint period hPeriod metric frame
local notation "cartanAdj" => frameFreeCartanAdjointColumn period hPeriod metric metric.tensor

open P0EFTJanusProgramPT12FrameFreeDiffeomorphismFPAdjoint4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothApproximation4D
local instance ambientGroup : NormedAddCommGroup Ambient := inferInstance
local instance : SeminormedAddCommGroup Ambient := (ambientGroup period hPeriod).toSeminormedAddCommGroup
local instance : NormedSpace Real Ambient := inferInstance
local instance : InnerProductSpace Real Ambient := inferInstance
local notation "action" => frameFreeDiffeomorphismFPSmoothL2 period hPeriod metric
open P0EFTJanusProgramPT12FrameFreeDiffeomorphismFPSmoothAdjoint4D
open P0EFTJanusProgramPT12FrameFreeDeDonderClosed4D
local notation "TensorL2" => FrameTensorL2Completion period hPeriod frame
local instance tensorGroup : NormedAddCommGroup TensorL2 := inferInstance
local instance : SeminormedAddCommGroup TensorL2 := (tensorGroup period hPeriod).toSeminormedAddCommGroup
local instance : NormedSpace Real TensorL2 := inferInstance
local instance : InnerProductSpace Real TensorL2 := Submodule.innerProductSpace (𝕜 := Real) _
local notation "minimal" => frameFreeDeDonderMinimal period hPeriod metric

def frameFreeDeDonderSmoothAdjoint (tests : N → Scalar) : TensorL2 :=
  ∑ index, frameFreeDeDonderAdjointColumn period hPeriod metric index (tests index)

/-- Green's identity holds against the whole native minimal de Donder domain. -/
theorem frameFreeDeDonderSmoothAdjoint_pairing
    (input : (minimal).domain) (tests : N → Scalar) :
    inner Real (minimal input) (frameFreeDiffeomorphismFPSmoothTest period hPeriod tests) =
      inner Real input.val (frameFreeDeDonderSmoothAdjoint period hPeriod metric tests) := by
  have hGraph := (minimal).mem_graph input
  rw [frameFreeDeDonderMinimal_graph] at hGraph
  rw [PiLp.inner_apply]
  simp only [frameFreeDeDonderSmoothAdjoint, inner_sum]
  apply Finset.sum_congr rfl
  intro index _
  exact frameFreeDeDonderClosedGraph_pairing period hPeriod metric ⟨_, hGraph⟩ index (tests index)

private theorem reverse_pairing (tests : N → Scalar) (input : (minimal).domain) :
    inner Real (frameFreeDeDonderSmoothAdjoint period hPeriod metric tests) input.val =
      inner Real (frameFreeDiffeomorphismFPSmoothTest period hPeriod tests) (minimal input) :=
  (real_inner_comm _ _).trans
    ((frameFreeDeDonderSmoothAdjoint_pairing period hPeriod metric input tests).symm.trans (real_inner_comm _ _))

theorem frameFreeDeDonderSmoothTest_mem_adjoint (tests : N → Scalar) :
    frameFreeDiffeomorphismFPSmoothTest period hPeriod tests ∈ (minimal).adjoint.domain :=
  LinearPMap.mem_adjoint_domain_of_exists _
    ⟨frameFreeDeDonderSmoothAdjoint period hPeriod metric tests, reverse_pairing period hPeriod metric tests⟩

theorem frameFreeDeDonderAdjoint_smooth_apply (tests : N → Scalar) :
    (minimal).adjoint ⟨frameFreeDiffeomorphismFPSmoothTest period hPeriod tests,
      frameFreeDeDonderSmoothTest_mem_adjoint period hPeriod metric tests⟩ =
      frameFreeDeDonderSmoothAdjoint period hPeriod metric tests :=
  LinearPMap.adjoint_apply_eq (frameFreeDeDonderMinimal_dense_domain period hPeriod metric) _
    (reverse_pairing period hPeriod metric tests)

theorem frameFreeDeDonderAdjoint_dense_domain :
    Dense ((minimal).adjoint.domain : Set Ambient) :=
  (frameFreeDiffeomorphismFPSmoothTest_denseRange period hPeriod).mono
    (by rintro _ ⟨tests, rfl⟩; exact frameFreeDeDonderSmoothTest_mem_adjoint period hPeriod metric tests)

theorem frameFreeDeDonderAdjoint_isClosed : (minimal).adjoint.IsClosed :=
  LinearPMap.adjoint_isClosed (frameFreeDeDonderMinimal_dense_domain period hPeriod metric)

/-- The actual normalized multiplier coordinates are smooth adjoint tests. -/
theorem frameFreeDeDonderMultiplier_mem_adjoint (multiplier : Ghost) :
    (inc multiplier).val ∈ (minimal).adjoint.domain :=
  frameFreeDeDonderSmoothTest_mem_adjoint period hPeriod metric
    (globalNormalizedVectorCoordinate period hPeriod metric multiplier)

def frameFreeDeDonderMultiplierAdjoint : Ghost →ₗ[Real] TensorL2 :=
  (minimal).adjoint.toFun.comp
    ((globalNormalizedVectorFrameL2LinearMap period hPeriod metric).codRestrict
      (minimal).adjoint.domain (frameFreeDeDonderMultiplier_mem_adjoint period hPeriod metric))

theorem frameFreeDeDonderMultiplierAdjoint_apply (multiplier : Ghost) :
    frameFreeDeDonderMultiplierAdjoint period hPeriod metric multiplier =
      frameFreeDeDonderSmoothAdjoint period hPeriod metric
        (globalNormalizedVectorCoordinate period hPeriod metric multiplier) :=
  frameFreeDeDonderAdjoint_smooth_apply period hPeriod metric
    (globalNormalizedVectorCoordinate period hPeriod metric multiplier)

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeDeDonderSmoothAdjoint4D
