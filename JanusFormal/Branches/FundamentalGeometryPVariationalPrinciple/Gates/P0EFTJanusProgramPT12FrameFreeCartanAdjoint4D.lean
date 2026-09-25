import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeCartanScalar4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeDeDonderAdjoint4D

/-! Cartan formal adjoint in the original physical normalized ghost completion. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeCartanAdjoint4D
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

/-- The recovered coefficient adjoints land in the faithful ghost completion. -/
def frameFreeCartanAdjointColumn (tensor : Tensor) (first second : N) (test : Scalar) : Core :=
  ∑ direction : N, (q direction).adjoint (incl
    (frameFreeFirstOrderColumnAdjoint period hPeriod metric frame first second
      (frameFreeCartanZeroth period hPeriod metric tensor direction first second)
      (h tensor direction second) (h tensor first direction) test))

theorem frameFreeCartanAdjointColumn_pairing (tensor : Tensor) (ghost : Ghost)
    (first second : N) (test : Scalar) :
    inner Real (incl (h (smoothMetricCartanAction period hPeriod ghost tensor) first second)) (incl test) =
      inner Real (inc ghost) (frameFreeCartanAdjointColumn period hPeriod metric tensor first second test) := by
  rw [frameFreeCartan_scalar_expression period hPeriod metric]
  simp only [map_sum, sum_inner, frameFreeCartanAdjointColumn, inner_sum,
    ContinuousLinearMap.adjoint_inner_right, frameFreeGhostCoordinate_smooth]
  apply Finset.sum_congr rfl
  intro direction _
  exact frameFreeFirstOrderColumn_pairing period hPeriod metric frame first second _ _ _ _ _

/-- The original infinitesimal metric action, read in physical tensor L². -/
def frameFreeCartanSmoothL2 (tensor : Tensor) : Ghost →ₗ[Real] FrameTensorL2Completion period hPeriod frame :=
  (frameTensorL2Smooth period hPeriod frame).comp ((smoothMetricCartanActionBilinear period hPeriod).flip tensor)

theorem frameFreeCartanSmoothL2_coordinate (tensor : Tensor) (ghost : Ghost) (first second : N) :
    frameFreeTensorCoordinate period hPeriod first second (frameFreeCartanSmoothL2 period hPeriod tensor ghost) =
      incl (h (smoothMetricCartanAction period hPeriod ghost tensor) first second) := rfl

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeCartanAdjoint4D
