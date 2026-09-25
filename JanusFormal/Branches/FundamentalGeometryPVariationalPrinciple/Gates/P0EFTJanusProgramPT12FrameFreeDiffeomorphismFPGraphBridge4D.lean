import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeDiffeomorphismFPClosed4D

/-! The actual off-shell completed ghost/FP slots lie in the native physical minimal graph. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeDiffeomorphismFPGraphBridge4D
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
open P0EFTJanusProgramPT12FrameFreeDiffeomorphismFPClosed4D
local notation "BRST" => GlobalDiffeomorphismOffShellGraphHilbert period hPeriod metric
local instance brstGroup : NormedAddCommGroup BRST := inferInstance
local instance : SeminormedAddCommGroup BRST := (brstGroup period hPeriod metric).toSeminormedAddCommGroup
local instance : NormedSpace Real BRST :=
  globalDiffeomorphismOffShellGraphNormedSpace period hPeriod metric
local notation "ghost" => globalDiffeomorphismOffShellGhostProjection period hPeriod metric
local notation "fp" => globalDiffeomorphismOffShellFPProjection period hPeriod metric
local notation "minimal" => frameFreeDiffeomorphismFPMinimal period hPeriod metric

private theorem ghost_mem (point : BRST) : ghost point ∈ frameFreeGhostL2Space period hPeriod metric := by
  have hClosed : IsClosed {point : BRST | ghost point ∈ frameFreeGhostL2Space period hPeriod metric} :=
    (globalNormalizedVectorFrameL2LinearMap period hPeriod metric).range.isClosed_topologicalClosure.preimage
      (ghost).continuous
  apply closure_minimal (s := Set.range (globalDiffeomorphismOffShellSmoothEmbedding period hPeriod metric)) ?_ hClosed
    (by rw [(globalDiffeomorphismOffShellSmoothEmbedding_denseRange period hPeriod metric).closure_range]; trivial)
  rintro _ ⟨state, rfl⟩
  exact (globalNormalizedVectorFrameL2LinearMap period hPeriod metric).range.le_topologicalClosure
    ⟨state.nonminimal.ghost.field, rfl⟩

def frameFreeOffShellGhostReadout : BRST →L[Real] Core :=
  (ghost).codRestrict (frameFreeGhostL2Space period hPeriod metric) (ghost_mem period hPeriod metric)

theorem frameFreeOffShellGhostReadout_smooth (state : GlobalDiffeomorphismBRSTState period hPeriod) :
    frameFreeOffShellGhostReadout period hPeriod metric
      (globalDiffeomorphismOffShellSmoothEmbedding period hPeriod metric state) = inc state.nonminimal.ghost.field := rfl

/-- Every completed native FP feature is the value of the physical closed operator. -/
theorem frameFreeOffShellGhostReadout_fp_graph (point : BRST) :
    (frameFreeOffShellGhostReadout period hPeriod metric point, fp point) ∈ (minimal).graph := by
  let pair := (frameFreeOffShellGhostReadout period hPeriod metric).prod fp
  have hClosed : IsClosed {point : BRST | pair point ∈ (minimal).graph} :=
    (frameFreeDiffeomorphismFPMinimal_isClosed period hPeriod metric).preimage pair.continuous
  apply closure_minimal (s := Set.range (globalDiffeomorphismOffShellSmoothEmbedding period hPeriod metric)) ?_ hClosed
    (by rw [(globalDiffeomorphismOffShellSmoothEmbedding_denseRange period hPeriod metric).closure_range]; trivial)
  rintro _ ⟨state, rfl⟩
  change (inc state.nonminimal.ghost.field, action state.nonminimal.ghost.field) ∈ (minimal).graph
  rw [frameFreeDiffeomorphismFPMinimal_graph]
  exact ((inc).prod action).range.le_topologicalClosure ⟨state.nonminimal.ghost.field, rfl⟩

/-- The original BRST completion adds no FP mode over a fixed physical ghost. -/
theorem frameFreeOffShellFP_eq_of_ghost_eq (first second : BRST) (hGhost : ghost first = ghost second) :
    fp first = fp second := by
  have hFirst := frameFreeOffShellGhostReadout_fp_graph period hPeriod metric first
  have hSecond := frameFreeOffShellGhostReadout_fp_graph period hPeriod metric second
  rw [frameFreeDiffeomorphismFPMinimal_graph] at hFirst hSecond
  exact congrArg (fun point => point.val.2)
    (frameFreeDiffeomorphismFPClosedGraph_fst_injective period hPeriod metric
      (a₁ := ⟨_, hFirst⟩) (a₂ := ⟨_, hSecond⟩) (Subtype.ext hGhost))

/-- The physical adjoint column tests all completed original BRST vectors. -/
theorem frameFreeOffShellFP_weak_pairing (point : BRST) (index : N) (test : Scalar) :
    inner Real (fp point index) (incl test) =
      inner Real (frameFreeOffShellGhostReadout period hPeriod metric point)
        (frameFreeDiffeomorphismFPAdjointColumn period hPeriod metric index test) := by
  have hGraph := frameFreeOffShellGhostReadout_fp_graph period hPeriod metric point
  rw [frameFreeDiffeomorphismFPMinimal_graph] at hGraph
  exact frameFreeDiffeomorphismFPClosedGraph_pairing period hPeriod metric ⟨_, hGraph⟩ index test

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeDiffeomorphismFPGraphBridge4D
