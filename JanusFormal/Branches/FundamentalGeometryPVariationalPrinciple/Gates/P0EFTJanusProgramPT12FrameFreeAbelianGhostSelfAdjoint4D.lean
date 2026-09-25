import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeFPMinimalAdjunction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeFPH1Domain4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12OffDiagonalSelfAdjoint4D

/-! A self-adjoint ghost block on the genuine canonical L² space, using the
minimal FP and its full Hilbert adjoint. Smooth and H¹ graph agreement is exact;
no equality of minimal and maximal domains or Fredholm property is asserted. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeAbelianGhostSelfAdjoint4D
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped Manifold ContDiff ENNReal LinearPMap
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalAbelianLorenzGraphRiesz4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPT12PairedFPCanonicalAdjoint4D
open P0EFTJanusProgramPT12FrameFreeFPClosed4D
open P0EFTJanusProgramPT12FrameFreeFPFormalAdjointCore4D
open P0EFTJanusProgramPT12IntrinsicFPSymmetry4D
open P0EFTJanusProgramPT12FrameFreeFPMinimalAdjunction4D
open P0EFTJanusProgramPT12CanonicalDirectionalH1L24D
open P0EFTJanusProgramPT12PairedFPH1Correction4D
open P0EFTJanusProgramPT12FrameFreeFPH1Domain4D
open P0EFTJanusProgramPT12OffDiagonalClosedOperator4D
open P0EFTJanusProgramPT12OffDiagonalSelfAdjoint4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev Q := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (Q period hPeriod) := reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (Q period hPeriod) := reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (Q period hPeriod) := reflectedSphereQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (Q period hPeriod) := borel _
local instance : BorelSpace (Q period hPeriod) where measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
local instance : NormedSpace Real (CanonicalTenFlowScalarH1 period hPeriod) :=
  Submodule.normedSpace (𝕜 := Real) _
local instance : NormedSpace Real (PairedFPH1 period hPeriod) :=
  PiLp.normedSpace (𝕜 := Real) (p := (2 : ENNReal))
    (β := fun _ : GlobalPairedAbelianLorenzCoordinateIndex => CanonicalTenFlowScalarH1 period hPeriod)

variable (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
local notation "H" => GlobalPairedGaugeLieL2 period hPeriod
local notation "FP" => frameFreeFPCanonicalMinimal period hPeriod metric

theorem frameFreeFPCanonicalAdjoint_dense_domain : Dense ((FP).adjoint.domain : Set H) :=
  (frameFreeFPFormalAdjointMinimal_dense_domain period hPeriod metric).mono
    (frameFreeFPFormalAdjointMinimal_le_adjoint period hPeriod metric).1

def frameFreeAbelianGhostOperator : WithLp 2 (H × H) →ₗ.[Real] WithLp 2 (H × H) :=
  offDiagonalOperator FP (FP).adjoint

theorem frameFreeAbelianGhostOperator_domain_iff
    (input : WithLp 2 (GlobalPairedGaugeLieL2 period hPeriod × GlobalPairedGaugeLieL2 period hPeriod)) :
    input ∈ (frameFreeAbelianGhostOperator period hPeriod metric).domain ↔
      input.fst ∈ (FP).adjoint.domain ∧ input.snd ∈ (FP).domain :=
  offDiagonalOperator_domain_iff FP (FP).adjoint input

theorem frameFreeAbelianGhostOperator_selfAdjoint :
    IsSelfAdjoint (frameFreeAbelianGhostOperator period hPeriod metric) :=
  offDiagonalOperator_selfAdjoint FP
    (frameFreeFPCanonicalMinimal_isClosed period hPeriod metric)
    (frameFreeFPCanonicalMinimal_dense_domain period hPeriod metric)
    (frameFreeFPCanonicalAdjoint_dense_domain period hPeriod metric)

theorem frameFreeAbelianGhostOperator_isClosed :
    (frameFreeAbelianGhostOperator period hPeriod metric).IsClosed :=
  (frameFreeAbelianGhostOperator_selfAdjoint period hPeriod metric).isClosed

theorem frameFreeAbelianGhostOperator_dense_domain :
    Dense ((frameFreeAbelianGhostOperator period hPeriod metric).domain : Set (WithLp 2 (H × H))) :=
  (frameFreeAbelianGhostOperator_selfAdjoint period hPeriod metric).dense_domain

theorem frameFreeAbelianGhostOperator_smooth_graph
    (antighost ghost : GlobalPairedGaugeLieSmooth period hPeriod) :
    (WithLp.toLp 2 (globalPairedGaugeLieL2LinearMap period hPeriod antighost,
        globalPairedGaugeLieL2LinearMap period hPeriod ghost),
      WithLp.toLp 2 (globalPairedAbelianFPL2LinearMap period hPeriod metric ghost,
        pairedFPCanonicalAdjointL2 period hPeriod metric antighost)) ∈
      (frameFreeAbelianGhostOperator period hPeriod metric).graph := by
  apply (offDiagonalOperator_mem_graph_iff FP (FP).adjoint _ _).mpr
  constructor
  · exact ((FP).mem_graph_iff).mpr
      ⟨⟨_, frameFreeFPCanonicalMinimal_smooth_mem period hPeriod metric ghost⟩, rfl,
        frameFreeFPCanonicalMinimal_smooth_apply period hPeriod metric ghost⟩
  · apply LinearPMap.le_graph_of_le (frameFreeFPFormalAdjointMinimal_le_adjoint period hPeriod metric)
    exact ((frameFreeFPFormalAdjointMinimal period hPeriod metric).mem_graph_iff).mpr
      ⟨⟨_, frameFreeFPFormalAdjointMinimal_smooth_mem period hPeriod metric antighost⟩, rfl,
        frameFreeFPFormalAdjointMinimal_smooth_apply period hPeriod metric antighost⟩

theorem frameFreeAbelianGhostOperator_H1_graph
    (antighost ghost : PairedFPH1 period hPeriod)
    (adjointOutput fpOutput : GlobalPairedGaugeLieL2 period hPeriod)
    (hAntighost : (antighost, adjointOutput) ∈
      (frameFreeFPFormalAdjointH1Minimal period hPeriod metric).graph)
    (hGhost : (ghost, fpOutput) ∈ (frameFreeFPH1Minimal period hPeriod metric).graph) :
    (WithLp.toLp 2 (pairedH1ToL2 period hPeriod antighost, pairedH1ToL2 period hPeriod ghost),
      WithLp.toLp 2 (fpOutput, adjointOutput)) ∈
      (frameFreeAbelianGhostOperator period hPeriod metric).graph :=
  (offDiagonalOperator_mem_graph_iff FP (FP).adjoint _ _).mpr
    ⟨frameFreeFPH1Minimal_forget_graph period hPeriod metric ghost fpOutput hGhost,
      LinearPMap.le_graph_of_le (frameFreeFPFormalAdjointMinimal_le_adjoint period hPeriod metric)
        (frameFreeFPFormalAdjointH1Minimal_forget_graph period hPeriod metric
          antighost adjointOutput hAntighost)⟩

theorem intrinsicAbelianGhostOperator_smooth_graph
    (antighost ghost : GlobalPairedGaugeLieSmooth period hPeriod) :
    (WithLp.toLp 2 (globalPairedGaugeLieL2LinearMap period hPeriod antighost,
        globalPairedGaugeLieL2LinearMap period hPeriod ghost),
      WithLp.toLp 2 (globalPairedAbelianFPL2LinearMap period hPeriod
          (fun _ => intrinsicSmoothGeneralLorentzMetric period hPeriod) ghost,
        globalPairedAbelianFPL2LinearMap period hPeriod
          (fun _ => intrinsicSmoothGeneralLorentzMetric period hPeriod) antighost)) ∈
      (frameFreeAbelianGhostOperator period hPeriod
        (fun _ => intrinsicSmoothGeneralLorentzMetric period hPeriod)).graph := by
  have h := frameFreeAbelianGhostOperator_smooth_graph period hPeriod
    (fun _ => intrinsicSmoothGeneralLorentzMetric period hPeriod) antighost ghost
  rw [intrinsicPairedFPFormalAdjointL2_eq] at h
  exact h

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeAbelianGhostSelfAdjoint4D
