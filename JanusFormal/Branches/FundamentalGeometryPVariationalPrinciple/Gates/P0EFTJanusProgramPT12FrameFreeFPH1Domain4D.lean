import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreePairedFPH1Correction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeScalarH1Injective4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeFPFormalAdjointCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12PairedFPH1Correction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12SobolevFeatureGraph4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CandidateAFPFormalAdjointCore4D

/-! Actual FP and formal-adjoint minimal closures with H¹ source: common domain.
These closures are contained in the existing L² graphs; no maximal-domain equality is claimed. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeFPH1Domain4D
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped Manifold ContDiff ENNReal
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusProgramPGlobalFieldSpace4D P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPT12PairedFPCanonicalAdjoint4D
open P0EFTJanusProgramPT12CandidateAAbelianFaithfulRealization4D
open P0EFTJanusProgramPT12CandidateAFPCanonicalClosed4D
open P0EFTJanusProgramPT12CandidateAFPFormalAdjointCore4D
open P0EFTJanusProgramPT12PairedFPH1Correction4D
open P0EFTJanusProgramPT12SobolevFeatureGraph4D
open P0EFTJanusProgramPT12CanonicalDirectionalH1L24D

open P0EFTJanusProgramPT12FrameFreePairedFPH1Correction4D
open P0EFTJanusProgramPT12FrameFreeScalarH1Injective4D
open P0EFTJanusProgramPT12FrameFreeFPClosed4D
open P0EFTJanusProgramPT12FrameFreeFPFormalAdjointCore4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance : BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
local instance : NormedSpace Real (CanonicalTenFlowScalarH1 period hPeriod) :=
  Submodule.normedSpace (𝕜 := Real) _
local instance : NormedSpace Real (PairedFPH1 period hPeriod) :=
  PiLp.normedSpace (𝕜 := Real) (p := (2 : ENNReal))
    (β := fun _ : P0EFTJanusProgramPGlobalAbelianLorenzGraphRiesz4D.GlobalPairedAbelianLorenzCoordinateIndex =>
      CanonicalTenFlowScalarH1 period hPeriod)

variable (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)

def frameFreeFPH1Correction : PairedFPH1 period hPeriod →L[Real] GlobalPairedGaugeLieL2 period hPeriod :=
  frameFreePairedFPVolumeCorrection period hPeriod metric


theorem frameFreeFPH1ToL2_injective : Function.Injective (pairedH1ToL2 period hPeriod) := by
  intro first second hEqual
  apply PiLp.ext
  intro index
  exact frameFreeCanonicalScalarH1ToL2_injective period hPeriod _
    (congrArg (fun value : GlobalPairedGaugeLieL2 period hPeriod => value index) hEqual)

private theorem smoothAdjoint_eq_correction :
    pairedFPCanonicalAdjointL2 period hPeriod metric =
      globalPairedAbelianFPL2LinearMap period hPeriod metric +
        (frameFreeFPH1Correction period hPeriod metric).toLinearMap.comp (pairedGhostH1 period hPeriod) := by
  apply LinearMap.ext
  intro field
  have h := frameFreePairedFPVolumeCorrection_smooth period hPeriod
    metric field
  exact h

def frameFreeFPH1Minimal : PairedFPH1 period hPeriod →ₗ.[Real] GlobalPairedGaugeLieL2 period hPeriod :=
  sobolevFeatureOperator (pairedGhostH1 period hPeriod)
    (globalPairedAbelianFPL2LinearMap period hPeriod metric)

def frameFreeFPFormalAdjointH1Minimal :
    PairedFPH1 period hPeriod →ₗ.[Real] GlobalPairedGaugeLieL2 period hPeriod :=
  sobolevFeatureOperator (pairedGhostH1 period hPeriod)
    (pairedFPCanonicalAdjointL2 period hPeriod metric)

private theorem fpCore_forgets (field : GlobalPairedGaugeLieSmooth period hPeriod) :
    (pairedH1ToL2 period hPeriod (pairedGhostH1 period hPeriod field),
      globalPairedAbelianFPL2LinearMap period hPeriod metric field) ∈
      (frameFreeFPCanonicalMinimal period hPeriod metric).graph := by
  rw [pairedH1ToL2_smooth]
  exact ((frameFreeFPCanonicalMinimal period hPeriod metric).mem_graph_iff).mpr
    ⟨⟨_, frameFreeFPCanonicalMinimal_smooth_mem period hPeriod metric field⟩, rfl,
      frameFreeFPCanonicalMinimal_smooth_apply period hPeriod metric field⟩

private theorem fpH1_single : Function.Injective
    (fun graph : sobolevFeatureGraphClosure (pairedGhostH1 period hPeriod)
      (globalPairedAbelianFPL2LinearMap period hPeriod metric) =>
        graph.val.1) :=
  sobolevFeatureGraphClosure_fst_injective_of_forget _ _ (pairedH1ToL2 period hPeriod)
    (frameFreeFPCanonicalMinimal period hPeriod metric) (frameFreeFPCanonicalMinimal_isClosed period hPeriod metric)
    (fpCore_forgets period hPeriod metric)

private theorem adjointH1_single : Function.Injective
    (fun graph : sobolevFeatureGraphClosure (pairedGhostH1 period hPeriod)
      (pairedFPCanonicalAdjointL2 period hPeriod metric) =>
        graph.val.1) := by
  rw [smoothAdjoint_eq_correction]
  exact sobolevFeatureGraphClosure_bounded_shear_fst_injective _ _
    (fpH1_single period hPeriod metric) (frameFreeFPH1Correction period hPeriod metric)

theorem frameFreeFPH1Minimal_isClosed : (frameFreeFPH1Minimal period hPeriod metric).IsClosed :=
  sobolevFeatureOperator_isClosed _ _ (fpH1_single period hPeriod metric)

theorem frameFreeFPFormalAdjointH1Minimal_isClosed :
    (frameFreeFPFormalAdjointH1Minimal period hPeriod metric).IsClosed :=
  sobolevFeatureOperator_isClosed _ _ (adjointH1_single period hPeriod metric)

theorem frameFreeFPH1Minimal_dense_domain :
    Dense ((frameFreeFPH1Minimal period hPeriod metric).domain : Set (PairedFPH1 period hPeriod)) :=
  sobolevFeatureOperator_dense_domain _ _ (pairedGhostH1_denseRange period hPeriod)

theorem frameFreeFPFormalAdjointH1Minimal_domain :
    (frameFreeFPFormalAdjointH1Minimal period hPeriod metric).domain =
      (frameFreeFPH1Minimal period hPeriod metric).domain := by
  unfold frameFreeFPFormalAdjointH1Minimal frameFreeFPH1Minimal
  rw [smoothAdjoint_eq_correction]
  exact sobolevFeatureOperator_bounded_shear_domain _ _ _

theorem frameFreeFPFormalAdjointH1Minimal_graph_iff
    (input : PairedFPH1 period hPeriod) (output : GlobalPairedGaugeLieL2 period hPeriod) :
    (input, output + frameFreeFPH1Correction period hPeriod metric input) ∈
        (frameFreeFPFormalAdjointH1Minimal period hPeriod metric).graph ↔
      (input, output) ∈ (frameFreeFPH1Minimal period hPeriod metric).graph := by
  rw [frameFreeFPFormalAdjointH1Minimal, frameFreeFPH1Minimal,
    sobolevFeatureOperator_graph _ _ (adjointH1_single period hPeriod metric),
    sobolevFeatureOperator_graph _ _ (fpH1_single period hPeriod metric),
    smoothAdjoint_eq_correction, sobolevFeatureGraphClosure_bounded_shear]
  constructor
  · rintro ⟨pair, hPair, hEqual⟩
    have hPairEq : pair = (input, output) :=
      (sobolevBoundedGraphShear (frameFreeFPH1Correction period hPeriod metric)).injective hEqual
    exact hPairEq ▸ hPair
  · intro hPair
    exact ⟨(input, output), hPair, rfl⟩

theorem frameFreeFPH1Minimal_forget_graph
    (input : PairedFPH1 period hPeriod) (output : GlobalPairedGaugeLieL2 period hPeriod)
    (hGraph : (input, output) ∈ (frameFreeFPH1Minimal period hPeriod metric).graph) :
    (pairedH1ToL2 period hPeriod input, output) ∈ (frameFreeFPCanonicalMinimal period hPeriod metric).graph := by
  rw [frameFreeFPH1Minimal, sobolevFeatureOperator_graph _ _ (fpH1_single period hPeriod metric)] at hGraph
  exact sobolevFeatureGraphClosure_forget_mem _ _ (pairedH1ToL2 period hPeriod)
    (frameFreeFPCanonicalMinimal period hPeriod metric) (frameFreeFPCanonicalMinimal_isClosed period hPeriod metric)
    (fpCore_forgets period hPeriod metric) _ hGraph

theorem frameFreeFPFormalAdjointH1Minimal_forget_graph
    (input : PairedFPH1 period hPeriod) (output : GlobalPairedGaugeLieL2 period hPeriod)
    (hGraph : (input, output) ∈ (frameFreeFPFormalAdjointH1Minimal period hPeriod metric).graph) :
    (pairedH1ToL2 period hPeriod input, output) ∈ (frameFreeFPFormalAdjointMinimal period hPeriod metric).graph := by
  rw [frameFreeFPFormalAdjointH1Minimal,
    sobolevFeatureOperator_graph _ _ (adjointH1_single period hPeriod metric)] at hGraph
  apply sobolevFeatureGraphClosure_forget_mem _ _ (pairedH1ToL2 period hPeriod)
    (frameFreeFPFormalAdjointMinimal period hPeriod metric)
    (frameFreeFPFormalAdjointMinimal_isClosed period hPeriod metric) ?_ _ hGraph
  intro field
  rw [pairedH1ToL2_smooth]
  exact ((frameFreeFPFormalAdjointMinimal period hPeriod metric).mem_graph_iff).mpr
    ⟨⟨_, frameFreeFPFormalAdjointMinimal_smooth_mem period hPeriod metric field⟩, rfl,
      frameFreeFPFormalAdjointMinimal_smooth_apply period hPeriod metric field⟩

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeFPH1Domain4D
