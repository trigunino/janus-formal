import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12PairedFPH1Correction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12SobolevFeatureGraph4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CandidateAFPFormalAdjointCore4D

/-! Actual FP and formal-adjoint minimal closures with H¹ source: common domain.
These closures are contained in the existing L² graphs; no maximal-domain equality is claimed. -/
namespace JanusFormal.P0EFTJanusProgramPT12CandidateAFPH1Domain4D
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

variable {configuration : GlobalFieldConfiguration period hPeriod}
variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
variable (data : GlobalCandidateAActionData period hPeriod configuration couplings NonNullFace NullFace)

def candidateAFPH1Correction : PairedFPH1 period hPeriod →L[Real] GlobalPairedGaugeLieL2 period hPeriod :=
  pairedFPVolumeCorrection period hPeriod (candidateARegularMetricBySector period hPeriod data)

include data in
theorem candidateAFPH1ToL2_injective : Function.Injective (pairedH1ToL2 period hPeriod) := by
  intro first second hEqual
  apply PiLp.ext
  intro index
  exact P0EFTJanusProgramPT12CanonicalScalarH1Injective4D.canonicalScalarH1ToL2_injective
    period hPeriod (candidateARegularMetricBySector period hPeriod data index.1) _
    (congrArg (fun value : GlobalPairedGaugeLieL2 period hPeriod => value index) hEqual)

private theorem smoothAdjoint_eq_correction :
    pairedFPCanonicalAdjointL2 period hPeriod (globalCandidateAMetricBySector period hPeriod data) =
      globalPairedAbelianFPL2LinearMap period hPeriod (globalCandidateAMetricBySector period hPeriod data) +
        (candidateAFPH1Correction period hPeriod data).toLinearMap.comp (pairedGhostH1 period hPeriod) := by
  apply LinearMap.ext
  intro field
  have h := pairedFPVolumeCorrection_smooth period hPeriod
    (candidateARegularMetricBySector period hPeriod data) field
  rw [candidateARegularMetricBySector_metric] at h
  exact h

def candidateAFPH1Minimal : PairedFPH1 period hPeriod →ₗ.[Real] GlobalPairedGaugeLieL2 period hPeriod :=
  sobolevFeatureOperator (pairedGhostH1 period hPeriod)
    (globalPairedAbelianFPL2LinearMap period hPeriod (globalCandidateAMetricBySector period hPeriod data))

def candidateAFPFormalAdjointH1Minimal :
    PairedFPH1 period hPeriod →ₗ.[Real] GlobalPairedGaugeLieL2 period hPeriod :=
  sobolevFeatureOperator (pairedGhostH1 period hPeriod)
    (pairedFPCanonicalAdjointL2 period hPeriod (globalCandidateAMetricBySector period hPeriod data))

private theorem fpCore_forgets (field : GlobalPairedGaugeLieSmooth period hPeriod) :
    (pairedH1ToL2 period hPeriod (pairedGhostH1 period hPeriod field),
      globalPairedAbelianFPL2LinearMap period hPeriod (globalCandidateAMetricBySector period hPeriod data) field) ∈
      (candidateAFPCanonicalMinimal period hPeriod data).graph := by
  rw [pairedH1ToL2_smooth]
  exact ((candidateAFPCanonicalMinimal period hPeriod data).mem_graph_iff).mpr
    ⟨⟨_, candidateAFPCanonicalMinimal_smooth_mem period hPeriod data field⟩, rfl,
      candidateAFPCanonicalMinimal_smooth_apply period hPeriod data field⟩

private theorem fpH1_single : Function.Injective
    (fun graph : sobolevFeatureGraphClosure (pairedGhostH1 period hPeriod)
      (globalPairedAbelianFPL2LinearMap period hPeriod (globalCandidateAMetricBySector period hPeriod data)) =>
        graph.val.1) :=
  sobolevFeatureGraphClosure_fst_injective_of_forget _ _ (pairedH1ToL2 period hPeriod)
    (candidateAFPCanonicalMinimal period hPeriod data) (candidateAFPCanonicalMinimal_isClosed period hPeriod data)
    (fpCore_forgets period hPeriod data)

private theorem adjointH1_single : Function.Injective
    (fun graph : sobolevFeatureGraphClosure (pairedGhostH1 period hPeriod)
      (pairedFPCanonicalAdjointL2 period hPeriod (globalCandidateAMetricBySector period hPeriod data)) =>
        graph.val.1) := by
  rw [smoothAdjoint_eq_correction]
  exact sobolevFeatureGraphClosure_bounded_shear_fst_injective _ _
    (fpH1_single period hPeriod data) (candidateAFPH1Correction period hPeriod data)

theorem candidateAFPH1Minimal_isClosed : (candidateAFPH1Minimal period hPeriod data).IsClosed :=
  sobolevFeatureOperator_isClosed _ _ (fpH1_single period hPeriod data)

theorem candidateAFPFormalAdjointH1Minimal_isClosed :
    (candidateAFPFormalAdjointH1Minimal period hPeriod data).IsClosed :=
  sobolevFeatureOperator_isClosed _ _ (adjointH1_single period hPeriod data)

theorem candidateAFPH1Minimal_dense_domain :
    Dense ((candidateAFPH1Minimal period hPeriod data).domain : Set (PairedFPH1 period hPeriod)) :=
  sobolevFeatureOperator_dense_domain _ _ (pairedGhostH1_denseRange period hPeriod)

theorem candidateAFPFormalAdjointH1Minimal_domain :
    (candidateAFPFormalAdjointH1Minimal period hPeriod data).domain =
      (candidateAFPH1Minimal period hPeriod data).domain := by
  unfold candidateAFPFormalAdjointH1Minimal candidateAFPH1Minimal
  rw [smoothAdjoint_eq_correction]
  exact sobolevFeatureOperator_bounded_shear_domain _ _ _

theorem candidateAFPFormalAdjointH1Minimal_graph_iff
    (input : PairedFPH1 period hPeriod) (output : GlobalPairedGaugeLieL2 period hPeriod) :
    (input, output + candidateAFPH1Correction period hPeriod data input) ∈
        (candidateAFPFormalAdjointH1Minimal period hPeriod data).graph ↔
      (input, output) ∈ (candidateAFPH1Minimal period hPeriod data).graph := by
  rw [candidateAFPFormalAdjointH1Minimal, candidateAFPH1Minimal,
    sobolevFeatureOperator_graph _ _ (adjointH1_single period hPeriod data),
    sobolevFeatureOperator_graph _ _ (fpH1_single period hPeriod data),
    smoothAdjoint_eq_correction, sobolevFeatureGraphClosure_bounded_shear]
  constructor
  · rintro ⟨pair, hPair, hEqual⟩
    have hPairEq : pair = (input, output) :=
      (sobolevBoundedGraphShear (candidateAFPH1Correction period hPeriod data)).injective hEqual
    exact hPairEq ▸ hPair
  · intro hPair
    exact ⟨(input, output), hPair, rfl⟩

theorem candidateAFPH1Minimal_forget_graph
    (input : PairedFPH1 period hPeriod) (output : GlobalPairedGaugeLieL2 period hPeriod)
    (hGraph : (input, output) ∈ (candidateAFPH1Minimal period hPeriod data).graph) :
    (pairedH1ToL2 period hPeriod input, output) ∈ (candidateAFPCanonicalMinimal period hPeriod data).graph := by
  rw [candidateAFPH1Minimal, sobolevFeatureOperator_graph _ _ (fpH1_single period hPeriod data)] at hGraph
  exact sobolevFeatureGraphClosure_forget_mem _ _ (pairedH1ToL2 period hPeriod)
    (candidateAFPCanonicalMinimal period hPeriod data) (candidateAFPCanonicalMinimal_isClosed period hPeriod data)
    (fpCore_forgets period hPeriod data) _ hGraph

theorem candidateAFPFormalAdjointH1Minimal_forget_graph
    (input : PairedFPH1 period hPeriod) (output : GlobalPairedGaugeLieL2 period hPeriod)
    (hGraph : (input, output) ∈ (candidateAFPFormalAdjointH1Minimal period hPeriod data).graph) :
    (pairedH1ToL2 period hPeriod input, output) ∈ (candidateAFPFormalAdjointMinimal period hPeriod data).graph := by
  rw [candidateAFPFormalAdjointH1Minimal,
    sobolevFeatureOperator_graph _ _ (adjointH1_single period hPeriod data)] at hGraph
  apply sobolevFeatureGraphClosure_forget_mem _ _ (pairedH1ToL2 period hPeriod)
    (candidateAFPFormalAdjointMinimal period hPeriod data)
    (candidateAFPFormalAdjointMinimal_isClosed period hPeriod data) ?_ _ hGraph
  intro field
  rw [pairedH1ToL2_smooth]
  exact ((candidateAFPFormalAdjointMinimal period hPeriod data).mem_graph_iff).mpr
    ⟨⟨_, candidateAFPFormalAdjointMinimal_smooth_mem period hPeriod data field⟩, rfl,
      candidateAFPFormalAdjointMinimal_smooth_apply period hPeriod data field⟩

end
end JanusFormal.P0EFTJanusProgramPT12CandidateAFPH1Domain4D
