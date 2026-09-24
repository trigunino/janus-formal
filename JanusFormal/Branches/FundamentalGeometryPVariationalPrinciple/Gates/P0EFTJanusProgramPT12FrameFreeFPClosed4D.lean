import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12PairedFPClosable4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ClosedFeatureOperator4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeFPCanonicalPairing4D

/-! The minimal closed actual FP operator for an intrinsic smooth pair of Lorentz metrics. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeFPClosed4D
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal Manifold ContDiff InnerProductSpace Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalAbelianLorenzGraphRiesz4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianNakanishiLautrupL2Residual4D
open P0EFTJanusProgramPT12PairedFPCanonicalAdjoint4D
open P0EFTJanusProgramPT12DenseAdjointGraphClosable4D
open P0EFTJanusProgramPT12PairedFPClosable4D
open P0EFTJanusProgramPT12ClosedFeatureOperator4D
open P0EFTJanusProgramPT12FrameFreeFPCanonicalPairing4D

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

variable (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)

theorem frameFreeCanonicalPairedFPGraph_input_injective :
    Function.Injective (fun graph : CanonicalPairedFPGraph period hPeriod metric => graph.val.1) :=
  linearFeatureGraphClosure_fst_injective (globalPairedGaugeLieL2LinearMap period hPeriod)
    (globalPairedAbelianFPL2LinearMap period hPeriod metric)
    (pairedFPCanonicalAdjointL2 period hPeriod metric)
    (globalPairedGaugeLieL2LinearMap_denseRange period hPeriod)
    (frameFreePairedFPCanonicalAdjoint_pairing period hPeriod metric)

/-- Closure of the genuine smooth FP graph in canonical L². -/
def frameFreeFPCanonicalMinimal :
    GlobalPairedGaugeLieL2 period hPeriod →ₗ.[Real] GlobalPairedGaugeLieL2 period hPeriod :=
  closedFeatureOperator (globalPairedGaugeLieL2LinearMap period hPeriod)
    (globalPairedAbelianFPL2LinearMap period hPeriod metric)

theorem frameFreeFPCanonicalMinimal_graph :
    (frameFreeFPCanonicalMinimal period hPeriod metric).graph =
      CanonicalPairedFPGraph period hPeriod metric :=
  closedFeatureOperator_graph _ _ (frameFreeCanonicalPairedFPGraph_input_injective period hPeriod metric)

theorem frameFreeFPCanonicalMinimal_isClosed :
    (frameFreeFPCanonicalMinimal period hPeriod metric).IsClosed :=
  closedFeatureOperator_isClosed _ _ (frameFreeCanonicalPairedFPGraph_input_injective period hPeriod metric)

theorem frameFreeFPCanonicalMinimal_dense_domain :
    Dense ((frameFreeFPCanonicalMinimal period hPeriod metric).domain :
      Set (GlobalPairedGaugeLieL2 period hPeriod)) :=
  closedFeatureOperator_dense_domain _ _ (globalPairedGaugeLieL2LinearMap_denseRange period hPeriod)

theorem frameFreeFPCanonicalMinimal_smooth_mem
    (field : GlobalPairedGaugeLieSmooth period hPeriod) :
    globalPairedGaugeLieL2LinearMap period hPeriod field ∈
      (frameFreeFPCanonicalMinimal period hPeriod metric).domain :=
  closedFeatureOperator_smooth_mem _ _ field

theorem frameFreeFPCanonicalMinimal_smooth_apply
    (field : GlobalPairedGaugeLieSmooth period hPeriod) :
    frameFreeFPCanonicalMinimal period hPeriod metric
      ⟨globalPairedGaugeLieL2LinearMap period hPeriod field,
        frameFreeFPCanonicalMinimal_smooth_mem period hPeriod metric field⟩ =
      globalPairedAbelianFPL2LinearMap period hPeriod metric field :=
  closedFeatureOperator_smooth_apply _ _
    (frameFreeCanonicalPairedFPGraph_input_injective period hPeriod metric) field

theorem frameFreeFPCanonicalMinimal_le_closed_extension
    (extension : GlobalPairedGaugeLieL2 period hPeriod →ₗ.[Real] GlobalPairedGaugeLieL2 period hPeriod)
    (hClosed : extension.IsClosed)
    (hExtends : ∀ field, (globalPairedGaugeLieL2LinearMap period hPeriod field,
      globalPairedAbelianFPL2LinearMap period hPeriod metric field) ∈ extension.graph) :
    frameFreeFPCanonicalMinimal period hPeriod metric ≤ extension :=
  closedFeatureOperator_minimal _ _
    (frameFreeCanonicalPairedFPGraph_input_injective period hPeriod metric) extension hClosed hExtends

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeFPClosed4D
