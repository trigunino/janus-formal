import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeFPClosed4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ClosedFeatureCore4D

/-! Minimal closure of the genuine smooth FP formal adjoint, without a global tangent basis.
This construction makes no assertion of equality with the maximal Hilbert adjoint. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeFPFormalAdjointCore4D
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
open P0EFTJanusProgramPT12ClosedFeatureOperator4D
open P0EFTJanusProgramPT12ClosedFeatureCore4D
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

def frameFreeFPFormalAdjointMinimal :
    GlobalPairedGaugeLieL2 period hPeriod →ₗ.[Real] GlobalPairedGaugeLieL2 period hPeriod :=
  closedFeatureOperator (globalPairedGaugeLieL2LinearMap period hPeriod)
    (pairedFPCanonicalAdjointL2 period hPeriod metric)

theorem frameFreeFPFormalAdjointGraph_input_injective :
    Function.Injective (fun graph : linearFeatureGraphClosure
      (globalPairedGaugeLieL2LinearMap period hPeriod)
      (pairedFPCanonicalAdjointL2 period hPeriod metric) => graph.val.1) := by
  apply linearFeatureGraphClosure_fst_injective _ _
    (globalPairedAbelianFPL2LinearMap period hPeriod metric)
    (globalPairedGaugeLieL2LinearMap_denseRange period hPeriod)
  intro field test
  calc
    _ = inner Real (globalPairedGaugeLieL2LinearMap period hPeriod test)
        (pairedFPCanonicalAdjointL2 period hPeriod metric field) := real_inner_comm _ _
    _ = inner Real (globalPairedAbelianFPL2LinearMap period hPeriod metric test)
        (globalPairedGaugeLieL2LinearMap period hPeriod field) :=
      (frameFreePairedFPCanonicalAdjoint_pairing period hPeriod metric test field).symm
    _ = _ := real_inner_comm _ _

theorem frameFreeFPFormalAdjointMinimal_graph :
    (frameFreeFPFormalAdjointMinimal period hPeriod metric).graph =
      linearFeatureGraphClosure (globalPairedGaugeLieL2LinearMap period hPeriod)
        (pairedFPCanonicalAdjointL2 period hPeriod metric) :=
  closedFeatureOperator_graph _ _ (frameFreeFPFormalAdjointGraph_input_injective period hPeriod metric)

theorem frameFreeFPFormalAdjointMinimal_isClosed :
    (frameFreeFPFormalAdjointMinimal period hPeriod metric).IsClosed :=
  closedFeatureOperator_isClosed _ _ (frameFreeFPFormalAdjointGraph_input_injective period hPeriod metric)

theorem frameFreeFPFormalAdjointMinimal_dense_domain :
    Dense ((frameFreeFPFormalAdjointMinimal period hPeriod metric).domain :
      Set (GlobalPairedGaugeLieL2 period hPeriod)) :=
  closedFeatureOperator_dense_domain _ _ (globalPairedGaugeLieL2LinearMap_denseRange period hPeriod)

theorem frameFreeFPFormalAdjointMinimal_smooth_mem
    (field : GlobalPairedGaugeLieSmooth period hPeriod) :
    globalPairedGaugeLieL2LinearMap period hPeriod field ∈
      (frameFreeFPFormalAdjointMinimal period hPeriod metric).domain :=
  closedFeatureOperator_smooth_mem _ _ field

theorem frameFreeFPFormalAdjointMinimal_smooth_apply
    (field : GlobalPairedGaugeLieSmooth period hPeriod) :
    frameFreeFPFormalAdjointMinimal period hPeriod metric
      ⟨globalPairedGaugeLieL2LinearMap period hPeriod field,
        frameFreeFPFormalAdjointMinimal_smooth_mem period hPeriod metric field⟩ =
      pairedFPCanonicalAdjointL2 period hPeriod metric field :=
  closedFeatureOperator_smooth_apply _ _
    (frameFreeFPFormalAdjointGraph_input_injective period hPeriod metric) field

theorem frameFreeFPFormalAdjointMinimal_hasCore :
    (frameFreeFPFormalAdjointMinimal period hPeriod metric).HasCore
      (globalPairedGaugeLieL2LinearMap period hPeriod).range :=
  closedFeatureOperator_hasCore _ _ (frameFreeFPFormalAdjointGraph_input_injective period hPeriod metric)

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeFPFormalAdjointCore4D
