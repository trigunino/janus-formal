import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismMetricProjection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismBosonL2Core4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismTripletComponent4D

/-! Isometric reconstruction of the actual metric–B space from its metric and auxiliary components. -/
namespace JanusFormal.P0EFTJanusProgramPT12MetricBAuxiliaryIsometry4D
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 600000
noncomputable section
open Set
open scoped InnerProductSpace Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphCore4D
open P0EFTJanusProgramPGlobalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPT12DiffeomorphismL2Core4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

open P0EFTJanusProgramPT12DiffeomorphismL2Triplet4D
variable (metric : SmoothGeneralLorentzMetric period hPeriod)

open P0EFTJanusProgramPT12DiffeomorphismTripletAdjoint4D

open P0EFTJanusProgramPT12DiffeomorphismTripletComponent4D
open P0EFTJanusProgramPT12DiffeomorphismGhostProjection4D

open P0EFTJanusProgramPT12DiffeomorphismBosonL2Core4D

open P0EFTJanusProgramPT12DiffeomorphismMetricProjection4D

local instance metricInnerProductSpace : InnerProductSpace Real (DiffeomorphismMetricL2 period hPeriod metric) :=
  Submodule.innerProductSpace (𝕜 := Real) (E := DiffeomorphismL2 period hPeriod metric)
    (diffeomorphismMetricProjection period hPeriod metric).range
local instance auxiliaryInnerProductSpace :
    InnerProductSpace Real (DiffeomorphismTripletComponentL2 period hPeriod metric 2) :=
  Submodule.innerProductSpace (𝕜 := Real) (E := DiffeomorphismL2 period hPeriod metric)
    (diffeomorphismTripletL2 period hPeriod metric 2 2).range
local instance bosonInnerProductSpace : InnerProductSpace Real (DiffeomorphismBosonPairL2 period hPeriod metric) :=
  Submodule.innerProductSpace (𝕜 := Real) (E := DiffeomorphismL2 period hPeriod metric)
    (diffeomorphismBosonProjection period hPeriod metric).range

abbrev MetricBAuxiliaryPairL2 := WithLp 2
  (DiffeomorphismMetricL2 period hPeriod metric × DiffeomorphismTripletComponentL2 period hPeriod metric 2)
local instance metricBPairInnerProductSpace : InnerProductSpace Real (MetricBAuxiliaryPairL2 period hPeriod metric) :=
  @WithLp.instProdInnerProductSpace Real
    (DiffeomorphismMetricL2 period hPeriod metric) (DiffeomorphismTripletComponentL2 period hPeriod metric 2)
    _ _ (metricInnerProductSpace period hPeriod metric) _ (auxiliaryInnerProductSpace period hPeriod metric)

theorem metricBAuxiliaryAssemble_fixed
    (first : DiffeomorphismMetricL2 period hPeriod metric)
    (second : DiffeomorphismTripletComponentL2 period hPeriod metric 2) :
    diffeomorphismBosonProjection period hPeriod metric (first.val + second.val) = first.val + second.val := by
  obtain ⟨x, hx⟩ := first.property
  obtain ⟨y, hy⟩ := second.property
  change diffeomorphismMetricProjection period hPeriod metric x = first.val at hx
  change diffeomorphismTripletL2 period hPeriod metric 2 2 y = second.val at hy
  rw [← hx, ← hy, map_add, diffeomorphismBoson_metric, diffeomorphismBoson_auxiliary]

def metricBAuxiliaryAssembleLinear : MetricBAuxiliaryPairL2 period hPeriod metric →ₗ[Real]
    DiffeomorphismBosonPairL2 period hPeriod metric :=
  let first := (diffeomorphismMetricProjection period hPeriod metric).range.subtype
  let second := (diffeomorphismTripletL2 period hPeriod metric 2 2).range.subtype
  let assemble := (first.coprod second).comp
    (WithLp.linearEquiv 2 Real
      (DiffeomorphismMetricL2 period hPeriod metric × DiffeomorphismTripletComponentL2 period hPeriod metric 2)).toLinearMap
  assemble.codRestrict (diffeomorphismBosonProjection period hPeriod metric).range
    (fun field => ⟨assemble field, metricBAuxiliaryAssemble_fixed period hPeriod metric field.fst field.snd⟩)

theorem metricBAuxiliary_orthogonal
    (first : DiffeomorphismMetricL2 period hPeriod metric)
    (second : DiffeomorphismTripletComponentL2 period hPeriod metric 2) :
    inner Real first.val second.val = 0 := by
  have h := diffeomorphismMetricProjection_pairing period hPeriod metric first.val second.val
  rw [diffeomorphismMetric_fixed] at h
  rw [h]
  obtain ⟨source, hSource⟩ := second.property
  change diffeomorphismTripletL2 period hPeriod metric 2 2 source = second.val at hSource
  rw [← hSource, diffeomorphismMetric_auxiliary_zero, inner_zero_right]

theorem metricBAuxiliaryAssemble_inner (first second : MetricBAuxiliaryPairL2 period hPeriod metric) :
    inner Real (metricBAuxiliaryAssembleLinear period hPeriod metric first)
      (metricBAuxiliaryAssembleLinear period hPeriod metric second) = inner Real first second := by
  change inner Real (first.fst.val + first.snd.val) (second.fst.val + second.snd.val) =
    inner Real first.fst.val second.fst.val + inner Real first.snd.val second.snd.val
  rw [inner_add_left, inner_add_right, inner_add_right, metricBAuxiliary_orthogonal,
    real_inner_comm second.fst.val first.snd.val, metricBAuxiliary_orthogonal, add_zero, zero_add]

def metricBAuxiliaryAssemble : MetricBAuxiliaryPairL2 period hPeriod metric →ₗᵢ[Real]
    DiffeomorphismBosonPairL2 period hPeriod metric where
  toLinearMap := metricBAuxiliaryAssembleLinear period hPeriod metric
  norm_map' field := by
    change ‖metricBAuxiliaryAssembleLinear period hPeriod metric field‖ = ‖field‖
    rw [norm_eq_sqrt_real_inner (metricBAuxiliaryAssembleLinear period hPeriod metric field),
      norm_eq_sqrt_real_inner field, metricBAuxiliaryAssemble_inner]

theorem metricBAuxiliaryAssemble_surjective : Function.Surjective (metricBAuxiliaryAssemble period hPeriod metric) := by
  intro field
  let first : DiffeomorphismMetricL2 period hPeriod metric :=
    ⟨diffeomorphismMetricProjection period hPeriod metric field.val, ⟨field.val, rfl⟩⟩
  let second : DiffeomorphismTripletComponentL2 period hPeriod metric 2 :=
    ⟨diffeomorphismTripletL2 period hPeriod metric 2 2 field.val, ⟨field.val, rfl⟩⟩
  refine ⟨WithLp.toLp 2 (first, second), ?_⟩
  apply Subtype.ext
  change diffeomorphismMetricProjection period hPeriod metric field.val +
    diffeomorphismTripletL2 period hPeriod metric 2 2 field.val = field.val
  rw [diffeomorphismMetricAuxiliary_decomposition]
  exact (Set.ext_iff.mp (diffeomorphismBosonProjection_range_eq_fixed period hPeriod metric) field.val).mp field.property

def metricBAuxiliaryIsometry : MetricBAuxiliaryPairL2 period hPeriod metric ≃ₗᵢ[Real]
    DiffeomorphismBosonPairL2 period hPeriod metric :=
  LinearIsometryEquiv.ofSurjective (metricBAuxiliaryAssemble period hPeriod metric)
    (metricBAuxiliaryAssemble_surjective period hPeriod metric)

end
end JanusFormal.P0EFTJanusProgramPT12MetricBAuxiliaryIsometry4D