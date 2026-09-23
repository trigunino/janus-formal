import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismMetricProjection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismBosonL2Core4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismTripletComponent4D

/-! Isometric reconstruction of the full field from its ghost and metric–B components. -/
namespace JanusFormal.P0EFTJanusProgramPT12GhostBosonIsometry4D
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

local instance ghostInnerProductSpace : InnerProductSpace Real (DiffeomorphismGhostPairL2 period hPeriod metric) :=
  Submodule.innerProductSpace (𝕜 := Real) (E := DiffeomorphismL2 period hPeriod metric) (diffeomorphismGhostProjection period hPeriod metric).range
local instance bosonInnerProductSpace : InnerProductSpace Real (DiffeomorphismBosonPairL2 period hPeriod metric) :=
  Submodule.innerProductSpace (𝕜 := Real) (E := DiffeomorphismL2 period hPeriod metric) (diffeomorphismBosonProjection period hPeriod metric).range

abbrev GhostBosonPairL2 := WithLp 2 (DiffeomorphismGhostPairL2 period hPeriod metric × DiffeomorphismBosonPairL2 period hPeriod metric)
local instance pairInnerProductSpace : InnerProductSpace Real (GhostBosonPairL2 period hPeriod metric) :=
  @WithLp.instProdInnerProductSpace Real (DiffeomorphismGhostPairL2 period hPeriod metric) (DiffeomorphismBosonPairL2 period hPeriod metric)
    _ _ (ghostInnerProductSpace period hPeriod metric) _ (bosonInnerProductSpace period hPeriod metric)

def ghostBosonAssembleLinear : GhostBosonPairL2 period hPeriod metric →ₗ[Real] DiffeomorphismL2 period hPeriod metric :=
  ((diffeomorphismGhostProjection period hPeriod metric).range.subtype.coprod (diffeomorphismBosonProjection period hPeriod metric).range.subtype).comp
    (WithLp.linearEquiv 2 Real (DiffeomorphismGhostPairL2 period hPeriod metric × DiffeomorphismBosonPairL2 period hPeriod metric)).toLinearMap

theorem ghostBosonComponents_orthogonal (first : DiffeomorphismGhostPairL2 period hPeriod metric) (second : DiffeomorphismBosonPairL2 period hPeriod metric) :
    inner Real first.val second.val = 0 := by
  obtain ⟨x, hx⟩ := first.property
  obtain ⟨y, hy⟩ := second.property
  change diffeomorphismGhostProjection period hPeriod metric x = first.val at hx
  change diffeomorphismBosonProjection period hPeriod metric y = second.val at hy
  rw [← hx, ← hy]
  exact diffeomorphismGhostBoson_orthogonal period hPeriod metric x y

theorem ghostBosonAssemble_inner (first second : GhostBosonPairL2 period hPeriod metric) :
    inner Real (ghostBosonAssembleLinear period hPeriod metric first)
      (ghostBosonAssembleLinear period hPeriod metric second) = inner Real first second := by
  change inner Real (first.fst.val + first.snd.val) (second.fst.val + second.snd.val) =
    inner Real first.fst.val second.fst.val + inner Real first.snd.val second.snd.val
  rw [inner_add_left, inner_add_right, inner_add_right, ghostBosonComponents_orthogonal,
    real_inner_comm second.fst.val first.snd.val, ghostBosonComponents_orthogonal, add_zero, zero_add]

def ghostBosonAssemble : GhostBosonPairL2 period hPeriod metric →ₗᵢ[Real] DiffeomorphismL2 period hPeriod metric where
  toLinearMap := ghostBosonAssembleLinear period hPeriod metric
  norm_map' field := by
    change ‖ghostBosonAssembleLinear period hPeriod metric field‖ = ‖field‖
    rw [norm_eq_sqrt_real_inner (ghostBosonAssembleLinear period hPeriod metric field),
      norm_eq_sqrt_real_inner field, ghostBosonAssemble_inner]

theorem ghostBosonAssemble_surjective : Function.Surjective (ghostBosonAssemble period hPeriod metric) := by
  intro field
  refine ⟨WithLp.toLp 2 ((diffeomorphismGhostProjection period hPeriod metric).rangeRestrict field, (diffeomorphismBosonProjection period hPeriod metric).rangeRestrict field), ?_⟩
  exact diffeomorphismGhostBoson_decomposition period hPeriod metric field

def ghostBosonIsometry : GhostBosonPairL2 period hPeriod metric ≃ₗᵢ[Real] DiffeomorphismL2 period hPeriod metric :=
  LinearIsometryEquiv.ofSurjective (ghostBosonAssemble period hPeriod metric)
    (ghostBosonAssemble_surjective period hPeriod metric)

theorem ghostBosonIsometry_apply (field : GhostBosonPairL2 period hPeriod metric) :
    ghostBosonIsometry period hPeriod metric field = field.fst.val + field.snd.val := rfl

theorem ghostBosonIsometry_symm_apply (field : DiffeomorphismL2 period hPeriod metric) :
    (ghostBosonIsometry period hPeriod metric).symm field =
      WithLp.toLp 2 ((diffeomorphismGhostProjection period hPeriod metric).rangeRestrict field, (diffeomorphismBosonProjection period hPeriod metric).rangeRestrict field) := by
  apply (ghostBosonIsometry period hPeriod metric).injective
  rw [LinearIsometryEquiv.apply_symm_apply, ghostBosonIsometry_apply]
  exact (diffeomorphismGhostBoson_decomposition period hPeriod metric field).symm

end
end JanusFormal.P0EFTJanusProgramPT12GhostBosonIsometry4D
