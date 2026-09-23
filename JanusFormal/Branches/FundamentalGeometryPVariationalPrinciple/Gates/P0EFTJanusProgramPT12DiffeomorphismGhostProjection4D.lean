import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismTripletAdjoint4D

/-! Orthogonal ghost/antighost projection inside the original BRST L² space. -/
namespace JanusFormal.P0EFTJanusProgramPT12DiffeomorphismGhostProjection4D
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

def diffeomorphismGhostProjection : DiffeomorphismL2 period hPeriod metric →L[Real]
    DiffeomorphismL2 period hPeriod metric :=
  diffeomorphismTripletL2 period hPeriod metric 0 0 + diffeomorphismTripletL2 period hPeriod metric 1 1

theorem diffeomorphismGhostProjection_pairing (first second : DiffeomorphismL2 period hPeriod metric) :
    inner Real (diffeomorphismGhostProjection period hPeriod metric first) second =
      inner Real first (diffeomorphismGhostProjection period hPeriod metric second) := by
  simp only [diffeomorphismGhostProjection, add_apply, inner_add_left,
    inner_add_right, diffeomorphismTripletL2_pairing]

theorem diffeomorphismGhostProjection_idempotent :
    (diffeomorphismGhostProjection period hPeriod metric).comp (diffeomorphismGhostProjection period hPeriod metric) =
      diffeomorphismGhostProjection period hPeriod metric := by
  simp only [diffeomorphismGhostProjection, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add,
    diffeomorphismTripletL2_comp]
  norm_num

theorem diffeomorphismGhostProjection_apply_twice (field : DiffeomorphismL2 period hPeriod metric) :
    diffeomorphismGhostProjection period hPeriod metric (diffeomorphismGhostProjection period hPeriod metric field) =
      diffeomorphismGhostProjection period hPeriod metric field :=
  congrArg (fun op : DiffeomorphismL2 period hPeriod metric →L[Real] DiffeomorphismL2 period hPeriod metric => op field)
    (diffeomorphismGhostProjection_idempotent period hPeriod metric)

theorem diffeomorphismGhostProjection_smooth
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    diffeomorphismGhostProjection period hPeriod metric (diffeomorphismL2Smooth period hPeriod metric field) =
      diffeomorphismL2Smooth period hPeriod metric
        (diffeomorphismTripletTransfer period hPeriod 0 0 field + diffeomorphismTripletTransfer period hPeriod 1 1 field) := by
  rw [diffeomorphismGhostProjection, add_apply,
    diffeomorphismTripletL2_smooth, diffeomorphismTripletL2_smooth, map_add]

theorem diffeomorphismGhostProjection_range_eq_fixed :
    ((diffeomorphismGhostProjection period hPeriod metric).range : Set (DiffeomorphismL2 period hPeriod metric)) =
      {field | diffeomorphismGhostProjection period hPeriod metric field = field} := by
  ext field
  constructor
  · rintro ⟨source, rfl⟩
    exact diffeomorphismGhostProjection_apply_twice period hPeriod metric source
  · intro h
    exact ⟨field, h⟩

theorem diffeomorphismGhostProjection_range_isClosed :
    IsClosed ((diffeomorphismGhostProjection period hPeriod metric).range : Set (DiffeomorphismL2 period hPeriod metric)) := by
  rw [diffeomorphismGhostProjection_range_eq_fixed]
  exact isClosed_eq (diffeomorphismGhostProjection period hPeriod metric).continuous continuous_id

abbrev DiffeomorphismGhostPairL2 := (diffeomorphismGhostProjection period hPeriod metric).range

instance : CompleteSpace (DiffeomorphismGhostPairL2 period hPeriod metric) :=
  (diffeomorphismGhostProjection_range_isClosed period hPeriod metric).completeSpace_coe

def diffeomorphismBosonProjection : DiffeomorphismL2 period hPeriod metric →L[Real]
    DiffeomorphismL2 period hPeriod metric :=
  ContinuousLinearMap.id Real _ - diffeomorphismGhostProjection period hPeriod metric

theorem diffeomorphismGhostBoson_decomposition (field : DiffeomorphismL2 period hPeriod metric) :
    diffeomorphismGhostProjection period hPeriod metric field + diffeomorphismBosonProjection period hPeriod metric field = field := by
  let projected : DiffeomorphismL2 period hPeriod metric := diffeomorphismGhostProjection period hPeriod metric field
  change projected + (field - projected) = field
  exact (add_comm projected (field - projected)).trans (sub_add_cancel field projected)

theorem diffeomorphismGhostBoson_orthogonal (first second : DiffeomorphismL2 period hPeriod metric) :
    inner Real (diffeomorphismGhostProjection period hPeriod metric first)
      (diffeomorphismBosonProjection period hPeriod metric second) = 0 := by
  change inner Real (diffeomorphismGhostProjection period hPeriod metric first)
    (second - diffeomorphismGhostProjection period hPeriod metric second) = 0
  rw [inner_sub_right, diffeomorphismGhostProjection_pairing, diffeomorphismGhostProjection_pairing,
    diffeomorphismGhostProjection_apply_twice, sub_self]

end
end JanusFormal.P0EFTJanusProgramPT12DiffeomorphismGhostProjection4D