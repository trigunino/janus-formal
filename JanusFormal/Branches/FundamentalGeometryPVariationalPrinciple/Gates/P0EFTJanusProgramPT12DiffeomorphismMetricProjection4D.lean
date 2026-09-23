import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismBosonL2Core4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismTripletComponent4D

/-! The orthogonal metric projection inside the actual metric–B Hilbert space. -/
namespace JanusFormal.P0EFTJanusProgramPT12DiffeomorphismMetricProjection4D
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

theorem diffeomorphismTripletL2_comp_zero (i j k l : Fin 3) (hne : j ≠ k)
    (field : DiffeomorphismL2 period hPeriod metric) :
    diffeomorphismTripletL2 period hPeriod metric i j
      (diffeomorphismTripletL2 period hPeriod metric k l field) = 0 := by
  have h := diffeomorphismTripletL2_comp period hPeriod metric i j k l
  rw [if_neg hne] at h
  exact congrArg (fun op : DiffeomorphismL2 period hPeriod metric →L[Real]
    DiffeomorphismL2 period hPeriod metric => op field) h

theorem diffeomorphismBoson_auxiliary (field : DiffeomorphismL2 period hPeriod metric) :
    diffeomorphismBosonProjection period hPeriod metric
      (diffeomorphismTripletL2 period hPeriod metric 2 2 field) =
      diffeomorphismTripletL2 period hPeriod metric 2 2 field := by
  change diffeomorphismTripletL2 period hPeriod metric 2 2 field -
    (diffeomorphismTripletL2 period hPeriod metric 0 0
      (diffeomorphismTripletL2 period hPeriod metric 2 2 field) +
     diffeomorphismTripletL2 period hPeriod metric 1 1
      (diffeomorphismTripletL2 period hPeriod metric 2 2 field)) = _
  rw [diffeomorphismTripletL2_comp_zero period hPeriod metric 0 0 2 2 (by decide),
    diffeomorphismTripletL2_comp_zero period hPeriod metric 1 1 2 2 (by decide), add_zero, sub_zero]

theorem diffeomorphismAuxiliary_boson (field : DiffeomorphismL2 period hPeriod metric) :
    diffeomorphismTripletL2 period hPeriod metric 2 2
      (diffeomorphismBosonProjection period hPeriod metric field) =
      diffeomorphismTripletL2 period hPeriod metric 2 2 field := by
  change diffeomorphismTripletL2 period hPeriod metric 2 2
    (field - (diffeomorphismTripletL2 period hPeriod metric 0 0 field +
      diffeomorphismTripletL2 period hPeriod metric 1 1 field)) = _
  rw [map_sub, map_add,
    diffeomorphismTripletL2_comp_zero period hPeriod metric 2 2 0 0 (by decide),
    diffeomorphismTripletL2_comp_zero period hPeriod metric 2 2 1 1 (by decide), add_zero, sub_zero]

def diffeomorphismMetricProjection : DiffeomorphismL2 period hPeriod metric →L[Real]
    DiffeomorphismL2 period hPeriod metric :=
  diffeomorphismBosonProjection period hPeriod metric - diffeomorphismTripletL2 period hPeriod metric 2 2

theorem diffeomorphismMetricProjection_pairing (first second : DiffeomorphismL2 period hPeriod metric) :
    inner Real (diffeomorphismMetricProjection period hPeriod metric first) second =
      inner Real first (diffeomorphismMetricProjection period hPeriod metric second) := by
  change inner Real (diffeomorphismBosonProjection period hPeriod metric first -
    diffeomorphismTripletL2 period hPeriod metric 2 2 first) second =
    inner Real first (diffeomorphismBosonProjection period hPeriod metric second -
      diffeomorphismTripletL2 period hPeriod metric 2 2 second)
  rw [inner_sub_left, inner_sub_right, diffeomorphismBosonProjection_pairing, diffeomorphismTripletL2_pairing]

theorem diffeomorphismBoson_metric (field : DiffeomorphismL2 period hPeriod metric) :
    diffeomorphismBosonProjection period hPeriod metric
      (diffeomorphismMetricProjection period hPeriod metric field) =
      diffeomorphismMetricProjection period hPeriod metric field := by
  change diffeomorphismBosonProjection period hPeriod metric
    (diffeomorphismBosonProjection period hPeriod metric field -
      diffeomorphismTripletL2 period hPeriod metric 2 2 field) = _
  rw [map_sub, diffeomorphismBosonProjection_apply_twice, diffeomorphismBoson_auxiliary]
  rfl

theorem diffeomorphismAuxiliary_metric_zero (field : DiffeomorphismL2 period hPeriod metric) :
    diffeomorphismTripletL2 period hPeriod metric 2 2
      (diffeomorphismMetricProjection period hPeriod metric field) = 0 := by
  change diffeomorphismTripletL2 period hPeriod metric 2 2
    (diffeomorphismBosonProjection period hPeriod metric field -
      diffeomorphismTripletL2 period hPeriod metric 2 2 field) = 0
  rw [map_sub, diffeomorphismAuxiliary_boson, diffeomorphismTripletL2_comp_apply, sub_self]

theorem diffeomorphismMetric_auxiliary_zero (field : DiffeomorphismL2 period hPeriod metric) :
    diffeomorphismMetricProjection period hPeriod metric
      (diffeomorphismTripletL2 period hPeriod metric 2 2 field) = 0 := by
  change diffeomorphismBosonProjection period hPeriod metric
    (diffeomorphismTripletL2 period hPeriod metric 2 2 field) -
    diffeomorphismTripletL2 period hPeriod metric 2 2
      (diffeomorphismTripletL2 period hPeriod metric 2 2 field) = 0
  rw [diffeomorphismBoson_auxiliary, diffeomorphismTripletL2_comp_apply, sub_self]

theorem diffeomorphismMetricProjection_apply_twice (field : DiffeomorphismL2 period hPeriod metric) :
    diffeomorphismMetricProjection period hPeriod metric
      (diffeomorphismMetricProjection period hPeriod metric field) =
      diffeomorphismMetricProjection period hPeriod metric field := by
  change diffeomorphismBosonProjection period hPeriod metric
    (diffeomorphismMetricProjection period hPeriod metric field) -
    diffeomorphismTripletL2 period hPeriod metric 2 2
      (diffeomorphismMetricProjection period hPeriod metric field) = _
  rw [diffeomorphismBoson_metric, diffeomorphismAuxiliary_metric_zero, sub_zero]

theorem diffeomorphismMetricAuxiliary_decomposition (field : DiffeomorphismL2 period hPeriod metric) :
    diffeomorphismMetricProjection period hPeriod metric field +
      diffeomorphismTripletL2 period hPeriod metric 2 2 field =
      diffeomorphismBosonProjection period hPeriod metric field :=
  sub_add_cancel _ _

theorem diffeomorphismMetricProjection_range_eq_fixed :
    ((diffeomorphismMetricProjection period hPeriod metric).range : Set (DiffeomorphismL2 period hPeriod metric)) =
      {field | diffeomorphismMetricProjection period hPeriod metric field = field} := by
  ext field
  constructor
  · rintro ⟨source, rfl⟩
    exact diffeomorphismMetricProjection_apply_twice period hPeriod metric source
  · intro h
    exact ⟨field, h⟩

theorem diffeomorphismMetricProjection_range_isClosed :
    IsClosed ((diffeomorphismMetricProjection period hPeriod metric).range : Set (DiffeomorphismL2 period hPeriod metric)) := by
  rw [diffeomorphismMetricProjection_range_eq_fixed]
  exact isClosed_eq (diffeomorphismMetricProjection period hPeriod metric).continuous continuous_id

abbrev DiffeomorphismMetricL2 := (diffeomorphismMetricProjection period hPeriod metric).range
instance : CompleteSpace (DiffeomorphismMetricL2 period hPeriod metric) :=
  (diffeomorphismMetricProjection_range_isClosed period hPeriod metric).completeSpace_coe

theorem diffeomorphismMetric_fixed (field : DiffeomorphismMetricL2 period hPeriod metric) :
    diffeomorphismMetricProjection period hPeriod metric field.val = field.val :=
  (Set.ext_iff.mp (diffeomorphismMetricProjection_range_eq_fixed period hPeriod metric) field.val).mp field.property

end
end JanusFormal.P0EFTJanusProgramPT12DiffeomorphismMetricProjection4D