import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismGhostProjection4D

/-! The closed actual metric–B Hilbert subspace and its dense projected smooth inclusion. -/
namespace JanusFormal.P0EFTJanusProgramPT12DiffeomorphismBosonL2Core4D
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

open P0EFTJanusProgramPT12DiffeomorphismGhostProjection4D

theorem diffeomorphismBosonProjection_pairing (first second : DiffeomorphismL2 period hPeriod metric) :
    inner Real (diffeomorphismBosonProjection period hPeriod metric first) second =
      inner Real first (diffeomorphismBosonProjection period hPeriod metric second) := by
  change inner Real (first - diffeomorphismGhostProjection period hPeriod metric first) second =
    inner Real first (second - diffeomorphismGhostProjection period hPeriod metric second)
  rw [inner_sub_left, inner_sub_right, diffeomorphismGhostProjection_pairing]

theorem diffeomorphismBosonProjection_apply_twice (field : DiffeomorphismL2 period hPeriod metric) :
    diffeomorphismBosonProjection period hPeriod metric
      (diffeomorphismBosonProjection period hPeriod metric field) =
      diffeomorphismBosonProjection period hPeriod metric field := by
  change (field - diffeomorphismGhostProjection period hPeriod metric field) -
    diffeomorphismGhostProjection period hPeriod metric
      (field - diffeomorphismGhostProjection period hPeriod metric field) = _
  rw [map_sub, diffeomorphismGhostProjection_apply_twice, sub_self, sub_zero]
  rfl

theorem diffeomorphismBosonProjection_range_eq_fixed :
    ((diffeomorphismBosonProjection period hPeriod metric).range : Set (DiffeomorphismL2 period hPeriod metric)) =
      {field | diffeomorphismBosonProjection period hPeriod metric field = field} := by
  ext field
  constructor
  · rintro ⟨source, rfl⟩
    exact diffeomorphismBosonProjection_apply_twice period hPeriod metric source
  · intro h
    exact ⟨field, h⟩

theorem diffeomorphismBosonProjection_range_isClosed :
    IsClosed ((diffeomorphismBosonProjection period hPeriod metric).range : Set (DiffeomorphismL2 period hPeriod metric)) := by
  rw [diffeomorphismBosonProjection_range_eq_fixed]
  exact isClosed_eq (diffeomorphismBosonProjection period hPeriod metric).continuous continuous_id

abbrev DiffeomorphismBosonPairL2 := (diffeomorphismBosonProjection period hPeriod metric).range

instance : CompleteSpace (DiffeomorphismBosonPairL2 period hPeriod metric) :=
  (diffeomorphismBosonProjection_range_isClosed period hPeriod metric).completeSpace_coe

def diffeomorphismBosonPairSmooth : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod →ₗ[Real]
    DiffeomorphismBosonPairL2 period hPeriod metric :=
  (diffeomorphismBosonProjection period hPeriod metric).rangeRestrict.toLinearMap.comp
    (diffeomorphismL2Smooth period hPeriod metric)

theorem diffeomorphismBosonPairSmooth_denseRange :
    DenseRange (diffeomorphismBosonPairSmooth period hPeriod metric) := by
  have hSurj : Function.Surjective (diffeomorphismBosonProjection period hPeriod metric).rangeRestrict := by
    rintro ⟨field, source, hSource⟩
    exact ⟨source, Subtype.ext hSource⟩
  exact hSurj.denseRange.comp (diffeomorphismL2Smooth_denseRange period hPeriod metric)
    (diffeomorphismBosonProjection period hPeriod metric).rangeRestrict.continuous

theorem diffeomorphismBosonPairSmooth_original
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    (diffeomorphismBosonPairSmooth period hPeriod metric field).val =
      diffeomorphismL2Smooth period hPeriod metric
        (field - (diffeomorphismTripletTransfer period hPeriod 0 0 field +
          diffeomorphismTripletTransfer period hPeriod 1 1 field)) := by
  change diffeomorphismL2Smooth period hPeriod metric field -
    diffeomorphismGhostProjection period hPeriod metric (diffeomorphismL2Smooth period hPeriod metric field) = _
  rw [diffeomorphismGhostProjection_smooth, map_sub]

end
end JanusFormal.P0EFTJanusProgramPT12DiffeomorphismBosonL2Core4D