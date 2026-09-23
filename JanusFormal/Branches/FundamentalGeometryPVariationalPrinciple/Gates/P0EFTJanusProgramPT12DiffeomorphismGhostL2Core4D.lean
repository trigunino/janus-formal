import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismGhostProjection4D

/-! A dense projected smooth ghost core and the exact original L² orthogonal splitting. -/
namespace JanusFormal.P0EFTJanusProgramPT12DiffeomorphismGhostL2Core4D
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

def diffeomorphismGhostPairSmooth : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod →ₗ[Real]
    DiffeomorphismGhostPairL2 period hPeriod metric :=
  (diffeomorphismGhostProjection period hPeriod metric).rangeRestrict.toLinearMap.comp
    (diffeomorphismL2Smooth period hPeriod metric)

theorem diffeomorphismGhostPairSmooth_denseRange :
    DenseRange (diffeomorphismGhostPairSmooth period hPeriod metric) := by
  have hSurj : Function.Surjective (diffeomorphismGhostProjection period hPeriod metric).rangeRestrict := by
    rintro ⟨field, source, hSource⟩
    exact ⟨source, Subtype.ext hSource⟩
  exact hSurj.denseRange.comp (diffeomorphismL2Smooth_denseRange period hPeriod metric)
    (diffeomorphismGhostProjection period hPeriod metric).rangeRestrict.continuous

theorem diffeomorphismGhostPairSmooth_original
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    (diffeomorphismGhostPairSmooth period hPeriod metric field).val =
      diffeomorphismL2Smooth period hPeriod metric
        (diffeomorphismTripletTransfer period hPeriod 0 0 field + diffeomorphismTripletTransfer period hPeriod 1 1 field) :=
  diffeomorphismGhostProjection_smooth period hPeriod metric field

theorem diffeomorphismGhostBoson_norm_sq (field : DiffeomorphismL2 period hPeriod metric) :
    ‖diffeomorphismGhostProjection period hPeriod metric field‖ ^ 2 +
      ‖diffeomorphismBosonProjection period hPeriod metric field‖ ^ 2 = ‖field‖ ^ 2 := by
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_real
    (diffeomorphismGhostBoson_orthogonal period hPeriod metric field field)
  rw [diffeomorphismGhostBoson_decomposition] at h
  simpa only [pow_two] using h.symm

theorem diffeomorphismGhostBoson_inner (first second : DiffeomorphismL2 period hPeriod metric) :
    inner Real first second =
      inner Real (diffeomorphismGhostProjection period hPeriod metric first)
        (diffeomorphismGhostProjection period hPeriod metric second) +
      inner Real (diffeomorphismBosonProjection period hPeriod metric first)
        (diffeomorphismBosonProjection period hPeriod metric second) := by
  have hReverse : inner Real (diffeomorphismBosonProjection period hPeriod metric first)
      (diffeomorphismGhostProjection period hPeriod metric second) = 0 :=
    (real_inner_comm (diffeomorphismGhostProjection period hPeriod metric second)
      (diffeomorphismBosonProjection period hPeriod metric first)).trans
      (diffeomorphismGhostBoson_orthogonal period hPeriod metric second first)
  calc
    inner Real first second = inner Real
      (diffeomorphismGhostProjection period hPeriod metric first + diffeomorphismBosonProjection period hPeriod metric first)
      (diffeomorphismGhostProjection period hPeriod metric second + diffeomorphismBosonProjection period hPeriod metric second) := by
        rw [diffeomorphismGhostBoson_decomposition, diffeomorphismGhostBoson_decomposition]
    _ = _ := by rw [inner_add_left, inner_add_right, inner_add_right,
      diffeomorphismGhostBoson_orthogonal, hReverse, add_zero, zero_add]

end
end JanusFormal.P0EFTJanusProgramPT12DiffeomorphismGhostL2Core4D