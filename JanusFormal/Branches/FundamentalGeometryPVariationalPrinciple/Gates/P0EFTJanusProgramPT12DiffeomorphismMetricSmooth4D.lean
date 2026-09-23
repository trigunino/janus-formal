import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismMetricProjection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismComponentSmooth4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismTripletComponent4D

/-! Linear smooth transfers and dense smooth domains of the actual triplet components. -/
namespace JanusFormal.P0EFTJanusProgramPT12DiffeomorphismMetricSmooth4D
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

open P0EFTJanusProgramPT12DiffeomorphismMetricProjection4D
open P0EFTJanusProgramPT12DiffeomorphismComponentSmooth4D

def diffeomorphismMetricTransfer :
    GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod →ₗ[Real]
      GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod :=
  LinearMap.id - (diffeomorphismTripletTransferLinearMap period hPeriod metric 0 0 +
    diffeomorphismTripletTransferLinearMap period hPeriod metric 1 1 +
    diffeomorphismTripletTransferLinearMap period hPeriod metric 2 2)

theorem diffeomorphismMetricTransfer_L2
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    diffeomorphismMetricProjection period hPeriod metric (diffeomorphismL2Smooth period hPeriod metric field) =
      diffeomorphismL2Smooth period hPeriod metric (diffeomorphismMetricTransfer period hPeriod metric field) := by
  change diffeomorphismL2Smooth period hPeriod metric field -
    (diffeomorphismTripletL2 period hPeriod metric 0 0 (diffeomorphismL2Smooth period hPeriod metric field) +
     diffeomorphismTripletL2 period hPeriod metric 1 1 (diffeomorphismL2Smooth period hPeriod metric field)) -
    diffeomorphismTripletL2 period hPeriod metric 2 2 (diffeomorphismL2Smooth period hPeriod metric field) =
    diffeomorphismL2Smooth period hPeriod metric
      (field - (diffeomorphismTripletTransfer period hPeriod 0 0 field +
        diffeomorphismTripletTransfer period hPeriod 1 1 field + diffeomorphismTripletTransfer period hPeriod 2 2 field))
  rw [diffeomorphismTripletL2_smooth, diffeomorphismTripletL2_smooth, diffeomorphismTripletL2_smooth,
    map_sub, map_add, map_add]
  abel

def diffeomorphismMetricSmooth : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod →ₗ[Real]
    DiffeomorphismMetricL2 period hPeriod metric :=
  (diffeomorphismMetricProjection period hPeriod metric).rangeRestrict.toLinearMap.comp
    (diffeomorphismL2Smooth period hPeriod metric)

theorem diffeomorphismMetricSmooth_denseRange : DenseRange (diffeomorphismMetricSmooth period hPeriod metric) := by
  have hSurj : Function.Surjective (diffeomorphismMetricProjection period hPeriod metric).rangeRestrict := by
    rintro ⟨field, source, hSource⟩
    exact ⟨source, Subtype.ext hSource⟩
  exact hSurj.denseRange.comp (diffeomorphismL2Smooth_denseRange period hPeriod metric)
    (diffeomorphismMetricProjection period hPeriod metric).rangeRestrict.continuous

theorem diffeomorphismMetricSmooth_original
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    (diffeomorphismMetricSmooth period hPeriod metric field).val =
      diffeomorphismL2Smooth period hPeriod metric (diffeomorphismMetricTransfer period hPeriod metric field) :=
  diffeomorphismMetricTransfer_L2 period hPeriod metric field

theorem diffeomorphismMetricTransfer_metric
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    (diffeomorphismMetricTransfer period hPeriod metric field).metricPerturbation = field.metricPerturbation := by
  change field.metricPerturbation - ((0 + 0) + 0) = field.metricPerturbation
  rw [add_zero, add_zero, sub_zero]

theorem diffeomorphismMetricTransfer_ghost
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    (diffeomorphismMetricTransfer period hPeriod metric field).nonminimal.ghost = 0 := by
  apply GlobalDiffeomorphismGhostField.ext
  change field.nonminimal.ghost.field - ((field.nonminimal.ghost.field + 0) + 0) = 0
  rw [add_zero, add_zero, sub_self]

theorem diffeomorphismMetricTransfer_antighost
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    (diffeomorphismMetricTransfer period hPeriod metric field).nonminimal.antighost = 0 := by
  apply GlobalDiffeomorphismAntighostField.ext
  change field.nonminimal.antighost.field - ((0 + field.nonminimal.antighost.field) + 0) = 0
  rw [zero_add, add_zero, sub_self]

theorem diffeomorphismMetricTransfer_B
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    (diffeomorphismMetricTransfer period hPeriod metric field).nonminimal.nakanishiLautrup = 0 := by
  apply GlobalDiffeomorphismNakanishiLautrupField.ext
  change field.nonminimal.nakanishiLautrup.field - ((0 + 0) + field.nonminimal.nakanishiLautrup.field) = 0
  rw [zero_add, zero_add, sub_self]

end
end JanusFormal.P0EFTJanusProgramPT12DiffeomorphismMetricSmooth4D