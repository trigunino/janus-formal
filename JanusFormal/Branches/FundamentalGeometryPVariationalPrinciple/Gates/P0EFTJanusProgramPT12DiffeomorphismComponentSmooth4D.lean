import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismTripletComponent4D

/-! Linear smooth transfers and dense smooth domains of the actual triplet components. -/
namespace JanusFormal.P0EFTJanusProgramPT12DiffeomorphismComponentSmooth4D
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

def diffeomorphismTripletTransferLinearMap (i j : Fin 3) :
    GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod →ₗ[Real]
      GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod where
  toFun := diffeomorphismTripletTransfer period hPeriod i j
  map_add' first second := by
    apply diffeomorphismL2Smooth_injective period hPeriod metric
    rw [map_add, ← diffeomorphismTripletL2_smooth, ← diffeomorphismTripletL2_smooth,
      ← diffeomorphismTripletL2_smooth, map_add, map_add]
  map_smul' scalar field := by
    apply diffeomorphismL2Smooth_injective period hPeriod metric
    change diffeomorphismL2Smooth period hPeriod metric
      (diffeomorphismTripletTransfer period hPeriod i j (scalar • field)) =
        diffeomorphismL2Smooth period hPeriod metric
          (scalar • diffeomorphismTripletTransfer period hPeriod i j field)
    rw [map_smul, ← diffeomorphismTripletL2_smooth, ← diffeomorphismTripletL2_smooth,
      map_smul, map_smul]

def diffeomorphismTripletComponentSmooth (i : Fin 3) :
    GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod →ₗ[Real]
      DiffeomorphismTripletComponentL2 period hPeriod metric i :=
  (diffeomorphismTripletL2 period hPeriod metric i i).rangeRestrict.toLinearMap.comp
    (diffeomorphismL2Smooth period hPeriod metric)

theorem diffeomorphismTripletComponentSmooth_denseRange (i : Fin 3) :
    DenseRange (diffeomorphismTripletComponentSmooth period hPeriod metric i) := by
  have hSurj : Function.Surjective (diffeomorphismTripletL2 period hPeriod metric i i).rangeRestrict := by
    rintro ⟨field, source, hSource⟩
    exact ⟨source, Subtype.ext hSource⟩
  exact hSurj.denseRange.comp (diffeomorphismL2Smooth_denseRange period hPeriod metric)
    (diffeomorphismTripletL2 period hPeriod metric i i).rangeRestrict.continuous

theorem diffeomorphismTripletComponentSmooth_original (i : Fin 3)
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    (diffeomorphismTripletComponentSmooth period hPeriod metric i field).val =
      diffeomorphismL2Smooth period hPeriod metric (diffeomorphismTripletTransfer period hPeriod i i field) :=
  diffeomorphismTripletL2_smooth period hPeriod metric i i field

theorem diffeomorphismTripletComponentSmooth_transfer (i j : Fin 3)
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    diffeomorphismTripletComponentTransfer period hPeriod metric i j
      (diffeomorphismTripletComponentSmooth period hPeriod metric j field) =
        diffeomorphismTripletComponentSmooth period hPeriod metric i
          (diffeomorphismTripletTransfer period hPeriod i j field) := by
  apply Subtype.ext
  change diffeomorphismTripletL2 period hPeriod metric i j
    (diffeomorphismTripletL2 period hPeriod metric j j
      (diffeomorphismL2Smooth period hPeriod metric field)) =
    diffeomorphismTripletL2 period hPeriod metric i i
      (diffeomorphismL2Smooth period hPeriod metric (diffeomorphismTripletTransfer period hPeriod i j field))
  rw [← diffeomorphismTripletL2_smooth, diffeomorphismTripletL2_comp_apply,
    diffeomorphismTripletL2_comp_apply]

end
end JanusFormal.P0EFTJanusProgramPT12DiffeomorphismComponentSmooth4D
