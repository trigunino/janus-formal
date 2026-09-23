import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismL2Triplet4D
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Orthogonal matrix units on the actual completed BRST triplet. -/
namespace JanusFormal.P0EFTJanusProgramPT12DiffeomorphismTripletAdjoint4D
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

theorem diffeomorphismTripletL2_pairing (i j : Fin 3)
    (first second : DiffeomorphismL2 period hPeriod metric) :
    inner Real (diffeomorphismTripletL2 period hPeriod metric i j first) second =
      inner Real first (diffeomorphismTripletL2 period hPeriod metric j i second) := by
  change inner Real (diffeomorphismTripletAmbient period hPeriod i j first.val) second.val =
    inner Real first.val (diffeomorphismTripletAmbient period hPeriod j i second.val)
  change inner Real (WithLp.fst (diffeomorphismTripletAmbient period hPeriod i j first.val)) (WithLp.fst second.val) +
    inner Real (WithLp.snd (diffeomorphismTripletAmbient period hPeriod i j first.val)) (WithLp.snd second.val) =
      inner Real (WithLp.fst first.val) (WithLp.fst (diffeomorphismTripletAmbient period hPeriod j i second.val)) +
        inner Real (WithLp.snd first.val) (WithLp.snd (diffeomorphismTripletAmbient period hPeriod j i second.val))
  rw [diffeomorphismTripletAmbient_metric, diffeomorphismTripletAmbient_metric,
    inner_zero_left, inner_zero_right, zero_add, zero_add]
  change (∑ k : Fin 3, inner Real (WithLp.snd (diffeomorphismTripletAmbient period hPeriod i j first.val) k)
      (WithLp.snd second.val k)) =
    ∑ k : Fin 3, inner Real (WithLp.snd first.val k)
      (WithLp.snd (diffeomorphismTripletAmbient period hPeriod j i second.val) k)
  simp only [diffeomorphismTripletAmbient_coordinate, apply_ite, inner_zero_right]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_eq_single i] <;> simp_all only [Finset.mem_univ, if_true, if_false, inner_zero_left, not_true_eq_false] <;> simp
theorem diffeomorphismTripletL2_idempotent (i : Fin 3) :
    (diffeomorphismTripletL2 period hPeriod metric i i).comp
      (diffeomorphismTripletL2 period hPeriod metric i i) =
        diffeomorphismTripletL2 period hPeriod metric i i := by
  rw [diffeomorphismTripletL2_comp, if_pos rfl]

theorem diffeomorphismTripletL2_orthogonal (i j : Fin 3) (h : i ≠ j)
    (first second : DiffeomorphismL2 period hPeriod metric) :
    inner Real (diffeomorphismTripletL2 period hPeriod metric i i first)
      (diffeomorphismTripletL2 period hPeriod metric j j second) = 0 := by
  rw [diffeomorphismTripletL2_pairing]
  have hComp := congrArg (fun op : DiffeomorphismL2 period hPeriod metric →L[Real]
      DiffeomorphismL2 period hPeriod metric => op second)
    (diffeomorphismTripletL2_comp period hPeriod metric i i j j)
  simp only [if_neg h, ContinuousLinearMap.comp_apply, zero_apply] at hComp
  rw [hComp, inner_zero_right]

end
end JanusFormal.P0EFTJanusProgramPT12DiffeomorphismTripletAdjoint4D