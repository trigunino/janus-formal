import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismGhostProjection4D

/-! The original triplet components are closed Hilbert subspaces with canonical isometric transfers. -/
namespace JanusFormal.P0EFTJanusProgramPT12DiffeomorphismTripletComponent4D
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

theorem diffeomorphismTripletL2_comp_apply (i j k : Fin 3)
    (field : DiffeomorphismL2 period hPeriod metric) :
    diffeomorphismTripletL2 period hPeriod metric i j
      (diffeomorphismTripletL2 period hPeriod metric j k field) =
        diffeomorphismTripletL2 period hPeriod metric i k field := by
  have h := diffeomorphismTripletL2_comp period hPeriod metric i j j k
  rw [if_pos rfl] at h
  exact congrArg (fun op : DiffeomorphismL2 period hPeriod metric →L[Real]
    DiffeomorphismL2 period hPeriod metric => op field) h

theorem diffeomorphismTripletL2_range_eq_fixed (i : Fin 3) :
    ((diffeomorphismTripletL2 period hPeriod metric i i).range :
      Set (DiffeomorphismL2 period hPeriod metric)) =
      {field | diffeomorphismTripletL2 period hPeriod metric i i field = field} := by
  ext field
  constructor
  · rintro ⟨source, rfl⟩
    exact diffeomorphismTripletL2_comp_apply period hPeriod metric i i i source
  · intro h
    exact ⟨field, h⟩

theorem diffeomorphismTripletL2_range_isClosed (i : Fin 3) :
    IsClosed ((diffeomorphismTripletL2 period hPeriod metric i i).range :
      Set (DiffeomorphismL2 period hPeriod metric)) := by
  rw [diffeomorphismTripletL2_range_eq_fixed]
  exact isClosed_eq (diffeomorphismTripletL2 period hPeriod metric i i).continuous continuous_id

abbrev DiffeomorphismTripletComponentL2 (i : Fin 3) :=
  (diffeomorphismTripletL2 period hPeriod metric i i).range

instance (i : Fin 3) : CompleteSpace (DiffeomorphismTripletComponentL2 period hPeriod metric i) :=
  (diffeomorphismTripletL2_range_isClosed period hPeriod metric i).completeSpace_coe

local instance componentInnerProductSpace (i : Fin 3) :
    InnerProductSpace Real (DiffeomorphismTripletComponentL2 period hPeriod metric i) :=
  Submodule.innerProductSpace (𝕜 := Real) (E := DiffeomorphismL2 period hPeriod metric)
    (diffeomorphismTripletL2 period hPeriod metric i i).range

theorem diffeomorphismTripletComponent_fixed (i : Fin 3)
    (field : DiffeomorphismTripletComponentL2 period hPeriod metric i) :
    diffeomorphismTripletL2 period hPeriod metric i i field.val = field.val :=
  (Set.ext_iff.mp (diffeomorphismTripletL2_range_eq_fixed period hPeriod metric i) field.val).mp field.property

def diffeomorphismTripletComponentTransfer (i j : Fin 3) :
    DiffeomorphismTripletComponentL2 period hPeriod metric j →ₗ[Real]
      DiffeomorphismTripletComponentL2 period hPeriod metric i :=
  ((diffeomorphismTripletL2 period hPeriod metric i j).toLinearMap.comp
    (diffeomorphismTripletL2 period hPeriod metric j j).range.subtype).codRestrict
      (diffeomorphismTripletL2 period hPeriod metric i i).range (fun field =>
        ⟨diffeomorphismTripletL2 period hPeriod metric i j field.val,
          diffeomorphismTripletL2_comp_apply period hPeriod metric i i j field.val⟩)

theorem diffeomorphismTripletComponentTransfer_inverse (i j : Fin 3)
    (field : DiffeomorphismTripletComponentL2 period hPeriod metric j) :
    diffeomorphismTripletComponentTransfer period hPeriod metric j i
      (diffeomorphismTripletComponentTransfer period hPeriod metric i j field) = field := by
  apply Subtype.ext
  change diffeomorphismTripletL2 period hPeriod metric j i
    (diffeomorphismTripletL2 period hPeriod metric i j field.val) = field.val
  rw [diffeomorphismTripletL2_comp_apply, diffeomorphismTripletComponent_fixed]

theorem diffeomorphismTripletComponentTransfer_inner (i j : Fin 3)
    (first second : DiffeomorphismTripletComponentL2 period hPeriod metric j) :
    inner Real (diffeomorphismTripletComponentTransfer period hPeriod metric i j first)
      (diffeomorphismTripletComponentTransfer period hPeriod metric i j second) =
        inner Real first second := by
  change inner Real (diffeomorphismTripletL2 period hPeriod metric i j first.val)
    (diffeomorphismTripletL2 period hPeriod metric i j second.val) = inner Real first.val second.val
  rw [diffeomorphismTripletL2_pairing, diffeomorphismTripletL2_comp_apply,
    diffeomorphismTripletComponent_fixed]

def diffeomorphismTripletComponentEquiv (i j : Fin 3) :
    DiffeomorphismTripletComponentL2 period hPeriod metric j ≃ₗ[Real]
      DiffeomorphismTripletComponentL2 period hPeriod metric i where
  toLinearMap := diffeomorphismTripletComponentTransfer period hPeriod metric i j
  invFun := diffeomorphismTripletComponentTransfer period hPeriod metric j i
  left_inv := diffeomorphismTripletComponentTransfer_inverse period hPeriod metric i j
  right_inv := diffeomorphismTripletComponentTransfer_inverse period hPeriod metric j i

def diffeomorphismTripletComponentIsometry (i j : Fin 3) :
    DiffeomorphismTripletComponentL2 period hPeriod metric j ≃ₗᵢ[Real]
      DiffeomorphismTripletComponentL2 period hPeriod metric i where
  toLinearEquiv := diffeomorphismTripletComponentEquiv period hPeriod metric i j
  norm_map' field := by
    change ‖diffeomorphismTripletComponentTransfer period hPeriod metric i j field‖ = ‖field‖
    rw [norm_eq_sqrt_real_inner (diffeomorphismTripletComponentTransfer period hPeriod metric i j field), norm_eq_sqrt_real_inner field,
      diffeomorphismTripletComponentTransfer_inner]

end
end JanusFormal.P0EFTJanusProgramPT12DiffeomorphismTripletComponent4D
