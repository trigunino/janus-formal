import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismTripletComponent4D

/-! Isometric reconstruction of the actual ghost pair from its original ghost component. -/
namespace JanusFormal.P0EFTJanusProgramPT12DiffeomorphismGhostPairIsometry4D
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

local instance componentInnerProductSpace (i : Fin 3) :
    InnerProductSpace Real (DiffeomorphismTripletComponentL2 period hPeriod metric i) :=
  Submodule.innerProductSpace (𝕜 := Real) (E := DiffeomorphismL2 period hPeriod metric)
    (diffeomorphismTripletL2 period hPeriod metric i i).range

local instance pairInnerProductSpace :
    InnerProductSpace Real (DiffeomorphismGhostPairL2 period hPeriod metric) :=
  Submodule.innerProductSpace (𝕜 := Real) (E := DiffeomorphismL2 period hPeriod metric)
    (diffeomorphismGhostProjection period hPeriod metric).range

abbrev DiffeomorphismGhostComponentPairL2 :=
  WithLp 2 (DiffeomorphismTripletComponentL2 period hPeriod metric 0 ×
    DiffeomorphismTripletComponentL2 period hPeriod metric 0)

local instance componentPairInnerProductSpace :
    InnerProductSpace Real (DiffeomorphismGhostComponentPairL2 period hPeriod metric) :=
  WithLp.instProdInnerProductSpace (𝕜 := Real)
    (E := DiffeomorphismTripletComponentL2 period hPeriod metric 0)
    (F := DiffeomorphismTripletComponentL2 period hPeriod metric 0)
private theorem triplet_comp_zero (i j k l : Fin 3) (hne : j ≠ k)
    (field : DiffeomorphismL2 period hPeriod metric) :
    diffeomorphismTripletL2 period hPeriod metric i j
      (diffeomorphismTripletL2 period hPeriod metric k l field) = 0 := by
  have h := diffeomorphismTripletL2_comp period hPeriod metric i j k l
  rw [if_neg hne] at h
  exact congrArg (fun op : DiffeomorphismL2 period hPeriod metric →L[Real]
    DiffeomorphismL2 period hPeriod metric => op field) h

theorem diffeomorphismGhostPairAssemble_fixed
    (first second : DiffeomorphismTripletComponentL2 period hPeriod metric 0) :
    diffeomorphismGhostProjection period hPeriod metric
      (first.val + diffeomorphismTripletL2 period hPeriod metric 1 0 second.val) =
        first.val + diffeomorphismTripletL2 period hPeriod metric 1 0 second.val := by
  obtain ⟨source, hSource⟩ := first.property
  change diffeomorphismTripletL2 period hPeriod metric 0 0 source = first.val at hSource
  rw [← hSource]
  simp only [diffeomorphismGhostProjection, add_apply, map_add,
    diffeomorphismTripletL2_comp_apply,
    triplet_comp_zero period hPeriod metric 0 0 1 0 (by decide),
    triplet_comp_zero period hPeriod metric 1 1 0 0 (by decide), add_zero, zero_add]

def diffeomorphismGhostPairAssembleLinear :
    DiffeomorphismGhostComponentPairL2 period hPeriod metric →ₗ[Real]
      DiffeomorphismGhostPairL2 period hPeriod metric :=
  let component := (diffeomorphismTripletL2 period hPeriod metric 0 0).range.subtype
  let transfer := (diffeomorphismTripletL2 period hPeriod metric 1 0).toLinearMap.comp component
  let assemble := (component.coprod transfer).comp
    (WithLp.linearEquiv 2 Real
      (DiffeomorphismTripletComponentL2 period hPeriod metric 0 ×
       DiffeomorphismTripletComponentL2 period hPeriod metric 0)).toLinearMap
  assemble.codRestrict (diffeomorphismGhostProjection period hPeriod metric).range
    (fun field => ⟨assemble field,
      diffeomorphismGhostPairAssemble_fixed period hPeriod metric field.fst field.snd⟩)

theorem diffeomorphismGhostPairAssemble_orthogonal
    (first second : DiffeomorphismTripletComponentL2 period hPeriod metric 0) :
    inner Real first.val (diffeomorphismTripletL2 period hPeriod metric 1 0 second.val) = 0 := by
  have h := diffeomorphismTripletL2_orthogonal period hPeriod metric 0 1 (by decide)
    first.val (diffeomorphismTripletL2 period hPeriod metric 1 0 second.val)
  rw [diffeomorphismTripletComponent_fixed, diffeomorphismTripletL2_comp_apply] at h
  exact h

theorem diffeomorphismGhostPairAssemble_inner
    (first second : DiffeomorphismGhostComponentPairL2 period hPeriod metric) :
    inner Real (diffeomorphismGhostPairAssembleLinear period hPeriod metric first)
      (diffeomorphismGhostPairAssembleLinear period hPeriod metric second) = inner Real first second := by
  change inner Real
    (first.fst.val + diffeomorphismTripletL2 period hPeriod metric 1 0 first.snd.val)
    (second.fst.val + diffeomorphismTripletL2 period hPeriod metric 1 0 second.snd.val) =
      inner Real first.fst.val second.fst.val + inner Real first.snd.val second.snd.val
  rw [inner_add_left, inner_add_right, inner_add_right,
    diffeomorphismGhostPairAssemble_orthogonal,
    real_inner_comm second.fst.val (diffeomorphismTripletL2 period hPeriod metric 1 0 first.snd.val),
    diffeomorphismGhostPairAssemble_orthogonal, add_zero, zero_add]
  apply congrArg (inner Real first.fst.val second.fst.val + ·)
  exact diffeomorphismTripletComponentTransfer_inner period hPeriod metric 1 0 first.snd second.snd

def diffeomorphismGhostPairAssemble :
    DiffeomorphismGhostComponentPairL2 period hPeriod metric →ₗᵢ[Real]
      DiffeomorphismGhostPairL2 period hPeriod metric where
  toLinearMap := diffeomorphismGhostPairAssembleLinear period hPeriod metric
  norm_map' field := by
    change ‖diffeomorphismGhostPairAssembleLinear period hPeriod metric field‖ = ‖field‖
    rw [norm_eq_sqrt_real_inner (diffeomorphismGhostPairAssembleLinear period hPeriod metric field),
      norm_eq_sqrt_real_inner field, diffeomorphismGhostPairAssemble_inner]

theorem diffeomorphismGhostPairAssemble_surjective :
    Function.Surjective (diffeomorphismGhostPairAssemble period hPeriod metric) := by
  intro field
  let first : DiffeomorphismTripletComponentL2 period hPeriod metric 0 :=
    ⟨diffeomorphismTripletL2 period hPeriod metric 0 0 field.val, ⟨field.val, rfl⟩⟩
  let second : DiffeomorphismTripletComponentL2 period hPeriod metric 0 :=
    ⟨diffeomorphismTripletL2 period hPeriod metric 0 1 field.val,
      ⟨diffeomorphismTripletL2 period hPeriod metric 0 1 field.val,
        diffeomorphismTripletL2_comp_apply period hPeriod metric 0 0 1 field.val⟩⟩
  refine ⟨WithLp.toLp 2 (first, second), ?_⟩
  apply Subtype.ext
  change diffeomorphismTripletL2 period hPeriod metric 0 0 field.val +
    diffeomorphismTripletL2 period hPeriod metric 1 0
      (diffeomorphismTripletL2 period hPeriod metric 0 1 field.val) = field.val
  rw [diffeomorphismTripletL2_comp_apply]
  exact (Set.ext_iff.mp (diffeomorphismGhostProjection_range_eq_fixed period hPeriod metric) field.val).mp field.property

def diffeomorphismGhostPairIsometry :
    DiffeomorphismGhostComponentPairL2 period hPeriod metric ≃ₗᵢ[Real]
      DiffeomorphismGhostPairL2 period hPeriod metric :=
  LinearIsometryEquiv.ofSurjective (diffeomorphismGhostPairAssemble period hPeriod metric)
    (diffeomorphismGhostPairAssemble_surjective period hPeriod metric)

end
end JanusFormal.P0EFTJanusProgramPT12DiffeomorphismGhostPairIsometry4D
