import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismL2Core4D

/-! Bounded matrix units on the actual L² BRST triplet. Their invariance of the
completed smooth image uses the common normalization of the three fields. -/
namespace JanusFormal.P0EFTJanusProgramPT12DiffeomorphismL2Triplet4D
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

/-- Transfer one triplet field, indexed as ghost/antighost/multiplier. -/
def diffeomorphismTripletTransfer (i j : Fin 3)
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod :=
  let source := ![field.nonminimal.ghost.field, field.nonminimal.antighost.field,
    field.nonminimal.nakanishiLautrup.field] j
  { metricPerturbation := 0
    nonminimal :=
      { ghost := ⟨if 0 = i then source else 0⟩
        antighost := ⟨if 1 = i then source else 0⟩
        nakanishiLautrup := ⟨if 2 = i then source else 0⟩ } }

def diffeomorphismTripletAmbient (i j : Fin 3) :
    DiffeomorphismL2Ambient period hPeriod →L[Real] DiffeomorphismL2Ambient period hPeriod :=
  let read := (PiLp.proj 2 (fun _ : Fin 3 => GlobalDiffeomorphismVectorL2 period hPeriod) j).comp
    (WithLp.sndL 2 Real _ _)
  (WithLp.prodContinuousLinearEquiv 2 Real _ _).symm.toContinuousLinearMap.comp
    ((0 : DiffeomorphismL2Ambient period hPeriod →L[Real]
      PiLp 2 fun _ : Sector => GlobalGeneralMetricTensorFrameL2 period hPeriod).prod
      ((PiLp.continuousLinearEquiv 2 Real _).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.pi (fun k : Fin 3 => if k = i then read else 0))))

theorem diffeomorphismTripletAmbient_metric (i j : Fin 3)
    (x : DiffeomorphismL2Ambient period hPeriod) :
    WithLp.fst (diffeomorphismTripletAmbient period hPeriod i j x) = 0 := rfl

theorem diffeomorphismTripletAmbient_coordinate (i j k : Fin 3)
    (x : DiffeomorphismL2Ambient period hPeriod) :
    WithLp.snd (diffeomorphismTripletAmbient period hPeriod i j x) k =
      if k = i then WithLp.snd x j else 0 := by
  change (if k = i then _ else (0 : DiffeomorphismL2Ambient period hPeriod →L[Real] _)) x = _
  split_ifs <;> rfl

theorem diffeomorphismTripletAmbient_smooth
    (metric : SmoothGeneralLorentzMetric period hPeriod) (i j : Fin 3)
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    diffeomorphismTripletAmbient period hPeriod i j
      (diffeomorphismL2Coordinates period hPeriod metric field) =
      diffeomorphismL2Coordinates period hPeriod metric
        (diffeomorphismTripletTransfer period hPeriod i j field) := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · apply PiLp.ext
    intro sector
    exact (globalGeneralMetricTensorFrameL2LinearMap period hPeriod).map_zero.symm
  · apply PiLp.ext
    intro k
    refine (diffeomorphismTripletAmbient_coordinate period hPeriod i j k
      (diffeomorphismL2Coordinates period hPeriod metric field)).trans ?_
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      first | rfl | exact (globalNormalizedVectorFrameL2LinearMap period hPeriod metric).map_zero.symm

theorem diffeomorphismTripletAmbient_mem
    (metric : SmoothGeneralLorentzMetric period hPeriod) (i j : Fin 3)
    (x : DiffeomorphismL2 period hPeriod metric) :
    diffeomorphismTripletAmbient period hPeriod i j x ∈
      diffeomorphismL2Space period hPeriod metric := by
  have h : Set.MapsTo (diffeomorphismTripletAmbient period hPeriod i j)
      ((diffeomorphismL2Coordinates period hPeriod metric).range : Set _)
      ((diffeomorphismL2Coordinates period hPeriod metric).range : Set _) := by
    rintro _ ⟨field, rfl⟩
    exact ⟨diffeomorphismTripletTransfer period hPeriod i j field,
      (diffeomorphismTripletAmbient_smooth period hPeriod metric i j field).symm⟩
  exact h.closure (diffeomorphismTripletAmbient period hPeriod i j).continuous x.property

def diffeomorphismTripletL2 (metric : SmoothGeneralLorentzMetric period hPeriod) (i j : Fin 3) :
    DiffeomorphismL2 period hPeriod metric →L[Real] DiffeomorphismL2 period hPeriod metric :=
  ((diffeomorphismTripletAmbient period hPeriod i j).comp
    (diffeomorphismL2Space period hPeriod metric).subtypeL).codRestrict
      (diffeomorphismL2Space period hPeriod metric)
      (diffeomorphismTripletAmbient_mem period hPeriod metric i j)

theorem diffeomorphismTripletL2_smooth
    (metric : SmoothGeneralLorentzMetric period hPeriod) (i j : Fin 3)
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    diffeomorphismTripletL2 period hPeriod metric i j
      (diffeomorphismL2Smooth period hPeriod metric field) =
      diffeomorphismL2Smooth period hPeriod metric
        (diffeomorphismTripletTransfer period hPeriod i j field) :=
  Subtype.ext (diffeomorphismTripletAmbient_smooth period hPeriod metric i j field)

theorem diffeomorphismTripletL2_comp
    (metric : SmoothGeneralLorentzMetric period hPeriod) (i j k l : Fin 3) :
    (diffeomorphismTripletL2 period hPeriod metric i j).comp
      (diffeomorphismTripletL2 period hPeriod metric k l) =
      if j = k then diffeomorphismTripletL2 period hPeriod metric i l else 0 := by
  apply ContinuousLinearMap.ext
  intro x
  split_ifs with h
  · apply Subtype.ext
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · rfl
    · apply PiLp.ext
      intro a
      change WithLp.snd (diffeomorphismTripletAmbient period hPeriod i j
        (diffeomorphismTripletAmbient period hPeriod k l x)) a =
        WithLp.snd (diffeomorphismTripletAmbient period hPeriod i l x) a
      simp only [diffeomorphismTripletAmbient_coordinate, h, if_true]
  ·
    apply Subtype.ext
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · rfl
    · apply PiLp.ext
      intro a
      change WithLp.snd (diffeomorphismTripletAmbient period hPeriod i j
        (diffeomorphismTripletAmbient period hPeriod k l x)) a = 0
      simp only [diffeomorphismTripletAmbient_coordinate, h, if_false]
      split_ifs <;> rfl

end
end JanusFormal.P0EFTJanusProgramPT12DiffeomorphismL2Triplet4D
