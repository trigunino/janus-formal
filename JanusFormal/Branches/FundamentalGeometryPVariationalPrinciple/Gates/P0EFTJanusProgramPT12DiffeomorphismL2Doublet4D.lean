import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismL2Triplet4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismL2BRST4D

/-! The nonminimal BRST doublet is contractible by an actual bounded L² map.
The homotopy identity holds for the original BRST differential on its domain. -/
namespace JanusFormal.P0EFTJanusProgramPT12DiffeomorphismL2Doublet4D
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 600000
noncomputable section
open Set
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPCandidateADiagonalDiffeomorphismKineticAdjointBridge4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPT12DiffeomorphismL2Core4D
open P0EFTJanusProgramPT12DiffeomorphismL2Triplet4D
open P0EFTJanusProgramPT12DiffeomorphismL2BRST4D

variable (period : Real) (hPeriod : period ≠ 0)
variable (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)

def diffeomorphismL2Nonminimal :
    DiffeomorphismL2 period hPeriod (metric .plus) →L[Real]
      DiffeomorphismL2 period hPeriod (metric .plus) :=
  diffeomorphismTripletL2 period hPeriod (metric .plus) 1 2

def diffeomorphismL2Homotopy :
    DiffeomorphismL2 period hPeriod (metric .plus) →L[Real]
      DiffeomorphismL2 period hPeriod (metric .plus) :=
  diffeomorphismTripletL2 period hPeriod (metric .plus) 2 1

def diffeomorphismL2DoubletProjection :
    DiffeomorphismL2 period hPeriod (metric .plus) →L[Real]
      DiffeomorphismL2 period hPeriod (metric .plus) :=
  diffeomorphismTripletL2 period hPeriod (metric .plus) 1 1 +
    diffeomorphismTripletL2 period hPeriod (metric .plus) 2 2

theorem diffeomorphismL2Nonminimal_square_zero :
    (diffeomorphismL2Nonminimal period hPeriod metric).comp
      (diffeomorphismL2Nonminimal period hPeriod metric) = 0 := by
  simp [diffeomorphismL2Nonminimal, diffeomorphismTripletL2_comp]

theorem diffeomorphismL2Homotopy_square_zero :
    (diffeomorphismL2Homotopy period hPeriod metric).comp
      (diffeomorphismL2Homotopy period hPeriod metric) = 0 := by
  simp [diffeomorphismL2Homotopy, diffeomorphismTripletL2_comp]

theorem diffeomorphismL2Doublet_contract :
    (diffeomorphismL2Nonminimal period hPeriod metric).comp
        (diffeomorphismL2Homotopy period hPeriod metric) +
      (diffeomorphismL2Homotopy period hPeriod metric).comp
        (diffeomorphismL2Nonminimal period hPeriod metric) =
      diffeomorphismL2DoubletProjection period hPeriod metric := by
  simp [diffeomorphismL2Nonminimal, diffeomorphismL2Homotopy,
    diffeomorphismL2DoubletProjection, diffeomorphismTripletL2_comp]

theorem diffeomorphismL2DoubletProjection_idempotent :
    (diffeomorphismL2DoubletProjection period hPeriod metric).comp
      (diffeomorphismL2DoubletProjection period hPeriod metric) =
      diffeomorphismL2DoubletProjection period hPeriod metric := by
  simp [diffeomorphismL2DoubletProjection, ContinuousLinearMap.add_comp,
    ContinuousLinearMap.comp_add, diffeomorphismTripletL2_comp]

private theorem smooth_contract
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    diffeomorphismBRSTLinearMap period hPeriod metric
        (diffeomorphismTripletTransfer period hPeriod 2 1 field) +
      diffeomorphismTripletTransfer period hPeriod 2 1
        (diffeomorphismBRSTLinearMap period hPeriod metric field) =
      diffeomorphismTripletTransfer period hPeriod 1 1 field +
        diffeomorphismTripletTransfer period hPeriod 2 2 field := by
  apply GlobalCandidateADiagonalDiffeomorphismBRSTState.ext
  · change globalCandidateADiagonalDiffeomorphismGaugeGeneratorLinearMap
      period hPeriod metric 0 + 0 = 0 + 0
    rw [map_zero]
  · rfl

theorem diffeomorphismL2Homotopy_mem_domain
    (x : (diffeomorphismL2BRST period hPeriod metric).domain) :
    diffeomorphismL2Homotopy period hPeriod metric x ∈
      (diffeomorphismL2BRST period hPeriod metric).domain := by
  obtain ⟨field, hField⟩ := x.property
  change diffeomorphismTripletL2 period hPeriod (metric .plus) 2 1 x ∈ _
  rw [← hField, diffeomorphismTripletL2_smooth]
  exact ⟨diffeomorphismTripletTransfer period hPeriod 2 1 field, rfl⟩

theorem diffeomorphismL2BRST_contract
    (x : (diffeomorphismL2BRST period hPeriod metric).domain) :
    diffeomorphismL2BRST period hPeriod metric
        ⟨diffeomorphismL2Homotopy period hPeriod metric x,
          diffeomorphismL2Homotopy_mem_domain period hPeriod metric x⟩ +
      diffeomorphismL2Homotopy period hPeriod metric
        (diffeomorphismL2BRST period hPeriod metric x) =
      diffeomorphismL2DoubletProjection period hPeriod metric x := by
  rcases x with ⟨x, hX⟩
  obtain ⟨field, rfl⟩ := hX
  have hHom := diffeomorphismTripletL2_smooth period hPeriod (metric .plus) 2 1 field
  have hInput :
      (⟨diffeomorphismL2Homotopy period hPeriod metric
          (diffeomorphismL2Smooth period hPeriod (metric .plus) field),
        diffeomorphismL2Homotopy_mem_domain period hPeriod metric
          ⟨diffeomorphismL2Smooth period hPeriod (metric .plus) field, ⟨field, rfl⟩⟩⟩ :
        (diffeomorphismL2BRST period hPeriod metric).domain) =
      ⟨diffeomorphismL2Smooth period hPeriod (metric .plus)
        (diffeomorphismTripletTransfer period hPeriod 2 1 field),
        ⟨diffeomorphismTripletTransfer period hPeriod 2 1 field, rfl⟩⟩ := Subtype.ext hHom
  rw [hInput, diffeomorphismL2BRST_smooth, diffeomorphismL2BRST_smooth]
  change _ + diffeomorphismTripletL2 period hPeriod (metric .plus) 2 1 _ =
    diffeomorphismTripletL2 period hPeriod (metric .plus) 1 1 _ +
      diffeomorphismTripletL2 period hPeriod (metric .plus) 2 2 _
  rw [diffeomorphismTripletL2_smooth, diffeomorphismTripletL2_smooth,
    diffeomorphismTripletL2_smooth, ← map_add, ← map_add]
  exact congrArg (diffeomorphismL2Smooth period hPeriod (metric .plus))
    (smooth_contract period hPeriod metric field)

/-- The doublet component of every BRST cycle is an actual BRST boundary. -/
theorem diffeomorphismL2BRST_doublet_cycle_exact
    (x : (diffeomorphismL2BRST period hPeriod metric).domain)
    (hCycle : diffeomorphismL2BRST period hPeriod metric x = 0) :
    diffeomorphismL2BRST period hPeriod metric
      ⟨diffeomorphismL2Homotopy period hPeriod metric x,
        diffeomorphismL2Homotopy_mem_domain period hPeriod metric x⟩ =
      diffeomorphismL2DoubletProjection period hPeriod metric x := by
  have h := diffeomorphismL2BRST_contract period hPeriod metric x
  rw [hCycle, map_zero, add_zero] at h
  exact h

end
end JanusFormal.P0EFTJanusProgramPT12DiffeomorphismL2Doublet4D
