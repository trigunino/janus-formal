import Mathlib.Analysis.InnerProductSpace.LinearPMap
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismL2Core4D

/-! The actual diagonal BRST differential on its dense, invariant L² smooth
domain. Nilpotency is transported from the original fields. This is the BRST
differential, not a claim of self-adjointness for its gauge-fixed Hessian. -/
namespace JanusFormal.P0EFTJanusProgramPT12DiffeomorphismL2BRST4D
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

variable (period : Real) (hPeriod : period ≠ 0)
variable (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)

def diffeomorphismBRSTLinearMap :
    GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod →ₗ[Real]
      GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod where
  toFun := globalCandidateADiagonalDiffeomorphismBRST period hPeriod metric
  map_add' first second := by
    apply GlobalCandidateADiagonalDiffeomorphismBRSTState.ext
    · exact (globalCandidateADiagonalDiffeomorphismGaugeGeneratorLinearMap
        period hPeriod metric).map_add _ _
    · apply GlobalDiffeomorphismNonminimalFields.ext
      · change (0 : GlobalDiffeomorphismGhostField period hPeriod) = 0 + 0
        exact (add_zero _).symm
      · rfl
      · change (0 : GlobalDiffeomorphismNakanishiLautrupField period hPeriod) = 0 + 0
        exact (add_zero _).symm
  map_smul' scalar field := by
    apply GlobalCandidateADiagonalDiffeomorphismBRSTState.ext
    · exact (globalCandidateADiagonalDiffeomorphismGaugeGeneratorLinearMap
        period hPeriod metric).map_smul scalar _
    · apply GlobalDiffeomorphismNonminimalFields.ext
      · change (0 : GlobalDiffeomorphismGhostField period hPeriod) = scalar • 0
        exact (smul_zero scalar).symm
      · rfl
      · change (0 : GlobalDiffeomorphismNakanishiLautrupField period hPeriod) = scalar • 0
        exact (smul_zero scalar).symm

theorem diffeomorphismBRSTLinearMap_square_zero
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    diffeomorphismBRSTLinearMap period hPeriod metric
      (diffeomorphismBRSTLinearMap period hPeriod metric field) = 0 :=
  globalCandidateADiagonalDiffeomorphismBRST_square_zero period hPeriod metric field

private def smoothEquivDomain :
    GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod ≃ₗ[Real]
      (diffeomorphismL2Smooth period hPeriod (metric .plus)).range :=
  LinearEquiv.ofInjective (diffeomorphismL2Smooth period hPeriod (metric .plus))
    (diffeomorphismL2Smooth_injective period hPeriod (metric .plus))

def diffeomorphismL2BRSTCore :
    (diffeomorphismL2Smooth period hPeriod (metric .plus)).range →ₗ[Real]
      (diffeomorphismL2Smooth period hPeriod (metric .plus)).range :=
  (smoothEquivDomain period hPeriod metric).toLinearMap.comp
    ((diffeomorphismBRSTLinearMap period hPeriod metric).comp
      (smoothEquivDomain period hPeriod metric).symm.toLinearMap)

theorem diffeomorphismL2BRSTCore_square_zero
    (x : (diffeomorphismL2Smooth period hPeriod (metric .plus)).range) :
    diffeomorphismL2BRSTCore period hPeriod metric
      (diffeomorphismL2BRSTCore period hPeriod metric x) = 0 := by
  simp only [diffeomorphismL2BRSTCore, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, diffeomorphismBRSTLinearMap_square_zero, map_zero]

def diffeomorphismL2BRST :
    DiffeomorphismL2 period hPeriod (metric .plus) →ₗ.[Real]
      DiffeomorphismL2 period hPeriod (metric .plus) where
  domain := (diffeomorphismL2Smooth period hPeriod (metric .plus)).range
  toFun := ((diffeomorphismL2Smooth period hPeriod (metric .plus)).range.subtype).comp
    (diffeomorphismL2BRSTCore period hPeriod metric)

theorem diffeomorphismL2BRST_denseDomain :
    Dense ((diffeomorphismL2BRST period hPeriod metric).domain :
      Set (DiffeomorphismL2 period hPeriod (metric .plus))) :=
  diffeomorphismL2Smooth_denseRange period hPeriod (metric .plus)

theorem diffeomorphismL2BRST_smooth
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    diffeomorphismL2BRST period hPeriod metric
      ⟨diffeomorphismL2Smooth period hPeriod (metric .plus) field, ⟨field, rfl⟩⟩ =
      diffeomorphismL2Smooth period hPeriod (metric .plus)
        (globalCandidateADiagonalDiffeomorphismBRST period hPeriod metric field) := by
  change ((smoothEquivDomain period hPeriod metric)
    (diffeomorphismBRSTLinearMap period hPeriod metric
      ((smoothEquivDomain period hPeriod metric).symm
        ((smoothEquivDomain period hPeriod metric) field))) :
      DiffeomorphismL2 period hPeriod (metric .plus)) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

theorem diffeomorphismL2BRST_apply_mem
    (x : (diffeomorphismL2BRST period hPeriod metric).domain) :
    diffeomorphismL2BRST period hPeriod metric x ∈
      (diffeomorphismL2BRST period hPeriod metric).domain :=
  (diffeomorphismL2BRSTCore period hPeriod metric x).property

theorem diffeomorphismL2BRST_square_zero
    (x : (diffeomorphismL2BRST period hPeriod metric).domain) :
    diffeomorphismL2BRST period hPeriod metric
      ⟨diffeomorphismL2BRST period hPeriod metric x,
        diffeomorphismL2BRST_apply_mem period hPeriod metric x⟩ = 0 :=
  congrArg Subtype.val (diffeomorphismL2BRSTCore_square_zero period hPeriod metric x)

end
end JanusFormal.P0EFTJanusProgramPT12DiffeomorphismL2BRST4D
