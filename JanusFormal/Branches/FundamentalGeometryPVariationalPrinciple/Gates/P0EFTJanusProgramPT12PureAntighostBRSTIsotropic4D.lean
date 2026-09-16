import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D

/-! # Pure-antighost isotropy of the diagonal BRST Hessian -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12PureAntighostBRSTIsotropic4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPCandidateADiagonalDiffeomorphismKineticAdjointBridge4D
open P0EFTJanusProgramPGlobalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- The triplet with only its antighost coordinate populated. -/
def pureAntighostNonminimal
    (antighost : GlobalDiffeomorphismAntighostField period hPeriod) :
    GlobalDiffeomorphismNonminimalFields period hPeriod where
  ghost := zeroGlobalDiffeomorphismGhostField period hPeriod
  antighost := antighost
  nakanishiLautrup :=
    zeroGlobalDiffeomorphismNakanishiLautrupField period hPeriod

private theorem zeroNakanishiLautrup_field :
    (zeroGlobalDiffeomorphismNakanishiLautrupField period hPeriod).field = 0 := by
  apply ContMDiffSection.ext
  intro point
  rfl

private theorem zeroGhost_eq_zero :
    zeroGlobalDiffeomorphismGhostField period hPeriod = 0 := by
  apply GlobalDiffeomorphismGhostField.ext
  apply ContMDiffSection.ext
  intro point
  rfl

private theorem monoPureAntighostHessian_self
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (antighost : GlobalDiffeomorphismAntighostField period hPeriod) :
    globalDiffeomorphismOffShellHessian period hPeriod metric
        (globalDiffeomorphismOffShellSmoothEmbedding period hPeriod metric
          { metricPerturbation := 0
            nonminimal := pureAntighostNonminimal period hPeriod antighost })
        (globalDiffeomorphismOffShellSmoothEmbedding period hPeriod metric
          { metricPerturbation := 0
            nonminimal := pureAntighostNonminimal period hPeriod antighost }) = 0 := by
  rw [globalDiffeomorphismOffShellHessian_apply]
  simp only [globalDiffeomorphismOffShellDeDonderProjection_smooth,
    globalDiffeomorphismOffShellBProjection_smooth,
    globalDiffeomorphismOffShellBFlatProjection_smooth,
    globalDiffeomorphismOffShellAntighostProjection_smooth,
    globalDiffeomorphismOffShellFPProjection_smooth]
  simp only [pureAntighostNonminimal, zeroNakanishiLautrup_field,
    zeroGhost_eq_zero, map_zero, inner_zero_left, inner_zero_right,
    mul_zero, add_zero, sub_zero]

/-- The quadratic diagonal BRST Hessian vanishes on each pure-antighost
smooth-core direction. This is an isotropy statement, not a kernel claim. -/
theorem pureAntighost_diagonalBRSTHessian_self
    (couplings : GlobalCandidateAActionCouplings)
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (antighost : GlobalDiffeomorphismAntighostField period hPeriod) :
    globalCandidateADiagonalDiffeomorphismOffShellHessian period hPeriod
        couplings metric
        (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding
          period hPeriod metric
          { metricPerturbation := 0
            nonminimal := pureAntighostNonminimal period hPeriod antighost })
        (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding
          period hPeriod metric
          { metricPerturbation := 0
            nonminimal := pureAntighostNonminimal period hPeriod antighost }) = 0 := by
  rw [globalCandidateADiagonalDiffeomorphismOffShellHessian_apply]
  simp only [globalCandidateADiagonalDiffeomorphismOffShellPlusProjection_smooth,
    globalCandidateADiagonalDiffeomorphismOffShellMinusProjection_smooth]
  change candidateAPlusEinsteinKineticWeight couplings *
      globalDiffeomorphismOffShellHessian period hPeriod (metric .plus)
        (globalDiffeomorphismOffShellSmoothEmbedding period hPeriod (metric .plus)
          { metricPerturbation := 0
            nonminimal := pureAntighostNonminimal period hPeriod antighost })
        (globalDiffeomorphismOffShellSmoothEmbedding period hPeriod (metric .plus)
          { metricPerturbation := 0
            nonminimal := pureAntighostNonminimal period hPeriod antighost }) +
      candidateAMinusEinsteinKineticWeight couplings *
      globalDiffeomorphismOffShellHessian period hPeriod (metric .minus)
        (globalDiffeomorphismOffShellSmoothEmbedding period hPeriod (metric .minus)
          { metricPerturbation := 0
            nonminimal := pureAntighostNonminimal period hPeriod antighost })
        (globalDiffeomorphismOffShellSmoothEmbedding period hPeriod (metric .minus)
          { metricPerturbation := 0
            nonminimal := pureAntighostNonminimal period hPeriod antighost }) = 0
  rw [monoPureAntighostHessian_self, monoPureAntighostHessian_self]
  ring

end
end P0EFTJanusProgramPT12PureAntighostBRSTIsotropic4D
end JanusFormal
