import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismSignedBRSTRealization4D

/-! A genuine diagonal BRST degeneracy: equal metrics and opposite action
weights annihilate every pure shared ghost. This is a conditional statement
about the actual graph, not an assertion that the selected background has
these parameters. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12DiagonalGhostCancellation4D
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped InnerProductSpace Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPCandidateADiagonalDiffeomorphismKineticAdjointBridge4D
open P0EFTJanusProgramPGlobalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D

attribute [local instance]
  globalDiffeomorphismOffShellGraphNormedSpace
  globalDiffeomorphismOffShellGraphModule
  globalDiffeomorphismOffShellGraphInnerProductSpace
  globalDiffeomorphismOffShellGraphCompleteSpace
  diagonalGraphNormedSpace diagonalGraphModule diagonalGraphInnerProductSpace
  diagonalGraphCompleteSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

def diagonalPureGhost : GlobalDiffeomorphismGhostField period hPeriod →ₗ[Real]
    GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod where
  toFun ghost := ⟨0, ⟨ghost, ⟨0⟩, ⟨0⟩⟩⟩
  map_add' _ _ := by
    apply GlobalCandidateADiagonalDiffeomorphismBRSTState.ext
    · exact (zero_add _).symm
    · apply GlobalDiffeomorphismNonminimalFields.ext
      · rfl
      · exact (zero_add _).symm
      · exact (zero_add _).symm
  map_smul' scalar _ := by
    apply GlobalCandidateADiagonalDiffeomorphismBRSTState.ext
    · exact (smul_zero scalar).symm
    · apply GlobalDiffeomorphismNonminimalFields.ext
      · rfl
      · exact (smul_zero scalar).symm
      · exact (smul_zero scalar).symm

theorem diagonalPureGhost_injective :
    Function.Injective (diagonalPureGhost period hPeriod) := by
  intro first second hEqual
  exact congrArg (fun state => state.nonminimal.ghost) hEqual

/-- Both metric projections see the same ghost, and the test antighost
is shared too. Thus the two off-shell pairings agree on this column. -/
theorem diagonalPureGhost_sector_pairings_eq
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (hMetric : metric .plus = metric .minus)
    (ghost : GlobalDiffeomorphismGhostField period hPeriod)
    (test : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    globalDiffeomorphismOffShellHessian period hPeriod (metric .plus)
      (globalDiffeomorphismOffShellSmoothEmbedding period hPeriod (metric .plus)
        (globalCandidateADiagonalDiffeomorphismSectorStateLinearMap period hPeriod .plus
          (diagonalPureGhost period hPeriod ghost)))
      (globalDiffeomorphismOffShellSmoothEmbedding period hPeriod (metric .plus)
        (globalCandidateADiagonalDiffeomorphismSectorStateLinearMap period hPeriod .plus test)) =
    globalDiffeomorphismOffShellHessian period hPeriod (metric .minus)
      (globalDiffeomorphismOffShellSmoothEmbedding period hPeriod (metric .minus)
        (globalCandidateADiagonalDiffeomorphismSectorStateLinearMap period hPeriod .minus
          (diagonalPureGhost period hPeriod ghost)))
      (globalDiffeomorphismOffShellSmoothEmbedding period hPeriod (metric .minus)
        (globalCandidateADiagonalDiffeomorphismSectorStateLinearMap period hPeriod .minus test)) := by
  simp [globalDiffeomorphismOffShellHessian_apply,
    globalCandidateADiagonalDiffeomorphismSectorStateLinearMap,
    diagonalPureGhost, hMetric]

theorem diagonalPureGhost_hessian_zero
    (couplings : GlobalCandidateAActionCouplings)
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (hMetric : metric .plus = metric .minus)
    (hWeights : candidateAPlusEinsteinKineticWeight couplings +
      candidateAMinusEinsteinKineticWeight couplings = 0)
    (ghost : GlobalDiffeomorphismGhostField period hPeriod)
    (test : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    globalCandidateADiagonalDiffeomorphismOffShellHessian period hPeriod couplings metric
      (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding period hPeriod metric
        (diagonalPureGhost period hPeriod ghost))
      (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding period hPeriod metric test) = 0 := by
  rw [globalCandidateADiagonalDiffeomorphismOffShellHessian_apply]
  simp only [globalCandidateADiagonalDiffeomorphismOffShellPlusProjection_smooth,
    globalCandidateADiagonalDiffeomorphismOffShellMinusProjection_smooth]
  rw [diagonalPureGhost_sector_pairings_eq period hPeriod metric hMetric,
    ← add_mul, hWeights, zero_mul]

/-- Density extends the vanishing column from smooth tests to the completed
graph, so this is an actual Riesz kernel statement. -/
theorem diagonalPureGhost_riesz_zero
    (couplings : GlobalCandidateAActionCouplings)
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (hMetric : metric .plus = metric .minus)
    (hWeights : candidateAPlusEinsteinKineticWeight couplings +
      candidateAMinusEinsteinKineticWeight couplings = 0)
    (ghost : GlobalDiffeomorphismGhostField period hPeriod) :
    globalCandidateADiagonalDiffeomorphismOffShellRieszOperator period hPeriod couplings metric
      (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding period hPeriod metric
        (diagonalPureGhost period hPeriod ghost)) = 0 := by
  let state := globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding period hPeriod metric
    (diagonalPureGhost period hPeriod ghost)
  have hRow : (globalCandidateADiagonalDiffeomorphismOffShellHessian
      period hPeriod couplings metric state : _ → Real) = fun _ => 0 := by
    apply (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding_denseRange
      period hPeriod metric).equalizer
      (globalCandidateADiagonalDiffeomorphismOffShellHessian
        period hPeriod couplings metric state).continuous continuous_const
    funext test
    exact diagonalPureGhost_hessian_zero period hPeriod couplings metric hMetric hWeights ghost test
  apply ext_inner_right Real
  intro test
  rw [inner_zero_left, globalCandidateADiagonalDiffeomorphismOffShellRieszOperator_pairing]
  exact congrFun hRow test

end
end P0EFTJanusProgramPT12DiagonalGhostCancellation4D
end JanusFormal
