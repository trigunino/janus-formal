import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismL2Core4D

/-! Continuous forgetful map from the existing differential graph to the
zeroth-order L² completion. Injectivity of this completed map is not assumed. -/
namespace JanusFormal.P0EFTJanusProgramPT12DiffeomorphismGraphToL24D
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 600000
noncomputable section
open Set
open scoped InnerProductSpace
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphCore4D
open P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphPairing4D
open P0EFTJanusProgramPGlobalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPT12DiffeomorphismL2Core4D

attribute [local instance]
  globalDiffeomorphismOffShellGraphNormedSpace
  globalDiffeomorphismOffShellGraphModule
  globalDiffeomorphismOffShellGraphInnerProductSpace
  globalDiffeomorphismOffShellGraphCompleteSpace
  diagonalGraphNormedSpace diagonalGraphModule diagonalGraphInnerProductSpace
  diagonalGraphCompleteSpace

variable (period : Real) (hPeriod : period ≠ 0)
variable (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)

private def sectorGraphProjection (sector : Sector) :
    GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period hPeriod metric →L[Real]
      GlobalDiffeomorphismOffShellGraphHilbert period hPeriod (metric sector) :=
  match sector with
  | .plus => globalCandidateADiagonalDiffeomorphismOffShellPlusProjection period hPeriod metric
  | .minus => globalCandidateADiagonalDiffeomorphismOffShellMinusProjection period hPeriod metric

private def metricReadout (sector : Sector) :
    GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period hPeriod metric →L[Real]
      GlobalGeneralMetricTensorFrameL2 period hPeriod :=
  (WithLp.fstL 2 Real _ _).comp
    ((globalGeneralMetricDeDonderGraphSubmodule period hPeriod (metric sector)).subtypeL.comp
      ((globalGeneralMetricDeDonderPairingBaseProjection period hPeriod (metric sector)).comp
        ((globalDiffeomorphismOffShellMetricProjection period hPeriod (metric sector)).comp
          (sectorGraphProjection period hPeriod metric sector))))

private def tripletReadout (index : Fin 3) :
    GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period hPeriod metric →L[Real]
      GlobalDiffeomorphismVectorL2 period hPeriod :=
  (![globalDiffeomorphismOffShellGhostProjection period hPeriod (metric .plus),
     globalDiffeomorphismOffShellAntighostProjection period hPeriod (metric .plus),
     globalDiffeomorphismOffShellBProjection period hPeriod (metric .plus)] index).comp
    (globalCandidateADiagonalDiffeomorphismOffShellPlusProjection period hPeriod metric)

def diffeomorphismGraphL2Readout :
    GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period hPeriod metric →L[Real]
      DiffeomorphismL2Ambient period hPeriod :=
  (WithLp.prodContinuousLinearEquiv 2 Real _ _).symm.toContinuousLinearMap.comp
    (((PiLp.continuousLinearEquiv 2 Real _).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi (metricReadout period hPeriod metric))).prod
     ((PiLp.continuousLinearEquiv 2 Real _).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi (tripletReadout period hPeriod metric))))

theorem diffeomorphismGraphL2Readout_smooth
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    diffeomorphismGraphL2Readout period hPeriod metric
      (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding period hPeriod metric field) =
      diffeomorphismL2Coordinates period hPeriod (metric .plus) field := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · apply PiLp.ext
    intro sector
    cases sector <;> rfl
  · apply PiLp.ext
    intro index
    fin_cases index <;> rfl

theorem diffeomorphismGraphL2Readout_mem
    (x : GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period hPeriod metric) :
    diffeomorphismGraphL2Readout period hPeriod metric x ∈
      diffeomorphismL2Space period hPeriod (metric .plus) := by
  have hClosed := ((diffeomorphismL2Coordinates period hPeriod (metric .plus)).range.isClosed_topologicalClosure).preimage
      (diffeomorphismGraphL2Readout period hPeriod metric).continuous
  have hSubset : Set.range
      (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding period hPeriod metric) ⊆
      (diffeomorphismGraphL2Readout period hPeriod metric) ⁻¹'
        (diffeomorphismL2Space period hPeriod (metric .plus) : Set _) := by
    rintro _ ⟨field, rfl⟩
    change diffeomorphismGraphL2Readout period hPeriod metric _ ∈
      diffeomorphismL2Space period hPeriod (metric .plus)
    rw [diffeomorphismGraphL2Readout_smooth]
    exact Submodule.le_topologicalClosure _ ⟨field, rfl⟩
  have h := closure_minimal hSubset hClosed
  exact h (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding_denseRange
    period hPeriod metric x)

def diffeomorphismGraphToL2 :
    GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert period hPeriod metric →L[Real]
      DiffeomorphismL2 period hPeriod (metric .plus) :=
  (diffeomorphismGraphL2Readout period hPeriod metric).codRestrict
    (diffeomorphismL2Space period hPeriod (metric .plus))
    (diffeomorphismGraphL2Readout_mem period hPeriod metric)

theorem diffeomorphismGraphToL2_smooth
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    diffeomorphismGraphToL2 period hPeriod metric
      (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding period hPeriod metric field) =
      diffeomorphismL2Smooth period hPeriod (metric .plus) field :=
  Subtype.ext (diffeomorphismGraphL2Readout_smooth period hPeriod metric field)

theorem diffeomorphismGraphToL2_denseRange :
    DenseRange (diffeomorphismGraphToL2 period hPeriod metric) := by
  apply (diffeomorphismL2Smooth_denseRange period hPeriod (metric .plus)).mono
  rintro _ ⟨field, rfl⟩
  exact ⟨globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding period hPeriod metric field,
    diffeomorphismGraphToL2_smooth period hPeriod metric field⟩

end
end JanusFormal.P0EFTJanusProgramPT12DiffeomorphismGraphToL24D
