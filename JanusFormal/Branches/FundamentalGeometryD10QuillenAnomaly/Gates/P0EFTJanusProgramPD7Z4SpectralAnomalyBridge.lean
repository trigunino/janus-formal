import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD7CircleHeatRegulatorBridge
import JanusFormal.Branches.FundamentalGeometryD10QuillenAnomaly.Gates.P0EFTJanusD2ModeFamilyInflowBridge

/-!
# Program P / D7 / D10 physical-Z4 bridge

This gate combines three results that refer to the same two normal-root
sectors: compact fixed-level heat blocks, the convergent D7 spectral
determinant, and additive mode/inflow cancellation.

It does not construct a smooth Fredholm family, a determinant line, a
Bismut--Freed connection, eta holonomy, or a Quillen partition section.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD7Z4SpectralAnomalyBridge

set_option autoImplicit false

noncomputable section

open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusRenormalizedSpectralDeterminant
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusQuarterDeterminantConvergence
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPD7CircleHeatRegulatorBridge
open P0EFTJanusAnomalyTransgressionInflow
open P0EFTJanusD2ModeFamilyInflowBridge

/-- The locally subtracted cutoff converges for either physical root. -/
theorem program_p_d7_z4_cutoff_converges
    (data : ProductThroatSpectralData) (choice : NormalRootChoice) :
    Filter.Tendsto
      (fun N => finiteCutoffLogDeterminant data N (rootHolonomy choice) -
        quarterLocalCounterterm data N)
      Filter.atTop
      (nhds ((z4RenormalizedDeterminant data).renormalizedLog choice)) := by
  exact (z4RenormalizedDeterminant data).cutoffConverges choice

/-- PT-related roots have the same renormalized logarithmic determinant in
the common quarter-root subtraction scheme. -/
theorem program_p_d7_pt_renormalized_logs_agree
    (data : ProductThroatSpectralData) :
    (z4RenormalizedDeterminant data).renormalizedLog
        NormalRootChoice.positiveQuarter =
      (z4RenormalizedDeterminant data).renormalizedLog
        NormalRootChoice.negativeQuarter := by
  rfl

/-- The D10 opposite-inflow representative cancels for every separated mode. -/
theorem program_p_d7_mode_inflow_cancels (mode : ProductDiracMode) :
    anomalyCancelled (modeRelativeAnomaly mode) := by
  exact d2_mode_opposite_inflow_cancels mode

/-- A scoped certificate for the physical `Z4` spectral/anomaly data already
proved by Program P, D7, and D10. -/
structure PhysicalZ4SpectralAnomalyCertificate
    (data : ProductThroatSpectralData) where
  compactLevelBlocks :
    ∀ time : HeatTime, ∀ level : ℕ, ∀ choice : NormalRootChoice,
      IsCompactOperator
        (d7SeparatedLevelHeatOperator data time level choice)
  renormalizedDeterminant :
    Nonempty (Z4RenormalizedDeterminantCertificate data)
  cutoffConverges : ∀ choice : NormalRootChoice,
    Filter.Tendsto
      (fun N => finiteCutoffLogDeterminant data N (rootHolonomy choice) -
        quarterLocalCounterterm data N)
      Filter.atTop
      (nhds ((z4RenormalizedDeterminant data).renormalizedLog choice))
  ptRenormalizedLogsAgree :
    (z4RenormalizedDeterminant data).renormalizedLog
        NormalRootChoice.positiveQuarter =
      (z4RenormalizedDeterminant data).renormalizedLog
        NormalRootChoice.negativeQuarter
  ptModePhasesCancel : ∀ mode : ProductDiracMode,
    modeAnomalyPhase mode + modeAnomalyPhase (ptMode mode) = 0
  oppositeInflowsCancel : ∀ mode : ProductDiracMode,
    anomalyCancelled (modeRelativeAnomaly mode)

noncomputable def physicalZ4SpectralAnomalyCertificate
    (data : ProductThroatSpectralData) :
    PhysicalZ4SpectralAnomalyCertificate data where
  compactLevelBlocks :=
    (circle_compactness_and_z4_determinant_close_physical_regulator data).1
  renormalizedDeterminant :=
    (circle_compactness_and_z4_determinant_close_physical_regulator data).2
  cutoffConverges := program_p_d7_z4_cutoff_converges data
  ptRenormalizedLogsAgree := program_p_d7_pt_renormalized_logs_agree data
  ptModePhasesCancel := pt_mode_anomaly_phases_cancel
  oppositeInflowsCancel := program_p_d7_mode_inflow_cancels

end

end P0EFTJanusProgramPD7Z4SpectralAnomalyBridge
end JanusFormal
