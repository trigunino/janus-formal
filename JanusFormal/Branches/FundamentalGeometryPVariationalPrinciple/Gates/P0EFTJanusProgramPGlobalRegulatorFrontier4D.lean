import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianFrontier4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD7CircleHeatRegulatorBridge
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCompleteVariationFiniteD10AnomalyRegulatorBridge4D

/-!
# Exact frontier of the common regulator problem

The D7 fixed-sphere-level heat blocks are compact, the physical quarter
determinant exists, and every finite D10 PT pair cancels at one common heat
time, including multiplicity and statistics signs.

This is not `REGULATOR-GLOBAL-01`: the identification with the full assembled
action Hessian and the continuum cutoff limit still depend on the explicit
Program-P/D7/D9/D10 domain-agreement contract.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalRegulatorFrontier4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusCompleteVariationFiniteD10AnomalyRegulatorBridge4D
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusFiniteModeCommonPhysicalGhostHeatRegulator4D
open P0EFTJanusFiniteModeHeatKernelAnomalyRegulator
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusProgramPD7CircleHeatRegulatorBridge
open P0EFTJanusQuarterDeterminantConvergence

/-- Unconditional operator-level and finite-mode regulator frontier. -/
theorem global_regulator_frontier_gate
    (data : ProductThroatSpectralData) :
    (∀ time : HeatTime, ∀ level : Nat, ∀ choice : NormalRootChoice,
      IsCompactOperator
        (d7SeparatedLevelHeatOperator data time level choice)) ∧
      Nonempty (Z4RenormalizedDeterminantCertificate data) ∧
      ∀ (chirality : RootChiralityAssignment)
        (sphereCutoff circleCutoff multiplicity : Nat)
        (statistics : FieldStatistics)
        (regulatorTime : RegulatorTime),
        signedPairedChiralTrace regulatorTime
            (⟨multiplicity, statistics,
              d10RegulatorSpectrum data chirality sphereCutoff circleCutoff⟩ :
              WeightedSector
                (TruncatedD10Mode data sphereCutoff circleCutoff)) = 0 := by
  rcases
      circle_compactness_and_z4_determinant_close_physical_regulator data with
    ⟨hCompact, hDeterminant⟩
  exact
    ⟨hCompact, hDeterminant,
      fun chirality sphereCutoff circleCutoff multiplicity statistics
          regulatorTime =>
        truncated_d10_signed_chiral_trace_cancels
          data chirality sphereCutoff circleCutoff multiplicity statistics
          regulatorTime⟩

/-- Once the already-typed domain agreement is supplied, the finite D10
regulator is literally the action Hessian on the corresponding complete
variations. -/
theorem global_regulator_conditional_hessian_bridge
    (period : Real) (hPeriod : period ≠ 0)
    {Spinor : Type*}
    (domain : ProgramPCommonGeometricDomain4D period hPeriod)
    (agreement :
      RemainingProgramPD7D9D10DomainAgreement4D
        period hPeriod Spinor domain)
    (sphereCutoff circleCutoff multiplicity : Nat)
    (statistics : FieldStatistics)
    (regulatorTime : RegulatorTime) :
    (∀ mode : TruncatedD10Mode domain.d7d10SpectralData
        sphereCutoff circleCutoff,
      agreement.actionHessian agreement.baseConfiguration
          (agreement.modeTangent (truncatedProgramPD10Mode4D mode))
          (agreement.modeTangent (truncatedProgramPD10Mode4D mode)) =
        (completeVariationD10WeightedSector period hPeriod domain sphereCutoff
          circleCutoff multiplicity statistics).spectrum.eigenvalueSq mode) ∧
      signedPairedChiralTrace regulatorTime
          (completeVariationD10WeightedSector period hPeriod domain sphereCutoff
            circleCutoff multiplicity statistics) = 0 :=
  completeVariation_hessian_finiteD10_signed_chiral_trace_cancels
    period hPeriod domain agreement sphereCutoff circleCutoff multiplicity
    statistics regulatorTime

end
end P0EFTJanusProgramPGlobalRegulatorFrontier4D
end JanusFormal
