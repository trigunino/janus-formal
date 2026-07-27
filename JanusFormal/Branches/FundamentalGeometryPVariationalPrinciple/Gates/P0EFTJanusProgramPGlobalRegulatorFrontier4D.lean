import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianFrontier4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD7CircleHeatRegulatorBridge
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD10ContinuumHeatOperatorNuclear4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCompleteVariationFiniteD10AnomalyRegulatorBridge4D

/-!
# Exact frontier of the common regulator problem

The D7 fixed-sphere-level heat blocks are compact, the physical quarter
determinant exists, and the complete multiplicity-aware D10 heat series is
summable at every positive time.  Its physical PT involution makes the
continuum chiral trace and its finite-cutoff limit vanish, including
multiplicity and statistics signs.  On the complete D10 Hilbert space the heat
operator is moreover the operator-norm sum of a summable family of rank-one
operators, hence compact.

This is not `REGULATOR-GLOBAL-01`: the identification with the full assembled
action Hessian and a common regulator for the remaining nonspectral sectors
still depend on the explicit Program-P/D7/D9/D10 domain-agreement contract.
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
open P0EFTJanusProgramPD10ContinuumHeatRegulator4D
open P0EFTJanusProgramPD10ContinuumHeatOperatorNuclear4D
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

/-- The all-level D10 heat regulator and its continuum PT cancellation are
unconditional on the exact multiplicity-aware mode space. -/
theorem global_regulator_d10_continuum_gate
    (data : ProductThroatSpectralData) :
    Nonempty (ProgramPD10ContinuumHeatRegulatorCertificate4D data) :=
  ⟨programPD10ContinuumHeatRegulatorCertificate4D data⟩

/-- The all-level D10 Gaussian is an actual compact nuclear operator, obtained
as the operator-norm limit of finite-rank spectral truncations. -/
theorem global_regulator_d10_nuclear_operator_gate
    (data : ProductThroatSpectralData) (time : HeatTime) :
    Nonempty (ProgramPD10HeatNuclearCertificate4D data time) :=
  ⟨programPD10HeatNuclearCertificate4D data time⟩

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
