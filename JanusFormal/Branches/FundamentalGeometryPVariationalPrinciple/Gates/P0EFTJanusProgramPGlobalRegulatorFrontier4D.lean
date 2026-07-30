import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianFrontier4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD7CircleHeatRegulatorBridge
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD10ContinuumHeatOperatorNuclear4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD10AgreementHeatRegulatorBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCompleteVariationFiniteD10AnomalyRegulatorBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPhysicalLLTemporalGhostHeatRegulator4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusD9GaugeGhostContinuumHeatRegulator4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSpinCMatterContinuumHeatRegulator4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPLL2EllipticNuclearHeatRegulator4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalReferenceNuclearRegulator4D

/-!
# Exact frontier of the common regulator problem

The D7 fixed-sphere-level heat blocks are compact, the physical quarter
determinant exists, and the complete multiplicity-aware D10 heat series is
summable at every positive time.  Its physical PT involution makes the
continuum chiral trace and its finite-cutoff limit vanish, including
multiplicity and statistics signs.  On the complete D10 Hilbert space the heat
operator is moreover the operator-norm sum of a summable family of rank-one
operators, hence compact.

The continuum D10 heat operator is also transported conditionally through the
exact action-Hessian coordinates, with contraction and common-domain
preservation.  The complete bulk, matter, D10 and LL ambient product now has,
at every positive time, one compact injective nuclear reference operator.
The bulk factor covers all finite metric, gauge, ghost and auxiliary slots;
its independent compact lift lands in the homogeneous Dirichlet domain.

This closes `REGULATOR-GLOBAL-01` as a common reference regularization
theorem.  It does not identify that basis-dependent reference operator with
the exponential of the global physical Hessian.  Exact D9 heat remains
conditional on its explicit continuum summability hypothesis, while an exact
LL elliptic heat remains conditional on compact-resolvent spectral data.
Those physical identifications stay in `HESSIAN-GLOBAL-01`.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalRegulatorFrontier4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusCompleteVariationFiniteD10AnomalyRegulatorBridge4D
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusD9GaugeGhostContinuumHeatRegulator4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusFiniteModeCommonPhysicalGhostHeatRegulator4D
open P0EFTJanusFiniteModeHeatKernelAnomalyRegulator
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLHessian4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusProgramPD7CircleHeatRegulatorBridge
open P0EFTJanusProgramPD10AgreementHeatRegulatorBridge4D
open P0EFTJanusProgramPD10ContinuumHeatRegulator4D
open P0EFTJanusProgramPD10ContinuumHeatOperatorNuclear4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalReferenceNuclearRegulator4D
open P0EFTJanusProgramPLL2EllipticNuclearHeatRegulator4D
open P0EFTJanusProgramPPhysicalLLTemporalGhostHeatRegulator4D
open P0EFTJanusProgramPSpinCMatterContinuumHeatRegulator4D
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

/-- Terminal closure of the common reference regulator on the exact completed
bulk, SpinC, D10 and LL ambient product. -/
theorem global_reference_nuclear_regulator_closed_gate
    (period : Real) (hPeriod : period ≠ 0)
    {configuration : GlobalFieldConfiguration period hPeriod}
    (data : GlobalAnalysisData period hPeriod configuration)
    (massSquared : Real) (time : HeatTime) :
    Nonempty
      (ProgramPGlobalReferenceNuclearCertificate4D
        period hPeriod data massSquared time) :=
  programP_global_reference_nuclear_regulator_gate
    period hPeriod data massSquared time

/-- The exact complete matter heat remains available as a physical,
mass-shifted nuclear sub-regulator at the same positive time. -/
theorem global_regulator_spinc_matter_nuclear_gate
    (period : Real) (hPeriod : period ≠ 0)
    (massSquared : Real) (time : HeatTime) :
    Nonempty
      (ProgramPSpinCMatterHeatNuclearCertificate4D
        period hPeriod massSquared time) :=
  programPSpinCMatterContinuumHeat_nuclear_gate
    period hPeriod massSquared time

/-- Exact D9 continuum heat is nuclear once its precise high-energy
summability input is supplied; every finite packet satisfies it
unconditionally. -/
theorem global_regulator_d9_continuum_nuclear_gate
    {ι : Type*} [DecidableEq ι]
    (covector : ι → TangentVector3)
    (time : HeatTime)
    (hSummable : D9GaugeGhostHeatSummability4D covector time) :
    Nonempty
      (D9GaugeGhostHeatNuclearCertificate4D covector time) :=
  d9GaugeGhostContinuumHeat_nuclear_gate covector time hSummable

/-- A physical LL heat realization becomes compact and nuclear under the
honest self-adjoint compact-resolvent spectral contract. -/
theorem global_regulator_ll_elliptic_nuclear_gate
    (period : Real) (hPeriod : period ≠ 0)
    {llData : PositiveLLH1Data period hPeriod}
    {Mode : Type*} [DecidableEq Mode]
    (analytic :
      ProgramPLL2EllipticHeatData period hPeriod llData Mode)
    (time : HeatTime) :
    (∀ first second,
      inner Real (analytic.operator (analytic.smoothCore first))
          (llH1SmoothToFluxL2 period hPeriod llData second) =
        globalPTSymmetricDifferentialLLFluxHessian period hPeriod
          llData.frame llData.fields first.toTest second.toTest llData.mu) ∧
      IsSelfAdjoint analytic.operator ∧
      IsCompactOperator analytic.resolvent ∧
      IsCompactOperator
        (programPLL2HeatOperator period hPeriod analytic time) ∧
      Summable
        (fun mode =>
          ‖programPLL2HeatRankOne
            period hPeriod analytic time mode‖) :=
  programPLL2EllipticNuclearHeat_regulator_gate
    period hPeriod analytic time

/-- One common positive time gives a bounded operator on the already
assembled physical spectral--LL sector together with the completed temporal
ghost.  The temporal ghost sub-block is compact and nuclear by its
certificate. -/
theorem global_regulator_physical_ll_temporal_ghost_gate
    (period : Real) [hPeriodPos : Fact (0 < period)]
    {ι : Type*}
    (covector : ι → TangentVector3)
    (spectralData : ProductThroatSpectralData)
    (matterMass : Real)
    (llData : PositiveLLH1Data period hPeriodPos.out.ne')
    (time : HeatTime) :
    Nonempty
      (ProgramPPhysicalLLTemporalGhostHeatRegulatorCertificate4D
        period covector spectralData matterMass llData time) :=
  ⟨programPPhysicalLLTemporalGhostHeatRegulatorCertificate4D
    period covector spectralData matterMass llData time⟩

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

/-- The complete D10 heat regulator is the exponential of the diagonal action
Hessian under the typed agreement, is contractive, and preserves the common
Fredholm/boundary domain. -/
theorem global_regulator_conditional_continuum_hessian_gate
    (period : Real) (hPeriod : period ≠ 0)
    {Spinor : Type*}
    (domain : ProgramPCommonGeometricDomain4D period hPeriod)
    (agreement :
      RemainingProgramPD7D9D10DomainAgreement4D
        period hPeriod Spinor domain)
    (time : HeatTime) :
    (∀ variation : ProgramPCompleteVariation4D period hPeriod,
      agreement.tangentNorm
          (programPAgreementHeatRegulator4D
            domain agreement time variation) ≤
        agreement.tangentNorm variation) ∧
      (∀ variation : ProgramPCompleteVariation4D period hPeriod,
        variation ∈ programPBoundaryTangentDomain4D period hPeriod domain →
          programPAgreementHeatRegulator4D
              domain agreement time variation ∈
            programPBoundaryTangentDomain4D period hPeriod domain) ∧
      ∀ mode : ProgramPD10Mode4D domain.d7d10SpectralData,
        programPAgreementHeatRegulator4D
            domain agreement time (agreement.modeTangent mode) =
          agreement.tangentSMul
            (Real.exp
              (-time.1 *
                agreement.actionHessian agreement.baseConfiguration
                  (agreement.modeTangent mode)
                  (agreement.modeTangent mode)))
            (agreement.modeTangent mode) := by
  exact
    ⟨programPAgreementHeatRegulator4D_tangentNorm_le domain agreement time,
      programPAgreementHeatRegulator4D_mem_boundaryDomain
        domain agreement time,
      programPAgreementHeatRegulator4D_mode_eq_exp_hessian
        domain agreement time⟩

end
end P0EFTJanusProgramPGlobalRegulatorFrontier4D
end JanusFormal
