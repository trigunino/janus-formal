import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCommonGeometricDomain4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteModeCommonPhysicalGhostHeatRegulator4D

/-!
# Complete-variation bridge to the finite D10 anomaly regulator

The strengthened Program-P/D9/D10 agreement contract already identifies each
truncated D10 label with a genuine `ProgramPCompleteVariation4D` tangent and
identifies its action-Hessian diagonal with the D10 regulator eigenvalue.
This gate transports the existing multiplicity/statistics-weighted finite heat
regulator through that exact identification and records the matching boundary
domain statement.

The result is conditional on the agreement contract and finite-mode only.
Chirality, multiplicity and statistics remain explicit regulator inputs; no
global Janus anomaly or Quillen trivialization is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusCompleteVariationFiniteD10AnomalyRegulatorBridge4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusFiniteModeHeatKernelAnomalyRegulator
open P0EFTJanusFiniteModeCommonPhysicalGhostHeatRegulator4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- A finite weighted D10 sector using exactly the spectral datum stored by
the common Program-P geometric domain. -/
def completeVariationD10WeightedSector
    (domain : ProgramPCommonGeometricDomain4D period hPeriod)
    (sphereCutoff circleCutoff multiplicity : Nat)
    (statistics : FieldStatistics) :
    WeightedSector
      (TruncatedD10Mode domain.d7d10SpectralData sphereCutoff circleCutoff) where
  multiplicity := multiplicity
  statistics := statistics
  spectrum := domain.d10FiniteRegulator period hPeriod sphereCutoff circleCutoff

@[simp]
theorem completeVariationD10WeightedSector_spectrum
    (domain : ProgramPCommonGeometricDomain4D period hPeriod)
    (sphereCutoff circleCutoff multiplicity : Nat)
    (statistics : FieldStatistics) :
    (completeVariationD10WeightedSector period hPeriod domain sphereCutoff
      circleCutoff multiplicity statistics).spectrum =
      domain.d10FiniteRegulator period hPeriod sphereCutoff circleCutoff :=
  rfl

/-- Under the concrete common-space agreement, the regulator eigenvalue is
the diagonal Hessian of the same action on the genuine complete tangent
assigned to that truncated D10 mode. -/
theorem completeVariationD10WeightedSector_hessian_eigenvalue
    {Spinor : Type*}
    (domain : ProgramPCommonGeometricDomain4D period hPeriod)
    (agreement :
      RemainingProgramPD7D9D10DomainAgreement4D period hPeriod Spinor domain)
    (sphereCutoff circleCutoff multiplicity : Nat)
    (statistics : FieldStatistics)
    (mode : TruncatedD10Mode domain.d7d10SpectralData
      sphereCutoff circleCutoff) :
    agreement.actionHessian agreement.baseConfiguration
        (agreement.modeTangent (truncatedProgramPD10Mode4D mode))
        (agreement.modeTangent (truncatedProgramPD10Mode4D mode)) =
      (completeVariationD10WeightedSector period hPeriod domain sphereCutoff
        circleCutoff multiplicity statistics).spectrum.eigenvalueSq mode := by
  exact agreement.regulator_hessian_spectrum_agreement
    sphereCutoff circleCutoff mode

/-- The same complete mode tangent lies in the current Program-P boundary
domain exactly when its D10 coordinate lies in the common Fredholm domain. -/
theorem completeVariationD10Mode_mem_boundaryDomain_iff
    {Spinor : Type*}
    (domain : ProgramPCommonGeometricDomain4D period hPeriod)
    (agreement :
      RemainingProgramPD7D9D10DomainAgreement4D period hPeriod Spinor domain)
    {sphereCutoff circleCutoff : Nat}
    (mode : TruncatedD10Mode domain.d7d10SpectralData
      sphereCutoff circleCutoff) :
    agreement.modeTangent (truncatedProgramPD10Mode4D mode) ∈
        programPBoundaryTangentDomain4D period hPeriod domain ↔
      agreement.modeCoordinateEquiv
          (agreement.modeTangent (truncatedProgramPD10Mode4D mode)) ∈
        programPD10FredholmModeDomain4D domain.d7d10SpectralData := by
  rw [← agreement.fredholmDomain_eq_boundaryDomain]
  exact agreement.fredholmDomain_modeAgreement _

/-- Multiplicity and statistics do not spoil the exact PT cancellation on
this finite D10 sector.  This is not a cutoff-limit or global anomaly claim. -/
theorem completeVariationD10WeightedSector_signed_chiral_trace_eq_zero
    (domain : ProgramPCommonGeometricDomain4D period hPeriod)
    (sphereCutoff circleCutoff multiplicity : Nat)
    (statistics : FieldStatistics)
    (regulatorTime : RegulatorTime) :
    signedPairedChiralTrace regulatorTime
        (completeVariationD10WeightedSector period hPeriod domain sphereCutoff
          circleCutoff multiplicity statistics) = 0 := by
  exact signedPairedChiralTrace_eq_zero regulatorTime _

/-- Conditional finite-mode bridge in one statement: every regulated
eigenvalue is an actual complete-variation Hessian diagonal, and its signed
PT-paired chiral trace cancels at the common heat time. -/
theorem completeVariation_hessian_finiteD10_signed_chiral_trace_cancels
    {Spinor : Type*}
    (domain : ProgramPCommonGeometricDomain4D period hPeriod)
    (agreement :
      RemainingProgramPD7D9D10DomainAgreement4D period hPeriod Spinor domain)
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
            circleCutoff multiplicity statistics) = 0 := by
  constructor
  · intro mode
    exact completeVariationD10WeightedSector_hessian_eigenvalue
      period hPeriod domain agreement sphereCutoff circleCutoff multiplicity
      statistics mode
  · exact completeVariationD10WeightedSector_signed_chiral_trace_eq_zero
      period hPeriod domain sphereCutoff circleCutoff multiplicity statistics
      regulatorTime

end

end P0EFTJanusCompleteVariationFiniteD10AnomalyRegulatorBridge4D
end JanusFormal
