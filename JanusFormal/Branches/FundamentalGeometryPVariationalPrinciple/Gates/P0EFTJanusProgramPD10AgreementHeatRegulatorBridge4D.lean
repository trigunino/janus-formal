import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD10AgreementFredholmBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD10ContinuumHeatOperatorNuclear4D

/-!
# Continuum heat regulator transported through the Program-P agreement

The existing complete D10 heat operator is complex, whereas the action-tangent
coordinates in `RemainingProgramPD7D9D10DomainAgreement4D` are real.  This
gate supplies the corresponding real diagonal multiplier and transports it to
the genuine complete variation.  On every mode it is exactly the exponential
of the diagonal action Hessian, is contractive, and preserves the common
Fredholm/boundary domain.

The construction remains conditional on the domain-agreement contract.  It
does not construct regulators for action blocks not identified by that
contract.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD10AgreementHeatRegulatorBridge4D

set_option autoImplicit false

noncomputable section

open scoped ENNReal lp
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusProgramPD10AgreementFredholmBridge4D
open P0EFTJanusProgramPD10ContinuumHeatRegulator4D
open P0EFTJanusProgramPD10ContinuumHeatOperatorNuclear4D

variable {period : ℝ} {hPeriod : period ≠ 0}
variable {Spinor : Type*}

/-- Real form of the complete D10 heat multiplier, matching the real action
tangent coordinates in the agreement contract. -/
def programPD10RealHeatMultiplier4D
    (data : ProductThroatSpectralData) (time : HeatTime)
    (state : ProgramPD10ModeHilbert4D data) :
    ProgramPD10ModeHilbert4D data :=
  ⟨fun mode => programPD10HeatWeight data time mode * state mode, by
    refine state.2.mono' ?_
    intro mode
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (programPD10HeatWeight_nonnegative data time mode)]
    simpa using mul_le_mul_of_nonneg_right
      (programPD10HeatWeight_le_one data time mode)
      (abs_nonneg (state mode))⟩

@[simp]
theorem programPD10RealHeatMultiplier4D_apply
    (data : ProductThroatSpectralData) (time : HeatTime)
    (state : ProgramPD10ModeHilbert4D data)
    (mode : ProgramPD10Mode4D data) :
    programPD10RealHeatMultiplier4D data time state mode =
      programPD10HeatWeight data time mode * state mode :=
  rfl

theorem programPD10RealHeatMultiplier4D_norm_le
    (data : ProductThroatSpectralData) (time : HeatTime)
    (state : ProgramPD10ModeHilbert4D data) :
    ‖programPD10RealHeatMultiplier4D data time state‖ ≤ ‖state‖ := by
  apply lp.norm_mono (p := (2 : ENNReal)) (by norm_num)
  intro mode
  change
    ‖programPD10HeatWeight data time mode * state mode‖ ≤ ‖state mode‖
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (programPD10HeatWeight_nonnegative data time mode)]
  exact mul_le_of_le_one_left (abs_nonneg (state mode))
    (programPD10HeatWeight_le_one data time mode)

theorem programPD10RealHeatMultiplier4D_mem_fredholmDomain
    (data : ProductThroatSpectralData) (time : HeatTime)
    (state : ProgramPD10ModeHilbert4D data)
    (hState : state ∈ programPD10FredholmModeDomain4D data) :
    programPD10RealHeatMultiplier4D data time state ∈
      programPD10FredholmModeDomain4D data := by
  exact hState.mono' (fun mode => by
    change
      ‖productDiracEigenvalueSquared data mode.separatedMode *
          (programPD10HeatWeight data time mode * state mode)‖ ≤
        ‖productDiracEigenvalueSquared data mode.separatedMode * state mode‖
    simp only [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (programPD10HeatWeight_nonnegative data time mode)]
    calc
      |productDiracEigenvalueSquared data mode.separatedMode| *
          (programPD10HeatWeight data time mode * |state mode|) =
        programPD10HeatWeight data time mode *
          (|productDiracEigenvalueSquared data mode.separatedMode| *
            |state mode|) := by ring
      _ ≤
          |productDiracEigenvalueSquared data mode.separatedMode| *
            |state mode| :=
        mul_le_of_le_one_left
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
          (programPD10HeatWeight_le_one data time mode))

/-- Continuum D10 heat regulator transported to the complete Program-P
variation through the exact agreement coordinates. -/
def programPAgreementHeatRegulator4D
    (domain : ProgramPCommonGeometricDomain4D period hPeriod)
    (agreement :
      RemainingProgramPD7D9D10DomainAgreement4D
        period hPeriod Spinor domain)
    (time : HeatTime)
    (variation : ProgramPCompleteVariation4D period hPeriod) :
    ProgramPCompleteVariation4D period hPeriod :=
  agreement.modeCoordinateEquiv.symm
    (programPD10RealHeatMultiplier4D
      domain.d7d10SpectralData time
      (agreement.modeCoordinateEquiv variation))

@[simp]
theorem programPAgreementHeatRegulator4D_coordinate
    (domain : ProgramPCommonGeometricDomain4D period hPeriod)
    (agreement :
      RemainingProgramPD7D9D10DomainAgreement4D
        period hPeriod Spinor domain)
    (time : HeatTime)
    (variation : ProgramPCompleteVariation4D period hPeriod) :
    agreement.modeCoordinateEquiv
        (programPAgreementHeatRegulator4D
          domain agreement time variation) =
      programPD10RealHeatMultiplier4D
        domain.d7d10SpectralData time
        (agreement.modeCoordinateEquiv variation) :=
  agreement.modeCoordinateEquiv.apply_symm_apply _

/-- The transported heat regulator is a contraction in the exact tangent
norm supplied by the agreement. -/
theorem programPAgreementHeatRegulator4D_tangentNorm_le
    (domain : ProgramPCommonGeometricDomain4D period hPeriod)
    (agreement :
      RemainingProgramPD7D9D10DomainAgreement4D
        period hPeriod Spinor domain)
    (time : HeatTime)
    (variation : ProgramPCompleteVariation4D period hPeriod) :
    agreement.tangentNorm
        (programPAgreementHeatRegulator4D
          domain agreement time variation) ≤
      agreement.tangentNorm variation := by
  rw [agreement.modeCoordinate_isometry,
    agreement.modeCoordinate_isometry,
    programPAgreementHeatRegulator4D_coordinate]
  exact programPD10RealHeatMultiplier4D_norm_le
    domain.d7d10SpectralData time
    (agreement.modeCoordinateEquiv variation)

/-- The continuum heat regulator preserves the exact common
Fredholm/boundary tangent domain. -/
theorem programPAgreementHeatRegulator4D_mem_boundaryDomain
    (domain : ProgramPCommonGeometricDomain4D period hPeriod)
    (agreement :
      RemainingProgramPD7D9D10DomainAgreement4D
        period hPeriod Spinor domain)
    (time : HeatTime)
    (variation : ProgramPCompleteVariation4D period hPeriod)
    (hVariation :
      variation ∈ programPBoundaryTangentDomain4D period hPeriod domain) :
    programPAgreementHeatRegulator4D domain agreement time variation ∈
      programPBoundaryTangentDomain4D period hPeriod domain := by
  rw [← agreement.fredholmDomain_eq_boundaryDomain] at hVariation ⊢
  apply (agreement.fredholmDomain_modeAgreement _).2
  rw [programPAgreementHeatRegulator4D_coordinate]
  exact programPD10RealHeatMultiplier4D_mem_fredholmDomain
    domain.d7d10SpectralData time
    (agreement.modeCoordinateEquiv variation)
    ((agreement.fredholmDomain_modeAgreement variation).1 hVariation)

/-- Each complete D10 tangent mode is an exact eigenvector of the transported
heat regulator. -/
theorem programPAgreementHeatRegulator4D_mode
    (domain : ProgramPCommonGeometricDomain4D period hPeriod)
    (agreement :
      RemainingProgramPD7D9D10DomainAgreement4D
        period hPeriod Spinor domain)
    (time : HeatTime)
    (mode : ProgramPD10Mode4D domain.d7d10SpectralData) :
    programPAgreementHeatRegulator4D
        domain agreement time (agreement.modeTangent mode) =
      agreement.tangentSMul
        (programPD10HeatWeight domain.d7d10SpectralData time mode)
        (agreement.modeTangent mode) := by
  apply agreement.modeCoordinateEquiv.injective
  rw [programPAgreementHeatRegulator4D_coordinate,
    agreement.modeCoordinate_smul]
  ext other
  change
    programPD10HeatWeight domain.d7d10SpectralData time other *
        agreement.modeCoordinateEquiv (agreement.modeTangent mode) other =
      programPD10HeatWeight domain.d7d10SpectralData time mode *
        agreement.modeCoordinateEquiv (agreement.modeTangent mode) other
  by_cases hMode : mode = other
  · subst other
    rw [agreement.modeCoordinate_same, mul_one]
  · rw [agreement.modeCoordinate_ne mode other hMode, mul_zero, mul_zero]

/-- The scalar heat weight is exactly the exponential of the diagonal action
Hessian on the corresponding complete tangent mode. -/
theorem programPD10HeatWeight_eq_exp_actionHessian
    (domain : ProgramPCommonGeometricDomain4D period hPeriod)
    (agreement :
      RemainingProgramPD7D9D10DomainAgreement4D
        period hPeriod Spinor domain)
    (time : HeatTime)
    (mode : ProgramPD10Mode4D domain.d7d10SpectralData) :
    programPD10HeatWeight domain.d7d10SpectralData time mode =
      Real.exp
        (-time.1 *
          agreement.actionHessian agreement.baseConfiguration
            (agreement.modeTangent mode)
            (agreement.modeTangent mode)) := by
  rw [programPAgreement_modeHessian_diagonal domain agreement]
  rfl

/-- Modewise functional-calculus statement for the transported regulator:
it is `exp (-t Hessian)` on every complete D10 eigendirection. -/
theorem programPAgreementHeatRegulator4D_mode_eq_exp_hessian
    (domain : ProgramPCommonGeometricDomain4D period hPeriod)
    (agreement :
      RemainingProgramPD7D9D10DomainAgreement4D
        period hPeriod Spinor domain)
    (time : HeatTime)
    (mode : ProgramPD10Mode4D domain.d7d10SpectralData) :
    programPAgreementHeatRegulator4D
        domain agreement time (agreement.modeTangent mode) =
      agreement.tangentSMul
        (Real.exp
          (-time.1 *
            agreement.actionHessian agreement.baseConfiguration
              (agreement.modeTangent mode)
              (agreement.modeTangent mode)))
        (agreement.modeTangent mode) := by
  rw [← programPD10HeatWeight_eq_exp_actionHessian
    domain agreement time mode]
  exact programPAgreementHeatRegulator4D_mode
    domain agreement time mode

end

end P0EFTJanusProgramPD10AgreementHeatRegulatorBridge4D
end JanusFormal
