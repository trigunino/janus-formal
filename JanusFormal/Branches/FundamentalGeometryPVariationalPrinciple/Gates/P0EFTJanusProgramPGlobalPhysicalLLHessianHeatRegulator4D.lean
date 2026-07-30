import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Exp
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalPhysicalLLHessianFredholm4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD10ContinuumHeatRegulator4D

/-!
# Bounded heat regulator for the physical spectral and LL Hessian

The already assembled D9/matter/D10 Hessian is diagonal.  D9 is already the
nonnegative squared-covector block, while the signed matter Dirac block is
first order and uses its squared Gaussian.  D10 is already the squared Dirac
block, so its existing continuum heat weight is reused without an extra
square.  The exact LL Riesz block is the identity, so the same functional
calculus gives the scalar factor `exp (-t)` on the LL energy completion.

This gate constructs the resulting common bounded operator on the existing
physical spectral--LL Hilbert sum.  It does not claim compactness or
trace-class regularity: those require spectral-growth input for D9 and a
compact-resolvent realization of the LL block.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalPhysicalLLHessianHeatRegulator4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusGaugeGhostBlockD9UnboundedFredholm4D
open P0EFTJanusGaugeFixedPrincipalSymbols
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusProgramPGlobalPhysicalLLHessianFredholm4D
open P0EFTJanusProgramPGlobalPhysicalSpectralHessianFredholm4D
open P0EFTJanusProgramPPrimitiveSpinCGeometricSignedFredholm4D
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusProgramPD10ContinuumHeatRegulator4D
open scoped ENNReal lp

variable (period : Real) (hPeriod : period ≠ 0)

/-- Order-corrected Gaussian on the assembled D9/matter/D10 modes.  D9 and
D10 are already squared; only the signed first-order matter block is squared
here. -/
def programPGlobalPhysicalSpectralHessianHeatWeight
    {ι : Type*}
    (covector : ι → TangentVector3)
    (spectralData : ProductThroatSpectralData)
    (matterMass : Real)
    (time : HeatTime) :
    ProgramPGlobalPhysicalSpectralHessianMode ι spectralData → Real
  | .inl mode =>
      Real.exp (-time.1 * d9GaugeGhostUnboundedWeight covector mode)
  | .inr (.inl mode) =>
      Real.exp
        (-time.1 *
          (primitiveSpinCGeometricSignedKineticHessianWeight
            period hPeriod mode.2 + matterMass) ^ 2)
  | .inr (.inr mode) =>
      programPD10HeatWeight spectralData time mode

@[simp]
theorem programPGlobalPhysicalSpectralHessianHeatWeight_d9
    {ι : Type*}
    (covector : ι → TangentVector3)
    (spectralData : ProductThroatSpectralData)
    (matterMass : Real)
    (time : HeatTime)
    (mode : ι × Fin 8) :
    programPGlobalPhysicalSpectralHessianHeatWeight
        period hPeriod covector spectralData matterMass time (.inl mode) =
      Real.exp (-time.1 * d9GaugeGhostUnboundedWeight covector mode) :=
  rfl

@[simp]
theorem programPGlobalPhysicalSpectralHessianHeatWeight_matter
    {ι : Type*}
    (covector : ι → TangentVector3)
    (spectralData : ProductThroatSpectralData)
    (matterMass : Real)
    (time : HeatTime)
    (mode : Sector × PrimitiveSpinCGeometricSignedMode) :
    programPGlobalPhysicalSpectralHessianHeatWeight
        period hPeriod covector spectralData matterMass time
          (.inr (.inl mode)) =
      Real.exp
        (-time.1 *
          (primitiveSpinCGeometricSignedKineticHessianWeight
            period hPeriod mode.2 + matterMass) ^ 2) :=
  rfl

@[simp]
theorem programPGlobalPhysicalSpectralHessianHeatWeight_d10
    {ι : Type*}
    (covector : ι → TangentVector3)
    (spectralData : ProductThroatSpectralData)
    (matterMass : Real)
    (time : HeatTime)
    (mode : ProgramPD10Mode4D spectralData) :
    programPGlobalPhysicalSpectralHessianHeatWeight
        period hPeriod covector spectralData matterMass time
          (.inr (.inr mode)) =
      programPD10HeatWeight spectralData time mode :=
  rfl

theorem programPGlobalPhysicalSpectralHessianHeatWeight_nonnegative
    {ι : Type*}
    (covector : ι → TangentVector3)
    (spectralData : ProductThroatSpectralData)
    (matterMass : Real)
    (time : HeatTime)
    (mode : ProgramPGlobalPhysicalSpectralHessianMode ι spectralData) :
    0 ≤ programPGlobalPhysicalSpectralHessianHeatWeight
      period hPeriod covector spectralData matterMass time mode := by
  rcases mode with mode | mode
  · exact (Real.exp_pos _).le
  · rcases mode with mode | mode
    · exact (Real.exp_pos _).le
    · exact programPD10HeatWeight_nonnegative spectralData time mode

theorem d9GaugeGhostUnboundedWeight_nonnegative
    {ι : Type*}
    (covector : ι → TangentVector3)
    (mode : ι × Fin 8) :
    0 ≤ d9GaugeGhostUnboundedWeight covector mode := by
  unfold d9GaugeGhostUnboundedWeight normSquared tangentDot
  nlinarith [sq_nonneg (covector mode.1).x,
    sq_nonneg (covector mode.1).y, sq_nonneg (covector mode.1).z]

theorem programPGlobalPhysicalSpectralHessianHeatWeight_le_one
    {ι : Type*}
    (covector : ι → TangentVector3)
    (spectralData : ProductThroatSpectralData)
    (matterMass : Real)
    (time : HeatTime)
    (mode : ProgramPGlobalPhysicalSpectralHessianMode ι spectralData) :
    programPGlobalPhysicalSpectralHessianHeatWeight
      period hPeriod covector spectralData matterMass time mode ≤ 1 := by
  have heat_le_one (eigenvalueSq : Real) (hEigenvalueSq : 0 ≤ eigenvalueSq) :
      Real.exp (-time.1 * eigenvalueSq) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr time.2.le) hEigenvalueSq
  rcases mode with mode | mode
  · exact heat_le_one _
      (d9GaugeGhostUnboundedWeight_nonnegative covector mode)
  · rcases mode with mode | mode
    · exact heat_le_one _ (sq_nonneg _)
    · exact heat_le_one _
        (product_spectrum_has_positive_gap
          spectralData mode.separatedMode).le

/-- Coordinatewise Gaussian as a real-linear map on the existing complex
spectral Hilbert space. -/
def programPGlobalPhysicalSpectralHessianHeatLinearMap
    {ι : Type*}
    (covector : ι → TangentVector3)
    (spectralData : ProductThroatSpectralData)
    (matterMass : Real)
    (time : HeatTime) :
    ProgramPGlobalPhysicalSpectralHessianHilbert ι spectralData →ₗ[Real]
      ProgramPGlobalPhysicalSpectralHessianHilbert ι spectralData where
  toFun state := ⟨fun mode =>
    (programPGlobalPhysicalSpectralHessianHeatWeight
      period hPeriod covector spectralData matterMass time mode : Complex) *
        state mode, by
      refine state.2.mono' ?_
      intro mode
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg
          (programPGlobalPhysicalSpectralHessianHeatWeight_nonnegative
            period hPeriod covector spectralData matterMass time mode)]
      simpa using mul_le_mul_of_nonneg_right
        (programPGlobalPhysicalSpectralHessianHeatWeight_le_one
          period hPeriod covector spectralData matterMass time mode)
        (norm_nonneg (state mode))⟩
  map_add' := by
    intro first second
    ext mode
    simp [mul_add]
  map_smul' := by
    intro scalar state
    ext mode
    simp [mul_left_comm]

/-- Bounded spectral Gaussian contraction. -/
def programPGlobalPhysicalSpectralHessianHeatOperator
    {ι : Type*}
    (covector : ι → TangentVector3)
    (spectralData : ProductThroatSpectralData)
    (matterMass : Real)
    (time : HeatTime) :
    ProgramPGlobalPhysicalSpectralHessianHilbert ι spectralData →L[Real]
      ProgramPGlobalPhysicalSpectralHessianHilbert ι spectralData :=
  (programPGlobalPhysicalSpectralHessianHeatLinearMap
    period hPeriod covector spectralData matterMass time).mkContinuous 1 (by
      intro state
      rw [one_mul]
      apply lp.norm_mono (p := (2 : ENNReal)) (by norm_num)
      intro mode
      change ‖(programPGlobalPhysicalSpectralHessianHeatWeight
        period hPeriod covector spectralData matterMass time mode : Complex) *
          state mode‖ ≤ ‖state mode‖
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg
          (programPGlobalPhysicalSpectralHessianHeatWeight_nonnegative
            period hPeriod covector spectralData matterMass time mode)]
      exact mul_le_of_le_one_left (norm_nonneg (state mode))
        (programPGlobalPhysicalSpectralHessianHeatWeight_le_one
          period hPeriod covector spectralData matterMass time mode))

@[simp]
theorem programPGlobalPhysicalSpectralHessianHeatOperator_apply
    {ι : Type*}
    (covector : ι → TangentVector3)
    (spectralData : ProductThroatSpectralData)
    (matterMass : Real)
    (time : HeatTime)
    (state : ProgramPGlobalPhysicalSpectralHessianHilbert ι spectralData)
    (mode : ProgramPGlobalPhysicalSpectralHessianMode ι spectralData) :
    programPGlobalPhysicalSpectralHessianHeatOperator
        period hPeriod covector spectralData matterMass time state mode =
      (programPGlobalPhysicalSpectralHessianHeatWeight
        period hPeriod covector spectralData matterMass time mode : Complex) *
        state mode :=
  rfl

theorem programPGlobalPhysicalSpectralHessianHeatOperator_opNorm_le_one
    {ι : Type*}
    (covector : ι → TangentVector3)
    (spectralData : ProductThroatSpectralData)
    (matterMass : Real)
    (time : HeatTime) :
    ‖programPGlobalPhysicalSpectralHessianHeatOperator
      period hPeriod covector spectralData matterMass time‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- Heat weight of the squared identity Riesz representative on LL. -/
def programPGlobalPhysicalLLHessianHeatWeight (time : HeatTime) : Real :=
  Real.exp (-time.1)

/-- The exact LL heat block. -/
def programPGlobalPhysicalLLHessianHeatOperator
    (time : HeatTime)
    (llData : PositiveLLH1Data period hPeriod) :
    LLH1Space period hPeriod llData →L[Real]
      LLH1Space period hPeriod llData :=
  programPGlobalPhysicalLLHessianHeatWeight time •
    ContinuousLinearMap.id Real (LLH1Space period hPeriod llData)

@[simp]
theorem programPGlobalPhysicalLLHessianHeatOperator_apply
    (time : HeatTime)
    (llData : PositiveLLH1Data period hPeriod)
    (state : LLH1Space period hPeriod llData) :
    programPGlobalPhysicalLLHessianHeatOperator
        period hPeriod time llData state =
      programPGlobalPhysicalLLHessianHeatWeight time • state := by
  rfl

/-- Exact obstruction for the LL factor: its present identity-Riesz heat is
compact precisely when the completed LL energy space is finite-dimensional. -/
theorem programPGlobalPhysicalLLHessianHeatOperator_isCompact_iff
    (time : HeatTime)
    (llData : PositiveLLH1Data period hPeriod) :
    IsCompactOperator
        (programPGlobalPhysicalLLHessianHeatOperator
          period hPeriod time llData) ↔
      FiniteDimensional Real (LLH1Space period hPeriod llData) := by
  rw [← isCompactOperator_id_iff_finiteDimensional]
  unfold programPGlobalPhysicalLLHessianHeatOperator
    programPGlobalPhysicalLLHessianHeatWeight
  change
    IsCompactOperator
        (Real.exp (-time.1) •
          (id : LLH1Space period hPeriod llData →
            LLH1Space period hPeriod llData)) ↔
      IsCompactOperator
        (id : LLH1Space period hPeriod llData →
          LLH1Space period hPeriod llData)
  exact
    (IsCompactOperator.smul_isUnit_iff
      (f := (id : LLH1Space period hPeriod llData →
        LLH1Space period hPeriod llData))
      (isUnit_iff_ne_zero.mpr (Real.exp_ne_zero _)))

/-- One common positive time on the existing physical spectral--LL Hilbert
sum. -/
def programPGlobalPhysicalLLCommonHeatOperator
    {ι : Type*}
    (covector : ι → TangentVector3)
    (spectralData : ProductThroatSpectralData)
    (matterMass : Real)
    (llData : PositiveLLH1Data period hPeriod)
    (time : HeatTime) :
    ProgramPGlobalPhysicalLLHessianHilbert
        period hPeriod ι spectralData llData →L[Real]
      ProgramPGlobalPhysicalLLHessianHilbert
        period hPeriod ι spectralData llData :=
  (WithLp.prodContinuousLinearEquiv 2 Real
      (ProgramPGlobalPhysicalSpectralHessianHilbert ι spectralData)
      (LLH1Space period hPeriod llData)).symm.toContinuousLinearMap ∘L
    ((programPGlobalPhysicalSpectralHessianHeatOperator
        period hPeriod covector spectralData matterMass time).prodMap
      (programPGlobalPhysicalLLHessianHeatOperator
        period hPeriod time llData)) ∘L
    (WithLp.prodContinuousLinearEquiv 2 Real
      (ProgramPGlobalPhysicalSpectralHessianHilbert ι spectralData)
      (LLH1Space period hPeriod llData)).toContinuousLinearMap

@[simp]
theorem programPGlobalPhysicalLLCommonHeatOperator_apply
    {ι : Type*}
    (covector : ι → TangentVector3)
    (spectralData : ProductThroatSpectralData)
    (matterMass : Real)
    (llData : PositiveLLH1Data period hPeriod)
    (time : HeatTime)
    (state : ProgramPGlobalPhysicalLLHessianHilbert
      period hPeriod ι spectralData llData) :
    WithLp.ofLp
      (programPGlobalPhysicalLLCommonHeatOperator
        period hPeriod covector spectralData matterMass llData time state) =
      (programPGlobalPhysicalSpectralHessianHeatOperator
          period hPeriod covector spectralData matterMass time
          (WithLp.ofLp state).1,
        programPGlobalPhysicalLLHessianHeatWeight time •
          (WithLp.ofLp state).2) :=
  rfl

/-- Minimal unconditional certificate: both actual completed blocks use one
positive heat time and the resulting common map is bounded by construction. -/
theorem programPGlobalPhysicalLLCommonHeat_regulator_gate
    {ι : Type*}
    (covector : ι → TangentVector3)
    (spectralData : ProductThroatSpectralData)
    (matterMass : Real)
    (llData : PositiveLLH1Data period hPeriod)
    (time : HeatTime) :
    Nonempty
      (ProgramPGlobalPhysicalLLHessianHilbert
          period hPeriod ι spectralData llData →L[Real]
        ProgramPGlobalPhysicalLLHessianHilbert
          period hPeriod ι spectralData llData) :=
  ⟨programPGlobalPhysicalLLCommonHeatOperator
    period hPeriod covector spectralData matterMass llData time⟩

end
end P0EFTJanusProgramPGlobalPhysicalLLHessianHeatRegulator4D
end JanusFormal
