import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12GaugeFixedLLFriedrichsCommonDomainFamily4D

/-!
# Norm-continuous LL Friedrichs resolvents

The nonnegative LL Friedrichs shifts satisfy the first resolvent identity.
Their energy construction gives a parameter-independent operator-norm bound,
so the squared-parameter family is continuous in operator norm.  Every fibre
remains compact by the preceding Friedrichs construction.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12LLFriedrichsNormResolventFamily4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPT12HilbertEnergyShift4D
open P0EFTJanusProgramPT12LLCanonicalH1L2Bridge4D
open P0EFTJanusProgramPT12LLCanonicalH1ShiftedWeakSolution4D
open P0EFTJanusProgramPT12LLCanonicalFriedrichsRealization4D
open P0EFTJanusProgramPT12LLCanonicalFriedrichsShiftedResolvent4D
open P0EFTJanusProgramPT12GaugeFixedLLFriedrichsCommonDomainFamily4D

private theorem energyShiftL2Solution_resolvent_identity_aux
    {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace Real V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace Real H] [CompleteSpace H]
    (I : V →L[Real] H)
    (first second : Real) (hFirst : 0 ≤ first) (hSecond : 0 ≤ second) :
    energyShiftL2Solution I first hFirst -
        energyShiftL2Solution I second hSecond =
      (second - first) •
        ((energyShiftL2Solution I first hFirst).comp
          (energyShiftL2Solution I second hSecond)) := by
  apply ContinuousLinearMap.ext
  intro source
  let firstSolution := energyShiftSolution I first hFirst source
  let secondSolution := energyShiftSolution I second hSecond source
  have hFirstPairing (test : V) :
      inner Real firstSolution test +
          first * inner Real (I firstSolution) (I test) =
        inner Real source (I test) :=
    energyShiftSolution_pairing I first hFirst source test
  have hSecondPairing (test : V) :
      inner Real secondSolution test +
          second * inner Real (I secondSolution) (I test) =
        inner Real source (I test) :=
    energyShiftSolution_pairing I second hSecond source test
  have hDifference :
      firstSolution - secondSolution =
        energyShiftSolution I first hFirst
          ((second - first) • energyShiftL2Solution I second hSecond source) := by
    apply energyShiftSolution_unique I first hFirst
    intro test
    change
      inner Real (firstSolution - secondSolution) test +
          first * inner Real (I (firstSolution - secondSolution)) (I test) =
        inner Real ((second - first) • I secondSolution) (I test)
    rw [inner_sub_left, map_sub, inner_sub_left, real_inner_smul_left]
    have hFirstEquation := hFirstPairing test
    have hSecondEquation := hSecondPairing test
    linear_combination hFirstEquation - hSecondEquation
  have hMapped := congrArg I hDifference
  simpa [firstSolution, secondSolution, energyShiftL2Solution,
    sub_apply, smul_apply,
    ContinuousLinearMap.comp_apply] using hMapped

private theorem energyShiftL2Solution_norm_le_aux
    {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace Real V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace Real H] [CompleteSpace H]
    (I : V →L[Real] H) (shift : Real) (hShift : 0 ≤ shift)
    (source : H) :
    ‖energyShiftL2Solution I shift hShift source‖ ≤
      ‖I‖ ^ 2 * ‖source‖ := by
  let solution := energyShiftSolution I shift hShift source
  have hPairing :
      inner Real solution solution +
          shift * inner Real (I solution) (I solution) =
        inner Real source (I solution) :=
    energyShiftSolution_pairing I shift hShift source solution
  have hSolutionSq :
      ‖solution‖ ^ 2 ≤ ‖source‖ * ‖I solution‖ := by
    calc
      ‖solution‖ ^ 2 ≤
          ‖solution‖ ^ 2 + shift * ‖I solution‖ ^ 2 :=
        le_add_of_nonneg_right (mul_nonneg hShift (sq_nonneg _))
      _ = inner Real source (I solution) := by
        simpa only [real_inner_self_eq_norm_sq] using hPairing
      _ ≤ ‖source‖ * ‖I solution‖ := real_inner_le_norm _ _
  have hSolutionNorm : ‖solution‖ ≤ ‖I‖ * ‖source‖ := by
    by_cases hSolutionZero : solution = 0
    · rw [hSolutionZero, norm_zero]
      positivity
    · have hSolutionPositive : 0 < ‖solution‖ := norm_pos_iff.mpr hSolutionZero
      apply le_of_mul_le_mul_right ?_ hSolutionPositive
      calc
        ‖solution‖ * ‖solution‖ = ‖solution‖ ^ 2 := by ring
        _ ≤ ‖source‖ * ‖I solution‖ := hSolutionSq
        _ ≤ ‖source‖ * (‖I‖ * ‖solution‖) :=
          mul_le_mul_of_nonneg_left (I.le_opNorm solution) (norm_nonneg source)
        _ = (‖I‖ * ‖source‖) * ‖solution‖ := by ring
  change ‖I solution‖ ≤ ‖I‖ ^ 2 * ‖source‖
  calc
    ‖I solution‖ ≤ ‖I‖ * ‖solution‖ := I.le_opNorm solution
    _ ≤ ‖I‖ * (‖I‖ * ‖source‖) :=
      mul_le_mul_of_nonneg_left hSolutionNorm (norm_nonneg I)
    _ = ‖I‖ ^ 2 * ‖source‖ := by ring

private theorem energyShiftL2Solution_opNorm_le_aux
    {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace Real V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace Real H] [CompleteSpace H]
    (I : V →L[Real] H) (shift : Real) (hShift : 0 ≤ shift) :
    ‖energyShiftL2Solution I shift hShift‖ ≤ ‖I‖ ^ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (sq_nonneg ‖I‖)
  exact energyShiftL2Solution_norm_le_aux I shift hShift

private theorem energyShiftL2Solution_resolvent_norm_sub_le_aux
    {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace Real V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace Real H] [CompleteSpace H]
    (I : V →L[Real] H)
    (first second : Real) (hFirst : 0 ≤ first) (hSecond : 0 ≤ second) :
    ‖energyShiftL2Solution I first hFirst -
        energyShiftL2Solution I second hSecond‖ ≤
      |second - first| * ((‖I‖ ^ 2) * (‖I‖ ^ 2)) := by
  rw [energyShiftL2Solution_resolvent_identity_aux I first second hFirst hSecond,
    norm_smul, Real.norm_eq_abs]
  calc
    |second - first| *
          ‖(energyShiftL2Solution I first hFirst).comp
            (energyShiftL2Solution I second hSecond)‖ ≤
        |second - first| *
          (‖energyShiftL2Solution I first hFirst‖ *
            ‖energyShiftL2Solution I second hSecond‖) :=
      mul_le_mul_of_nonneg_left
        (ContinuousLinearMap.opNorm_comp_le _ _) (abs_nonneg _)
    _ ≤ |second - first| * ((‖I‖ ^ 2) * (‖I‖ ^ 2)) := by
      gcongr
      · exact energyShiftL2Solution_opNorm_le_aux I first hFirst
      · exact energyShiftL2Solution_opNorm_le_aux I second hSecond

private theorem energyShiftL2Solution_continuous_aux
    {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace Real V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace Real H] [CompleteSpace H]
    (I : V →L[Real] H)
    (shift : Real → Real) (hShift : ∀ parameter, 0 ≤ shift parameter)
    (hShiftContinuous : Continuous shift) :
    Continuous (fun parameter =>
      energyShiftL2Solution I (shift parameter) (hShift parameter)) := by
  rw [continuous_iff_continuousAt]
  intro parameter
  apply tendsto_iff_norm_sub_tendsto_zero.2
  refine squeeze_zero (fun other => norm_nonneg _) (fun other =>
    energyShiftL2Solution_resolvent_norm_sub_le_aux I
      (shift other) (shift parameter) (hShift other) (hShift parameter)) ?_
  have hBoundContinuous : ContinuousAt
      (fun other =>
        |shift parameter - shift other| *
          ((‖I‖ ^ 2) * (‖I‖ ^ 2))) parameter :=
    ((continuousAt_const.sub hShiftContinuous.continuousAt).abs.mul_const _)
  simpa using hBoundContinuous.tendsto

variable (period : Real) (hPeriod : period ≠ 0)

/-- Exact first resolvent identity for the squared-parameter LL family. -/
theorem programPT12GaugeFixedLLFriedrichsD11LLResolvent_identity
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (first second : Real) :
    programPT12GaugeFixedLLFriedrichsD11LLResolvent
          period hPeriod analysis first -
        programPT12GaugeFixedLLFriedrichsD11LLResolvent
          period hPeriod analysis second =
      (programPT12GaugeFixedLLFriedrichsD11Shift second -
          programPT12GaugeFixedLLFriedrichsD11Shift first) •
        ((programPT12GaugeFixedLLFriedrichsD11LLResolvent
            period hPeriod analysis first).comp
          (programPT12GaugeFixedLLFriedrichsD11LLResolvent
            period hPeriod analysis second)) := by
  simpa only [programPT12GaugeFixedLLFriedrichsD11LLResolvent,
    canonicalLLFriedrichsShiftedResolvent,
    canonicalLLShiftedWeakL2Solution] using
    (energyShiftL2Solution_resolvent_identity_aux
      (canonicalLLH1ToFluxL2 period hPeriod analysis)
      (programPT12GaugeFixedLLFriedrichsD11Shift first)
      (programPT12GaugeFixedLLFriedrichsD11Shift second)
      (programPT12GaugeFixedLLFriedrichsD11Shift_nonnegative first)
      (programPT12GaugeFixedLLFriedrichsD11Shift_nonnegative second))

/-- Uniform operator-norm control inherited from the energy embedding. -/
theorem programPT12GaugeFixedLLFriedrichsD11LLResolvent_opNorm_le
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (parameter : Real) :
    ‖programPT12GaugeFixedLLFriedrichsD11LLResolvent
      period hPeriod analysis parameter‖ ≤
        ‖canonicalLLH1ToFluxL2 period hPeriod analysis‖ ^ 2 := by
  simpa only [programPT12GaugeFixedLLFriedrichsD11LLResolvent,
    canonicalLLFriedrichsShiftedResolvent,
    canonicalLLShiftedWeakL2Solution] using
    (energyShiftL2Solution_opNorm_le_aux
      (canonicalLLH1ToFluxL2 period hPeriod analysis)
      (programPT12GaugeFixedLLFriedrichsD11Shift parameter)
      (programPT12GaugeFixedLLFriedrichsD11Shift_nonnegative parameter))

/-- Quantitative operator-norm modulus for two fibres. -/
theorem programPT12GaugeFixedLLFriedrichsD11LLResolvent_norm_sub_le
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (first second : Real) :
    ‖programPT12GaugeFixedLLFriedrichsD11LLResolvent
          period hPeriod analysis first -
        programPT12GaugeFixedLLFriedrichsD11LLResolvent
          period hPeriod analysis second‖ ≤
      |programPT12GaugeFixedLLFriedrichsD11Shift second -
          programPT12GaugeFixedLLFriedrichsD11Shift first| *
        ((‖canonicalLLH1ToFluxL2 period hPeriod analysis‖ ^ 2) *
          (‖canonicalLLH1ToFluxL2 period hPeriod analysis‖ ^ 2)) := by
  simpa only [programPT12GaugeFixedLLFriedrichsD11LLResolvent,
    canonicalLLFriedrichsShiftedResolvent,
    canonicalLLShiftedWeakL2Solution] using
    (energyShiftL2Solution_resolvent_norm_sub_le_aux
      (canonicalLLH1ToFluxL2 period hPeriod analysis)
      (programPT12GaugeFixedLLFriedrichsD11Shift first)
      (programPT12GaugeFixedLLFriedrichsD11Shift second)
      (programPT12GaugeFixedLLFriedrichsD11Shift_nonnegative first)
      (programPT12GaugeFixedLLFriedrichsD11Shift_nonnegative second))

/-- The compact LL resolvents vary continuously in operator norm. -/
theorem programPT12GaugeFixedLLFriedrichsD11LLResolvent_continuous
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    Continuous (fun parameter =>
      programPT12GaugeFixedLLFriedrichsD11LLResolvent
        period hPeriod analysis parameter) := by
  have hShiftContinuous :
      Continuous programPT12GaugeFixedLLFriedrichsD11Shift := by
    unfold programPT12GaugeFixedLLFriedrichsD11Shift
    fun_prop
  simpa only [programPT12GaugeFixedLLFriedrichsD11LLResolvent,
    canonicalLLFriedrichsShiftedResolvent,
    canonicalLLShiftedWeakL2Solution] using
    (energyShiftL2Solution_continuous_aux
      (canonicalLLH1ToFluxL2 period hPeriod analysis)
      programPT12GaugeFixedLLFriedrichsD11Shift
      programPT12GaugeFixedLLFriedrichsD11Shift_nonnegative
      hShiftContinuous)

/-- Compact, uniformly bounded and norm-continuous LL resolvent family. -/
structure ProgramPT12GaugeFixedLLFriedrichsD11LLNormResolventFamilyCertificate4D
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) : Prop where
  resolventIdentity : ∀ first second,
    programPT12GaugeFixedLLFriedrichsD11LLResolvent
          period hPeriod analysis first -
        programPT12GaugeFixedLLFriedrichsD11LLResolvent
          period hPeriod analysis second =
      (programPT12GaugeFixedLLFriedrichsD11Shift second -
          programPT12GaugeFixedLLFriedrichsD11Shift first) •
        ((programPT12GaugeFixedLLFriedrichsD11LLResolvent
            period hPeriod analysis first).comp
          (programPT12GaugeFixedLLFriedrichsD11LLResolvent
            period hPeriod analysis second))
  uniformBound : ∀ parameter,
    ‖programPT12GaugeFixedLLFriedrichsD11LLResolvent
      period hPeriod analysis parameter‖ ≤
        ‖canonicalLLH1ToFluxL2 period hPeriod analysis‖ ^ 2
  operatorNormContinuous : Continuous (fun parameter =>
    programPT12GaugeFixedLLFriedrichsD11LLResolvent
      period hPeriod analysis parameter)
  compactResolvent : ∀ parameter,
    IsCompactOperator
      (programPT12GaugeFixedLLFriedrichsD11LLResolvent
        period hPeriod analysis parameter)

theorem programPT12GaugeFixedLLFriedrichsD11LLNormResolventFamily_gate
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    ProgramPT12GaugeFixedLLFriedrichsD11LLNormResolventFamilyCertificate4D
      period hPeriod analysis where
  resolventIdentity :=
    programPT12GaugeFixedLLFriedrichsD11LLResolvent_identity
      period hPeriod analysis
  uniformBound :=
    programPT12GaugeFixedLLFriedrichsD11LLResolvent_opNorm_le
      period hPeriod analysis
  operatorNormContinuous :=
    programPT12GaugeFixedLLFriedrichsD11LLResolvent_continuous
      period hPeriod analysis
  compactResolvent :=
    programPT12GaugeFixedLLFriedrichsD11LLResolvent_compact
      period hPeriod analysis

end
end P0EFTJanusProgramPT12LLFriedrichsNormResolventFamily4D
end JanusFormal
