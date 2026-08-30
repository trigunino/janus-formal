import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMatterGraphMaximalSpectralResidual4D

/-!
# Kernel of the maximal-graph SpinC spectral residual

The full closed-graph critical locus consists exactly of states supported on
the mass shell.  Resonant modes therefore give nonzero stationary states.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMatterGraphMaximalSpectralKernel4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalEulerLagrangeMatterGraphMaximalSpectralResidual4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance programPPrimitiveSpinCMatterModeDecidableEq :
    DecidableEq ProgramPPrimitiveSpinCMatterMode :=
  Classical.decEq _

local instance matterHilbertRealInnerProductSpace :
    InnerProductSpace Real ProgramPPrimitiveSpinCMatterHilbert :=
  InnerProductSpace.complexToReal

/-- Exact mass shell of the maximal diagonal SpinC graph. -/
def programPPrimitiveSpinCMatterGraphMaximalSpectralMassShell
    (massSquared : Real) : Set ProgramPPrimitiveSpinCMatterMode :=
  {mode | programPPrimitiveSpinCMatterHessianWeight
    period hPeriod massSquared mode = 0}

/-- The maximal strong residual vanishes exactly on graph states supported on
the spectral mass shell. -/
theorem programPPrimitiveSpinCMatterGraphMaximalResidual_eq_zero_iff_support
    (massSquared : Real)
    (state : ProgramPPrimitiveSpinCMatterGraphDomain
      period hPeriod massSquared) :
    programPPrimitiveSpinCMatterGraphMaximalSpectralResidual period hPeriod
        massSquared state = 0 ↔
      {mode | state.1.1 mode ≠ 0} ⊆
        programPPrimitiveSpinCMatterGraphMaximalSpectralMassShell period
          hPeriod massSquared := by
  constructor
  · intro hResidual mode hMode
    have hApply := congrArg
      (fun residual : ProgramPPrimitiveSpinCMatterHilbert ↦ residual mode)
      hResidual
    rw [programPPrimitiveSpinCMatterGraphMaximalSpectralResidual_apply]
      at hApply
    change programPPrimitiveSpinCMatterHessianWeight period hPeriod
      massSquared mode = 0
    exact Complex.ofReal_eq_zero.mp
      ((mul_eq_zero.mp hApply).resolve_right hMode)
  · intro hSupport
    ext mode
    rw [programPPrimitiveSpinCMatterGraphMaximalSpectralResidual_apply]
    by_cases hWeight : programPPrimitiveSpinCMatterHessianWeight period
        hPeriod massSquared mode = 0
    · simp [hWeight]
    · have hState : state.1.1 mode = 0 := by
        by_contra hMode
        exact hWeight (hSupport hMode)
      simp [hState]

/-- Stationarity of the maximal graph action is support on the exact mass
shell. -/
theorem programPPrimitiveSpinCMatterGraphAction_fderiv_eq_zero_iff_support
    (massSquared : Real)
    (state : ProgramPPrimitiveSpinCMatterGraphDomain
      period hPeriod massSquared) :
    fderiv Real
        (programPPrimitiveSpinCMatterGraphAction period hPeriod massSquared)
        state = 0 ↔
      {mode | state.1.1 mode ≠ 0} ⊆
        programPPrimitiveSpinCMatterGraphMaximalSpectralMassShell period
          hPeriod massSquared := by
  rw [programPPrimitiveSpinCMatterGraphAction_fderiv_eq_zero_iff_maximalResidual
    period hPeriod massSquared state]
  exact programPPrimitiveSpinCMatterGraphMaximalResidual_eq_zero_iff_support
    period hPeriod massSquared state

/-- Canonical maximal-graph state concentrated on one resonant mode. -/
def programPPrimitiveSpinCMatterGraphMaximalResonantState
    (massSquared : Real)
    (mode : ProgramPPrimitiveSpinCMatterMode) :
    ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod massSquared :=
  programPPrimitiveSpinCMatterGraphSingle period hPeriod massSquared
    mode.1 mode.2 1

theorem programPPrimitiveSpinCMatterGraphMaximalResonantState_ne_zero
    (massSquared : Real)
    (mode : ProgramPPrimitiveSpinCMatterMode) :
    programPPrimitiveSpinCMatterGraphMaximalResonantState period hPeriod
      massSquared mode ≠ 0 := by
  intro hZero
  have hMode := congrArg
    (fun state : ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
      massSquared ↦ state.1.1 mode) hZero
  change (lp.single 2 mode 1 : ProgramPPrimitiveSpinCMatterHilbert) mode = 0
    at hMode
  simp at hMode

/-- Every resonant mode produces an explicit nonzero stationary state of the
maximal graph action. -/
theorem programPPrimitiveSpinCMatterGraphAction_has_nonzero_stationary_of_resonant
    (massSquared : Real)
    (mode : ProgramPPrimitiveSpinCMatterMode)
    (hResonant : programPPrimitiveSpinCMatterHessianWeight period hPeriod
      massSquared mode = 0) :
    let state := programPPrimitiveSpinCMatterGraphMaximalResonantState period
      hPeriod massSquared mode
    state ≠ 0 ∧
      fderiv Real
        (programPPrimitiveSpinCMatterGraphAction period hPeriod massSquared)
        state = 0 := by
  dsimp
  refine ⟨programPPrimitiveSpinCMatterGraphMaximalResonantState_ne_zero
    period hPeriod massSquared mode, ?_⟩
  rw [programPPrimitiveSpinCMatterGraphAction_fderiv_eq_zero_iff_support]
  intro other hOther
  change programPPrimitiveSpinCMatterHessianWeight period hPeriod
    massSquared other = 0
  have hOtherEq : other = mode := by
    by_contra hNe
    apply hOther
    change (lp.single 2 mode 1 : ProgramPPrimitiveSpinCMatterHilbert) other = 0
    simp [hNe]
  simpa [hOtherEq] using hResonant

end
end P0EFTJanusProgramPGlobalEulerLagrangeMatterGraphMaximalSpectralKernel4D
end JanusFormal
