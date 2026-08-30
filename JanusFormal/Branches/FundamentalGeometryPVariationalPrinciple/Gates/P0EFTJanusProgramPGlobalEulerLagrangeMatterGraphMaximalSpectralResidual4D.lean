import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMatterFiniteSpectralKernel4D

/-!
# Maximal-graph SpinC spectral residual

The second component of the closed maximal graph is the full diagonal strong
residual.  Pairing it with the first component of every graph test represents
the actual graph-action Euler covector and separates the ambient Hilbert field.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMatterGraphMaximalSpectralResidual4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSeparatingPDEResidual4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance programPPrimitiveSpinCMatterModeDecidableEq :
    DecidableEq ProgramPPrimitiveSpinCMatterMode :=
  Classical.decEq _

local instance matterHilbertRealInnerProductSpace :
    InnerProductSpace Real ProgramPPrimitiveSpinCMatterHilbert :=
  InnerProductSpace.complexToReal

/-- Full strong residual carried by the maximal closed graph. -/
def programPPrimitiveSpinCMatterGraphMaximalSpectralResidual
    (massSquared : Real)
    (state : ProgramPPrimitiveSpinCMatterGraphDomain
      period hPeriod massSquared) :
    ProgramPPrimitiveSpinCMatterHilbert :=
  state.1.2

/-- Weak pairing of an ambient spectral residual with a maximal-graph test. -/
def programPPrimitiveSpinCMatterGraphMaximalSpectralResidualPairing
    (massSquared : Real)
    (residual : ProgramPPrimitiveSpinCMatterHilbert)
    (direction : ProgramPPrimitiveSpinCMatterGraphDomain
      period hPeriod massSquared) : Real :=
  inner Real direction.1.1 residual

/-- The maximal spectral residual represents the true graph Euler covector. -/
theorem programPPrimitiveSpinCMatterGraphForm_eq_maximalResidualPairing
    (massSquared : Real)
    (state direction : ProgramPPrimitiveSpinCMatterGraphDomain
      period hPeriod massSquared) :
    programPPrimitiveSpinCMatterGraphForm period hPeriod massSquared
        state direction =
      programPPrimitiveSpinCMatterGraphMaximalSpectralResidualPairing
        period hPeriod massSquared
          (programPPrimitiveSpinCMatterGraphMaximalSpectralResidual
            period hPeriod massSquared state)
          direction := by
  rw [programPPrimitiveSpinCMatterGraphForm_comm,
    programPPrimitiveSpinCMatterGraphForm_apply]
  rfl

/-- Tests from the maximal graph separate every ambient spectral residual. -/
theorem programPPrimitiveSpinCMatterGraphMaximalResidualPairing_separates
    (massSquared : Real)
    (residual : ProgramPPrimitiveSpinCMatterHilbert) :
    (∀ direction : ProgramPPrimitiveSpinCMatterGraphDomain
        period hPeriod massSquared,
      programPPrimitiveSpinCMatterGraphMaximalSpectralResidualPairing
        period hPeriod massSquared residual direction = 0) ↔
      residual = 0 := by
  constructor
  · intro hPairing
    ext mode
    let coefficients : ProgramPPrimitiveSpinCMatterFiniteCoefficients :=
      Finsupp.single mode (residual mode)
    let direction := programPPrimitiveSpinCMatterGraphFinite period hPeriod
      massSquared coefficients
    have hMode := hPairing direction
    change inner Real
      (programPPrimitiveSpinCMatterFiniteHilbertEmbedding coefficients)
      residual = 0 at hMode
    have hSingle :
        programPPrimitiveSpinCMatterFiniteHilbertEmbedding coefficients =
          (lp.single 2 mode (residual mode) :
            ProgramPPrimitiveSpinCMatterHilbert) := by
      ext other
      rw [programPPrimitiveSpinCMatterFiniteHilbertEmbedding_apply]
      change (Finsupp.single mode (residual mode)) other =
        (lp.single 2 mode (residual mode) :
          ProgramPPrimitiveSpinCMatterHilbert) other
      by_cases hOther : other = mode
      · subst other
        simp
      · rw [Finsupp.single_eq_of_ne hOther]
        simp [hOther]
    rw [hSingle, real_inner_eq_re_inner, lp.inner_single_left] at hMode
    rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow,
      RCLike.ofReal_re] at hMode
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hMode)
  · intro hResidual direction
    rw [hResidual]
    simp [programPPrimitiveSpinCMatterGraphMaximalSpectralResidualPairing]

/-- The explicit maximal residual and pairing instantiate the separating
interface for the actual graph-action Euler covector. -/
def programPPrimitiveSpinCMatterGraphMaximalSpectralResidualRepresentation
    (massSquared : Real)
    (state : ProgramPPrimitiveSpinCMatterGraphDomain
      period hPeriod massSquared) :
    SeparatingPDEResidualRepresentation
      (programPPrimitiveSpinCMatterGraphForm period hPeriod massSquared
        state).toLinearMap where
  Residual := ProgramPPrimitiveSpinCMatterHilbert
  zeroResidual := 0
  residual := programPPrimitiveSpinCMatterGraphMaximalSpectralResidual
    period hPeriod massSquared state
  pairing := programPPrimitiveSpinCMatterGraphMaximalSpectralResidualPairing
    period hPeriod massSquared
  represents := programPPrimitiveSpinCMatterGraphForm_eq_maximalResidualPairing
    period hPeriod massSquared state
  separates :=
    programPPrimitiveSpinCMatterGraphMaximalResidualPairing_separates
      period hPeriod massSquared
        (programPPrimitiveSpinCMatterGraphMaximalSpectralResidual period
          hPeriod massSquared state)

/-- Pointwise, the maximal residual is exactly multiplication by the spectral
weight `2D + m²`. -/
theorem programPPrimitiveSpinCMatterGraphMaximalSpectralResidual_apply
    (massSquared : Real)
    (state : ProgramPPrimitiveSpinCMatterGraphDomain
      period hPeriod massSquared)
    (mode : ProgramPPrimitiveSpinCMatterMode) :
    programPPrimitiveSpinCMatterGraphMaximalSpectralResidual period hPeriod
        massSquared state mode =
      ((programPPrimitiveSpinCMatterHessianWeight period hPeriod massSquared
        mode : Real) : Complex) * state.1.1 mode :=
  P0EFTJanusComplexDiagonalGraphFredholm4D.complexDiagonalGraphDomain_relation
    ProgramPPrimitiveSpinCMatterMode
      (programPPrimitiveSpinCMatterHessianWeight period hPeriod massSquared)
      state mode

/-- Stationarity of the actual maximal graph action is the full strong
spectral equation. -/
theorem programPPrimitiveSpinCMatterGraphAction_fderiv_eq_zero_iff_maximalResidual
    (massSquared : Real)
    (state : ProgramPPrimitiveSpinCMatterGraphDomain
      period hPeriod massSquared) :
    fderiv Real
        (programPPrimitiveSpinCMatterGraphAction period hPeriod massSquared)
        state = 0 ↔
      programPPrimitiveSpinCMatterGraphMaximalSpectralResidual period hPeriod
        massSquared state = 0 := by
  rw [programPPrimitiveSpinCMatterGraphAction_fderiv]
  constructor
  · intro hEuler
    apply
      (programPPrimitiveSpinCMatterGraphMaximalSpectralResidualRepresentation
        period hPeriod massSquared state).separates.mp
    intro direction
    rw [←
      (programPPrimitiveSpinCMatterGraphMaximalSpectralResidualRepresentation
        period hPeriod massSquared state).represents direction]
    rw [hEuler]
    rfl
  · intro hResidual
    apply ContinuousLinearMap.ext
    intro direction
    rw [programPPrimitiveSpinCMatterGraphForm_eq_maximalResidualPairing]
    exact
      (programPPrimitiveSpinCMatterGraphMaximalSpectralResidualRepresentation
        period hPeriod massSquared state).separates.mpr hResidual direction

/-- If no spectral weight vanishes, the maximal strong residual has trivial
kernel. -/
theorem programPPrimitiveSpinCMatterGraphMaximalResidual_eq_zero_iff_state_eq_zero
    (massSquared : Real)
    (hNonresonant : ∀ mode, programPPrimitiveSpinCMatterHessianWeight
      period hPeriod massSquared mode ≠ 0)
    (state : ProgramPPrimitiveSpinCMatterGraphDomain
      period hPeriod massSquared) :
    programPPrimitiveSpinCMatterGraphMaximalSpectralResidual period hPeriod
        massSquared state = 0 ↔ state = 0 := by
  constructor
  · intro hResidual
    apply Subtype.ext
    apply Prod.ext
    · ext mode
      have hApply := congrArg
        (fun residual : ProgramPPrimitiveSpinCMatterHilbert ↦ residual mode)
        hResidual
      have hRelation :=
        programPPrimitiveSpinCMatterGraphMaximalSpectralResidual_apply
          period hPeriod massSquared state mode
      rw [hApply] at hRelation
      exact (mul_eq_zero.mp hRelation.symm).resolve_left
        (Complex.ofReal_ne_zero.mpr (hNonresonant mode))
    · exact hResidual
  · intro hState
    subst state
    rfl

/-- Off resonance, zero is the unique stationary point of the actual maximal
graph action. -/
theorem programPPrimitiveSpinCMatterGraphAction_fderiv_eq_zero_iff_state_eq_zero_of_nonresonant
    (massSquared : Real)
    (hNonresonant : ∀ mode, programPPrimitiveSpinCMatterHessianWeight
      period hPeriod massSquared mode ≠ 0)
    (state : ProgramPPrimitiveSpinCMatterGraphDomain
      period hPeriod massSquared) :
    fderiv Real
        (programPPrimitiveSpinCMatterGraphAction period hPeriod massSquared)
        state = 0 ↔ state = 0 := by
  rw [programPPrimitiveSpinCMatterGraphAction_fderiv_eq_zero_iff_maximalResidual
    period hPeriod massSquared state]
  exact
    programPPrimitiveSpinCMatterGraphMaximalResidual_eq_zero_iff_state_eq_zero
      period hPeriod massSquared hNonresonant state

end
end P0EFTJanusProgramPGlobalEulerLagrangeMatterGraphMaximalSpectralResidual4D
end JanusFormal
