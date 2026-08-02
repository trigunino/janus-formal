import Mathlib.Analysis.InnerProductSpace.PiL2
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalGHYSameActionHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalNullBoundaryReparametrizationHessian4D

/-!
# Finite boundary-reparametrization Hilbert Hessian

The exact one-face transgression theorem is assembled for independent real
normalization parameters on every finite null face.  Together with the
unchanged GHY term, this gives the actual finite boundary action on a genuine
finite-dimensional real Hilbert chart.  The action is constant, so its first
and second Frechet derivatives and its bounded Riesz representative vanish.

This covers null-generator reparametrizations only.  It does not identify a
normal displacement or a general deformation of the boundary geometry.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalBoundaryReparametrizationHilbertHessian4D

set_option autoImplicit false

noncomputable section

open scoped BigOperators ContDiff InnerProductSpace
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalGHYSameActionHessian4D
open P0EFTJanusProgramPGlobalNullBoundaryReparametrizationHessian4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Independent normalization parameter for every finite null face. -/
abbrev GlobalCandidateABoundaryReparametrizationHilbert
    (NullFace : Type*) :=
  EuclideanSpace Real NullFace

/-- Exact GHY plus finite-null-boundary action with independently rescaled
null-generator normalizations. -/
def globalCandidateABoundaryReparametrizationAction
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (parameters : GlobalCandidateABoundaryReparametrizationHilbert NullFace) :
    Real :=
  globalCandidateAGHYAction period hPeriod data +
    ∑ face : NullFace,
      finiteNullFaceReparametrizationActionCurve
        (data.nullActionFaces face) (parameters face)

/-- Independent face parameters specialize to the existing simultaneous
one-parameter curve. -/
theorem globalCandidateABoundaryReparametrizationAction_const_eq
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (parameter : Real) :
    globalCandidateABoundaryReparametrizationAction period hPeriod data
        (WithLp.toLp 2 (fun _face : NullFace => parameter)) =
      globalCandidateAGHYAction period hPeriod data +
        globalCandidateANullBoundaryReparametrizationActionCurve
          period hPeriod data parameter := by
  rfl

/-- The independently reparametrized action is exactly the original finite
GHY plus null-face/counterterm/joint boundary block. -/
theorem globalCandidateABoundaryReparametrizationAction_eq
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (contract :
      GlobalCandidateANullBoundaryReparametrizationIntegrability
        period hPeriod data)
    (parameters : GlobalCandidateABoundaryReparametrizationHilbert NullFace) :
    globalCandidateABoundaryReparametrizationAction period hPeriod data
        parameters =
      globalCandidateAGHYAction period hPeriod data +
        globalCandidateANullBoundaryAction period hPeriod data := by
  classical
  unfold globalCandidateABoundaryReparametrizationAction
    globalCandidateANullBoundaryAction
  congr 1
  apply Finset.sum_congr rfl
  intro face _
  exact finiteNullFaceReparametrizationActionCurve_eq
    (data.nullActionFaces face)
    (contract.toInterval period hPeriod face) (parameters face)

/-- The exact finite boundary action is smooth on the independent-face
Hilbert chart. -/
theorem globalCandidateABoundaryReparametrizationAction_contDiff
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (contract :
      GlobalCandidateANullBoundaryReparametrizationIntegrability
        period hPeriod data) :
    ContDiff Real ∞
      (globalCandidateABoundaryReparametrizationAction period hPeriod data) := by
  rw [show
    globalCandidateABoundaryReparametrizationAction period hPeriod data =
      fun _parameters =>
        globalCandidateAGHYAction period hPeriod data +
          globalCandidateANullBoundaryAction period hPeriod data by
    funext parameters
    exact globalCandidateABoundaryReparametrizationAction_eq
      period hPeriod data contract parameters]
  exact contDiff_const

theorem globalCandidateABoundaryReparametrizationAction_hasFDerivAt
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (contract :
      GlobalCandidateANullBoundaryReparametrizationIntegrability
        period hPeriod data)
    (parameters : GlobalCandidateABoundaryReparametrizationHilbert NullFace) :
    HasFDerivAt
      (globalCandidateABoundaryReparametrizationAction period hPeriod data)
      (0 : GlobalCandidateABoundaryReparametrizationHilbert NullFace →L[Real]
        Real) parameters := by
  rw [show
    globalCandidateABoundaryReparametrizationAction period hPeriod data =
      fun _varied =>
        globalCandidateAGHYAction period hPeriod data +
          globalCandidateANullBoundaryAction period hPeriod data by
    funext varied
    exact globalCandidateABoundaryReparametrizationAction_eq
      period hPeriod data contract varied]
  exact hasFDerivAt_const (𝕜 := Real)
    (globalCandidateAGHYAction period hPeriod data +
      globalCandidateANullBoundaryAction period hPeriod data) parameters

theorem globalCandidateABoundaryReparametrizationAction_fderiv_eq_zero
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (contract :
      GlobalCandidateANullBoundaryReparametrizationIntegrability
        period hPeriod data)
    (parameters : GlobalCandidateABoundaryReparametrizationHilbert NullFace) :
    fderiv Real
        (globalCandidateABoundaryReparametrizationAction period hPeriod data)
        parameters =
      0 :=
  (globalCandidateABoundaryReparametrizationAction_hasFDerivAt
    period hPeriod data contract parameters).fderiv

/-- Actual second Frechet derivative of the same exact boundary action. -/
def globalCandidateABoundaryReparametrizationHessian
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (parameters : GlobalCandidateABoundaryReparametrizationHilbert NullFace) :
    GlobalCandidateABoundaryReparametrizationHilbert NullFace →L[Real]
      GlobalCandidateABoundaryReparametrizationHilbert NullFace →L[Real]
        Real :=
  fderiv Real
    (fderiv Real
      (globalCandidateABoundaryReparametrizationAction period hPeriod data))
    parameters

theorem globalCandidateABoundaryReparametrizationHessian_eq_zero
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (contract :
      GlobalCandidateANullBoundaryReparametrizationIntegrability
        period hPeriod data)
    (parameters : GlobalCandidateABoundaryReparametrizationHilbert NullFace) :
    globalCandidateABoundaryReparametrizationHessian period hPeriod data
        parameters =
      0 := by
  unfold globalCandidateABoundaryReparametrizationHessian
  rw [show
    globalCandidateABoundaryReparametrizationAction period hPeriod data =
      fun _varied =>
        globalCandidateAGHYAction period hPeriod data +
          globalCandidateANullBoundaryAction period hPeriod data by
    funext varied
    exact globalCandidateABoundaryReparametrizationAction_eq
      period hPeriod data contract varied]
  simp

theorem globalCandidateABoundaryReparametrizationAction_hasSecondFDerivAt
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (contract :
      GlobalCandidateANullBoundaryReparametrizationIntegrability
        period hPeriod data)
    (parameters : GlobalCandidateABoundaryReparametrizationHilbert NullFace) :
    HasFDerivAt
      (fderiv Real
        (globalCandidateABoundaryReparametrizationAction period hPeriod data))
      (globalCandidateABoundaryReparametrizationHessian
        period hPeriod data parameters)
      parameters := by
  have hDerivative :
      fderiv Real
          (globalCandidateABoundaryReparametrizationAction
            period hPeriod data) =
        fun _varied =>
          (0 : GlobalCandidateABoundaryReparametrizationHilbert NullFace
            →L[Real] Real) := by
    funext varied
    exact globalCandidateABoundaryReparametrizationAction_fderiv_eq_zero
      period hPeriod data contract varied
  rw [hDerivative,
    globalCandidateABoundaryReparametrizationHessian_eq_zero
      period hPeriod data contract parameters]
  exact hasFDerivAt_const (𝕜 := Real)
    (0 : GlobalCandidateABoundaryReparametrizationHilbert NullFace →L[Real]
      Real) parameters

theorem globalCandidateABoundaryReparametrizationHessian_symmetric
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (contract :
      GlobalCandidateANullBoundaryReparametrizationIntegrability
        period hPeriod data)
    (parameters first second :
      GlobalCandidateABoundaryReparametrizationHilbert NullFace) :
    globalCandidateABoundaryReparametrizationHessian period hPeriod data
        parameters first second =
      globalCandidateABoundaryReparametrizationHessian period hPeriod data
        parameters second first := by
  rw [globalCandidateABoundaryReparametrizationHessian_eq_zero
    period hPeriod data contract parameters]
  rfl

/-- Bounded Riesz representative of the same-action boundary Hessian. -/
def globalCandidateABoundaryReparametrizationRieszOperator
    (NullFace : Type*) [Fintype NullFace] :
    GlobalCandidateABoundaryReparametrizationHilbert NullFace →L[Real]
      GlobalCandidateABoundaryReparametrizationHilbert NullFace :=
  0

theorem globalCandidateABoundaryReparametrizationRieszOperator_pairing
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (contract :
      GlobalCandidateANullBoundaryReparametrizationIntegrability
        period hPeriod data)
    (parameters first second :
      GlobalCandidateABoundaryReparametrizationHilbert NullFace) :
    inner Real
        (globalCandidateABoundaryReparametrizationRieszOperator NullFace first)
        second =
      globalCandidateABoundaryReparametrizationHessian period hPeriod data
        parameters first second := by
  rw [globalCandidateABoundaryReparametrizationHessian_eq_zero
    period hPeriod data contract parameters]
  simp [globalCandidateABoundaryReparametrizationRieszOperator]

/-- The zero boundary Riesz representative is self-adjoint. -/
theorem globalCandidateABoundaryReparametrizationRieszOperator_isSelfAdjoint
    (NullFace : Type*) [Fintype NullFace] :
    IsSelfAdjoint
      (globalCandidateABoundaryReparametrizationRieszOperator NullFace) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro first second
  simp [globalCandidateABoundaryReparametrizationRieszOperator]

end
end P0EFTJanusProgramPGlobalBoundaryReparametrizationHilbertHessian4D
end JanusFormal
