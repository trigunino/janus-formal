import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1Fredholm4D

/-!
# Unconditional coercive variational closure of the static scalar sector

The positive time-static Jacobi form is the Hessian of the unchanged scalar
action.  On its energy completion the Riesz operator is the identity.  This
gives, without an additional analytic hypothesis:

* coercivity with constant one;
* a unique solution for every energy-dual source;
* the exact completed-square identity and unique global minimization;
* a nonnegative Gaussian response;
* self-adjoint Fredholm closure of index zero.

Every finite smooth-mode Galerkin cutoff additionally has a compact inverse.
This is the positive static sector, not an ellipticization of the Lorentzian
wave operator.  Compact resolvent on a bulk `L²` space still requires a
separate compact energy-to-`L²` embedding.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarStaticCoerciveVariationalClosure4D

set_option autoImplicit false
noncomputable section

open scoped InnerProduct
open P0EFTJanusMappingTorusGlobalHolonomicScalarWeakJacobiRiesz4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1Fredholm4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev StaticEnergy
    (data : PositiveStaticGlobalScalarData period hPeriod) :=
  StaticScalarEnergyH1 period hPeriod data

/-- The static Jacobi Riesz operator has coercivity constant one. -/
theorem completedStaticScalarJacobiOperator_coercive
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (field : StaticEnergy period hPeriod data) :
    ‖field‖ ^ 2 ≤
      inner Real
        (completedStaticScalarJacobiOperator period hPeriod data field) field := by
  rw [completedStaticScalarJacobiOperator_apply,
    real_inner_self_eq_norm_sq]

/-- Energy-space source action associated with the unchanged static Hessian. -/
def staticScalarSourceAction
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (source field : StaticEnergy period hPeriod data) : Real :=
  (1 / 2 : Real) * ‖field‖ ^ 2 - inner Real source field

/-- The source solution is the inverse of the completed Jacobi operator. -/
def staticScalarSourceSolution
    (data : PositiveStaticGlobalScalarData period hPeriod) :
    StaticEnergy period hPeriod data →L[Real]
      StaticEnergy period hPeriod data :=
  ContinuousLinearMap.id Real (StaticEnergy period hPeriod data)

@[simp]
theorem staticScalarSourceSolution_apply
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (source : StaticEnergy period hPeriod data) :
    staticScalarSourceSolution period hPeriod data source = source :=
  rfl

/-- Strong source equation on the energy completion. -/
theorem staticScalarSourceSolution_equation
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (source : StaticEnergy period hPeriod data) :
    completedStaticScalarJacobiOperator period hPeriod data
        (staticScalarSourceSolution period hPeriod data source) =
      source := by
  rfl

/-- Exact square completion for the sourced static action. -/
theorem staticScalarSourceAction_completion
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (source field : StaticEnergy period hPeriod data) :
    staticScalarSourceAction period hPeriod data source field =
      staticScalarSourceAction period hPeriod data source
          (staticScalarSourceSolution period hPeriod data source) +
        (1 / 2 : Real) *
          ‖field - staticScalarSourceSolution period hPeriod data source‖ ^ 2 := by
  simp only [staticScalarSourceAction, staticScalarSourceSolution_apply]
  rw [norm_sub_sq_real, real_inner_self_eq_norm_sq,
    real_inner_comm field source]
  ring

/-- The source solution is the unique global minimizer. -/
theorem staticScalarSourceSolution_unique_minimizer
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (source : StaticEnergy period hPeriod data) :
    (∀ field : StaticEnergy period hPeriod data,
      staticScalarSourceAction period hPeriod data source
          (staticScalarSourceSolution period hPeriod data source) ≤
        staticScalarSourceAction period hPeriod data source field) ∧
      (∀ field : StaticEnergy period hPeriod data,
        staticScalarSourceAction period hPeriod data source field =
            staticScalarSourceAction period hPeriod data source
              (staticScalarSourceSolution period hPeriod data source) →
          field = staticScalarSourceSolution period hPeriod data source) := by
  constructor
  · intro field
    rw [staticScalarSourceAction_completion period hPeriod data source field]
    nlinarith [sq_nonneg
      ‖field - staticScalarSourceSolution period hPeriod data source‖]
  · intro field hAction
    rw [staticScalarSourceAction_completion period hPeriod data source field]
      at hAction
    have hNorm :
        ‖field - staticScalarSourceSolution period hPeriod data source‖ = 0 := by
      nlinarith [norm_nonneg
        (field - staticScalarSourceSolution period hPeriod data source)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hNorm)

/-- Gaussian response generated by the static source problem. -/
def staticScalarGaussianResponse
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (source : StaticEnergy period hPeriod data) : Real :=
  (1 / 2 : Real) * ‖source‖ ^ 2

theorem staticScalarGaussianResponse_nonneg
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (source : StaticEnergy period hPeriod data) :
    0 ≤ staticScalarGaussianResponse period hPeriod data source := by
  unfold staticScalarGaussianResponse
  positivity

/-- The Gaussian response is minus the on-shell source action. -/
theorem staticScalarGaussianResponse_eq_neg_onShell
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (source : StaticEnergy period hPeriod data) :
    staticScalarGaussianResponse period hPeriod data source =
      -staticScalarSourceAction period hPeriod data source
        (staticScalarSourceSolution period hPeriod data source) := by
  simp only [staticScalarGaussianResponse, staticScalarSourceAction,
    staticScalarSourceSolution_apply, real_inner_self_eq_norm_sq]
  ring

/-- Complete nonconditional analytic certificate in the positive static
sector.  Its only inputs are the physical positivity data used to define that
sector. -/
theorem completed_static_scalar_coercive_variational_closure
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (source : StaticEnergy period hPeriod data) :
    IsSelfAdjoint
        (completedStaticScalarJacobiOperator period hPeriod data) ∧
      completedStaticScalarJacobiIndex period hPeriod data = 0 ∧
      (∀ field : StaticEnergy period hPeriod data,
        ‖field‖ ^ 2 ≤
          inner Real
            (completedStaticScalarJacobiOperator period hPeriod data field)
            field) ∧
      completedStaticScalarJacobiOperator period hPeriod data
          (staticScalarSourceSolution period hPeriod data source) = source ∧
      (∀ field : StaticEnergy period hPeriod data,
        staticScalarSourceAction period hPeriod data source
            (staticScalarSourceSolution period hPeriod data source) ≤
          staticScalarSourceAction period hPeriod data source field) ∧
      (∀ field : StaticEnergy period hPeriod data,
        staticScalarSourceAction period hPeriod data source field =
            staticScalarSourceAction period hPeriod data source
              (staticScalarSourceSolution period hPeriod data source) →
          field = staticScalarSourceSolution period hPeriod data source) ∧
      0 ≤ staticScalarGaussianResponse period hPeriod data source := by
  exact
    ⟨completedStaticScalarJacobiOperator_isSelfAdjoint period hPeriod data,
      completedStaticScalarJacobiIndex_zero period hPeriod data,
      completedStaticScalarJacobiOperator_coercive period hPeriod data,
      staticScalarSourceSolution_equation period hPeriod data source,
      (staticScalarSourceSolution_unique_minimizer
        period hPeriod data source).1,
      (staticScalarSourceSolution_unique_minimizer
        period hPeriod data source).2,
      staticScalarGaussianResponse_nonneg period hPeriod data source⟩

/-- Exact compactness frontier on the full static energy completion: because
the source inverse is the identity, it is compact exactly in finite
dimension. -/
theorem staticScalarSourceSolution_isCompact_iff_finiteDimensional
    (data : PositiveStaticGlobalScalarData period hPeriod) :
    IsCompactOperator (staticScalarSourceSolution period hPeriod data) ↔
      FiniteDimensional Real (StaticEnergy period hPeriod data) := by
  change IsCompactOperator
      (fun field : StaticEnergy period hPeriod data => field) ↔ _
  exact isCompactOperator_id_iff_finiteDimensional

/-- Span of finitely many smooth fields inside the genuine static energy
completion. -/
abbrev StaticScalarSmoothGalerkinSpace
    (data : PositiveStaticGlobalScalarData period hPeriod)
    {modeCount : Nat}
    (modes : Fin modeCount → StaticGlobalScalarTest period hPeriod data) :=
  Submodule.span Real
    (Set.range fun index =>
      staticScalarEnergyEmbedding period hPeriod data (modes index))

noncomputable instance staticScalarSmoothGalerkinSpace_finiteDimensional
    (data : PositiveStaticGlobalScalarData period hPeriod)
    {modeCount : Nat}
    (modes : Fin modeCount → StaticGlobalScalarTest period hPeriod data) :
    FiniteDimensional Real
      (StaticScalarSmoothGalerkinSpace period hPeriod data modes) :=
  FiniteDimensional.span_of_finite Real (Set.finite_range _)

/-- A selected smooth mode as a vector of its Galerkin span. -/
def staticScalarGalerkinMode
    (data : PositiveStaticGlobalScalarData period hPeriod)
    {modeCount : Nat}
    (modes : Fin modeCount → StaticGlobalScalarTest period hPeriod data)
    (index : Fin modeCount) :
    StaticScalarSmoothGalerkinSpace period hPeriod data modes :=
  ⟨staticScalarEnergyEmbedding period hPeriod data (modes index),
    Submodule.subset_span (Set.mem_range_self index)⟩

/-- Static Jacobi operator restricted to a finite smooth-mode cutoff. -/
def staticScalarGalerkinJacobiOperator
    (data : PositiveStaticGlobalScalarData period hPeriod)
    {modeCount : Nat}
    (modes : Fin modeCount → StaticGlobalScalarTest period hPeriod data) :
    StaticScalarSmoothGalerkinSpace period hPeriod data modes →L[Real]
      StaticScalarSmoothGalerkinSpace period hPeriod data modes :=
  ContinuousLinearMap.id Real
    (StaticScalarSmoothGalerkinSpace period hPeriod data modes)

/-- On selected smooth modes the Galerkin pairing is exactly the Jacobi
Hessian of the unchanged action. -/
theorem staticScalarGalerkinJacobiOperator_mode_pairing
    (data : PositiveStaticGlobalScalarData period hPeriod)
    {modeCount : Nat}
    (modes : Fin modeCount → StaticGlobalScalarTest period hPeriod data)
    (first second : Fin modeCount) :
    inner Real
        (staticScalarGalerkinJacobiOperator period hPeriod data modes
          (staticScalarGalerkinMode period hPeriod data modes first))
        (staticScalarGalerkinMode period hPeriod data modes second) =
      globalHolonomicScalarJacobiForm period hPeriod data.formData
        (modes first).toField (modes second).toField := by
  change inner Real
      (staticScalarEnergyEmbedding period hPeriod data (modes first))
      (staticScalarEnergyEmbedding period hPeriod data (modes second)) = _
  exact strongStaticScalarJacobiRiesz_smooth_pairing
    period hPeriod data (modes first) (modes second)

/-- At zero spectral parameter the finite-cutoff resolvent is the identity. -/
def staticScalarGalerkinResolvent
    (data : PositiveStaticGlobalScalarData period hPeriod)
    {modeCount : Nat}
    (modes : Fin modeCount → StaticGlobalScalarTest period hPeriod data) :
    StaticScalarSmoothGalerkinSpace period hPeriod data modes →L[Real]
      StaticScalarSmoothGalerkinSpace period hPeriod data modes :=
  ContinuousLinearMap.id Real
    (StaticScalarSmoothGalerkinSpace period hPeriod data modes)

/-- The finite smooth-mode resolvent is compact, with no Rellich assumption. -/
theorem staticScalarGalerkinResolvent_isCompact
    (data : PositiveStaticGlobalScalarData period hPeriod)
    {modeCount : Nat}
    (modes : Fin modeCount → StaticGlobalScalarTest period hPeriod data) :
    IsCompactOperator
      (staticScalarGalerkinResolvent period hPeriod data modes) := by
  exact isCompactOperator_of_locallyCompactSpace_dom
    (staticScalarGalerkinResolvent period hPeriod data modes)

/-- Full finite-cutoff compact-resolvent certificate. -/
theorem static_scalar_galerkin_compact_resolvent_closure
    (data : PositiveStaticGlobalScalarData period hPeriod)
    {modeCount : Nat}
    (modes : Fin modeCount → StaticGlobalScalarTest period hPeriod data) :
    IsSelfAdjoint
        (staticScalarGalerkinJacobiOperator period hPeriod data modes) ∧
      IsCompactOperator
        (staticScalarGalerkinResolvent period hPeriod data modes) ∧
      (staticScalarGalerkinJacobiOperator period hPeriod data modes).comp
          (staticScalarGalerkinResolvent period hPeriod data modes) =
        ContinuousLinearMap.id Real
          (StaticScalarSmoothGalerkinSpace period hPeriod data modes) ∧
      (staticScalarGalerkinResolvent period hPeriod data modes).comp
          (staticScalarGalerkinJacobiOperator period hPeriod data modes) =
        ContinuousLinearMap.id Real
          (StaticScalarSmoothGalerkinSpace period hPeriod data modes) := by
  refine ⟨?_, staticScalarGalerkinResolvent_isCompact
    period hPeriod data modes, rfl, rfl⟩
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro first second
  rfl

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarStaticCoerciveVariationalClosure4D
end JanusFormal
