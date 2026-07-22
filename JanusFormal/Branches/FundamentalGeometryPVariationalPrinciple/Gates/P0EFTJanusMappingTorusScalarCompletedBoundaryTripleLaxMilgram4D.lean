import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.Adjoint
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCompletedBoundaryTripleResolvent4D

/-!
# Lax--Milgram construction on a completed scalar boundary triple

A completed Lagrangian domain is a closed subspace of the maximal graph Hilbert
space.  If the shifted bulk pairing is represented by a bounded coercive
bilinear form on that domain, Lax--Milgram solves the source equation.

Density of the ambient domain inclusion upgrades the weak equation to the strong
shifted equation.  The same coercivity estimate gives an explicit lower norm
bound for the shifted operator, so the result is exactly the
`LagrangianCoerciveSurjectiveAt` package used by the direct resolvent theory.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarCompletedBoundaryTripleLaxMilgram4D

set_option autoImplicit false
noncomputable section

open Set Topology
open scoped InnerProduct
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleResolvent4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

namespace CanonicalScalarCompletedBoundaryTripleData

/-- Completeness of every closed completed Lagrangian domain. -/
@[implicit_reducible]
noncomputable def lagrangianDomainCompleteSpace
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace) :
    CompleteSpace (triple.lagrangianDomainSubmodule condition) := by
  letI : CompleteSpace (CanonicalScalarGreenCoreGraphSpace core) :=
    canonicalScalarGreenCoreGraphCompleteSpace core
  exact (triple.lagrangianDomain_isClosed condition).completeSpace_coe

/-- Lax--Milgram data for one shifted completed Lagrangian realization. -/
structure LagrangianLaxMilgramData
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real) where
  form : triple.lagrangianDomainSubmodule condition →L[Real]
    triple.lagrangianDomainSubmodule condition →L[Real] Real
  form_eq_pairing : ∀ first second,
    form first second =
      inner Real
        (triple.lagrangianShiftedOperator
          condition spectralParameter first)
        (triple.lagrangianInclusion condition second)
  constant : Real
  constant_pos : 0 < constant
  coercive : ∀ field,
    constant * ‖field‖ * ‖field‖ ≤ form field field
  dense : DenseRange (triple.lagrangianInclusion condition)

namespace LagrangianLaxMilgramData

/-- The bounded bilinear form is coercive in Mathlib's sense. -/
theorem isCoercive
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (data : triple.LagrangianLaxMilgramData
      condition spectralParameter) :
    IsCoercive data.form :=
  ⟨data.constant, data.constant_pos, data.coercive⟩

/-- Riesz representative of an ambient source restricted to the Lagrangian
domain. -/
noncomputable def sourceRepresenter
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (data : triple.LagrangianLaxMilgramData
      condition spectralParameter) :
    Ambient →L[Real] triple.lagrangianDomainSubmodule condition := by
  letI : CompleteSpace (triple.lagrangianDomainSubmodule condition) :=
    triple.lagrangianDomainCompleteSpace condition
  exact (triple.lagrangianInclusion condition)†

/-- Lax--Milgram solution map. -/
noncomputable def solution
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (data : triple.LagrangianLaxMilgramData
      condition spectralParameter) :
    Ambient →L[Real] triple.lagrangianDomainSubmodule condition := by
  letI : CompleteSpace (triple.lagrangianDomainSubmodule condition) :=
    triple.lagrangianDomainCompleteSpace condition
  exact (data.isCoercive triple condition spectralParameter)
    |>.continuousLinearEquivOfBilin.symm.toContinuousLinearMap.comp
      (data.sourceRepresenter triple condition spectralParameter)

/-- Weak source equation solved by the Lax--Milgram field. -/
theorem solution_weak
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (data : triple.LagrangianLaxMilgramData
      condition spectralParameter)
    (source : Ambient)
    (test : triple.lagrangianDomainSubmodule condition) :
    inner Real
        (triple.lagrangianShiftedOperator condition spectralParameter
          (data.solution triple condition spectralParameter source))
        (triple.lagrangianInclusion condition test) =
      inner Real source (triple.lagrangianInclusion condition test) := by
  letI : CompleteSpace (triple.lagrangianDomainSubmodule condition) :=
    triple.lagrangianDomainCompleteSpace condition
  have hLax := IsCoercive.continuousLinearEquivOfBilin_apply
    (data.isCoercive triple condition spectralParameter)
    (data.solution triple condition spectralParameter source) test
  have hInverse :
      (data.isCoercive triple condition spectralParameter)
          |>.continuousLinearEquivOfBilin
            (data.solution triple condition spectralParameter source) =
        data.sourceRepresenter triple condition spectralParameter source := by
    exact ContinuousLinearEquiv.apply_symm_apply _ _
  rw [hInverse] at hLax
  rw [data.form_eq_pairing] at hLax
  rw [ContinuousLinearMap.adjoint_inner_left] at hLax
  exact hLax.symm

/-- The weak source equation is the strong shifted equation by density. -/
theorem solution_strong
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (data : triple.LagrangianLaxMilgramData
      condition spectralParameter)
    (source : Ambient) :
    triple.lagrangianShiftedOperator condition spectralParameter
        (data.solution triple condition spectralParameter source) = source := by
  let residual : Ambient :=
    triple.lagrangianShiftedOperator condition spectralParameter
        (data.solution triple condition spectralParameter source) - source
  have hOrthogonal
      (test : triple.lagrangianDomainSubmodule condition) :
      inner Real residual (triple.lagrangianInclusion condition test) = 0 := by
    unfold residual
    rw [inner_sub_left, data.solution_weak]
    exact sub_self _
  let good : Set Ambient := {test | inner Real residual test = 0}
  have hGoodClosed : IsClosed good := by
    dsimp [good]
    apply isClosed_eq <;> fun_prop
  have hRange : Set.range (triple.lagrangianInclusion condition) ⊆ good := by
    rintro test ⟨domainTest, rfl⟩
    exact hOrthogonal domainTest
  have hClosure : closure
      (Set.range (triple.lagrangianInclusion condition)) = Set.univ :=
    data.dense.closure_range
  have hResidualMem : residual ∈ closure
      (Set.range (triple.lagrangianInclusion condition)) := by
    rw [hClosure]
    trivial
  have hSelf : inner Real residual residual = 0 :=
    (closure_minimal hRange hGoodClosed) hResidualMem
  have hNormSq : ‖residual‖ ^ 2 = 0 := by
    simpa [real_inner_self_eq_norm_sq] using hSelf
  have hResidualZero : residual = 0 :=
    norm_eq_zero.mp (by nlinarith [sq_nonneg ‖residual‖])
  exact sub_eq_zero.mp hResidualZero

/-- The direct shifted operator is surjective. -/
theorem shifted_surjective
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (data : triple.LagrangianLaxMilgramData
      condition spectralParameter) :
    Function.Surjective
      (triple.lagrangianShiftedOperator condition spectralParameter) := by
  intro source
  exact ⟨data.solution triple condition spectralParameter source,
    data.solution_strong triple condition spectralParameter source⟩

/-- A positive normalization for the domain inclusion norm. -/
def inclusionNormControl
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace) : Real :=
  max 1 ‖triple.lagrangianInclusion condition‖

/-- The inclusion normalization is strictly positive. -/
theorem inclusionNormControl_pos
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace) :
    0 < triple.inclusionNormControl condition :=
  lt_of_lt_of_le zero_lt_one (le_max_left _ _)

/-- Explicit coercive constant for the shifted operator norm. -/
def shiftedCoerciveConstant
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (data : triple.LagrangianLaxMilgramData
      condition spectralParameter) : Real :=
  data.constant / triple.inclusionNormControl condition

/-- The shifted coercive constant is positive. -/
theorem shiftedCoerciveConstant_pos
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (data : triple.LagrangianLaxMilgramData
      condition spectralParameter) :
    0 < data.shiftedCoerciveConstant triple condition spectralParameter :=
  div_pos data.constant_pos (triple.inclusionNormControl_pos condition)

/-- Lax--Milgram coercivity implies the required shifted-operator norm bound. -/
theorem shifted_lower_bound
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (data : triple.LagrangianLaxMilgramData
      condition spectralParameter)
    (field : triple.lagrangianDomainSubmodule condition) :
    data.shiftedCoerciveConstant triple condition spectralParameter * ‖field‖ ≤
      ‖triple.lagrangianShiftedOperator
        condition spectralParameter field‖ := by
  by_cases hField : ‖field‖ = 0
  · simp [hField]
  have hFieldPos : 0 < ‖field‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hField)
  have hCoercive := data.coercive field
  rw [data.form_eq_pairing] at hCoercive
  have hCauchy :
      inner Real
          (triple.lagrangianShiftedOperator condition spectralParameter field)
          (triple.lagrangianInclusion condition field) ≤
        ‖triple.lagrangianShiftedOperator condition spectralParameter field‖ *
          ‖triple.lagrangianInclusion condition field‖ :=
    real_inner_le_norm _ _
  have hInclusion := (triple.lagrangianInclusion condition).le_opNorm field
  have hNormOperator :
      ‖triple.lagrangianInclusion condition‖ ≤
        triple.inclusionNormControl condition :=
    le_max_right _ _
  have hInclusionControl :
      ‖triple.lagrangianInclusion condition field‖ ≤
        triple.inclusionNormControl condition * ‖field‖ :=
    hInclusion.trans
      (mul_le_mul_of_nonneg_right hNormOperator (norm_nonneg _))
  have hUpper :
      ‖triple.lagrangianShiftedOperator condition spectralParameter field‖ *
          ‖triple.lagrangianInclusion condition field‖ ≤
        ‖triple.lagrangianShiftedOperator condition spectralParameter field‖ *
          (triple.inclusionNormControl condition * ‖field‖) :=
    mul_le_mul_of_nonneg_left hInclusionControl (norm_nonneg _)
  have hCombined :
      data.constant * ‖field‖ * ‖field‖ ≤
        ‖triple.lagrangianShiftedOperator condition spectralParameter field‖ *
          (triple.inclusionNormControl condition * ‖field‖) :=
    hCoercive.trans (hCauchy.trans hUpper)
  have hReduced :
      data.constant * ‖field‖ ≤
        ‖triple.lagrangianShiftedOperator condition spectralParameter field‖ *
          triple.inclusionNormControl condition := by
    nlinarith
  unfold shiftedCoerciveConstant
  rw [div_mul_eq_mul_div]
  exact (div_le_iff₀ (triple.inclusionNormControl_pos condition)).2 (by
    simpa [mul_assoc, mul_comm, mul_left_comm] using hReduced)

/-- Lax--Milgram produces the direct coercive-surjective package. -/
def toCoerciveSurjectiveAt
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (data : triple.LagrangianLaxMilgramData
      condition spectralParameter) :
    triple.LagrangianCoerciveSurjectiveAt condition spectralParameter where
  constant := data.shiftedCoerciveConstant triple condition spectralParameter
  constant_pos := data.shiftedCoerciveConstant_pos
    triple condition spectralParameter
  lower_bound := data.shifted_lower_bound triple condition spectralParameter
  surjective := data.shifted_surjective triple condition spectralParameter

/-- Bounded direct resolvent constructed by Lax--Milgram. -/
noncomputable def boundedResolvent
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (data : triple.LagrangianLaxMilgramData
      condition spectralParameter) :
    triple.LagrangianBoundedResolventAt condition spectralParameter :=
  (data.toCoerciveSurjectiveAt triple condition spectralParameter)
    |>.boundedResolvent triple condition spectralParameter

/-- Lax--Milgram closure certificate. -/
theorem certificate
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (data : triple.LagrangianLaxMilgramData
      condition spectralParameter) :
    Function.Surjective
        (triple.lagrangianShiftedOperator condition spectralParameter) ∧
      (∀ field : triple.lagrangianDomainSubmodule condition,
        data.shiftedCoerciveConstant triple condition spectralParameter *
            ‖field‖ ≤
          ‖triple.lagrangianShiftedOperator
            condition spectralParameter field‖) ∧
      triple.LagrangianResolventPoint condition spectralParameter :=
  ⟨data.shifted_surjective triple condition spectralParameter,
    data.shifted_lower_bound triple condition spectralParameter,
    (data.boundedResolvent triple condition spectralParameter)
      |>.resolventPoint triple condition spectralParameter⟩

end LagrangianLaxMilgramData

end CanonicalScalarCompletedBoundaryTripleData

end
end P0EFTJanusMappingTorusScalarCompletedBoundaryTripleLaxMilgram4D
end JanusFormal
