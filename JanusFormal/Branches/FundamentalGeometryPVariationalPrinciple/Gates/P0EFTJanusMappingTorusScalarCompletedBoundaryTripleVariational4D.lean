import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCompletedBoundaryTripleShiftedForm4D

/-!
# Variational principle on a completed scalar boundary triple

The corrected completed Lagrangian realization carries its quadratic action
directly.  For a real spectral parameter `lambda` and source `f`, define

`S_f(u) = 1/2 <(A-lambda)u,u> - <f,u>`.

Symmetry gives the exact affine Taylor formula and the first variation.  Density
of the ambient domain inclusion identifies weak stationarity with the strong
source equation.  Coercivity of the canonical shifted form makes the
Lax--Milgram solution the unique global minimizer.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarCompletedBoundaryTripleVariational4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleResolvent4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleLaxMilgram4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleShiftedForm4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

namespace CanonicalScalarCompletedBoundaryTripleData

/-- Direct shifted Jacobi pairing. -/
def lagrangianShiftedJacobiPairing
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (first second : triple.lagrangianDomainSubmodule condition) : Real :=
  inner Real
    (triple.lagrangianShiftedOperator condition spectralParameter first)
    (triple.lagrangianInclusion condition second)

/-- Symmetry of the shifted Jacobi pairing. -/
theorem lagrangianShiftedJacobiPairing_comm
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (first second : triple.lagrangianDomainSubmodule condition) :
    triple.lagrangianShiftedJacobiPairing condition spectralParameter
        first second =
      triple.lagrangianShiftedJacobiPairing condition spectralParameter
        second first := by
  unfold lagrangianShiftedJacobiPairing
  rw [triple.lagrangianShiftedOperator_apply,
    triple.lagrangianShiftedOperator_apply,
    inner_sub_left, inner_sub_left,
    real_inner_smul_left, real_inner_smul_left,
    triple.lagrangianOperator_symmetric condition first second,
    real_inner_comm
      (triple.lagrangianInclusion condition first)
      (triple.lagrangianInclusion condition second)]

/-- Direct shifted quadratic functional. -/
def lagrangianShiftedQuadraticFunctional
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (field : triple.lagrangianDomainSubmodule condition) : Real :=
  (1 / 2 : Real) *
    triple.lagrangianShiftedJacobiPairing condition spectralParameter field field

/-- Direct source action. -/
def lagrangianSourceAction
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (source : Ambient)
    (field : triple.lagrangianDomainSubmodule condition) : Real :=
  triple.lagrangianShiftedQuadraticFunctional
      condition spectralParameter field -
    inner Real source (triple.lagrangianInclusion condition field)

/-- Exact affine expansion of the shifted quadratic functional. -/
theorem lagrangianShiftedQuadraticFunctional_add
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (field variation : triple.lagrangianDomainSubmodule condition) :
    triple.lagrangianShiftedQuadraticFunctional condition spectralParameter
        (field + variation) =
      triple.lagrangianShiftedQuadraticFunctional condition spectralParameter field +
        triple.lagrangianShiftedJacobiPairing condition spectralParameter
          variation field +
        triple.lagrangianShiftedQuadraticFunctional condition spectralParameter
          variation := by
  unfold lagrangianShiftedQuadraticFunctional lagrangianShiftedJacobiPairing
  simp only [map_add, inner_add_left, inner_add_right]
  rw [triple.lagrangianShiftedJacobiPairing_comm
      condition spectralParameter field variation]
  unfold lagrangianShiftedJacobiPairing
  ring

/-- Exact source-action expansion. -/
theorem lagrangianSourceAction_add
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (source : Ambient)
    (field variation : triple.lagrangianDomainSubmodule condition) :
    triple.lagrangianSourceAction condition spectralParameter source
        (field + variation) =
      triple.lagrangianSourceAction condition spectralParameter source field +
        inner Real
          (triple.lagrangianShiftedOperator condition spectralParameter field -
            source)
          (triple.lagrangianInclusion condition variation) +
        triple.lagrangianShiftedQuadraticFunctional condition spectralParameter
          variation := by
  unfold lagrangianSourceAction
  rw [triple.lagrangianShiftedQuadraticFunctional_add]
  simp only [map_add, inner_add_right]
  unfold lagrangianShiftedJacobiPairing
  ring

/-- First variation of the direct source action. -/
theorem lagrangianSourceAction_hasDerivAt
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (source : Ambient)
    (field variation : triple.lagrangianDomainSubmodule condition) :
    HasDerivAt
      (fun parameter : Real =>
        triple.lagrangianSourceAction condition spectralParameter source
          (field + parameter • variation))
      (inner Real
        (triple.lagrangianShiftedOperator condition spectralParameter field -
          source)
        (triple.lagrangianInclusion condition variation)) 0 := by
  let linearTerm := inner Real
    (triple.lagrangianShiftedOperator condition spectralParameter field - source)
    (triple.lagrangianInclusion condition variation)
  let quadraticTerm :=
    triple.lagrangianShiftedQuadraticFunctional
      condition spectralParameter variation
  have hPolynomial : ∀ parameter : Real,
      triple.lagrangianSourceAction condition spectralParameter source
          (field + parameter • variation) =
        triple.lagrangianSourceAction condition spectralParameter source field +
          parameter * linearTerm + parameter ^ 2 * quadraticTerm := by
    intro parameter
    rw [triple.lagrangianSourceAction_add]
    unfold lagrangianShiftedQuadraticFunctional
    simp only [map_smul, real_inner_smul_left, real_inner_smul_right]
    dsimp [linearTerm, quadraticTerm]
    ring
  rw [show (fun parameter : Real =>
      triple.lagrangianSourceAction condition spectralParameter source
        (field + parameter • variation)) =
    (fun parameter : Real =>
      triple.lagrangianSourceAction condition spectralParameter source field +
        parameter * linearTerm + parameter ^ 2 * quadraticTerm) from by
      funext parameter
      exact hPolynomial parameter]
  convert (((hasDerivAt_const (x := (0 : Real))
      (triple.lagrangianSourceAction condition spectralParameter source field)).add
      ((hasDerivAt_id (0 : Real)).mul_const linearTerm)).add
      (((hasDerivAt_id (0 : Real)).pow 2).mul_const quadraticTerm)) using 1 <;>
    norm_num

/-- Weak stationarity of the source action. -/
def lagrangianSourceStationary
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (source : Ambient)
    (field : triple.lagrangianDomainSubmodule condition) : Prop :=
  ∀ variation : triple.lagrangianDomainSubmodule condition,
    inner Real
      (triple.lagrangianShiftedOperator condition spectralParameter field - source)
      (triple.lagrangianInclusion condition variation) = 0

/-- Strong source equation implies weak stationarity. -/
theorem lagrangianSourceStationary_of_equation
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (source : Ambient)
    (field : triple.lagrangianDomainSubmodule condition)
    (hEquation : triple.lagrangianShiftedOperator
      condition spectralParameter field = source) :
    triple.lagrangianSourceStationary condition spectralParameter source field := by
  intro variation
  rw [hEquation, sub_self, inner_zero_left]

/-- Density upgrades weak stationarity to the strong source equation. -/
theorem lagrangianSourceEquation_of_stationary
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (source : Ambient)
    (field : triple.lagrangianDomainSubmodule condition)
    (hDense : DenseRange (triple.lagrangianInclusion condition))
    (hStationary : triple.lagrangianSourceStationary
      condition spectralParameter source field) :
    triple.lagrangianShiftedOperator condition spectralParameter field = source := by
  let residual :=
    triple.lagrangianShiftedOperator condition spectralParameter field - source
  let good : Set Ambient := {test | inner Real residual test = 0}
  have hGoodClosed : IsClosed good := by
    dsimp [good]
    apply isClosed_eq <;> fun_prop
  have hRange : Set.range (triple.lagrangianInclusion condition) ⊆ good := by
    rintro test ⟨variation, rfl⟩
    exact hStationary variation
  have hClosure : closure
      (Set.range (triple.lagrangianInclusion condition)) = Set.univ :=
    hDense.closure_range
  have hResidual : residual ∈ closure
      (Set.range (triple.lagrangianInclusion condition)) := by
    rw [hClosure]
    trivial
  have hSelf : inner Real residual residual = 0 :=
    (closure_minimal hRange hGoodClosed) hResidual
  have hNorm : ‖residual‖ = 0 := by
    have hNormSq : ‖residual‖ ^ 2 = 0 := by
      simpa [real_inner_self_eq_norm_sq] using hSelf
    nlinarith [sq_nonneg ‖residual‖]
  exact sub_eq_zero.mp (norm_eq_zero.mp hNorm)

/-- Weak stationarity is equivalent to the strong source equation on a dense
domain. -/
theorem lagrangianSourceStationary_iff_equation
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (source : Ambient)
    (field : triple.lagrangianDomainSubmodule condition)
    (hDense : DenseRange (triple.lagrangianInclusion condition)) :
    triple.lagrangianSourceStationary condition spectralParameter source field ↔
      triple.lagrangianShiftedOperator condition spectralParameter field = source :=
  ⟨triple.lagrangianSourceEquation_of_stationary condition spectralParameter
      source field hDense,
    triple.lagrangianSourceStationary_of_equation condition spectralParameter
      source field⟩

/-- Energy difference from a strong source solution. -/
theorem lagrangianSourceAction_sub_solution
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (source : Ambient)
    (solution field : triple.lagrangianDomainSubmodule condition)
    (hSolution : triple.lagrangianShiftedOperator
      condition spectralParameter solution = source) :
    triple.lagrangianSourceAction condition spectralParameter source field -
        triple.lagrangianSourceAction condition spectralParameter source solution =
      triple.lagrangianShiftedQuadraticFunctional condition spectralParameter
        (field - solution) := by
  let variation := field - solution
  have hField : field = solution + variation := by
    dsimp [variation]
    module
  rw [hField, triple.lagrangianSourceAction_add, hSolution, sub_self,
    inner_zero_left, zero_add, add_sub_cancel_left]

/-- Coercivity makes the Lax--Milgram source solution the unique global
minimizer. -/
theorem LagrangianShiftedFormCoerciveData.unique_minimizer
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (coercive : triple.LagrangianShiftedFormCoerciveData
      condition spectralParameter)
    (hDense : DenseRange (triple.lagrangianInclusion condition))
    (source : Ambient) :
    let solution := coercive.boundedResolvent
      triple condition spectralParameter hDense |>.resolvent source
    (∀ field : triple.lagrangianDomainSubmodule condition,
      triple.lagrangianSourceAction condition spectralParameter source solution ≤
        triple.lagrangianSourceAction condition spectralParameter source field) ∧
      (∀ field : triple.lagrangianDomainSubmodule condition,
        triple.lagrangianSourceAction condition spectralParameter source field =
          triple.lagrangianSourceAction condition spectralParameter source solution →
        field = solution) := by
  dsimp
  let bounded := coercive.boundedResolvent
    triple condition spectralParameter hDense
  let solution := bounded.resolvent source
  have hSolution : triple.lagrangianShiftedOperator
      condition spectralParameter solution = source :=
    bounded.left_inverse source
  constructor
  · intro field
    have hDifference := triple.lagrangianSourceAction_sub_solution
      condition spectralParameter source solution field hSolution
    unfold lagrangianShiftedQuadraticFunctional
    rw [lagrangianShiftedJacobiPairing]
    have hCoercive := coercive.coercive (field - solution)
    rw [triple.lagrangianShiftedForm_apply] at hCoercive
    linarith [sq_nonneg ‖field - solution‖]
  · intro field hEqual
    have hDifference := triple.lagrangianSourceAction_sub_solution
      condition spectralParameter source solution field hSolution
    rw [hEqual, sub_self] at hDifference
    unfold lagrangianShiftedQuadraticFunctional at hDifference
    have hCoercive := coercive.coercive (field - solution)
    rw [triple.lagrangianShiftedForm_apply] at hCoercive
    have hNorm : ‖field - solution‖ = 0 := by
      nlinarith [sq_nonneg ‖field - solution‖]
    exact sub_eq_zero.mp (norm_eq_zero.mp hNorm)

/-- Direct variational certificate. -/
theorem directVariational_certificate
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (spectralParameter : Real)
    (source : Ambient)
    (field : triple.lagrangianDomainSubmodule condition)
    (hDense : DenseRange (triple.lagrangianInclusion condition)) :
    triple.lagrangianSourceStationary condition spectralParameter source field ↔
      triple.lagrangianShiftedOperator condition spectralParameter field = source :=
  triple.lagrangianSourceStationary_iff_equation
    condition spectralParameter source field hDense

end CanonicalScalarCompletedBoundaryTripleData

end
end P0EFTJanusMappingTorusScalarCompletedBoundaryTripleVariational4D
end JanusFormal
