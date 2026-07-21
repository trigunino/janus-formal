import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarLagrangianPTSymmetry4D

/-!
# Coercive source variational problem on a scalar Lagrangian domain

For a source `f` in the ambient Hilbert space, this file defines

`S_f(u) = 1/2 <A u,u> - <f,u>`

on the actual closed Lagrangian operator domain.  Its first variation is the
weak residual pairing.  Dense domain inclusion converts weak stationarity to
the strong equation `A u = f`.

A strictly positive quadratic lower bound gives uniqueness and a global
minimum.  If zero has a bounded resolvent, the minimizer is the resolvent image
of the source.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarLagrangianCoerciveVariationalProblem4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarClosedGraphRealization4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarLagrangianResolvent4D
open P0EFTJanusMappingTorusScalarLagrangianSemiboundedSpectrum4D
open P0EFTJanusMappingTorusScalarLagrangianVariationalEigenprinciple4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

private abbrev LagrangianDomain
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace) :=
  canonicalScalarClosedLagrangianDomainSubmodule
    data hClosable traceBound condition

/-- Quadratic source action. -/
def canonicalScalarClosedLagrangianSourceAction
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (source : Ambient)
    (field : LagrangianDomain data hClosable traceBound condition) : Real :=
  (1 / 2 : Real) * canonicalScalarClosedLagrangianQuadraticFunctional
      data hClosable traceBound condition field -
    inner Real source
      (canonicalScalarClosedLagrangianDomainInclusion
        data hClosable traceBound condition field)

/-- Exact affine Taylor formula for the source action. -/
theorem canonicalScalarClosedLagrangianSourceAction_affine
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (source : Ambient)
    (field variation : LagrangianDomain data hClosable traceBound condition)
    (parameter : Real) :
    canonicalScalarClosedLagrangianSourceAction
        data hClosable traceBound condition source
        (field + parameter • variation) =
      canonicalScalarClosedLagrangianSourceAction
          data hClosable traceBound condition source field +
        parameter *
          (canonicalScalarClosedLagrangianJacobiPairing
              data hClosable traceBound condition field variation -
            inner Real source
              (canonicalScalarClosedLagrangianDomainInclusion
                data hClosable traceBound condition variation)) +
        (1 / 2 : Real) * parameter ^ 2 *
          canonicalScalarClosedLagrangianQuadraticFunctional
            data hClosable traceBound condition variation := by
  unfold canonicalScalarClosedLagrangianSourceAction
  rw [canonicalScalarClosedLagrangianQuadraticFunctional_affine]
  simp only [map_add, map_smul, inner_add_right, real_inner_smul_right]
  ring

/-- First variation of the source action. -/
theorem canonicalScalarClosedLagrangianSourceAction_hasDerivAt
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (source : Ambient)
    (field variation : LagrangianDomain data hClosable traceBound condition) :
    HasDerivAt
      (fun parameter : Real =>
        canonicalScalarClosedLagrangianSourceAction
          data hClosable traceBound condition source
          (field + parameter • variation))
      (canonicalScalarClosedLagrangianJacobiPairing
          data hClosable traceBound condition field variation -
        inner Real source
          (canonicalScalarClosedLagrangianDomainInclusion
            data hClosable traceBound condition variation)) 0 := by
  rw [show (fun parameter : Real =>
      canonicalScalarClosedLagrangianSourceAction
        data hClosable traceBound condition source
        (field + parameter • variation)) =
    (fun parameter : Real =>
      canonicalScalarClosedLagrangianSourceAction
          data hClosable traceBound condition source field +
        parameter *
          (canonicalScalarClosedLagrangianJacobiPairing
              data hClosable traceBound condition field variation -
            inner Real source
              (canonicalScalarClosedLagrangianDomainInclusion
                data hClosable traceBound condition variation)) +
        (1 / 2 : Real) * parameter ^ 2 *
          canonicalScalarClosedLagrangianQuadraticFunctional
            data hClosable traceBound condition variation) from by
      funext parameter
      exact canonicalScalarClosedLagrangianSourceAction_affine
        data hClosable traceBound condition source field variation parameter]
  convert (((hasDerivAt_const (x := (0 : Real))
      (canonicalScalarClosedLagrangianSourceAction
        data hClosable traceBound condition source field)).add
      ((hasDerivAt_id (0 : Real)).mul_const
        (canonicalScalarClosedLagrangianJacobiPairing
            data hClosable traceBound condition field variation -
          inner Real source
            (canonicalScalarClosedLagrangianDomainInclusion
              data hClosable traceBound condition variation)))).add
      ((((hasDerivAt_id (0 : Real)).pow 2).const_mul (1 / 2 : Real)).mul_const
        (canonicalScalarClosedLagrangianQuadraticFunctional
          data hClosable traceBound condition variation))) using 1 <;> norm_num

/-- Weak source stationarity. -/
def CanonicalScalarClosedLagrangianSourceStationary
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (source : Ambient)
    (field : LagrangianDomain data hClosable traceBound condition) : Prop :=
  ∀ variation : LagrangianDomain data hClosable traceBound condition,
    canonicalScalarClosedLagrangianJacobiPairing
        data hClosable traceBound condition field variation =
      inner Real source
        (canonicalScalarClosedLagrangianDomainInclusion
          data hClosable traceBound condition variation)

/-- Every strong source solution is weakly stationary. -/
theorem canonicalScalarClosedLagrangian_sourceSolution_stationary
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (source : Ambient)
    (field : LagrangianDomain data hClosable traceBound condition)
    (hEquation : canonicalScalarClosedLagrangianDomainOperator
      data hClosable traceBound condition field = source) :
    CanonicalScalarClosedLagrangianSourceStationary
      data hClosable traceBound condition source field := by
  intro variation
  unfold canonicalScalarClosedLagrangianJacobiPairing
  rw [hEquation]

/-- Dense weak source stationarity implies the strong source equation. -/
theorem canonicalScalarClosedLagrangian_stationary_sourceSolution
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (source : Ambient)
    (field : LagrangianDomain data hClosable traceBound condition)
    (hDense : DenseRange
      (canonicalScalarClosedLagrangianDomainInclusion
        data hClosable traceBound condition))
    (hStationary : CanonicalScalarClosedLagrangianSourceStationary
      data hClosable traceBound condition source field) :
    canonicalScalarClosedLagrangianDomainOperator
        data hClosable traceBound condition field = source := by
  let residual : Ambient :=
    canonicalScalarClosedLagrangianDomainOperator
        data hClosable traceBound condition field - source
  let good : Set Ambient := {test | inner Real residual test = 0}
  have hGoodClosed : IsClosed good := by
    dsimp [good]
    apply isClosed_eq <;> fun_prop
  have hRange : Set.range
      (canonicalScalarClosedLagrangianDomainInclusion
        data hClosable traceBound condition) ⊆ good := by
    rintro test ⟨variation, rfl⟩
    dsimp [good, residual]
    rw [inner_sub_left]
    change canonicalScalarClosedLagrangianJacobiPairing
          data hClosable traceBound condition field variation -
        inner Real source
          (canonicalScalarClosedLagrangianDomainInclusion
            data hClosable traceBound condition variation) = 0
    rw [hStationary variation, sub_self]
  have hClosure : closure (Set.range
      (canonicalScalarClosedLagrangianDomainInclusion
        data hClosable traceBound condition)) = Set.univ :=
    hDense.closure_range
  have hResidualMem : residual ∈ closure (Set.range
      (canonicalScalarClosedLagrangianDomainInclusion
        data hClosable traceBound condition)) := by
    rw [hClosure]
    trivial
  have hResidualGood := (closure_minimal hRange hGoodClosed) hResidualMem
  have hResidualInner : inner Real residual residual = 0 := hResidualGood
  have hResidualNorm : ‖residual‖ = 0 := by
    rw [← sq_eq_zero_iff]
    simpa [real_inner_self_eq_norm_sq] using hResidualInner
  exact sub_eq_zero.mp (norm_eq_zero.mp hResidualNorm)

/-- Weak stationarity is equivalent to the strong source equation under density. -/
theorem canonicalScalarClosedLagrangian_sourceStationary_iff_equation
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (source : Ambient)
    (field : LagrangianDomain data hClosable traceBound condition)
    (hDense : DenseRange
      (canonicalScalarClosedLagrangianDomainInclusion
        data hClosable traceBound condition)) :
    CanonicalScalarClosedLagrangianSourceStationary
        data hClosable traceBound condition source field ↔
      canonicalScalarClosedLagrangianDomainOperator
        data hClosable traceBound condition field = source :=
  ⟨canonicalScalarClosedLagrangian_stationary_sourceSolution
      data hClosable traceBound condition source field hDense,
    canonicalScalarClosedLagrangian_sourceSolution_stationary
      data hClosable traceBound condition source field⟩

/-- Energy difference from a strong source solution is exactly the quadratic
energy of the displacement. -/
theorem canonicalScalarClosedLagrangianSourceAction_sub_solution
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (source : Ambient)
    (solution field : LagrangianDomain data hClosable traceBound condition)
    (hSolution : canonicalScalarClosedLagrangianDomainOperator
      data hClosable traceBound condition solution = source) :
    canonicalScalarClosedLagrangianSourceAction
          data hClosable traceBound condition source field -
        canonicalScalarClosedLagrangianSourceAction
          data hClosable traceBound condition source solution =
      (1 / 2 : Real) * canonicalScalarClosedLagrangianQuadraticFunctional
        data hClosable traceBound condition (field - solution) := by
  let displacement := field - solution
  have hField : field = solution + displacement := by
    dsimp [displacement]
    module
  rw [hField,
    canonicalScalarClosedLagrangianSourceAction_affine
      data hClosable traceBound condition source solution displacement 1]
  unfold canonicalScalarClosedLagrangianJacobiPairing
  rw [hSolution]
  ring

/-- Strictly positive semiboundedness makes every strong source solution a
unique global minimizer. -/
theorem canonicalScalarClosedLagrangianSourceAction_unique_minimizer
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (semibounded : CanonicalScalarClosedLagrangianSemiboundedData
      data hClosable traceBound condition)
    (hPositive : 0 < semibounded.lowerBound)
    (source : Ambient)
    (solution : LagrangianDomain data hClosable traceBound condition)
    (hSolution : canonicalScalarClosedLagrangianDomainOperator
      data hClosable traceBound condition solution = source) :
    (∀ field : LagrangianDomain data hClosable traceBound condition,
      canonicalScalarClosedLagrangianSourceAction
          data hClosable traceBound condition source solution ≤
        canonicalScalarClosedLagrangianSourceAction
          data hClosable traceBound condition source field) ∧
      (∀ field : LagrangianDomain data hClosable traceBound condition,
        canonicalScalarClosedLagrangianSourceAction
            data hClosable traceBound condition source field =
          canonicalScalarClosedLagrangianSourceAction
            data hClosable traceBound condition source solution →
        field = solution) := by
  constructor
  · intro field
    have hDifference := canonicalScalarClosedLagrangianSourceAction_sub_solution
      data hClosable traceBound condition source solution field hSolution
    have hBound := semibounded.bound (field - solution)
    unfold canonicalScalarClosedLagrangianQuadraticFunctional
      canonicalScalarClosedLagrangianJacobiPairing at hBound
    linarith [sq_nonneg
      ‖canonicalScalarClosedLagrangianDomainInclusion
        data hClosable traceBound condition (field - solution)‖]
  · intro field hEqual
    have hDifference := canonicalScalarClosedLagrangianSourceAction_sub_solution
      data hClosable traceBound condition source solution field hSolution
    rw [hEqual, sub_self] at hDifference
    have hBound := semibounded.bound (field - solution)
    unfold canonicalScalarClosedLagrangianQuadraticFunctional
      canonicalScalarClosedLagrangianJacobiPairing at hBound hDifference
    have hNorm : ‖canonicalScalarClosedLagrangianDomainInclusion
        data hClosable traceBound condition (field - solution)‖ = 0 := by
      nlinarith [sq_nonneg
        ‖canonicalScalarClosedLagrangianDomainInclusion
          data hClosable traceBound condition (field - solution)‖]
    have hZero : canonicalScalarClosedLagrangianDomainInclusion
        data hClosable traceBound condition (field - solution) = 0 :=
      norm_eq_zero.mp hNorm
    have hDisplacement : field - solution = 0 :=
      canonicalScalarClosedLagrangianDomainInclusion_injective
        data hClosable traceBound condition hZero
    exact sub_eq_zero.mp hDisplacement

/-- A bounded zero resolvent constructs the unique strong source solution. -/
theorem canonicalScalarClosedLagrangian_zeroResolvent_solution
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (zeroResolvent : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition 0)
    (source : Ambient) :
    canonicalScalarClosedLagrangianDomainOperator
        data hClosable traceBound condition (zeroResolvent.resolvent source) =
      source := by
  have hEquation := zeroResolvent.left_inverse source
  simpa [canonicalScalarClosedLagrangianShiftedOperator_apply] using hEquation

/-- Complete coercive variational solution certificate. -/
theorem canonicalScalarLagrangianCoerciveVariationalProblem_certificate
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (semibounded : CanonicalScalarClosedLagrangianSemiboundedData
      data hClosable traceBound condition)
    (hPositive : 0 < semibounded.lowerBound)
    (zeroResolvent : CanonicalScalarClosedLagrangianBoundedResolventAt
      data hClosable traceBound condition 0)
    (source : Ambient) :
    let solution := zeroResolvent.resolvent source
    canonicalScalarClosedLagrangianDomainOperator
          data hClosable traceBound condition solution = source ∧
      (∀ field : LagrangianDomain data hClosable traceBound condition,
        canonicalScalarClosedLagrangianSourceAction
            data hClosable traceBound condition source solution ≤
          canonicalScalarClosedLagrangianSourceAction
            data hClosable traceBound condition source field) ∧
      (∀ field : LagrangianDomain data hClosable traceBound condition,
        canonicalScalarClosedLagrangianSourceAction
            data hClosable traceBound condition source field =
          canonicalScalarClosedLagrangianSourceAction
            data hClosable traceBound condition source solution →
        field = solution) := by
  dsimp
  have hSolution := canonicalScalarClosedLagrangian_zeroResolvent_solution
    data hClosable traceBound condition zeroResolvent source
  exact ⟨hSolution,
    (canonicalScalarClosedLagrangianSourceAction_unique_minimizer
      data hClosable traceBound condition semibounded hPositive source
        (zeroResolvent.resolvent source) hSolution).1,
    (canonicalScalarClosedLagrangianSourceAction_unique_minimizer
      data hClosable traceBound condition semibounded hPositive source
        (zeroResolvent.resolvent source) hSolution).2⟩

end
end P0EFTJanusMappingTorusScalarLagrangianCoerciveVariationalProblem4D
end JanusFormal
