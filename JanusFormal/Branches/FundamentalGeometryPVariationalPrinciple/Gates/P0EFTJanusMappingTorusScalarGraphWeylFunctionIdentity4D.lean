import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarGraphCalderonProjector4D

/-!
# Poisson and Weyl-function identities

The Dirichlet-to-Neumann operator is the Weyl function of the completed scalar
boundary triple.  This file compares two real spectral parameters.

A Dirichlet resolvent at `lambda` transports the Poisson operator at `mu` to the
Poisson operator at `lambda`.  The completed Green identity then gives the exact
Weyl identity relating `DtN_lambda - DtN_mu` to the bulk pairing of the two
Poisson solutions.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarGraphWeylFunctionIdentity4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarGraphPoissonDirichletToNeumann4D
open P0EFTJanusMappingTorusScalarGraphKreinResolventFormula4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

/-- Change-of-parameter formula for Poisson solutions. -/
theorem canonicalScalarGraphPoisson_change_parameter
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (firstParameter secondParameter : Real)
    (firstPoisson : CanonicalScalarGraphDirichletPoissonData
      data traceBound firstParameter)
    (secondPoisson : CanonicalScalarGraphDirichletPoissonData
      data traceBound secondParameter)
    (firstDirichletResolvent : CanonicalScalarGraphDirichletResolventData
      data traceBound firstParameter)
    (boundary : Trace) :
    firstPoisson.poisson boundary =
      secondPoisson.poisson boundary +
        (firstParameter - secondParameter) •
          firstDirichletResolvent.resolvent
            (canonicalScalarOperatorGraphInclusion data
              (secondPoisson.poisson boundary)) := by
  let correction : CanonicalScalarOperatorGraphSpace data :=
    (firstParameter - secondParameter) •
      firstDirichletResolvent.resolvent
        (canonicalScalarOperatorGraphInclusion data
          (secondPoisson.poisson boundary))
  let candidate := secondPoisson.poisson boundary + correction
  apply (firstPoisson.unique candidate boundary).symm
  · dsimp [candidate, correction]
    rw [map_add, map_smul, secondPoisson.value_trace,
      firstDirichletResolvent.value_zero, map_zero, smul_zero, add_zero]
  · dsimp [candidate, correction]
    rw [map_add, map_smul,
      firstDirichletResolvent.equation]
    have hSecond := secondPoisson.homogeneous boundary
    rw [canonicalScalarGraphShiftedOperator_apply] at hSecond ⊢
    have hSecondOperator :
        canonicalScalarOperatorGraphOperator data
            (secondPoisson.poisson boundary) =
          secondParameter • canonicalScalarOperatorGraphInclusion data
            (secondPoisson.poisson boundary) :=
      sub_eq_zero.mp hSecond
    rw [hSecondOperator]
    module

/-- Linear-map form of the Poisson change-of-parameter identity. -/
theorem canonicalScalarGraphPoisson_change_parameter_clm
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (firstParameter secondParameter : Real)
    (firstPoisson : CanonicalScalarGraphDirichletPoissonData
      data traceBound firstParameter)
    (secondPoisson : CanonicalScalarGraphDirichletPoissonData
      data traceBound secondParameter)
    (firstDirichletResolvent : CanonicalScalarGraphDirichletResolventData
      data traceBound firstParameter) :
    firstPoisson.poisson =
      secondPoisson.poisson +
        (firstParameter - secondParameter) •
          (firstDirichletResolvent.resolvent.comp
            ((canonicalScalarOperatorGraphInclusion data).comp
              secondPoisson.poisson)) := by
  ext boundary
  exact canonicalScalarGraphPoisson_change_parameter
    data traceBound firstParameter secondParameter firstPoisson secondPoisson
      firstDirichletResolvent boundary

/-- Exact Weyl identity for the two Dirichlet-to-Neumann operators. -/
theorem canonicalScalarGraphDirichletToNeumann_weyl_identity
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (firstParameter secondParameter : Real)
    (firstPoisson : CanonicalScalarGraphDirichletPoissonData
      data traceBound firstParameter)
    (secondPoisson : CanonicalScalarGraphDirichletPoissonData
      data traceBound secondParameter)
    (firstBoundary secondBoundary : Trace) :
    2 * (inner Real firstBoundary
          (canonicalScalarGraphDirichletToNeumann
            data traceBound secondParameter secondPoisson secondBoundary) -
        inner Real
          (canonicalScalarGraphDirichletToNeumann
            data traceBound firstParameter firstPoisson firstBoundary)
          secondBoundary) =
      (firstParameter - secondParameter) *
        inner Real
          (canonicalScalarOperatorGraphInclusion data
            (firstPoisson.poisson firstBoundary))
          (canonicalScalarOperatorGraphInclusion data
            (secondPoisson.poisson secondBoundary)) := by
  have hGreen := canonicalScalarCompletedGreenIdentity data traceBound
    (firstPoisson.poisson firstBoundary)
    (secondPoisson.poisson secondBoundary)
  have hFirst := firstPoisson.homogeneous firstBoundary
  have hSecond := secondPoisson.homogeneous secondBoundary
  have hFirstOperator :
      canonicalScalarOperatorGraphOperator data
          (firstPoisson.poisson firstBoundary) =
        firstParameter • canonicalScalarOperatorGraphInclusion data
          (firstPoisson.poisson firstBoundary) :=
    sub_eq_zero.mp (by
      simpa [canonicalScalarGraphShiftedOperator_apply] using hFirst)
  have hSecondOperator :
      canonicalScalarOperatorGraphOperator data
          (secondPoisson.poisson secondBoundary) =
        secondParameter • canonicalScalarOperatorGraphInclusion data
          (secondPoisson.poisson secondBoundary) :=
    sub_eq_zero.mp (by
      simpa [canonicalScalarGraphShiftedOperator_apply] using hSecond)
  rw [hFirstOperator, hSecondOperator,
    real_inner_smul_left, real_inner_smul_right] at hGreen
  unfold canonicalScalarCompletedBoundaryGreenPairing at hGreen
  rw [firstPoisson.value_trace, secondPoisson.value_trace] at hGreen
  change
    firstParameter * inner Real
        (canonicalScalarOperatorGraphInclusion data
          (firstPoisson.poisson firstBoundary))
        (canonicalScalarOperatorGraphInclusion data
          (secondPoisson.poisson secondBoundary)) -
      secondParameter * inner Real
        (canonicalScalarOperatorGraphInclusion data
          (firstPoisson.poisson firstBoundary))
        (canonicalScalarOperatorGraphInclusion data
          (secondPoisson.poisson secondBoundary)) =
    2 * (inner Real firstBoundary
        (canonicalScalarGraphDirichletToNeumann
          data traceBound secondParameter secondPoisson secondBoundary) -
      inner Real
        (canonicalScalarGraphDirichletToNeumann
          data traceBound firstParameter firstPoisson firstBoundary)
        secondBoundary) at hGreen
  linarith

/-- Diagonal boundary form of the Weyl identity. -/
theorem canonicalScalarGraphDirichletToNeumann_weyl_identity_self
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (firstParameter secondParameter : Real)
    (firstPoisson : CanonicalScalarGraphDirichletPoissonData
      data traceBound firstParameter)
    (secondPoisson : CanonicalScalarGraphDirichletPoissonData
      data traceBound secondParameter)
    (boundary : Trace) :
    2 * inner Real boundary
        ((canonicalScalarGraphDirichletToNeumann
            data traceBound secondParameter secondPoisson -
          canonicalScalarGraphDirichletToNeumann
            data traceBound firstParameter firstPoisson) boundary) =
      (firstParameter - secondParameter) *
        inner Real
          (canonicalScalarOperatorGraphInclusion data
            (firstPoisson.poisson boundary))
          (canonicalScalarOperatorGraphInclusion data
            (secondPoisson.poisson boundary)) := by
  simpa [inner_sub_right] using
    canonicalScalarGraphDirichletToNeumann_weyl_identity
      data traceBound firstParameter secondParameter firstPoisson secondPoisson
        boundary boundary

/-- Difference of Robin Schur operators is exactly the difference of Weyl
functions when the Robin operator is fixed. -/
theorem canonicalScalarGraphBoundarySchurOperator_sub
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (firstParameter secondParameter : Real)
    (firstPoisson : CanonicalScalarGraphDirichletPoissonData
      data traceBound firstParameter)
    (secondPoisson : CanonicalScalarGraphDirichletPoissonData
      data traceBound secondParameter)
    (robin : Trace →L[Real] Trace) :
    canonicalScalarGraphBoundarySchurOperator
          data traceBound firstParameter firstPoisson robin -
        canonicalScalarGraphBoundarySchurOperator
          data traceBound secondParameter secondPoisson robin =
      canonicalScalarGraphDirichletToNeumann
          data traceBound firstParameter firstPoisson -
        canonicalScalarGraphDirichletToNeumann
          data traceBound secondParameter secondPoisson := by
  module

/-- Poisson/Weyl comparison certificate. -/
theorem canonicalScalarGraphWeylFunctionIdentity_certificate
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (firstParameter secondParameter : Real)
    (firstPoisson : CanonicalScalarGraphDirichletPoissonData
      data traceBound firstParameter)
    (secondPoisson : CanonicalScalarGraphDirichletPoissonData
      data traceBound secondParameter)
    (firstDirichletResolvent : CanonicalScalarGraphDirichletResolventData
      data traceBound firstParameter) :
    (∀ boundary : Trace,
      firstPoisson.poisson boundary =
        secondPoisson.poisson boundary +
          (firstParameter - secondParameter) •
            firstDirichletResolvent.resolvent
              (canonicalScalarOperatorGraphInclusion data
                (secondPoisson.poisson boundary))) ∧
      (∀ firstBoundary secondBoundary : Trace,
        2 * (inner Real firstBoundary
              (canonicalScalarGraphDirichletToNeumann
                data traceBound secondParameter secondPoisson secondBoundary) -
            inner Real
              (canonicalScalarGraphDirichletToNeumann
                data traceBound firstParameter firstPoisson firstBoundary)
              secondBoundary) =
          (firstParameter - secondParameter) *
            inner Real
              (canonicalScalarOperatorGraphInclusion data
                (firstPoisson.poisson firstBoundary))
              (canonicalScalarOperatorGraphInclusion data
                (secondPoisson.poisson secondBoundary))) :=
  ⟨canonicalScalarGraphPoisson_change_parameter
      data traceBound firstParameter secondParameter firstPoisson secondPoisson
        firstDirichletResolvent,
    canonicalScalarGraphDirichletToNeumann_weyl_identity
      data traceBound firstParameter secondParameter firstPoisson secondPoisson⟩

end
end P0EFTJanusMappingTorusScalarGraphWeylFunctionIdentity4D
end JanusFormal
