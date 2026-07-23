import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalResolventReducedAnalyticClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D

/-!
# Standard separated physical scalar realizations

The final resolvent-reduced scalar endpoint accepts an arbitrary closed
Lagrangian boundary condition.  The physically standard separated families are
already closed Lagrangian subspaces of the completed Cauchy trace space, so they
can be exposed without retaining a boundary-condition field in the input.

This file provides one generic separated endpoint

`a γ₀ u + b γ₁ u = 0`,

and the three standard specializations:

* Dirichlet: `γ₀ u = 0`;
* Neumann: `γ₁ u = 0`;
* constant real Robin: `γ₁ u = κ γ₀ u`.

For each family, a positive shifted-form decomposition and finite-rank Rellich
scheme give self-adjointness, compact resolvent and the complete spectral
conclusions through the preferred adjoint-free path.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalStandardBoundaryResolventClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology MeasureTheory
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalReducedPDEClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalResolventReducedAnalyticClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFiniteRankRellich4D
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTriplePositiveShiftedForm4D

universe r

variable (period : Real) (hPeriod : period ≠ 0)
variable {massSquared : Real}
variable {Regularity : Type r}
  [NormedAddCommGroup Regularity] [NormedSpace Real Regularity]
  [CompleteSpace Regularity]

private abbrev BoundaryL2 := CanonicalPhysicalScalarFirstSheetL2 period

/-- Canonical separated Lagrangian condition on the physical Cauchy trace. -/
noncomputable def canonicalPhysicalScalarSeparatedCondition
    (a b : Real) (hNondegenerate : a ≠ 0 ∨ b ≠ 0) :
    CanonicalScalarHilbertLagrangianBoundaryCondition (BoundaryL2 period) :=
  CanonicalScalarHilbertLagrangianBoundaryCondition.separated
    (Trace := BoundaryL2 period) a b hNondegenerate

/-- Dirichlet condition on the completed physical trace. -/
noncomputable def canonicalPhysicalScalarDirichletCondition :
    CanonicalScalarHilbertLagrangianBoundaryCondition (BoundaryL2 period) :=
  CanonicalScalarHilbertLagrangianBoundaryCondition.dirichlet
    (Trace := BoundaryL2 period)

/-- Neumann condition on the completed physical trace. -/
noncomputable def canonicalPhysicalScalarNeumannCondition :
    CanonicalScalarHilbertLagrangianBoundaryCondition (BoundaryL2 period) :=
  CanonicalScalarHilbertLagrangianBoundaryCondition.neumann
    (Trace := BoundaryL2 period)

/-- Constant real Robin condition `γ₁ = κ γ₀`. -/
noncomputable def canonicalPhysicalScalarRobinCondition
    (coefficient : Real) :
    CanonicalScalarHilbertLagrangianBoundaryCondition (BoundaryL2 period) :=
  CanonicalScalarHilbertLagrangianBoundaryCondition.scalarRobin
    (Trace := BoundaryL2 period) coefficient

/-- Final analytic inputs for a fixed separated condition. -/
structure CanonicalPhysicalScalarCanonicalSeparatedResolventData
    (massSquared a b : Real)
    (hNondegenerate : a ≠ 0 ∨ b ≠ 0) where
  boundary : CanonicalPhysicalScalarCanonicalReducedPDEData
    period hPeriod massSquared (Regularity := Regularity)
  referenceParameter : Real
  shiftedPositiveDecomposition :
    boundary.triple.LagrangianShiftedPositiveDecompositionData
      (canonicalPhysicalScalarSeparatedCondition
        period a b hNondegenerate)
      referenceParameter
  finiteRankRellich : CanonicalPhysicalScalarFiniteRankRellichData
    period hPeriod

namespace CanonicalPhysicalScalarCanonicalSeparatedResolventData

/-- Conversion to the generic adjoint-free final analytic package. -/
def toResolventReducedAnalyticData
    {a b : Real} {hNondegenerate : a ≠ 0 ∨ b ≠ 0}
    (data : CanonicalPhysicalScalarCanonicalSeparatedResolventData
      period hPeriod massSquared a b hNondegenerate
      (Regularity := Regularity)) :
    CanonicalPhysicalScalarCanonicalResolventReducedAnalyticData
      period hPeriod massSquared (Regularity := Regularity) where
  boundary := data.boundary
  condition := canonicalPhysicalScalarSeparatedCondition
    period a b hNondegenerate
  referenceParameter := data.referenceParameter
  shiftedPositiveDecomposition := data.shiftedPositiveDecomposition
  finiteRankRellich := data.finiteRankRellich

/-- Membership in the completed separated realization is exactly the separated
Cauchy constraint. -/
theorem mem_lagrangianDomainSubmodule_iff
    {a b : Real} {hNondegenerate : a ≠ 0 ∨ b ≠ 0}
    (data : CanonicalPhysicalScalarCanonicalSeparatedResolventData
      period hPeriod massSquared a b hNondegenerate
      (Regularity := Regularity))
    (field : data.boundary.triple.MaximalDomain) :
    field ∈ data.boundary.triple.lagrangianDomainSubmodule
        (canonicalPhysicalScalarSeparatedCondition
          period a b hNondegenerate) ↔
      a • (data.boundary.completedBoundaryTrace period hPeriod field).1 +
        b • (data.boundary.completedBoundaryTrace period hPeriod field).2 =
          0 := by
  change data.boundary.completedBoundaryTrace period hPeriod field ∈
        canonicalScalarHilbertSeparatedBoundarySubmodule
          (Trace := BoundaryL2 period) a b ↔ _
  exact mem_canonicalScalarHilbertSeparatedBoundarySubmodule
    (Trace := BoundaryL2 period) a b _

/-- Actual Hilbert self-adjointness of every separated endpoint. -/
theorem actualAdjointDomain_eq
    {a b : Real} {hNondegenerate : a ≠ 0 ∨ b ≠ 0}
    (data : CanonicalPhysicalScalarCanonicalSeparatedResolventData
      period hPeriod massSquared a b hNondegenerate
      (Regularity := Regularity)) :
    data.boundary.triple.actualAdjointDomain
        (canonicalPhysicalScalarSeparatedCondition
          period a b hNondegenerate) =
      data.boundary.triple.realizationDomain
        (canonicalPhysicalScalarSeparatedCondition
          period a b hNondegenerate) :=
  (data.toResolventReducedAnalyticData period hPeriod)
    |>.actualAdjointDomain_eq period hPeriod

/-- Compact reference resolvent for every separated endpoint. -/
noncomputable def compactResolvent
    {a b : Real} {hNondegenerate : a ≠ 0 ∨ b ≠ 0}
    (data : CanonicalPhysicalScalarCanonicalSeparatedResolventData
      period hPeriod massSquared a b hNondegenerate
      (Regularity := Regularity)) :=
  (data.toResolventReducedAnalyticData period hPeriod)
    |>.compactResolvent period hPeriod

/-- Fredholm alternative for every separated endpoint. -/
theorem fredholmAlternative
    {a b : Real} {hNondegenerate : a ≠ 0 ∨ b ≠ 0}
    (data : CanonicalPhysicalScalarCanonicalSeparatedResolventData
      period hPeriod massSquared a b hNondegenerate
      (Regularity := Regularity))
    (spectralParameter : Real)
    (hParameter : spectralParameter ≠ data.referenceParameter) :
    data.boundary.triple.LagrangianHasEigenvalue
        (canonicalPhysicalScalarSeparatedCondition
          period a b hNondegenerate) spectralParameter ∨
      data.boundary.triple.LagrangianResolventPoint
        (canonicalPhysicalScalarSeparatedCondition
          period a b hNondegenerate) spectralParameter :=
  (data.toResolventReducedAnalyticData period hPeriod)
    |>.fredholmAlternative period hPeriod spectralParameter hParameter

/-- Finite multiplicity for every nonreference separated eigenspace. -/
theorem finiteDimensional_operatorEigenspace
    {a b : Real} {hNondegenerate : a ≠ 0 ∨ b ≠ 0}
    (data : CanonicalPhysicalScalarCanonicalSeparatedResolventData
      period hPeriod massSquared a b hNondegenerate
      (Regularity := Regularity))
    (eigenvalue : Real)
    (hEigenvalue : eigenvalue ≠ data.referenceParameter) :
    FiniteDimensional Real
      (data.boundary.triple.lagrangianOperatorEigenspace
        (canonicalPhysicalScalarSeparatedCondition
          period a b hNondegenerate) eigenvalue) :=
  (data.toResolventReducedAnalyticData period hPeriod)
    |>.finiteDimensional_operatorEigenspace
      period hPeriod eigenvalue hEigenvalue

/-- Lower spectral bound for every separated endpoint. -/
theorem eigenvalue_ge_referenceParameter
    {a b : Real} {hNondegenerate : a ≠ 0 ∨ b ≠ 0}
    (data : CanonicalPhysicalScalarCanonicalSeparatedResolventData
      period hPeriod massSquared a b hNondegenerate
      (Regularity := Regularity))
    (eigenvalue : Real)
    (hEigenvalue : data.boundary.triple.LagrangianHasEigenvalue
      (canonicalPhysicalScalarSeparatedCondition
        period a b hNondegenerate) eigenvalue) :
    data.referenceParameter ≤ eigenvalue :=
  (data.toResolventReducedAnalyticData period hPeriod)
    |>.eigenvalue_ge_referenceParameter period hPeriod eigenvalue hEigenvalue

end CanonicalPhysicalScalarCanonicalSeparatedResolventData

/-- Final Dirichlet input package. -/
abbrev CanonicalPhysicalScalarCanonicalDirichletResolventData
    (massSquared : Real) :=
  CanonicalPhysicalScalarCanonicalSeparatedResolventData
    period hPeriod massSquared 1 0 (Or.inl one_ne_zero)
      (Regularity := Regularity)

/-- Final Neumann input package. -/
abbrev CanonicalPhysicalScalarCanonicalNeumannResolventData
    (massSquared : Real) :=
  CanonicalPhysicalScalarCanonicalSeparatedResolventData
    period hPeriod massSquared 0 1 (Or.inr one_ne_zero)
      (Regularity := Regularity)

/-- Final constant Robin input package. -/
abbrev CanonicalPhysicalScalarCanonicalRobinResolventData
    (massSquared coefficient : Real) :=
  CanonicalPhysicalScalarCanonicalSeparatedResolventData
    period hPeriod massSquared (-coefficient) 1 (Or.inr one_ne_zero)
      (Regularity := Regularity)

namespace CanonicalPhysicalScalarCanonicalSeparatedResolventData

/-- Dirichlet domain is exactly zero completed value trace. -/
theorem mem_dirichletDomain_iff
    (data : CanonicalPhysicalScalarCanonicalDirichletResolventData
      period hPeriod massSquared (Regularity := Regularity))
    (field : data.boundary.triple.MaximalDomain) :
    field ∈ data.boundary.triple.lagrangianDomainSubmodule
        (canonicalPhysicalScalarDirichletCondition period) ↔
      (data.boundary.completedBoundaryTrace period hPeriod field).1 = 0 := by
  change data.boundary.completedBoundaryTrace period hPeriod field ∈
        canonicalScalarHilbertDirichletBoundarySubmodule
          (Trace := BoundaryL2 period) ↔ _
  exact mem_canonicalScalarHilbertDirichletBoundarySubmodule
    (Trace := BoundaryL2 period) _

/-- Neumann domain is exactly zero completed normal trace. -/
theorem mem_neumannDomain_iff
    (data : CanonicalPhysicalScalarCanonicalNeumannResolventData
      period hPeriod massSquared (Regularity := Regularity))
    (field : data.boundary.triple.MaximalDomain) :
    field ∈ data.boundary.triple.lagrangianDomainSubmodule
        (canonicalPhysicalScalarNeumannCondition period) ↔
      (data.boundary.completedBoundaryTrace period hPeriod field).2 = 0 := by
  change data.boundary.completedBoundaryTrace period hPeriod field ∈
        canonicalScalarHilbertNeumannBoundarySubmodule
          (Trace := BoundaryL2 period) ↔ _
  exact mem_canonicalScalarHilbertNeumannBoundarySubmodule
    (Trace := BoundaryL2 period) _

/-- Robin domain is exactly `γ₁ = κ γ₀`. -/
theorem mem_robinDomain_iff
    (coefficient : Real)
    (data : CanonicalPhysicalScalarCanonicalRobinResolventData
      period hPeriod massSquared coefficient (Regularity := Regularity))
    (field : data.boundary.triple.MaximalDomain) :
    field ∈ data.boundary.triple.lagrangianDomainSubmodule
        (canonicalPhysicalScalarRobinCondition period coefficient) ↔
      (data.boundary.completedBoundaryTrace period hPeriod field).2 =
        coefficient •
          (data.boundary.completedBoundaryTrace period hPeriod field).1 := by
  change data.boundary.completedBoundaryTrace period hPeriod field ∈
        canonicalScalarHilbertRobinBoundarySubmodule
          (Trace := BoundaryL2 period) coefficient ↔ _
  exact mem_canonicalScalarHilbertRobinBoundarySubmodule
    (Trace := BoundaryL2 period) coefficient _

/-- Standard-boundary closure certificate. -/
theorem standardBoundary_certificate
    (dirichlet : CanonicalPhysicalScalarCanonicalDirichletResolventData
      period hPeriod massSquared (Regularity := Regularity))
    (neumann : CanonicalPhysicalScalarCanonicalNeumannResolventData
      period hPeriod massSquared (Regularity := Regularity))
    (coefficient : Real)
    (robin : CanonicalPhysicalScalarCanonicalRobinResolventData
      period hPeriod massSquared coefficient (Regularity := Regularity)) :
    dirichlet.boundary.triple.actualAdjointDomain
        (canonicalPhysicalScalarDirichletCondition period) =
      dirichlet.boundary.triple.realizationDomain
        (canonicalPhysicalScalarDirichletCondition period) ∧
      neumann.boundary.triple.actualAdjointDomain
        (canonicalPhysicalScalarNeumannCondition period) =
      neumann.boundary.triple.realizationDomain
        (canonicalPhysicalScalarNeumannCondition period) ∧
      robin.boundary.triple.actualAdjointDomain
        (canonicalPhysicalScalarRobinCondition period coefficient) =
      robin.boundary.triple.realizationDomain
        (canonicalPhysicalScalarRobinCondition period coefficient) :=
  ⟨dirichlet.actualAdjointDomain_eq period hPeriod,
    neumann.actualAdjointDomain_eq period hPeriod,
    robin.actualAdjointDomain_eq period hPeriod⟩

end CanonicalPhysicalScalarCanonicalSeparatedResolventData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalStandardBoundaryResolventClosure4D
end JanusFormal
