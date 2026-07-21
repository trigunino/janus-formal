import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D

/-!
# Actual Hilbert adjoint of a completed boundary-triple realization

For a Lagrangian realization `T_L : D_L → H`, a vector `y : H` lies in the
actual Hilbert adjoint domain when there exists `z : H` such that

`<T_L x, y> = <x, z>`

for every `x ∈ D_L`.

The missing elliptic regularity theorem says that every such adjoint pair
`(y,z)` is represented by one vector of the completed maximal graph.  The Green
identity then turns the adjoint relation into symplectic orthogonality to the
boundary condition.  Lagrangian maximality puts the maximal representative back
in `D_L`.

Thus maximal adjoint regularity plus the completed boundary triple proves actual
Hilbert self-adjointness, not merely equality with a formally named boundary
adjoint set.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarCompletedBoundaryTripleActualAdjoint4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

namespace CanonicalScalarCompletedBoundaryTripleData

variable
  {core : CanonicalScalarHilbertGreenCore
    (Domain := Domain) (Ambient := Ambient) (Trace := Trace)}
  {traceBound : HasCanonicalScalarHilbertGreenCoreBoundaryGraphBound core}

/-- Actual Hilbert adjoint admissibility for one Lagrangian realization. -/
def actualAdjointAdmissible
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (candidate : Ambient) : Prop :=
  ∃ adjointValue : Ambient,
    ∀ test : triple.lagrangianDomainSubmodule condition,
      inner Real (triple.lagrangianOperator condition test) candidate =
        inner Real (triple.lagrangianInclusion condition test) adjointValue

/-- Actual Hilbert adjoint domain as a subset of the ambient Hilbert space. -/
def actualAdjointDomain
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace) :
    Set Ambient :=
  {candidate | actualAdjointAdmissible triple condition candidate}

/-- The ambient domain of the original realization. -/
def realizationDomain
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace) :
    Set Ambient :=
  Set.range (triple.lagrangianInclusion condition)

/-- Maximal adjoint regularity: every Hilbert adjoint pair is represented by the
completed maximal graph. -/
structure MaximalAdjointRegularity
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace) where
  represent : ∀ (candidate adjointValue : Ambient),
    (∀ test : triple.lagrangianDomainSubmodule condition,
      inner Real (triple.lagrangianOperator condition test) candidate =
        inner Real (triple.lagrangianInclusion condition test) adjointValue) →
    ∃ maximal : triple.MaximalDomain,
      canonicalScalarGreenCoreGraphInclusion core maximal = candidate ∧
      canonicalScalarGreenCoreGraphOperator core maximal = adjointValue

/-- Every original-domain vector is in the actual Hilbert adjoint domain. -/
theorem realizationDomain_subset_actualAdjointDomain
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace) :
    realizationDomain triple condition ⊆
      actualAdjointDomain triple condition := by
  rintro candidate ⟨field, rfl⟩
  refine ⟨triple.lagrangianOperator condition field, ?_⟩
  intro test
  exact triple.lagrangianOperator_symmetric condition test field

/-- A maximal representative of an actual adjoint pair satisfies the boundary
adjoint test. -/
theorem maximal_mem_boundaryAdjoint_of_actualAdjointPair
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (candidate adjointValue : Ambient)
    (hPair : ∀ test : triple.lagrangianDomainSubmodule condition,
      inner Real (triple.lagrangianOperator condition test) candidate =
        inner Real (triple.lagrangianInclusion condition test) adjointValue)
    (maximal : triple.MaximalDomain)
    (hCandidate : canonicalScalarGreenCoreGraphInclusion core maximal = candidate)
    (hAdjoint : canonicalScalarGreenCoreGraphOperator core maximal = adjointValue) :
    triple.lagrangianAdjointAdmissible condition maximal := by
  intro test
  have hActual := hPair test
  rw [← hCandidate, ← hAdjoint] at hActual
  have hGreen := canonicalScalarGreenCoreCompletedGreenIdentity
    core traceBound maximal test.1
  unfold canonicalScalarGreenCoreCompletedBoundaryPairing at hGreen
  have hFirstComm := real_inner_comm
    (canonicalScalarGreenCoreGraphOperator core maximal)
    (canonicalScalarGreenCoreGraphInclusion core test.1)
  have hSecondComm := real_inner_comm
    (canonicalScalarGreenCoreGraphInclusion core maximal)
    (canonicalScalarGreenCoreGraphOperator core test.1)
  change inner Real
      (canonicalScalarGreenCoreGraphOperator core test.1)
      (canonicalScalarGreenCoreGraphInclusion core maximal) =
    inner Real
      (canonicalScalarGreenCoreGraphInclusion core test.1)
      (canonicalScalarGreenCoreGraphOperator core maximal) at hActual
  linarith

/-- Maximal adjoint regularity gives the reverse domain inclusion. -/
theorem actualAdjointDomain_subset_realizationDomain
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (regularity : MaximalAdjointRegularity triple condition) :
    actualAdjointDomain triple condition ⊆
      realizationDomain triple condition := by
  intro candidate hCandidate
  rcases hCandidate with ⟨adjointValue, hPair⟩
  obtain ⟨maximal, hMaximalCandidate, hMaximalAdjoint⟩ :=
    regularity.represent candidate adjointValue hPair
  have hBoundaryAdjoint :=
    maximal_mem_boundaryAdjoint_of_actualAdjointPair triple
      condition candidate adjointValue hPair maximal
      hMaximalCandidate hMaximalAdjoint
  have hDomain : maximal ∈ triple.lagrangianDomainSubmodule condition :=
    (triple.lagrangianAdjointAdmissible_iff_mem condition maximal).1
      hBoundaryAdjoint
  refine ⟨⟨maximal, hDomain⟩, ?_⟩
  exact hMaximalCandidate

/-- Actual Hilbert adjoint domain equals the realization domain. -/
theorem actualAdjointDomain_eq_realizationDomain
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (regularity : MaximalAdjointRegularity triple condition) :
    actualAdjointDomain triple condition =
      realizationDomain triple condition :=
  Set.Subset.antisymm
    (actualAdjointDomain_subset_realizationDomain triple
      condition regularity)
    (realizationDomain_subset_actualAdjointDomain triple condition)

/-- The adjoint value is the original operator value on the realization domain. -/
theorem actualAdjointValue_eq_operator
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (regularity : MaximalAdjointRegularity triple condition)
    (field : triple.lagrangianDomainSubmodule condition)
    (adjointValue : Ambient)
    (hPair : ∀ test : triple.lagrangianDomainSubmodule condition,
      inner Real (triple.lagrangianOperator condition test)
          (triple.lagrangianInclusion condition field) =
        inner Real (triple.lagrangianInclusion condition test) adjointValue)
    (hDense : DenseRange (triple.lagrangianInclusion condition)) :
    adjointValue = triple.lagrangianOperator condition field := by
  let residual := adjointValue - triple.lagrangianOperator condition field
  have hOrthogonal (test : triple.lagrangianDomainSubmodule condition) :
      inner Real (triple.lagrangianInclusion condition test) residual = 0 := by
    unfold residual
    rw [inner_sub_right, ← hPair test]
    exact sub_eq_zero.mpr
      (triple.lagrangianOperator_symmetric condition test field)
  let good : Set Ambient := {test | inner Real test residual = 0}
  have hGoodClosed : IsClosed good := by
    dsimp [good]
    apply isClosed_eq <;> fun_prop
  have hRange : Set.range (triple.lagrangianInclusion condition) ⊆ good := by
    rintro test ⟨domainTest, rfl⟩
    exact hOrthogonal domainTest
  have hClosure : closure
      (Set.range (triple.lagrangianInclusion condition)) = Set.univ :=
    hDense.closure_range
  have hResidualMem : residual ∈ closure
      (Set.range (triple.lagrangianInclusion condition)) := by
    rw [hClosure]
    trivial
  have hSelf : inner Real residual residual = 0 :=
    (closure_minimal hRange hGoodClosed) hResidualMem
  have hNorm : ‖residual‖ = 0 := by
    have hNormSq : ‖residual‖ ^ 2 = 0 := by
      simpa [real_inner_self_eq_norm_sq] using hSelf
    nlinarith [sq_nonneg ‖residual‖]
  exact sub_eq_zero.mp (norm_eq_zero.mp hNorm)

/-- Actual self-adjointness certificate. -/
theorem actualAdjoint_certificate
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (regularity : MaximalAdjointRegularity triple condition) :
    actualAdjointDomain triple condition =
        realizationDomain triple condition ∧
      triple.lagrangianAdjointDomain condition =
        (triple.lagrangianDomainSubmodule condition :
          Set triple.MaximalDomain) :=
  ⟨actualAdjointDomain_eq_realizationDomain triple condition regularity,
    triple.lagrangianAdjointDomain_eq condition⟩

end CanonicalScalarCompletedBoundaryTripleData

end
end P0EFTJanusMappingTorusScalarCompletedBoundaryTripleActualAdjoint4D
end JanusFormal
