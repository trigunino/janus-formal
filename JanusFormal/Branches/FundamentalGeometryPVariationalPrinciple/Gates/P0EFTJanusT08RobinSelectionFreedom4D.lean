import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D

/-!
# T08: Robin consistency and independent boundary selection

The existing scalar Green system admits every bounded symmetric Robin graph.
With the value and normal traces held fixed, these graphs and their completed
domains retain the entire Robin operator. In particular, closed Lagrangian
boundary consistency leaves an injective real family of scalar Robin domains.
A nonzero marked value/normal observation determines the scalar coefficient.

These are boundary-domain statements; they neither select a Janus coefficient
nor assert actual operator self-adjointness without the existing regularity
hypotheses. Trace coordinates are marked, so no quotient by boundary shears is
being taken.
-/

namespace JanusFormal
namespace P0EFTJanusT08RobinSelectionFreedom4D

set_option autoImplicit false
noncomputable section

open Set
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarHilbertRobinGraph4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryDomains4D
open P0EFTJanusMappingTorusScalarClosedGraphRealization4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D

universe u v w

variable {Trace : Type w}
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]

/-- A Robin graph determines the whole operator in fixed trace coordinates. -/
theorem robin_graph_injective :
    Function.Injective (canonicalScalarHilbertRobinGraphSubmodule
      (Trace := Trace)) := by
  intro first second hGraph
  ext value
  have hMem : (value, first value) ∈
      canonicalScalarHilbertRobinGraphSubmodule first := by simp
  rw [hGraph] at hMem
  exact (mem_canonicalScalarHilbertRobinGraphSubmodule
    second (value, first value)).1 hMem

/-- The scalar coefficient is not lost in the Robin operator. -/
theorem scalar_robin_operator_injective [Nontrivial Trace] :
    Function.Injective (canonicalScalarHilbertScalarRobinOperator
      (Trace := Trace)) := by
  intro first second hOperator
  obtain ⟨value, hValue⟩ := exists_ne (0 : Trace)
  apply smul_left_injective Real hValue
  exact congrArg (fun operator : Trace →L[Real] Trace => operator value) hOperator

/-- Every coefficient uses the existing closed Lagrangian Robin constructor. -/
def robinCondition (coefficient : Real) :
    CanonicalScalarHilbertLagrangianBoundaryCondition Trace :=
  CanonicalScalarHilbertLagrangianBoundaryCondition.robinGraph
    (canonicalScalarHilbertScalarRobinOperator coefficient)
    (canonicalScalarHilbertScalarRobinOperator_isSymmetric coefficient)

theorem robin_condition_subspace_injective [Nontrivial Trace] :
    Function.Injective (fun coefficient : Real =>
      (robinCondition (Trace := Trace) coefficient).subspace) := by
  intro first second hSubspace
  exact scalar_robin_operator_injective (robin_graph_injective hSubspace)

/-- One nonzero marked trace pair already distinguishes scalar Robin data. -/
theorem coefficient_eq_of_marked_trace
    (first second : Real) (value normal : Trace) (hValue : value ≠ 0)
    (hFirst : (value, normal) ∈ (robinCondition first).subspace)
    (hSecond : (value, normal) ∈ (robinCondition second).subspace) :
    first = second := by
  apply smul_left_injective Real hValue
  have hFirst' : normal = first • value :=
    (mem_canonicalScalarHilbertRobinGraphSubmodule _ _).1 hFirst
  have hSecond' : normal = second • value :=
    (mem_canonicalScalarHilbertRobinGraphSubmodule _ _).1 hSecond
  exact hFirst'.symm.trans hSecond'

/-- The response of one nonzero marked trace gives an explicit selector. -/
theorem coefficient_from_marked_trace
    (coefficient : Real) (value normal : Trace) (hValue : value ≠ 0)
    (hGraph : (value, normal) ∈ (robinCondition coefficient).subspace) :
    coefficient = inner Real value normal / ‖value‖ ^ 2 := by
  have hNormal : normal = coefficient • value :=
    (mem_canonicalScalarHilbertRobinGraphSubmodule _ _).1 hGraph
  apply (eq_div_iff (pow_ne_zero 2 (norm_ne_zero_iff.mpr hValue))).2
  simp [hNormal, real_inner_smul_right]

variable {Domain : Type u} {Ambient : Type v}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient] [CompleteSpace Trace]

/-- Surjective completed trace makes every boundary subspace observable in its
domain, without any choice of a Robin coefficient. -/
theorem completed_domain_eq_iff_boundary_subspace_eq
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (first second : CanonicalScalarHilbertLagrangianBoundaryCondition Trace) :
    canonicalScalarCompletedLagrangianDomainSubmodule data traceBound first =
        canonicalScalarCompletedLagrangianDomainSubmodule data traceBound second ↔
      first.subspace = second.subspace := by
  constructor
  · intro hDomain
    exact Submodule.comap_injective_of_surjective
      (canonicalScalarCompletedBoundaryTrace_surjective data traceBound) hDomain
  · intro hSubspace
    unfold canonicalScalarCompletedLagrangianDomainSubmodule
    rw [hSubspace]

/-- The same distinction survives passage to the genuine closed domain when
the Green graph is closable. -/
theorem closed_domain_eq_iff_boundary_subspace_eq
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (first second : CanonicalScalarHilbertLagrangianBoundaryCondition Trace) :
    canonicalScalarClosedLagrangianDomainSubmodule data hClosable traceBound first =
        canonicalScalarClosedLagrangianDomainSubmodule data hClosable traceBound second ↔
      first.subspace = second.subspace := by
  constructor
  · intro hDomain
    exact Submodule.comap_injective_of_surjective
      (canonicalScalarClosedBoundaryTrace_surjective data hClosable traceBound) hDomain
  · intro hSubspace
    unfold canonicalScalarClosedLagrangianDomainSubmodule
    rw [hSubspace]

/-- There is an injective real family of completed Robin domains: closed
Lagrangian boundary consistency alone does not choose its parameter. -/
theorem completed_robin_domains_injective [Nontrivial Trace]
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data) :
    Function.Injective (fun coefficient : Real =>
      canonicalScalarCompletedLagrangianDomainSubmodule data traceBound
        (robinCondition coefficient)) := by
  intro first second hDomain
  exact robin_condition_subspace_injective
    ((completed_domain_eq_iff_boundary_subspace_eq data traceBound _ _).1 hDomain)

theorem closed_robin_domains_injective [Nontrivial Trace]
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data) :
    Function.Injective (fun coefficient : Real =>
      canonicalScalarClosedLagrangianDomainSubmodule data hClosable traceBound
        (robinCondition coefficient)) := by
  intro first second hDomain
  exact robin_condition_subspace_injective
    ((closed_domain_eq_iff_boundary_subspace_eq data hClosable traceBound _ _).1 hDomain)

/-- All members of that real family are closed and equal their boundary-adjoint
domains. This is boundary maximality, with actual adjoint regularity separate. -/
theorem completed_robin_consistency_for_every_coefficient
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (coefficient : Real) :
    IsClosed (canonicalScalarCompletedLagrangianDomainSubmodule
      data traceBound (robinCondition coefficient) :
      Set (CanonicalScalarOperatorGraphSpace data)) ∧
    canonicalScalarCompletedLagrangianAdjointDomain
        data traceBound (robinCondition coefficient) =
      (canonicalScalarCompletedLagrangianDomainSubmodule
        data traceBound (robinCondition coefficient) :
        Set (CanonicalScalarOperatorGraphSpace data)) :=
  ⟨canonicalScalarCompletedLagrangianDomainSubmodule_isClosed data traceBound _,
    canonicalScalarCompletedLagrangianAdjointDomain_eq data traceBound _⟩

end
end P0EFTJanusT08RobinSelectionFreedom4D
end JanusFormal
