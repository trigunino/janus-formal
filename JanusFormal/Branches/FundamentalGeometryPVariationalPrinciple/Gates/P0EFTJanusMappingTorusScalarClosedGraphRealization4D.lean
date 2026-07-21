import Mathlib.Algebra.Module.Submodule.Equiv
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCompletedBoundaryDomains4D

/-!
# Closable scalar closed-graph realization

The preceding gates construct the closure of the algebraic graph in
`Ambient × Ambient`, together with its completed value/normal trace and Green
identity.  This file isolates the exact single-valuedness condition required to
read that closed relation as an actual closed operator.

Under injectivity of the first graph projection, the closed graph is linearly
equivalent to its ambient domain.  The second projection becomes a genuine
linear operator on that domain, the completed boundary trace descends to the
same domain, and the completed Green identity is transported without loss.

No closability or graph estimate is hidden: both remain explicit hypotheses of
the resulting realization.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarClosedGraphRealization4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryDomains4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

/-- Vertical vectors in the closed graph: graph elements whose ambient field
coordinate vanishes. -/
def canonicalScalarOperatorGraphVerticalSubmodule
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace)) :
    Submodule Real (CanonicalScalarOperatorGraphSpace data) :=
  LinearMap.ker (canonicalScalarOperatorGraphInclusion data).toLinearMap

@[simp] theorem mem_canonicalScalarOperatorGraphVerticalSubmodule
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (field : CanonicalScalarOperatorGraphSpace data) :
    field ∈ canonicalScalarOperatorGraphVerticalSubmodule data ↔
      canonicalScalarOperatorGraphInclusion data field = 0 :=
  Iff.rfl

/-- The closed graph is single-valued over its first coordinate.  This is the
operator-theoretic closability condition in the graph model used here. -/
def CanonicalScalarGraphClosable
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace)) : Prop :=
  Function.Injective (canonicalScalarOperatorGraphInclusion data)

/-- Closability kills the vertical part of the closed graph. -/
theorem canonicalScalarOperatorGraphVerticalSubmodule_eq_bot
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data) :
    canonicalScalarOperatorGraphVerticalSubmodule data = ⊥ := by
  apply LinearMap.ker_eq_bot.mpr
  intro first second hEqual
  exact hClosable hEqual

/-- Ambient domain of the closed operator: the range of the first graph
projection. -/
def canonicalScalarClosedOperatorDomain
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace)) :
    Submodule Real Ambient :=
  LinearMap.range (canonicalScalarOperatorGraphInclusion data).toLinearMap

/-- Under closability, the graph is linearly equivalent to its ambient domain. -/
noncomputable def canonicalScalarGraphToClosedDomainEquiv
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data) :
    CanonicalScalarOperatorGraphSpace data ≃ₗ[Real]
      canonicalScalarClosedOperatorDomain data :=
  LinearEquiv.ofInjective
    (canonicalScalarOperatorGraphInclusion data).toLinearMap
    (by
      intro first second hEqual
      exact hClosable hEqual)

/-- Canonical inclusion of the actual closed-operator domain into the ambient
Hilbert space. -/
def canonicalScalarClosedOperatorInclusion
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace)) :
    canonicalScalarClosedOperatorDomain data →ₗ[Real] Ambient :=
  (canonicalScalarClosedOperatorDomain data).subtype

/-- The genuine single-valued closed operator obtained from the second graph
coordinate. -/
noncomputable def canonicalScalarClosedOperator
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data) :
    canonicalScalarClosedOperatorDomain data →ₗ[Real] Ambient :=
  (canonicalScalarOperatorGraphOperator data).toLinearMap.comp
    (canonicalScalarGraphToClosedDomainEquiv data hClosable).symm.toLinearMap

/-- Completed paired boundary trace transported to the actual closed-operator
domain. -/
noncomputable def canonicalScalarClosedBoundaryTrace
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data) :
    canonicalScalarClosedOperatorDomain data →ₗ[Real]
      CanonicalScalarHilbertBoundaryDatum (Trace := Trace) :=
  (canonicalScalarCompletedBoundaryTrace data traceBound).toLinearMap.comp
    (canonicalScalarGraphToClosedDomainEquiv data hClosable).symm.toLinearMap

@[simp] theorem canonicalScalarGraphToClosedDomainEquiv_coe
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (field : CanonicalScalarOperatorGraphSpace data) :
    ((canonicalScalarGraphToClosedDomainEquiv data hClosable field :
        canonicalScalarClosedOperatorDomain data) : Ambient) =
      canonicalScalarOperatorGraphInclusion data field :=
  rfl

@[simp] theorem canonicalScalarGraphInclusion_equiv_symm
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (field : canonicalScalarClosedOperatorDomain data) :
    canonicalScalarOperatorGraphInclusion data
        ((canonicalScalarGraphToClosedDomainEquiv data hClosable).symm field) =
      (field : Ambient) := by
  have hEqual := congrArg Subtype.val
    ((canonicalScalarGraphToClosedDomainEquiv data hClosable).apply_symm_apply field)
  simpa using hEqual

@[simp] theorem canonicalScalarClosedOperatorInclusion_equiv
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (field : CanonicalScalarOperatorGraphSpace data) :
    canonicalScalarClosedOperatorInclusion data
        (canonicalScalarGraphToClosedDomainEquiv data hClosable field) =
      canonicalScalarOperatorGraphInclusion data field :=
  rfl

@[simp] theorem canonicalScalarClosedOperator_equiv
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (field : CanonicalScalarOperatorGraphSpace data) :
    canonicalScalarClosedOperator data hClosable
        (canonicalScalarGraphToClosedDomainEquiv data hClosable field) =
      canonicalScalarOperatorGraphOperator data field := by
  simp [canonicalScalarClosedOperator]

@[simp] theorem canonicalScalarClosedBoundaryTrace_equiv
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (field : CanonicalScalarOperatorGraphSpace data) :
    canonicalScalarClosedBoundaryTrace data hClosable traceBound
        (canonicalScalarGraphToClosedDomainEquiv data hClosable field) =
      canonicalScalarCompletedBoundaryTrace data traceBound field := by
  simp [canonicalScalarClosedBoundaryTrace]

/-- The actual closed operator reconstructs both coordinates of every graph
vector. -/
theorem canonicalScalarClosedOperator_reconstructs_graph
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (field : CanonicalScalarOperatorGraphSpace data) :
    (canonicalScalarClosedOperatorInclusion data
        (canonicalScalarGraphToClosedDomainEquiv data hClosable field),
      canonicalScalarClosedOperator data hClosable
        (canonicalScalarGraphToClosedDomainEquiv data hClosable field)) =
      (canonicalScalarOperatorGraphInclusion data field,
        canonicalScalarOperatorGraphOperator data field) := by
  apply Prod.ext <;> simp

/-- Surjectivity of the completed paired trace survives passage from the graph
to the actual closed-operator domain. -/
theorem canonicalScalarClosedBoundaryTrace_surjective
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data) :
    Function.Surjective
      (canonicalScalarClosedBoundaryTrace data hClosable traceBound) := by
  intro boundary
  obtain ⟨field, hField⟩ :=
    canonicalScalarCompletedBoundaryTrace_surjective data traceBound boundary
  refine ⟨canonicalScalarGraphToClosedDomainEquiv data hClosable field, ?_⟩
  simpa using hField

/-- Exact Green identity on the genuine closed-operator domain. -/
theorem canonicalScalarClosedGreenIdentity
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (first second : canonicalScalarClosedOperatorDomain data) :
    inner Real (canonicalScalarClosedOperator data hClosable first)
          (canonicalScalarClosedOperatorInclusion data second) -
        inner Real (canonicalScalarClosedOperatorInclusion data first)
          (canonicalScalarClosedOperator data hClosable second) =
      2 * canonicalScalarHilbertBoundarySymplecticForm
        (canonicalScalarClosedBoundaryTrace data hClosable traceBound first)
        (canonicalScalarClosedBoundaryTrace data hClosable traceBound second) := by
  let firstGraph :=
    (canonicalScalarGraphToClosedDomainEquiv data hClosable).symm first
  let secondGraph :=
    (canonicalScalarGraphToClosedDomainEquiv data hClosable).symm second
  have hGreen := canonicalScalarCompletedGreenIdentity
    data traceBound firstGraph secondGraph
  simpa [canonicalScalarClosedOperator,
    canonicalScalarClosedOperatorInclusion,
    canonicalScalarClosedBoundaryTrace,
    firstGraph, secondGraph] using hGreen

/-- Closed-graph realization certificate: single-valued ambient inclusion,
surjective paired trace, and the transported Green identity. -/
theorem canonicalScalarClosedGraphRealization_certificate
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data) :
    Function.Injective (canonicalScalarClosedOperatorInclusion data) ∧
      Function.Surjective
        (canonicalScalarClosedBoundaryTrace data hClosable traceBound) ∧
      (∀ first second : canonicalScalarClosedOperatorDomain data,
        inner Real (canonicalScalarClosedOperator data hClosable first)
              (canonicalScalarClosedOperatorInclusion data second) -
            inner Real (canonicalScalarClosedOperatorInclusion data first)
              (canonicalScalarClosedOperator data hClosable second) =
          2 * canonicalScalarHilbertBoundarySymplecticForm
            (canonicalScalarClosedBoundaryTrace data hClosable traceBound first)
            (canonicalScalarClosedBoundaryTrace data hClosable traceBound second)) := by
  refine ⟨?_, canonicalScalarClosedBoundaryTrace_surjective
      data hClosable traceBound,
    canonicalScalarClosedGreenIdentity data hClosable traceBound⟩
  intro first second hEqual
  exact Subtype.ext hEqual

end
end P0EFTJanusMappingTorusScalarClosedGraphRealization4D
end JanusFormal
