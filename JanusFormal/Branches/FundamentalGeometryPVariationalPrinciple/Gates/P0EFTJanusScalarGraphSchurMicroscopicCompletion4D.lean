import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarGraphBoundaryReducedAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusHilbertBoundaryParentSchurSelection

/-!
# Scalar graph Schur target and microscopic parent completion

The existing Poisson/Green construction already provides a symmetric
Dirichlet-to-Neumann/Robin Schur operator on the completed trace Hilbert space.
This gate turns its represented bilinear form into the reduced target of the
Hilbert parent-selection theorem.  Hence every supplied microscopic bulk
fingerprint has one and only one bounded parent completion reproducing that
actual graph-boundary response.
-/

namespace JanusFormal
namespace P0EFTJanusScalarGraphSchurMicroscopicCompletion4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarGraphPoissonDirichletToNeumann4D
open P0EFTJanusMappingTorusScalarGraphBoundaryReducedAction4D
open P0EFTJanusHilbertBoundaryParentSchurSelection

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

/-- Continuous bilinear form represented by one bounded trace operator. -/
def traceOperatorPairing
    (operator : Trace →L[Real] Trace) :
    Trace →L[Real] Trace →L[Real] Real :=
  (innerSL Real).bilinearComp operator (ContinuousLinearMap.id Real Trace)

omit [CompleteSpace Trace] in
@[simp]
theorem traceOperatorPairing_apply
    (operator : Trace →L[Real] Trace) (left right : Trace) :
    traceOperatorPairing operator left right =
      inner Real (operator left) right := rfl

omit [CompleteSpace Trace] in
theorem trace_operator_pairing_symmetric
    (operator : Trace →L[Real] Trace)
    (hSymmetric : operator.toLinearMap.IsSymmetric)
    (left right : Trace) :
    traceOperatorPairing operator left right =
      traceOperatorPairing operator right left := by
  rw [traceOperatorPairing_apply, traceOperatorPairing_apply]
  calc
    inner Real (operator left) right =
        inner Real left (operator right) := hSymmetric left right
    _ = inner Real (operator right) left := real_inner_comm _ _

/-- The actual graph-boundary Schur response as a Hilbert reduced target. -/
def scalarGraphSchurReducedTarget
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace)
    (hRobin : robin.toLinearMap.IsSymmetric) :
    HilbertReducedTarget Trace :=
  { pairing := traceOperatorPairing
      (canonicalScalarGraphBoundarySchurOperator
        data traceBound spectralParameter poissonData robin)
    pairing_symmetric := trace_operator_pairing_symmetric _
      (canonicalScalarGraphBoundarySchurOperator_isSymmetric
        data traceBound spectralParameter poissonData robin hRobin) }

theorem scalar_graph_schur_target_pairing
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace)
    (hRobin : robin.toLinearMap.IsSymmetric) :
    (scalarGraphSchurReducedTarget data traceBound spectralParameter
      poissonData robin hRobin).pairing =
      traceOperatorPairing
        (canonicalScalarGraphBoundarySchurOperator
          data traceBound spectralParameter poissonData robin) := rfl

/-- Two explicit, distinct bulk fingerprints available over every trace
Hilbert space. -/
def unitBulkFingerprint : HilbertBulkFingerprint Trace :=
  { bulkCoefficient := 1
    bulkCoupling := 0
    bulkCoefficientNonzero := one_ne_zero }

def doubledBulkFingerprint : HilbertBulkFingerprint Trace :=
  { bulkCoefficient := 2
    bulkCoupling := 0
    bulkCoefficientNonzero := by norm_num }

omit [CompleteSpace Trace] in
theorem unit_bulk_fingerprint_ne_doubled :
    unitBulkFingerprint (Trace := Trace) ≠ doubledBulkFingerprint := by
  intro hEqual
  have hCoefficient := congrArg HilbertBulkFingerprint.bulkCoefficient hEqual
  norm_num [unitBulkFingerprint, doubledBulkFingerprint] at hCoefficient

/-- The actual scalar graph Schur response has exactly one bounded parent for
every supplied microscopic bulk fingerprint. -/
theorem scalar_graph_schur_has_unique_parent_completion
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace)
    (hRobin : robin.toLinearMap.IsSymmetric)
    (fingerprint : HilbertBulkFingerprint Trace) :
    ∃! parent : HilbertBoundaryParentData Trace,
      ParentHasHilbertBulkFingerprint parent fingerprint /\
        reducedBoundaryPairing parent =
          traceOperatorPairing
            (canonicalScalarGraphBoundarySchurOperator
              data traceBound spectralParameter poissonData robin) := by
  simpa [scalarGraphSchurReducedTarget] using
    (conditional_hilbert_microscopic_parent_completion
      Trace fingerprint
        (scalarGraphSchurReducedTarget data traceBound spectralParameter
          poissonData robin hRobin))

/-- The actual graph Schur response alone cannot select a microscopic bulk
fingerprint: two distinct completed parents reduce to exactly that response. -/
theorem scalar_graph_schur_does_not_select_bulk_fingerprint
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace)
    (hRobin : robin.toLinearMap.IsSymmetric) :
    let target := scalarGraphSchurReducedTarget data traceBound
      spectralParameter poissonData robin hRobin
    let firstParent := hilbertParentCompletion
      (unitBulkFingerprint (Trace := Trace)) target
    let secondParent := hilbertParentCompletion
      (doubledBulkFingerprint (Trace := Trace)) target
    firstParent ≠ secondParent /\
      reducedBoundaryPairing firstParent = target.pairing /\
      reducedBoundaryPairing secondParent = target.pairing := by
  dsimp only
  refine ⟨?_, hilbert_parent_completion_reduces_exactly _ _,
    hilbert_parent_completion_reduces_exactly _ _⟩
  intro hParents
  have hCoefficient := congrArg HilbertBoundaryParentData.bulkCoefficient hParents
  norm_num [hilbertParentCompletion, unitBulkFingerprint,
    doubledBulkFingerprint] at hCoefficient

end
end P0EFTJanusScalarGraphSchurMicroscopicCompletion4D
end JanusFormal
