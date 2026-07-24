import Mathlib.Analysis.InnerProductSpace.Symmetric
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarResolventEigenvalueCorrespondence4D

/-!
# Operator-valued Robin graphs on the scalar Hilbert boundary space

Constant scalar Robin data are only the simplest Lagrangian graphs.  On a
Hilbert trace space, every bounded symmetric operator `B` defines the boundary
condition

`normalTrace = B valueTrace`.

This file proves that the graph of `B` is closed and Lagrangian for the scalar
Green symplectic form.  The result includes Neumann as `B = 0` and allows later
instantiation by multiplication operators, matrix-valued interface couplings,
or bounded pseudodifferential boundary operators.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarHilbertRobinGraph4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D

universe u

variable {Trace : Type u}
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]

/-- Continuous constraint `normal - B value` for an operator-valued Robin
condition. -/
def canonicalScalarHilbertRobinGraphConstraint
    (robin : Trace →L[Real] Trace) :
    CanonicalScalarHilbertBoundaryDatum (Trace := Trace) →L[Real] Trace :=
  ContinuousLinearMap.snd Real Trace Trace -
    robin.comp (ContinuousLinearMap.fst Real Trace Trace)

@[simp] theorem canonicalScalarHilbertRobinGraphConstraint_apply
    (robin : Trace →L[Real] Trace)
    (datum : CanonicalScalarHilbertBoundaryDatum (Trace := Trace)) :
    canonicalScalarHilbertRobinGraphConstraint robin datum =
      datum.2 - robin datum.1 :=
  rfl

/-- Closed graph of an operator-valued Robin condition. -/
def canonicalScalarHilbertRobinGraphSubmodule
    (robin : Trace →L[Real] Trace) :
    Submodule Real (CanonicalScalarHilbertBoundaryDatum (Trace := Trace)) :=
  LinearMap.ker (canonicalScalarHilbertRobinGraphConstraint robin).toLinearMap

@[simp] theorem mem_canonicalScalarHilbertRobinGraphSubmodule
    (robin : Trace →L[Real] Trace)
    (datum : CanonicalScalarHilbertBoundaryDatum (Trace := Trace)) :
    datum ∈ canonicalScalarHilbertRobinGraphSubmodule robin ↔
      datum.2 = robin datum.1 := by
  rw [canonicalScalarHilbertRobinGraphSubmodule,
    LinearMap.mem_ker]
  change datum.2 - robin datum.1 = 0 ↔ _
  exact sub_eq_zero

/-- Every bounded Robin graph is closed. -/
theorem canonicalScalarHilbertRobinGraphSubmodule_isClosed
    (robin : Trace →L[Real] Trace) :
    IsClosed
      (canonicalScalarHilbertRobinGraphSubmodule robin :
        Set (CanonicalScalarHilbertBoundaryDatum (Trace := Trace))) := by
  change IsClosed {datum |
    canonicalScalarHilbertRobinGraphConstraint robin datum = 0}
  exact isClosed_singleton.preimage
    (canonicalScalarHilbertRobinGraphConstraint robin).continuous

/-- The graph of a symmetric boundary operator is isotropic for the Hilbert
Green form. -/
theorem canonicalScalarHilbertRobinGraphSubmodule_le_orthogonal
    (robin : Trace →L[Real] Trace)
    (hRobin : robin.toLinearMap.IsSymmetric) :
    canonicalScalarHilbertRobinGraphSubmodule robin ≤
      canonicalScalarHilbertBoundarySymplecticOrthogonal
        (canonicalScalarHilbertRobinGraphSubmodule robin) := by
  intro first hFirst second hSecond
  have hFirstGraph :=
    (mem_canonicalScalarHilbertRobinGraphSubmodule robin first).1 hFirst
  have hSecondGraph :=
    (mem_canonicalScalarHilbertRobinGraphSubmodule robin second).1 hSecond
  unfold canonicalScalarHilbertBoundarySymplecticForm
  rw [hFirstGraph, hSecondGraph]
  apply sub_eq_zero.mpr
  simpa using (hRobin first.1 second.1).symm

/-- Symplectic orthogonality to a symmetric Robin graph forces the same Robin
condition. -/
theorem canonicalScalarHilbertBoundarySymplecticOrthogonal_le_robinGraph
    (robin : Trace →L[Real] Trace)
    (hRobin : robin.toLinearMap.IsSymmetric) :
    canonicalScalarHilbertBoundarySymplecticOrthogonal
        (canonicalScalarHilbertRobinGraphSubmodule robin) ≤
      canonicalScalarHilbertRobinGraphSubmodule robin := by
  intro datum hDatum
  let residual : Trace := datum.2 - robin datum.1
  let probe : CanonicalScalarHilbertBoundaryDatum (Trace := Trace) :=
    (residual, robin residual)
  have hProbe : probe ∈ canonicalScalarHilbertRobinGraphSubmodule robin := by
    apply (mem_canonicalScalarHilbertRobinGraphSubmodule robin probe).2
    rfl
  have hOrth := hDatum probe hProbe
  have hOrth' :
      inner Real (robin datum.1) residual -
          inner Real datum.2 residual = 0 := by
    unfold canonicalScalarHilbertBoundarySymplecticForm at hOrth
    dsimp [probe] at hOrth
    have hSymm : inner Real (robin datum.1) residual =
        inner Real datum.1 (robin residual) := by
      simpa using hRobin datum.1 residual
    rw [hSymm]
    exact hOrth
  have hResidualExpanded :
      inner Real residual residual =
        inner Real datum.2 residual -
          inner Real (robin datum.1) residual := by
    simp only [residual, inner_sub_left]
  have hResidualInner : inner Real residual residual = 0 := by
    linarith
  have hResidualNormSq : ‖residual‖ ^ 2 = 0 := by
    rw [← real_inner_self_eq_norm_sq residual]
    exact hResidualInner
  have hResidual : residual = 0 := by
    apply norm_eq_zero.mp
    nlinarith [sq_nonneg ‖residual‖]
  apply (mem_canonicalScalarHilbertRobinGraphSubmodule robin datum).2
  exact sub_eq_zero.mp hResidual

/-- Every bounded symmetric Robin graph is Lagrangian. -/
theorem canonicalScalarHilbertRobinGraphSubmodule_orthogonal_eq
    (robin : Trace →L[Real] Trace)
    (hRobin : robin.toLinearMap.IsSymmetric) :
    canonicalScalarHilbertBoundarySymplecticOrthogonal
        (canonicalScalarHilbertRobinGraphSubmodule robin) =
      canonicalScalarHilbertRobinGraphSubmodule robin := by
  apply le_antisymm
  · exact canonicalScalarHilbertBoundarySymplecticOrthogonal_le_robinGraph
      robin hRobin
  · exact canonicalScalarHilbertRobinGraphSubmodule_le_orthogonal
      robin hRobin

/-- Direct vanishing of the Green form on a symmetric Robin graph. -/
theorem canonicalScalarHilbertBoundarySymplecticForm_eq_zero_of_mem_robinGraph
    (robin : Trace →L[Real] Trace)
    (hRobin : robin.toLinearMap.IsSymmetric)
    (first second : CanonicalScalarHilbertBoundaryDatum (Trace := Trace))
    (hFirst : first ∈ canonicalScalarHilbertRobinGraphSubmodule robin)
    (hSecond : second ∈ canonicalScalarHilbertRobinGraphSubmodule robin) :
    canonicalScalarHilbertBoundarySymplecticForm first second = 0 :=
  canonicalScalarHilbertRobinGraphSubmodule_le_orthogonal
    robin hRobin hFirst second hSecond

/-- The zero Robin operator recovers the Hilbert Neumann boundary subspace. -/
theorem canonicalScalarHilbertRobinGraphSubmodule_zero_eq_neumann :
    canonicalScalarHilbertRobinGraphSubmodule
        (0 : Trace →L[Real] Trace) =
      canonicalScalarHilbertNeumannBoundarySubmodule (Trace := Trace) := by
  ext datum
  simp [canonicalScalarHilbertNeumannBoundarySubmodule]

/-- Scalar multiplication by a real coefficient recovers the previously defined
constant Robin graph. -/
def canonicalScalarHilbertScalarRobinOperator
    (coefficient : Real) : Trace →L[Real] Trace :=
  coefficient • ContinuousLinearMap.id Real Trace

@[simp] theorem canonicalScalarHilbertScalarRobinOperator_apply
    (coefficient : Real) (value : Trace) :
    canonicalScalarHilbertScalarRobinOperator
        (Trace := Trace) coefficient value = coefficient • value := by
  rfl

/-- Scalar Robin multiplication is symmetric. -/
theorem canonicalScalarHilbertScalarRobinOperator_isSymmetric
    (coefficient : Real) :
    (canonicalScalarHilbertScalarRobinOperator
      (Trace := Trace) coefficient).toLinearMap.IsSymmetric := by
  intro first second
  simp [canonicalScalarHilbertScalarRobinOperator,
    real_inner_smul_left, real_inner_smul_right]

/-- Operator-valued Robin specializes exactly to the constant scalar Robin
submodule. -/
theorem canonicalScalarHilbertRobinGraphSubmodule_scalar_eq
    (coefficient : Real) :
    canonicalScalarHilbertRobinGraphSubmodule
        (canonicalScalarHilbertScalarRobinOperator
          (Trace := Trace) coefficient) =
      canonicalScalarHilbertRobinBoundarySubmodule
        (Trace := Trace) coefficient := by
  ext datum
  rw [mem_canonicalScalarHilbertRobinGraphSubmodule,
    mem_canonicalScalarHilbertRobinBoundarySubmodule]
  rfl

/-- Closed-Lagrangian certificate for every bounded symmetric operator-valued
Robin condition. -/
theorem canonicalScalarHilbertRobinGraph_certificate
    (robin : Trace →L[Real] Trace)
    (hRobin : robin.toLinearMap.IsSymmetric) :
    IsClosed
        (canonicalScalarHilbertRobinGraphSubmodule robin :
          Set (CanonicalScalarHilbertBoundaryDatum (Trace := Trace))) ∧
      canonicalScalarHilbertBoundarySymplecticOrthogonal
          (canonicalScalarHilbertRobinGraphSubmodule robin) =
        canonicalScalarHilbertRobinGraphSubmodule robin :=
  ⟨canonicalScalarHilbertRobinGraphSubmodule_isClosed robin,
    canonicalScalarHilbertRobinGraphSubmodule_orthogonal_eq robin hRobin⟩

end
end P0EFTJanusMappingTorusScalarHilbertRobinGraph4D
end JanusFormal
