import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarLagrangianCompactSpectrum4D

/-!
# Symplectic covariance of scalar Lagrangian boundary conditions

The scalar Green form is invariant under canonical symplectic changes of
boundary variables.  This file packages continuous linear symplectomorphisms of
the paired Hilbert trace space and proves that they transport closed Lagrangian
boundary conditions to closed Lagrangian boundary conditions.

Two concrete transformations are supplied:

* the quarter-turn `(value, normal) ↦ (normal, -value)`, exchanging Dirichlet and
  Neumann;
* the symmetric shear `(value, normal) ↦ (value, normal + B value)`, transporting
  Neumann to the graph of a bounded symmetric Robin operator `B`.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarBoundarySymplecticCovariance4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarHilbertRobinGraph4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D

universe u

variable {Trace : Type u}
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]

/-- Continuous linear symplectomorphism of the paired scalar Hilbert trace
space. -/
structure CanonicalScalarHilbertBoundarySymplecticEquiv where
  equiv : CanonicalScalarHilbertBoundaryDatum (Trace := Trace) ≃L[Real]
    CanonicalScalarHilbertBoundaryDatum (Trace := Trace)
  preserves : ∀ first second,
    canonicalScalarHilbertBoundarySymplecticForm
        (equiv first) (equiv second) =
      canonicalScalarHilbertBoundarySymplecticForm first second

namespace CanonicalScalarHilbertBoundarySymplecticEquiv

/-- Identity symplectomorphism. -/
noncomputable def refl :
    CanonicalScalarHilbertBoundarySymplecticEquiv (Trace := Trace) where
  equiv := ContinuousLinearEquiv.refl Real _
  preserves := by intro first second; rfl

/-- Composition of boundary symplectomorphisms. -/
noncomputable def trans
    (first second : CanonicalScalarHilbertBoundarySymplecticEquiv
      (Trace := Trace)) :
    CanonicalScalarHilbertBoundarySymplecticEquiv (Trace := Trace) where
  equiv := first.equiv.trans second.equiv
  preserves := by
    intro x y
    rw [second.preserves, first.preserves]

/-- Inverse boundary symplectomorphism. -/
noncomputable def symm
    (symplectic : CanonicalScalarHilbertBoundarySymplecticEquiv
      (Trace := Trace)) :
    CanonicalScalarHilbertBoundarySymplecticEquiv (Trace := Trace) where
  equiv := symplectic.equiv.symm
  preserves := by
    intro first second
    have h := symplectic.preserves
      (symplectic.equiv.symm first) (symplectic.equiv.symm second)
    simpa using h.symm

/-- Transport of a closed Lagrangian boundary condition by a continuous
symplectomorphism.  The transported subspace is the image, represented as the
preimage under the inverse equivalence. -/
noncomputable def transport
    (symplectic : CanonicalScalarHilbertBoundarySymplecticEquiv
      (Trace := Trace))
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace) :
    CanonicalScalarHilbertLagrangianBoundaryCondition Trace where
  subspace := condition.subspace.comap
    symplectic.equiv.symm.toLinearEquiv.toLinearMap
  isClosed := by
    change IsClosed
      (symplectic.equiv.symm ⁻¹'
        (condition.subspace :
          Set (CanonicalScalarHilbertBoundaryDatum (Trace := Trace))))
    exact condition.isClosed.preimage symplectic.equiv.symm.continuous
  lagrangian := by
    apply le_antisymm
    · intro datum hDatum
      change symplectic.equiv.symm datum ∈ condition.subspace
      rw [← condition.lagrangian]
      intro test hTest
      have hMapped : symplectic.equiv test ∈
          condition.subspace.comap
            symplectic.equiv.symm.toLinearEquiv.toLinearMap := by
        change symplectic.equiv.symm (symplectic.equiv test) ∈
          condition.subspace
        simpa using hTest
      have hOrth := hDatum (symplectic.equiv test) hMapped
      have hPreserves := symplectic.preserves
        (symplectic.equiv.symm datum) test
      simpa using hPreserves.symm.trans hOrth
    · intro datum hDatum test hTest
      have hDatumBase : symplectic.equiv.symm datum ∈ condition.subspace :=
        hDatum
      have hTestBase : symplectic.equiv.symm test ∈ condition.subspace :=
        hTest
      have hZero := condition.pairing_eq_zero
        (symplectic.equiv.symm datum) (symplectic.equiv.symm test)
        hDatumBase hTestBase
      have hPreserves := symplectic.preserves
        (symplectic.equiv.symm datum) (symplectic.equiv.symm test)
      simpa using hPreserves.trans hZero

end CanonicalScalarHilbertBoundarySymplecticEquiv

/-- Canonical symplectic quarter-turn `(u,n) ↦ (n,-u)`. -/
noncomputable def canonicalScalarHilbertBoundaryQuarterTurnEquiv :
    CanonicalScalarHilbertBoundaryDatum (Trace := Trace) ≃L[Real]
      CanonicalScalarHilbertBoundaryDatum (Trace := Trace) where
  toFun datum := (datum.2, -datum.1)
  invFun datum := (-datum.2, datum.1)
  left_inv := by intro datum; ext <;> simp
  right_inv := by intro datum; ext <;> simp
  map_add' := by intro first second; ext <;> simp
  map_smul' := by intro scalar datum; ext <;> simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The quarter-turn preserves the Green symplectic form. -/
noncomputable def canonicalScalarHilbertBoundaryQuarterTurn :
    CanonicalScalarHilbertBoundarySymplecticEquiv (Trace := Trace) where
  equiv := canonicalScalarHilbertBoundaryQuarterTurnEquiv (Trace := Trace)
  preserves := by
    intro first second
    unfold canonicalScalarHilbertBoundarySymplecticForm
    dsimp [canonicalScalarHilbertBoundaryQuarterTurnEquiv]
    simp [inner_neg_left, inner_neg_right]
    ring

/-- Quarter-turn transport exchanges Dirichlet and Neumann. -/
theorem canonicalScalarHilbertBoundaryQuarterTurn_dirichlet_eq_neumann :
    CanonicalScalarHilbertBoundarySymplecticEquiv.transport
        (canonicalScalarHilbertBoundaryQuarterTurn (Trace := Trace))
        (CanonicalScalarHilbertLagrangianBoundaryCondition.dirichlet
          (Trace := Trace)) =
      CanonicalScalarHilbertLagrangianBoundaryCondition.neumann
        (Trace := Trace) := by
  apply CanonicalScalarHilbertLagrangianBoundaryCondition.ext
  ext datum
  change (-datum.2, datum.1) ∈
      canonicalScalarHilbertDirichletBoundarySubmodule (Trace := Trace) ↔
    datum ∈ canonicalScalarHilbertNeumannBoundarySubmodule (Trace := Trace)
  simp

/-- Symmetric boundary shear `(u,n) ↦ (u,n + B u)`. -/
noncomputable def canonicalScalarHilbertBoundaryShearEquiv
    (robin : Trace →L[Real] Trace) :
    CanonicalScalarHilbertBoundaryDatum (Trace := Trace) ≃L[Real]
      CanonicalScalarHilbertBoundaryDatum (Trace := Trace) where
  toFun datum := (datum.1, datum.2 + robin datum.1)
  invFun datum := (datum.1, datum.2 - robin datum.1)
  left_inv := by intro datum; ext <;> simp
  right_inv := by intro datum; ext <;> simp
  map_add' := by intro first second; ext <;> simp [map_add]
  map_smul' := by intro scalar datum; ext <;> simp [map_smul]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- A shear by a bounded symmetric operator preserves the Green symplectic
form. -/
noncomputable def canonicalScalarHilbertBoundaryShear
    (robin : Trace →L[Real] Trace)
    (hRobin : robin.toLinearMap.IsSymmetric) :
    CanonicalScalarHilbertBoundarySymplecticEquiv (Trace := Trace) where
  equiv := canonicalScalarHilbertBoundaryShearEquiv robin
  preserves := by
    intro first second
    unfold canonicalScalarHilbertBoundarySymplecticForm
    dsimp [canonicalScalarHilbertBoundaryShearEquiv]
    rw [inner_add_right, inner_add_left, hRobin first.1 second.1]
    ring

/-- A symmetric shear transports Neumann exactly to the Robin graph of the
shearing operator. -/
theorem canonicalScalarHilbertBoundaryShear_neumann_eq_robinGraph
    (robin : Trace →L[Real] Trace)
    (hRobin : robin.toLinearMap.IsSymmetric) :
    CanonicalScalarHilbertBoundarySymplecticEquiv.transport
        (canonicalScalarHilbertBoundaryShear robin hRobin)
        (CanonicalScalarHilbertLagrangianBoundaryCondition.neumann
          (Trace := Trace)) =
      CanonicalScalarHilbertLagrangianBoundaryCondition.robinGraph
        robin hRobin := by
  apply CanonicalScalarHilbertLagrangianBoundaryCondition.ext
  ext datum
  change (datum.1, datum.2 - robin datum.1) ∈
      canonicalScalarHilbertNeumannBoundarySubmodule (Trace := Trace) ↔
    datum ∈ canonicalScalarHilbertRobinGraphSubmodule robin
  rw [mem_canonicalScalarHilbertNeumannBoundarySubmodule,
    mem_canonicalScalarHilbertRobinGraphSubmodule]
  exact sub_eq_zero

/-- Covariance certificate for the two basic boundary symplectomorphisms. -/
theorem canonicalScalarBoundarySymplecticCovariance_certificate
    (robin : Trace →L[Real] Trace)
    (hRobin : robin.toLinearMap.IsSymmetric) :
    CanonicalScalarHilbertBoundarySymplecticEquiv.transport
        (canonicalScalarHilbertBoundaryQuarterTurn (Trace := Trace))
        (CanonicalScalarHilbertLagrangianBoundaryCondition.dirichlet
          (Trace := Trace)) =
      CanonicalScalarHilbertLagrangianBoundaryCondition.neumann
        (Trace := Trace) ∧
    CanonicalScalarHilbertBoundarySymplecticEquiv.transport
        (canonicalScalarHilbertBoundaryShear robin hRobin)
        (CanonicalScalarHilbertLagrangianBoundaryCondition.neumann
          (Trace := Trace)) =
      CanonicalScalarHilbertLagrangianBoundaryCondition.robinGraph
        robin hRobin :=
  ⟨canonicalScalarHilbertBoundaryQuarterTurn_dirichlet_eq_neumann,
    canonicalScalarHilbertBoundaryShear_neumann_eq_robinGraph robin hRobin⟩

end
end P0EFTJanusMappingTorusScalarBoundarySymplecticCovariance4D
end JanusFormal
