import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarAdjointCoreClosable4D

/-!
# Strong-system bridge after boundary completion

The legacy spectral architecture expects an algebraic Green system whose trace
is already surjective.  For an infinite-dimensional physical boundary this is
appropriate only after graph completion.

A corrected completed boundary triple therefore determines a strong Green
system with domain equal to the completed maximal graph.  Its trace is genuinely
surjective, its Green identity is exact, and its trace graph estimate follows
from continuity.  A dense formal-adjoint test core then proves closability of
this strong presentation, allowing all existing closed Lagrangian resolvent and
spectral results to be reused.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarCompletedBoundaryTripleStrongSystem4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarClosedGraphRealization4D
open P0EFTJanusMappingTorusScalarAdjointCoreClosable4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D

universe u v w z

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  {TestDomain : Type z}
  [AddCommGroup Domain] [Module Real Domain]
  [AddCommGroup TestDomain] [Module Real TestDomain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

namespace CanonicalScalarCompletedBoundaryTripleData

/-- Strong Green system whose domain is the corrected completed maximal graph. -/
def toStrongSystem
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound) :
    CanonicalScalarHilbertGreenSystem
      (Domain := triple.MaximalDomain)
      (Ambient := Ambient) (Trace := Trace) where
  inclusion := (canonicalScalarGreenCoreGraphInclusion core).toLinearMap
  operator := (canonicalScalarGreenCoreGraphOperator core).toLinearMap
  boundaryTrace :=
    (canonicalScalarGreenCoreCompletedBoundaryTrace core traceBound).toLinearMap
  boundary_surjective := triple.boundary_surjective
  green_identity := by
    intro first second
    exact canonicalScalarGreenCoreCompletedGreenIdentity
      core traceBound first second

/-- The strong-system graph map is the original maximal graph point itself. -/
theorem toStrongSystem_graphMap_eq_val
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (field : triple.MaximalDomain) :
    canonicalScalarOperatorGraphLinearMap triple.toStrongSystem field = field.1 :=
  rfl

/-- The norm of the strong-system graph lift is the norm already carried by the
completed maximal graph. -/
theorem toStrongSystem_graphLift_norm
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (field : triple.MaximalDomain) :
    ‖canonicalScalarSmoothToOperatorGraphLinearMap
        triple.toStrongSystem field‖ = ‖field‖ :=
  rfl

/-- Continuity of the completed trace supplies the graph-bound hypothesis for
the strong presentation. -/
def toStrongSystemBoundaryGraphBound
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound) :
    HasCanonicalScalarHilbertBoundaryGraphBound triple.toStrongSystem where
  constant := ‖canonicalScalarGreenCoreCompletedBoundaryTrace core traceBound‖
  nonnegative := norm_nonneg _
  bound := by
    intro field
    rw [triple.toStrongSystem_graphLift_norm]
    exact (canonicalScalarGreenCoreCompletedBoundaryTrace
      core traceBound).le_opNorm field

/-- Dense formal-adjoint test data for the strong completed presentation. -/
structure StrongAdjointTestCore
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound) where
  inclusion : TestDomain →ₗ[Real] Ambient
  operator : TestDomain →ₗ[Real] Ambient
  dense : DenseRange inclusion
  pairing : ∀ field : triple.MaximalDomain, ∀ test : TestDomain,
    inner Real (canonicalScalarGreenCoreGraphOperator core field)
        (inclusion test) =
      inner Real (canonicalScalarGreenCoreGraphInclusion core field)
        (operator test)

/-- Conversion to the generic dense-adjoint-core package. -/
def StrongAdjointTestCore.toGeneric
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (testCore : triple.StrongAdjointTestCore
      (TestDomain := TestDomain)) :
    CanonicalScalarAdjointTestCore
      (TestDomain := TestDomain) triple.toStrongSystem where
  inclusion := testCore.inclusion
  operator := testCore.operator
  dense := testCore.dense
  pairing := testCore.pairing

/-- A dense formal-adjoint core closes the strong completed presentation. -/
theorem toStrongSystem_closable
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (testCore : triple.StrongAdjointTestCore
      (TestDomain := TestDomain)) :
    CanonicalScalarGraphClosable triple.toStrongSystem :=
  (testCore.toGeneric triple).graphClosable

/-- Strong-system bridge certificate. -/
theorem strongSystem_certificate
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (testCore : triple.StrongAdjointTestCore
      (TestDomain := TestDomain)) :
    Function.Surjective triple.toStrongSystem.boundaryTrace ∧
      CanonicalScalarGraphClosable triple.toStrongSystem ∧
      (∀ first second : triple.MaximalDomain,
        inner Real (triple.toStrongSystem.operator first)
              (triple.toStrongSystem.inclusion second) -
            inner Real (triple.toStrongSystem.inclusion first)
              (triple.toStrongSystem.operator second) =
          2 * canonicalScalarHilbertBoundarySymplecticForm
            (triple.toStrongSystem.boundaryTrace first)
            (triple.toStrongSystem.boundaryTrace second)) :=
  ⟨triple.boundary_surjective,
    triple.toStrongSystem_closable testCore,
    triple.toStrongSystem.green_identity⟩

end CanonicalScalarCompletedBoundaryTripleData

end
end P0EFTJanusMappingTorusScalarCompletedBoundaryTripleStrongSystem4D
end JanusFormal
