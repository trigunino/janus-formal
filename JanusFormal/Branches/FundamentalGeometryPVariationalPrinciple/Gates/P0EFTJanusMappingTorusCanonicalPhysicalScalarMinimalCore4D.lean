import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGraphTraceBound4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarAdjointCoreClosable4D

/-!
# The physical zero-Cauchy core closes the maximal scalar graph

The smooth minimal scalar domain consists of fields whose first-sheet value and
normal traces both vanish.  The physical Green identity then has no boundary
term when an arbitrary maximal-core field is tested against a minimal-core
field.

If this minimal inclusion is dense in bulk L2, it is a dense formal-adjoint test
core.  The maximal physical Euler graph is therefore closable.  Together with
the paired graph-trace bound this produces the actual closed maximal operator,
its completed Cauchy trace and the exact closed-domain Green identity.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarMinimalCore4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenSystem4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGraphTraceBound4D
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarClosedGraphRealization4D
open P0EFTJanusMappingTorusScalarAdjointCoreClosable4D

variable (period : Real) (hPeriod : period ≠ 0)

namespace CanonicalPhysicalScalarFirstSheetGreenData

/-- Smooth minimal physical domain `γ₀u = 0`, `γ₁u = 0`. -/
def smoothMinimalDomainSubmodule
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared) :
    Submodule Real (SmoothQuotientField period hPeriod Real) :=
  LinearMap.ker green.system.boundaryTrace

@[simp] theorem mem_smoothMinimalDomainSubmodule
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared)
    (field : SmoothQuotientField period hPeriod Real) :
    field ∈ green.smoothMinimalDomainSubmodule period hPeriod ↔
      smoothCanonicalPhysicalScalarFirstSheetValueL2
          period hPeriod field = 0 ∧
        smoothCanonicalPhysicalScalarFirstSheetNormalL2
          period hPeriod field = 0 := by
  rw [smoothMinimalDomainSubmodule, LinearMap.mem_ker]
  change
    (smoothCanonicalPhysicalScalarFirstSheetValueL2 period hPeriod field,
      smoothCanonicalPhysicalScalarFirstSheetNormalL2 period hPeriod field) = 0 ↔ _
  constructor
  · intro hZero
    exact ⟨congrArg Prod.fst hZero, congrArg Prod.snd hZero⟩
  · rintro ⟨hValue, hNormal⟩
    apply Prod.ext <;> simpa

/-- Minimal-core inclusion into physical bulk L2. -/
def smoothMinimalInclusion
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared) :
    green.smoothMinimalDomainSubmodule period hPeriod →ₗ[Real]
      CanonicalPhysicalBulkL2 period hPeriod :=
  green.system.inclusion.comp
    (green.smoothMinimalDomainSubmodule period hPeriod).subtype

/-- Minimal-core Euler operator. -/
def smoothMinimalOperator
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared) :
    green.smoothMinimalDomainSubmodule period hPeriod →ₗ[Real]
      CanonicalPhysicalBulkL2 period hPeriod :=
  green.system.operator.comp
    (green.smoothMinimalDomainSubmodule period hPeriod).subtype

/-- The maximal physical operator pairs with the minimal core by the formal
adjoint identity. -/
theorem maximal_minimal_pairing
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared)
    (field : SmoothQuotientField period hPeriod Real)
    (test : green.smoothMinimalDomainSubmodule period hPeriod) :
    inner Real (green.system.operator field)
        (green.smoothMinimalInclusion period hPeriod test) =
      inner Real (green.system.inclusion field)
        (green.smoothMinimalOperator period hPeriod test) := by
  have hGreen := green.system.green_identity field test.1
  have hTraceZero : green.system.boundaryTrace test.1 = 0 :=
    LinearMap.mem_ker.mp test.2
  rw [hTraceZero,
    canonicalScalarHilbertBoundarySymplecticForm_zero_right] at hGreen
  linarith

/-- Density of the zero-Cauchy smooth core.  This is the exact density theorem
needed to close the maximal physical Euler graph. -/
def SmoothMinimalCoreDense
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared) : Prop :=
  DenseRange (green.smoothMinimalInclusion period hPeriod)

/-- The physical minimal core as a dense formal-adjoint test package. -/
def minimalAdjointTestCore
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared)
    (hDense : green.SmoothMinimalCoreDense period hPeriod) :
    CanonicalScalarAdjointTestCore
      (TestDomain := green.smoothMinimalDomainSubmodule period hPeriod)
      green.system where
  inclusion := green.smoothMinimalInclusion period hPeriod
  operator := green.smoothMinimalOperator period hPeriod
  dense := hDense
  pairing := green.maximal_minimal_pairing period hPeriod

/-- Density of zero-Cauchy test fields implies closability of the maximal
physical scalar operator. -/
theorem maximalGraph_closable_of_minimal_dense
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared)
    (hDense : green.SmoothMinimalCoreDense period hPeriod) :
    CanonicalScalarGraphClosable green.system :=
  (green.minimalAdjointTestCore period hPeriod hDense).graphClosable

/-- Full physical maximal-operator closure inputs. -/
structure MaximalClosureData
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared) where
  coarea : CanonicalPhysicalScalarLatitudeCoareaTheorem period hPeriod
  elliptic : CanonicalPhysicalScalarGraphEllipticEstimate
    period hPeriod green
  normal : CanonicalPhysicalScalarNormalGraphEstimate
    period hPeriod green
  minimalDense : green.SmoothMinimalCoreDense period hPeriod

namespace MaximalClosureData

/-- Paired graph bound supplied by the coarea, elliptic and normal estimates. -/
def graphBound
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared)
    (closure : green.MaximalClosureData period hPeriod) :
    HasCanonicalScalarHilbertBoundaryGraphBound green.system :=
  canonicalPhysicalScalarFirstSheetBoundaryGraphBound
    period hPeriod green closure.coarea closure.elliptic closure.normal

/-- Maximal physical graph is closable. -/
theorem closable
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared)
    (closure : green.MaximalClosureData period hPeriod) :
    CanonicalScalarGraphClosable green.system :=
  green.maximalGraph_closable_of_minimal_dense
    period hPeriod closure.minimalDense

/-- Actual closed maximal physical scalar domain. -/
abbrev ClosedDomain
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared)
    (closure : green.MaximalClosureData period hPeriod) :=
  canonicalScalarClosedOperatorDomain green.system

/-- Actual closed maximal physical scalar operator. -/
noncomputable def closedOperator
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared)
    (closure : green.MaximalClosureData period hPeriod) :
    closure.ClosedDomain green →ₗ[Real]
      CanonicalPhysicalBulkL2 period hPeriod :=
  canonicalScalarClosedOperator green.system (closure.closable green)

/-- Completed physical Cauchy trace on the actual maximal domain. -/
noncomputable def closedBoundaryTrace
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared)
    (closure : green.MaximalClosureData period hPeriod) :
    closure.ClosedDomain green →ₗ[Real]
      CanonicalScalarHilbertBoundaryDatum
        (Trace := CanonicalPhysicalScalarFirstSheetL2 period) :=
  canonicalScalarClosedBoundaryTrace green.system
    (closure.closable green) (closure.graphBound green)

/-- Exact Green identity on the actual closed maximal physical domain. -/
theorem closedGreenIdentity
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared)
    (closure : green.MaximalClosureData period hPeriod)
    (first second : closure.ClosedDomain green) :
    inner Real (closure.closedOperator green first) second.1 -
        inner Real first.1 (closure.closedOperator green second) =
      2 * canonicalScalarHilbertBoundarySymplecticForm
        (closure.closedBoundaryTrace green first)
        (closure.closedBoundaryTrace green second) :=
  canonicalScalarClosedGreenIdentity green.system
    (closure.closable green) (closure.graphBound green) first second

/-- Closed maximal physical trace remains surjective. -/
theorem closedBoundaryTrace_surjective
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared)
    (closure : green.MaximalClosureData period hPeriod) :
    Function.Surjective (closure.closedBoundaryTrace green) :=
  canonicalScalarClosedBoundaryTrace_surjective green.system
    (closure.closable green) (closure.graphBound green)

/-- Maximal physical closure certificate. -/
theorem certificate
    (green : CanonicalPhysicalScalarFirstSheetGreenData
      period hPeriod massSquared)
    (closure : green.MaximalClosureData period hPeriod) :
    CanonicalScalarGraphClosable green.system ∧
      Function.Surjective (closure.closedBoundaryTrace green) ∧
      (∀ first second : closure.ClosedDomain green,
        inner Real (closure.closedOperator green first) second.1 -
            inner Real first.1 (closure.closedOperator green second) =
          2 * canonicalScalarHilbertBoundarySymplecticForm
            (closure.closedBoundaryTrace green first)
            (closure.closedBoundaryTrace green second)) :=
  ⟨closure.closable green,
    closure.closedBoundaryTrace_surjective green,
    closure.closedGreenIdentity green⟩

end MaximalClosureData

end CanonicalPhysicalScalarFirstSheetGreenData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarMinimalCore4D
end JanusFormal
