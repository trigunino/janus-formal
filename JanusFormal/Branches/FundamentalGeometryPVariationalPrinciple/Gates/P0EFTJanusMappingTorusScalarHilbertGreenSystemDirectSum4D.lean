import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarHilbertBoundaryDirectSum4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D

/-!
# Direct sums of scalar Hilbert Green systems

Two independent scalar sectors combine into one Hilbert Green system on product
domains, product ambient spaces and product trace spaces.  The combined Green
identity is exactly the sum of the two component identities, matching the direct
sum of the boundary symplectic forms.

This gives the canonical analytic container for the two-sector Janus scalar
problem.  Any componentwise closed Lagrangian boundary conditions combine into
one closed Lagrangian boundary condition through the previously constructed
direct-sum operation.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarHilbertGreenSystemDirectSum4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarHilbertBoundaryDirectSum4D

universe u₁ u₂ v₁ v₂ w₁ w₂

variable {DomainLeft : Type u₁} {DomainRight : Type u₂}
  {AmbientLeft : Type v₁} {AmbientRight : Type v₂}
  {TraceLeft : Type w₁} {TraceRight : Type w₂}
  [AddCommGroup DomainLeft] [Module Real DomainLeft]
  [AddCommGroup DomainRight] [Module Real DomainRight]
  [NormedAddCommGroup AmbientLeft] [InnerProductSpace Real AmbientLeft]
  [NormedAddCommGroup AmbientRight] [InnerProductSpace Real AmbientRight]
  [NormedAddCommGroup TraceLeft] [InnerProductSpace Real TraceLeft]
  [NormedAddCommGroup TraceRight] [InnerProductSpace Real TraceRight]

/-- Product inclusion of two scalar Green systems. -/
def canonicalScalarHilbertGreenSystemDirectSumInclusion
    (left : CanonicalScalarHilbertGreenSystem
      (Domain := DomainLeft) (Ambient := AmbientLeft) (Trace := TraceLeft))
    (right : CanonicalScalarHilbertGreenSystem
      (Domain := DomainRight) (Ambient := AmbientRight) (Trace := TraceRight)) :
    DomainLeft × DomainRight →ₗ[Real] AmbientLeft × AmbientRight where
  toFun field := (left.inclusion field.1, right.inclusion field.2)
  map_add' first second := by ext <;> simp
  map_smul' scalar field := by ext <;> simp

/-- Product operator of two scalar Green systems. -/
def canonicalScalarHilbertGreenSystemDirectSumOperator
    (left : CanonicalScalarHilbertGreenSystem
      (Domain := DomainLeft) (Ambient := AmbientLeft) (Trace := TraceLeft))
    (right : CanonicalScalarHilbertGreenSystem
      (Domain := DomainRight) (Ambient := AmbientRight) (Trace := TraceRight)) :
    DomainLeft × DomainRight →ₗ[Real] AmbientLeft × AmbientRight where
  toFun field := (left.operator field.1, right.operator field.2)
  map_add' first second := by ext <;> simp
  map_smul' scalar field := by ext <;> simp

/-- Product paired Cauchy trace.  Values and normal traces are grouped by
geometric type rather than by sector. -/
def canonicalScalarHilbertGreenSystemDirectSumBoundaryTrace
    (left : CanonicalScalarHilbertGreenSystem
      (Domain := DomainLeft) (Ambient := AmbientLeft) (Trace := TraceLeft))
    (right : CanonicalScalarHilbertGreenSystem
      (Domain := DomainRight) (Ambient := AmbientRight) (Trace := TraceRight)) :
    DomainLeft × DomainRight →ₗ[Real]
      CanonicalScalarHilbertBoundaryDatum (Trace := TraceLeft × TraceRight) where
  toFun field :=
    ((left.boundaryTrace field.1).1, (right.boundaryTrace field.2).1,
     (left.boundaryTrace field.1).2, (right.boundaryTrace field.2).2)
  map_add' first second := by ext <;> simp
  map_smul' scalar field := by ext <;> simp

@[simp] theorem canonicalScalarHilbertGreenSystemDirectSumBoundaryTrace_value
    (left : CanonicalScalarHilbertGreenSystem
      (Domain := DomainLeft) (Ambient := AmbientLeft) (Trace := TraceLeft))
    (right : CanonicalScalarHilbertGreenSystem
      (Domain := DomainRight) (Ambient := AmbientRight) (Trace := TraceRight))
    (field : DomainLeft × DomainRight) :
    (canonicalScalarHilbertGreenSystemDirectSumBoundaryTrace left right field).1 =
      ((left.boundaryTrace field.1).1, (right.boundaryTrace field.2).1) :=
  rfl

@[simp] theorem canonicalScalarHilbertGreenSystemDirectSumBoundaryTrace_normal
    (left : CanonicalScalarHilbertGreenSystem
      (Domain := DomainLeft) (Ambient := AmbientLeft) (Trace := TraceLeft))
    (right : CanonicalScalarHilbertGreenSystem
      (Domain := DomainRight) (Ambient := AmbientRight) (Trace := TraceRight))
    (field : DomainLeft × DomainRight) :
    (canonicalScalarHilbertGreenSystemDirectSumBoundaryTrace left right field).2 =
      ((left.boundaryTrace field.1).2, (right.boundaryTrace field.2).2) :=
  rfl

/-- Direct sum of two Hilbert Green systems. -/
def CanonicalScalarHilbertGreenSystem.directSum
    (left : CanonicalScalarHilbertGreenSystem
      (Domain := DomainLeft) (Ambient := AmbientLeft) (Trace := TraceLeft))
    (right : CanonicalScalarHilbertGreenSystem
      (Domain := DomainRight) (Ambient := AmbientRight) (Trace := TraceRight)) :
    CanonicalScalarHilbertGreenSystem
      (Domain := DomainLeft × DomainRight)
      (Ambient := AmbientLeft × AmbientRight)
      (Trace := TraceLeft × TraceRight) where
  inclusion := canonicalScalarHilbertGreenSystemDirectSumInclusion left right
  operator := canonicalScalarHilbertGreenSystemDirectSumOperator left right
  boundaryTrace := canonicalScalarHilbertGreenSystemDirectSumBoundaryTrace left right
  boundary_surjective := by
    intro boundary
    obtain ⟨leftField, hLeft⟩ := left.boundary_surjective
      (boundary.1.1, boundary.2.1)
    obtain ⟨rightField, hRight⟩ := right.boundary_surjective
      (boundary.1.2, boundary.2.2)
    refine ⟨(leftField, rightField), ?_⟩
    apply Prod.ext <;> apply Prod.ext
    · exact congrArg Prod.fst hLeft
    · exact congrArg Prod.fst hRight
    · exact congrArg Prod.snd hLeft
    · exact congrArg Prod.snd hRight
  green_identity := by
    intro first second
    have hLeft := left.green_identity first.1 second.1
    have hRight := right.green_identity first.2 second.2
    rw [canonicalScalarHilbertBoundarySymplecticForm_directSum]
    change
      (inner Real (left.operator first.1) (left.inclusion second.1) -
          inner Real (left.inclusion first.1) (left.operator second.1)) +
        (inner Real (right.operator first.2) (right.inclusion second.2) -
          inner Real (right.inclusion first.2) (right.operator second.2)) =
      2 * canonicalScalarHilbertBoundarySymplecticForm
          (left.boundaryTrace first.1) (left.boundaryTrace second.1) +
        2 * canonicalScalarHilbertBoundarySymplecticForm
          (right.boundaryTrace first.2) (right.boundaryTrace second.2)
    rw [hLeft, hRight]

/-- Direct-sum boundary conditions fit the direct-sum Green system. -/
noncomputable def canonicalScalarHilbertGreenSystemDirectSumBoundaryCondition
    (leftCondition : CanonicalScalarHilbertLagrangianBoundaryCondition TraceLeft)
    (rightCondition : CanonicalScalarHilbertLagrangianBoundaryCondition TraceRight) :
    CanonicalScalarHilbertLagrangianBoundaryCondition
      (TraceLeft × TraceRight) :=
  leftCondition.directSum rightCondition

/-- Direct sum of two graph bounds.  The estimate itself is kept as an explicit
quantitative input because the product graph norm constants depend on the chosen
norm conventions. -/
structure CanonicalScalarHilbertGreenSystemDirectSumGraphBound
    (left : CanonicalScalarHilbertGreenSystem
      (Domain := DomainLeft) (Ambient := AmbientLeft) (Trace := TraceLeft))
    (right : CanonicalScalarHilbertGreenSystem
      (Domain := DomainRight) (Ambient := AmbientRight) (Trace := TraceRight)) where
  constant : Real
  nonnegative : 0 ≤ constant
  bound : ∀ field : DomainLeft × DomainRight,
    ‖(left.directSum right).boundaryTrace field‖ ≤
      constant * ‖canonicalScalarSmoothToOperatorGraphLinearMap
        (left.directSum right) field‖

/-- Conversion to the generic graph-bound package. -/
def CanonicalScalarHilbertGreenSystemDirectSumGraphBound.toAbstract
    (left : CanonicalScalarHilbertGreenSystem
      (Domain := DomainLeft) (Ambient := AmbientLeft) (Trace := TraceLeft))
    (right : CanonicalScalarHilbertGreenSystem
      (Domain := DomainRight) (Ambient := AmbientRight) (Trace := TraceRight))
    (bound : CanonicalScalarHilbertGreenSystemDirectSumGraphBound left right) :
    HasCanonicalScalarHilbertBoundaryGraphBound (left.directSum right) where
  constant := bound.constant
  nonnegative := bound.nonnegative
  bound := bound.bound

/-- Direct-sum Green-system certificate. -/
theorem canonicalScalarHilbertGreenSystemDirectSum_certificate
    (left : CanonicalScalarHilbertGreenSystem
      (Domain := DomainLeft) (Ambient := AmbientLeft) (Trace := TraceLeft))
    (right : CanonicalScalarHilbertGreenSystem
      (Domain := DomainRight) (Ambient := AmbientRight) (Trace := TraceRight)) :
    Function.Surjective (left.directSum right).boundaryTrace ∧
      (∀ first second : DomainLeft × DomainRight,
        inner Real ((left.directSum right).operator first)
              ((left.directSum right).inclusion second) -
            inner Real ((left.directSum right).inclusion first)
              ((left.directSum right).operator second) =
          2 * canonicalScalarHilbertBoundarySymplecticForm
            ((left.directSum right).boundaryTrace first)
            ((left.directSum right).boundaryTrace second)) :=
  ⟨(left.directSum right).boundary_surjective,
    (left.directSum right).green_identity⟩

end
end P0EFTJanusMappingTorusScalarHilbertGreenSystemDirectSum4D
end JanusFormal
