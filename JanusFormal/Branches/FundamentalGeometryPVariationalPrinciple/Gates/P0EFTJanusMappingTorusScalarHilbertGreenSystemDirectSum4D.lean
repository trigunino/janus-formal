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
open P0EFTJanusMappingTorusScalarHilbertBoundaryDirectSum4D.CanonicalScalarHilbertLagrangianBoundaryCondition

universe u₁ u₂ v₁ v₂ w₁ w₂

variable {DomainLeft : Type u₁} {DomainRight : Type u₂}
  {AmbientLeft : Type v₁} {AmbientRight : Type v₂}
  {TraceLeft : Type w₁} {TraceRight : Type w₂}
  [AddCommGroup DomainLeft] [Module Real DomainLeft]
  [AddCommGroup DomainRight] [Module Real DomainRight]
  [NormedAddCommGroup AmbientLeft] [InnerProductSpace Real AmbientLeft]
  [CompleteSpace AmbientLeft]
  [NormedAddCommGroup AmbientRight] [InnerProductSpace Real AmbientRight]
  [CompleteSpace AmbientRight]
  [NormedAddCommGroup TraceLeft] [InnerProductSpace Real TraceLeft]
  [CompleteSpace TraceLeft]
  [NormedAddCommGroup TraceRight] [InnerProductSpace Real TraceRight]
  [CompleteSpace TraceRight]

private abbrev CombinedAmbient := WithLp 2 (AmbientLeft × AmbientRight)
private abbrev CombinedTrace := WithLp 2 (TraceLeft × TraceRight)

/-- Product inclusion of two scalar Green systems. -/
def canonicalScalarHilbertGreenSystemDirectSumInclusion
    (left : CanonicalScalarHilbertGreenSystem
      (Domain := DomainLeft) (Ambient := AmbientLeft) (Trace := TraceLeft))
    (right : CanonicalScalarHilbertGreenSystem
      (Domain := DomainRight) (Ambient := AmbientRight) (Trace := TraceRight)) :
    DomainLeft × DomainRight →ₗ[Real]
      CombinedAmbient (AmbientLeft := AmbientLeft) (AmbientRight := AmbientRight) where
  toFun field := WithLp.toLp 2
    (left.inclusion field.1, right.inclusion field.2)
  map_add' first second := by
    apply (WithLp.equiv 2 (AmbientLeft × AmbientRight)).injective
    ext <;> simp
  map_smul' scalar field := by
    apply (WithLp.equiv 2 (AmbientLeft × AmbientRight)).injective
    ext <;> simp

/-- Product operator of two scalar Green systems. -/
def canonicalScalarHilbertGreenSystemDirectSumOperator
    (left : CanonicalScalarHilbertGreenSystem
      (Domain := DomainLeft) (Ambient := AmbientLeft) (Trace := TraceLeft))
    (right : CanonicalScalarHilbertGreenSystem
      (Domain := DomainRight) (Ambient := AmbientRight) (Trace := TraceRight)) :
    DomainLeft × DomainRight →ₗ[Real]
      CombinedAmbient (AmbientLeft := AmbientLeft) (AmbientRight := AmbientRight) where
  toFun field := WithLp.toLp 2
    (left.operator field.1, right.operator field.2)
  map_add' first second := by
    apply (WithLp.equiv 2 (AmbientLeft × AmbientRight)).injective
    ext <;> simp
  map_smul' scalar field := by
    apply (WithLp.equiv 2 (AmbientLeft × AmbientRight)).injective
    ext <;> simp

/-- Product paired Cauchy trace. Values and normal traces are grouped by
geometric type rather than by sector. -/
def canonicalScalarHilbertGreenSystemDirectSumBoundaryTrace
    (left : CanonicalScalarHilbertGreenSystem
      (Domain := DomainLeft) (Ambient := AmbientLeft) (Trace := TraceLeft))
    (right : CanonicalScalarHilbertGreenSystem
      (Domain := DomainRight) (Ambient := AmbientRight) (Trace := TraceRight)) :
    DomainLeft × DomainRight →ₗ[Real]
      CanonicalScalarHilbertBoundaryDatum
        (Trace := CombinedTrace (TraceLeft := TraceLeft) (TraceRight := TraceRight)) where
  toFun field :=
    (WithLp.toLp 2
        ((left.boundaryTrace field.1).1, (right.boundaryTrace field.2).1),
      WithLp.toLp 2
        ((left.boundaryTrace field.1).2, (right.boundaryTrace field.2).2))
  map_add' first second := by
    apply Prod.ext
    · apply (WithLp.equiv 2 (TraceLeft × TraceRight)).injective
      ext <;> simp
    · apply (WithLp.equiv 2 (TraceLeft × TraceRight)).injective
      ext <;> simp
  map_smul' scalar field := by
    apply Prod.ext
    · apply (WithLp.equiv 2 (TraceLeft × TraceRight)).injective
      ext <;> simp
    · apply (WithLp.equiv 2 (TraceLeft × TraceRight)).injective
      ext <;> simp

@[simp] theorem canonicalScalarHilbertGreenSystemDirectSumBoundaryTrace_value
    (left : CanonicalScalarHilbertGreenSystem
      (Domain := DomainLeft) (Ambient := AmbientLeft) (Trace := TraceLeft))
    (right : CanonicalScalarHilbertGreenSystem
      (Domain := DomainRight) (Ambient := AmbientRight) (Trace := TraceRight))
    (field : DomainLeft × DomainRight) :
    (canonicalScalarHilbertGreenSystemDirectSumBoundaryTrace left right field).1 =
      WithLp.toLp 2
        ((left.boundaryTrace field.1).1, (right.boundaryTrace field.2).1) :=
  rfl

@[simp] theorem canonicalScalarHilbertGreenSystemDirectSumBoundaryTrace_normal
    (left : CanonicalScalarHilbertGreenSystem
      (Domain := DomainLeft) (Ambient := AmbientLeft) (Trace := TraceLeft))
    (right : CanonicalScalarHilbertGreenSystem
      (Domain := DomainRight) (Ambient := AmbientRight) (Trace := TraceRight))
    (field : DomainLeft × DomainRight) :
    (canonicalScalarHilbertGreenSystemDirectSumBoundaryTrace left right field).2 =
      WithLp.toLp 2
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
      (Ambient := CombinedAmbient (AmbientLeft := AmbientLeft)
        (AmbientRight := AmbientRight))
      (Trace := CombinedTrace (TraceLeft := TraceLeft)
        (TraceRight := TraceRight)) where
  inclusion := canonicalScalarHilbertGreenSystemDirectSumInclusion left right
  operator := canonicalScalarHilbertGreenSystemDirectSumOperator left right
  boundaryTrace := canonicalScalarHilbertGreenSystemDirectSumBoundaryTrace left right
  boundary_surjective := by
    intro boundary
    obtain ⟨leftField, hLeft⟩ := left.boundary_surjective
      (boundary.1.fst, boundary.2.fst)
    obtain ⟨rightField, hRight⟩ := right.boundary_surjective
      (boundary.1.snd, boundary.2.snd)
    have hLeftValue :
        (left.boundaryTrace leftField).1 = boundary.1.fst :=
      congrArg Prod.fst hLeft
    have hLeftNormal :
        (left.boundaryTrace leftField).2 = boundary.2.fst :=
      congrArg Prod.snd hLeft
    have hRightValue :
        (right.boundaryTrace rightField).1 = boundary.1.snd :=
      congrArg Prod.fst hRight
    have hRightNormal :
        (right.boundaryTrace rightField).2 = boundary.2.snd :=
      congrArg Prod.snd hRight
    refine ⟨(leftField, rightField), ?_⟩
    apply Prod.ext
    · apply (WithLp.equiv 2 (TraceLeft × TraceRight)).injective
      change ((left.boundaryTrace leftField).1,
        (right.boundaryTrace rightField).1) =
          (boundary.1.fst, boundary.1.snd)
      apply Prod.ext
      · exact hLeftValue
      · exact hRightValue
    · apply (WithLp.equiv 2 (TraceLeft × TraceRight)).injective
      change ((left.boundaryTrace leftField).2,
        (right.boundaryTrace rightField).2) =
          (boundary.2.fst, boundary.2.snd)
      apply Prod.ext
      · exact hLeftNormal
      · exact hRightNormal
  green_identity := by
    intro first second
    have hLeft := left.green_identity first.1 second.1
    have hRight := right.green_identity first.2 second.2
    rw [canonicalScalarHilbertBoundarySymplecticForm_directSum]
    simp only [canonicalScalarHilbertGreenSystemDirectSumOperator,
      canonicalScalarHilbertGreenSystemDirectSumInclusion,
      canonicalScalarHilbertGreenSystemDirectSumBoundaryTrace_value,
      canonicalScalarHilbertGreenSystemDirectSumBoundaryTrace_normal,
      canonicalScalarHilbertBoundaryDatumLeft_apply,
      canonicalScalarHilbertBoundaryDatumRight_apply,
      WithLp.prod_inner_apply, WithLp.toLp_fst, WithLp.toLp_snd]
    linear_combination hLeft + hRight

/-- Direct-sum boundary conditions fit the direct-sum Green system. -/
noncomputable def canonicalScalarHilbertGreenSystemDirectSumBoundaryCondition
    (leftCondition : CanonicalScalarHilbertLagrangianBoundaryCondition TraceLeft)
    (rightCondition : CanonicalScalarHilbertLagrangianBoundaryCondition TraceRight) :
    CanonicalScalarHilbertLagrangianBoundaryCondition
      (CombinedTrace (TraceLeft := TraceLeft) (TraceRight := TraceRight)) :=
  directSum leftCondition rightCondition

/-- Direct sum of two graph bounds. The estimate itself is kept as an explicit
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
    ‖(CanonicalScalarHilbertGreenSystem.directSum left right).boundaryTrace field‖ ≤
      constant * ‖canonicalScalarSmoothToOperatorGraphLinearMap
        (CanonicalScalarHilbertGreenSystem.directSum left right) field‖

/-- Conversion to the generic graph-bound package. -/
def CanonicalScalarHilbertGreenSystemDirectSumGraphBound.toAbstract
    (left : CanonicalScalarHilbertGreenSystem
      (Domain := DomainLeft) (Ambient := AmbientLeft) (Trace := TraceLeft))
    (right : CanonicalScalarHilbertGreenSystem
      (Domain := DomainRight) (Ambient := AmbientRight) (Trace := TraceRight))
    (bound : CanonicalScalarHilbertGreenSystemDirectSumGraphBound left right) :
    HasCanonicalScalarHilbertBoundaryGraphBound
      (CanonicalScalarHilbertGreenSystem.directSum left right) where
  constant := bound.constant
  nonnegative := bound.nonnegative
  bound := bound.bound

/-- Direct-sum Green-system certificate. -/
theorem canonicalScalarHilbertGreenSystemDirectSum_certificate
    (left : CanonicalScalarHilbertGreenSystem
      (Domain := DomainLeft) (Ambient := AmbientLeft) (Trace := TraceLeft))
    (right : CanonicalScalarHilbertGreenSystem
      (Domain := DomainRight) (Ambient := AmbientRight) (Trace := TraceRight)) :
    Function.Surjective
        (CanonicalScalarHilbertGreenSystem.directSum left right).boundaryTrace ∧
      (∀ first second : DomainLeft × DomainRight,
        inner Real ((CanonicalScalarHilbertGreenSystem.directSum left right).operator first)
              ((CanonicalScalarHilbertGreenSystem.directSum left right).inclusion second) -
            inner Real ((CanonicalScalarHilbertGreenSystem.directSum left right).inclusion first)
              ((CanonicalScalarHilbertGreenSystem.directSum left right).operator second) =
          2 * canonicalScalarHilbertBoundarySymplecticForm
            ((CanonicalScalarHilbertGreenSystem.directSum left right).boundaryTrace first)
            ((CanonicalScalarHilbertGreenSystem.directSum left right).boundaryTrace second)) :=
  ⟨(CanonicalScalarHilbertGreenSystem.directSum left right).boundary_surjective,
    (CanonicalScalarHilbertGreenSystem.directSum left right).green_identity⟩

end
end P0EFTJanusMappingTorusScalarHilbertGreenSystemDirectSum4D
end JanusFormal
