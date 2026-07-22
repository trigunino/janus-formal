import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarLagrangianVariationalEigenprinciple4D
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Direct sums of scalar Hilbert boundary conditions

The cut bulk naturally has several boundary sheets.  This file proves that
closed Lagrangian scalar boundary conditions assemble componentwise.

For Hilbert trace spaces `TraceLeft` and `TraceRight`, the Green form on the
product trace space splits as the sum of the two component Green forms.  The
componentwise direct sum of two closed Lagrangian boundary conditions is again
closed and Lagrangian.

Dirichlet, Neumann and bounded symmetric Robin graphs are compatible with this
assembly; Robin operators combine block-diagonally.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarHilbertBoundaryDirectSum4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarHilbertRobinGraph4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D

universe u v

variable {TraceLeft : Type u} {TraceRight : Type v}
  [NormedAddCommGroup TraceLeft] [InnerProductSpace Real TraceLeft]
  [CompleteSpace TraceLeft]
  [NormedAddCommGroup TraceRight] [InnerProductSpace Real TraceRight]
  [CompleteSpace TraceRight]

private abbrev CombinedTrace := WithLp 2 (TraceLeft × TraceRight)

/-- Left component of a paired boundary datum on a product trace space. -/
def canonicalScalarHilbertBoundaryDatumLeft :
    CanonicalScalarHilbertBoundaryDatum
        (Trace := CombinedTrace (TraceLeft := TraceLeft) (TraceRight := TraceRight)) →L[Real]
      CanonicalScalarHilbertBoundaryDatum (Trace := TraceLeft) where
  toFun datum := (datum.1.fst, datum.2.fst)
  map_add' first second := by ext <;> rfl
  map_smul' scalar datum := by ext <;> rfl
  cont := by fun_prop

/-- Right component of a paired boundary datum on a product trace space. -/
def canonicalScalarHilbertBoundaryDatumRight :
    CanonicalScalarHilbertBoundaryDatum
        (Trace := CombinedTrace (TraceLeft := TraceLeft) (TraceRight := TraceRight)) →L[Real]
      CanonicalScalarHilbertBoundaryDatum (Trace := TraceRight) where
  toFun datum := (datum.1.snd, datum.2.snd)
  map_add' first second := by ext <;> rfl
  map_smul' scalar datum := by ext <;> rfl
  cont := by fun_prop

@[simp] theorem canonicalScalarHilbertBoundaryDatumLeft_apply
    (datum : CanonicalScalarHilbertBoundaryDatum
      (Trace := CombinedTrace (TraceLeft := TraceLeft) (TraceRight := TraceRight))) :
    canonicalScalarHilbertBoundaryDatumLeft datum =
      (datum.1.fst, datum.2.fst) :=
  rfl

@[simp] theorem canonicalScalarHilbertBoundaryDatumRight_apply
    (datum : CanonicalScalarHilbertBoundaryDatum
      (Trace := CombinedTrace (TraceLeft := TraceLeft) (TraceRight := TraceRight))) :
    canonicalScalarHilbertBoundaryDatumRight datum =
      (datum.1.snd, datum.2.snd) :=
  rfl

/-- The product Green form is the sum of the two component Green forms. -/
theorem canonicalScalarHilbertBoundarySymplecticForm_directSum
    (first second : CanonicalScalarHilbertBoundaryDatum
      (Trace := CombinedTrace (TraceLeft := TraceLeft) (TraceRight := TraceRight))) :
    canonicalScalarHilbertBoundarySymplecticForm first second =
      canonicalScalarHilbertBoundarySymplecticForm
          (canonicalScalarHilbertBoundaryDatumLeft first)
          (canonicalScalarHilbertBoundaryDatumLeft second) +
        canonicalScalarHilbertBoundarySymplecticForm
          (canonicalScalarHilbertBoundaryDatumRight first)
          (canonicalScalarHilbertBoundaryDatumRight second) := by
  unfold canonicalScalarHilbertBoundarySymplecticForm
  simp
  ring

/-- Componentwise direct sum of two Hilbert Lagrangian scalar boundary
conditions. -/
noncomputable def CanonicalScalarHilbertLagrangianBoundaryCondition.directSum
    (left : CanonicalScalarHilbertLagrangianBoundaryCondition TraceLeft)
    (right : CanonicalScalarHilbertLagrangianBoundaryCondition TraceRight) :
    CanonicalScalarHilbertLagrangianBoundaryCondition
      (CombinedTrace (TraceLeft := TraceLeft) (TraceRight := TraceRight)) where
  subspace :=
    { carrier := {datum |
        canonicalScalarHilbertBoundaryDatumLeft datum ∈ left.subspace ∧
          canonicalScalarHilbertBoundaryDatumRight datum ∈ right.subspace}
      zero_mem' := ⟨left.subspace.zero_mem, right.subspace.zero_mem⟩
      add_mem' := by
        intro first second hFirst hSecond
        exact ⟨left.subspace.add_mem hFirst.1 hSecond.1,
          right.subspace.add_mem hFirst.2 hSecond.2⟩
      smul_mem' := by
        intro scalar datum hDatum
        exact ⟨left.subspace.smul_mem scalar hDatum.1,
          right.subspace.smul_mem scalar hDatum.2⟩ }
  isClosed := by
    change IsClosed
      ((canonicalScalarHilbertBoundaryDatumLeft :
          CanonicalScalarHilbertBoundaryDatum
              (Trace := CombinedTrace (TraceLeft := TraceLeft)
                (TraceRight := TraceRight)) →L[Real]
            CanonicalScalarHilbertBoundaryDatum (Trace := TraceLeft)) ⁻¹'
          (left.subspace : Set (CanonicalScalarHilbertBoundaryDatum
            (Trace := TraceLeft))) ∩
        (canonicalScalarHilbertBoundaryDatumRight :
          CanonicalScalarHilbertBoundaryDatum
              (Trace := CombinedTrace (TraceLeft := TraceLeft)
                (TraceRight := TraceRight)) →L[Real]
            CanonicalScalarHilbertBoundaryDatum (Trace := TraceRight)) ⁻¹'
          (right.subspace : Set (CanonicalScalarHilbertBoundaryDatum
            (Trace := TraceRight))))
    exact (left.isClosed.preimage
      (canonicalScalarHilbertBoundaryDatumLeft
        (TraceLeft := TraceLeft) (TraceRight := TraceRight)).continuous).inter
      (right.isClosed.preimage
        (canonicalScalarHilbertBoundaryDatumRight
          (TraceLeft := TraceLeft) (TraceRight := TraceRight)).continuous)
  lagrangian := by
    apply le_antisymm
    · intro datum hDatum
      constructor
      · rw [← left.lagrangian]
        intro test hTest
        let combinedTest : CanonicalScalarHilbertBoundaryDatum
            (Trace := CombinedTrace (TraceLeft := TraceLeft)
              (TraceRight := TraceRight)) :=
          (WithLp.toLp 2 (test.1, 0), WithLp.toLp 2 (test.2, 0))
        have hOrth := hDatum combinedTest (by
          exact ⟨hTest, right.subspace.zero_mem⟩)
        rw [canonicalScalarHilbertBoundarySymplecticForm_directSum] at hOrth
        dsimp [combinedTest] at hOrth
        simpa using hOrth
      · rw [← right.lagrangian]
        intro test hTest
        let combinedTest : CanonicalScalarHilbertBoundaryDatum
            (Trace := CombinedTrace (TraceLeft := TraceLeft)
              (TraceRight := TraceRight)) :=
          (WithLp.toLp 2 (0, test.1), WithLp.toLp 2 (0, test.2))
        have hOrth := hDatum combinedTest (by
          exact ⟨left.subspace.zero_mem, hTest⟩)
        rw [canonicalScalarHilbertBoundarySymplecticForm_directSum] at hOrth
        dsimp [combinedTest] at hOrth
        simpa using hOrth
    · intro datum hDatum test hTest
      rw [canonicalScalarHilbertBoundarySymplecticForm_directSum]
      rw [left.pairing_eq_zero
          (canonicalScalarHilbertBoundaryDatumLeft datum)
          (canonicalScalarHilbertBoundaryDatumLeft test) hDatum.1 hTest.1,
        right.pairing_eq_zero
          (canonicalScalarHilbertBoundaryDatumRight datum)
          (canonicalScalarHilbertBoundaryDatumRight test) hDatum.2 hTest.2,
        add_zero]

/-- Block-diagonal Robin operator on a product trace space. -/
def canonicalScalarHilbertRobinOperatorDirectSum
    (left : TraceLeft →L[Real] TraceLeft)
    (right : TraceRight →L[Real] TraceRight) :
    CombinedTrace (TraceLeft := TraceLeft) (TraceRight := TraceRight) →L[Real]
      CombinedTrace (TraceLeft := TraceLeft) (TraceRight := TraceRight) where
  toFun value := WithLp.toLp 2 (left value.fst, right value.snd)
  map_add' first second := by
    apply (WithLp.equiv 2 (TraceLeft × TraceRight)).injective
    ext <;> simp
  map_smul' scalar value := by
    apply (WithLp.equiv 2 (TraceLeft × TraceRight)).injective
    ext <;> simp
  cont := by fun_prop

@[simp] theorem canonicalScalarHilbertRobinOperatorDirectSum_apply
    (left : TraceLeft →L[Real] TraceLeft)
    (right : TraceRight →L[Real] TraceRight)
    (value : CombinedTrace (TraceLeft := TraceLeft) (TraceRight := TraceRight)) :
    canonicalScalarHilbertRobinOperatorDirectSum left right value =
      WithLp.toLp 2 (left value.fst, right value.snd) :=
  rfl

/-- Block-diagonal sum of symmetric Robin operators is symmetric. -/
theorem canonicalScalarHilbertRobinOperatorDirectSum_isSymmetric
    (left : TraceLeft →L[Real] TraceLeft)
    (right : TraceRight →L[Real] TraceRight)
    (hLeft : left.toLinearMap.IsSymmetric)
    (hRight : right.toLinearMap.IsSymmetric) :
    (canonicalScalarHilbertRobinOperatorDirectSum left right).toLinearMap.IsSymmetric := by
  intro first second
  change inner Real
      (WithLp.toLp 2 (left first.fst, right first.snd)) second =
    inner Real first
      (WithLp.toLp 2 (left second.fst, right second.snd))
  rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply]
  exact congrArg₂ (· + ·) (hLeft first.fst second.fst)
    (hRight first.snd second.snd)

/-- Direct sum of two Robin-graph conditions is the Robin graph of the
block-diagonal sum. -/
theorem canonicalScalarHilbertLagrangianBoundaryCondition_directSum_robinGraph
    (left : TraceLeft →L[Real] TraceLeft)
    (right : TraceRight →L[Real] TraceRight)
    (hLeft : left.toLinearMap.IsSymmetric)
    (hRight : right.toLinearMap.IsSymmetric) :
    (CanonicalScalarHilbertLagrangianBoundaryCondition.directSum
      (CanonicalScalarHilbertLagrangianBoundaryCondition.robinGraph left hLeft)
      (CanonicalScalarHilbertLagrangianBoundaryCondition.robinGraph right hRight)).subspace =
      (CanonicalScalarHilbertLagrangianBoundaryCondition.robinGraph
        (canonicalScalarHilbertRobinOperatorDirectSum left right)
        (canonicalScalarHilbertRobinOperatorDirectSum_isSymmetric
          left right hLeft hRight)).subspace := by
  ext datum
  change
    (canonicalScalarHilbertBoundaryDatumLeft datum ∈
          canonicalScalarHilbertRobinGraphSubmodule left ∧
        canonicalScalarHilbertBoundaryDatumRight datum ∈
          canonicalScalarHilbertRobinGraphSubmodule right) ↔
      datum ∈ canonicalScalarHilbertRobinGraphSubmodule
        (canonicalScalarHilbertRobinOperatorDirectSum left right)
  rw [mem_canonicalScalarHilbertRobinGraphSubmodule,
    mem_canonicalScalarHilbertRobinGraphSubmodule,
    mem_canonicalScalarHilbertRobinGraphSubmodule]
  change
    (datum.2.fst = left datum.1.fst ∧
        datum.2.snd = right datum.1.snd) ↔
      datum.2 = WithLp.toLp 2 (left datum.1.fst, right datum.1.snd)
  constructor
  · intro h
    apply (WithLp.equiv 2 (TraceLeft × TraceRight)).injective
    exact Prod.ext h.1 h.2
  · intro h
    exact ⟨congrArg WithLp.fst h, congrArg WithLp.snd h⟩

/-- Direct-sum closure certificate. -/
theorem canonicalScalarHilbertBoundaryDirectSum_certificate
    (left : CanonicalScalarHilbertLagrangianBoundaryCondition TraceLeft)
    (right : CanonicalScalarHilbertLagrangianBoundaryCondition TraceRight) :
    IsClosed
        ((CanonicalScalarHilbertLagrangianBoundaryCondition.directSum
            left right).subspace :
          Set (CanonicalScalarHilbertBoundaryDatum
            (Trace := CombinedTrace (TraceLeft := TraceLeft)
              (TraceRight := TraceRight)))) ∧
      canonicalScalarHilbertBoundarySymplecticOrthogonal
          (CanonicalScalarHilbertLagrangianBoundaryCondition.directSum
            left right).subspace =
        (CanonicalScalarHilbertLagrangianBoundaryCondition.directSum
          left right).subspace :=
  ⟨(CanonicalScalarHilbertLagrangianBoundaryCondition.directSum
      left right).isClosed,
    (CanonicalScalarHilbertLagrangianBoundaryCondition.directSum
      left right).lagrangian⟩

end
end P0EFTJanusMappingTorusScalarHilbertBoundaryDirectSum4D
end JanusFormal
