import Mathlib.Analysis.InnerProductSpace.Basic
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarBoundaryTripleMaximality4D

/-!
# Hilbert scalar boundary symplectic space

This file upgrades the pointwise real boundary plane to an arbitrary real
Hilbert trace space.  A boundary datum is a pair `(value, normalDerivative)`
and carries the Green form

`omega((u,n),(v,m)) = <u,m> - <n,v>`.

For every nonzero real coefficient pair `(a,b)`, the separated subspace

`a • u + b • n = 0`

is proved closed and exactly equal to its symplectic orthogonal.  Thus
Dirichlet, Neumann and constant real Robin graphs are genuine closed
Lagrangian subspaces at the completed trace-space level.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D

set_option autoImplicit false
noncomputable section

open Set
open P0EFTJanusMappingTorusScalarBoundarySymplecticPlane4D

universe u

variable {Trace : Type u}
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]

/-- Hilbert boundary value and Hilbert normal trace. -/
abbrev CanonicalScalarHilbertBoundaryDatum := Trace × Trace

/-- Continuous separated boundary constraint `a u + b n`. -/
def canonicalScalarHilbertBoundaryConstraint (a b : Real) :
    CanonicalScalarHilbertBoundaryDatum (Trace := Trace) →L[Real] Trace :=
  a • ContinuousLinearMap.fst Real Trace Trace +
    b • ContinuousLinearMap.snd Real Trace Trace

@[simp] theorem canonicalScalarHilbertBoundaryConstraint_apply
    (a b : Real) (datum : CanonicalScalarHilbertBoundaryDatum (Trace := Trace)) :
    canonicalScalarHilbertBoundaryConstraint (Trace := Trace) a b datum =
      a • datum.1 + b • datum.2 := by
  rfl

/-- Hilbert-space Green form on completed scalar boundary data. -/
def canonicalScalarHilbertBoundarySymplecticForm
    (first second : CanonicalScalarHilbertBoundaryDatum (Trace := Trace)) : Real :=
  inner Real first.1 second.2 - inner Real first.2 second.1

@[simp] theorem canonicalScalarHilbertBoundarySymplecticForm_zero_left
    (datum : CanonicalScalarHilbertBoundaryDatum (Trace := Trace)) :
    canonicalScalarHilbertBoundarySymplecticForm (0, 0) datum = 0 := by
  simp [canonicalScalarHilbertBoundarySymplecticForm]

@[simp] theorem canonicalScalarHilbertBoundarySymplecticForm_zero_right
    (datum : CanonicalScalarHilbertBoundaryDatum (Trace := Trace)) :
    canonicalScalarHilbertBoundarySymplecticForm datum (0, 0) = 0 := by
  simp [canonicalScalarHilbertBoundarySymplecticForm]

@[simp] theorem canonicalScalarHilbertBoundarySymplecticForm_add_left
    (first second third : CanonicalScalarHilbertBoundaryDatum (Trace := Trace)) :
    canonicalScalarHilbertBoundarySymplecticForm (first + second) third =
      canonicalScalarHilbertBoundarySymplecticForm first third +
        canonicalScalarHilbertBoundarySymplecticForm second third := by
  simp [canonicalScalarHilbertBoundarySymplecticForm, inner_add_left]
  ring

@[simp] theorem canonicalScalarHilbertBoundarySymplecticForm_add_right
    (first second third : CanonicalScalarHilbertBoundaryDatum (Trace := Trace)) :
    canonicalScalarHilbertBoundarySymplecticForm first (second + third) =
      canonicalScalarHilbertBoundarySymplecticForm first second +
        canonicalScalarHilbertBoundarySymplecticForm first third := by
  simp [canonicalScalarHilbertBoundarySymplecticForm, inner_add_right]
  ring

@[simp] theorem canonicalScalarHilbertBoundarySymplecticForm_smul_left
    (scalar : Real)
    (first second : CanonicalScalarHilbertBoundaryDatum (Trace := Trace)) :
    canonicalScalarHilbertBoundarySymplecticForm (scalar • first) second =
      scalar * canonicalScalarHilbertBoundarySymplecticForm first second := by
  simp [canonicalScalarHilbertBoundarySymplecticForm, real_inner_smul_left]
  ring

@[simp] theorem canonicalScalarHilbertBoundarySymplecticForm_smul_right
    (scalar : Real)
    (first second : CanonicalScalarHilbertBoundaryDatum (Trace := Trace)) :
    canonicalScalarHilbertBoundarySymplecticForm first (scalar • second) =
      scalar * canonicalScalarHilbertBoundarySymplecticForm first second := by
  simp [canonicalScalarHilbertBoundarySymplecticForm, real_inner_smul_right]
  ring

/-- Antisymmetry of the completed Green form. -/
theorem canonicalScalarHilbertBoundarySymplecticForm_antisymm
    (first second : CanonicalScalarHilbertBoundaryDatum (Trace := Trace)) :
    canonicalScalarHilbertBoundarySymplecticForm first second =
      -canonicalScalarHilbertBoundarySymplecticForm second first := by
  unfold canonicalScalarHilbertBoundarySymplecticForm
  rw [real_inner_comm first.1 second.2, real_inner_comm first.2 second.1]
  ring

@[simp] theorem canonicalScalarHilbertBoundarySymplecticForm_self
    (datum : CanonicalScalarHilbertBoundaryDatum (Trace := Trace)) :
    canonicalScalarHilbertBoundarySymplecticForm datum datum = 0 := by
  unfold canonicalScalarHilbertBoundarySymplecticForm
  rw [real_inner_comm datum.1 datum.2]
  ring

/-- Symplectic orthogonal of a Hilbert boundary submodule. -/
def canonicalScalarHilbertBoundarySymplecticOrthogonal
    (subspace : Submodule Real
      (CanonicalScalarHilbertBoundaryDatum (Trace := Trace))) :
    Submodule Real (CanonicalScalarHilbertBoundaryDatum (Trace := Trace)) where
  carrier := {datum | ∀ test, test ∈ subspace →
    canonicalScalarHilbertBoundarySymplecticForm datum test = 0}
  zero_mem' := by
    intro test hTest
    simp
  add_mem' := by
    intro first second hFirst hSecond test hTest
    rw [canonicalScalarHilbertBoundarySymplecticForm_add_left,
      hFirst test hTest, hSecond test hTest, add_zero]
  smul_mem' := by
    intro scalar datum hDatum test hTest
    rw [canonicalScalarHilbertBoundarySymplecticForm_smul_left,
      hDatum test hTest, mul_zero]

@[simp] theorem mem_canonicalScalarHilbertBoundarySymplecticOrthogonal
    (subspace : Submodule Real
      (CanonicalScalarHilbertBoundaryDatum (Trace := Trace)))
    (datum : CanonicalScalarHilbertBoundaryDatum (Trace := Trace)) :
    datum ∈ canonicalScalarHilbertBoundarySymplecticOrthogonal subspace ↔
      ∀ test, test ∈ subspace →
        canonicalScalarHilbertBoundarySymplecticForm datum test = 0 :=
  Iff.rfl

/-- Completed separated boundary subspace. -/
def canonicalScalarHilbertSeparatedBoundarySubmodule (a b : Real) :
    Submodule Real (CanonicalScalarHilbertBoundaryDatum (Trace := Trace)) :=
  LinearMap.ker
    (canonicalScalarHilbertBoundaryConstraint (Trace := Trace) a b).toLinearMap

@[simp] theorem mem_canonicalScalarHilbertSeparatedBoundarySubmodule
    (a b : Real)
    (datum : CanonicalScalarHilbertBoundaryDatum (Trace := Trace)) :
    datum ∈ canonicalScalarHilbertSeparatedBoundarySubmodule
        (Trace := Trace) a b ↔
      a • datum.1 + b • datum.2 = 0 := by
  rfl

/-- The separated Hilbert boundary space is closed. -/
theorem canonicalScalarHilbertSeparatedBoundarySubmodule_isClosed
    (a b : Real) :
    IsClosed
      (canonicalScalarHilbertSeparatedBoundarySubmodule
        (Trace := Trace) a b :
          Set (CanonicalScalarHilbertBoundaryDatum (Trace := Trace))) := by
  change IsClosed {datum |
    canonicalScalarHilbertBoundaryConstraint (Trace := Trace) a b datum = 0}
  exact isClosed_singleton.preimage
    (canonicalScalarHilbertBoundaryConstraint (Trace := Trace) a b).continuous

private theorem coefficient_square_sum_pos
    (a b : Real) (hNondegenerate : a ≠ 0 ∨ b ≠ 0) :
    0 < a ^ 2 + b ^ 2 := by
  rcases hNondegenerate with hA | hB
  · nlinarith [sq_pos_of_ne_zero hA, sq_nonneg b]
  · nlinarith [sq_nonneg a, sq_pos_of_ne_zero hB]

/-- Every separated subspace is isotropic for the Hilbert Green form. -/
theorem canonicalScalarHilbertSeparatedBoundarySubmodule_le_orthogonal
    (a b : Real) (hNondegenerate : a ≠ 0 ∨ b ≠ 0) :
    canonicalScalarHilbertSeparatedBoundarySubmodule (Trace := Trace) a b ≤
      canonicalScalarHilbertBoundarySymplecticOrthogonal
        (canonicalScalarHilbertSeparatedBoundarySubmodule
          (Trace := Trace) a b) := by
  intro first hFirst second hSecond
  have hFirstConstraint : a • first.1 + b • first.2 = 0 := hFirst
  have hSecondConstraint : a • second.1 + b • second.2 = 0 := hSecond
  have hFirstNormal := congrArg
    (fun value : Trace => inner Real value second.2) hFirstConstraint
  have hFirstValue := congrArg
    (fun value : Trace => inner Real value second.1) hFirstConstraint
  have hSecondValue := congrArg
    (fun value : Trace => inner Real first.1 value) hSecondConstraint
  have hSecondNormal := congrArg
    (fun value : Trace => inner Real first.2 value) hSecondConstraint
  simp [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right] at hFirstNormal hFirstValue hSecondValue hSecondNormal
  have hScaled :
      (a ^ 2 + b ^ 2) *
          canonicalScalarHilbertBoundarySymplecticForm first second = 0 := by
    unfold canonicalScalarHilbertBoundarySymplecticForm
    nlinarith
  exact (mul_eq_zero.mp hScaled).resolve_left
    (ne_of_gt (coefficient_square_sum_pos a b hNondegenerate))

/-- A datum symplectically orthogonal to a separated subspace satisfies the
same separated condition. -/
theorem canonicalScalarHilbertBoundarySymplecticOrthogonal_le_separated
    (a b : Real) (hNondegenerate : a ≠ 0 ∨ b ≠ 0) :
    canonicalScalarHilbertBoundarySymplecticOrthogonal
        (canonicalScalarHilbertSeparatedBoundarySubmodule
          (Trace := Trace) a b) ≤
      canonicalScalarHilbertSeparatedBoundarySubmodule
        (Trace := Trace) a b := by
  intro datum hDatum
  let residual : Trace := a • datum.1 + b • datum.2
  let probe : CanonicalScalarHilbertBoundaryDatum (Trace := Trace) :=
    (b • residual, -a • residual)
  have hProbe : probe ∈
      canonicalScalarHilbertSeparatedBoundarySubmodule
        (Trace := Trace) a b := by
    change a • (b • residual) + b • (-a • residual) = 0
    module
  have hOrth := hDatum probe hProbe
  have hOrthExpanded :
      -(a * inner Real datum.1 residual +
          b * inner Real datum.2 residual) = 0 := by
    simpa [probe, canonicalScalarHilbertBoundarySymplecticForm,
      real_inner_smul_right] using hOrth
  have hResidualExpanded :
      inner Real residual residual =
        a * inner Real datum.1 residual +
          b * inner Real datum.2 residual := by
    simp [residual, inner_add_left, real_inner_smul_left]
  have hResidualInner : inner Real residual residual = 0 := by
    linarith
  have hResidualNormSq : ‖residual‖ ^ 2 = 0 := by
    simpa [real_inner_self_eq_norm_sq] using hResidualInner
  have hResidualNorm : ‖residual‖ = 0 := by
    nlinarith [sq_nonneg ‖residual‖]
  have hResidual : residual = 0 := norm_eq_zero.mp hResidualNorm
  change a • datum.1 + b • datum.2 = 0
  exact hResidual

/-- Every nondegenerate separated Hilbert boundary subspace is Lagrangian. -/
theorem canonicalScalarHilbertSeparatedBoundarySubmodule_orthogonal_eq
    (a b : Real) (hNondegenerate : a ≠ 0 ∨ b ≠ 0) :
    canonicalScalarHilbertBoundarySymplecticOrthogonal
        (canonicalScalarHilbertSeparatedBoundarySubmodule
          (Trace := Trace) a b) =
      canonicalScalarHilbertSeparatedBoundarySubmodule
        (Trace := Trace) a b := by
  apply le_antisymm
  · exact canonicalScalarHilbertBoundarySymplecticOrthogonal_le_separated
      (Trace := Trace) a b hNondegenerate
  · exact canonicalScalarHilbertSeparatedBoundarySubmodule_le_orthogonal
      (Trace := Trace) a b hNondegenerate

/-- Direct zero-pairing form of separated isotropy. -/
theorem canonicalScalarHilbertBoundarySymplecticForm_eq_zero_of_mem_separated
    (a b : Real) (hNondegenerate : a ≠ 0 ∨ b ≠ 0)
    (first second : CanonicalScalarHilbertBoundaryDatum (Trace := Trace))
    (hFirst : first ∈ canonicalScalarHilbertSeparatedBoundarySubmodule
      (Trace := Trace) a b)
    (hSecond : second ∈ canonicalScalarHilbertSeparatedBoundarySubmodule
      (Trace := Trace) a b) :
    canonicalScalarHilbertBoundarySymplecticForm first second = 0 :=
  canonicalScalarHilbertSeparatedBoundarySubmodule_le_orthogonal
    (Trace := Trace) a b hNondegenerate hFirst second hSecond

/-- Completed Dirichlet trace subspace. -/
def canonicalScalarHilbertDirichletBoundarySubmodule :
    Submodule Real (CanonicalScalarHilbertBoundaryDatum (Trace := Trace)) :=
  canonicalScalarHilbertSeparatedBoundarySubmodule (Trace := Trace) 1 0

/-- Completed Neumann trace subspace. -/
def canonicalScalarHilbertNeumannBoundarySubmodule :
    Submodule Real (CanonicalScalarHilbertBoundaryDatum (Trace := Trace)) :=
  canonicalScalarHilbertSeparatedBoundarySubmodule (Trace := Trace) 0 1

/-- Completed constant real Robin trace subspace `n = kappa u`. -/
def canonicalScalarHilbertRobinBoundarySubmodule (coefficient : Real) :
    Submodule Real (CanonicalScalarHilbertBoundaryDatum (Trace := Trace)) :=
  canonicalScalarHilbertSeparatedBoundarySubmodule
    (Trace := Trace) (-coefficient) 1

@[simp] theorem mem_canonicalScalarHilbertDirichletBoundarySubmodule
    (datum : CanonicalScalarHilbertBoundaryDatum (Trace := Trace)) :
    datum ∈ canonicalScalarHilbertDirichletBoundarySubmodule (Trace := Trace) ↔
      datum.1 = 0 := by
  simp [canonicalScalarHilbertDirichletBoundarySubmodule]

@[simp] theorem mem_canonicalScalarHilbertNeumannBoundarySubmodule
    (datum : CanonicalScalarHilbertBoundaryDatum (Trace := Trace)) :
    datum ∈ canonicalScalarHilbertNeumannBoundarySubmodule (Trace := Trace) ↔
      datum.2 = 0 := by
  simp [canonicalScalarHilbertNeumannBoundarySubmodule]

@[simp] theorem mem_canonicalScalarHilbertRobinBoundarySubmodule
    (coefficient : Real)
    (datum : CanonicalScalarHilbertBoundaryDatum (Trace := Trace)) :
    datum ∈ canonicalScalarHilbertRobinBoundarySubmodule
        (Trace := Trace) coefficient ↔
      datum.2 = coefficient • datum.1 := by
  change -coefficient • datum.1 + datum.2 = 0 ↔ _
  constructor <;> intro h
  · exact eq_of_sub_eq_zero (by simpa [sub_eq_add_neg, add_comm] using h)
  · rw [h]
    module

/-- Dirichlet is closed Lagrangian. -/
theorem canonicalScalarHilbertDirichletBoundarySubmodule_lagrangian :
    canonicalScalarHilbertBoundarySymplecticOrthogonal
        (canonicalScalarHilbertDirichletBoundarySubmodule (Trace := Trace)) =
      canonicalScalarHilbertDirichletBoundarySubmodule (Trace := Trace) := by
  exact canonicalScalarHilbertSeparatedBoundarySubmodule_orthogonal_eq
    (Trace := Trace) 1 0 (Or.inl one_ne_zero)

/-- Neumann is closed Lagrangian. -/
theorem canonicalScalarHilbertNeumannBoundarySubmodule_lagrangian :
    canonicalScalarHilbertBoundarySymplecticOrthogonal
        (canonicalScalarHilbertNeumannBoundarySubmodule (Trace := Trace)) =
      canonicalScalarHilbertNeumannBoundarySubmodule (Trace := Trace) := by
  exact canonicalScalarHilbertSeparatedBoundarySubmodule_orthogonal_eq
    (Trace := Trace) 0 1 (Or.inr one_ne_zero)

/-- Every constant real Robin graph is closed Lagrangian. -/
theorem canonicalScalarHilbertRobinBoundarySubmodule_lagrangian
    (coefficient : Real) :
    canonicalScalarHilbertBoundarySymplecticOrthogonal
        (canonicalScalarHilbertRobinBoundarySubmodule
          (Trace := Trace) coefficient) =
      canonicalScalarHilbertRobinBoundarySubmodule
        (Trace := Trace) coefficient := by
  exact canonicalScalarHilbertSeparatedBoundarySubmodule_orthogonal_eq
    (Trace := Trace) (-coefficient) 1 (Or.inr one_ne_zero)

/-- Closed-Lagrangian certificate for the three standard scalar boundary
families. -/
theorem canonicalScalarHilbertBoundaryLagrangian_certificate
    (coefficient : Real) :
    IsClosed
        (canonicalScalarHilbertDirichletBoundarySubmodule (Trace := Trace) :
          Set (CanonicalScalarHilbertBoundaryDatum (Trace := Trace))) ∧
      IsClosed
        (canonicalScalarHilbertNeumannBoundarySubmodule (Trace := Trace) :
          Set (CanonicalScalarHilbertBoundaryDatum (Trace := Trace))) ∧
      IsClosed
        (canonicalScalarHilbertRobinBoundarySubmodule
          (Trace := Trace) coefficient :
            Set (CanonicalScalarHilbertBoundaryDatum (Trace := Trace))) ∧
      canonicalScalarHilbertBoundarySymplecticOrthogonal
          (canonicalScalarHilbertRobinBoundarySubmodule
            (Trace := Trace) coefficient) =
        canonicalScalarHilbertRobinBoundarySubmodule
          (Trace := Trace) coefficient := by
  exact ⟨canonicalScalarHilbertSeparatedBoundarySubmodule_isClosed
      (Trace := Trace) 1 0,
    canonicalScalarHilbertSeparatedBoundarySubmodule_isClosed
      (Trace := Trace) 0 1,
    canonicalScalarHilbertSeparatedBoundarySubmodule_isClosed
      (Trace := Trace) (-coefficient) 1,
    canonicalScalarHilbertRobinBoundarySubmodule_lagrangian
      (Trace := Trace) coefficient⟩

end
end P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
end JanusFormal
