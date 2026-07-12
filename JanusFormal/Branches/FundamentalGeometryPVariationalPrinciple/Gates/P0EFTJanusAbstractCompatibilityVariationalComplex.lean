import Mathlib

namespace JanusFormal
namespace P0EFTJanusAbstractCompatibilityVariationalComplex

set_option autoImplicit false

universe u v w x

/--
Abstract linearized compatibility complex

`Gauge --R--> Field --K--> Invariant --B--> Identity`

augmented by an adjoint `K*`, a target response `H`, and pairings on fields and
invariants.  This is the coordinate-free algebraic core of the corrected P.F
bridge.
-/
structure CompatibilityVariationalComplex
    (Gauge : Type u)
    (Field : Type v)
    (Invariant : Type w)
    (Identity : Type x)
    [Zero Field]
    [Zero Invariant]
    [Zero Identity] where
  gaugeAction : Gauge → Field
  compatibilityMap : Field → Invariant
  bianchiMap : Invariant → Identity
  adjointCompatibility : Invariant → Field
  targetResponse : Invariant → Invariant
  fieldPairing : Field → Field → ℝ
  invariantPairing : Invariant → Invariant → ℝ
  compatibilityZero : compatibilityMap 0 = 0
  bianchiZero : bianchiMap 0 = 0
  adjointCompatibilityZero : adjointCompatibility 0 = 0
  targetResponseZero : targetResponse 0 = 0
  compatibilityGaugeZero :
    ∀ gauge, compatibilityMap (gaugeAction gauge) = 0
  bianchiCompatibilityZero :
    ∀ field, bianchiMap (compatibilityMap field) = 0
  fieldPairingSymmetric :
    ∀ first second,
      fieldPairing first second = fieldPairing second first
  invariantPairingSymmetric :
    ∀ first second,
      invariantPairing first second = invariantPairing second first
  adjointLaw :
    ∀ invariant field,
      fieldPairing (adjointCompatibility invariant) field =
        invariantPairing invariant (compatibilityMap field)
  targetResponseSelfAdjoint :
    ∀ first second,
      invariantPairing (targetResponse first) second =
        invariantPairing first (targetResponse second)

variable
  {Gauge : Type u}
  {Field : Type v}
  {Invariant : Type w}
  {Identity : Type x}
  [Zero Field]
  [Zero Invariant]
  [Zero Identity]

/-- Pullback Hessian `A = K* H K`. -/
def sourceHessian
    (complex :
      CompatibilityVariationalComplex Gauge Field Invariant Identity)
    (field : Field) : Field :=
  complex.adjointCompatibility
    (complex.targetResponse
      (complex.compatibilityMap field))

/-- The pulled-back Hessian sends zero to zero. -/
@[simp] theorem source_hessian_zero
    (complex :
      CompatibilityVariationalComplex Gauge Field Invariant Identity) :
    sourceHessian complex 0 = 0 := by
  unfold sourceHessian
  rw [complex.compatibilityZero,
    complex.targetResponseZero,
    complex.adjointCompatibilityZero]

/-- Geometric compatibility gives the first complex relation `K R = 0`. -/
theorem compatibility_after_gauge_zero
    (complex :
      CompatibilityVariationalComplex Gauge Field Invariant Identity)
    (gauge : Gauge) :
    complex.compatibilityMap (complex.gaugeAction gauge) = 0 :=
  complex.compatibilityGaugeZero gauge

/-- The geometric Bianchi relation gives `B K = 0`. -/
theorem bianchi_after_compatibility_zero
    (complex :
      CompatibilityVariationalComplex Gauge Field Invariant Identity)
    (field : Field) :
    complex.bianchiMap (complex.compatibilityMap field) = 0 :=
  complex.bianchiCompatibilityZero field

/-- The Hessian annihilates gauge directions: the linearized Noether identity. -/
theorem source_hessian_annihilates_gauge
    (complex :
      CompatibilityVariationalComplex Gauge Field Invariant Identity)
    (gauge : Gauge) :
    sourceHessian complex (complex.gaugeAction gauge) = 0 := by
  unfold sourceHessian
  rw [complex.compatibilityGaugeZero,
    complex.targetResponseZero,
    complex.adjointCompatibilityZero]

/-- The pulled-back Hessian is formally self-adjoint. -/
theorem source_hessian_formally_self_adjoint
    (complex :
      CompatibilityVariationalComplex Gauge Field Invariant Identity)
    (first second : Field) :
    complex.fieldPairing (sourceHessian complex first) second =
      complex.fieldPairing first (sourceHessian complex second) := by
  calc
    complex.fieldPairing (sourceHessian complex first) second =
        complex.invariantPairing
          (complex.targetResponse
            (complex.compatibilityMap first))
          (complex.compatibilityMap second) := by
      exact complex.adjointLaw
        (complex.targetResponse
          (complex.compatibilityMap first)) second
    _ = complex.invariantPairing
          (complex.compatibilityMap first)
          (complex.targetResponse
            (complex.compatibilityMap second)) := by
      exact complex.targetResponseSelfAdjoint
        (complex.compatibilityMap first)
        (complex.compatibilityMap second)
    _ = complex.invariantPairing
          (complex.targetResponse
            (complex.compatibilityMap second))
          (complex.compatibilityMap first) := by
      exact complex.invariantPairingSymmetric _ _
    _ = complex.fieldPairing
          (sourceHessian complex second) first := by
      exact (complex.adjointLaw
        (complex.targetResponse
          (complex.compatibilityMap second)) first).symm
    _ = complex.fieldPairing first
          (sourceHessian complex second) := by
      exact complex.fieldPairingSymmetric _ _

/-- Quadratic action obtained by restricting the target pairing to compatible invariants. -/
noncomputable def compatibilityEnergy
    (complex :
      CompatibilityVariationalComplex Gauge Field Invariant Identity)
    (field : Field) : ℝ :=
  complex.invariantPairing
      (complex.compatibilityMap field)
      (complex.targetResponse
        (complex.compatibilityMap field)) / 2

/-- The action depends only on the compatible invariant value `K(field)`. -/
theorem compatibility_energy_factors_through_invariants
    (complex :
      CompatibilityVariationalComplex Gauge Field Invariant Identity)
    (first second : Field)
    (hInvariant :
      complex.compatibilityMap first =
        complex.compatibilityMap second) :
    compatibilityEnergy complex first =
      compatibilityEnergy complex second := by
  unfold compatibilityEnergy
  rw [hInvariant]

/-- Complete abstract P.F theorem matrix. -/
theorem compatibility_variational_complex_matrix
    (complex :
      CompatibilityVariationalComplex Gauge Field Invariant Identity)
    (gauge : Gauge)
    (first second : Field) :
    complex.compatibilityMap (complex.gaugeAction gauge) = 0 /\
    complex.bianchiMap (complex.compatibilityMap first) = 0 /\
    sourceHessian complex (complex.gaugeAction gauge) = 0 /\
    complex.fieldPairing (sourceHessian complex first) second =
      complex.fieldPairing first (sourceHessian complex second) := by
  exact ⟨compatibility_after_gauge_zero complex gauge,
    bianchi_after_compatibility_zero complex first,
    source_hessian_annihilates_gauge complex gauge,
    source_hessian_formally_self_adjoint complex first second⟩

/--
Interpretation: `K R = 0` supplies Noether degeneracy, `B K = 0` supplies the
geometric compatibility identity, and self-adjointness of `H` supplies
Helmholtz reciprocity.  The three relations are distinct and are combined, not
identified.
-/
structure AbstractPFPhysicalStatus where
  gaugeSpaceConstructed : Prop
  fieldSpaceConstructed : Prop
  compatibleInvariantSpaceConstructed : Prop
  identitySpaceConstructed : Prop
  gaugeActionDerived : Prop
  compatibilityMapDerived : Prop
  bianchiMapDerived : Prop
  adjointCompatibilityDerived : Prop
  targetPairingDerived : Prop
  targetResponseSelfAdjointProved : Prop
  noetherIdentityDerived : Prop
  helmholtzReciprocityDerived : Prop
  globalActionConstructed : Prop


def abstractPFPhysicalClosure
    (s : AbstractPFPhysicalStatus) : Prop :=
  s.gaugeSpaceConstructed /\
  s.fieldSpaceConstructed /\
  s.compatibleInvariantSpaceConstructed /\
  s.identitySpaceConstructed /\
  s.gaugeActionDerived /\
  s.compatibilityMapDerived /\
  s.bianchiMapDerived /\
  s.adjointCompatibilityDerived /\
  s.targetPairingDerived /\
  s.targetResponseSelfAdjointProved /\
  s.noetherIdentityDerived /\
  s.helmholtzReciprocityDerived /\
  s.globalActionConstructed

end P0EFTJanusAbstractCompatibilityVariationalComplex
end JanusFormal
