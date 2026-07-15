import Mathlib
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusAbstractCompatibilityVariationalComplex
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaussCodazziHelmholtzBridge

namespace JanusFormal
namespace P0EFTJanusCompatibilityBridgeHierarchy

set_option autoImplicit false

open P0EFTJanusAbstractCompatibilityVariationalComplex
open P0EFTJanusGaussCodazziHelmholtzBridge

universe u v w x

variable
  {Gauge : Type u}
  {Field : Type v}
  {Invariant : Type w}
  {Identity : Type x}
  [Zero Field]
  [Zero Invariant]
  [Zero Identity]

/--
A strong pullback Hessian `K* H K` defines a constrained Green bridge with zero
transgression and zero boundary defect.  This embeds the strong P.F theorem in
the weaker compatibility-ideal framework.
-/
def strongPullbackAsConstraintBridge
    (complex :
      CompatibilityVariationalComplex Gauge Field Invariant Identity) :
    ConstraintGeneratedHelmholtzBridge Field Invariant where
  compatibility := complex.compatibilityMap
  pairedLinearization := fun first second =>
    complex.fieldPairing first (sourceHessian complex second)
  constraintTransgression := fun _ _ => 0
  boundaryFlux := fun _ _ => 0
  transgressionAtZero := by
    intro variation
    rfl
  defectFactorization := by
    intro first second
    have hAdjoint :=
      source_hessian_formally_self_adjoint complex first second
    have hSymmetry :=
      complex.fieldPairingSymmetric
        (sourceHessian complex first) second
    rw [← hAdjoint, hSymmetry]
    ring

/-- Every strong pullback Hessian is restricted Helmholtz on compatible fields. -/
theorem strong_pullback_implies_restricted_helmholtz
    (complex :
      CompatibilityVariationalComplex Gauge Field Invariant Identity) :
    RestrictedHelmholtz
      (strongPullbackAsConstraintBridge complex) :=
  compatibility_generated_defect_implies_restricted_helmholtz
    (strongPullbackAsConstraintBridge complex)

/-- In the strong pullback route, the boundary flux vanishes identically. -/
theorem strong_pullback_boundary_flux_zero
    (complex :
      CompatibilityVariationalComplex Gauge Field Invariant Identity)
    (first second : Field) :
    BoundaryFluxVanishes
      (strongPullbackAsConstraintBridge complex) first second := by
  rfl

/-- Gauge directions are compatible variations in the strong pullback route. -/
theorem gauge_direction_is_compatible_variation
    (complex :
      CompatibilityVariationalComplex Gauge Field Invariant Identity)
    (gauge : Gauge) :
    IsCompatibleVariation
      (strongPullbackAsConstraintBridge complex)
      (complex.gaugeAction gauge) := by
  exact complex.compatibilityGaugeZero gauge

/-- Strong route summary: global reciprocity, Noether degeneracy and restricted reciprocity all hold. -/
theorem strong_bridge_matrix
    (complex :
      CompatibilityVariationalComplex Gauge Field Invariant Identity)
    (gauge : Gauge)
    (first second : Field) :
    complex.fieldPairing (sourceHessian complex first) second =
        complex.fieldPairing first (sourceHessian complex second) /\
    sourceHessian complex (complex.gaugeAction gauge) = 0 /\
    RestrictedHelmholtz
      (strongPullbackAsConstraintBridge complex) := by
  exact ⟨source_hessian_formally_self_adjoint
      complex first second,
    source_hessian_annihilates_gauge complex gauge,
    strong_pullback_implies_restricted_helmholtz complex⟩

/--
Abstract synthesis of the strong compatibility-complex route.  The two
successive compositions vanish, the pulled-back Hessian is self-adjoint and
restricted Helmholtz, and gauge directions obey the linearized Noether
degeneracy.  This is an algebraic theorem about the supplied complex; it does
not construct the nonlinear Janus complex.
-/
theorem abstract_compatibility_variational_synthesis
    (complex :
      CompatibilityVariationalComplex Gauge Field Invariant Identity)
    (gauge : Gauge)
    (first second : Field) :
    complex.compatibilityMap (complex.gaugeAction gauge) = 0 /\
    complex.bianchiMap (complex.compatibilityMap first) = 0 /\
    complex.fieldPairing (sourceHessian complex first) second =
      complex.fieldPairing first (sourceHessian complex second) /\
    sourceHessian complex (complex.gaugeAction gauge) = 0 /\
    IsCompatibleVariation
      (strongPullbackAsConstraintBridge complex)
      (complex.gaugeAction gauge) /\
    RestrictedHelmholtz
      (strongPullbackAsConstraintBridge complex) := by
  exact ⟨compatibility_after_gauge_zero complex gauge,
    bianchi_after_compatibility_zero complex first,
    source_hessian_formally_self_adjoint complex first second,
    source_hessian_annihilates_gauge complex gauge,
    gauge_direction_is_compatible_variation complex gauge,
    strong_pullback_implies_restricted_helmholtz complex⟩

/--
The weak compatibility-ideal route is strictly more general: it can be
restricted Helmholtz even when the operator is globally nonreciprocal.
-/
theorem weak_bridge_does_not_imply_global_reciprocity :
    RestrictedHelmholtz constrainedNonreciprocalBridge /\
    badMatrixPairing
        { first := 1, second := 0 }
        { first := 0, second := 1 } ≠
      badMatrixPairing
        { first := 0, second := 1 }
        { first := 1, second := 0 } := by
  exact ⟨example_restricted_helmholtz,
    example_globally_nonreciprocal⟩

/-- Exact hierarchy of the two sufficient mechanisms. -/
structure CompatibilityBridgeHierarchyStatus where
  strongPullbackHessianConstructed : Prop
  strongTargetPairingSelfAdjoint : Prop
  strongGlobalHelmholtzDerived : Prop
  strongNoetherDegeneracyDerived : Prop
  strongBridgeEmbeddedInConstraintFramework : Prop
  weakDefectFactorizationDerived : Prop
  weakBoundaryFluxControlled : Prop
  weakRestrictedHelmholtzDerived : Prop
  weakGlobalReciprocityNotClaimed : Prop


def compatibilityBridgeHierarchyClosed
    (s : CompatibilityBridgeHierarchyStatus) : Prop :=
  s.strongPullbackHessianConstructed /\
  s.strongTargetPairingSelfAdjoint /\
  s.strongGlobalHelmholtzDerived /\
  s.strongNoetherDegeneracyDerived /\
  s.strongBridgeEmbeddedInConstraintFramework /\
  s.weakDefectFactorizationDerived /\
  s.weakBoundaryFluxControlled /\
  s.weakRestrictedHelmholtzDerived /\
  s.weakGlobalReciprocityNotClaimed

/--
P.F hierarchy:

* **strong route:** `A = K* H K` with self-adjoint `H`; global Helmholtz and
  Noether follow;
* **weak route:** the antisymmetric defect lies in the compatibility ideal,
  modulo boundary flux; only restricted Helmholtz follows.

The actual Janus operator may realize the strong route, the weak route, or a
mixture sector by sector.  This must be computed rather than assumed.
-/
structure JanusCompatibilityHierarchyPhysicalStatus where
  actualCompatibilityMapConstructed : Prop
  actualAdjointConstructed : Prop
  actualTargetPairingConstructed : Prop
  strongFactorizationCheckedBySector : Prop
  residualAntisymmetricDefectComputed : Prop
  residualDefectFactorizationProved : Prop
  boundaryFluxComputed : Prop
  physicalDomainSpecified : Prop
  strongestValidRouteSelectedBySector : Prop


def janusCompatibilityHierarchyPhysicalClosure
    (s : JanusCompatibilityHierarchyPhysicalStatus) : Prop :=
  s.actualCompatibilityMapConstructed /\
  s.actualAdjointConstructed /\
  s.actualTargetPairingConstructed /\
  s.strongFactorizationCheckedBySector /\
  s.residualAntisymmetricDefectComputed /\
  s.residualDefectFactorizationProved /\
  s.boundaryFluxComputed /\
  s.physicalDomainSpecified /\
  s.strongestValidRouteSelectedBySector

end P0EFTJanusCompatibilityBridgeHierarchy
end JanusFormal
