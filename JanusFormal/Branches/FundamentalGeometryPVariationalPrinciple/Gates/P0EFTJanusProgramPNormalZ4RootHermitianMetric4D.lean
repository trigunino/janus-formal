import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusSmoothNormalZ4RootBundle

/-! # Hermitian metric on the global normal Z4-root line

The actual complex root line on the Janus throat has unitary transition
phases.  Hence its standard Hermitian pairing is independent of local bundle
coordinates.  This is a global throat result, not yet an ambient PinC bundle.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPNormalZ4RootHermitianMetric4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusSmoothNormalZ4RootBundle
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatCover :=
  MappingTorusCover (fixedEquatorData period hPeriod)

private abbrev ThroatBase :=
  MappingTorus (fixedEquatorData period hPeriod)

/-- Every deck transition of either normal-root choice is a unit phase. -/
theorem quarterRootRepresentation_norm
    (choice : NormalRootChoice) (winding : ℤ) :
    ‖quarterRootRepresentation choice winding‖ = 1 := by
  rw [quarterRootRepresentation, norm_zpow]
  cases choice <;> simp [normalRootMultiplier]

/-- The root transition represented as an element of the unit circle. -/
def quarterRootCircleRepresentation
    (choice : NormalRootChoice) (winding : ℤ) : Circle where
  val := quarterRootRepresentation choice winding
  property := mem_sphere_zero_iff_norm.mpr
    (quarterRootRepresentation_norm choice winding)

def normalZ4RootHermitianPairing (first second : Complex) : Complex :=
  (starRingEnd Complex) first * second

/-- A quarter-root deck transformation preserves the Hermitian pairing. -/
theorem normalZ4RootHermitianPairing_quarterRoot_invariant
    (choice : NormalRootChoice) (winding : ℤ) (first second : Complex) :
    normalZ4RootHermitianPairing
        (quarterRootCLM choice winding first)
        (quarterRootCLM choice winding second) =
      normalZ4RootHermitianPairing first second := by
  let phase := quarterRootCircleRepresentation choice winding
  change (starRingEnd Complex) ((phase : Complex) * first) *
      ((phase : Complex) * second) =
    (starRingEnd Complex) first * second
  rw [map_mul, ← Circle.coe_inv_eq_conj]
  calc
    (((phase⁻¹ : Circle) : Complex) * (starRingEnd Complex) first) *
          ((phase : Complex) * second) =
        (((phase⁻¹ : Circle) : Complex) * (phase : Complex)) *
          ((starRingEnd Complex) first * second) := by ring
    _ = (starRingEnd Complex) first * second := by
      rw [← Circle.coe_mul]
      simp

/-- The actual root-bundle coordinate changes preserve the pairing. -/
theorem fixedThroatNormalZ4Root_coordChange_preserves_pairing
    (choice : NormalRootChoice)
    (firstChart secondChart : ThroatCover period hPeriod)
    (base : ThroatBase period hPeriod) (first second : Complex) :
    normalZ4RootHermitianPairing
        ((fixedThroatNormalZ4RootBundleCore period hPeriod choice).coordChange
          firstChart secondChart base first)
        ((fixedThroatNormalZ4RootBundleCore period hPeriod choice).coordChange
          firstChart secondChart base second) =
      normalZ4RootHermitianPairing first second := by
  simp only [fixedThroatNormalZ4RootBundleCore, quarterRootCLM_apply]
  exact normalZ4RootHermitianPairing_quarterRoot_invariant _ _ _ _

theorem normalZ4RootHermitianPairing_nondegenerate
    (root : Complex)
    (hRadical : ∀ test, normalZ4RootHermitianPairing root test = 0) :
    root = 0 := by
  have hSelf := hRadical root
  change (starRingEnd Complex) root * root = 0 at hSelf
  have hNormSq : (Complex.normSq root : Complex) = 0 := by
    rw [Complex.normSq_eq_conj_mul_self]
    exact hSelf
  exact Complex.normSq_eq_zero.mp (Complex.ofReal_injective hNormSq)

structure ProgramPNormalZ4RootHermitianMetricCertificate4D
    (choice : NormalRootChoice) where
  bundleCore :
    VectorBundleCore Complex (ThroatBase period hPeriod) Complex
      (ThroatCover period hPeriod)
  canonicalBundle :
    bundleCore = fixedThroatNormalZ4RootBundleCore period hPeriod choice
  transitionInvariant :
    ∀ firstChart secondChart base first second,
      normalZ4RootHermitianPairing
          (bundleCore.coordChange firstChart secondChart base first)
          (bundleCore.coordChange firstChart secondChart base second) =
        normalZ4RootHermitianPairing first second
  nondegenerate :
    ∀ root, (∀ test, normalZ4RootHermitianPairing root test = 0) → root = 0

def programPNormalZ4RootHermitianMetricCertificate4D
    (choice : NormalRootChoice) :
    ProgramPNormalZ4RootHermitianMetricCertificate4D period hPeriod choice where
  bundleCore := fixedThroatNormalZ4RootBundleCore period hPeriod choice
  canonicalBundle := rfl
  transitionInvariant :=
    fixedThroatNormalZ4Root_coordChange_preserves_pairing period hPeriod choice
  nondegenerate := normalZ4RootHermitianPairing_nondegenerate

theorem programPNormalZ4RootHermitianMetricCertificate4D_nonempty
    (choice : NormalRootChoice) :
    Nonempty
      (ProgramPNormalZ4RootHermitianMetricCertificate4D
        period hPeriod choice) :=
  ⟨programPNormalZ4RootHermitianMetricCertificate4D period hPeriod choice⟩

end
end P0EFTJanusProgramPNormalZ4RootHermitianMetric4D
end JanusFormal
