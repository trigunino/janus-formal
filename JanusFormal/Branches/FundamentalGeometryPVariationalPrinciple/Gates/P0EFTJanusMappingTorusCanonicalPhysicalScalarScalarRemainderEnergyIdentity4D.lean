import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarGardingIdentity4D

/-!
# Physical scalar energy identity with a scalar zeroth-order remainder

For a Klein--Gordon type scalar operator, the zeroth-order part of the first-jet
energy identity is scalar multiplication on physical bulk `L²`.  Supplying an
arbitrary bounded operator is therefore unnecessary.

This file packages the concrete identity

`E₁(u) = σ <Au,u> + c ‖u‖²`,

with `|σ| = 1`.  It constructs the former exact-energy package using
`c • id`, so the complete Gårding and graph-elliptic estimates follow with
zeroth-order constant `|c|`.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarScalarRemainderEnergyIdentity4D
end P0EFTJanusMappingTorusCanonicalPhysicalScalarScalarRemainderEnergyIdentity4D

namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarAutomaticGardingEnergy4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarGardingIdentity4D

variable (period : Real) (hPeriod : period ≠ 0)
variable {massSquared : Real}

private abbrev BulkL2 :=
  CanonicalPhysicalBulkL2 period hPeriod

namespace CanonicalPhysicalScalarFirstSheetGreenCoreData

/-- Exact first-jet energy identity with a scalar zeroth-order remainder. -/
structure ScalarRemainderEnergyIdentityData
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared) where
  pairingSign : Real
  pairingSign_abs : |pairingSign| = 1
  zerothCoefficient : Real
  energy_identity : ∀ field : SmoothQuotientField period hPeriod Real,
    canonicalPhysicalScalarFirstJetComponentEnergy period hPeriod field =
      pairingSign *
          inner Real (green.core.operator field)
            (green.core.inclusion field) +
        zerothCoefficient * ‖green.core.inclusion field‖ ^ 2

/-- First-jet identity after restoring the mass term to the Euler operator.
The scalar remainder is then forced to be `pairingSign * massSquared`. -/
structure MassCorrectedEnergyIdentityData
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared) where
  pairingSign : Real
  pairingSign_abs : |pairingSign| = 1
  kinetic_identity : ∀ field : SmoothQuotientField period hPeriod Real,
    canonicalPhysicalScalarFirstJetComponentEnergy period hPeriod field =
      pairingSign *
        (inner Real (green.core.operator field)
            (green.core.inclusion field) +
          massSquared * ‖green.core.inclusion field‖ ^ 2)

namespace MassCorrectedEnergyIdentityData

/-- Conversion to the scalar-remainder interface, with no independent
zeroth-order coefficient. -/
def toScalarRemainderEnergyIdentityData
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (identity : green.MassCorrectedEnergyIdentityData period hPeriod) :
    green.ScalarRemainderEnergyIdentityData period hPeriod where
  pairingSign := identity.pairingSign
  pairingSign_abs := identity.pairingSign_abs
  zerothCoefficient := identity.pairingSign * massSquared
  energy_identity := by
    intro field
    rw [identity.kinetic_identity]
    ring

/-- The mass convention completely determines the old scalar remainder. -/
theorem certificate
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (identity : green.MassCorrectedEnergyIdentityData period hPeriod) :
    (identity.toScalarRemainderEnergyIdentityData period hPeriod green).zerothCoefficient =
      identity.pairingSign * massSquared ∧
      (∀ field : SmoothQuotientField period hPeriod Real,
        canonicalPhysicalScalarFirstJetComponentEnergy period hPeriod field =
          identity.pairingSign *
              inner Real (green.core.operator field)
                (green.core.inclusion field) +
            identity.pairingSign * massSquared *
              ‖green.core.inclusion field‖ ^ 2) := by
  refine ⟨rfl, ?_⟩
  intro field
  rw [identity.kinetic_identity]
  ring

end MassCorrectedEnergyIdentityData

namespace ScalarRemainderEnergyIdentityData

/-- Scalar multiplication on physical bulk `L²`. -/
def zerothOrderOperator
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (identity : green.ScalarRemainderEnergyIdentityData period hPeriod) :
    BulkL2 period hPeriod →L[Real] BulkL2 period hPeriod :=
  identity.zerothCoefficient • ContinuousLinearMap.id Real (BulkL2 period hPeriod)

/-- Quadratic form of the scalar multiplication operator. -/
theorem zerothOrderOperator_pairing
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (identity : green.ScalarRemainderEnergyIdentityData period hPeriod)
    (field : SmoothQuotientField period hPeriod Real) :
    inner Real
        (identity.zerothOrderOperator period hPeriod green
          (green.core.inclusion field))
        (green.core.inclusion field) =
      identity.zerothCoefficient * ‖green.core.inclusion field‖ ^ 2 := by
  simp [zerothOrderOperator, real_inner_smul_left,
    real_inner_self_eq_norm_sq]

/-- Conversion to the general exact-energy identity package. -/
def toExactEnergyGardingIdentityData
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (identity : green.ScalarRemainderEnergyIdentityData period hPeriod) :
    green.ExactEnergyGardingIdentityData period hPeriod where
  pairingSign := identity.pairingSign
  pairingSign_abs := identity.pairingSign_abs
  zerothOrderOperator := identity.zerothOrderOperator period hPeriod green
  energy_identity := by
    intro field
    rw [identity.zerothOrderOperator_pairing period hPeriod green field]
    exact identity.energy_identity field

/-- Automatic Gårding package. -/
def toAutomaticEnergyGardingData
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (identity : green.ScalarRemainderEnergyIdentityData period hPeriod) :=
  (identity.toExactEnergyGardingIdentityData period hPeriod green)
    |>.toAutomaticEnergyGardingData period hPeriod green

/-- Physical graph-elliptic estimate. -/
def toGraphEllipticEstimate
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (identity : green.ScalarRemainderEnergyIdentityData period hPeriod) :=
  (identity.toExactEnergyGardingIdentityData period hPeriod green)
    |>.toGraphEllipticEstimate period hPeriod green

/-- Direct scalar-remainder Gårding estimate. -/
theorem componentEnergy_le_euler_pairing
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (identity : green.ScalarRemainderEnergyIdentityData period hPeriod)
    (field : SmoothQuotientField period hPeriod Real) :
    canonicalPhysicalScalarFirstJetComponentEnergy period hPeriod field ≤
      |inner Real (green.core.operator field)
          (green.core.inclusion field)| +
        |identity.zerothCoefficient| *
          ‖green.core.inclusion field‖ ^ 2 := by
  rw [identity.energy_identity]
  let pairing := inner Real (green.core.operator field)
    (green.core.inclusion field)
  have hSign : |identity.pairingSign * pairing| = |pairing| := by
    rw [abs_mul, identity.pairingSign_abs, one_mul]
  calc
    identity.pairingSign * pairing +
        identity.zerothCoefficient * ‖green.core.inclusion field‖ ^ 2 ≤
      |identity.pairingSign * pairing| +
        |identity.zerothCoefficient * ‖green.core.inclusion field‖ ^ 2| :=
      add_le_add (le_abs_self _) (le_abs_self _)
    _ = |pairing| + |identity.zerothCoefficient| *
        ‖green.core.inclusion field‖ ^ 2 := by
      rw [hSign, abs_mul, abs_sq]

/-- Scalar-remainder energy certificate. -/
theorem certificate
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (identity : green.ScalarRemainderEnergyIdentityData period hPeriod) :
    (∀ field : SmoothQuotientField period hPeriod Real,
      canonicalPhysicalScalarFirstJetComponentEnergy period hPeriod field =
        identity.pairingSign *
            inner Real (green.core.operator field)
              (green.core.inclusion field) +
          identity.zerothCoefficient * ‖green.core.inclusion field‖ ^ 2) ∧
      (∀ field : SmoothQuotientField period hPeriod Real,
        canonicalPhysicalScalarFirstJetComponentEnergy period hPeriod field ≤
          |inner Real (green.core.operator field)
              (green.core.inclusion field)| +
            |identity.zerothCoefficient| *
              ‖green.core.inclusion field‖ ^ 2) :=
  ⟨identity.energy_identity,
    identity.componentEnergy_le_euler_pairing period hPeriod green⟩

end ScalarRemainderEnergyIdentityData

end CanonicalPhysicalScalarFirstSheetGreenCoreData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D
end JanusFormal
