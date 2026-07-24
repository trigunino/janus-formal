import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarAutomaticGardingEnergy4D

/-!
# Gårding from an exact first-jet energy identity

For the physical scalar operator, the first-jet energy should arise from an
exact integration-by-parts identity.  The only lower-order contribution is a
bounded operator on physical bulk `L²`.

This file packages the natural identity

`E₁(u) = σ <Au,u> + <Bu,u>`,

where `|σ| = 1` and `B` is bounded.  Cauchy--Schwarz and the operator norm give

`E₁(u) ≤ |<Au,u>| + ‖B‖ ‖u‖²`.

Thus the former Gårding inequality and its constant are derived rather than
supplied independently.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarGardingIdentity4D
end P0EFTJanusMappingTorusCanonicalPhysicalScalarGardingIdentity4D

namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarAutomaticGardingEnergy4D

variable (period : Real) (hPeriod : period ≠ 0)
variable {massSquared : Real}

private abbrev BulkL2 :=
  CanonicalPhysicalBulkL2 period hPeriod

namespace CanonicalPhysicalScalarFirstSheetGreenCoreData

/-- Exact first-jet energy identity with a bounded zeroth-order remainder. -/
structure ExactEnergyGardingIdentityData
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared) where
  pairingSign : Real
  pairingSign_abs : |pairingSign| = 1
  zerothOrderOperator : BulkL2 period hPeriod →L[Real]
    BulkL2 period hPeriod
  energy_identity : ∀ field : SmoothQuotientField period hPeriod Real,
    canonicalPhysicalScalarFirstJetComponentEnergy period hPeriod field =
      pairingSign *
          inner Real (green.core.operator field)
            (green.core.inclusion field) +
        inner Real
          (zerothOrderOperator (green.core.inclusion field))
          (green.core.inclusion field)

namespace ExactEnergyGardingIdentityData

/-- The bounded zeroth-order quadratic form is controlled by its operator norm. -/
theorem zerothOrderPairing_abs_le
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (identity : green.ExactEnergyGardingIdentityData period hPeriod)
    (field : SmoothQuotientField period hPeriod Real) :
    |inner Real
        (identity.zerothOrderOperator (green.core.inclusion field))
        (green.core.inclusion field)| ≤
      ‖identity.zerothOrderOperator‖ *
        ‖green.core.inclusion field‖ ^ 2 := by
  let bulkField := green.core.inclusion field
  calc
    |inner Real (identity.zerothOrderOperator bulkField) bulkField| ≤
        ‖identity.zerothOrderOperator bulkField‖ * ‖bulkField‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ (‖identity.zerothOrderOperator‖ * ‖bulkField‖) * ‖bulkField‖ := by
      gcongr
      exact identity.zerothOrderOperator.le_opNorm bulkField
    _ = ‖identity.zerothOrderOperator‖ * ‖bulkField‖ ^ 2 := by ring

/-- The exact identity implies the one remaining automatic Gårding estimate. -/
theorem componentEnergy_le_euler_pairing
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (identity : green.ExactEnergyGardingIdentityData period hPeriod)
    (field : SmoothQuotientField period hPeriod Real) :
    canonicalPhysicalScalarFirstJetComponentEnergy period hPeriod field ≤
      |inner Real (green.core.operator field)
          (green.core.inclusion field)| +
        ‖identity.zerothOrderOperator‖ *
          ‖green.core.inclusion field‖ ^ 2 := by
  rw [identity.energy_identity]
  let pairing := inner Real (green.core.operator field)
    (green.core.inclusion field)
  let remainder := inner Real
    (identity.zerothOrderOperator (green.core.inclusion field))
    (green.core.inclusion field)
  have hSign : |identity.pairingSign * pairing| = |pairing| := by
    rw [abs_mul, identity.pairingSign_abs, one_mul]
  have hRemainder :=
    identity.zerothOrderPairing_abs_le period hPeriod green field
  change identity.pairingSign * pairing + remainder ≤
    |pairing| + ‖identity.zerothOrderOperator‖ *
      ‖green.core.inclusion field‖ ^ 2
  calc
    identity.pairingSign * pairing + remainder ≤
        |identity.pairingSign * pairing| + |remainder| :=
      add_le_add (le_abs_self _) (le_abs_self _)
    _ = |pairing| + |remainder| := by rw [hSign]
    _ ≤ _ := add_le_add_right hRemainder _

/-- Conversion to the automatic Gårding package. -/
def toAutomaticEnergyGardingData
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (identity : green.ExactEnergyGardingIdentityData period hPeriod) :
    green.AutomaticEnergyGardingData period hPeriod where
  zerothConstant := ‖identity.zerothOrderOperator‖
  zerothConstant_nonnegative :=
    ContinuousLinearMap.opNorm_nonneg identity.zerothOrderOperator
  componentEnergy_le_euler_pairing :=
    identity.componentEnergy_le_euler_pairing period hPeriod green

/-- Squared physical Gårding estimate. -/
def toSquaredGardingEstimate
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (identity : green.ExactEnergyGardingIdentityData period hPeriod) :=
  (identity.toAutomaticEnergyGardingData period hPeriod green)
    |>.toSquaredGardingEstimate period hPeriod green

/-- Physical graph-elliptic estimate. -/
def toGraphEllipticEstimate
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (identity : green.ExactEnergyGardingIdentityData period hPeriod) :=
  (identity.toAutomaticEnergyGardingData period hPeriod green)
    |>.toGraphEllipticEstimate period hPeriod green

/-- Exact-energy Gårding certificate. -/
theorem certificate
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (identity : green.ExactEnergyGardingIdentityData period hPeriod) :
    (∀ field : SmoothQuotientField period hPeriod Real,
      canonicalPhysicalScalarFirstJetComponentEnergy period hPeriod field =
        identity.pairingSign *
            inner Real (green.core.operator field)
              (green.core.inclusion field) +
          inner Real
            (identity.zerothOrderOperator (green.core.inclusion field))
            (green.core.inclusion field)) ∧
      (∀ field : SmoothQuotientField period hPeriod Real,
        canonicalPhysicalScalarFirstJetComponentEnergy period hPeriod field ≤
          |inner Real (green.core.operator field)
              (green.core.inclusion field)| +
            ‖identity.zerothOrderOperator‖ *
              ‖green.core.inclusion field‖ ^ 2) :=
  ⟨identity.energy_identity,
    identity.componentEnergy_le_euler_pairing period hPeriod green⟩

end ExactEnergyGardingIdentityData

end CanonicalPhysicalScalarFirstSheetGreenCoreData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D
end JanusFormal
