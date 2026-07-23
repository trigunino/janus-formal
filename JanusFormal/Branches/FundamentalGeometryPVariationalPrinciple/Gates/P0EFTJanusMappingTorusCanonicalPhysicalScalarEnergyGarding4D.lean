import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarGardingEstimate4D

/-!
# Physical scalar Gårding estimate from the geometric energy

A standard Gårding proof has two geometric inputs.  First, the physical `H¹`
norm is bounded by the bulk `L²` norm plus a nonnegative first-derivative energy.
Second, integration by parts bounds that derivative energy by the absolute Euler
pairing plus a bounded zeroth-order contribution.

Cauchy--Schwarz and the elementary Young inequality

`a b ≤ (a²+b²)/2`

then give

`||u||_H1² ≤ C (||u||_L2² + ||A u||_L2²)`.

This file performs that functional-analytic part and leaves only the two genuine
geometric energy estimates to be proved from the intrinsic metric.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarEnergyGarding4D
end P0EFTJanusMappingTorusCanonicalPhysicalScalarEnergyGarding4D

namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarGardingEstimate4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D

variable (period : Real) (hPeriod : period ≠ 0)
variable {massSquared : Real}

namespace CanonicalPhysicalScalarFirstSheetGreenCoreData

/-- Geometric energy input for the physical scalar Gårding inequality. -/
structure EnergyGardingData
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared) where
  derivativeEnergy : SmoothQuotientField period hPeriod Real → Real
  derivativeEnergy_nonnegative : ∀ field, 0 ≤ derivativeEnergy field
  h1_sq_le_l2_sq_add_energy :
    ∀ field : SmoothQuotientField period hPeriod Real,
      ‖P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D.smoothToCanonicalPhysicalScalarH1
          period hPeriod field‖ ^ 2 ≤
        ‖green.core.inclusion field‖ ^ 2 + derivativeEnergy field
  zerothOrderConstant : Real
  zerothOrderConstant_nonnegative : 0 ≤ zerothOrderConstant
  energy_le_euler_pairing :
    ∀ field : SmoothQuotientField period hPeriod Real,
      derivativeEnergy field ≤
        |inner Real (green.core.operator field) (green.core.inclusion field)| +
          zerothOrderConstant * ‖green.core.inclusion field‖ ^ 2

namespace EnergyGardingData

/-- Coefficient multiplying the sum of bulk and Euler squares. -/
def gardingConstant
    {green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared}
    (energy : green.EnergyGardingData period hPeriod) : Real :=
  max (1 / 2 : Real) (3 / 2 + energy.zerothOrderConstant)

/-- Positivity of the Gårding coefficient. -/
theorem gardingConstant_nonnegative
    {green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared}
    (energy : green.EnergyGardingData period hPeriod) :
    0 ≤ energy.gardingConstant := by
  exact (by norm_num : (0 : Real) ≤ 1 / 2).trans
    (le_max_left _ _)

/-- Young's inequality in the exact normalization used below. -/
theorem norm_mul_norm_le_half_sq_add_half_sq
    (first second : Real) (hFirst : 0 ≤ first) (hSecond : 0 ≤ second) :
    first * second ≤ (1 / 2 : Real) * first ^ 2 +
      (1 / 2 : Real) * second ^ 2 := by
  nlinarith [sq_nonneg (first - second)]

/-- The two geometric energy statements imply the squared Gårding estimate. -/
def toSquaredGardingEstimate
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (energy : green.EnergyGardingData period hPeriod) :
    green.SquaredGardingEstimate period hPeriod where
  constant := energy.gardingConstant
  nonnegative := energy.gardingConstant_nonnegative
  bound_sq := by
    intro field
    let inclusionNorm := ‖green.core.inclusion field‖
    let operatorNorm := ‖green.core.operator field‖
    have hInclusionNonnegative : 0 ≤ inclusionNorm := norm_nonneg _
    have hOperatorNonnegative : 0 ≤ operatorNorm := norm_nonneg _
    have hPair :
        |inner Real (green.core.operator field) (green.core.inclusion field)| ≤
          operatorNorm * inclusionNorm := by
      exact abs_real_inner_le_norm _ _
    have hYoung : operatorNorm * inclusionNorm ≤
        (1 / 2 : Real) * operatorNorm ^ 2 +
          (1 / 2 : Real) * inclusionNorm ^ 2 :=
      norm_mul_norm_le_half_sq_add_half_sq
        operatorNorm inclusionNorm hOperatorNonnegative hInclusionNonnegative
    have hEnergy := energy.energy_le_euler_pairing field
    have hH1 := energy.h1_sq_le_l2_sq_add_energy field
    have hOperatorCoefficient :
        (1 / 2 : Real) ≤ energy.gardingConstant :=
      le_max_left _ _
    have hInclusionCoefficient :
        3 / 2 + energy.zerothOrderConstant ≤ energy.gardingConstant :=
      le_max_right _ _
    have hOperatorScaled :
        (1 / 2 : Real) * operatorNorm ^ 2 ≤
          energy.gardingConstant * operatorNorm ^ 2 :=
      mul_le_mul_of_nonneg_right hOperatorCoefficient (sq_nonneg _)
    have hInclusionScaled :
        (3 / 2 + energy.zerothOrderConstant) * inclusionNorm ^ 2 ≤
          energy.gardingConstant * inclusionNorm ^ 2 :=
      mul_le_mul_of_nonneg_right hInclusionCoefficient (sq_nonneg _)
    calc
      ‖P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D.smoothToCanonicalPhysicalScalarH1
          period hPeriod field‖ ^ 2 ≤
          inclusionNorm ^ 2 + energy.derivativeEnergy field := hH1
      _ ≤ inclusionNorm ^ 2 +
          (|inner Real (green.core.operator field)
              (green.core.inclusion field)| +
            energy.zerothOrderConstant * inclusionNorm ^ 2) :=
        add_le_add_right hEnergy _
      _ ≤ inclusionNorm ^ 2 +
          (operatorNorm * inclusionNorm +
            energy.zerothOrderConstant * inclusionNorm ^ 2) :=
        add_le_add_right
          (add_le_add_left hPair _) _
      _ ≤ inclusionNorm ^ 2 +
          ((1 / 2 : Real) * operatorNorm ^ 2 +
            (1 / 2 : Real) * inclusionNorm ^ 2 +
            energy.zerothOrderConstant * inclusionNorm ^ 2) :=
        add_le_add_right
          (add_le_add_left hYoung _) _
      _ = (1 / 2 : Real) * operatorNorm ^ 2 +
          (3 / 2 + energy.zerothOrderConstant) * inclusionNorm ^ 2 := by
        ring
      _ ≤ energy.gardingConstant * operatorNorm ^ 2 +
          energy.gardingConstant * inclusionNorm ^ 2 :=
        add_le_add hOperatorScaled hInclusionScaled
      _ = energy.gardingConstant *
          (inclusionNorm ^ 2 + operatorNorm ^ 2) := by
        ring

/-- Linear graph-elliptic estimate obtained from the energy argument. -/
def toGraphEllipticEstimate
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (energy : green.EnergyGardingData period hPeriod) :
    green.GraphEllipticEstimate period hPeriod :=
  (energy.toSquaredGardingEstimate period hPeriod green)
    |>.toGraphEllipticEstimate period hPeriod green

/-- Energy-Gårding certificate. -/
theorem certificate
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (energy : green.EnergyGardingData period hPeriod) :
    (∀ field : SmoothQuotientField period hPeriod Real,
      ‖P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D.smoothToCanonicalPhysicalScalarH1
          period hPeriod field‖ ^ 2 ≤
        energy.gardingConstant *
          (‖green.core.inclusion field‖ ^ 2 +
            ‖green.core.operator field‖ ^ 2)) ∧
      (∀ field : SmoothQuotientField period hPeriod Real,
        ‖P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D.smoothToCanonicalPhysicalScalarH1
            period hPeriod field‖ ≤
          Real.sqrt (2 * energy.gardingConstant) *
            ‖canonicalScalarGreenCoreToGraph green.core field‖) :=
  ⟨(energy.toSquaredGardingEstimate period hPeriod green).bound_sq,
    (energy.toGraphEllipticEstimate period hPeriod green).bound⟩

end EnergyGardingData

end CanonicalPhysicalScalarFirstSheetGreenCoreData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D
end JanusFormal
