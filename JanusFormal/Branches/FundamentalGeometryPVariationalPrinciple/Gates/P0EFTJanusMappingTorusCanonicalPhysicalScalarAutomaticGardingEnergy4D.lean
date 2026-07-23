import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusH1GraphComponentEnergy4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarEnergyGarding4D

/-!
# Automatic first-jet energy in the physical scalar Gårding estimate

The physical `H¹` graph is literally the closure of the value and finite-frame
derivative first jet.  Its squared norm is therefore dominated by the explicit
component energy constructed from the two `L²` projections.

This discharges the first field of `EnergyGardingData`.  A physical Gårding proof
now needs only one genuine PDE estimate:

`componentEnergy(u) ≤ |<Au,u>| + C₀ ‖u‖²`.

The abstract Gårding module then gives the graph-elliptic estimate consumed by
the completed boundary trace.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarAutomaticGardingEnergy4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusH1GraphComponentEnergy4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEnergyGarding4D

variable (period : Real) (hPeriod : period ≠ 0)
variable {massSquared : Real}

local instance canonicalLorentzVolumeFinite :
    MeasureTheory.IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

/-- Explicit physical first-jet component energy. -/
def canonicalPhysicalScalarFirstJetComponentEnergy
    (field : SmoothQuotientField period hPeriod Real) : Real :=
  smoothFirstJetComponentEnergy period hPeriod Real
    (finiteSmoothTangentFrame period hPeriod)
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) field

/-- Nonnegativity of the physical component energy. -/
theorem canonicalPhysicalScalarFirstJetComponentEnergy_nonnegative
    (field : SmoothQuotientField period hPeriod Real) :
    0 ≤ canonicalPhysicalScalarFirstJetComponentEnergy
      period hPeriod field :=
  smoothFirstJetComponentEnergy_nonnegative period hPeriod Real
    (finiteSmoothTangentFrame period hPeriod)
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) field

/-- The physical `H¹` norm is dominated by the explicit component energy. -/
theorem smoothToCanonicalPhysicalScalarH1_norm_sq_le_componentEnergy
    (field : SmoothQuotientField period hPeriod Real) :
    ‖smoothToCanonicalPhysicalScalarH1 period hPeriod field‖ ^ 2 ≤
      canonicalPhysicalScalarFirstJetComponentEnergy period hPeriod field :=
  smoothToH1Graph_norm_sq_le_componentEnergy period hPeriod Real
    (finiteSmoothTangentFrame period hPeriod)
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) field

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarAutomaticGardingEnergy4D

namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusH1GraphComponentEnergy4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEnergyGarding4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarAutomaticGardingEnergy4D

variable (period : Real) (hPeriod : period ≠ 0)
variable {massSquared : Real}

local instance canonicalLorentzVolumeFinite :
    MeasureTheory.IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

namespace CanonicalPhysicalScalarFirstSheetGreenCoreData

/-- The sole physical energy estimate still needed for Gårding after exposing
the actual first-jet components. -/
structure AutomaticEnergyGardingData
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared) where
  zerothConstant : Real
  zerothConstant_nonnegative : 0 ≤ zerothConstant
  componentEnergy_le_euler_pairing :
    ∀ field : SmoothQuotientField period hPeriod Real,
      canonicalPhysicalScalarFirstJetComponentEnergy period hPeriod field ≤
        |inner Real (green.core.operator field)
            (green.core.inclusion field)| +
          zerothConstant * ‖green.core.inclusion field‖ ^ 2

namespace AutomaticEnergyGardingData

/-- Conversion to the general energy-Gårding package. -/
def toEnergyGardingData
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (energy : green.AutomaticEnergyGardingData period hPeriod) :
    green.EnergyGardingData period hPeriod where
  derivativeEnergy :=
    canonicalPhysicalScalarFirstJetComponentEnergy period hPeriod
  derivativeEnergy_nonnegative :=
    canonicalPhysicalScalarFirstJetComponentEnergy_nonnegative period hPeriod
  h1_sq_le_l2_sq_add_energy := by
    intro field
    calc
      ‖smoothToCanonicalPhysicalScalarH1 period hPeriod field‖ ^ 2 ≤
          canonicalPhysicalScalarFirstJetComponentEnergy
            period hPeriod field :=
        smoothToCanonicalPhysicalScalarH1_norm_sq_le_componentEnergy
          period hPeriod field
      _ ≤ ‖green.core.inclusion field‖ ^ 2 +
          canonicalPhysicalScalarFirstJetComponentEnergy
            period hPeriod field := by
        exact le_add_of_nonneg_left (sq_nonneg _)
  zerothOrderConstant := energy.zerothConstant
  zerothOrderConstant_nonnegative := energy.zerothConstant_nonnegative
  energy_le_euler_pairing := energy.componentEnergy_le_euler_pairing

/-- Physical squared Gårding estimate. -/
def toSquaredGardingEstimate
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (energy : green.AutomaticEnergyGardingData period hPeriod) :=
  (energy.toEnergyGardingData period hPeriod green)
    |>.toSquaredGardingEstimate period hPeriod green

/-- Physical graph-elliptic estimate. -/
def toGraphEllipticEstimate
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (energy : green.AutomaticEnergyGardingData period hPeriod) :=
  (energy.toEnergyGardingData period hPeriod green)
    |>.toGraphEllipticEstimate period hPeriod green

/-- Automatic first-jet Gårding certificate. -/
theorem certificate
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared)
    (energy : green.AutomaticEnergyGardingData period hPeriod) :
    (∀ field : SmoothQuotientField period hPeriod Real,
      ‖smoothToCanonicalPhysicalScalarH1 period hPeriod field‖ ^ 2 ≤
        canonicalPhysicalScalarFirstJetComponentEnergy period hPeriod field) ∧
      (∀ field : SmoothQuotientField period hPeriod Real,
        ‖smoothToCanonicalPhysicalScalarH1 period hPeriod field‖ ^ 2 ≤
          (energy.toSquaredGardingEstimate period hPeriod green).constant *
            (‖green.core.inclusion field‖ ^ 2 +
              ‖green.core.operator field‖ ^ 2)) :=
  ⟨smoothToCanonicalPhysicalScalarH1_norm_sq_le_componentEnergy
      period hPeriod,
    (energy.toSquaredGardingEstimate period hPeriod green).bound_sq⟩

end AutomaticEnergyGardingData

end CanonicalPhysicalScalarFirstSheetGreenCoreData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D
end JanusFormal
