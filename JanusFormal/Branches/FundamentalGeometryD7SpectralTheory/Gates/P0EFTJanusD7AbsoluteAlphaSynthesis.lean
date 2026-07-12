import Mathlib
import JanusFormal.Branches.FundamentalGeometryD.Gates.P0EFTJanusRGHeatKernelAbsoluteScale

namespace JanusFormal
namespace P0EFTJanusD7AbsoluteAlphaSynthesis

set_option autoImplicit false

open P0EFTJanusRGHeatKernelAbsoluteScale

/--
Terminal D7 data.  The renormalized nonlocal action supplies a dimensionless
stationary product, RG transmutation supplies a generated mass, and the
Dirac/LL sector supplies the primitive positive charge-radius lock.
-/
structure D7AbsoluteAlphaSynthesis extends RGHeatKernelScale where
  geometricLength : ℝ
  llChargeUnit : ℝ
  geometricLengthPositive : 0 < geometricLength
  llChargePositive : 0 < llChargeUnit
  alphaGeometryLock : alphaSquaredLength = geometricLength
  primitiveChargeRadiusLock :
    4 * llChargeUnit * alphaSquaredLength ^ 2 = 1

/-- D7 absolute hierarchy equation. -/
theorem terminal_alpha_hierarchy_law
    (s : D7AbsoluteAlphaSynthesis) :
    s.uvMass * s.circleModulus * s.alphaSquaredLength =
      s.stationaryProduct * Real.exp s.hierarchyExponent := by
  exact rg_spectral_hierarchy_law s.toRGHeatKernelScale

/-- The same primitive charge lock holds on the geometric throat radius. -/
theorem terminal_geometric_charge_lock
    (s : D7AbsoluteAlphaSynthesis) :
    4 * s.llChargeUnit * s.geometricLength ^ 2 = 1 := by
  rw [← s.alphaGeometryLock]
  exact s.primitiveChargeRadiusLock

/-- Division form of the absolute prediction. -/
theorem terminal_alpha_division_law
    (s : D7AbsoluteAlphaSynthesis) :
    s.alphaSquaredLength =
      s.stationaryProduct * Real.exp s.hierarchyExponent /
        (s.uvMass * s.circleModulus) := by
  exact rg_spectral_alpha_division_law s.toRGHeatKernelScale

/--
Eliminating the radius gives the terminal charge hierarchy relation

`4*q*x_*^2*exp(X)^2 = (mu_UV*T)^2`.
-/
theorem terminal_charge_hierarchy_law
    (s : D7AbsoluteAlphaSynthesis) :
    4 * s.llChargeUnit * s.stationaryProduct ^ 2 *
        Real.exp s.hierarchyExponent ^ 2 =
      (s.uvMass * s.circleModulus) ^ 2 := by
  have hHierarchy := terminal_alpha_hierarchy_law s
  calc
    4 * s.llChargeUnit * s.stationaryProduct ^ 2 *
        Real.exp s.hierarchyExponent ^ 2 =
      4 * s.llChargeUnit *
        (s.stationaryProduct * Real.exp s.hierarchyExponent) ^ 2 := by ring
    _ = 4 * s.llChargeUnit *
        (s.uvMass * s.circleModulus * s.alphaSquaredLength) ^ 2 := by
      rw [← hHierarchy]
    _ = (s.uvMass * s.circleModulus) ^ 2 *
        (4 * s.llChargeUnit * s.alphaSquaredLength ^ 2) := by ring
    _ = (s.uvMass * s.circleModulus) ^ 2 := by
      rw [s.primitiveChargeRadiusLock]
      ring

/-- The primitive squared-flux equation follows from the unsquared positive lock. -/
theorem terminal_primitive_flux_law
    (s : D7AbsoluteAlphaSynthesis) :
    16 * s.llChargeUnit ^ 2 * s.alphaSquaredLength ^ 4 = 1 := by
  calc
    16 * s.llChargeUnit ^ 2 * s.alphaSquaredLength ^ 4 =
      (4 * s.llChargeUnit * s.alphaSquaredLength ^ 2) ^ 2 := by ring
    _ = 1 := by
      rw [s.primitiveChargeRadiusLock]
      norm_num

/-- Complete terminal relational spectrum. -/
theorem terminal_d7_relational_spectrum
    (s : D7AbsoluteAlphaSynthesis) :
    (s.uvMass * s.circleModulus * s.alphaSquaredLength =
      s.stationaryProduct * Real.exp s.hierarchyExponent) /\
    (4 * s.llChargeUnit * s.geometricLength ^ 2 = 1) /\
    (4 * s.llChargeUnit * s.stationaryProduct ^ 2 *
        Real.exp s.hierarchyExponent ^ 2 =
      (s.uvMass * s.circleModulus) ^ 2) /\
    (16 * s.llChargeUnit ^ 2 * s.alphaSquaredLength ^ 4 = 1) := by
  exact ⟨terminal_alpha_hierarchy_law s,
    terminal_geometric_charge_lock s,
    terminal_charge_hierarchy_law s,
    terminal_primitive_flux_law s⟩

/-- Same independently derived microscopic and spectral data fix the same alpha. -/
theorem same_terminal_data_fix_same_alpha
    (first second : D7AbsoluteAlphaSynthesis)
    (hUV : first.uvMass = second.uvMass)
    (hProduct :
      first.betaCouplingProduct = second.betaCouplingProduct)
    (hPi : first.piConstant = second.piConstant)
    (hModulus : first.circleModulus = second.circleModulus)
    (hStationary :
      first.stationaryProduct = second.stationaryProduct) :
    first.alphaSquaredLength = second.alphaSquaredLength := by
  exact same_rg_and_spectral_data_fix_same_alpha
    first.toRGHeatKernelScale second.toRGHeatKernelScale
    hUV hProduct hPi hModulus hStationary

/--
Evidence status of the terminal D7 route.  Local heat coefficients are not
listed as sufficient inputs: they must be supplemented by the global analytic,
renormalization, RG and charge theorems below.
-/
structure D7TerminalPhysicalStatus where
  globalPinSpinCOperatorConstructed : Prop
  separatedInfiniteSpectrumProved : Prop
  heatKernelAndZetaContinuationProved : Prop
  etaAndZeroModesControlled : Prop
  fullRenormalizedNonlocalActionDerived : Prop
  finiteCountertermsFixedMicroscopically : Prop
  stableStationaryProductDerived : Prop
  circleModulusDerived : Prop
  betaFunctionComputed : Prop
  uvCouplingFixedMicroscopically : Prop
  independentUVMassDerived : Prop
  generatedMassDerived : Prop
  diracLLChargeLawDerived : Prop
  bimetricRadiusLockDerived : Prop
  bulkBoundaryChargeCompatibilityDerived : Prop
  noObservedScaleImported : Prop
  absoluteAlphaDerivedNoFit : Prop


def d7TerminalPhysicalClosure
    (s : D7TerminalPhysicalStatus) : Prop :=
  s.globalPinSpinCOperatorConstructed /\
  s.separatedInfiniteSpectrumProved /\
  s.heatKernelAndZetaContinuationProved /\
  s.etaAndZeroModesControlled /\
  s.fullRenormalizedNonlocalActionDerived /\
  s.finiteCountertermsFixedMicroscopically /\
  s.stableStationaryProductDerived /\
  s.circleModulusDerived /\
  s.betaFunctionComputed /\
  s.uvCouplingFixedMicroscopically /\
  s.independentUVMassDerived /\
  s.generatedMassDerived /\
  s.diracLLChargeLawDerived /\
  s.bimetricRadiusLockDerived /\
  s.bulkBoundaryChargeCompatibilityDerived /\
  s.noObservedScaleImported /\
  s.absoluteAlphaDerivedNoFit

/-- Missing a microscopic UV mass blocks the absolute prediction. -/
theorem missing_independent_uv_mass_blocks_d7_closure
    (s : D7TerminalPhysicalStatus)
    (hMissing : Not s.independentUVMassDerived) :
    Not (d7TerminalPhysicalClosure s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.2.2.2.2.1

/-- A fitted finite counterterm also blocks the physical closure. -/
theorem missing_microscopic_counterterm_law_blocks_d7_closure
    (s : D7TerminalPhysicalStatus)
    (hMissing : Not s.finiteCountertermsFixedMicroscopically) :
    Not (d7TerminalPhysicalClosure s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.1

end P0EFTJanusD7AbsoluteAlphaSynthesis
end JanusFormal
