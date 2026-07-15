import Mathlib

namespace JanusFormal
namespace P0EFTJanusCO01PlugstarSourceAudit

set_option autoImplicit false

noncomputable section

/-- Central lapse factor of the constant-density Schwarzschild interior,
written with the surface root `x = sqrt(1-Rs/R)`. -/
def centralLapseFromSurfaceRoot (x : ℝ) : ℝ := (3 * x - 1) / 2

/-- At the pressure-critical compactness `Rs/R=8/9`, the surface root is
`x=1/3` and the lapse factor is `1/3`. -/
theorem critical_central_lapse :
    centralLapseFromSurfaceRoot (1 / 3 : ℝ) = 0 := by
  norm_num [centralLapseFromSurfaceRoot]

/-- The paper's redshift computation instead evaluates the central-to-surface
factor `3/2 sqrt(1-8/9)-1/2 sqrt(1-8/9)=1/3`. -/
def quotedCriticalRedshiftLapse (x : ℝ) : ℝ :=
  (3 / 2 : ℝ) * x - (1 / 2 : ℝ) * x

theorem quoted_critical_redshift_lapse :
    quotedCriticalRedshiftLapse (1 / 3 : ℝ) = 1 / 3 := by
  norm_num [quotedCriticalRedshiftLapse]

theorem quoted_wavelength_ratio_is_three :
    1 / quotedCriticalRedshiftLapse (1 / 3 : ℝ) = 3 := by
  norm_num [quotedCriticalRedshiftLapse]

/-- CO01 separates exact source formulas from the new physical assumptions
needed for a plugstar. -/
structure PlugstarSourceLedger where
  constantDensityInteriorMetricCurated : Prop
  hydrostaticPressureFirstIntegralCurated : Prop
  pressureCriticalCompactnessCurated : Prop
  quotedRedshiftRatioChecked : Prop
  variablePhysicalLightSpeedDerived : Prop
  massInversionLawDerived : Prop
  negativeSectorStressTensorSpecified : Prop
  junctionConditionsSpecified : Prop
  radialStabilityDerived : Prop
  emissionModelSpecified : Prop

def sourceFormulaCoreChecked (s : PlugstarSourceLedger) : Prop :=
  s.constantDensityInteriorMetricCurated ∧
  s.hydrostaticPressureFirstIntegralCurated ∧
  s.pressureCriticalCompactnessCurated ∧
  s.quotedRedshiftRatioChecked

def physicalPlugstarModelReady (s : PlugstarSourceLedger) : Prop :=
  sourceFormulaCoreChecked s ∧
  s.variablePhysicalLightSpeedDerived ∧
  s.massInversionLawDerived ∧
  s.negativeSectorStressTensorSpecified ∧
  s.junctionConditionsSpecified ∧
  s.radialStabilityDerived ∧
  s.emissionModelSpecified

theorem missing_mass_inversion_blocks_physical_model
    (s : PlugstarSourceLedger) (hMissing : ¬s.massInversionLawDerived) :
    ¬physicalPlugstarModelReady s := by
  intro hReady
  exact hMissing hReady.2.2.1

end

end P0EFTJanusCO01PlugstarSourceAudit
end JanusFormal
