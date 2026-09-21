import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusT08GlobalLLPotentialVariation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusDifferentialLLWeakEquation4D

/-!
# T08: potentials coupled to the existing differential LL energy

The kinetic term acts on the flux, with weight 1 + norm(auxiliary metric)^2.
A power potential in the independent scalar measure changes its Euler
coefficient, while the flux and auxiliary-metric variations retain the
existing differential pairings. No intrinsic Lorentzian contraction,
strong divergence formula, source selection or BRST/BV closure is claimed.
-/
namespace JanusFormal
namespace P0EFTJanusT08DifferentialLLPotentialVariation4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusGlobalLLWorldvolume4D
open P0EFTJanusMappingTorusGlobalLLVariation4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusT08GlobalLLPotentialVariation4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev Throat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace ThroatCoverModel (Throat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (Throat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (Throat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (Throat period hPeriod) := borel _
local instance : BorelSpace (Throat period hPeriod) where measurable_eq := rfl
local instance realNormedModule : Module Real Real := NormedField.toNormedSpace.toModule

def globalDifferentialLLPowerAction (frame : SmoothThroatGeneratingFrame period hPeriod)
    (coupling reference : Real) (degree : Nat) (fields : IndependentFields period hPeriod)
    (mu : Measure (Throat period hPeriod)) : Real :=
  globalDifferentialLLAction period hPeriod frame fields mu +
    ∫ point, powerPotentialDensity period hPeriod coupling reference degree fields point ∂mu

/-- The new potential has no flux dependence. The derivative retains the
weighted derivative pairing, so the algebraic zero-flux classification must
not be reused as a pointwise differential equation. -/
theorem differential_power_flux_hasDerivAt
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (coupling reference : Real) (degree : Nat) (fields : IndependentFields period hPeriod)
    (direction : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (Throat period hPeriod)) [IsFiniteMeasure mu] :
    HasDerivAt (fun t : Real => globalDifferentialLLPowerAction period hPeriod frame
      coupling reference degree (differentialLLFluxCurve period hPeriod fields direction t) mu)
      (globalDifferentialLLFluxFirstVariation period hPeriod frame fields direction mu) 0 := by
  exact (globalDifferentialLLAction_fluxCurve_hasDerivAt period hPeriod frame fields direction mu).add_const
    (∫ point, powerPotentialDensity period hPeriod coupling reference degree fields point ∂mu)

theorem differential_power_auxMetric_hasDerivAt
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (coupling reference : Real) (degree : Nat) (fields : IndependentFields period hPeriod)
    (direction : SmoothThroatField period hPeriod LLMetricFiber)
    (mu : Measure (Throat period hPeriod)) [IsFiniteMeasure mu] :
    HasDerivAt (fun t : Real => globalDifferentialLLPowerAction period hPeriod frame
      coupling reference degree (differentialLLAuxMetricCurve period hPeriod fields direction t) mu)
      (globalDifferentialLLAuxMetricFirstVariation period hPeriod frame fields direction mu) 0 := by
  exact (globalDifferentialLLAction_auxMetricCurve_hasDerivAt period hPeriod frame fields direction mu).add_const
    (∫ point, powerPotentialDensity period hPeriod coupling reference degree fields point ∂mu)

/-- Exact separation of the kinetic energy from the deformed algebraic action. -/
theorem differential_power_eq_kinetic_add
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (coupling reference : Real) (degree : Nat) (fields : IndependentFields period hPeriod)
    (mu : Measure (Throat period hPeriod)) [IsFiniteMeasure mu] :
    globalDifferentialLLPowerAction period hPeriod frame coupling reference degree fields mu =
      (∫ point, (1 / 2 : Real) * llAuxiliaryKineticWeight period hPeriod fields point *
        throatDerivativeEnergy period hPeriod frame fields.llField point ∂mu) +
      globalLLPowerAction period hPeriod coupling reference degree fields mu := by
  have hKin : Integrable (fun point => (1 / 2 : Real) *
      llAuxiliaryKineticWeight period hPeriod fields point *
      throatDerivativeEnergy period hPeriod frame fields.llField point) mu :=
    ((continuous_const.mul (llAuxiliaryKineticWeight_continuous period hPeriod fields)).mul
      (throatDerivativeEnergy_continuous period hPeriod frame fields.llField)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  unfold globalDifferentialLLPowerAction globalDifferentialLLAction differentialLLDensity
    globalLLPowerAction globalLLAction
  rw [integral_add hKin (llWorldvolumeDensity_integrable period hPeriod fields mu)]
  ring

/-- Only chi varies; the kinetic energy is constant on this curve. -/
theorem differential_power_measure_hasDerivAt
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (coupling reference : Real) (degree : Nat) (fields : IndependentFields period hPeriod)
    (direction : SmoothThroatField period hPeriod Real)
    (mu : Measure (Throat period hPeriod)) [IsFiniteMeasure mu] :
    HasDerivAt (fun t : Real => globalDifferentialLLPowerAction period hPeriod frame
      coupling reference degree
      (llAffineCurve period hPeriod fields ⟨direction, 0⟩ t) mu)
      (∫ point, direction point * powerMeasureEuler period hPeriod coupling reference degree fields point ∂mu) 0 := by
  have hBase := globalLLPowerAction_affine_hasDerivAt period hPeriod coupling reference degree
    fields ⟨direction, 0⟩ mu
  have hAdded := hBase.const_add
    (∫ point, (1 / 2 : Real) * llAuxiliaryKineticWeight period hPeriod fields point *
      throatDerivativeEnergy period hPeriod frame fields.llField point ∂mu)
  have hZero : ∀ point : Throat period hPeriod,
      (0 : SmoothThroatField period hPeriod LLFieldFiber).toFun point = 0 := fun _ => rfl
  simpa only [differential_power_eq_kinetic_add, llAffineCurve, smul_zero, add_zero,
    llAuxiliaryKineticWeight, hZero, inner_zero_right] using hAdded

/-- Flux stationarity of the deformed action is exactly the existing weak
LL equation, with chi evaluated at the deformed configuration. -/
theorem differential_power_flux_stationary_iff
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (coupling reference : Real) (degree : Nat) (fields : IndependentFields period hPeriod)
    (mu : Measure (Throat period hPeriod)) [IsFiniteMeasure mu] :
    (∀ direction : SmoothThroatField period hPeriod LLFieldFiber,
      HasDerivAt (fun t : Real => globalDifferentialLLPowerAction period hPeriod frame
        coupling reference degree (differentialLLFluxCurve period hPeriod fields direction t) mu) 0 0) ↔
      SatisfiesWeakDifferentialLLEquation period hPeriod frame fields mu := by
  constructor
  · intro h direction
    exact (differential_power_flux_hasDerivAt period hPeriod frame coupling reference degree
      fields direction mu).unique (h direction)
  · intro h direction
    simpa only [h direction] using differential_power_flux_hasDerivAt period hPeriod frame
      coupling reference degree fields direction mu

end
end P0EFTJanusT08DifferentialLLPotentialVariation4D
end JanusFormal
