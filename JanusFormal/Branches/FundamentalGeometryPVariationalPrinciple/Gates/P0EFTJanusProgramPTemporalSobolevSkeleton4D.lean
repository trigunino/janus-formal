import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSobolevGalerkinHelmholtz4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusInfiniteTemporalFourierSobolevBridge4D

/-!
# Temporal geometric skeleton of the Program-P Sobolev chart

The common real coefficient Hilbert space is embedded isometrically into the
existing complex temporal `H¹` coefficients by reindexing `ℕ` with `ℤ` and
taking the real coefficient slice.  Fourier synthesis then realizes every
one of the nine common coordinates as an actual `L²` field on the effective
mapping-torus quotient, together with its temporal spectral derivative.

Finite-mode cutoffs converge in both genuine quotient `L²` targets.  This is
the maximal geometric realization currently supplied by the established
infinite Fourier theory: it is a spatially constant scalar temporal skeleton,
not an identification of the tensor, spinor, gauge, or ghost bundles.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPTemporalSobolevSkeleton4D

set_option autoImplicit false

noncomputable section

open Filter Topology
open scoped BigOperators ENNReal
open P0EFTJanusCircleUnboundedDiracDomain
open P0EFTJanusMappingTorusFiniteTemporalFourierGaugeGhostCohomology4D
open P0EFTJanusMappingTorusInfiniteTemporalFourierSobolevBridge4D
open P0EFTJanusProgramPSobolevGalerkinHelmholtz4D
open P0EFTJanusShiftedSobolevMappingTorusFiniteTemporalFourierBridge4D

variable (period : ℝ) [hPeriodPos : Fact (0 < period)]

/-- Isometric real slice of the established complex temporal `H¹`
coefficient space. -/
def realModesToTemporalH1
    (state : ProgramPModeHilbert) :
    TemporalH1CoefficientHilbert period := by
  refine ⟨fun mode => (state (Equiv.intEquivNat mode) : ℂ), ?_⟩
  change Memℓp
    (fun mode : ℤ => (state (Equiv.intEquivNat mode) : ℂ)) 2
  rw [memℓp_gen_iff (by norm_num)]
  have hSummable :=
    (lp.memℓp state).summable (by norm_num)
  simpa [Function.comp_def, Complex.norm_real] using
    (Equiv.intEquivNat.summable_iff.mpr hSummable)

omit hPeriodPos in
@[simp]
theorem realModesToTemporalH1_apply
    (state : ProgramPModeHilbert) (mode : ℤ) :
    realModesToTemporalH1 period state mode =
      (state (Equiv.intEquivNat mode) : ℂ) :=
  rfl

/-- The real slice is linear over the real action field. -/
def realModesToTemporalH1LinearMap :
    ProgramPModeHilbert →ₗ[ℝ] TemporalH1CoefficientHilbert period where
  toFun := realModesToTemporalH1 period
  map_add' := by
    intro first second
    ext mode
    simp
  map_smul' := by
    intro scalar state
    ext mode
    simp

omit hPeriodPos in
theorem realModesToTemporalH1_norm
    (state : ProgramPModeHilbert) :
    ‖realModesToTemporalH1 period state‖ = ‖state‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num),
    lp.norm_eq_tsum_rpow (by norm_num)]
  congr 1
  simpa only [realModesToTemporalH1_apply, Complex.norm_real] using
    Equiv.intEquivNat.tsum_eq
      (fun mode : ℕ => ‖state mode‖ ^ ENNReal.toReal 2)

/-- Canonical linear isometry from the Program-P mode chart into the genuine
temporal Sobolev coefficient completion. -/
def realModesToTemporalH1LinearIsometry :
    ProgramPModeHilbert →ₗᵢ[ℝ] TemporalH1CoefficientHilbert period :=
  LinearIsometry.mk (realModesToTemporalH1LinearMap period)
    (realModesToTemporalH1_norm period)

/-- The field and derivative multipliers partition the weighted `H¹`
energy exactly at every temporal mode. -/
theorem temporalH1Scale_energy (mode : ℤ) :
    ‖temporalH1FieldScale period mode‖ ^ 2 +
        ‖temporalH1DerivativeScale period mode‖ ^ 2 = 1 := by
  rw [temporalH1DerivativeScale, norm_mul, temporalH1FieldScale,
    norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  have hWeight : 0 < temporalH1Weight period mode :=
    temporalH1Weight_pos period mode
  have hSqrt : Real.sqrt (temporalH1Weight period mode) ≠ 0 :=
    (Real.sqrt_pos.2 hWeight).ne'
  field_simp
  rw [Real.sq_sqrt hWeight.le]
  unfold temporalH1Weight
  ring

/-- Pointwise Parseval energy identity for the two decoded coefficient
operators. -/
theorem temporalH1Coefficient_energy
    (state : TemporalH1CoefficientHilbert period) (mode : ℤ) :
    ‖temporalH1FieldCoefficientOperator period state mode‖ ^ 2 +
        ‖temporalH1DerivativeCoefficientOperator period state mode‖ ^ 2 =
      ‖state mode‖ ^ 2 := by
  simp only [temporalH1DerivativeCoefficientOperator_apply,
    temporalH1FieldCoefficientOperator_apply, norm_mul]
  calc
    (‖temporalH1FieldScale period mode‖ * ‖state mode‖) ^ 2 +
        (‖temporalFourierDerivativeMultiplier period mode‖ *
          (‖temporalH1FieldScale period mode‖ * ‖state mode‖)) ^ 2 =
      (‖temporalH1FieldScale period mode‖ ^ 2 +
        ‖temporalH1DerivativeScale period mode‖ ^ 2) *
          ‖state mode‖ ^ 2 := by
            rw [temporalH1DerivativeScale, norm_mul]
            ring
    _ = ‖state mode‖ ^ 2 := by
      rw [temporalH1Scale_energy period mode, one_mul]

/-- Global coefficient-space `H¹` energy identity. -/
theorem temporalH1CoefficientOperators_energy
    (state : TemporalH1CoefficientHilbert period) :
    ‖temporalH1FieldCoefficientOperator period state‖ ^ 2 +
        ‖temporalH1DerivativeCoefficientOperator period state‖ ^ 2 =
      ‖state‖ ^ 2 := by
  have hField :=
    (lp.memℓp (temporalH1FieldCoefficientOperator period state)).summable
      (by norm_num)
  have hDerivative :=
    (lp.memℓp (temporalH1DerivativeCoefficientOperator period state)).summable
      (by norm_num)
  have hFieldTwo : Summable
      (fun mode : ℤ =>
        ‖temporalH1FieldCoefficientOperator period state mode‖ ^ 2) := by
    simpa using hField
  have hDerivativeTwo : Summable
      (fun mode : ℤ =>
        ‖temporalH1DerivativeCoefficientOperator period state mode‖ ^ 2) := by
    simpa using hDerivative
  rw [show ‖temporalH1FieldCoefficientOperator period state‖ ^ 2 =
      ∑' mode : ℤ,
        ‖temporalH1FieldCoefficientOperator period state mode‖ ^ 2 by
      simpa using lp.norm_rpow_eq_tsum (p := (2 : ENNReal))
        (by norm_num)
        (temporalH1FieldCoefficientOperator period state)]
  rw [show ‖temporalH1DerivativeCoefficientOperator period state‖ ^ 2 =
      ∑' mode : ℤ,
        ‖temporalH1DerivativeCoefficientOperator period state mode‖ ^ 2 by
      simpa using lp.norm_rpow_eq_tsum (p := (2 : ENNReal))
        (by norm_num)
        (temporalH1DerivativeCoefficientOperator period state)]
  rw [show ‖state‖ ^ 2 = ∑' mode : ℤ, ‖state mode‖ ^ 2 by
      simpa using lp.norm_rpow_eq_tsum (p := (2 : ENNReal))
        (by norm_num) state]
  rw [← hFieldTwo.tsum_add hDerivativeTwo]
  apply tsum_congr
  intro mode
  exact temporalH1Coefficient_energy period state mode

omit hPeriodPos in
/-- Exact integer-mode support selected by a Program-P finite cutoff. -/
@[simp]
theorem realModesToTemporalH1_finiteModeProjection_apply
    (cutoff : ℕ) (state : ProgramPModeHilbert) (mode : ℤ) :
    realModesToTemporalH1 period (finiteModeProjection cutoff state) mode =
      if Equiv.intEquivNat mode < cutoff
      then (state (Equiv.intEquivNat mode) : ℂ)
      else 0 := by
  by_cases hMode : Equiv.intEquivNat mode < cutoff <;>
    simp [finiteModeProjection_apply_coordinate, hMode]

/-- Actual scalar quotient `L²` realization of one common coefficient
sector. -/
def temporalScalarFieldL2 :
    ProgramPModeHilbert →L[ℝ] CanonicalTemporalQuotientL2 period :=
  ((temporalH1FieldL2 period).restrictScalars ℝ).comp
    (realModesToTemporalH1LinearIsometry period).toContinuousLinearMap

/-- Actual temporal spectral derivative in the same quotient `L²` space. -/
def temporalScalarDerivativeL2 :
    ProgramPModeHilbert →L[ℝ] CanonicalTemporalQuotientL2 period :=
  ((temporalH1DerivativeL2 period).restrictScalars ℝ).comp
    (realModesToTemporalH1LinearIsometry period).toContinuousLinearMap

/-- Exact graph-energy identity after genuine Fourier synthesis on the
mapping-torus quotient. -/
theorem temporalH1L2Graph_energy
    (state : TemporalH1CoefficientHilbert period) :
    ‖temporalH1FieldL2 period state‖ ^ 2 +
        ‖temporalH1DerivativeL2 period state‖ ^ 2 =
      ‖state‖ ^ 2 := by
  simpa [temporalH1FieldL2, temporalH1DerivativeL2] using
    temporalH1CoefficientOperators_energy period state

/-- The Program-P real mode chart is isometric to the genuine temporal
`H¹` graph energy on its real coefficient slice. -/
theorem temporalScalarL2Graph_energy
    (state : ProgramPModeHilbert) :
    ‖temporalScalarFieldL2 period state‖ ^ 2 +
        ‖temporalScalarDerivativeL2 period state‖ ^ 2 =
      ‖state‖ ^ 2 := by
  simpa [temporalScalarFieldL2, temporalScalarDerivativeL2,
    realModesToTemporalH1LinearIsometry,
    realModesToTemporalH1LinearMap,
    realModesToTemporalH1_norm] using
      temporalH1L2Graph_energy period
        (realModesToTemporalH1 period state)

theorem temporalScalarFieldL2_injective :
    Function.Injective (temporalScalarFieldL2 period) :=
  (temporalH1FieldL2_injective period).comp
    (realModesToTemporalH1LinearIsometry period).injective

/-- The synthesized field is the convergent infinite Fourier series in the
actual quotient `L²` norm. -/
theorem temporalScalarFieldL2_hasSum
    (state : ProgramPModeHilbert) :
    HasSum
      (fun mode : ℤ =>
        (temporalH1FieldCoefficientOperator period
          (realModesToTemporalH1 period state) mode) •
            mappingTorusTemporalModeL2 period mode)
      (temporalScalarFieldL2 period state) := by
  simpa [temporalScalarFieldL2,
    realModesToTemporalH1LinearIsometry,
    realModesToTemporalH1LinearMap] using
    temporalH1FieldL2_hasSum period
      (realModesToTemporalH1 period state)

/-- The synthesized temporal derivative is independently represented by its
convergent physical-multiplier Fourier series. -/
theorem temporalScalarDerivativeL2_hasSum
    (state : ProgramPModeHilbert) :
    HasSum
      (fun mode : ℤ =>
        (temporalFourierDerivativeMultiplier period mode *
          temporalH1FieldCoefficientOperator period
            (realModesToTemporalH1 period state) mode) •
              mappingTorusTemporalModeL2 period mode)
      (temporalScalarDerivativeL2 period state) := by
  simpa [temporalScalarDerivativeL2,
    realModesToTemporalH1LinearIsometry,
    realModesToTemporalH1LinearMap] using
    temporalH1DerivativeL2_hasSum period
      (realModesToTemporalH1 period state)

/-- Coordinatewise realization of all nine common sectors as temporal scalar
test fields on the actual quotient. -/
def configurationTemporalScalarFields :
    ProgramPSobolevConfiguration →L[ℝ]
      (Fin 9 → CanonicalTemporalQuotientL2 period) :=
  ContinuousLinearMap.piMap fun _ : Fin 9 => temporalScalarFieldL2 period

/-- The nine-field temporal realization retains every common coefficient. -/
theorem configurationTemporalScalarFields_injective :
    Function.Injective (configurationTemporalScalarFields period) := by
  intro first second hEqual
  funext block
  apply temporalScalarFieldL2_injective period
  exact congrFun hEqual block

/-- Coordinatewise realization of all nine temporal spectral derivatives. -/
def configurationTemporalScalarDerivatives :
    ProgramPSobolevConfiguration →L[ℝ]
      (Fin 9 → CanonicalTemporalQuotientL2 period) :=
  ContinuousLinearMap.piMap fun _ : Fin 9 =>
    temporalScalarDerivativeL2 period

/-- The nine temporal scalar test sectors preserve the summed common-chart
energy exactly. -/
theorem configurationTemporalScalarL2Graph_energy
    (configuration : ProgramPSobolevConfiguration) :
    (∑ block : Fin 9,
        (‖configurationTemporalScalarFields period configuration block‖ ^ 2 +
          ‖configurationTemporalScalarDerivatives
            period configuration block‖ ^ 2)) =
      ∑ block : Fin 9, ‖configuration block‖ ^ 2 := by
  apply Finset.sum_congr rfl
  intro block _
  exact temporalScalarL2Graph_energy period (configuration block)

/-- Scalar fields of finite Program-P cutoffs converge in actual quotient
`L²`. -/
theorem temporalScalarFieldL2_cutoff_tendsto
    (state : ProgramPModeHilbert) :
    Tendsto
      (fun cutoff => temporalScalarFieldL2 period
        (finiteModeProjection cutoff state))
      atTop (𝓝 (temporalScalarFieldL2 period state)) := by
  exact Filter.Tendsto.comp
    (temporalScalarFieldL2 period).continuous.continuousAt
    (finiteModeProjection_tendsto state)

/-- Temporal derivatives of finite Program-P cutoffs converge in actual
quotient `L²`. -/
theorem temporalScalarDerivativeL2_cutoff_tendsto
    (state : ProgramPModeHilbert) :
    Tendsto
      (fun cutoff => temporalScalarDerivativeL2 period
        (finiteModeProjection cutoff state))
      atTop (𝓝 (temporalScalarDerivativeL2 period state)) := by
  exact Filter.Tendsto.comp
    (temporalScalarDerivativeL2 period).continuous.continuousAt
    (finiteModeProjection_tendsto state)

/-- All nine finite-cutoff scalar test fields converge simultaneously. -/
theorem configurationTemporalScalarFields_cutoff_tendsto
    (configuration : ProgramPSobolevConfiguration) :
    Tendsto
      (fun cutoff => configurationTemporalScalarFields period
        (configurationFiniteModeProjection cutoff configuration))
      atTop
      (𝓝 (configurationTemporalScalarFields period configuration)) := by
  exact Filter.Tendsto.comp
    (configurationTemporalScalarFields period).continuous.continuousAt
    (configurationFiniteModeProjection_tendsto configuration)

/-- All nine finite-cutoff temporal derivatives converge simultaneously. -/
theorem configurationTemporalScalarDerivatives_cutoff_tendsto
    (configuration : ProgramPSobolevConfiguration) :
    Tendsto
      (fun cutoff => configurationTemporalScalarDerivatives period
        (configurationFiniteModeProjection cutoff configuration))
      atTop
      (𝓝 (configurationTemporalScalarDerivatives period configuration)) := by
  exact Filter.Tendsto.comp
    (configurationTemporalScalarDerivatives period).continuous.continuousAt
    (configurationFiniteModeProjection_tendsto configuration)

end

end P0EFTJanusProgramPTemporalSobolevSkeleton4D
end JanusFormal
