import JanusFormal.Branches.FundamentalGeometryD7SpectralTheory.Gates.P0EFTJanusMonopoleHeatAsymptoticMatch
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPLongTimeExponentialDominatingFunction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D

/-!
# Product-throat sphere short-time finite part

The proved order-four Euler--Maclaurin estimate makes the sphere heat trace,
after subtraction of its three local heat coefficients, logarithmically
integrable at zero.  This discharges the short-time integrability field used
by the relative finite-part determinant.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPProductThroatSphereShortTimeFinitePart4D

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusMonopoleHeatAsymptoticMatch
open P0EFTJanusMonopoleSphereHeatTrace
open P0EFTJanusProgramPLongTimeExponentialDominatingFunction4D
open P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D

/-- The positive-time dimensionless sphere heat trace. -/
def dimensionlessSphereHeatTrace
    (data : ProductThroatSpectralData) (time : HeatTime) : Real :=
  dimensionlessFullSphereHeatTrace data time.1

/-- Remove the monopole zero-mode multiplicity before the long-time heat
integral. -/
def dimensionlessReducedSphereHeatTrace
    (data : ProductThroatSpectralData) (time : HeatTime) : Real :=
  dimensionlessSphereHeatTrace data time -
    (monopoleAbsCharge data : Real)

/-- The matching local subtraction for the reduced sphere trace. -/
def reducedSphereCounterterm
    (data : ProductThroatSpectralData) (time : Real) : Real :=
  predictedSphereHeatExpansion (monopoleAbsCharge data : Real) time -
    (monopoleAbsCharge data : Real)

theorem measurable_dimensionlessFullSphereHeatTrace
    (data : ProductThroatSpectralData) :
    Measurable (dimensionlessFullSphereHeatTrace data) := by
  unfold dimensionlessFullSphereHeatTrace sphereHeatTrace sphereHeatTerm
  fun_prop

/-- A fixed positive-time trace controlling the reduced sphere tail. -/
def reducedSphereLongTimeScale
    (data : ProductThroatSpectralData) : Real :=
  2 * sphereHeatTrace data (data.sphereRadius ^ 2 / 2)

theorem sphereHeatTrace_nonnegative
    (data : ProductThroatSpectralData) (time : Real) :
    0 ≤ sphereHeatTrace data time := by
  unfold sphereHeatTrace
  exact tsum_nonneg (sphere_heat_term_nonnegative data time)

theorem reducedSphereLongTimeScale_nonnegative
    (data : ProductThroatSpectralData) :
    0 ≤ reducedSphereLongTimeScale data := by
  exact mul_nonneg (by norm_num) (sphereHeatTrace_nonnegative data _)

theorem sphereHeatTerm_le_longTimeExponential
    (data : ProductThroatSpectralData) {time : Real} (hTime : 1 ≤ time)
    (level : ℕ) :
    sphereHeatTerm data (time * data.sphereRadius ^ 2) level ≤
      Real.exp (-((1 : Real) / 2) * time) *
        sphereHeatTerm data (data.sphereRadius ^ 2 / 2) level := by
  have hRadius : 0 < data.sphereRadius ^ 2 :=
    sq_pos_of_pos data.sphereRadiusPositive
  have hEigen := sphere_eigenvalue_linear_lower_bound data level
  have hScaledEigen :
      ((level + 1 : ℕ) : Real) ≤
        data.sphereRadius ^ 2 * sphereEigenvalueSquared data level := by
    have := (div_le_iff₀ hRadius).mp hEigen
    nlinarith
  have hOneEigen :
      1 ≤ data.sphereRadius ^ 2 * sphereEigenvalueSquared data level := by
    exact (by norm_num : (1 : Real) ≤ ((level + 1 : ℕ) : Real)).trans
      hScaledEigen
  have hProduct :
      time / 2 +
          (data.sphereRadius ^ 2 * sphereEigenvalueSquared data level) / 2 ≤
        time *
          (data.sphereRadius ^ 2 * sphereEigenvalueSquared data level) := by
    have hA := sub_nonneg.mpr hTime
    have hB := sub_nonneg.mpr hOneEigen
    nlinarith [mul_nonneg hA hB]
  unfold sphereHeatTerm
  calc
    (sphereMultiplicity data level : Real) *
        Real.exp (-(time * data.sphereRadius ^ 2) *
          sphereEigenvalueSquared data level) ≤
      (sphereMultiplicity data level : Real) *
        Real.exp (-((1 : Real) / 2) * time -
          (data.sphereRadius ^ 2 / 2) *
            sphereEigenvalueSquared data level) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      nlinarith
    _ = Real.exp (-((1 : Real) / 2) * time) *
        ((sphereMultiplicity data level : Real) *
          Real.exp (-(data.sphereRadius ^ 2 / 2) *
            sphereEigenvalueSquared data level)) := by
      rw [show -((1 : Real) / 2) * time -
          (data.sphereRadius ^ 2 / 2) *
            sphereEigenvalueSquared data level =
          -((1 : Real) / 2) * time +
            (-(data.sphereRadius ^ 2 / 2) *
              sphereEigenvalueSquared data level) by ring,
        Real.exp_add]
      ring

theorem sphereHeatTrace_le_longTimeExponential
    (data : ProductThroatSpectralData) {time : Real} (hTime : 1 ≤ time) :
    sphereHeatTrace data (time * data.sphereRadius ^ 2) ≤
      Real.exp (-((1 : Real) / 2) * time) *
        sphereHeatTrace data (data.sphereRadius ^ 2 / 2) := by
  have hTimePos : 0 < time := lt_of_lt_of_le (by norm_num) hTime
  have hRadius : 0 < data.sphereRadius ^ 2 :=
    sq_pos_of_pos data.sphereRadiusPositive
  unfold sphereHeatTrace
  rw [← tsum_mul_left]
  exact Summable.tsum_le_tsum
    (sphereHeatTerm_le_longTimeExponential data hTime)
    (sphere_heat_trace_summable data _ (mul_pos hTimePos hRadius))
    ((sphere_heat_trace_summable data _ (div_pos hRadius (by norm_num))).mul_left _)

theorem dimensionlessReducedSphereHeatTrace_eq
    (data : ProductThroatSpectralData) (time : HeatTime) :
    dimensionlessReducedSphereHeatTrace data time =
      2 * sphereHeatTrace data (time.1 * data.sphereRadius ^ 2) := by
  unfold dimensionlessReducedSphereHeatTrace dimensionlessSphereHeatTrace
    dimensionlessFullSphereHeatTrace
  ring

theorem reducedSphereLogTrace_le_longTimeExponential
    (data : ProductThroatSpectralData) {time : Real} (hTime : 1 < time) :
    ‖(dimensionlessFullSphereHeatTrace data time -
        (monopoleAbsCharge data : Real)) / time‖ ≤
      longTimeExponentialBound (reducedSphereLongTimeScale data)
        ((1 : Real) / 2) time := by
  have hTimeLe : 1 ≤ time := hTime.le
  have hTimePos : 0 < time := lt_trans (by norm_num) hTime
  have hTraceNonnegative :
      0 ≤ sphereHeatTrace data (time * data.sphereRadius ^ 2) :=
    sphereHeatTrace_nonnegative data _
  have hNumerator :
      dimensionlessFullSphereHeatTrace data time -
          (monopoleAbsCharge data : Real) =
        2 * sphereHeatTrace data (time * data.sphereRadius ^ 2) := by
    unfold dimensionlessFullSphereHeatTrace
    ring
  rw [hNumerator, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (mul_nonneg (by norm_num) hTraceNonnegative)
      hTimePos.le)]
  calc
    2 * sphereHeatTrace data (time * data.sphereRadius ^ 2) / time ≤
        2 * sphereHeatTrace data (time * data.sphereRadius ^ 2) :=
      div_le_self (mul_nonneg (by norm_num) hTraceNonnegative) hTimeLe
    _ ≤ 2 * (Real.exp (-((1 : Real) / 2) * time) *
        sphereHeatTrace data (data.sphereRadius ^ 2 / 2)) :=
      mul_le_mul_of_nonneg_left
        (sphereHeatTrace_le_longTimeExponential data hTimeLe) (by norm_num)
    _ = longTimeExponentialBound (reducedSphereLongTimeScale data)
        ((1 : Real) / 2) time := by
      unfold longTimeExponentialBound reducedSphereLongTimeScale
      ring

theorem reducedSphereLogTrace_integrableOn
    (data : ProductThroatSpectralData) :
    IntegrableOn
      (fun time =>
        (dimensionlessFullSphereHeatTrace data time -
          (monopoleAbsCharge data : Real)) / time)
      (Set.Ioi (1 : Real)) := by
  refine (integrableOn_longTimeExponentialBound
    (reducedSphereLongTimeScale data) (by norm_num : (0 : Real) < 1 / 2)
      1).mono' ?_ ?_
  · exact (((measurable_dimensionlessFullSphereHeatTrace data).sub
      measurable_const).div measurable_id).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with time hTime
    exact reducedSphereLogTrace_le_longTimeExponential data hTime

/-- Continuous elementary envelope for the logarithmically weighted
Euler--Maclaurin remainder and its polynomial tail. -/
def sphereShortTimeMajorant
    (data : ProductThroatSpectralData) (time : Real) : Real :=
  2 * Real.exp (time * (monopoleAbsCharge data : Real) ^ 2 / 4) *
      Real.sqrt time * emFifthProfileL1 +
    |(monopoleAbsCharge data : Real) ^ 2 * time / 30 -
      (monopoleAbsCharge data : Real) ^ 4 * time ^ 2 / 360|

theorem sphereShortTimeMajorant_integrableOn
    (data : ProductThroatSpectralData) :
    IntegrableOn (sphereShortTimeMajorant data) (Set.Ioc (0 : Real) 1) := by
  apply IntegrableOn.mono_set
    ((show Continuous (sphereShortTimeMajorant data) by
      unfold sphereShortTimeMajorant
      fun_prop).integrableOn_Icc)
  exact Set.Ioc_subset_Icc_self

theorem sphereShortTimeMajorant_bound
    (data : ProductThroatSpectralData) {time : Real}
    (hTime : time ∈ Set.Ioc (0 : Real) 1) :
    ‖(dimensionlessFullSphereHeatTrace data time -
        predictedSphereHeatExpansion (monopoleAbsCharge data : Real) time) /
      time‖ ≤ sphereShortTimeMajorant data time := by
  have hTimePos : 0 < time := hTime.1
  have hTimeNe : time ≠ 0 := ne_of_gt hTimePos
  let q : Real := monopoleAbsCharge data
  have hEuler := dimensionless_trace_euler_maclaurin_bound data time hTimePos
  have hWeightedEuler :
      |(dimensionlessFullSphereHeatTrace data time -
          eulerMaclaurinApproximation q time) / time| ≤
        2 * Real.exp (time * q ^ 2 / 4) * Real.sqrt time *
          emFifthProfileL1 := by
    rw [abs_div, abs_of_pos hTimePos]
    calc
      |dimensionlessFullSphereHeatTrace data time -
          eulerMaclaurinApproximation q time| / time ≤
          (2 * (Real.exp (time * q ^ 2 / 4) * time *
            Real.sqrt time * emFifthProfileL1)) / time :=
        (div_le_div_iff_of_pos_right hTimePos).2 (by simpa [q] using hEuler)
      _ = 2 * Real.exp (time * q ^ 2 / 4) * Real.sqrt time *
          emFifthProfileL1 := by field_simp [hTimeNe]
  have hDecomposition :
      (dimensionlessFullSphereHeatTrace data time -
          predictedSphereHeatExpansion q time) / time =
        (dimensionlessFullSphereHeatTrace data time -
          eulerMaclaurinApproximation q time) / time +
        (q ^ 2 * time / 30 - q ^ 4 * time ^ 2 / 360) := by
    rw [euler_maclaurin_approximation_expands]
    field_simp [hTimeNe]
    ring
  rw [Real.norm_eq_abs, hDecomposition]
  refine (abs_add_le _ _).trans ?_
  simpa [sphereShortTimeMajorant, q] using
    add_le_add_right hWeightedEuler
      |q ^ 2 * time / 30 - q ^ 4 * time ^ 2 / 360|

/-- The locally subtracted sphere trace is integrable against `dt / t` at
zero. -/
theorem sphere_shortTimeIntegrable
    (data : ProductThroatSpectralData) :
    IntegrableOn
      (fun time =>
        (dimensionlessFullSphereHeatTrace data time -
          predictedSphereHeatExpansion
            (monopoleAbsCharge data : Real) time) / time)
      (Set.Ioc (0 : Real) 1) := by
  refine (sphereShortTimeMajorant_integrableOn data).mono' ?_ ?_
  · exact (((measurable_dimensionlessFullSphereHeatTrace data).sub
      (by unfold predictedSphereHeatExpansion; fun_prop)).div
        measurable_id).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with time hTime
    exact sphereShortTimeMajorant_bound data hTime

/-- The same result in the exact positive-time-extension form required by
`RelativeHeatFinitePartData.shortTimeIntegrable`. -/
theorem positiveTimeSphere_shortTimeIntegrable
    (data : ProductThroatSpectralData) :
    IntegrableOn
      (fun time =>
        (positiveTimeTraceExtension (dimensionlessSphereHeatTrace data) time -
          predictedSphereHeatExpansion
            (monopoleAbsCharge data : Real) time) / time)
      (Set.Ioc (0 : Real) 1) := by
  refine (sphere_shortTimeIntegrable data).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with time hTime
  simp [dimensionlessSphereHeatTrace, hTime.1]

/-- Zero-mode reduction leaves the renormalized short-time remainder
unchanged. -/
theorem positiveTimeReducedSphere_shortTimeIntegrable
    (data : ProductThroatSpectralData) :
    IntegrableOn
      (fun time =>
        (positiveTimeTraceExtension
            (dimensionlessReducedSphereHeatTrace data) time -
          reducedSphereCounterterm data time) / time)
      (Set.Ioc (0 : Real) 1) := by
  refine (positiveTimeSphere_shortTimeIntegrable data).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with time hTime
  simp [dimensionlessReducedSphereHeatTrace, dimensionlessSphereHeatTrace,
    reducedSphereCounterterm, hTime.1]

/-- The zero-mode-reduced sphere trace is logarithmically integrable at
infinity. -/
theorem positiveTimeReducedSphere_longTimeIntegrable
    (data : ProductThroatSpectralData) :
    IntegrableOn
      (fun time =>
        positiveTimeTraceExtension
          (dimensionlessReducedSphereHeatTrace data) time / time)
      (Set.Ioi (1 : Real)) := by
  refine (reducedSphereLogTrace_integrableOn data).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with time hTime
  simp [dimensionlessReducedSphereHeatTrace, dimensionlessSphereHeatTrace,
    (by norm_num : (0 : Real) < 1).trans hTime]

/-- Hadamard finite part of the explicitly integrated reduced local
counterterm on `(0,1]`. -/
def reducedSphereCountertermFinitePart
    (data : ProductThroatSpectralData) : Real :=
  -2 + ((5 * (monopoleAbsCharge data : Real) ^ 2 - 1) / 30)

/-- Build the reduced sphere packet from any alternate long-time proof. -/
def reducedSphereFinitePartDataOfLongTime
    (data : ProductThroatSpectralData)
    (countertermFinitePart : Real)
    (longTimeIntegrable : IntegrableOn
      (fun time =>
        positiveTimeTraceExtension
          (dimensionlessReducedSphereHeatTrace data) time / time)
      (Set.Ioi (1 : Real))) :
    RelativeHeatFinitePartData (dimensionlessReducedSphereHeatTrace data) where
  counterterm := reducedSphereCounterterm data
  countertermFinitePart := countertermFinitePart
  shortTimeIntegrable := positiveTimeReducedSphere_shortTimeIntegrable data
  longTimeIntegrable := longTimeIntegrable

/-- Fully spectral finite-part data for the reduced product-throat sphere
trace. -/
def reducedSphereFinitePartData
    (data : ProductThroatSpectralData) :
    RelativeHeatFinitePartData (dimensionlessReducedSphereHeatTrace data) :=
  reducedSphereFinitePartDataOfLongTime data
    (reducedSphereCountertermFinitePart data)
    (positiveTimeReducedSphere_longTimeIntegrable data)

theorem reducedSphereFinitePartDeterminant_pos
    (data : ProductThroatSpectralData) :
    0 < relativeHeatFinitePartDeterminant
      (reducedSphereFinitePartData data) :=
  relativeHeatFinitePartDeterminant_pos _

/-- Public finite-part checkpoint: both analytic ends and positivity of the
renormalized determinant are now unconditional for the reduced sphere trace. -/
theorem product_throat_sphere_finite_part_gate
    (data : ProductThroatSpectralData) :
    IntegrableOn
        (fun time =>
          (positiveTimeTraceExtension
              (dimensionlessReducedSphereHeatTrace data) time -
            reducedSphereCounterterm data time) / time)
        (Set.Ioc (0 : Real) 1) ∧
      IntegrableOn
        (fun time =>
          positiveTimeTraceExtension
            (dimensionlessReducedSphereHeatTrace data) time / time)
        (Set.Ioi (1 : Real)) ∧
      0 < relativeHeatFinitePartDeterminant
        (reducedSphereFinitePartData data) :=
  ⟨positiveTimeReducedSphere_shortTimeIntegrable data,
    positiveTimeReducedSphere_longTimeIntegrable data,
    reducedSphereFinitePartDeterminant_pos data⟩

end
end P0EFTJanusProgramPProductThroatSphereShortTimeFinitePart4D
end JanusFormal
