import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatSphereMellinFinitePartNormalization4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D

/-!
# Reduced-sphere Mellin integrability in the convergence half-plane

The reduced product-throat sphere heat trace is Mellin integrable for
`1 < re s`.  The proof uses the subtracted short-time packet and the explicit
three-term counterterm on `(0,1]`, then the exponential spectral estimate on
`(1,∞)`.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPProductThroatSphereMellinHalfPlaneIntegrability4D

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusMonopoleHeatAsymptoticMatch
open P0EFTJanusProgramPLongTimeExponentialDominatingFunction4D
open P0EFTJanusProgramPProductThroatSphereShortTimeFinitePart4D
open P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D
open P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D

private theorem reducedSphereMellinRemainder_integrableOn_Ioc
    (data : ProductThroatSpectralData) (spectral : Complex)
    (hSpectral : 1 < spectral.re) :
    IntegrableOn
      (fun time : Real =>
        (time : Complex) ^ spectral *
          (((positiveTimeTraceExtension
                (dimensionlessReducedSphereHeatTrace data) time -
              reducedSphereCounterterm data time) / time : Real) : Complex))
      (Set.Ioc (0 : Real) 1) := by
  have hRemainder : IntegrableOn
      (fun time : Real =>
        (((positiveTimeTraceExtension
              (dimensionlessReducedSphereHeatTrace data) time -
            reducedSphereCounterterm data time) / time : Real) : Complex))
      (Set.Ioc (0 : Real) 1) :=
    (positiveTimeReducedSphere_shortTimeIntegrable data).ofReal
  refine hRemainder.bdd_mul (c := 1)
    (Complex.continuous_ofReal_cpow_const (by linarith)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with time hTime
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hTime.1]
  exact Real.rpow_le_one hTime.1.le hTime.2 (by linarith)

private theorem reducedSphereMellinCounterterm_integrableOn_Ioc
    (data : ProductThroatSpectralData) (spectral : Complex)
    (hSpectral : 1 < spectral.re) :
    IntegrableOn
      (fun time : Real =>
        (time : Complex) ^ (spectral - 1) *
          (reducedSphereCounterterm data time : Complex))
      (Set.Ioc (0 : Real) 1) := by
  have hInversePower : IntegrableOn
      (fun time : Real => (time : Complex) ^ (spectral - 2))
      (Set.Ioc (0 : Real) 1) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo,
      intervalIntegral.integrableOn_Ioo_cpow_iff
        (by norm_num : (0 : Real) < 1)]
    norm_num [Complex.sub_re]
    linarith
  have hConstantPower : IntegrableOn
      (fun time : Real => (time : Complex) ^ (spectral - 1))
      (Set.Ioc (0 : Real) 1) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo,
      intervalIntegral.integrableOn_Ioo_cpow_iff
        (by norm_num : (0 : Real) < 1)]
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hLinearPower : IntegrableOn
      (fun time : Real => (time : Complex) ^ spectral)
      (Set.Ioc (0 : Real) 1) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo,
      intervalIntegral.integrableOn_Ioo_cpow_iff
        (by norm_num : (0 : Real) < 1)]
    linarith
  have hSum : IntegrableOn
      (fun time : Real =>
        (2 : Complex) * (time : Complex) ^ (spectral - 2) +
          ((-(1 / 3 : Real) - (monopoleAbsCharge data : Real) : Real) : Complex) *
            (time : Complex) ^ (spectral - 1) +
          (((5 * (monopoleAbsCharge data : Real) ^ 2 - 1) / 30 : Real) : Complex) *
            (time : Complex) ^ spectral)
      (Set.Ioc (0 : Real) 1) :=
    ((hInversePower.const_mul 2).add
      (hConstantPower.const_mul
        ((-(1 / 3 : Real) - (monopoleAbsCharge data : Real) : Real) : Complex))).add
      (hLinearPower.const_mul
        (((5 * (monopoleAbsCharge data : Real) ^ 2 - 1) / 30 : Real) : Complex))
  refine hSum.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with time hTime
  have hTimeNe : (time : Complex) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hTime.1.ne'
  rw [show spectral - 2 = (spectral - 1) - 1 by ring,
    Complex.cpow_sub _ _ hTimeNe, Complex.cpow_one,
    show spectral = (spectral - 1) + 1 by ring,
    Complex.cpow_add _ _ hTimeNe, Complex.cpow_one]
  unfold reducedSphereCounterterm predictedSphereHeatExpansion
  push_cast
  field_simp
  ring_nf

theorem reducedSphereMellinKernel_integrableOn_Ioc
    (data : ProductThroatSpectralData) (spectral : Complex)
    (hSpectral : 1 < spectral.re) :
    IntegrableOn
      (relativeHeatMellinKernel
        (dimensionlessReducedSphereHeatTrace data) spectral)
      (Set.Ioc (0 : Real) 1) := by
  have hSum :=
    (reducedSphereMellinRemainder_integrableOn_Ioc data spectral hSpectral).add
      (reducedSphereMellinCounterterm_integrableOn_Ioc data spectral hSpectral)
  refine hSum.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with time hTime
  unfold relativeHeatMellinKernel
  change
    (time : Complex) ^ spectral *
          (((positiveTimeTraceExtension
                (dimensionlessReducedSphereHeatTrace data) time -
              reducedSphereCounterterm data time) / time : Real) : Complex) +
        (time : Complex) ^ (spectral - 1) *
          (reducedSphereCounterterm data time : Complex) =
      (time : Complex) ^ (spectral - 1) *
        (positiveTimeTraceExtension
          (dimensionlessReducedSphereHeatTrace data) time : Complex)
  have hTimeNe : (time : Complex) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hTime.1.ne'
  have hPower :
      (time : Complex) ^ (spectral - 1) =
        (time : Complex) ^ spectral / (time : Complex) := by
    rw [Complex.cpow_sub _ _ hTimeNe, Complex.cpow_one]
  rw [hPower]
  push_cast
  field_simp [hTimeNe]
  ring_nf

private theorem reducedSphereMellinLongMajorant_integrable
    (data : ProductThroatSpectralData) (spectral : Complex)
    (hSpectral : 1 < spectral.re) :
    IntegrableOn
      (fun time : Real =>
        reducedSphereLongTimeScale data *
          (time ^ spectral.re * Real.exp (-((1 : Real) / 2) * time)))
      (Set.Ioi (1 : Real)) := by
  have hBase : IntegrableOn
      (fun time : Real =>
        time ^ spectral.re * Real.exp (-((1 : Real) / 2) * time))
      (Set.Ioi (0 : Real)) := by
    simpa only [Real.rpow_one] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (s := spectral.re) (p := (1 : Real)) (b := (1 : Real) / 2)
        (by linarith) (by norm_num) (by norm_num))
  exact IntegrableOn.mono_set
    (hBase.const_mul (reducedSphereLongTimeScale data)) (by
    intro time hTime
    exact (by norm_num : (0 : Real) < 1).trans hTime)

theorem reducedSphereMellinKernel_integrableOn_Ioi_one
    (data : ProductThroatSpectralData) (spectral : Complex)
    (hSpectral : 1 < spectral.re) :
    IntegrableOn
      (relativeHeatMellinKernel
        (dimensionlessReducedSphereHeatTrace data) spectral)
      (Set.Ioi (1 : Real)) := by
  let explicitKernel : Real → Complex := fun time =>
    (time : Complex) ^ (spectral - 1) *
      ((dimensionlessFullSphereHeatTrace data time -
        (monopoleAbsCharge data : Real) : Real) : Complex)
  have hExplicitMeasurable : AEStronglyMeasurable explicitKernel
      (volume.restrict (Set.Ioi (1 : Real))) := by
    apply Measurable.aestronglyMeasurable
    unfold explicitKernel
    exact
      (Complex.continuous_ofReal_cpow_const (by
          simp only [Complex.sub_re, Complex.one_re]
          linarith)).measurable.mul
        (Complex.continuous_ofReal.measurable.comp
          ((measurable_dimensionlessFullSphereHeatTrace data).sub measurable_const))
  have hExplicit : IntegrableOn explicitKernel (Set.Ioi (1 : Real)) := by
    refine (reducedSphereMellinLongMajorant_integrable
      data spectral hSpectral).mono' hExplicitMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with time hTime
    have hTimePos : 0 < time :=
      (by norm_num : (0 : Real) < 1).trans hTime
    have hTraceBound := reducedSphereLogTrace_le_longTimeExponential data hTime
    have hNormIdentity :
        ‖dimensionlessFullSphereHeatTrace data time -
            (monopoleAbsCharge data : Real)‖ =
          time * ‖(dimensionlessFullSphereHeatTrace data time -
            (monopoleAbsCharge data : Real)) / time‖ := by
      simp only [Real.norm_eq_abs]
      rw [abs_div, abs_of_pos hTimePos]
      field_simp
    have hKernelBound :
        ‖explicitKernel time‖ ≤
          reducedSphereLongTimeScale data *
            (time ^ spectral.re * Real.exp (-((1 : Real) / 2) * time)) := by
      unfold explicitKernel
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hTimePos,
        Complex.norm_real, hNormIdentity]
      calc
        time ^ (spectral - 1).re *
              (time * ‖(dimensionlessFullSphereHeatTrace data time -
                (monopoleAbsCharge data : Real)) / time‖) =
            time ^ spectral.re *
              ‖(dimensionlessFullSphereHeatTrace data time -
                (monopoleAbsCharge data : Real)) / time‖ := by
          rw [show spectral.re = (spectral - 1).re + 1 by simp,
            Real.rpow_add hTimePos, Real.rpow_one]
          ring
        _ ≤ time ^ spectral.re *
              longTimeExponentialBound (reducedSphereLongTimeScale data)
                ((1 : Real) / 2) time :=
          mul_le_mul_of_nonneg_left hTraceBound
            (Real.rpow_nonneg hTimePos.le _)
        _ = reducedSphereLongTimeScale data *
              (time ^ spectral.re *
                Real.exp (-((1 : Real) / 2) * time)) := by
          unfold longTimeExponentialBound
          ring
    simpa only [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (reducedSphereLongTimeScale_nonnegative data)
        (mul_nonneg (Real.rpow_nonneg hTimePos.le _)
          (Real.exp_pos _).le))] using hKernelBound
  refine hExplicit.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with time hTime
  have hTimePos : 0 < time :=
    (by norm_num : (0 : Real) < 1).trans hTime
  simp [explicitKernel, relativeHeatMellinKernel,
    positiveTimeTraceExtension, dimensionlessReducedSphereHeatTrace,
    dimensionlessSphereHeatTrace, hTimePos]

/-- The reduced-sphere Mellin kernel converges on the natural half-plane
`1 < re s`. -/
theorem reducedSphereMellinKernel_integrable
    (data : ProductThroatSpectralData) (spectral : Complex)
    (hSpectral : 1 < spectral.re) :
    IntegrableOn
      (relativeHeatMellinKernel
        (dimensionlessReducedSphereHeatTrace data) spectral)
      (Set.Ioi (0 : Real)) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : Real) ≤ 1),
    integrableOn_union]
  exact ⟨reducedSphereMellinKernel_integrableOn_Ioc data spectral hSpectral,
    reducedSphereMellinKernel_integrableOn_Ioi_one data spectral hSpectral⟩

/-- Public short- and long-time Mellin integrability checkpoint. -/
theorem product_throat_sphere_mellin_half_plane_integrability_gate
    (data : ProductThroatSpectralData) (spectral : Complex)
    (hSpectral : 1 < spectral.re) :
    IntegrableOn
        (relativeHeatMellinKernel
          (dimensionlessReducedSphereHeatTrace data) spectral)
        (Set.Ioc (0 : Real) 1) ∧
      IntegrableOn
        (relativeHeatMellinKernel
          (dimensionlessReducedSphereHeatTrace data) spectral)
        (Set.Ioi (1 : Real)) ∧
      IntegrableOn
        (relativeHeatMellinKernel
          (dimensionlessReducedSphereHeatTrace data) spectral)
        (Set.Ioi (0 : Real)) :=
  ⟨reducedSphereMellinKernel_integrableOn_Ioc data spectral hSpectral,
    reducedSphereMellinKernel_integrableOn_Ioi_one data spectral hSpectral,
    reducedSphereMellinKernel_integrable data spectral hSpectral⟩

end
end P0EFTJanusProgramPProductThroatSphereMellinHalfPlaneIntegrability4D
end JanusFormal
