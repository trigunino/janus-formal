import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatSphereMellinCountertermContinuation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatSphereMellinRemainderGerm4D

/-!
# Honest Mellin continuation of the reduced product-throat sphere zeta

The zeta function is the sum of the regular Gamma-normalized remainder and
the explicit Gamma-regularized counterterm.  On `1 < re s` it is proved equal
to the original heat Mellin transform; at zero its derivative is the complete
Gamma-normalized finite part.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPProductThroatSphereMellinZetaContinuation4D

set_option autoImplicit false
noncomputable section

open Filter MeasureTheory Set
open scoped Topology
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusMonopoleHeatAsymptoticMatch
open P0EFTJanusProgramPProductThroatSphereShortTimeFinitePart4D
open P0EFTJanusProgramPProductThroatSphereMellinFinitePartNormalization4D
open P0EFTJanusProgramPProductThroatSphereMellinHalfPlaneIntegrability4D
open P0EFTJanusProgramPProductThroatSphereMellinCountertermContinuation4D
open P0EFTJanusProgramPProductThroatSphereMellinRemainderGerm4D
open P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D
open P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D

/-- The explicit reduced-sphere Mellin zeta continuation. -/
def reducedSphereMellinZeta
    (data : ProductThroatSpectralData) (spectral : Complex) : Complex :=
  reducedSphereMellinRegularRemainderZeta data spectral +
    reducedSphereCountertermMellinZeta data spectral

/-- Its derivative at zero, expressed intrinsically through the normalized
finite-part logarithm. -/
def reducedSphereMellinZetaDerivativeAtZero
    (data : ProductThroatSpectralData) : Complex :=
  ((-relativeHeatFinitePartLogDeterminant
    (reducedSphereMellinFinitePartData data) : Real) : Complex)

private theorem reducedSphereCountertermMellinIntegrand_eq
    (data : ProductThroatSpectralData) (spectral : Complex)
    {time : Real} (hTime : time ∈ Set.Ioc (0 : Real) 1) :
    (time : Complex) ^ (spectral - 1) *
        (reducedSphereCounterterm data time : Complex) =
      (2 : Complex) * (time : Complex) ^ (spectral - 2) +
        (reducedSphereMellinConstantCoefficient data : Complex) *
          (time : Complex) ^ (spectral - 1) +
        (reducedSphereMellinLinearCoefficient data : Complex) *
          (time : Complex) ^ spectral := by
  change
    (time : Complex) ^ (spectral - 1) *
        ((predictedSphereHeatExpansion
            (monopoleAbsCharge data : Real) time -
          (monopoleAbsCharge data : Real) : Real) : Complex) =
      (2 : Complex) * (time : Complex) ^ (spectral - 2) +
        ((-(1 / 3 : Real) - (monopoleAbsCharge data : Real) : Real) : Complex) *
          (time : Complex) ^ (spectral - 1) +
        (((5 * (monopoleAbsCharge data : Real) ^ 2 - 1) / 30 : Real) : Complex) *
          (time : Complex) ^ spectral
  have hTimeNe : (time : Complex) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hTime.1.ne'
  have hInversePower :
      (time : Complex) ^ (spectral - 2) =
        (time : Complex) ^ (spectral - 1) / (time : Complex) := by
    calc
      (time : Complex) ^ (spectral - 2) =
          (time : Complex) ^ ((spectral - 1) - 1) := by
        congr 1
        ring
      _ = (time : Complex) ^ (spectral - 1) /
          (time : Complex) ^ (1 : Complex) :=
        Complex.cpow_sub _ _ hTimeNe
      _ = (time : Complex) ^ (spectral - 1) / (time : Complex) := by
        rw [Complex.cpow_one]
  have hLinearPower :
      (time : Complex) ^ spectral =
        (time : Complex) ^ (spectral - 1) * (time : Complex) := by
    calc
      (time : Complex) ^ spectral =
          (time : Complex) ^ ((spectral - 1) + 1) := by
        congr 1
        ring
      _ = (time : Complex) ^ (spectral - 1) *
          (time : Complex) ^ (1 : Complex) :=
        Complex.cpow_add _ _ hTimeNe
      _ = (time : Complex) ^ (spectral - 1) * (time : Complex) := by
        rw [Complex.cpow_one]
  rw [hInversePower, hLinearPower]
  unfold predictedSphereHeatExpansion
  push_cast
  field_simp [hTimeNe]
  ring

private theorem reducedSphereCountertermMellinIntegrableOn_Ioc
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
          (reducedSphereMellinConstantCoefficient data : Complex) *
            (time : Complex) ^ (spectral - 1) +
          (reducedSphereMellinLinearCoefficient data : Complex) *
            (time : Complex) ^ spectral)
      (Set.Ioc (0 : Real) 1) :=
    ((hInversePower.const_mul 2).add
      (hConstantPower.const_mul
        (reducedSphereMellinConstantCoefficient data : Complex))).add
      (hLinearPower.const_mul
        (reducedSphereMellinLinearCoefficient data : Complex))
  refine hSum.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with time hTime
  exact (reducedSphereCountertermMellinIntegrand_eq
    data spectral hTime).symm

/-- The three explicit counterterm profiles have Mellin transform
`2/(s-1) + a₀/s + a₁/(s+1)` on the convergence half-plane. -/
theorem reducedSphereCountertermMellinIntegral_eq_pole
    (data : ProductThroatSpectralData) (spectral : Complex)
    (hSpectral : 1 < spectral.re) :
    (∫ time in Set.Ioc (0 : Real) 1,
      (time : Complex) ^ (spectral - 1) *
        (reducedSphereCounterterm data time : Complex)) =
      reducedSphereCountertermMellinPole data spectral := by
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
  have hInverseIntegral :
      (∫ time in Set.Ioc (0 : Real) 1,
        (time : Complex) ^ (spectral - 2)) = 1 / (spectral - 1) := by
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : Real) ≤ 1),
      integral_cpow (Or.inl (by
        norm_num [Complex.sub_re]
        linarith))]
    have hNe : spectral - 1 ≠ 0 := by
      intro h
      apply_fun Complex.re at h
      simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at h
      linarith
    simp [show spectral - 2 + 1 = spectral - 1 by ring, hNe]
  have hConstantIntegral :
      (∫ time in Set.Ioc (0 : Real) 1,
        (time : Complex) ^ (spectral - 1)) = 1 / spectral := by
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : Real) ≤ 1),
      integral_cpow (Or.inl (by
        simp only [Complex.sub_re, Complex.one_re]
        linarith))]
    have hNe : spectral ≠ 0 := by
      intro h
      subst spectral
      norm_num at hSpectral
    simp [show spectral - 1 + 1 = spectral by ring, hNe]
  have hLinearIntegral :
      (∫ time in Set.Ioc (0 : Real) 1,
        (time : Complex) ^ spectral) = 1 / (spectral + 1) := by
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : Real) ≤ 1),
      integral_cpow (Or.inl (by linarith))]
    have hNe : spectral + 1 ≠ 0 := by
      intro h
      apply_fun Complex.re at h
      simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at h
      linarith
    simp [hNe]
  have hOuterIntegral :
      (∫ time in Set.Ioc (0 : Real) 1,
        ((2 : Complex) * (time : Complex) ^ (spectral - 2) +
          (reducedSphereMellinConstantCoefficient data : Complex) *
            (time : Complex) ^ (spectral - 1)) +
          (reducedSphereMellinLinearCoefficient data : Complex) *
            (time : Complex) ^ spectral) =
        (∫ time in Set.Ioc (0 : Real) 1,
          (2 : Complex) * (time : Complex) ^ (spectral - 2) +
            (reducedSphereMellinConstantCoefficient data : Complex) *
              (time : Complex) ^ (spectral - 1)) +
        ∫ time in Set.Ioc (0 : Real) 1,
          (reducedSphereMellinLinearCoefficient data : Complex) *
            (time : Complex) ^ spectral := by
    simpa only [Pi.add_apply] using
      integral_add
        ((hInversePower.const_mul 2).add
          (hConstantPower.const_mul
            (reducedSphereMellinConstantCoefficient data : Complex)))
        (hLinearPower.const_mul
          (reducedSphereMellinLinearCoefficient data : Complex))
  have hInnerIntegral :
      (∫ time in Set.Ioc (0 : Real) 1,
        (2 : Complex) * (time : Complex) ^ (spectral - 2) +
          (reducedSphereMellinConstantCoefficient data : Complex) *
            (time : Complex) ^ (spectral - 1)) =
        (∫ time in Set.Ioc (0 : Real) 1,
          (2 : Complex) * (time : Complex) ^ (spectral - 2)) +
        ∫ time in Set.Ioc (0 : Real) 1,
          (reducedSphereMellinConstantCoefficient data : Complex) *
            (time : Complex) ^ (spectral - 1) := by
    simpa only [Pi.add_apply] using
      integral_add (hInversePower.const_mul 2)
        (hConstantPower.const_mul
          (reducedSphereMellinConstantCoefficient data : Complex))
  calc
    (∫ time in Set.Ioc (0 : Real) 1,
      (time : Complex) ^ (spectral - 1) *
        (reducedSphereCounterterm data time : Complex)) =
        ∫ time in Set.Ioc (0 : Real) 1,
          ((2 : Complex) * (time : Complex) ^ (spectral - 2) +
            (reducedSphereMellinConstantCoefficient data : Complex) *
              (time : Complex) ^ (spectral - 1)) +
            (reducedSphereMellinLinearCoefficient data : Complex) *
              (time : Complex) ^ spectral := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with time hTime
      exact reducedSphereCountertermMellinIntegrand_eq data spectral hTime
    _ = (2 : Complex) * (1 / (spectral - 1)) +
          (reducedSphereMellinConstantCoefficient data : Complex) *
            (1 / spectral) +
          (reducedSphereMellinLinearCoefficient data : Complex) *
            (1 / (spectral + 1)) := by
      rw [hOuterIntegral, hInnerIntegral,
        integral_const_mul, integral_const_mul, integral_const_mul,
        hInverseIntegral, hConstantIntegral, hLinearIntegral]
    _ = reducedSphereCountertermMellinPole data spectral := by
      unfold reducedSphereCountertermMellinPole
      ring

private theorem reducedSphereMellinShortRemainder_integrableOn_rightHalfPlane
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

private theorem reducedSphereMellinShortKernel_split
    (data : ProductThroatSpectralData) (spectral : Complex)
    (hSpectral : 1 < spectral.re) :
    (∫ time in Set.Ioc (0 : Real) 1,
      relativeHeatMellinKernel
        (dimensionlessReducedSphereHeatTrace data) spectral time) =
      reducedSphereMellinShortRemainderIntegral data spectral +
        reducedSphereCountertermMellinPole data spectral := by
  have hRemainder :=
    reducedSphereMellinShortRemainder_integrableOn_rightHalfPlane
      data spectral hSpectral
  have hCounterterm :=
    reducedSphereCountertermMellinIntegrableOn_Ioc data spectral hSpectral
  calc
    (∫ time in Set.Ioc (0 : Real) 1,
      relativeHeatMellinKernel
        (dimensionlessReducedSphereHeatTrace data) spectral time) =
        ∫ time in Set.Ioc (0 : Real) 1,
          ((time : Complex) ^ spectral *
              (((positiveTimeTraceExtension
                  (dimensionlessReducedSphereHeatTrace data) time -
                reducedSphereCounterterm data time) / time : Real) : Complex) +
            (time : Complex) ^ (spectral - 1) *
              (reducedSphereCounterterm data time : Complex)) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with time hTime
      unfold relativeHeatMellinKernel
      have hTimeNe : (time : Complex) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr hTime.1.ne'
      rw [show (time : Complex) ^ (spectral - 1) =
          (time : Complex) ^ spectral / (time : Complex) by
        rw [Complex.cpow_sub _ _ hTimeNe, Complex.cpow_one]]
      push_cast
      field_simp [hTimeNe]
      ring_nf
    _ = reducedSphereMellinShortRemainderIntegral data spectral +
          (∫ time in Set.Ioc (0 : Real) 1,
            (time : Complex) ^ (spectral - 1) *
              (reducedSphereCounterterm data time : Complex)) := by
      rw [integral_add hRemainder hCounterterm]
      rfl
    _ = reducedSphereMellinShortRemainderIntegral data spectral +
          reducedSphereCountertermMellinPole data spectral := by
      rw [reducedSphereCountertermMellinIntegral_eq_pole data spectral hSpectral]

private theorem reducedSphereMellinLongKernel_eq_tail
    (data : ProductThroatSpectralData) (spectral : Complex) :
    (∫ time in Set.Ioi (1 : Real),
      relativeHeatMellinKernel
        (dimensionlessReducedSphereHeatTrace data) spectral time) =
      reducedSphereMellinLongTailIntegral data spectral := by
  unfold reducedSphereMellinLongTailIntegral
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with time hTime
  unfold relativeHeatMellinKernel
  have hTimePos : 0 < time := (by norm_num : (0 : Real) < 1).trans hTime
  have hTimeNe : (time : Complex) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hTimePos.ne'
  rw [Complex.cpow_sub _ _ hTimeNe, Complex.cpow_one]
  push_cast
  field_simp [hTimeNe]

/-- Subtracted short part, long tail, and explicit pole reconstruct the
original Mellin integral on `1 < re s`. -/
theorem reducedSphereMellinIntegral_eq_regular_add_pole
    (data : ProductThroatSpectralData) (spectral : Complex)
    (hSpectral : 1 < spectral.re) :
    relativeHeatMellinIntegral
        (dimensionlessReducedSphereHeatTrace data) spectral =
      reducedSphereMellinRegularRemainderIntegral data spectral +
        reducedSphereCountertermMellinPole data spectral := by
  have hFull := reducedSphereMellinKernel_integrable data spectral hSpectral
  have hShort : IntegrableOn
      (relativeHeatMellinKernel
        (dimensionlessReducedSphereHeatTrace data) spectral)
      (Set.Ioc (0 : Real) 1) :=
    hFull.mono_set Set.Ioc_subset_Ioi_self
  have hLong : IntegrableOn
      (relativeHeatMellinKernel
        (dimensionlessReducedSphereHeatTrace data) spectral)
      (Set.Ioi (1 : Real)) :=
    hFull.mono_set (Set.Ioi_subset_Ioi (by norm_num : (0 : Real) ≤ 1))
  unfold relativeHeatMellinIntegral
  rw [← Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : Real) ≤ 1),
    setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi hShort hLong,
    reducedSphereMellinShortKernel_split data spectral hSpectral,
    reducedSphereMellinLongKernel_eq_tail data spectral]
  unfold reducedSphereMellinRegularRemainderIntegral
  ring

/-- The explicit continuation equals the Gamma-normalized heat Mellin
candidate throughout its natural convergence half-plane. -/
theorem reducedSphereMellinZeta_eq_candidate
    (data : ProductThroatSpectralData) (spectral : Complex)
    (hSpectral : 1 < spectral.re) :
    reducedSphereMellinZeta data spectral =
      relativeHeatMellinZetaCandidate
        (dimensionlessReducedSphereHeatTrace data) spectral := by
  have hZero : spectral ≠ 0 := by
    intro h
    subst spectral
    norm_num at hSpectral
  unfold reducedSphereMellinZeta
    reducedSphereMellinRegularRemainderZeta
    relativeHeatMellinZetaCandidate
  rw [reducedSphereCountertermMellinZeta_eq data hZero,
    reducedSphereMellinIntegral_eq_regular_add_pole data spectral hSpectral]
  ring

/-- The derivative of the complete continuation is the complete normalized
finite part. -/
theorem reducedSphereMellinZeta_hasDerivAt_zero
    (data : ProductThroatSpectralData) :
    HasDerivAt (reducedSphereMellinZeta data)
      (reducedSphereMellinZetaDerivativeAtZero data) 0 := by
  have hRaw :=
    (reducedSphereMellinRegularRemainderZeta_hasDerivAt_zero data).add
      (reducedSphereCountertermMellinZeta_hasDerivAt_zero data)
  have hNormalized := hRaw.congr_deriv (show
      ((relativeHeatShortTimeFinitePart
          (reducedSphereMellinFinitePartData data) +
        relativeHeatLongTimeIntegral
          (reducedSphereMellinFinitePartData data) : Real) : Complex) +
        (reducedSphereMellinCountertermFinitePart data : Complex) =
      reducedSphereMellinZetaDerivativeAtZero data by
    unfold reducedSphereMellinZetaDerivativeAtZero
      relativeHeatFinitePartLogDeterminant
    push_cast
    rw [reducedSphereMellinFinitePartData_countertermFinitePart]
    ring)
  rw [hasDerivAt_iff_tendsto_slope]
  refine hNormalized.tendsto_slope.congr' ?_
  filter_upwards with spectral
  rfl

/-- Concrete honest continuation packet for the normalized reduced sphere. -/
def reducedSphereMellinZetaContinuationData
    (data : ProductThroatSpectralData) :
    RelativeHeatMellinZetaContinuationData
      (reducedSphereMellinFinitePartData data) where
  convergenceAbscissa := 1
  zeta := reducedSphereMellinZeta data
  derivativeAtZero := reducedSphereMellinZetaDerivativeAtZero data
  mellin_integrable := fun spectral hSpectral =>
    reducedSphereMellinKernel_integrable data spectral hSpectral
  zeta_eq_mellin := fun spectral hSpectral =>
    reducedSphereMellinZeta_eq_candidate data spectral hSpectral
  hasDerivAt_zero := reducedSphereMellinZeta_hasDerivAt_zero data
  finitePart_realPart := by
    simp [reducedSphereMellinZetaDerivativeAtZero]

@[simp]
theorem reducedSphereMellinZetaContinuationData_derivativeAtZero_im
    (data : ProductThroatSpectralData) :
    (reducedSphereMellinZetaContinuationData data).derivativeAtZero.im = 0 := by
  simp [reducedSphereMellinZetaContinuationData,
    reducedSphereMellinZetaDerivativeAtZero]

/-- Public terminal checkpoint for the explicit sphere continuation. -/
theorem product_throat_sphere_mellin_zeta_continuation_gate
    (data : ProductThroatSpectralData) :
    (∀ spectral : Complex, 1 < spectral.re →
      reducedSphereMellinZeta data spectral =
        relativeHeatMellinZetaCandidate
          (dimensionlessReducedSphereHeatTrace data) spectral) ∧
      HasDerivAt (reducedSphereMellinZeta data)
        (reducedSphereMellinZetaDerivativeAtZero data) 0 ∧
      (reducedSphereMellinZetaContinuationData data).derivativeAtZero.im = 0 ∧
      relativeHeatMellinZetaDeterminant
          (reducedSphereMellinZetaContinuationData data) ≠ 0 ∧
      ‖relativeHeatMellinZetaDeterminant
          (reducedSphereMellinZetaContinuationData data)‖ =
        relativeHeatFinitePartDeterminant
          (reducedSphereMellinFinitePartData data) := by
  refine ⟨reducedSphereMellinZeta_eq_candidate data,
    reducedSphereMellinZeta_hasDerivAt_zero data,
    reducedSphereMellinZetaContinuationData_derivativeAtZero_im data, ?_⟩
  exact relativeHeatMellinZetaDeterminant_gate
    (reducedSphereMellinZetaContinuationData data)

end
end P0EFTJanusProgramPProductThroatSphereMellinZetaContinuation4D
end JanusFormal
