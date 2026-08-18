import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatSphereShortTimeFinitePart4D

/-!
# Cutoff proof of the reduced sphere counterterm finite part

This certifies the Hadamard finite part used by the reduced product-throat
sphere determinant.  The local counterterm is integrated on `[ε,1]`; after
removing its inverse and logarithmic divergences, the cutoff expression tends
to the declared finite part.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPProductThroatSphereCountertermFinitePartLimit4D

set_option autoImplicit false
noncomputable section

open Filter MeasureTheory Set
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusMonopoleHeatAsymptoticMatch
open P0EFTJanusProgramPProductThroatSphereShortTimeFinitePart4D
open P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D

/-- Primitive of the logarithmically weighted reduced local counterterm. -/
def reducedSphereCountertermPrimitive
    (data : ProductThroatSpectralData) (time : Real) : Real :=
  -2 / time +
    (-(1 / 3 : Real) - (monopoleAbsCharge data : Real)) * Real.log time +
    ((5 * (monopoleAbsCharge data : Real) ^ 2 - 1) / 30) * time

theorem reducedSphereCountertermPrimitive_hasDerivAt
    (data : ProductThroatSpectralData) {time : Real} (hTime : time ≠ 0) :
    HasDerivAt (reducedSphereCountertermPrimitive data)
      (reducedSphereCounterterm data time / time) time := by
  unfold reducedSphereCountertermPrimitive
  refine (((hasDerivAt_const time (-2 : Real)).div (hasDerivAt_id time) hTime).add
      ((Real.hasDerivAt_log hTime).const_mul
        (-(1 / 3 : Real) - (monopoleAbsCharge data : Real)))).add
      ((hasDerivAt_id time).const_mul
        ((5 * (monopoleAbsCharge data : Real) ^ 2 - 1) / 30)) |>.congr_deriv ?_
  unfold reducedSphereCounterterm predictedSphereHeatExpansion
  simp only [id_eq]
  field_simp [hTime]
  ring

theorem reducedSphereCounterterm_intervalIntegral
    (data : ProductThroatSpectralData) {cutoff : Real}
    (hCutoff : cutoff ∈ Set.Ioc (0 : Real) 1) :
    (∫ time in cutoff..1, reducedSphereCounterterm data time / time) =
      2 / cutoff - 2 +
        ((1 / 3 : Real) + (monopoleAbsCharge data : Real)) *
          Real.log cutoff +
        ((5 * (monopoleAbsCharge data : Real) ^ 2 - 1) / 30) *
          (1 - cutoff) := by
  have hCutoffPos : 0 < cutoff := hCutoff.1
  have hCutoffLe : cutoff ≤ 1 := hCutoff.2
  have hContinuous : ContinuousOn
      (fun time => reducedSphereCounterterm data time / time)
      (Set.uIcc cutoff 1) := by
    rw [Set.uIcc_of_le hCutoffLe]
    have hNonzero : ∀ time ∈ Set.Icc cutoff 1, time ≠ 0 :=
      fun time hTime => ne_of_gt (hCutoffPos.trans_le hTime.1)
    have hTwoDiv : ContinuousOn (fun time : Real => 2 / time)
        (Set.Icc cutoff 1) :=
      continuous_const.continuousOn.div continuous_id.continuousOn hNonzero
    have hLinear : Continuous
        (fun time : Real =>
          (5 * (monopoleAbsCharge data : Real) ^ 2 - 1) * time / 30) := by
      fun_prop
    have hCounterterm : ContinuousOn (reducedSphereCounterterm data)
        (Set.Icc cutoff 1) := by
      unfold reducedSphereCounterterm predictedSphereHeatExpansion
      exact ((hTwoDiv.sub continuous_const.continuousOn).add
        hLinear.continuousOn).sub continuous_const.continuousOn
    exact hCounterterm.div continuous_id.continuousOn hNonzero
  have hIntegral := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := cutoff) (b := 1)
    (f := reducedSphereCountertermPrimitive data)
    (f' := fun time => reducedSphereCounterterm data time / time)
    (fun time hTime =>
      reducedSphereCountertermPrimitive_hasDerivAt data
        (ne_of_gt (hCutoffPos.trans_le ((Set.uIcc_of_le hCutoffLe ▸ hTime).1))))
    hContinuous.intervalIntegrable
  rw [hIntegral]
  unfold reducedSphereCountertermPrimitive
  rw [Real.log_one]
  field_simp [ne_of_gt hCutoffPos]
  ring

/-- Divergent part of the truncated logarithmic counterterm integral. -/
def reducedSphereCountertermDivergence
    (data : ProductThroatSpectralData) (cutoff : Real) : Real :=
  2 / cutoff +
    ((1 / 3 : Real) + (monopoleAbsCharge data : Real)) * Real.log cutoff

/-- Truncated integral after removal of its explicit UV divergences. -/
def reducedSphereCountertermRenormalizedCutoff
    (data : ProductThroatSpectralData) (cutoff : Real) : Real :=
  (∫ time in cutoff..1, reducedSphereCounterterm data time / time) -
    reducedSphereCountertermDivergence data cutoff

theorem reducedSphereCountertermRenormalizedCutoff_eq
    (data : ProductThroatSpectralData) {cutoff : Real}
    (hCutoff : cutoff ∈ Set.Ioc (0 : Real) 1) :
    reducedSphereCountertermRenormalizedCutoff data cutoff =
      reducedSphereCountertermFinitePart data -
        ((5 * (monopoleAbsCharge data : Real) ^ 2 - 1) / 30) * cutoff := by
  rw [reducedSphereCountertermRenormalizedCutoff,
    reducedSphereCounterterm_intervalIntegral data hCutoff]
  unfold reducedSphereCountertermDivergence
    reducedSphereCountertermFinitePart
  ring

/-- The declared scalar is the genuine cutoff finite part. -/
theorem reducedSphereCountertermRenormalizedCutoff_tendsto
    (data : ProductThroatSpectralData) :
    Tendsto (reducedSphereCountertermRenormalizedCutoff data)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (reducedSphereCountertermFinitePart data)) := by
  have hModel : Tendsto
      (fun cutoff : Real =>
        reducedSphereCountertermFinitePart data -
          ((5 * (monopoleAbsCharge data : Real) ^ 2 - 1) / 30) * cutoff)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (reducedSphereCountertermFinitePart data)) := by
    have hId : Tendsto (fun cutoff : Real => cutoff)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
      tendsto_id.mono_left inf_le_left
    simpa using tendsto_const_nhds.sub (tendsto_const_nhds.mul hId)
  refine hModel.congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds
      (Iio_mem_nhds (by norm_num : (0 : Real) < 1))] with cutoff hPositive hSmall
  exact reducedSphereCountertermRenormalizedCutoff_eq data
    ⟨hPositive, hSmall.le⟩ |>.symm

/-- The counterterm field used by the finite-part packet has the certified
cutoff value. -/
theorem reducedSphereFinitePartData_counterterm_limit
    (data : ProductThroatSpectralData) :
    Tendsto (reducedSphereCountertermRenormalizedCutoff data)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (reducedSphereFinitePartData data).countertermFinitePart) := by
  simpa [reducedSphereFinitePartData,
    reducedSphereFinitePartDataOfLongTime] using
    reducedSphereCountertermRenormalizedCutoff_tendsto data

/-- The logarithmic weight identity on the open short-time interval. -/
theorem shortTimeInvWeight_mul_time_eq_one :
    ∀ᵐ time ∂volume.restrict (Set.Ioo (0 : Real) 1),
      time⁻¹ * time = 1 := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with time hTime
  simp [ne_of_gt hTime.1]

/-- The concrete reduced-sphere remainder is integrable on the exact open
region used by the Duhamel short-time frontend. -/
theorem positiveTimeReducedSphere_shortTimeIntegrable_Ioo
    (data : ProductThroatSpectralData) :
    IntegrableOn
      (fun time => time⁻¹ *
        (positiveTimeTraceExtension
            (dimensionlessReducedSphereHeatTrace data) time -
          reducedSphereCounterterm data time))
      (Set.Ioo (0 : Real) 1) := by
  rw [← integrableOn_Ioc_iff_integrableOn_Ioo]
  simpa [div_eq_mul_inv, mul_comm] using
    positiveTimeReducedSphere_shortTimeIntegrable data

/-- The open-interval integral is exactly the short-time contribution stored
in the reduced-sphere finite-part packet. -/
theorem positiveTimeReducedSphere_shortTimeIntegral_Ioo_eq
    (data : ProductThroatSpectralData) :
    (∫ time in Set.Ioo (0 : Real) 1,
      time⁻¹ *
        (positiveTimeTraceExtension
            (dimensionlessReducedSphereHeatTrace data) time -
          reducedSphereCounterterm data time)) =
      relativeHeatShortTimeFinitePart (reducedSphereFinitePartData data) := by
  unfold relativeHeatShortTimeFinitePart
  rw [integral_Ioc_eq_integral_Ioo]
  simp only [reducedSphereFinitePartData,
    reducedSphereFinitePartDataOfLongTime]
  apply integral_congr_ae
  filter_upwards with time
  ring

/-- Public open-region checkpoint matching the logarithmic Duhamel weight. -/
theorem product_throat_sphere_short_time_Ioo_gate
    (data : ProductThroatSpectralData) :
    (∀ᵐ time ∂volume.restrict (Set.Ioo (0 : Real) 1),
      time⁻¹ * time = 1) ∧
    IntegrableOn
      (fun time => time⁻¹ *
        (positiveTimeTraceExtension
            (dimensionlessReducedSphereHeatTrace data) time -
          reducedSphereCounterterm data time))
      (Set.Ioo (0 : Real) 1) ∧
    (∫ time in Set.Ioo (0 : Real) 1,
      time⁻¹ *
        (positiveTimeTraceExtension
            (dimensionlessReducedSphereHeatTrace data) time -
          reducedSphereCounterterm data time)) =
      relativeHeatShortTimeFinitePart (reducedSphereFinitePartData data) :=
  ⟨shortTimeInvWeight_mul_time_eq_one,
    positiveTimeReducedSphere_shortTimeIntegrable_Ioo data,
    positiveTimeReducedSphere_shortTimeIntegral_Ioo_eq data⟩

/-- Public cutoff certification checkpoint. -/
theorem product_throat_sphere_counterterm_finite_part_limit_gate
    (data : ProductThroatSpectralData) :
    Tendsto (reducedSphereCountertermRenormalizedCutoff data)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (reducedSphereFinitePartData data).countertermFinitePart) :=
  reducedSphereFinitePartData_counterterm_limit data

end
end P0EFTJanusProgramPProductThroatSphereCountertermFinitePartLimit4D
end JanusFormal
