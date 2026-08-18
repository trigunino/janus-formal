import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Countable trace sum/integral interchange

A countable family of integrable scalar summands may be integrated termwise
when the integrals of their norms are summable.  The collapsed Duhamel
specialization has exactly the shape required by the existing
`trace_integral_interchange` fields.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPNuclearDuhamelTraceIntegralInterchange4D

set_option autoImplicit false
noncomputable section

open MeasureTheory Set

universe u v

variable {X : Type u} [MeasurableSpace X]
  {Index : Type v}

/-- Minimal certificate for commuting a countable scalar sum with a Bochner
integral. -/
structure CountableTraceIntegralInterchangeData
    (measure : Measure X) (summand : Index → X → Real) where
  summand_integrable : ∀ index, Integrable (summand index) measure
  integral_norm_summable :
    Summable (fun index => ∫ point, ‖summand index point‖ ∂measure)

namespace CountableTraceIntegralInterchangeData

/-- The certified countable sum may be integrated termwise. -/
theorem integral_tsum_eq_tsum_integral
    [Countable Index]
    {measure : Measure X} {summand : Index → X → Real}
    (data : CountableTraceIntegralInterchangeData measure summand) :
    (∫ point, ∑' index, summand index point ∂measure) =
      ∑' index, ∫ point, summand index point ∂measure :=
  (MeasureTheory.integral_tsum_of_summable_integral_norm
    data.summand_integrable data.integral_norm_summable).symm

end CountableTraceIntegralInterchangeData

/-- Concrete domination data generating the countable interchange
certificate. -/
structure DominatedCountableTraceIntegralInterchangeData
    (measure : Measure X) (summand : Index → X → Real) where
  envelope : X → Real
  envelope_integrable : Integrable envelope measure
  coefficientBound : Index → Real
  coefficientBound_summable : Summable coefficientBound
  coefficientBound_nonnegative : ∀ index, 0 ≤ coefficientBound index
  summand_aeStronglyMeasurable : ∀ index,
    AEStronglyMeasurable (summand index) measure
  summand_norm_le : ∀ index, ∀ᵐ point ∂measure,
    ‖summand index point‖ ≤ coefficientBound index * envelope point

namespace DominatedCountableTraceIntegralInterchangeData

/-- Each scalar summand is integrable under the common envelope. -/
theorem summand_integrable
    {measure : Measure X} {summand : Index → X → Real}
    (data : DominatedCountableTraceIntegralInterchangeData measure summand)
    (index : Index) :
    Integrable (summand index) measure := by
  apply (data.envelope_integrable.const_mul
    (data.coefficientBound index)).mono'
  · exact data.summand_aeStronglyMeasurable index
  · exact data.summand_norm_le index

/-- The integral of each summand norm is bounded by the corresponding
coefficient times the integral of the envelope. -/
theorem integral_norm_le
    {measure : Measure X} {summand : Index → X → Real}
    (data : DominatedCountableTraceIntegralInterchangeData measure summand)
    (index : Index) :
    (∫ point, ‖summand index point‖ ∂measure) ≤
      data.coefficientBound index *
        ∫ point, data.envelope point ∂measure := by
  calc
    (∫ point, ‖summand index point‖ ∂measure) ≤
        ∫ point,
          data.coefficientBound index * data.envelope point ∂measure :=
      integral_mono_ae (data.summand_integrable index).norm
        (data.envelope_integrable.const_mul (data.coefficientBound index))
        (data.summand_norm_le index)
    _ = data.coefficientBound index *
        ∫ point, data.envelope point ∂measure :=
      MeasureTheory.integral_const_mul _ _

/-- The integrals of the summand norms form a summable family. -/
theorem integral_norm_summable
    {measure : Measure X} {summand : Index → X → Real}
    (data : DominatedCountableTraceIntegralInterchangeData measure summand) :
    Summable (fun index => ∫ point, ‖summand index point‖ ∂measure) :=
  (data.coefficientBound_summable.mul_right
      (∫ point, data.envelope point ∂measure)).of_nonneg_of_le
    (fun _ => integral_nonneg fun _ => norm_nonneg _)
    data.integral_norm_le

/-- Forget the concrete envelope after generating the minimal interchange
certificate. -/
def toCountableTraceIntegralInterchangeData
    {measure : Measure X} {summand : Index → X → Real}
    (data : DominatedCountableTraceIntegralInterchangeData measure summand) :
    CountableTraceIntegralInterchangeData measure summand where
  summand_integrable := data.summand_integrable
  integral_norm_summable := data.integral_norm_summable

/-- The dominated countable sum may be integrated termwise. -/
theorem integral_tsum_eq_tsum_integral
    [Countable Index]
    {measure : Measure X} {summand : Index → X → Real}
    (data : DominatedCountableTraceIntegralInterchangeData measure summand) :
    (∫ point, ∑' index, summand index point ∂measure) =
      ∑' index, ∫ point, summand index point ∂measure :=
  data.toCountableTraceIntegralInterchangeData.integral_tsum_eq_tsum_integral

/-- Public dominated countable interchange checkpoint. -/
theorem dominated_countable_trace_integral_interchange_gate
    [Countable Index]
    {measure : Measure X} {summand : Index → X → Real}
    (data : DominatedCountableTraceIntegralInterchangeData measure summand) :
    (∀ index, Integrable (summand index) measure) ∧
    Summable (fun index => ∫ point, ‖summand index point‖ ∂measure) ∧
    (∫ point, ∑' index, summand index point ∂measure) =
      ∑' index, ∫ point, summand index point ∂measure :=
  ⟨data.summand_integrable, data.integral_norm_summable,
    data.integral_tsum_eq_tsum_integral⟩

end DominatedCountableTraceIntegralInterchangeData

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E]

/-- Specialization producing exactly the spectral `trace_integral_interchange`
field used by the collapsed Duhamel packets. -/
theorem collapsedTrace_integral_interchange
    [Countable Index]
    {timeRegion : Set Real}
    {coefficient : Real → Real → Index → Real}
    {leftVector rightVector : Real → Index → E}
    {integratedCoefficient : Real → Index → Real}
    (integratedCoefficient_eq : ∀ parameter index,
      integratedCoefficient parameter index =
        ∫ time in timeRegion,
          if 0 < time then coefficient parameter time index else 0)
    (certificate : ∀ parameter,
      CountableTraceIntegralInterchangeData
        (volume.restrict timeRegion)
        (fun index time =>
          (if 0 < time then coefficient parameter time index else 0) *
            inner Real (leftVector parameter index)
              (rightVector parameter index)))
    (parameter : Real) :
    (∫ time in timeRegion,
      ∑' index,
        (if 0 < time then coefficient parameter time index else 0) *
          inner Real (leftVector parameter index)
            (rightVector parameter index)) =
      ∑' index,
        integratedCoefficient parameter index *
          inner Real (leftVector parameter index)
            (rightVector parameter index) := by
  calc
    _ = ∑' index,
        ∫ time in timeRegion,
          (if 0 < time then coefficient parameter time index else 0) *
            inner Real (leftVector parameter index)
              (rightVector parameter index) :=
      (certificate parameter).integral_tsum_eq_tsum_integral
    _ = _ := by
      apply tsum_congr
      intro index
      rw [MeasureTheory.integral_mul_const,
        integratedCoefficient_eq parameter index]

/-- Public countable spectral interchange checkpoint. -/
theorem nuclear_duhamel_trace_integral_interchange_gate
    [Countable Index]
    {timeRegion : Set Real}
    {coefficient : Real → Real → Index → Real}
    {leftVector rightVector : Real → Index → E}
    {integratedCoefficient : Real → Index → Real}
    (integratedCoefficient_eq : ∀ parameter index,
      integratedCoefficient parameter index =
        ∫ time in timeRegion,
          if 0 < time then coefficient parameter time index else 0)
    (certificate : ∀ parameter,
      CountableTraceIntegralInterchangeData
        (volume.restrict timeRegion)
        (fun index time =>
          (if 0 < time then coefficient parameter time index else 0) *
            inner Real (leftVector parameter index)
              (rightVector parameter index))) :
    ∀ parameter,
      (∫ time in timeRegion,
        ∑' index,
          (if 0 < time then coefficient parameter time index else 0) *
            inner Real (leftVector parameter index)
              (rightVector parameter index)) =
        ∑' index,
          integratedCoefficient parameter index *
            inner Real (leftVector parameter index)
              (rightVector parameter index) :=
  collapsedTrace_integral_interchange integratedCoefficient_eq certificate

end
end P0EFTJanusProgramPNuclearDuhamelTraceIntegralInterchange4D
end JanusFormal
