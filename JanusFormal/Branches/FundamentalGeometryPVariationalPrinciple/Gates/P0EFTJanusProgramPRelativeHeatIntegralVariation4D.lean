import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatFinitePartTermwiseVariation4D

/-!
# Differentiation of parameterized relative heat integrals

The short- and long-time pieces of a finite-part determinant are parameterized
integrals.  Their geometric input naturally arrives as a pointwise derivative
of the heat trace, while the analytic input is the theorem allowing derivative
and integral to be interchanged.

This file records that interface without committing to one dominated
convergence theorem.  A concrete application supplies

```text
contribution(a) = integral kernel(a,t) dt,
derivativeContribution(a) = integral derivativeKernel(a,t) dt,
HasDerivAt contribution derivativeContribution a.
```

Thus all domination, measurability and endpoint estimates are concentrated in
one typed interchange certificate for each time region.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRelativeHeatIntegralVariation4D

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open P0EFTJanusProgramPRelativeHeatFinitePartTermwiseVariation4D

/-- Differentiated scalar integral over one fixed measurable time region. -/
structure ParametricRealIntegralVariationData
    (timeRegion : Set Real) where
  kernel : Real → Real → Real
  derivativeKernel : Real → Real → Real
  contribution : Real → Real
  derivativeContribution : Real → Real
  contribution_eq_integral : ∀ parameter,
    contribution parameter =
      ∫ time in timeRegion, kernel parameter time
  derivativeContribution_eq_integral : ∀ parameter,
    derivativeContribution parameter =
      ∫ time in timeRegion, derivativeKernel parameter time
  pointwise_hasDerivAt : ∀ parameter,
    ∀ᵐ time ∂volume.restrict timeRegion,
      HasDerivAt (fun current => kernel current time)
        (derivativeKernel parameter time) parameter
  hasDerivAt_integral : ∀ parameter,
    HasDerivAt contribution (derivativeContribution parameter) parameter

namespace ParametricRealIntegralVariationData

/-- Public differentiated-integral checkpoint. -/
theorem parametric_real_integral_variation_gate
    (timeRegion : Set Real)
    (data : ParametricRealIntegralVariationData timeRegion) :
    (∀ parameter,
      data.contribution parameter =
        ∫ time in timeRegion, data.kernel parameter time) ∧
    (∀ parameter,
      data.derivativeContribution parameter =
        ∫ time in timeRegion, data.derivativeKernel parameter time) ∧
    (∀ parameter,
      HasDerivAt data.contribution
        (data.derivativeContribution parameter) parameter) :=
  ⟨data.contribution_eq_integral,
    data.derivativeContribution_eq_integral,
    data.hasDerivAt_integral⟩

end ParametricRealIntegralVariationData

/-- Counterterm plus short- and long-time integral variations assembling one
reference finite-part family. -/
structure ReferenceHeatFinitePartIntegralAssemblyData
    (family : RelativeHeatMellinZetaFamilyData)
    (shortTimeRegion longTimeRegion : Set Real) where
  countertermContribution : Real → Real
  countertermDerivative : Real → Real
  hasDerivAt_counterterm : ∀ parameter,
    HasDerivAt countertermContribution (countertermDerivative parameter)
      parameter
  shortTime : ParametricRealIntegralVariationData shortTimeRegion
  longTime : ParametricRealIntegralVariationData longTimeRegion
  logDeterminant_eq : ∀ parameter,
    P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D.
        relativeHeatFinitePartLogDeterminant
          (family.finitePartFamily.finitePart parameter) =
      countertermContribution parameter + shortTime.contribution parameter +
        longTime.contribution parameter
  logarithmicTrace : Real → Real
  integratedDerivative_eq_trace : ∀ parameter,
    countertermDerivative parameter +
        shortTime.derivativeContribution parameter +
          longTime.derivativeContribution parameter =
      logarithmicTrace parameter
  zetaPrimeAtZero_real : ∀ parameter,
    (family.zetaPrimeAtZero parameter).im = 0

namespace ReferenceHeatFinitePartIntegralAssemblyData

/-- Forget integral presentations and retain the three termwise scalar
variations. -/
def toTermwiseVariation
    {family : RelativeHeatMellinZetaFamilyData}
    {shortTimeRegion longTimeRegion : Set Real}
    (data : ReferenceHeatFinitePartIntegralAssemblyData family shortTimeRegion
      longTimeRegion) :
    RelativeHeatFinitePartTermwiseVariationData family.finitePartFamily where
  countertermContribution := data.countertermContribution
  shortTimeContribution := data.shortTime.contribution
  longTimeContribution := data.longTime.contribution
  countertermDerivative := data.countertermDerivative
  shortTimeDerivative := data.shortTime.derivativeContribution
  longTimeDerivative := data.longTime.derivativeContribution
  logDeterminant_eq := data.logDeterminant_eq
  hasDerivAt_counterterm := data.hasDerivAt_counterterm
  hasDerivAt_shortTime := data.shortTime.hasDerivAt_integral
  hasDerivAt_longTime := data.longTime.hasDerivAt_integral

/-- Integral assembly gives the complete termwise reference-trace packet. -/
def toTermwiseTraceData
    {family : RelativeHeatMellinZetaFamilyData}
    {shortTimeRegion longTimeRegion : Set Real}
    (data : ReferenceHeatFinitePartIntegralAssemblyData family shortTimeRegion
      longTimeRegion) :
    ReferenceHeatFinitePartTermwiseTraceData family where
  termwise := data.toTermwiseVariation
  logarithmicTrace := data.logarithmicTrace
  totalDerivative_eq_trace := data.integratedDerivative_eq_trace
  zetaPrimeAtZero_real := data.zetaPrimeAtZero_real

/-- Direct reference finite-part derivative from the two differentiated heat
integrals and the counterterm. -/
theorem hasDerivAt_finitePartLog
    {family : RelativeHeatMellinZetaFamilyData}
    {shortTimeRegion longTimeRegion : Set Real}
    (data : ReferenceHeatFinitePartIntegralAssemblyData family shortTimeRegion
      longTimeRegion)
    (parameter : Real) :
    HasDerivAt
      (fun current =>
        P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D.
          relativeHeatFinitePartLogDeterminant
            (family.finitePartFamily.finitePart current))
      (data.logarithmicTrace parameter) parameter :=
  data.toTermwiseTraceData.toReferenceFinitePartTraceVariation.
    hasDerivAt_finitePartLog parameter

/-- Standalone reference coefficient produced by the integral assembly. -/
theorem connectionCoefficient_eq_neg_trace
    {family : RelativeHeatMellinZetaFamilyData}
    {shortTimeRegion longTimeRegion : Set Real}
    (data : ReferenceHeatFinitePartIntegralAssemblyData family shortTimeRegion
      longTimeRegion)
    (parameter : Real) :
    P0EFTJanusProgramPRelativeZetaDeterminantConnection4D.
        relativeZetaConnectionCoefficient family.toZetaFamily parameter =
      -(data.logarithmicTrace parameter : Complex) :=
  data.toTermwiseTraceData.connectionCoefficient_eq_neg_trace parameter

/-- Public integral-assembly checkpoint. -/
theorem reference_heat_finite_part_integral_assembly_gate
    (family : RelativeHeatMellinZetaFamilyData)
    (shortTimeRegion longTimeRegion : Set Real)
    (data : ReferenceHeatFinitePartIntegralAssemblyData family shortTimeRegion
      longTimeRegion) :
    (∀ parameter,
      HasDerivAt
        (fun current =>
          P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D.
            relativeHeatFinitePartLogDeterminant
              (family.finitePartFamily.finitePart current))
        (data.logarithmicTrace parameter) parameter) ∧
    (∀ parameter,
      P0EFTJanusProgramPRelativeZetaDeterminantConnection4D.
          relativeZetaConnectionCoefficient family.toZetaFamily parameter =
        -(data.logarithmicTrace parameter : Complex)) :=
  ⟨data.hasDerivAt_finitePartLog,
    data.connectionCoefficient_eq_neg_trace⟩

end ReferenceHeatFinitePartIntegralAssemblyData

end
end P0EFTJanusProgramPRelativeHeatIntegralVariation4D
end JanusFormal
