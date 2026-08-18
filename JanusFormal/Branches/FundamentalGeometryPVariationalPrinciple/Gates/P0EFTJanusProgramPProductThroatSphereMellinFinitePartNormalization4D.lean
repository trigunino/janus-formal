import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatSphereFiniteCountertermVariation4D

/-!
# Mellin normalization of the reduced-sphere finite part

Gamma normalization adds the Euler--Mascheroni correction attached to the
constant short-time heat coefficient.  This file records that correction
without asserting existence of a Mellin continuation.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPProductThroatSphereMellinFinitePartNormalization4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusProgramPFiniteHeatCountertermVariation4D
open P0EFTJanusProgramPFiniteHeatCountertermFinitePartVariation4D
open P0EFTJanusProgramPProductThroatSphereShortTimeFinitePart4D
open P0EFTJanusProgramPProductThroatSphereFiniteCountertermVariation4D
open P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D

open P0EFTJanusProgramPProductThroatSphereFiniteCountertermVariation4D
  ReducedSphereCountertermProfile

/-- Constant coefficient in the reduced-sphere short-time counterterm. -/
def reducedSphereMellinConstantCoefficient
    (data : ProductThroatSpectralData) : Real :=
  -(1 / 3 : Real) - (monopoleAbsCharge data : Real)

/-- Raw cutoff finite part with the Gamma-normalized constant-coefficient
correction. -/
def reducedSphereMellinCountertermFinitePart
    (data : ProductThroatSpectralData) : Real :=
  reducedSphereCountertermFinitePart data +
    Real.eulerMascheroniConstant *
      reducedSphereMellinConstantCoefficient data

/-- Gamma-normalized finite parts of `t⁻¹`, `1`, and `t`. -/
def reducedSphereMellinCountertermBasisFinitePart :
    ReducedSphereCountertermProfile → Real
  | .inverse => -1
  | .constant => Real.eulerMascheroniConstant
  | .linear => 1

/-- Finite counterterm packet using the Gamma-normalized profile values. -/
def reducedSphereMellinFiniteCountertermVariation
    (data : ProductThroatSpectralData) :
    FiniteHeatCountertermFinitePartVariationData
      ReducedSphereCountertermProfile where
  variation := reducedSphereCountertermVariation data
  basisFinitePart := reducedSphereMellinCountertermBasisFinitePart

theorem reducedSphereMellinFiniteCountertermVariation_counterterm_eq
    (data : ProductThroatSpectralData) (parameter time : Real) :
    counterterm
        (reducedSphereMellinFiniteCountertermVariation data).variation
        parameter time =
      reducedSphereCounterterm data time :=
  reducedSphereCountertermVariation_counterterm_eq data parameter time

theorem reducedSphereMellinFiniteCountertermVariation_contribution_eq
    (data : ProductThroatSpectralData) (parameter : Real) :
    finitePartContribution
        (reducedSphereMellinFiniteCountertermVariation data) parameter =
      reducedSphereMellinCountertermFinitePart data := by
  unfold finitePartContribution
    reducedSphereMellinFiniteCountertermVariation
    reducedSphereCountertermVariation reducedSphereCountertermCoefficient
    reducedSphereMellinCountertermBasisFinitePart
    reducedSphereMellinCountertermFinitePart
    reducedSphereMellinConstantCoefficient
    reducedSphereCountertermFinitePart
  simp
  ring

theorem reducedSphereMellinFiniteCountertermVariation_derivative_eq_zero
    (data : ProductThroatSpectralData) (parameter : Real) :
    finitePartDerivative
        (reducedSphereMellinFiniteCountertermVariation data) parameter = 0 := by
  unfold finitePartDerivative
    reducedSphereMellinFiniteCountertermVariation
    reducedSphereCountertermVariation
    reducedSphereMellinCountertermBasisFinitePart
  simp

/-- Reduced-sphere finite-part packet in the Gamma-normalized Mellin scheme. -/
def reducedSphereMellinFinitePartData
    (data : ProductThroatSpectralData) :
    RelativeHeatFinitePartData (dimensionlessReducedSphereHeatTrace data) where
  counterterm := reducedSphereCounterterm data
  countertermFinitePart := reducedSphereMellinCountertermFinitePart data
  shortTimeIntegrable := positiveTimeReducedSphere_shortTimeIntegrable data
  longTimeIntegrable := positiveTimeReducedSphere_longTimeIntegrable data

@[simp]
theorem reducedSphereMellinFinitePartData_countertermFinitePart
    (data : ProductThroatSpectralData) :
    (reducedSphereMellinFinitePartData data).countertermFinitePart =
      reducedSphereMellinCountertermFinitePart data :=
  rfl

theorem reducedSphereMellinFinitePartData_shortTime_eq_raw
    (data : ProductThroatSpectralData) :
    relativeHeatShortTimeFinitePart (reducedSphereMellinFinitePartData data) =
      relativeHeatShortTimeFinitePart (reducedSphereFinitePartData data) :=
  rfl

theorem reducedSphereMellinFinitePartData_longTime_eq_raw
    (data : ProductThroatSpectralData) :
    relativeHeatLongTimeIntegral (reducedSphereMellinFinitePartData data) =
      relativeHeatLongTimeIntegral (reducedSphereFinitePartData data) :=
  rfl

/-- The Mellin-normalized logarithm differs from the raw cutoff logarithm by
exactly the Euler--Mascheroni correction. -/
theorem reducedSphereMellinFinitePartLogDeterminant_eq_raw
    (data : ProductThroatSpectralData) :
    relativeHeatFinitePartLogDeterminant
        (reducedSphereMellinFinitePartData data) =
      relativeHeatFinitePartLogDeterminant
          (reducedSphereFinitePartData data) -
        Real.eulerMascheroniConstant *
          reducedSphereMellinConstantCoefficient data := by
  unfold relativeHeatFinitePartLogDeterminant
  rw [reducedSphereMellinFinitePartData_shortTime_eq_raw,
    reducedSphereMellinFinitePartData_longTime_eq_raw]
  unfold reducedSphereMellinFinitePartData
    reducedSphereMellinCountertermFinitePart reducedSphereFinitePartData
    reducedSphereFinitePartDataOfLongTime
  ring

/-- Public checkpoint for the Gamma-normalized reduced-sphere finite part. -/
theorem product_throat_sphere_mellin_finite_part_normalization_gate
    (data : ProductThroatSpectralData) (parameter time : Real) :
    counterterm
        (reducedSphereMellinFiniteCountertermVariation data).variation
        parameter time = reducedSphereCounterterm data time ∧
      finitePartContribution
          (reducedSphereMellinFiniteCountertermVariation data) parameter =
        reducedSphereMellinCountertermFinitePart data ∧
      finitePartDerivative
          (reducedSphereMellinFiniteCountertermVariation data) parameter = 0 ∧
      relativeHeatShortTimeFinitePart
          (reducedSphereMellinFinitePartData data) =
        relativeHeatShortTimeFinitePart (reducedSphereFinitePartData data) ∧
      relativeHeatLongTimeIntegral
          (reducedSphereMellinFinitePartData data) =
        relativeHeatLongTimeIntegral (reducedSphereFinitePartData data) ∧
      relativeHeatFinitePartLogDeterminant
          (reducedSphereMellinFinitePartData data) =
        relativeHeatFinitePartLogDeterminant
            (reducedSphereFinitePartData data) -
          Real.eulerMascheroniConstant *
            reducedSphereMellinConstantCoefficient data :=
  ⟨reducedSphereMellinFiniteCountertermVariation_counterterm_eq
      data parameter time,
    reducedSphereMellinFiniteCountertermVariation_contribution_eq data parameter,
    reducedSphereMellinFiniteCountertermVariation_derivative_eq_zero data parameter,
    reducedSphereMellinFinitePartData_shortTime_eq_raw data,
    reducedSphereMellinFinitePartData_longTime_eq_raw data,
    reducedSphereMellinFinitePartLogDeterminant_eq_raw data⟩

end
end P0EFTJanusProgramPProductThroatSphereMellinFinitePartNormalization4D
end JanusFormal
