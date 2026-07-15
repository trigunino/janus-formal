import Mathlib.Analysis.Asymptotics.Lemmas
import JanusFormal.Branches.FundamentalGeometryD7SpectralTheory.Gates.P0EFTJanusMonopoleSphereHeatTrace
import JanusFormal.Branches.FundamentalGeometryD7SpectralTheory.Gates.P0EFTJanusProductThroatDiracHeatCoefficients

namespace JanusFormal
namespace P0EFTJanusMonopoleHeatAsymptoticMatch

set_option autoImplicit false

open Filter Set Asymptotics
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusMonopoleSphereHeatTrace
open P0EFTJanusProductThroatLocalInvariants
open P0EFTJanusProductThroatDiracHeatCoefficients
open P0EFTJanusUniversalClosedHeatCoefficients
open P0EFTJanusDiracSeeleyDeWittCandidate

noncomputable section

def dimensionlessFullSphereHeatTrace
    (data : ProductThroatSpectralData) (u : ℝ) : ℝ :=
  (monopoleAbsCharge data : ℝ) +
    2 * sphereHeatTrace data (u * data.sphereRadius ^ 2)

/-- Euler--Maclaurin boundary jets for `(2x+q) exp(-u x(x+q))`. -/
def emFirstJet (q u : ℝ) : ℝ := 2 - q ^ 2 * u

def emThirdJet (q u : ℝ) : ℝ :=
  -12 * u + 12 * q ^ 2 * u ^ 2 - q ^ 4 * u ^ 3

def eulerMaclaurinApproximation (q u : ℝ) : ℝ :=
  q + 2 * (1 / u - q / 2 - emFirstJet q u / 12 +
    emThirdJet q u / 720)

def predictedSphereHeatExpansion (q u : ℝ) : ℝ :=
  2 / u - 1 / 3 + (5 * q ^ 2 - 1) * u / 30

theorem euler_maclaurin_approximation_expands
    (q u : ℝ) :
    eulerMaclaurinApproximation q u =
      predictedSphereHeatExpansion q u +
        q ^ 2 * u ^ 2 / 30 - q ^ 4 * u ^ 3 / 360 := by
  unfold eulerMaclaurinApproximation predictedSphereHeatExpansion
    emFirstJet emThirdJet
  ring

def EulerMaclaurinRemainderControlled
    (data : ProductThroatSpectralData) : Prop :=
  Tendsto
    (fun u => (dimensionlessFullSphereHeatTrace data u -
      eulerMaclaurinApproximation (monopoleAbsCharge data : ℝ) u) / u)
    (nhdsWithin 0 (Ioi 0)) (nhds 0)

def SmallTimeSphereHeatCoefficientsMatched
    (data : ProductThroatSpectralData) : Prop :=
  Tendsto
    (fun u => (dimensionlessFullSphereHeatTrace data u -
      predictedSphereHeatExpansion (monopoleAbsCharge data : ℝ) u) / u)
    (nhdsWithin 0 (Ioi 0)) (nhds 0)

theorem polynomial_tail_ratio_tends_to_zero (q : ℝ) :
    Tendsto (fun u : ℝ => q ^ 2 * u / 30 - q ^ 4 * u ^ 2 / 360)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hContinuous : ContinuousAt
      (fun u : ℝ => q ^ 2 * u / 30 - q ^ 4 * u ^ 2 / 360) 0 := by
    fun_prop
  change Tendsto (fun u : ℝ => q ^ 2 * u / 30 - q ^ 4 * u ^ 2 / 360)
    (nhds 0 ⊓ Filter.principal (Ioi 0)) (nhds 0)
  simpa using hContinuous.tendsto.mono_left inf_le_left

theorem small_time_coefficients_match_of_euler_maclaurin_control
    (data : ProductThroatSpectralData)
    (hControl : EulerMaclaurinRemainderControlled data) :
    SmallTimeSphereHeatCoefficientsMatched data := by
  unfold EulerMaclaurinRemainderControlled at hControl
  unfold SmallTimeSphereHeatCoefficientsMatched
  have hTail := polynomial_tail_ratio_tends_to_zero
    (monopoleAbsCharge data : ℝ)
  have hSum : Tendsto
      (fun u =>
        (dimensionlessFullSphereHeatTrace data u -
          eulerMaclaurinApproximation (monopoleAbsCharge data : ℝ) u) / u +
        ((monopoleAbsCharge data : ℝ) ^ 2 * u / 30 -
          (monopoleAbsCharge data : ℝ) ^ 4 * u ^ 2 / 360))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa using hControl.add hTail
  refine hSum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with u hu
  have huNonzero : u ≠ 0 := ne_of_gt hu
  rw [euler_maclaurin_approximation_expands]
  field_simp
  ring

def spectralSphereLeadingCoefficient : ℝ := 2

def spectralSphereConstantCoefficient : ℝ := -(1 / 3)

def spectralSphereLinearCoefficient (monopoleNumber : ℤ) : ℝ :=
  (5 * (monopoleNumber : ℝ) ^ 2 - 1) / 30

def spectralProductA0 (data : ProductThroatInvariantData) : ℝ :=
  4 * data.piConstant * spectralSphereLeadingCoefficient *
    data.geometricLength ^ 3 * data.circleModulus

def spectralProductA2 (data : ProductThroatInvariantData) : ℝ :=
  4 * data.piConstant * spectralSphereConstantCoefficient *
    data.geometricLength * data.circleModulus

def spectralProductA4 (data : ProductThroatInvariantData) : ℝ :=
  4 * data.piConstant * spectralSphereLinearCoefficient data.monopoleNumber *
    data.circleModulus / data.geometricLength

theorem spectral_product_coefficients_match_universal
    (data : ProductThroatInvariantData) :
    spectralProductA0 data =
      reducedA0 (rankTwoDiracAsLaplaceData (productThroatDiracTraceData data)) ∧
    spectralProductA2 data =
      reducedA2 (rankTwoDiracAsLaplaceData (productThroatDiracTraceData data)) ∧
    spectralProductA4 data =
      reducedA4 (rankTwoDiracAsLaplaceData (productThroatDiracTraceData data)) := by
  rw [universal_product_throat_a0_formula,
    universal_product_throat_a2_formula,
    universal_product_throat_a4_formula]
  unfold spectralProductA0 spectralProductA2 spectralProductA4
    spectralSphereLeadingCoefficient spectralSphereConstantCoefficient
    spectralSphereLinearCoefficient
  constructor
  · ring
  · constructor <;> ring

end

end P0EFTJanusMonopoleHeatAsymptoticMatch
end JanusFormal
