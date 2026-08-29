import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPThroatMetricPositiveDualizer4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusDifferentialLLWeakEquation4D

/-!
# Finite-frame separation of throat metric tensors

The existing finite smooth tangent-generating family detects a symmetric
two-tensor by the sum of squares of all its frame readings.  This closes the
pointwise algebra needed by the positive-dualizer gate without assuming a
global basis or parallelizability.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPThroatMetricGeneratingFrameSeparation4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff BigOperators
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVThroatBoundary4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusProgramPThroatMetricTensorModule4D
open P0EFTJanusProgramPThroatMetricPositiveDualizer4D
open P0EFTJanusMappingTorusIntrinsicMetricBVThroatBracket4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- Sum of squares of all readings of one symmetric tensor on a finite
generating family. -/
def throatMetricFrameEnergy
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (point : EffectiveThroat period hPeriod) : Real :=
  ∑ i, ∑ j,
    (tensor.tensor point (frame.vectorAt point i)
      (frame.vectorAt point j)) ^ 2

theorem throatMetricFrameEnergy_nonnegative
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    0 ≤ throatMetricFrameEnergy period hPeriod frame tensor point := by
  exact Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _

private theorem throatMetricFrameEnergy_zero_reading
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (hEnergy : throatMetricFrameEnergy period hPeriod frame tensor point = 0)
    (i j : Fin frame.count) :
    tensor.tensor point (frame.vectorAt point i)
        (frame.vectorAt point j) = 0 := by
  have hOuter :
      ∀ i ∈ Finset.univ,
        (∑ j,
          (tensor.tensor point (frame.vectorAt point i)
            (frame.vectorAt point j)) ^ 2) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)).mp hEnergy
  have hSquare :
      (tensor.tensor point (frame.vectorAt point i)
        (frame.vectorAt point j)) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun _ _ => sq_nonneg _)).mp
      (hOuter i (Finset.mem_univ i)) j (Finset.mem_univ j)
  exact sq_eq_zero_iff.mp hSquare

/-- Vanishing frame energy at one point forces the tensor value at that point
to vanish because the finite smooth family spans the tangent fiber. -/
theorem throatMetricFrameEnergy_eq_zero_value
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (hEnergy : throatMetricFrameEnergy period hPeriod frame tensor point = 0) :
    tensor.tensor point = 0 := by
  have hOuter : (tensor.tensor point).toLinearMap = 0 := by
    apply LinearMap.ext_on_range (frame.spansAt point)
    intro i
    apply ContinuousLinearMap.ext
    intro y
    have hInner :
        (tensor.tensor point (frame.vectorAt point i)).toLinearMap = 0 := by
      apply LinearMap.ext_on_range (frame.spansAt point)
      intro j
      exact throatMetricFrameEnergy_zero_reading
        period hPeriod frame tensor point hEnergy i j
    exact LinearMap.congr_fun hInner y
  apply ContinuousLinearMap.ext
  intro x
  exact LinearMap.congr_fun hOuter x

/-- The frame energy vanishes everywhere exactly only for the zero smooth
tensor. -/
theorem throatMetricFrameEnergy_pointwiseSeparates
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (hEnergy :
      ∀ point,
        throatMetricFrameEnergy period hPeriod frame tensor point = 0) :
    tensor = 0 := by
  apply SmoothSymmetricThroatCovariantTwoTensor.ext
  apply ContMDiffSection.ext
  intro point
  exact throatMetricFrameEnergy_eq_zero_value
    period hPeriod frame tensor point (hEnergy point)

/-- Two-sector positive energy used by the throat antifield pair. -/
def throatMetricPairFrameEnergy
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (tensor : SmoothThroatGeneralMetricTensorPair period hPeriod)
    (point : EffectiveThroat period hPeriod) : Real :=
  throatMetricFrameEnergy period hPeriod frame tensor.1 point +
    throatMetricFrameEnergy period hPeriod frame tensor.2 point

theorem throatMetricPairFrameEnergy_nonnegative
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (tensor : SmoothThroatGeneralMetricTensorPair period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    0 ≤ throatMetricPairFrameEnergy period hPeriod frame tensor point :=
  add_nonneg
    (throatMetricFrameEnergy_nonnegative
      period hPeriod frame tensor.1 point)
    (throatMetricFrameEnergy_nonnegative
      period hPeriod frame tensor.2 point)

theorem throatMetricPairFrameEnergy_pointwiseSeparates
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (tensor : SmoothThroatGeneralMetricTensorPair period hPeriod)
    (hEnergy :
      ∀ point,
        throatMetricPairFrameEnergy period hPeriod frame tensor point = 0) :
    tensor = 0 := by
  have hFirst :
      ∀ point,
        throatMetricFrameEnergy period hPeriod frame tensor.1 point = 0 := by
    intro point
    have hFirstNonnegative :=
      throatMetricFrameEnergy_nonnegative
        period hPeriod frame tensor.1 point
    have hSecondNonnegative :=
      throatMetricFrameEnergy_nonnegative
        period hPeriod frame tensor.2 point
    have hSum := hEnergy point
    unfold throatMetricPairFrameEnergy at hSum
    linarith
  have hSecond :
      ∀ point,
        throatMetricFrameEnergy period hPeriod frame tensor.2 point = 0 := by
    intro point
    have hFirstNonnegative :=
      throatMetricFrameEnergy_nonnegative
        period hPeriod frame tensor.1 point
    have hSecondNonnegative :=
      throatMetricFrameEnergy_nonnegative
        period hPeriod frame tensor.2 point
    have hSum := hEnergy point
    unfold throatMetricPairFrameEnergy at hSum
    linarith
  apply Prod.ext
  · exact throatMetricFrameEnergy_pointwiseSeparates
      period hPeriod frame tensor.1 hFirst
  · exact throatMetricFrameEnergy_pointwiseSeparates
      period hPeriod frame tensor.2 hSecond

/-- It is enough to construct a smooth dualizer whose intrinsic Lorentz
pairing is the finite-frame sum of squares. -/
def throatMetricSmoothPositiveDualizerData_of_frameEnergy
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (dualize :
      SmoothThroatGeneralMetricTensorPair period hPeriod →
        SmoothThroatGeneralMetricTensorPair period hPeriod)
    (hContinuous :
      ∀ antifield,
        Continuous
          (fun point : EffectiveThroat period hPeriod =>
            intrinsicThroatTensorPairPairingAt period hPeriod
              antifield (dualize antifield) point))
    (hPairing :
      ∀ antifield point,
        intrinsicThroatTensorPairPairingAt period hPeriod
            antifield (dualize antifield) point =
          throatMetricPairFrameEnergy
            period hPeriod frame antifield point) :
    ThroatMetricSmoothPositiveDualizerData period hPeriod where
  dualize := dualize
  pairingContinuous := hContinuous
  pairingNonnegative := by
    intro antifield point
    rw [hPairing]
    exact throatMetricPairFrameEnergy_nonnegative
      period hPeriod frame antifield point
  pointwiseSeparates := by
    intro antifield hZero
    apply throatMetricPairFrameEnergy_pointwiseSeparates
      period hPeriod frame antifield
    intro point
    rw [← hPairing]
    exact hZero point

end
end P0EFTJanusProgramPThroatMetricGeneratingFrameSeparation4D
end JanusFormal
