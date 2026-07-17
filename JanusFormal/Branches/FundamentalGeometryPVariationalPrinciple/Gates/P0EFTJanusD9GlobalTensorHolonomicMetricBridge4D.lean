import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusD9FullSymmetricMetricLocalCompletion4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D

/-!
# Global tensor coefficients in the local D9 metric slot

A supplied holonomic frame turns a genuine global smooth symmetric covariant
two-tensor into six smooth spatial chart coefficients.  Those coefficients
fill the local D9 symmetric-metric slot.  This does not construct the chart,
identify its frame intrinsically with the throat tangent bundle, or show that
the tensor is a tangent to the global Program-P action.
-/

namespace JanusFormal
namespace P0EFTJanusD9GlobalTensorHolonomicMetricBridge4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusMappingTorusD8NonabelianGhostThroatBRST4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusD9MatterSquaredSpinorCoordinateCompletion4D
open P0EFTJanusD9FullSymmetricMetricLocalCompletion4D

variable (period : Real) (hPeriod : period ≠ 0)

abbrev Index4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Index4
abbrev Vector4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveThroat := MappingTorus (throatData period hPeriod)
private abbrev ThroatCover := MappingTorusCover (throatData period hPeriod)

/-- One coefficient of a global symmetric tensor in a supplied holonomic
frame. -/
def d9TensorChartCoefficient
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (first second : Index4) (coordinate : Vector4) : Real :=
  tensor.tensor (patch.coordinateMap coordinate)
    (patch.frame coordinate first) (patch.frame coordinate second)

theorem d9TensorChartCoefficient_contDiff
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (first second : Index4) :
    ContDiff Real ∞
      (d9TensorChartCoefficient period hPeriod tensor patch first second) := by
  change ContDiff Real ∞ (fun coordinate =>
    tensor.tensor (patch.coordinateMap coordinate)
      (patch.frame coordinate first) (patch.frame coordinate second))
  exact patch.tensorCoefficient_contDiff tensor first second

/-- The spatial `1,2,3` block of a global tensor, expressed as the six D9
metric coefficients at one supplied chart coordinate. -/
def d9TensorChartMetricVariation
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) : D9FullSymmetricMetricVariation where
  xx := d9TensorChartCoefficient period hPeriod tensor patch 1 1 coordinate
  yy := d9TensorChartCoefficient period hPeriod tensor patch 2 2 coordinate
  zz := d9TensorChartCoefficient period hPeriod tensor patch 3 3 coordinate
  xy := d9TensorChartCoefficient period hPeriod tensor patch 1 2 coordinate
  xz := d9TensorChartCoefficient period hPeriod tensor patch 1 3 coordinate
  yz := d9TensorChartCoefficient period hPeriod tensor patch 2 3 coordinate

theorem d9TensorChartMetricVariation_xx_contDiff
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    ContDiff Real ∞ (fun coordinate =>
      (d9TensorChartMetricVariation period hPeriod tensor patch coordinate).xx) := by
  simpa [d9TensorChartMetricVariation] using
    d9TensorChartCoefficient_contDiff period hPeriod tensor patch
      (1 : Index4) (1 : Index4)

theorem d9TensorChartMetricVariation_yy_contDiff
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    ContDiff Real ∞ (fun coordinate =>
      (d9TensorChartMetricVariation period hPeriod tensor patch coordinate).yy) := by
  simpa [d9TensorChartMetricVariation] using
    d9TensorChartCoefficient_contDiff period hPeriod tensor patch
      (2 : Index4) (2 : Index4)

theorem d9TensorChartMetricVariation_zz_contDiff
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    ContDiff Real ∞ (fun coordinate =>
      (d9TensorChartMetricVariation period hPeriod tensor patch coordinate).zz) := by
  simpa [d9TensorChartMetricVariation] using
    d9TensorChartCoefficient_contDiff period hPeriod tensor patch
      (3 : Index4) (3 : Index4)

theorem d9TensorChartMetricVariation_xy_contDiff
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    ContDiff Real ∞ (fun coordinate =>
      (d9TensorChartMetricVariation period hPeriod tensor patch coordinate).xy) := by
  simpa [d9TensorChartMetricVariation] using
    d9TensorChartCoefficient_contDiff period hPeriod tensor patch
      (1 : Index4) (2 : Index4)

theorem d9TensorChartMetricVariation_xz_contDiff
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    ContDiff Real ∞ (fun coordinate =>
      (d9TensorChartMetricVariation period hPeriod tensor patch coordinate).xz) := by
  simpa [d9TensorChartMetricVariation] using
    d9TensorChartCoefficient_contDiff period hPeriod tensor patch
      (1 : Index4) (3 : Index4)

theorem d9TensorChartMetricVariation_yz_contDiff
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    ContDiff Real ∞ (fun coordinate =>
      (d9TensorChartMetricVariation period hPeriod tensor patch coordinate).yz) := by
  simpa [d9TensorChartMetricVariation] using
    d9TensorChartCoefficient_contDiff period hPeriod tensor patch
      (2 : Index4) (3 : Index4)

/-- Assemble the existing Program-P variation with metric coefficients coming
from a genuine global tensor in one supplied holonomic frame. -/
def d9CompleteLocalVariationFromTensorChart
    (programVariation : IndependentFieldVariation period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) : D9CompleteLocalVariation period hPeriod where
  programVariation := programVariation
  metricVariation :=
    d9TensorChartMetricVariation period hPeriod tensor patch coordinate

/-- At a throat point represented by the supplied chart coordinate, the D9
metric slot is exactly the six spatial coefficients of the global tensor.
The coordinate-point equality is a supplied local compatibility datum. -/
theorem d9LocalField_tensorChartMetricPerturbation
    (fields : IndependentFields period hPeriod)
    (programVariation : IndependentFieldVariation period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (anchor : ThroatCover period hPeriod)
    (hPoint : point ∈ normalBundleBaseSet period hPeriod anchor)
    (ghost : CInfinityThroatGhost period hPeriod)
    (_hCoordinatePoint : patch.coordinateMap coordinate =
      fixedThroatQuotientInclusion period hPeriod point) :
    (d9LocalFieldWithFullSymmetricMetric period hPeriod fields
      (d9CompleteLocalVariationFromTensorChart period hPeriod
        programVariation tensor patch coordinate)
      sector column point displacement anchor hPoint ghost).bosonic.metricPerturbation =
      { xx := d9TensorChartCoefficient period hPeriod tensor patch 1 1 coordinate
        yy := d9TensorChartCoefficient period hPeriod tensor patch 2 2 coordinate
        zz := d9TensorChartCoefficient period hPeriod tensor patch 3 3 coordinate
        xy := d9TensorChartCoefficient period hPeriod tensor patch 1 2 coordinate
        xz := d9TensorChartCoefficient period hPeriod tensor patch 1 3 coordinate
        yz := d9TensorChartCoefficient period hPeriod tensor patch 2 3 coordinate } := by
  rfl

end

end P0EFTJanusD9GlobalTensorHolonomicMetricBridge4D
end JanusFormal
