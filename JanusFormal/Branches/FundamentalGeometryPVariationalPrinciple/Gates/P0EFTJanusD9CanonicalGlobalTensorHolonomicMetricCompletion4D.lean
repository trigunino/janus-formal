import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusD9GlobalTensorHolonomicMetricBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalTotalR4BallParametrization4D

/-!
# Canonical chart selection for the D9 global-tensor metric slot

The total `R^4` ball parametrization supplies a holonomic chart through the
image of every actual throat point.  A classical selection of that chart and
coordinate removes the compatibility datum previously supplied by hand, and
the six spatial coefficients of a genuine global symmetric tensor assemble
the complete local D9 metric variation.

The Program-P variation and every non-metric D9 input remain explicit.  The
global tensor is independent geometric data here; this gate does not identify
it with a tangent vector to the global action.
-/

namespace JanusFormal
namespace P0EFTJanusD9CanonicalGlobalTensorHolonomicMetricCompletion4D

set_option autoImplicit false

noncomputable section

open Set
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusMappingTorusD8NonabelianGhostThroatBRST4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusCompleteGaugeFixedEllipticSymbol
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusD9MatterSquaredSpinorCoordinateCompletion4D
open P0EFTJanusD9FullSymmetricMetricLocalCompletion4D
open P0EFTJanusD9GlobalTensorHolonomicMetricBridge4D

variable (period : Real) (hPeriod : period ≠ 0)

abbrev Vector4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveThroat := MappingTorus (throatData period hPeriod)
private abbrev ThroatCover := MappingTorusCover (throatData period hPeriod)

/-- A holonomic chart witness through the spacetime image of one genuine
throat point. -/
structure D9ThroatHolonomicChartWitness
    (point : EffectiveThroat period hPeriod) where
  patch : SmoothHolonomicFrameChart4 period hPeriod
  coordinate : Vector4
  coordinateMap_eq :
    patch.coordinateMap coordinate =
      fixedThroatQuotientInclusion period hPeriod point

/-- The total-ball theorem produces a chart witness at every actual throat
point; no chart-coordinate compatibility hypothesis is supplied by callers.
-/
theorem d9ThroatHolonomicChartWitness_nonempty
    (point : EffectiveThroat period hPeriod) :
    Nonempty (D9ThroatHolonomicChartWitness period hPeriod point) := by
  have hCharts :=
    P0EFTJanusMappingTorusCanonicalHolonomicChartBallRealization4D.canonicalHolonomicChartThroughEveryPoint_of_totalR4BallParametrizations
      period hPeriod
      P0EFTJanusMappingTorusCanonicalTotalR4BallParametrization4D.totalR4BallParametrizationsExist
  rcases hCharts (fixedThroatQuotientInclusion period hPeriod point) with
    ⟨patch, coordinate, hCoordinate⟩
  exact ⟨⟨patch, coordinate, hCoordinate⟩⟩

/-- One selected witness from the canonical chart-existence theorem.  No
uniqueness of this classical selection is asserted. -/
def selectedD9ThroatHolonomicChart
    (point : EffectiveThroat period hPeriod) :
    D9ThroatHolonomicChartWitness period hPeriod point :=
  Classical.choice
    (d9ThroatHolonomicChartWitness_nonempty period hPeriod point)

def selectedD9ThroatHolonomicPatch
    (point : EffectiveThroat period hPeriod) :
    SmoothHolonomicFrameChart4 period hPeriod :=
  (selectedD9ThroatHolonomicChart period hPeriod point).patch

def selectedD9ThroatHolonomicCoordinate
    (point : EffectiveThroat period hPeriod) : Vector4 :=
  (selectedD9ThroatHolonomicChart period hPeriod point).coordinate

@[simp] theorem selectedD9ThroatHolonomicPatch_coordinateMap
    (point : EffectiveThroat period hPeriod) :
    (selectedD9ThroatHolonomicPatch period hPeriod point).coordinateMap
        (selectedD9ThroatHolonomicCoordinate period hPeriod point) =
      fixedThroatQuotientInclusion period hPeriod point :=
  (selectedD9ThroatHolonomicChart period hPeriod point).coordinateMap_eq

/-- Assemble the complete D9 local variation from the explicit Program-P
variation and the six selected-chart coefficients of a genuine global
symmetric tensor. -/
def d9CompleteLocalVariationFromGlobalTensorAtThroatPoint
    (programVariation : IndependentFieldVariation period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    D9CompleteLocalVariation period hPeriod :=
  d9CompleteLocalVariationFromTensorChart period hPeriod programVariation tensor
    (selectedD9ThroatHolonomicPatch period hPeriod point)
    (selectedD9ThroatHolonomicCoordinate period hPeriod point)

/-- Complete local D9 field with every non-metric datum still explicit. -/
def d9LocalFieldFromGlobalTensorAtThroatPoint
    (fields : IndependentFields period hPeriod)
    (programVariation : IndependentFieldVariation period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (anchor : ThroatCover period hPeriod)
    (hPoint : point ∈ normalBundleBaseSet period hPeriod anchor)
    (ghost : CInfinityThroatGhost period hPeriod) :
    CompleteLocalField D9SquaredSpinorCoordinateFiber :=
  d9LocalFieldWithFullSymmetricMetric period hPeriod fields
    (d9CompleteLocalVariationFromGlobalTensorAtThroatPoint period hPeriod
      programVariation tensor point)
    sector column point displacement anchor hPoint ghost

/-- The automatically selected chart fills the D9 metric slot with exactly
the six spatial chart coefficients of the supplied global tensor. -/
theorem d9LocalField_globalTensorAtThroatPoint_metricPerturbation
    (fields : IndependentFields period hPeriod)
    (programVariation : IndependentFieldVariation period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (anchor : ThroatCover period hPeriod)
    (hPoint : point ∈ normalBundleBaseSet period hPeriod anchor)
    (ghost : CInfinityThroatGhost period hPeriod) :
    (d9LocalFieldFromGlobalTensorAtThroatPoint period hPeriod fields
      programVariation tensor sector column point displacement anchor hPoint
      ghost).bosonic.metricPerturbation =
      { xx := d9TensorChartCoefficient period hPeriod tensor
          (selectedD9ThroatHolonomicPatch period hPeriod point) 1 1
          (selectedD9ThroatHolonomicCoordinate period hPeriod point)
        yy := d9TensorChartCoefficient period hPeriod tensor
          (selectedD9ThroatHolonomicPatch period hPeriod point) 2 2
          (selectedD9ThroatHolonomicCoordinate period hPeriod point)
        zz := d9TensorChartCoefficient period hPeriod tensor
          (selectedD9ThroatHolonomicPatch period hPeriod point) 3 3
          (selectedD9ThroatHolonomicCoordinate period hPeriod point)
        xy := d9TensorChartCoefficient period hPeriod tensor
          (selectedD9ThroatHolonomicPatch period hPeriod point) 1 2
          (selectedD9ThroatHolonomicCoordinate period hPeriod point)
        xz := d9TensorChartCoefficient period hPeriod tensor
          (selectedD9ThroatHolonomicPatch period hPeriod point) 1 3
          (selectedD9ThroatHolonomicCoordinate period hPeriod point)
        yz := d9TensorChartCoefficient period hPeriod tensor
          (selectedD9ThroatHolonomicPatch period hPeriod point) 2 3
          (selectedD9ThroatHolonomicCoordinate period hPeriod point) } := by
  simpa [d9LocalFieldFromGlobalTensorAtThroatPoint,
    d9CompleteLocalVariationFromGlobalTensorAtThroatPoint] using
    (d9LocalField_tensorChartMetricPerturbation period hPeriod fields
      programVariation tensor
      (selectedD9ThroatHolonomicPatch period hPeriod point)
      (selectedD9ThroatHolonomicCoordinate period hPeriod point)
      sector column point displacement anchor hPoint ghost
      (selectedD9ThroatHolonomicPatch_coordinateMap period hPeriod point))

end
end P0EFTJanusD9CanonicalGlobalTensorHolonomicMetricCompletion4D
end JanusFormal
