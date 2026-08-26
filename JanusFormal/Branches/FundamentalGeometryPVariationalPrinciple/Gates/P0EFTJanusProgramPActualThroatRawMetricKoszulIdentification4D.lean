import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatTangentialConnectionQuadratic4D

/-!
# Pointwise raw-metric identification of the actual throat Koszul candidate

The actual induced throat metric remains symmetric after transport to the
fixed Euclidean frame.  Its raw transported first derivative is symmetric in
the two metric slots because the underlying genuine tensor germ is symmetric
on a neighborhood of the selected point.  Thus the explicit symmetrization
used by the existing pointwise Koszul candidate is the identity on this
actual derivative, and the candidate satisfies the Koszul formula written
directly with the raw derivative.

All statements are pointwise in the selected throat chart and fixed frame.
This gate proves no chart-overlap law, smooth global connection, torsion or
metric-compatibility theorem on the throat, and no identification with a
global Levi--Civita connection.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatRawMetricKoszulIdentification4D

set_option autoImplicit false
noncomputable section

open Filter
open scoped Manifold ContDiff InnerProductSpace RealInnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPGlobalMetricChartwiseSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatAbelianPotentialChartwiseSecondOrderJetExtraction4D
open P0EFTJanusRieszShapeOperatorContinuousStructuredJetReduction
open P0EFTJanusEuclideanMetricKoszulConnection
open P0EFTJanusEuclideanKoszulConnectionExistence
open P0EFTJanusProgramPActualThroatTangentialConnectionQuadratic4D

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

local instance throatMetricTensorNormedAddCommGroup :
    NormedAddCommGroup
      (FramedCovariantTwoTensor ThroatCoverCoordinates) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance throatMetricTensorNormedSpace :
    NormedSpace Real (FramedCovariantTwoTensor ThroatCoverCoordinates) :=
  ContinuousLinearMap.toNormedSpace

local instance euclideanCovectorNormedAddCommGroup :
    NormedAddCommGroup (EuclideanR3 →L[Real] Real) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance euclideanCovectorNormedSpace :
    NormedSpace Real (EuclideanR3 →L[Real] Real) :=
  ContinuousLinearMap.toNormedSpace

local instance euclideanMetricTensorNormedAddCommGroup :
    NormedAddCommGroup (ContinuousMetricTensor EuclideanR3) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance euclideanMetricTensorNormedSpace :
    NormedSpace Real (ContinuousMetricTensor EuclideanR3) :=
  ContinuousLinearMap.toNormedSpace

local instance euclideanMetricDerivativeNormedAddCommGroup :
    NormedAddCommGroup
      (ContinuousMetricDerivativeTensor (Model := EuclideanR3)) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance euclideanMetricDerivativeNormedSpace :
    NormedSpace Real
      (ContinuousMetricDerivativeTensor (Model := EuclideanR3)) :=
  ContinuousLinearMap.toNormedSpace

private theorem fderiv_framedCovariantTwoTensor_apply_apply
    (field : ThroatCoverCoordinates →
      FramedCovariantTwoTensor ThroatCoverCoordinates)
    (base direction first second : ThroatCoverCoordinates)
    (hField : DifferentiableAt Real field base) :
    fderiv Real (fun point => field point first second) base direction =
      fderiv Real field base direction first second := by
  have hFirst := fderiv_clm_apply hField
    (differentiableAt_const (c := first))
  have hFirstDiff : DifferentiableAt Real
      (fun point => field point first) base :=
    hField.clm_apply (differentiableAt_const (c := first))
  have hSecond := fderiv_clm_apply hFirstDiff
    (differentiableAt_const (c := second))
  rw [hSecond, hFirst]
  simp

private theorem throatTensorChartGerm_eventually_symmetric
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (anchor : EffectiveThroat period hPeriod)
    (first second : ThroatCoverCoordinates) :
    (fun coordinate =>
      throatTensorChartGerm period hPeriod tensor anchor coordinate first second)
      =ᶠ[nhds (extChartAt throatCoverModelWithCorners anchor anchor)]
    (fun coordinate =>
      throatTensorChartGerm period hPeriod tensor anchor coordinate second first) := by
  let inverse := (extChartAt throatCoverModelWithCorners anchor).symm
  have hInverseContinuous : ContinuousAt inverse
      (extChartAt throatCoverModelWithCorners anchor anchor) :=
    continuousAt_extChartAt_symm anchor
  have hInverseAt :
      inverse (extChartAt throatCoverModelWithCorners anchor anchor) = anchor := by
    dsimp only [inverse]
    rw [extChartAt_to_inv]
  have hInverseTendsto : Tendsto inverse
      (nhds (extChartAt throatCoverModelWithCorners anchor anchor))
      (nhds anchor) := by
    have hTendsto := hInverseContinuous
    change Tendsto inverse
      (nhds (extChartAt throatCoverModelWithCorners anchor anchor))
      (nhds (inverse
        (extChartAt throatCoverModelWithCorners anchor anchor))) at hTendsto
    rw [hInverseAt] at hTendsto
    exact hTendsto
  have hCurrent : ∀ᶠ current in nhds anchor,
      current ∈
        (trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) anchor).baseSet :=
    (trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) anchor).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) anchor)
  filter_upwards [hInverseTendsto.eventually hCurrent] with coordinate hCoordinate
  change throatTensorCoordinates period hPeriod tensor anchor
      (inverse coordinate) first second =
    throatTensorCoordinates period hPeriod tensor anchor
      (inverse coordinate) second first
  unfold throatTensorCoordinates
  rw [inCoordinates_apply_eq₂ hCoordinate hCoordinate (Set.mem_univ _),
    inCoordinates_apply_eq₂ hCoordinate hCoordinate (Set.mem_univ _)]
  apply congrArg
    ((trivializationAt Real
      (fun _ : EffectiveThroat period hPeriod => Real) anchor).linearMapAt
        Real (inverse coordinate))
  exact tensor.symmetric _ _ _

private theorem throatTensorChartGerm_fderiv_symmetric
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (anchor : EffectiveThroat period hPeriod)
    (direction first second : ThroatCoverCoordinates) :
    fderiv Real (throatTensorChartGerm period hPeriod tensor anchor)
        (extChartAt throatCoverModelWithCorners anchor anchor)
        direction first second =
      fderiv Real (throatTensorChartGerm period hPeriod tensor anchor)
        (extChartAt throatCoverModelWithCorners anchor anchor)
        direction second first := by
  have hField : DifferentiableAt Real
      (throatTensorChartGerm period hPeriod tensor anchor)
      (extChartAt throatCoverModelWithCorners anchor anchor) :=
    (throatTensorChartGerm_contDiffAt_two
      period hPeriod tensor anchor).differentiableAt (by simp)
  have hSymmetric := throatTensorChartGerm_eventually_symmetric
    period hPeriod tensor anchor first second
  calc
    fderiv Real (throatTensorChartGerm period hPeriod tensor anchor)
        (extChartAt throatCoverModelWithCorners anchor anchor)
        direction first second =
      fderiv Real
        (fun coordinate => throatTensorChartGerm
          period hPeriod tensor anchor coordinate first second)
        (extChartAt throatCoverModelWithCorners anchor anchor) direction :=
      (fderiv_framedCovariantTwoTensor_apply_apply
        (throatTensorChartGerm period hPeriod tensor anchor)
        (extChartAt throatCoverModelWithCorners anchor anchor)
        direction first second hField).symm
    _ = fderiv Real
        (fun coordinate => throatTensorChartGerm
          period hPeriod tensor anchor coordinate second first)
        (extChartAt throatCoverModelWithCorners anchor anchor) direction := by
      exact congrArg (fun derivative => derivative direction)
        (hSymmetric.fderiv_eq (𝕜 := Real))
    _ = fderiv Real (throatTensorChartGerm period hPeriod tensor anchor)
        (extChartAt throatCoverModelWithCorners anchor anchor)
        direction second first :=
      fderiv_framedCovariantTwoTensor_apply_apply
        (throatTensorChartGerm period hPeriod tensor anchor)
        (extChartAt throatCoverModelWithCorners anchor anchor)
        direction second first hField

/-! ## Symmetry of the transported actual metric one-jet -/

/-- The actual induced metric value remains symmetric in the fixed Euclidean
frame. -/
theorem globalGaugeFixedThroatMetricEuclideanValueAt_symmetric
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (base : EffectiveThroat period hPeriod) (sector : Sector)
    (first second : EuclideanR3) :
    globalGaugeFixedThroatMetricEuclideanValueAt
        period hPeriod configuration base sector first second =
      globalGaugeFixedThroatMetricEuclideanValueAt
        period hPeriod configuration base sector second first := by
  simp only [globalGaugeFixedThroatMetricEuclideanValueAt_apply]
  exact globalGaugeFixedThroatMetricSecondOrderJetAt_value_symmetric
    period hPeriod configuration sector base
      (throatRadialReferenceEquiv first)
      (throatRadialReferenceEquiv second)

/-- The raw transported first derivative of the actual induced metric is
symmetric in its two metric slots. -/
theorem globalGaugeFixedThroatMetricEuclideanFirstDerivativeAt_symmetric
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (base : EffectiveThroat period hPeriod) (sector : Sector)
    (direction first second : EuclideanR3) :
    globalGaugeFixedThroatMetricEuclideanFirstDerivativeAt
        period hPeriod configuration base sector direction first second =
      globalGaugeFixedThroatMetricEuclideanFirstDerivativeAt
        period hPeriod configuration base sector direction second first := by
  simp only [globalGaugeFixedThroatMetricEuclideanFirstDerivativeAt_apply,
    globalGaugeFixedThroatMetricSecondOrderJetAt_firstDerivative]
  exact throatTensorChartGerm_fderiv_symmetric period hPeriod
    (globalGaugeFixedInducedMetricBySector
      period hPeriod configuration sector) base
    (throatRadialReferenceEquiv direction)
    (throatRadialReferenceEquiv first)
    (throatRadialReferenceEquiv second)

/-- Explicit symmetrization fixes the raw transported actual metric
derivative. -/
theorem symmetrized_globalGaugeFixedThroatMetricEuclideanFirstDerivativeAt
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (base : EffectiveThroat period hPeriod) (sector : Sector) :
    symmetrizedThroatMetricEuclideanDerivative
        (globalGaugeFixedThroatMetricEuclideanFirstDerivativeAt
          period hPeriod configuration base sector) =
      globalGaugeFixedThroatMetricEuclideanFirstDerivativeAt
        period hPeriod configuration base sector := by
  apply ContinuousLinearMap.ext
  intro direction
  apply ContinuousLinearMap.ext
  intro first
  apply ContinuousLinearMap.ext
  intro second
  simp only [symmetrizedThroatMetricEuclideanDerivative, smul_apply,
    add_apply, swapSecondThirdCLM_euclidean_apply]
  rw [globalGaugeFixedThroatMetricEuclideanFirstDerivativeAt_symmetric
    period hPeriod configuration base sector direction second first]
  ring

/-! ## Raw pointwise Koszul identification -/

/-- The existing actual throat candidate obeys the pointwise Koszul identity
with the raw transported metric derivative.  This is an identification with
the raw Koszul formula at the selected point, not with a global
Levi--Civita connection. -/
theorem globalCandidateAActualThroatTangentialConnectionQuadraticAt_raw_koszul
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (base : EffectiveThroat period hPeriod)
    (hTransverse : ∀ sector,
      HasNoTangentialRadical period hPeriod
        (globalGaugeFixedBulkMetricBySector
          period hPeriod configuration sector))
    (sector : Sector) (first second test : EuclideanR3) :
    let metric := globalGaugeFixedThroatMetricEuclideanValueAt
      period hPeriod configuration base sector
    let derivative := globalGaugeFixedThroatMetricEuclideanFirstDerivativeAt
      period hPeriod configuration base sector
    2 * metric
        (globalCandidateAActualThroatTangentialConnectionQuadraticAt
          period hPeriod configuration base hTransverse sector first second) test =
      derivative first second test + derivative second first test -
        derivative test first second := by
  dsimp only
  have hKoszul :=
    globalCandidateAActualThroatTangentialConnectionQuadraticAt_koszul
      period hPeriod configuration base hTransverse sector first second test
  dsimp only at hKoszul
  rw [symmetrized_globalGaugeFixedThroatMetricEuclideanFirstDerivativeAt
    period hPeriod configuration base sector] at hKoszul
  exact hKoszul

end
end P0EFTJanusProgramPActualThroatRawMetricKoszulIdentification4D
end JanusFormal
