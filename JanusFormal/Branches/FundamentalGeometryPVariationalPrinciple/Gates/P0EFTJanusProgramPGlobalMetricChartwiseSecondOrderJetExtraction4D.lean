import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPhysicalSecondOrderJetChartwiseExtraction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusStableRadialReferenceConjugacy4D

/-!
# Chartwise second jets of the actual Program-P metrics

This gate extracts both Candidate-A bulk metrics in a supplied holonomic
chart and both induced throat metrics in the tangent-bundle trivialization at
an actual throat point.  The results have exactly the metric-slot types of the
physical second-order carrier.

The constructions are local.  No overlap law, global jet bundle,
nondegeneracy of the throat trace, or invariant-theory exhaustion is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalMetricChartwiseSecondOrderJetExtraction4D

set_option autoImplicit false
noncomputable section

open Set
open scoped Manifold ContDiff Matrix.Norms.Frobenius
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusStableRadialReferenceConjugacy4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPPhysicalSecondOrderJetChartwiseExtraction4D

variable (period : Real) (hPeriod : period ≠ 0)

abbrev HolonomicVector4 :=
  P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

abbrev HolonomicMatrix4 :=
  P0EFTJanusMetricCoupledScalarMatterJetVariation.Matrix4

local instance holonomicMatrix4NormedAddCommGroup :
    NormedAddCommGroup HolonomicMatrix4 :=
  Matrix.frobeniusNormedAddCommGroup

local instance holonomicMatrix4NormedSpace :
    NormedSpace Real HolonomicMatrix4 :=
  Matrix.frobeniusNormedSpace

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev EffectiveThroat := MappingTorus (ThroatData period hPeriod)

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-! ## Bulk metric jets -/

/-- The two actual bulk metrics owned by a gauge-fixed configuration. -/
def globalGaugeFixedBulkMetricBySector
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) :
    Sector → SmoothGeneralLorentzMetric period hPeriod
  | .plus => configuration.physical.geometry.plusMetric
  | .minus => configuration.physical.geometry.minusMetric

/-- Fixed continuous-linear identification between the carrier's split cover
coordinates and the `Fin 4` holonomic coordinate model. -/
def coverToHolonomicEquiv :
    CoverCoordinates ≃L[Real] HolonomicVector4 :=
  stableRadialReferenceEquiv.symm.trans
    (EuclideanSpace.equiv (Fin 4) Real)

private def coverMetricFormFromMatrix
    (matrix : HolonomicMatrix4) :
    LinearMap.BilinForm Real CoverCoordinates :=
  (Matrix.toBilin' matrix).comp
    coverToHolonomicEquiv.toLinearMap
    coverToHolonomicEquiv.toLinearMap

/-- Fixed linear transport from holonomic `R^4` matrix coefficients to the
cover-coordinate covariant-tensor model used by the physical carrier. -/
def bulkMetricMatrixToFramedTensor :
    HolonomicMatrix4 →L[Real]
      FramedCovariantTwoTensor CoverCoordinates :=
  LinearMap.toContinuousLinearMap
    { toFun := fun matrix =>
        (coverMetricFormFromMatrix matrix).toContinuousBilinearMap
      map_add' := by
        intro first second
        apply ContinuousLinearMap.ext
        intro left
        apply ContinuousLinearMap.ext
        intro right
        simp [coverMetricFormFromMatrix, Matrix.toBilin'_apply]
      map_smul' := by
        intro scalar matrix
        apply ContinuousLinearMap.ext
        intro left
        apply ContinuousLinearMap.ext
        intro right
        simp [coverMetricFormFromMatrix, Matrix.toBilin'_apply] }

@[simp]
theorem bulkMetricMatrixToFramedTensor_apply
    (matrix : HolonomicMatrix4) (first second : CoverCoordinates) :
    bulkMetricMatrixToFramedTensor matrix first second =
      Matrix.toBilin' matrix
        (coverToHolonomicEquiv first)
        (coverToHolonomicEquiv second) :=
  rfl

/-- One actual bulk metric matrix in a supplied holonomic chart, with the
chart coordinates transported from the carrier's cover-coordinate model. -/
def globalGaugeFixedBulkMetricMatrixChartGerm
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    CoverCoordinates → HolonomicMatrix4 :=
  fun coordinate =>
    localMetricMatrix period hPeriod
      (globalGaugeFixedBulkMetricBySector period hPeriod configuration sector)
      patch (coverToHolonomicEquiv coordinate)

theorem globalGaugeFixedBulkMetricMatrixChartGerm_contDiff
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    ContDiff Real ∞
      (globalGaugeFixedBulkMetricMatrixChartGerm
        period hPeriod configuration sector patch) := by
  exact
    (localMetricMatrix_contDiff period hPeriod
      (globalGaugeFixedBulkMetricBySector period hPeriod configuration sector)
      patch).comp coverToHolonomicEquiv.contDiff

/-- One actual bulk metric expressed in the carrier's covariant-tensor model. -/
def globalGaugeFixedBulkMetricChartGerm
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    CoverCoordinates → FramedCovariantTwoTensor CoverCoordinates :=
  fun coordinate =>
    bulkMetricMatrixToFramedTensor
      (globalGaugeFixedBulkMetricMatrixChartGerm
        period hPeriod configuration sector patch coordinate)

/-- Matrix-valued second jet before transport to the carrier tensor model. -/
def globalGaugeFixedBulkMetricMatrixSecondOrderJetAt
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoverCoordinates) :
    FramedSecondOrderJet CoverCoordinates HolonomicMatrix4 :=
  chartwiseSecondOrderJetAt
    (globalGaugeFixedBulkMetricMatrixChartGerm
      period hPeriod configuration sector patch)
    coordinate
    ((globalGaugeFixedBulkMetricMatrixChartGerm_contDiff
      period hPeriod configuration sector patch).contDiffAt.of_le (by
        show (2 : ℕ∞ω) ≤ ∞
        exact WithTop.coe_le_coe.mpr le_top))

/-- Apply the fixed matrix-to-tensor map at all three levels of a framed
second jet. -/
private def bulkMetricMatrixSecondOrderJetToFramedTensor
    (jet : FramedSecondOrderJet CoverCoordinates HolonomicMatrix4) :
    FramedSecondOrderJet CoverCoordinates
      (FramedCovariantTwoTensor CoverCoordinates) where
  value := bulkMetricMatrixToFramedTensor jet.value
  firstDerivative :=
    bulkMetricMatrixToFramedTensor.comp jet.firstDerivative
  secondDerivative :=
    ((ContinuousLinearMap.compL Real CoverCoordinates HolonomicMatrix4
      (FramedCovariantTwoTensor CoverCoordinates))
        bulkMetricMatrixToFramedTensor).comp jet.secondDerivative
  secondDerivative_symmetric := by
    intro first second
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.compL_apply]
    rw [jet.secondDerivative_symmetric first second]

/-- Actual second jet of one Candidate-A metric in a supplied bulk chart. -/
def globalGaugeFixedBulkMetricSecondOrderJetAt
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoverCoordinates) :
    FramedSecondOrderJet CoverCoordinates
      (FramedCovariantTwoTensor CoverCoordinates) :=
  bulkMetricMatrixSecondOrderJetToFramedTensor
    (globalGaugeFixedBulkMetricMatrixSecondOrderJetAt
      period hPeriod configuration sector patch coordinate)

@[simp]
theorem globalGaugeFixedBulkMetricSecondOrderJetAt_value_apply
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate first second : CoverCoordinates) :
    (globalGaugeFixedBulkMetricSecondOrderJetAt period hPeriod configuration
      sector patch coordinate).value first second =
      Matrix.toBilin'
        (localMetricMatrix period hPeriod
          (globalGaugeFixedBulkMetricBySector
            period hPeriod configuration sector)
          patch (coverToHolonomicEquiv coordinate))
        (coverToHolonomicEquiv first)
        (coverToHolonomicEquiv second) :=
  rfl

@[simp]
theorem globalGaugeFixedBulkMetricSecondOrderJetAt_firstDerivative
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoverCoordinates) :
    (globalGaugeFixedBulkMetricSecondOrderJetAt period hPeriod configuration
      sector patch coordinate).firstDerivative =
      bulkMetricMatrixToFramedTensor.comp
        (fderiv Real
          (globalGaugeFixedBulkMetricMatrixChartGerm
            period hPeriod configuration sector patch) coordinate) :=
  rfl

theorem globalGaugeFixedBulkMetricSecondOrderJetAt_secondDerivative_symmetric
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate first second : CoverCoordinates) :
    (globalGaugeFixedBulkMetricSecondOrderJetAt period hPeriod configuration
      sector patch coordinate).secondDerivative first second =
      (globalGaugeFixedBulkMetricSecondOrderJetAt period hPeriod configuration
        sector patch coordinate).secondDerivative second first :=
  (globalGaugeFixedBulkMetricSecondOrderJetAt period hPeriod configuration
    sector patch coordinate).secondDerivative_symmetric first second

/-- The actual quotient point represented by the transported bulk chart
coordinate. -/
def globalGaugeFixedBulkMetricJetPoint
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoverCoordinates) :
    ProgramPBulkJetBase period hPeriod :=
  patch.coordinateMap (coverToHolonomicEquiv coordinate)

/-! ## Induced throat metric jets -/

/-- Local tensor coefficients in the tangent-bundle trivialization centered
at `anchor`. -/
def throatTensorCoordinates
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (anchor current : EffectiveThroat period hPeriod) :
    FramedCovariantTwoTensor ThroatCoverCoordinates :=
  ContinuousLinearMap.inCoordinates ThroatCoverCoordinates
    (ThroatTangentFiber period hPeriod)
    (ThroatCoverCoordinates →L[Real] Real)
    (ThroatCotangentFiber period hPeriod)
    anchor current anchor current (tensor.tensor current)

theorem throatTensorCoordinates_contMDiffAt
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (anchor : EffectiveThroat period hPeriod) :
    ContMDiffAt throatCoverModelWithCorners
      𝓘(Real, FramedCovariantTwoTensor ThroatCoverCoordinates) ∞
      (throatTensorCoordinates period hPeriod tensor anchor) anchor := by
  have hSmooth := tensor.tensor.contMDiff anchor
  rw [contMDiffAt_hom_bundle] at hSmooth
  exact hSmooth.2

/-- The intrinsic throat tensor in the extended source chart and the tangent
trivialization centered at `anchor`. -/
def throatTensorChartGerm
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (anchor : EffectiveThroat period hPeriod) :
    ThroatCoverCoordinates →
      FramedCovariantTwoTensor ThroatCoverCoordinates :=
  throatTensorCoordinates period hPeriod tensor anchor ∘
    (extChartAt throatCoverModelWithCorners anchor).symm

theorem throatTensorChartGerm_contDiffAt_two
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (anchor : EffectiveThroat period hPeriod) :
    ContDiffAt Real 2 (throatTensorChartGerm period hPeriod tensor anchor)
      (extChartAt throatCoverModelWithCorners anchor anchor) := by
  have hCoordinates : ContMDiffAt throatCoverModelWithCorners
      𝓘(Real, FramedCovariantTwoTensor ThroatCoverCoordinates) 2
      (throatTensorCoordinates period hPeriod tensor anchor) anchor :=
    (throatTensorCoordinates_contMDiffAt
      period hPeriod tensor anchor).of_le (by
        show (2 : ℕ∞ω) ≤ ∞
        exact WithTop.coe_le_coe.mpr le_top)
  have hSource := (contMDiffAt_iff_source).mp hCoordinates
  have hRange : Set.range throatCoverModelWithCorners = Set.univ := by
    ext coordinate
    simp
  rw [hRange, contMDiffWithinAt_univ] at hSource
  exact hSource.contDiffAt

@[simp]
theorem throatTensorChartGerm_center_apply
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (anchor : EffectiveThroat period hPeriod)
    (first second : ThroatCoverCoordinates) :
    throatTensorChartGerm period hPeriod tensor anchor
        (extChartAt throatCoverModelWithCorners anchor anchor) first second =
      tensor.tensor anchor
        ((trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) anchor).symm anchor first)
        ((trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) anchor).symm anchor second) := by
  have hAnchor : anchor ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) anchor).baseSet :=
    mem_baseSet_trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) anchor
  unfold throatTensorChartGerm
  rw [Function.comp_apply, extChartAt_to_inv]
  unfold throatTensorCoordinates
  rw [inCoordinates_apply_eq₂ hAnchor hAnchor (Set.mem_univ _)]
  simp

/-- The two actual induced throat tensors owned by the configuration. -/
def globalGaugeFixedInducedMetricBySector
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) :
    Sector → SmoothSymmetricThroatCovariantTwoTensor period hPeriod
  | .plus =>
      generalLorentzMetricThroatTrace period hPeriod
        configuration.physical.geometry.plusMetric
  | .minus =>
      generalLorentzMetricThroatTrace period hPeriod
        configuration.physical.geometry.minusMetric

/-- Actual second jet of one induced Candidate-A metric at a throat point. -/
def globalGaugeFixedThroatMetricSecondOrderJetAt
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector)
    (anchor : EffectiveThroat period hPeriod) :
    FramedSecondOrderJet ThroatCoverCoordinates
      (FramedCovariantTwoTensor ThroatCoverCoordinates) :=
  chartwiseSecondOrderJetAt
    (throatTensorChartGerm period hPeriod
      (globalGaugeFixedInducedMetricBySector
        period hPeriod configuration sector) anchor)
    (extChartAt throatCoverModelWithCorners anchor anchor)
    (throatTensorChartGerm_contDiffAt_two period hPeriod
      (globalGaugeFixedInducedMetricBySector
        period hPeriod configuration sector) anchor)

@[simp]
theorem globalGaugeFixedThroatMetricSecondOrderJetAt_value_apply
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector)
    (anchor : EffectiveThroat period hPeriod)
    (first second : ThroatCoverCoordinates) :
    (globalGaugeFixedThroatMetricSecondOrderJetAt period hPeriod configuration
      sector anchor).value first second =
      (globalGaugeFixedInducedMetricBySector
        period hPeriod configuration sector).tensor anchor
        ((trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) anchor).symm anchor first)
        ((trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) anchor).symm anchor second) := by
  rw [globalGaugeFixedThroatMetricSecondOrderJetAt,
    chartwiseSecondOrderJetAt_value,
    throatTensorChartGerm_center_apply]

theorem globalGaugeFixedThroatMetricSecondOrderJetAt_value_symmetric
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector)
    (anchor : EffectiveThroat period hPeriod)
    (first second : ThroatCoverCoordinates) :
    (globalGaugeFixedThroatMetricSecondOrderJetAt period hPeriod configuration
      sector anchor).value first second =
      (globalGaugeFixedThroatMetricSecondOrderJetAt period hPeriod configuration
        sector anchor).value second first := by
  rw [globalGaugeFixedThroatMetricSecondOrderJetAt_value_apply,
    globalGaugeFixedThroatMetricSecondOrderJetAt_value_apply]
  exact (globalGaugeFixedInducedMetricBySector
    period hPeriod configuration sector).symmetric _ _ _

@[simp]
theorem globalGaugeFixedThroatMetricSecondOrderJetAt_firstDerivative
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector)
    (anchor : EffectiveThroat period hPeriod) :
    (globalGaugeFixedThroatMetricSecondOrderJetAt period hPeriod configuration
      sector anchor).firstDerivative =
      fderiv Real
        (throatTensorChartGerm period hPeriod
          (globalGaugeFixedInducedMetricBySector
            period hPeriod configuration sector) anchor)
        (extChartAt throatCoverModelWithCorners anchor anchor) :=
  rfl

theorem globalGaugeFixedThroatMetricSecondOrderJetAt_secondDerivative_symmetric
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector)
    (anchor : EffectiveThroat period hPeriod)
    (first second : ThroatCoverCoordinates) :
    (globalGaugeFixedThroatMetricSecondOrderJetAt period hPeriod configuration
      sector anchor).secondDerivative first second =
      (globalGaugeFixedThroatMetricSecondOrderJetAt period hPeriod configuration
        sector anchor).secondDerivative second first :=
  (globalGaugeFixedThroatMetricSecondOrderJetAt period hPeriod configuration
    sector anchor).secondDerivative_symmetric first second

end
end P0EFTJanusProgramPGlobalMetricChartwiseSecondOrderJetExtraction4D
end JanusFormal
