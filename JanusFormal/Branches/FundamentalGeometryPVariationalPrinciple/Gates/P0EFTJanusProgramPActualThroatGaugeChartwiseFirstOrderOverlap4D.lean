import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeDifferentiatedOverlap4D

/-!
# Chartwise first-order overlap law for the actual throat gauge covector

In the extended throat chart centered at a point of a double centered-frame
overlap, the first derivative of the second representative is the Leibniz
derivative of the contragredient transition applied to the first
representative.

This is an explicit first-order law in one fixed base chart.  It does not
provide chart-independent jet descent, a second-order overlap law, a gauge
transformation law, normal geometry or a global Levi--Civita connection.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatGaugeChartwiseFirstOrderOverlap4D

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff RealInnerProductSpace Topology
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPActualThroatAbelianPotentialChartwiseSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatAbelianPotentialZeroOrderTrivializationOverlap4D
open P0EFTJanusProgramPActualThroatGaugeZeroOrderTransitionCocycle4D
open P0EFTJanusProgramPActualThroatGaugeZeroOrderOverlapDataSmoothness4D
open P0EFTJanusProgramPActualThroatGaugeDifferentiatedOverlap4D

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

/-! ## Fixed-chart representatives -/

/-- A centered-frame gauge covector read in the extended base chart centered
at `center`. -/
def throatGaugeCovectorCenteredChart
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2) (anchor center : EffectiveThroat period hPeriod) :
    ThroatCoverCoordinates → FramedCovector ThroatCoverCoordinates :=
  fun coordinate =>
    throatGaugeCovectorCoordinates period hPeriod potential component anchor
      ((extChartAt throatCoverModelWithCorners center).symm coordinate)

/-- The contragredient centered-frame transition read in the same extended
base chart centered at `center`. -/
def throatGaugeCovectorTransitionCenteredChart
    (firstAnchor secondAnchor center : EffectiveThroat period hPeriod) :
    ThroatCoverCoordinates →
      (FramedCovector ThroatCoverCoordinates →L[Real]
        FramedCovector ThroatCoverCoordinates) :=
  fun coordinate =>
    (throatGaugeCovectorTrivializationTransitionAt period hPeriod
      firstAnchor secondAnchor
      ((extChartAt throatCoverModelWithCorners center).symm coordinate) :
        FramedCovector ThroatCoverCoordinates →L[Real]
          FramedCovector ThroatCoverCoordinates)

/-! ## Explicit first-order transition law -/

/-- In the fixed chart centered at `current`, differentiation of the exact
overlap identity gives the full first-order Leibniz law.  The first summand
transports the derivative of the first representative; the second records
the variation of the frame transition itself. -/
theorem throatGaugeCovectorCenteredChart_fderiv_transition
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (firstAnchor secondAnchor current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatGaugeCenteredTrivializationOverlap period hPeriod
        firstAnchor secondAnchor) :
    fderiv Real
        (throatGaugeCovectorCenteredChart period hPeriod potential component
          secondAnchor current)
        (extChartAt throatCoverModelWithCorners current current) =
      (throatGaugeCovectorTrivializationTransitionAt period hPeriod
          firstAnchor secondAnchor current :
            FramedCovector ThroatCoverCoordinates →L[Real]
              FramedCovector ThroatCoverCoordinates).comp
        (fderiv Real
          (throatGaugeCovectorCenteredChart period hPeriod potential component
            firstAnchor current)
          (extChartAt throatCoverModelWithCorners current current)) +
      (fderiv Real
        (throatGaugeCovectorTransitionCenteredChart period hPeriod
          firstAnchor secondAnchor current)
        (extChartAt throatCoverModelWithCorners current current)).flip
          (throatGaugeCovectorCoordinates period hPeriod potential component
            firstAnchor current) := by
  let firstTrivialization :=
    trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) firstAnchor
  let secondTrivialization :=
    trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) secondAnchor
  let centerCoordinate :=
    extChartAt throatCoverModelWithCorners current current
  change
    fderiv Real
        (fun coordinate =>
          throatGaugeCovectorCoordinates period hPeriod potential component
            secondAnchor
            ((extChartAt throatCoverModelWithCorners current).symm coordinate))
        centerCoordinate =
      (throatGaugeCovectorTrivializationTransitionAt period hPeriod
          firstAnchor secondAnchor current :
            FramedCovector ThroatCoverCoordinates →L[Real]
              FramedCovector ThroatCoverCoordinates).comp
        (fderiv Real
          (fun coordinate =>
            throatGaugeCovectorCoordinates period hPeriod potential component
              firstAnchor
              ((extChartAt throatCoverModelWithCorners current).symm coordinate))
          centerCoordinate) +
      (fderiv Real
        (fun coordinate =>
          (throatGaugeCovectorTrivializationTransitionAt period hPeriod
            firstAnchor secondAnchor
            ((extChartAt throatCoverModelWithCorners current).symm coordinate) :
              FramedCovector ThroatCoverCoordinates →L[Real]
                FramedCovector ThroatCoverCoordinates))
        centerCoordinate).flip
          (throatGaugeCovectorCoordinates period hPeriod potential component
            firstAnchor current)
  have hOverlapOpen : IsOpen
      (throatGaugeCenteredTrivializationOverlap period hPeriod
        firstAnchor secondAnchor) := by
    exact firstTrivialization.open_baseSet.inter
      secondTrivialization.open_baseSet
  have hOverlapNhds :
      throatGaugeCenteredTrivializationOverlap period hPeriod
          firstAnchor secondAnchor ∈ 𝓝 current :=
    hOverlapOpen.mem_nhds hCurrent
  have hChartInverse :
      ContMDiffAt (modelWithCornersSelf Real ThroatCoverCoordinates)
        throatCoverModelWithCorners ∞
        (extChartAt throatCoverModelWithCorners current).symm
        centerCoordinate := by
    exact
      (contMDiffOn_extChartAt_symm
        (I := throatCoverModelWithCorners) (n := ∞) current).contMDiffAt
        ((isOpen_extChartAt_target current).mem_nhds
          (mem_extChartAt_target current))
  have hTransitionAt :
      ContMDiffAt throatCoverModelWithCorners
        (modelWithCornersSelf Real
          (FramedCovector ThroatCoverCoordinates →L[Real]
            FramedCovector ThroatCoverCoordinates)) ∞
        (fun point : EffectiveThroat period hPeriod =>
          (throatGaugeCovectorTrivializationTransitionAt period hPeriod
            firstAnchor secondAnchor point :
              FramedCovector ThroatCoverCoordinates →L[Real]
                FramedCovector ThroatCoverCoordinates)) current :=
    (throatGaugeCovectorTrivializationTransitionAt_contMDiffOn
      period hPeriod firstAnchor secondAnchor).contMDiffAt hOverlapNhds
  have hFirstAt :
      ContMDiffAt throatCoverModelWithCorners
        (modelWithCornersSelf Real
          (FramedCovector ThroatCoverCoordinates)) ∞
        (throatGaugeCovectorCoordinates period hPeriod potential component
          firstAnchor) current := by
    apply
      (throatGaugeCovectorCoordinates_contMDiffOn_baseSet
        period hPeriod potential component firstAnchor).contMDiffAt
    exact firstTrivialization.open_baseSet.mem_nhds hCurrent.1
  have hTransitionChart : DifferentiableAt Real
      (fun coordinate =>
        (throatGaugeCovectorTrivializationTransitionAt period hPeriod
          firstAnchor secondAnchor
          ((extChartAt throatCoverModelWithCorners current).symm coordinate) :
            FramedCovector ThroatCoverCoordinates →L[Real]
              FramedCovector ThroatCoverCoordinates)) centerCoordinate := by
    have hComposed := hTransitionAt.comp_of_eq hChartInverse
      (extChartAt_to_inv current)
    have hSmooth : ContMDiffAt
        (modelWithCornersSelf Real ThroatCoverCoordinates)
        (modelWithCornersSelf Real
          (FramedCovector ThroatCoverCoordinates →L[Real]
            FramedCovector ThroatCoverCoordinates)) ∞
        (fun coordinate =>
          (throatGaugeCovectorTrivializationTransitionAt period hPeriod
            firstAnchor secondAnchor
            ((extChartAt throatCoverModelWithCorners current).symm coordinate) :
              FramedCovector ThroatCoverCoordinates →L[Real]
                FramedCovector ThroatCoverCoordinates)) centerCoordinate := by
      simpa only [Function.comp_def] using hComposed
    exact hSmooth.contDiffAt.differentiableAt (by simp)
  have hFirstChart : DifferentiableAt Real
      (fun coordinate =>
        throatGaugeCovectorCoordinates period hPeriod potential component
          firstAnchor
          ((extChartAt throatCoverModelWithCorners current).symm coordinate))
      centerCoordinate := by
    have hComposed := hFirstAt.comp_of_eq hChartInverse
      (extChartAt_to_inv current)
    have hSmooth : ContMDiffAt
        (modelWithCornersSelf Real ThroatCoverCoordinates)
        (modelWithCornersSelf Real
          (FramedCovector ThroatCoverCoordinates)) ∞
        (fun coordinate =>
          throatGaugeCovectorCoordinates period hPeriod potential component
            firstAnchor
            ((extChartAt throatCoverModelWithCorners current).symm coordinate))
        centerCoordinate := by
      simpa only [Function.comp_def] using hComposed
    exact hSmooth.contDiffAt.differentiableAt (by simp)
  have hProduct := fderiv_clm_apply hTransitionChart hFirstChart
  have hInverseEventually :
      (extChartAt throatCoverModelWithCorners current).symm ⁻¹'
          throatGaugeCenteredTrivializationOverlap period hPeriod
            firstAnchor secondAnchor ∈ 𝓝 centerCoordinate := by
    apply hChartInverse.continuousAt.preimage_mem_nhds
    simpa only [centerCoordinate, extChartAt_to_inv] using hOverlapNhds
  have hEventually :
      (fun coordinate =>
        (throatGaugeCovectorTrivializationTransitionAt period hPeriod
          firstAnchor secondAnchor
          ((extChartAt throatCoverModelWithCorners current).symm coordinate) :
            FramedCovector ThroatCoverCoordinates →L[Real]
              FramedCovector ThroatCoverCoordinates)
          (throatGaugeCovectorCoordinates period hPeriod potential component
            firstAnchor
            ((extChartAt throatCoverModelWithCorners current).symm
              coordinate))) =ᶠ[𝓝 centerCoordinate]
        (fun coordinate =>
          throatGaugeCovectorCoordinates period hPeriod potential component
            secondAnchor
            ((extChartAt throatCoverModelWithCorners current).symm
              coordinate)) := by
    filter_upwards [hInverseEventually] with coordinate hCoordinate
    simpa only [throatGaugeCovectorCoordinatesTransported,
      throatGaugeCovectorTrivializationTransitionAt,
      ContinuousLinearEquiv.coe_coe] using
      (throatGaugeCovectorCoordinatesTransported_eq period hPeriod potential
        component firstAnchor secondAnchor
        ((extChartAt throatCoverModelWithCorners current).symm coordinate)
        hCoordinate)
  calc
    fderiv Real
        (fun coordinate =>
          throatGaugeCovectorCoordinates period hPeriod potential component
            secondAnchor
            ((extChartAt throatCoverModelWithCorners current).symm coordinate))
        centerCoordinate =
      fderiv Real
        (fun coordinate =>
          (throatGaugeCovectorTrivializationTransitionAt period hPeriod
            firstAnchor secondAnchor
            ((extChartAt throatCoverModelWithCorners current).symm coordinate) :
              FramedCovector ThroatCoverCoordinates →L[Real]
                FramedCovector ThroatCoverCoordinates)
            (throatGaugeCovectorCoordinates period hPeriod potential component
              firstAnchor
              ((extChartAt throatCoverModelWithCorners current).symm
                coordinate))) centerCoordinate := by
      exact hEventually.fderiv_eq.symm
    _ = _ := by
      simpa only [centerCoordinate, extChartAt_to_inv] using hProduct

end
end P0EFTJanusProgramPActualThroatGaugeChartwiseFirstOrderOverlap4D
end JanusFormal
