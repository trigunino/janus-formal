import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeChartwiseFirstOrderOverlap4D

/-!
# First-order overlap law in the actual throat gauge jet carrier

The tangent-frame anchor and the center of the base chart are separated.  At
every point in the frame base set this gives the genuine chartwise second-order
jet carrier, and its `firstDerivative` satisfies the explicit frame-transition
law proved in the preceding gate.

No transformation law for `secondDerivative`, chart-independent jet descent,
gauge transformation, normal geometry or global connection is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatGaugeChartwiseFirstOrderJetOverlap4D

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff RealInnerProductSpace
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPPhysicalSecondOrderJetChartwiseExtraction4D
open P0EFTJanusProgramPActualThroatAbelianPotentialChartwiseSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatGaugeDifferentiatedOverlap4D
open P0EFTJanusProgramPActualThroatGaugeZeroOrderTransitionCocycle4D
open P0EFTJanusProgramPActualThroatGaugeZeroOrderOverlapDataSmoothness4D
open P0EFTJanusProgramPActualThroatGaugeChartwiseFirstOrderOverlap4D

variable (period : Real) (hPeriod : period ≠ 0)
variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*}
variable [Fintype NonNullFace] [Fintype NullFace]

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-! ## A frame anchor independent of the base-chart center -/

/-- The representative in the frame centered at `frameAnchor` is `C²` in the
extended base chart centered at any `current` in that frame's base set. -/
theorem throatGaugeCovectorCenteredChart_contDiffAt_two
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (frameAnchor current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) frameAnchor).baseSet) :
    ContDiffAt Real 2
      (throatGaugeCovectorCenteredChart period hPeriod potential component
        frameAnchor current)
      (extChartAt throatCoverModelWithCorners current current) := by
  change ContDiffAt Real 2
    (fun coordinate =>
      throatGaugeCovectorCoordinates period hPeriod potential component
        frameAnchor
        ((extChartAt throatCoverModelWithCorners current).symm coordinate))
    (extChartAt throatCoverModelWithCorners current current)
  have hCoordinates : ContMDiffAt throatCoverModelWithCorners
      (modelWithCornersSelf Real
        (FramedCovector ThroatCoverCoordinates)) 2
      (throatGaugeCovectorCoordinates period hPeriod potential component
        frameAnchor) current := by
    apply
      ((throatGaugeCovectorCoordinates_contMDiffOn_baseSet
        period hPeriod potential component frameAnchor).contMDiffAt
          ((trivializationAt ThroatCoverCoordinates
            (ThroatTangentFiber period hPeriod) frameAnchor).open_baseSet.mem_nhds
              hCurrent)).of_le
    show (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω)
    exact WithTop.coe_le_coe.mpr le_top
  have hSource := (contMDiffAt_iff_source).mp hCoordinates
  have hRange : Set.range throatCoverModelWithCorners = Set.univ := by
    ext coordinate
    simp
  rw [hRange, contMDiffWithinAt_univ] at hSource
  exact hSource.contDiffAt

/-- The genuine value, first derivative and symmetric second derivative of the
`frameAnchor` representative in the base chart centered at `current`. -/
def throatGaugeCovectorSecondOrderJetInFrameAt
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (frameAnchor current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) frameAnchor).baseSet) :
    FramedSecondOrderJet ThroatCoverCoordinates
      (FramedCovector ThroatCoverCoordinates) :=
  chartwiseSecondOrderJetAt
    (throatGaugeCovectorCenteredChart period hPeriod potential component
      frameAnchor current)
    (extChartAt throatCoverModelWithCorners current current)
    (throatGaugeCovectorCenteredChart_contDiffAt_two period hPeriod potential
      component frameAnchor current hCurrent)

@[simp]
theorem throatGaugeCovectorSecondOrderJetInFrameAt_value
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (frameAnchor current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) frameAnchor).baseSet) :
    (throatGaugeCovectorSecondOrderJetInFrameAt period hPeriod potential
      component frameAnchor current hCurrent).value =
      throatGaugeCovectorCoordinates period hPeriod potential component
        frameAnchor current := by
  rw [throatGaugeCovectorSecondOrderJetInFrameAt,
    chartwiseSecondOrderJetAt_value]
  simp only [throatGaugeCovectorCenteredChart, extChartAt_to_inv]

@[simp]
theorem throatGaugeCovectorSecondOrderJetInFrameAt_firstDerivative
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (frameAnchor current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) frameAnchor).baseSet) :
    (throatGaugeCovectorSecondOrderJetInFrameAt period hPeriod potential
      component frameAnchor current hCurrent).firstDerivative =
      fderiv Real
        (throatGaugeCovectorCenteredChart period hPeriod potential component
          frameAnchor current)
      (extChartAt throatCoverModelWithCorners current current) :=
  rfl

@[simp]
theorem throatGaugeCovectorSecondOrderJetInFrameAt_secondDerivative
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (frameAnchor current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) frameAnchor).baseSet) :
    (throatGaugeCovectorSecondOrderJetInFrameAt period hPeriod potential
      component frameAnchor current hCurrent).secondDerivative =
      fderiv Real
        (fderiv Real
          (throatGaugeCovectorCenteredChart period hPeriod potential component
            frameAnchor current))
        (extChartAt throatCoverModelWithCorners current current) :=
  rfl

/-! ## Agreement with the original diagonal extractor -/

/-- When frame anchor, chart center and evaluation point coincide, the new
two-parameter carrier is exactly the original Candidate-A gauge jet. -/
theorem globalCandidateAThroatGaugeSecondOrderJetAt_eq_inFrameAt
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (sector : Sector) (component : Fin 2)
    (anchor : EffectiveThroat period hPeriod) :
    globalCandidateAThroatGaugeSecondOrderJetAt period hPeriod data sector
        component anchor =
      throatGaugeCovectorSecondOrderJetInFrameAt period hPeriod
        (globalCandidateAThroatPotentialBySector period hPeriod data sector)
        component anchor anchor
        (mem_baseSet_trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) anchor) := by
  rfl

/-! ## The overlap law in the jet carrier -/

/-- The `firstDerivative` slots of the two genuine local jet carriers obey the
same full Leibniz law: transported first derivative plus the derivative of the
varying contragredient transition acting on the first value. -/
theorem throatGaugeCovectorSecondOrderJetInFrameAt_firstDerivative_transition
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (firstAnchor secondAnchor current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatGaugeCenteredTrivializationOverlap period hPeriod
        firstAnchor secondAnchor) :
    (throatGaugeCovectorSecondOrderJetInFrameAt period hPeriod potential
      component secondAnchor current hCurrent.2).firstDerivative =
      (throatGaugeCovectorTrivializationTransitionAt period hPeriod
          firstAnchor secondAnchor current :
            FramedCovector ThroatCoverCoordinates →L[Real]
              FramedCovector ThroatCoverCoordinates).comp
        (throatGaugeCovectorSecondOrderJetInFrameAt period hPeriod potential
          component firstAnchor current hCurrent.1).firstDerivative +
      (fderiv Real
        (throatGaugeCovectorTransitionCenteredChart period hPeriod
          firstAnchor secondAnchor current)
        (extChartAt throatCoverModelWithCorners current current)).flip
          (throatGaugeCovectorSecondOrderJetInFrameAt period hPeriod potential
            component firstAnchor current hCurrent.1).value := by
  rw [throatGaugeCovectorSecondOrderJetInFrameAt_firstDerivative,
    throatGaugeCovectorSecondOrderJetInFrameAt_firstDerivative,
    throatGaugeCovectorSecondOrderJetInFrameAt_value]
  exact throatGaugeCovectorCenteredChart_fderiv_transition period hPeriod
    potential component firstAnchor secondAnchor current hCurrent

end
end P0EFTJanusProgramPActualThroatGaugeChartwiseFirstOrderJetOverlap4D
end JanusFormal
