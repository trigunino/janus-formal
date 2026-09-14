import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeSecondOrderJetLocalSectionSmoothness4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPhysicalThirdOrderJetChartwiseExtraction4D

/-!
# Actual throat gauge third jets in arbitrary frames and base charts

The existing arbitrary-frame/base-chart second jet of a genuine smooth throat
gauge covector is extended by its genuine third Frechet derivative.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatGaugeArbitraryFrameBaseChartThirdOrderJetExtraction4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 600000

noncomputable section

open Set
open scoped Manifold ContDiff RealInnerProductSpace Topology
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPFramedThirdOrderJetConstantFiberBaseChange4D
open P0EFTJanusProgramPPhysicalThirdOrderJetChartwiseExtraction4D
open P0EFTJanusProgramPActualThroatAbelianPotentialChartwiseSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatGaugeChartwiseFirstOrderOverlap4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartSecondOrderJetOverlap4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetLocalSectionSmoothness4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable (period : Real) (hPeriod : period ≠ 0)
variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*}
variable [Fintype NonNullFace] [Fintype NullFace]

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev GaugeCovector :=
  FramedCovector ThroatCoverCoordinates

private abbrev GaugeFirstDerivative :=
  ThroatCoverCoordinates →L[Real] GaugeCovector

local instance gaugeFirstDerivativeNormedAddCommGroup :
    NormedAddCommGroup GaugeFirstDerivative :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance gaugeFirstDerivativeNormedSpace :
    NormedSpace Real GaugeFirstDerivative :=
  ContinuousLinearMap.toNormedSpace

private abbrev GaugeSecondDerivative :=
  ThroatCoverCoordinates →L[Real] GaugeFirstDerivative

local instance gaugeSecondDerivativeNormedAddCommGroup :
    NormedAddCommGroup GaugeSecondDerivative :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance gaugeSecondDerivativeNormedSpace :
    NormedSpace Real GaugeSecondDerivative :=
  ContinuousLinearMap.toNormedSpace

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- The genuine third jet of a smooth throat gauge covector in arbitrary valid
frame and base-chart choices. -/
def throatGaugeCovectorThirdOrderJetInBaseChartAt
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (frameAnchor chartAnchor current : EffectiveThroat period hPeriod)
    (hFrame : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) frameAnchor).baseSet)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    FramedThirdOrderJet ThroatCoverCoordinates GaugeCovector :=
  chartwiseThirdOrderJetAt
    (throatGaugeCovectorCenteredChart period hPeriod potential component
      frameAnchor chartAnchor)
    (extChartAt throatCoverModelWithCorners chartAnchor current)
    ((throatGaugeCovectorCenteredChart_contDiffAt_infty_of_mem_baseSet
      period hPeriod potential component frameAnchor chartAnchor current
        hFrame hChart).of_le
      (by
        change ((3 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
        exact WithTop.coe_le_coe.mpr le_top))

/-- Forgetting the third derivative recovers the existing gauge second-jet
extraction definitionally. -/
@[simp]
theorem throatGaugeCovectorThirdOrderJetInBaseChartAt_truncate
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (frameAnchor chartAnchor current : EffectiveThroat period hPeriod)
    (hFrame : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) frameAnchor).baseSet)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    (throatGaugeCovectorThirdOrderJetInBaseChartAt period hPeriod potential
      component frameAnchor chartAnchor current hFrame
        hChart).toFramedSecondOrderJet =
      throatGaugeCovectorSecondOrderJetInBaseChartAt period hPeriod potential
        component frameAnchor chartAnchor current hFrame hChart :=
  rfl

@[simp]
theorem throatGaugeCovectorThirdOrderJetInBaseChartAt_value
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (frameAnchor chartAnchor current : EffectiveThroat period hPeriod)
    (hFrame : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) frameAnchor).baseSet)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    (throatGaugeCovectorThirdOrderJetInBaseChartAt period hPeriod potential
      component frameAnchor chartAnchor current hFrame hChart).value =
      throatGaugeCovectorCoordinates period hPeriod potential component
        frameAnchor current :=
  throatGaugeCovectorSecondOrderJetInBaseChartAt_value period hPeriod
    potential component frameAnchor chartAnchor current hFrame hChart

@[simp]
theorem throatGaugeCovectorThirdOrderJetInBaseChartAt_firstDerivative
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (frameAnchor chartAnchor current : EffectiveThroat period hPeriod)
    (hFrame : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) frameAnchor).baseSet)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    (throatGaugeCovectorThirdOrderJetInBaseChartAt period hPeriod potential
      component frameAnchor chartAnchor current hFrame hChart).firstDerivative =
      fderiv Real
        (throatGaugeCovectorCenteredChart period hPeriod potential component
          frameAnchor chartAnchor)
        (extChartAt throatCoverModelWithCorners chartAnchor current) :=
  rfl

@[simp]
theorem throatGaugeCovectorThirdOrderJetInBaseChartAt_secondDerivative
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (frameAnchor chartAnchor current : EffectiveThroat period hPeriod)
    (hFrame : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) frameAnchor).baseSet)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    (throatGaugeCovectorThirdOrderJetInBaseChartAt period hPeriod potential
      component frameAnchor chartAnchor current hFrame hChart).secondDerivative =
      fderiv Real
        (fderiv Real
          (throatGaugeCovectorCenteredChart period hPeriod potential component
            frameAnchor chartAnchor))
        (extChartAt throatCoverModelWithCorners chartAnchor current) :=
  rfl

@[simp]
theorem throatGaugeCovectorThirdOrderJetInBaseChartAt_thirdDerivative
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (frameAnchor chartAnchor current : EffectiveThroat period hPeriod)
    (hFrame : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) frameAnchor).baseSet)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    (throatGaugeCovectorThirdOrderJetInBaseChartAt period hPeriod potential
      component frameAnchor chartAnchor current hFrame hChart).thirdDerivative =
      fderiv Real
        (fderiv Real
          (fderiv Real
            (throatGaugeCovectorCenteredChart period hPeriod potential component
              frameAnchor chartAnchor)))
        (extChartAt throatCoverModelWithCorners chartAnchor current) :=
  rfl

/-- Physical Candidate-A throat gauge third jet in arbitrary valid frame and
base-chart choices. -/
def globalCandidateAThroatGaugeThirdOrderJetInBaseChartAt
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (sector : Sector) (component : Fin 2)
    (frameAnchor chartAnchor current : EffectiveThroat period hPeriod)
    (hFrame : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) frameAnchor).baseSet)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    FramedThirdOrderJet ThroatCoverCoordinates GaugeCovector :=
  throatGaugeCovectorThirdOrderJetInBaseChartAt period hPeriod
    (globalCandidateAThroatPotentialBySector period hPeriod data sector)
    component frameAnchor chartAnchor current hFrame hChart

/-- Physical gauge third-jet extraction truncates to the corresponding
arbitrary-frame/base-chart second jet. -/
@[simp]
theorem globalCandidateAThroatGaugeThirdOrderJetInBaseChartAt_truncate
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (sector : Sector) (component : Fin 2)
    (frameAnchor chartAnchor current : EffectiveThroat period hPeriod)
    (hFrame : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) frameAnchor).baseSet)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    (globalCandidateAThroatGaugeThirdOrderJetInBaseChartAt period hPeriod data
      sector component frameAnchor chartAnchor current hFrame
        hChart).toFramedSecondOrderJet =
      throatGaugeCovectorSecondOrderJetInBaseChartAt period hPeriod
        (globalCandidateAThroatPotentialBySector period hPeriod data sector)
        component frameAnchor chartAnchor current hFrame hChart :=
  rfl

/-- At centered frame and base charts, truncation recovers the previous
physical Candidate-A gauge second jet. -/
@[simp]
theorem globalCandidateAThroatGaugeThirdOrderJetInBaseChartAt_diagonal_truncate
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (sector : Sector) (component : Fin 2)
    (anchor : EffectiveThroat period hPeriod) :
    (globalCandidateAThroatGaugeThirdOrderJetInBaseChartAt period hPeriod data
      sector component anchor anchor anchor
        (FiberBundle.mem_baseSet_trivializationAt' anchor)
        (mem_extChartAt_source anchor)).toFramedSecondOrderJet =
      globalCandidateAThroatGaugeSecondOrderJetAt period hPeriod data sector
        component anchor :=
  rfl

end
end P0EFTJanusProgramPActualThroatGaugeArbitraryFrameBaseChartThirdOrderJetExtraction4D
end JanusFormal
