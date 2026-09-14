import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeArbitraryFrameBaseChartThirdOrderJetExtraction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeSecondOrderJetLocalSectionSmoothness4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFramedThirdOrderJetSemidirectTransportSmoothness4D

/-!
# Smooth local representatives of actual throat gauge third jets

For a fixed frame/base-chart index, the existing smooth second-jet
representative and the genuine third derivative assemble into a smooth framed
third jet on the corresponding atlas patch.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatGaugeThirdOrderJetLocalSectionSmoothness4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 600000

noncomputable section

open Function Module Set
open scoped Manifold ContDiff RealInnerProductSpace Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPFramedThirdOrderJetConstantFiberBaseChange4D
open P0EFTJanusProgramPFramedThirdOrderJetSemidirectTransportSmoothness4D
open P0EFTJanusProgramPActualThroatAbelianPotentialChartwiseSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatGaugeChartwiseFirstOrderOverlap4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetBundleAtlasData4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetLocalSectionSmoothness4D
open P0EFTJanusProgramPActualThroatGaugeArbitraryFrameBaseChartThirdOrderJetExtraction4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev GaugeCovector :=
  FramedCovector ThroatCoverCoordinates

private abbrev GaugeSecondJet :=
  FramedSecondOrderJet ThroatCoverCoordinates GaugeCovector

private abbrev GaugeThirdJet :=
  FramedThirdOrderJet ThroatCoverCoordinates GaugeCovector

private abbrev BundleIndex :=
  ThroatGaugeSecondOrderJetBundleIndex period hPeriod

local instance gaugeCovectorFiniteDimensional :
    FiniteDimensional Real GaugeCovector :=
  ContinuousLinearMap.finiteDimensional

private abbrev GaugeFirstDerivative :=
  ThroatCoverCoordinates →L[Real] GaugeCovector

local instance gaugeFirstDerivativeNormedAddCommGroup :
    NormedAddCommGroup GaugeFirstDerivative :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance gaugeFirstDerivativeNormedSpace :
    NormedSpace Real GaugeFirstDerivative :=
  ContinuousLinearMap.toNormedSpace

local instance gaugeFirstDerivativeFiniteDimensional :
    FiniteDimensional Real GaugeFirstDerivative :=
  ContinuousLinearMap.finiteDimensional

private abbrev GaugeSecondDerivative :=
  ThroatCoverCoordinates →L[Real] GaugeFirstDerivative

local instance gaugeSecondDerivativeNormedAddCommGroup :
    NormedAddCommGroup GaugeSecondDerivative :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance gaugeSecondDerivativeNormedSpace :
    NormedSpace Real GaugeSecondDerivative :=
  ContinuousLinearMap.toNormedSpace

local instance gaugeSecondDerivativeFiniteDimensional :
    FiniteDimensional Real GaugeSecondDerivative :=
  ContinuousLinearMap.finiteDimensional

private abbrev GaugeThirdDerivative :=
  ThroatCoverCoordinates →L[Real] GaugeSecondDerivative

local instance gaugeThirdDerivativeNormedAddCommGroup :
    NormedAddCommGroup GaugeThirdDerivative :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance gaugeThirdDerivativeNormedSpace :
    NormedSpace Real GaugeThirdDerivative :=
  ContinuousLinearMap.toNormedSpace

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- The third derivative of a fixed-frame/base-chart gauge representative is
smooth on its atlas patch. -/
theorem throatGaugeCovectorLocalThirdDerivative_contMDiffOn
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (index : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, GaugeThirdDerivative) ∞
      (fun current : EffectiveThroat period hPeriod ↦
        fderiv Real
          (fderiv Real
            (fderiv Real
              (throatGaugeCovectorCenteredChart period hPeriod potential
                component index.1 index.2)))
          (extChartAt throatCoverModelWithCorners index.2 current))
      (throatGaugeSecondOrderJetBundleBaseSet period hPeriod index) := by
  intro current hCurrent
  have hGerm :=
    throatGaugeCovectorCenteredChart_contDiffAt_infty_of_mem_baseSet
      period hPeriod potential component index.1 index.2 current
        hCurrent.1 hCurrent.2
  have hThirdDerivative :=
    ((hGerm.fderiv_right (m := ∞) (by simp)).fderiv_right
      (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)
  have hChart : ContMDiffAt throatCoverModelWithCorners
      𝓘(Real, ThroatCoverCoordinates) ∞
      (extChartAt throatCoverModelWithCorners index.2) current := by
    apply contMDiffAt_extChartAt'
    simpa only [extChartAt_source] using hCurrent.2
  exact (hThirdDerivative.contMDiffAt.comp current hChart).contMDiffWithinAt

/-- Totalized gauge third-jet representative in one fixed atlas patch. -/
def actualThroatGaugeThirdOrderJetLocalRepresentative
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (index : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod) : GaugeThirdJet := by
  classical
  exact if hCurrent : current ∈
      throatGaugeSecondOrderJetBundleBaseSet period hPeriod index then
    throatGaugeCovectorThirdOrderJetInBaseChartAt period hPeriod potential
      component index.1 index.2 current hCurrent.1 hCurrent.2
  else 0

/-- On its atlas patch, the totalized representative is the arbitrary
frame/base-chart extraction. -/
theorem actualThroatGaugeThirdOrderJetLocalRepresentative_eq_of_mem
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (index : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatGaugeSecondOrderJetBundleBaseSet period hPeriod index) :
    actualThroatGaugeThirdOrderJetLocalRepresentative period hPeriod potential
        component index current =
      throatGaugeCovectorThirdOrderJetInBaseChartAt period hPeriod potential
        component index.1 index.2 current hCurrent.1 hCurrent.2 := by
  simp only [actualThroatGaugeThirdOrderJetLocalRepresentative,
    dif_pos hCurrent]

/-- The third-jet representative truncates exactly to the existing local
second-jet representative. -/
@[simp]
theorem actualThroatGaugeThirdOrderJetLocalRepresentative_truncate
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (index : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod) :
    (actualThroatGaugeThirdOrderJetLocalRepresentative period hPeriod potential
      component index current).toFramedSecondOrderJet =
      actualThroatGaugeSecondOrderJetLocalRepresentative period hPeriod
        potential component index current := by
  classical
  unfold actualThroatGaugeThirdOrderJetLocalRepresentative
    actualThroatGaugeSecondOrderJetLocalRepresentative
  split <;> rfl

private theorem actualThroatGaugeThirdOrderJetLocalRepresentative_thirdDerivative_contMDiffOn
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (index : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, GaugeThirdDerivative) ∞
      (fun current : EffectiveThroat period hPeriod ↦
        (actualThroatGaugeThirdOrderJetLocalRepresentative period hPeriod
          potential component index current).thirdDerivative)
      (throatGaugeSecondOrderJetBundleBaseSet period hPeriod index) := by
  apply (throatGaugeCovectorLocalThirdDerivative_contMDiffOn period hPeriod
    potential component index).congr
  intro current hCurrent
  unfold actualThroatGaugeThirdOrderJetLocalRepresentative
  split
  · rw [throatGaugeCovectorThirdOrderJetInBaseChartAt_thirdDerivative]
  · contradiction

/-- A smooth throat gauge covector gives a smooth raw third jet on every
fixed atlas patch. -/
theorem actualThroatGaugeThirdOrderJetLocalRepresentative_contMDiffOn
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (index : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners 𝓘(Real, GaugeThirdJet) ∞
      (actualThroatGaugeThirdOrderJetLocalRepresentative period hPeriod
        potential component index)
      (throatGaugeSecondOrderJetBundleBaseSet period hPeriod index) := by
  have hLower : ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, GaugeSecondJet) ∞
      (fun current ↦
        (actualThroatGaugeThirdOrderJetLocalRepresentative period hPeriod
          potential component index current).toFramedSecondOrderJet)
      (throatGaugeSecondOrderJetBundleBaseSet period hPeriod index) := by
    apply
      (actualThroatGaugeSecondOrderJetLocalRepresentative_contMDiffOn
        period hPeriod potential component index).congr
    intro current _
    exact actualThroatGaugeThirdOrderJetLocalRepresentative_truncate
      period hPeriod potential component index current
  exact contMDiffOn_framedThirdOrderJet_of_truncate_and_thirdDerivative
    (actualThroatGaugeThirdOrderJetLocalRepresentative period hPeriod
      potential component index) hLower
    (actualThroatGaugeThirdOrderJetLocalRepresentative_thirdDerivative_contMDiffOn
      period hPeriod potential component index)

end
end P0EFTJanusProgramPActualThroatGaugeThirdOrderJetLocalSectionSmoothness4D
end JanusFormal
