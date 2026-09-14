import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatMetricArbitraryFrameChartThirdOrderJetExtraction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatMetricSecondOrderJetLocalSectionSmoothness4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFramedThirdOrderJetSemidirectTransportSmoothness4D

/-!
# Smooth local representatives of actual throat metric third jets

For a fixed frame/chart index, the existing smooth second-jet representative
and the genuine third derivative assemble into a smooth framed third jet on
the corresponding atlas patch.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatMetricThirdOrderJetLocalSectionSmoothness4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 600000

noncomputable section

open Function Module Set
open scoped Manifold ContDiff RealInnerProductSpace Topology
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPFramedThirdOrderJetConstantFiberBaseChange4D
open P0EFTJanusProgramPFramedThirdOrderJetSemidirectTransportSmoothness4D
open P0EFTJanusProgramPGlobalMetricChartwiseSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatMetricArbitraryFrameChartSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatMetricArbitraryFrameChartThirdOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatMetricSecondOrderJetBundleAtlasData4D
open P0EFTJanusProgramPActualThroatMetricSecondOrderJetLocalSectionSmoothness4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev TensorModel :=
  FramedCovariantTwoTensor ThroatCoverCoordinates

private abbrev MetricSecondJet :=
  FramedSecondOrderJet ThroatCoverCoordinates TensorModel

private abbrev MetricThirdJet :=
  FramedThirdOrderJet ThroatCoverCoordinates TensorModel

private abbrev BundleIndex :=
  ThroatMetricSecondOrderJetBundleIndex period hPeriod

local instance tensorModelNormedAddCommGroup :
    NormedAddCommGroup TensorModel :=
  P0EFTJanusProgramPActualThroatMetricSecondOrderJetSemidirectTransport4D.tensorModelNormedAddCommGroup

local instance tensorModelNormedSpace : NormedSpace Real TensorModel :=
  P0EFTJanusProgramPActualThroatMetricSecondOrderJetSemidirectTransport4D.tensorModelNormedSpace

local instance tensorModelFiniteDimensional :
    FiniteDimensional Real TensorModel :=
  ContinuousLinearMap.finiteDimensional

private abbrev MetricFirstDerivative :=
  ThroatCoverCoordinates →L[Real] TensorModel

local instance metricFirstDerivativeNormedAddCommGroup :
    NormedAddCommGroup MetricFirstDerivative :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance metricFirstDerivativeNormedSpace :
    NormedSpace Real MetricFirstDerivative :=
  ContinuousLinearMap.toNormedSpace

local instance metricFirstDerivativeFiniteDimensional :
    FiniteDimensional Real MetricFirstDerivative :=
  ContinuousLinearMap.finiteDimensional

private abbrev MetricSecondDerivative :=
  ThroatCoverCoordinates →L[Real] MetricFirstDerivative

local instance metricSecondDerivativeNormedAddCommGroup :
    NormedAddCommGroup MetricSecondDerivative :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance metricSecondDerivativeNormedSpace :
    NormedSpace Real MetricSecondDerivative :=
  ContinuousLinearMap.toNormedSpace

local instance metricSecondDerivativeFiniteDimensional :
    FiniteDimensional Real MetricSecondDerivative :=
  ContinuousLinearMap.finiteDimensional

private abbrev MetricThirdDerivative :=
  ThroatCoverCoordinates →L[Real] MetricSecondDerivative

local instance metricThirdDerivativeNormedAddCommGroup :
    NormedAddCommGroup MetricThirdDerivative :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance metricThirdDerivativeNormedSpace :
    NormedSpace Real MetricThirdDerivative :=
  ContinuousLinearMap.toNormedSpace

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- The third derivative of a fixed-frame/chart tensor representative is
smooth on its atlas patch. -/
theorem throatTensorLocalThirdDerivative_contMDiffOn
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (index : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, MetricThirdDerivative) ∞
      (fun current : EffectiveThroat period hPeriod ↦
        fderiv Real
          (fderiv Real
            (fderiv Real
              (throatTensorFrameChartRepresentative period hPeriod tensor
                index.1 index.2)))
          (extChartAt throatCoverModelWithCorners index.2 current))
      (throatMetricSecondOrderJetBundleBaseSet period hPeriod index) := by
  intro current hCurrent
  have hGerm :=
    throatTensorFrameChartRepresentative_contDiffAt_infty period hPeriod
      tensor index.1 index.2 current hCurrent.1 hCurrent.2
  have hThirdDerivative :=
    ((hGerm.fderiv_right (m := ∞) (by simp)).fderiv_right
      (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)
  have hChart : ContMDiffAt throatCoverModelWithCorners
      𝓘(Real, ThroatCoverCoordinates) ∞
      (extChartAt throatCoverModelWithCorners index.2) current := by
    apply contMDiffAt_extChartAt'
    simpa only [extChartAt_source] using hCurrent.2
  exact (hThirdDerivative.contMDiffAt.comp current hChart).contMDiffWithinAt

/-- Totalized metric third-jet representative in one fixed frame/chart. -/
def actualThroatMetricThirdOrderJetLocalRepresentative
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (index : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod) : MetricThirdJet := by
  classical
  exact if hCurrent : current ∈
      throatMetricSecondOrderJetBundleBaseSet period hPeriod index then
    throatTensorThirdOrderJetInFrameChartAt period hPeriod tensor
      index.1 index.2 current hCurrent.1 hCurrent.2
  else 0

/-- On its atlas patch, the totalized representative is the arbitrary
frame/chart extraction. -/
theorem actualThroatMetricThirdOrderJetLocalRepresentative_eq_of_mem
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (index : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatMetricSecondOrderJetBundleBaseSet period hPeriod index) :
    actualThroatMetricThirdOrderJetLocalRepresentative period hPeriod tensor
        index current =
      throatTensorThirdOrderJetInFrameChartAt period hPeriod tensor
        index.1 index.2 current hCurrent.1 hCurrent.2 := by
  simp only [actualThroatMetricThirdOrderJetLocalRepresentative,
    dif_pos hCurrent]

/-- The third-jet representative truncates exactly to the existing local
second-jet representative. -/
@[simp]
theorem actualThroatMetricThirdOrderJetLocalRepresentative_truncate
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (index : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod) :
    (actualThroatMetricThirdOrderJetLocalRepresentative period hPeriod tensor
      index current).toFramedSecondOrderJet =
      actualThroatMetricSecondOrderJetLocalRepresentative period hPeriod
        tensor index current := by
  classical
  unfold actualThroatMetricThirdOrderJetLocalRepresentative
    actualThroatMetricSecondOrderJetLocalRepresentative
  split <;> rfl

private theorem actualThroatMetricThirdOrderJetLocalRepresentative_thirdDerivative_contMDiffOn
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (index : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, MetricThirdDerivative) ∞
      (fun current : EffectiveThroat period hPeriod ↦
        (actualThroatMetricThirdOrderJetLocalRepresentative period hPeriod
          tensor index current).thirdDerivative)
      (throatMetricSecondOrderJetBundleBaseSet period hPeriod index) := by
  apply (throatTensorLocalThirdDerivative_contMDiffOn period hPeriod
    tensor index).congr
  intro current hCurrent
  unfold actualThroatMetricThirdOrderJetLocalRepresentative
  split
  · rw [throatTensorThirdOrderJetInFrameChartAt_thirdDerivative]
  · contradiction

/-- The value and first three derivatives of a smooth throat tensor form a
smooth raw framed third jet on every fixed atlas patch. -/
theorem actualThroatMetricThirdOrderJetLocalRepresentative_contMDiffOn
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (index : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners 𝓘(Real, MetricThirdJet) ∞
      (actualThroatMetricThirdOrderJetLocalRepresentative period hPeriod
        tensor index)
      (throatMetricSecondOrderJetBundleBaseSet period hPeriod index) := by
  have hLower : ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, MetricSecondJet) ∞
      (fun current ↦
        (actualThroatMetricThirdOrderJetLocalRepresentative period hPeriod
          tensor index current).toFramedSecondOrderJet)
      (throatMetricSecondOrderJetBundleBaseSet period hPeriod index) := by
    apply
      (actualThroatMetricSecondOrderJetLocalRepresentative_contMDiffOn
        period hPeriod tensor index).congr
    intro current _
    exact actualThroatMetricThirdOrderJetLocalRepresentative_truncate
      period hPeriod tensor index current
  exact contMDiffOn_framedThirdOrderJet_of_truncate_and_thirdDerivative
    (actualThroatMetricThirdOrderJetLocalRepresentative period hPeriod
      tensor index) hLower
    (actualThroatMetricThirdOrderJetLocalRepresentative_thirdDerivative_contMDiffOn
      period hPeriod tensor index)

/-! ## Actual induced metric wrapper -/

/-- Local third-jet representative of one actual induced sector metric. -/
def globalGaugeFixedInducedMetricThirdOrderJetLocalRepresentative
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector)
    (index : BundleIndex period hPeriod) :
    EffectiveThroat period hPeriod → MetricThirdJet :=
  actualThroatMetricThirdOrderJetLocalRepresentative period hPeriod
    (globalGaugeFixedInducedMetricBySector period hPeriod configuration sector)
    index

theorem globalGaugeFixedInducedMetricThirdOrderJetLocalRepresentative_eq_of_mem
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector)
    (index : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatMetricSecondOrderJetBundleBaseSet period hPeriod index) :
    globalGaugeFixedInducedMetricThirdOrderJetLocalRepresentative period
        hPeriod configuration sector index current =
      globalGaugeFixedThroatMetricThirdOrderJetInFrameChartAt period hPeriod
        configuration sector index.1 index.2 current hCurrent.1 hCurrent.2 :=
  actualThroatMetricThirdOrderJetLocalRepresentative_eq_of_mem period hPeriod
    (globalGaugeFixedInducedMetricBySector period hPeriod configuration sector)
    index current hCurrent

/-- Physical local third jets truncate to the corresponding actual local
second jets. -/
@[simp]
theorem globalGaugeFixedInducedMetricThirdOrderJetLocalRepresentative_truncate
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector)
    (index : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod) :
    (globalGaugeFixedInducedMetricThirdOrderJetLocalRepresentative period
      hPeriod configuration sector index current).toFramedSecondOrderJet =
      actualThroatMetricSecondOrderJetLocalRepresentative period hPeriod
        (globalGaugeFixedInducedMetricBySector period hPeriod configuration
          sector) index current :=
  actualThroatMetricThirdOrderJetLocalRepresentative_truncate period hPeriod
    (globalGaugeFixedInducedMetricBySector period hPeriod configuration sector)
    index current

/-- Every actual induced metric sector has a smooth local third-jet
representative on each atlas patch. -/
theorem globalGaugeFixedInducedMetricThirdOrderJetLocalRepresentative_contMDiffOn
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector)
    (index : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners 𝓘(Real, MetricThirdJet) ∞
      (globalGaugeFixedInducedMetricThirdOrderJetLocalRepresentative period
        hPeriod configuration sector index)
      (throatMetricSecondOrderJetBundleBaseSet period hPeriod index) :=
  actualThroatMetricThirdOrderJetLocalRepresentative_contMDiffOn period hPeriod
    (globalGaugeFixedInducedMetricBySector period hPeriod configuration sector)
    index

end
end P0EFTJanusProgramPActualThroatMetricThirdOrderJetLocalSectionSmoothness4D
end JanusFormal
