import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatMetricSecondOrderJetBundleAtlasData4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatMetricArbitraryFrameChartSecondOrderJetExtraction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFramedSecondOrderJetSemidirectTransportSmoothness4D

/-!
# Smooth local representatives of actual throat metric second jets

For a fixed frame/chart index, the value and first two derivatives of a
smooth covariant two-tensor form a `C∞` raw framed second jet on the patch.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatMetricSecondOrderJetLocalSectionSmoothness4D

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
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPActualThroatMetricArbitraryFrameChartSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatMetricSecondOrderJetBundleAtlasData4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev TensorModel :=
  FramedCovariantTwoTensor ThroatCoverCoordinates

private abbrev MetricJet :=
  FramedSecondOrderJet ThroatCoverCoordinates TensorModel

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

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-! ## Retraction from arbitrary components to symmetric jets -/

private def symmetrizedMetricJet
    (components : FramedSecondOrderJetAmbient
      ThroatCoverCoordinates TensorModel) : MetricJet where
  value := components.1
  firstDerivative := components.2.1
  secondDerivative :=
    (2 : Real)⁻¹ • (components.2.2 + components.2.2.flip)
  secondDerivative_symmetric first second := by
    simp only [smul_apply, add_apply, ContinuousLinearMap.flip_apply]
    rw [add_comm]

private def symmetrizedMetricJetLinearMap :
    FramedSecondOrderJetAmbient ThroatCoverCoordinates TensorModel →ₗ[Real]
      MetricJet where
  toFun := symmetrizedMetricJet
  map_add' first second := by
    apply FramedSecondOrderJet.ext_components
      ThroatCoverCoordinates TensorModel
    · simp only [symmetrizedMetricJet,
        FramedSecondOrderJet.add_value, Prod.fst_add]
    · simp only [symmetrizedMetricJet,
        FramedSecondOrderJet.add_firstDerivative, Prod.snd_add,
        Prod.fst_add]
    · simp only [symmetrizedMetricJet,
        FramedSecondOrderJet.add_secondDerivative, Prod.snd_add,
        ContinuousLinearMap.flip_add]
      module
  map_smul' scalar components := by
    apply FramedSecondOrderJet.ext_components
      ThroatCoverCoordinates TensorModel
    · simp only [symmetrizedMetricJet,
        FramedSecondOrderJet.smul_value, Prod.smul_fst,
        RingHom.id_apply]
    · simp only [symmetrizedMetricJet,
        FramedSecondOrderJet.smul_firstDerivative, Prod.smul_snd,
        Prod.smul_fst, RingHom.id_apply]
    · simp only [symmetrizedMetricJet,
        FramedSecondOrderJet.smul_secondDerivative, Prod.smul_snd,
        ContinuousLinearMap.flip_smul, RingHom.id_apply]
      module

private def symmetrizedMetricJetContinuousLinearMap :
    FramedSecondOrderJetAmbient ThroatCoverCoordinates TensorModel →L[Real]
      MetricJet :=
  LinearMap.toContinuousLinearMap symmetrizedMetricJetLinearMap

private theorem symmetrizedMetricJetContinuousLinearMap_components
    (jet : MetricJet) :
    symmetrizedMetricJetContinuousLinearMap
        (jet.value, jet.firstDerivative, jet.secondDerivative) = jet := by
  change symmetrizedMetricJet
    (jet.value, jet.firstDerivative, jet.secondDerivative) = jet
  apply FramedSecondOrderJet.ext_components
    ThroatCoverCoordinates TensorModel
  · rfl
  · rfl
  · apply ContinuousLinearMap.ext
    intro first
    apply ContinuousLinearMap.ext
    intro second
    simp only [symmetrizedMetricJet, smul_apply, add_apply,
      ContinuousLinearMap.flip_apply]
    rw [jet.secondDerivative_symmetric second first]
    module

/-! ## Smooth fixed-chart derivative fields -/

theorem throatTensorLocalFirstDerivative_contMDiffOn
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (index : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, MetricFirstDerivative) ∞
      (fun current : EffectiveThroat period hPeriod ↦
        fderiv Real
          (throatTensorFrameChartRepresentative period hPeriod tensor
            index.1 index.2)
          (extChartAt throatCoverModelWithCorners index.2 current))
      (throatMetricSecondOrderJetBundleBaseSet period hPeriod index) := by
  intro current hCurrent
  have hGerm :=
    throatTensorFrameChartRepresentative_contDiffAt_infty period hPeriod
      tensor index.1 index.2 current hCurrent.1 hCurrent.2
  have hDerivative := hGerm.fderiv_right (m := ∞) (by simp)
  have hChart : ContMDiffAt throatCoverModelWithCorners
      𝓘(Real, ThroatCoverCoordinates) ∞
      (extChartAt throatCoverModelWithCorners index.2) current := by
    apply contMDiffAt_extChartAt'
    simpa only [extChartAt_source] using hCurrent.2
  exact (hDerivative.contMDiffAt.comp current hChart).contMDiffWithinAt

theorem throatTensorLocalSecondDerivative_contMDiffOn
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (index : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, ThroatCoverCoordinates →L[Real] MetricFirstDerivative) ∞
      (fun current : EffectiveThroat period hPeriod ↦
        fderiv Real
          (fderiv Real
            (throatTensorFrameChartRepresentative period hPeriod tensor
              index.1 index.2))
          (extChartAt throatCoverModelWithCorners index.2 current))
      (throatMetricSecondOrderJetBundleBaseSet period hPeriod index) := by
  intro current hCurrent
  have hGerm :=
    throatTensorFrameChartRepresentative_contDiffAt_infty period hPeriod
      tensor index.1 index.2 current hCurrent.1 hCurrent.2
  have hSecondDerivative :=
    (hGerm.fderiv_right (m := ∞) (by simp)).fderiv_right
      (m := ∞) (by simp)
  have hChart : ContMDiffAt throatCoverModelWithCorners
      𝓘(Real, ThroatCoverCoordinates) ∞
      (extChartAt throatCoverModelWithCorners index.2) current := by
    apply contMDiffAt_extChartAt'
    simpa only [extChartAt_source] using hCurrent.2
  exact (hSecondDerivative.contMDiffAt.comp current hChart).contMDiffWithinAt

/-! ## Smooth raw second-jet representative -/

/-- Totalized metric second-jet representative in one fixed frame/chart. -/
def actualThroatMetricSecondOrderJetLocalRepresentative
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (index : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod) : MetricJet := by
  classical
  exact if hCurrent : current ∈
      throatMetricSecondOrderJetBundleBaseSet period hPeriod index then
    throatTensorSecondOrderJetInFrameChartAt period hPeriod tensor
      index.1 index.2 current hCurrent.1 hCurrent.2
  else 0

private theorem actualThroatMetricSecondOrderJetLocalRepresentative_value_contMDiffOn
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (index : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners 𝓘(Real, TensorModel) ∞
      (fun current : EffectiveThroat period hPeriod ↦
        (actualThroatMetricSecondOrderJetLocalRepresentative period hPeriod
          tensor index current).value)
      (throatMetricSecondOrderJetBundleBaseSet period hPeriod index) := by
  apply (throatTensorCoordinates_contMDiffOn_frameChartBaseSet period hPeriod
    tensor index.1 index.2).congr
  intro current hCurrent
  unfold actualThroatMetricSecondOrderJetLocalRepresentative
  split
  · rw [throatTensorSecondOrderJetInFrameChartAt_value]
    rfl
  · contradiction

private theorem actualThroatMetricSecondOrderJetLocalRepresentative_firstDerivative_contMDiffOn
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (index : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, MetricFirstDerivative) ∞
      (fun current : EffectiveThroat period hPeriod ↦
        (actualThroatMetricSecondOrderJetLocalRepresentative period hPeriod
          tensor index current).firstDerivative)
      (throatMetricSecondOrderJetBundleBaseSet period hPeriod index) := by
  apply (throatTensorLocalFirstDerivative_contMDiffOn period hPeriod
    tensor index).congr
  intro current hCurrent
  unfold actualThroatMetricSecondOrderJetLocalRepresentative
  split
  · rw [throatTensorSecondOrderJetInFrameChartAt_firstDerivative]
  · contradiction

private theorem actualThroatMetricSecondOrderJetLocalRepresentative_secondDerivative_contMDiffOn
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (index : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, ThroatCoverCoordinates →L[Real] MetricFirstDerivative) ∞
      (fun current : EffectiveThroat period hPeriod ↦
        (actualThroatMetricSecondOrderJetLocalRepresentative period hPeriod
          tensor index current).secondDerivative)
      (throatMetricSecondOrderJetBundleBaseSet period hPeriod index) := by
  apply (throatTensorLocalSecondDerivative_contMDiffOn period hPeriod
    tensor index).congr
  intro current hCurrent
  unfold actualThroatMetricSecondOrderJetLocalRepresentative
  split
  · rw [throatTensorSecondOrderJetInFrameChartAt_secondDerivative]
  · contradiction

/-- The actual metric value, Jacobian and Hessian form a `C∞` raw framed
second jet on every fixed frame/chart patch. -/
theorem actualThroatMetricSecondOrderJetLocalRepresentative_contMDiffOn
    (tensor : SmoothSymmetricThroatCovariantTwoTensor period hPeriod)
    (index : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners 𝓘(Real, MetricJet) ∞
      (actualThroatMetricSecondOrderJetLocalRepresentative period hPeriod
        tensor index)
      (throatMetricSecondOrderJetBundleBaseSet period hPeriod index) := by
  have hValue :=
    actualThroatMetricSecondOrderJetLocalRepresentative_value_contMDiffOn
      period hPeriod tensor index
  have hFirstDerivative :=
    actualThroatMetricSecondOrderJetLocalRepresentative_firstDerivative_contMDiffOn
      period hPeriod tensor index
  have hSecondDerivative :=
    actualThroatMetricSecondOrderJetLocalRepresentative_secondDerivative_contMDiffOn
      period hPeriod tensor index
  have hComponents : ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, FramedSecondOrderJetAmbient
        ThroatCoverCoordinates TensorModel) ∞
      (fun current : EffectiveThroat period hPeriod ↦
        ((actualThroatMetricSecondOrderJetLocalRepresentative period hPeriod
            tensor index current).value,
          (actualThroatMetricSecondOrderJetLocalRepresentative period hPeriod
            tensor index current).firstDerivative,
          (actualThroatMetricSecondOrderJetLocalRepresentative period hPeriod
            tensor index current).secondDerivative))
      (throatMetricSecondOrderJetBundleBaseSet period hPeriod index) := by
    rw [contMDiffOn_prod_module_iff]
    constructor
    · change ContMDiffOn throatCoverModelWithCorners _ ∞
        (fun current ↦
          (actualThroatMetricSecondOrderJetLocalRepresentative period hPeriod
            tensor index current).value) _
      exact hValue
    · rw [contMDiffOn_prod_module_iff]
      constructor
      · change ContMDiffOn throatCoverModelWithCorners _ ∞
          (fun current ↦
            (actualThroatMetricSecondOrderJetLocalRepresentative period hPeriod
              tensor index current).firstDerivative) _
        exact hFirstDerivative
      · change ContMDiffOn throatCoverModelWithCorners _ ∞
          (fun current ↦
            (actualThroatMetricSecondOrderJetLocalRepresentative period hPeriod
              tensor index current).secondDerivative) _
        exact hSecondDerivative
  have hBack :=
    symmetrizedMetricJetContinuousLinearMap.contMDiff.comp_contMDiffOn
      hComponents
  apply hBack.congr
  intro current _
  exact
    (symmetrizedMetricJetContinuousLinearMap_components
      (actualThroatMetricSecondOrderJetLocalRepresentative period hPeriod
        tensor index current)).symm

end
end P0EFTJanusProgramPActualThroatMetricSecondOrderJetLocalSectionSmoothness4D
end JanusFormal
