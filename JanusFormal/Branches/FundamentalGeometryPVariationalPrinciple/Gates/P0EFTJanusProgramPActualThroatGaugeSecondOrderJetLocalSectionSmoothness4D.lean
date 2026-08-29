import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeSecondOrderJetBundleAtlasData4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeBaseChartSecondOrderJetOverlap4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeZeroOrderOverlapDataSmoothness4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFramedSecondOrderJetSemidirectTransportSmoothness4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeSecondOrderJetVectorBundleDescentLocalTrivialization4D

/-!
# Smooth local representatives of the actual throat gauge second jet

For a fixed frame/chart atlas index, the value, Jacobian and Hessian of an
actual potential component form a `C∞` raw framed second jet on that patch.
This is local section regularity; compatibility between patches is handled by
the previously proved transition laws.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatGaugeSecondOrderJetLocalSectionSmoothness4D

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
open P0EFTJanusProgramPActualThroatAbelianPotentialChartwiseSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatGaugeChartwiseFirstOrderOverlap4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartSecondOrderJetOverlap4D
open P0EFTJanusProgramPActualThroatGaugeZeroOrderOverlapDataSmoothness4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetBundleAtlasData4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetVectorBundleCore4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPointwiseQuotientDescent4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPointwiseNormalization4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetVectorBundleDescent4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetVectorBundleDescentLocalTrivialization4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev GaugeCovector :=
  FramedCovector ThroatCoverCoordinates

private abbrev GaugeJet :=
  FramedSecondOrderJet ThroatCoverCoordinates GaugeCovector

private abbrev BundleIndex :=
  ThroatGaugeSecondOrderJetBundleIndex period hPeriod

private abbrev GaugeFirstDerivative :=
  ThroatCoverCoordinates →L[Real] GaugeCovector

local instance gaugeFirstDerivativeNormedAddCommGroup :
    NormedAddCommGroup GaugeFirstDerivative :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance gaugeFirstDerivativeNormedSpace :
    NormedSpace Real GaugeFirstDerivative :=
  ContinuousLinearMap.toNormedSpace

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-! ## A continuous-linear retraction from arbitrary jet components -/

private def symmetrizedGaugeJet
    (components : FramedSecondOrderJetAmbient
      ThroatCoverCoordinates GaugeCovector) :
    GaugeJet where
  value := components.1
  firstDerivative := components.2.1
  secondDerivative :=
    (2 : Real)⁻¹ • (components.2.2 + components.2.2.flip)
  secondDerivative_symmetric first second := by
    simp only [smul_apply, add_apply, ContinuousLinearMap.flip_apply]
    rw [add_comm]

private def symmetrizedGaugeJetLinearMap :
    FramedSecondOrderJetAmbient ThroatCoverCoordinates GaugeCovector →ₗ[Real]
      GaugeJet where
  toFun := symmetrizedGaugeJet
  map_add' first second := by
    apply FramedSecondOrderJet.ext_components
      ThroatCoverCoordinates GaugeCovector
    · simp only [symmetrizedGaugeJet,
        FramedSecondOrderJet.add_value, Prod.fst_add]
    · simp only [symmetrizedGaugeJet,
        FramedSecondOrderJet.add_firstDerivative, Prod.snd_add,
        Prod.fst_add]
    · simp only [symmetrizedGaugeJet,
        FramedSecondOrderJet.add_secondDerivative, Prod.snd_add,
        ContinuousLinearMap.flip_add]
      module
  map_smul' scalar components := by
    apply FramedSecondOrderJet.ext_components
      ThroatCoverCoordinates GaugeCovector
    · simp only [symmetrizedGaugeJet,
        FramedSecondOrderJet.smul_value, Prod.smul_fst,
        RingHom.id_apply]
    · simp only [symmetrizedGaugeJet,
        FramedSecondOrderJet.smul_firstDerivative, Prod.smul_snd,
        Prod.smul_fst, RingHom.id_apply]
    · simp only [symmetrizedGaugeJet,
        FramedSecondOrderJet.smul_secondDerivative, Prod.smul_snd,
        ContinuousLinearMap.flip_smul, RingHom.id_apply]
      module

private def symmetrizedGaugeJetContinuousLinearMap :
    FramedSecondOrderJetAmbient ThroatCoverCoordinates GaugeCovector →L[Real]
      GaugeJet :=
  LinearMap.toContinuousLinearMap symmetrizedGaugeJetLinearMap

private theorem symmetrizedGaugeJetContinuousLinearMap_components
    (jet : GaugeJet) :
    symmetrizedGaugeJetContinuousLinearMap
        (jet.value, jet.firstDerivative, jet.secondDerivative) = jet := by
  change symmetrizedGaugeJet
    (jet.value, jet.firstDerivative, jet.secondDerivative) = jet
  apply FramedSecondOrderJet.ext_components
    ThroatCoverCoordinates GaugeCovector
  · rfl
  · rfl
  · apply ContinuousLinearMap.ext
    intro first
    apply ContinuousLinearMap.ext
    intro second
    simp only [symmetrizedGaugeJet, smul_apply, add_apply,
      ContinuousLinearMap.flip_apply]
    rw [jet.secondDerivative_symmetric second first]
    module

/-! ## Smooth fixed-chart derivative fields -/

/-- A fixed-frame representative in any valid fixed chart is `C∞` at the
coordinate of every point in the corresponding atlas patch. -/
theorem throatGaugeCovectorCenteredChart_contDiffAt_infty_of_mem_baseSet
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2)
    (frameAnchor chartAnchor current : EffectiveThroat period hPeriod)
    (hFrame : current ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) frameAnchor).baseSet)
    (hChart : current ∈
      (extChartAt throatCoverModelWithCorners chartAnchor).source) :
    ContDiffAt Real ∞
      (throatGaugeCovectorCenteredChart period hPeriod potential component
        frameAnchor chartAnchor)
      (extChartAt throatCoverModelWithCorners chartAnchor current) := by
  have hCoordinates : ContMDiffAt throatCoverModelWithCorners
      𝓘(Real, GaugeCovector) ∞
      (throatGaugeCovectorCoordinates period hPeriod potential component
        frameAnchor) current :=
    (throatGaugeCovectorCoordinates_contMDiffOn_baseSet period hPeriod
      potential component frameAnchor).contMDiffAt
        ((trivializationAt ThroatCoverCoordinates
          (ThroatTangentFiber period hPeriod) frameAnchor).open_baseSet.mem_nhds
            hFrame)
  have hTarget :
      extChartAt throatCoverModelWithCorners chartAnchor current ∈
        (extChartAt throatCoverModelWithCorners chartAnchor).target :=
    (extChartAt throatCoverModelWithCorners chartAnchor).map_source hChart
  have hInverse : ContMDiffAt
      𝓘(Real, ThroatCoverCoordinates) throatCoverModelWithCorners ∞
      (extChartAt throatCoverModelWithCorners chartAnchor).symm
      (extChartAt throatCoverModelWithCorners chartAnchor current) :=
    (contMDiffOn_extChartAt_symm
      (I := throatCoverModelWithCorners) (n := ∞) chartAnchor).contMDiffAt
        (extChartAt_target_mem_nhds' hTarget)
  have hComposition := hCoordinates.comp_of_eq hInverse
    ((extChartAt throatCoverModelWithCorners chartAnchor).left_inv hChart)
  change ContDiffAt Real ∞
    (throatGaugeCovectorCoordinates period hPeriod potential component
      frameAnchor ∘
        (extChartAt throatCoverModelWithCorners chartAnchor).symm)
    (extChartAt throatCoverModelWithCorners chartAnchor current)
  exact hComposition.contDiffAt

/-- The fixed-chart Jacobian field is `C∞` on its frame/chart patch. -/
theorem throatGaugeCovectorLocalFirstDerivative_contMDiffOn
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2) (index : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, GaugeFirstDerivative) ∞
      (fun current : EffectiveThroat period hPeriod ↦
        fderiv Real
          (throatGaugeCovectorCenteredChart period hPeriod potential component
            index.1 index.2)
          (extChartAt throatCoverModelWithCorners index.2 current))
      (throatGaugeSecondOrderJetBundleBaseSet period hPeriod index) := by
  intro current hCurrent
  have hGerm :=
    throatGaugeCovectorCenteredChart_contDiffAt_infty_of_mem_baseSet
      period hPeriod potential component index.1 index.2 current
        hCurrent.1 hCurrent.2
  have hDerivative := hGerm.fderiv_right (m := ∞) (by simp)
  have hChart : ContMDiffAt throatCoverModelWithCorners
      𝓘(Real, ThroatCoverCoordinates) ∞
      (extChartAt throatCoverModelWithCorners index.2) current := by
    apply contMDiffAt_extChartAt'
    simpa only [extChartAt_source] using hCurrent.2
  exact (hDerivative.contMDiffAt.comp current hChart).contMDiffWithinAt

/-- The fixed-chart Hessian field is `C∞` on its frame/chart patch. -/
theorem throatGaugeCovectorLocalSecondDerivative_contMDiffOn
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2) (index : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, ThroatCoverCoordinates →L[Real] GaugeFirstDerivative) ∞
      (fun current : EffectiveThroat period hPeriod ↦
        fderiv Real
          (fderiv Real
            (throatGaugeCovectorCenteredChart period hPeriod potential
              component index.1 index.2))
          (extChartAt throatCoverModelWithCorners index.2 current))
      (throatGaugeSecondOrderJetBundleBaseSet period hPeriod index) := by
  intro current hCurrent
  have hGerm :=
    throatGaugeCovectorCenteredChart_contDiffAt_infty_of_mem_baseSet
      period hPeriod potential component index.1 index.2 current
        hCurrent.1 hCurrent.2
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

/-- Totalized local representative of the actual second jet in one fixed
frame/chart patch.  Its value away from the patch is irrelevant. -/
def actualThroatGaugeSecondOrderJetLocalRepresentative
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2) (index : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod) : GaugeJet := by
  classical
  exact if hCurrent : current ∈
      throatGaugeSecondOrderJetBundleBaseSet period hPeriod index then
    throatGaugeCovectorSecondOrderJetInBaseChartAt period hPeriod
      potential component index.1 index.2 current hCurrent.1 hCurrent.2
  else 0

/-- Actual local representatives agree under the gauge second-jet coordinate
change on every overlap. -/
theorem actualThroatGaugeSecondOrderJetLocalRepresentative_coordChange
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2) (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatGaugeSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatGaugeSecondOrderJetBundleBaseSet period hPeriod second) :
    (throatGaugeSecondOrderJetVectorBundleCore period hPeriod).coordChange
        first second current
        (actualThroatGaugeSecondOrderJetLocalRepresentative period hPeriod
          potential component first current) =
      actualThroatGaugeSecondOrderJetLocalRepresentative period hPeriod
        potential component second current := by
  let jetClass :=
    actualThroatGaugeSecondOrderJetPointwiseClass period hPeriod potential
      component current
  have hFirstNormalization :
      throatGaugeSecondOrderJetPointwiseNormalizeAt period hPeriod
          first.1 first.2 current hCurrent.1.1 hCurrent.1.2 jetClass =
        throatGaugeCovectorSecondOrderJetInBaseChartAt period hPeriod
          potential component first.1 first.2 current
            hCurrent.1.1 hCurrent.1.2 := by
    calc
      throatGaugeSecondOrderJetPointwiseNormalizeAt period hPeriod
          first.1 first.2 current hCurrent.1.1 hCurrent.1.2 jetClass =
          ((throatGaugeSecondOrderJetVectorBundleCore period hPeriod).localTriv
            first
            (actualThroatGaugeSecondOrderJetVectorBundleSection period hPeriod
              potential component current)).2 := by
        exact (throatGaugeSecondOrderJetPointwiseClass_localTriv_snd
          period hPeriod first current hCurrent.1 jetClass).symm
      _ = throatGaugeCovectorSecondOrderJetInBaseChartAt period hPeriod
            potential component first.1 first.2 current
              hCurrent.1.1 hCurrent.1.2 :=
        actualThroatGaugeSecondOrderJetVectorBundleSection_localTriv_snd
          period hPeriod potential component first current hCurrent.1
  have hSecondNormalization :
      throatGaugeSecondOrderJetPointwiseNormalizeAt period hPeriod
          second.1 second.2 current hCurrent.2.1 hCurrent.2.2 jetClass =
        throatGaugeCovectorSecondOrderJetInBaseChartAt period hPeriod
          potential component second.1 second.2 current
            hCurrent.2.1 hCurrent.2.2 := by
    calc
      throatGaugeSecondOrderJetPointwiseNormalizeAt period hPeriod
          second.1 second.2 current hCurrent.2.1 hCurrent.2.2 jetClass =
          ((throatGaugeSecondOrderJetVectorBundleCore period hPeriod).localTriv
            second
            (actualThroatGaugeSecondOrderJetVectorBundleSection period hPeriod
              potential component current)).2 := by
        exact (throatGaugeSecondOrderJetPointwiseClass_localTriv_snd
          period hPeriod second current hCurrent.2 jetClass).symm
      _ = throatGaugeCovectorSecondOrderJetInBaseChartAt period hPeriod
            potential component second.1 second.2 current
              hCurrent.2.1 hCurrent.2.2 :=
        actualThroatGaugeSecondOrderJetVectorBundleSection_localTriv_snd
          period hPeriod potential component second current hCurrent.2
  simp only [actualThroatGaugeSecondOrderJetLocalRepresentative,
    dif_pos hCurrent.1, dif_pos hCurrent.2,
    throatGaugeSecondOrderJetVectorBundleCore_coordChange]
  rw [← hFirstNormalization, ← hSecondNormalization]
  exact throatGaugeSecondOrderJetPointwiseNormalizeAt_coordChange
    period hPeriod first second current hCurrent.1 hCurrent.2 jetClass

private theorem actualThroatGaugeSecondOrderJetLocalRepresentative_value_contMDiffOn
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2) (index : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, GaugeCovector) ∞
      (fun current : EffectiveThroat period hPeriod ↦
        (actualThroatGaugeSecondOrderJetLocalRepresentative period hPeriod
          potential component index current).value)
      (throatGaugeSecondOrderJetBundleBaseSet period hPeriod index) := by
  apply (throatGaugeCovectorCoordinates_contMDiffOn_baseSet period hPeriod
    potential component index.1).mono
    (inter_subset_left)
    |>.congr
  intro current hCurrent
  unfold actualThroatGaugeSecondOrderJetLocalRepresentative
  split
  · rw [throatGaugeCovectorSecondOrderJetInBaseChartAt_value]
  · contradiction

private theorem actualThroatGaugeSecondOrderJetLocalRepresentative_firstDerivative_contMDiffOn
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2) (index : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, GaugeFirstDerivative) ∞
      (fun current : EffectiveThroat period hPeriod ↦
        (actualThroatGaugeSecondOrderJetLocalRepresentative period hPeriod
          potential component index current).firstDerivative)
      (throatGaugeSecondOrderJetBundleBaseSet period hPeriod index) := by
  apply (throatGaugeCovectorLocalFirstDerivative_contMDiffOn period hPeriod
    potential component index).congr
  intro current hCurrent
  unfold actualThroatGaugeSecondOrderJetLocalRepresentative
  split
  · rw [throatGaugeCovectorSecondOrderJetInBaseChartAt_firstDerivative]
  · contradiction

private theorem actualThroatGaugeSecondOrderJetLocalRepresentative_secondDerivative_contMDiffOn
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2) (index : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, ThroatCoverCoordinates →L[Real] GaugeFirstDerivative) ∞
      (fun current : EffectiveThroat period hPeriod ↦
        (actualThroatGaugeSecondOrderJetLocalRepresentative period hPeriod
          potential component index current).secondDerivative)
      (throatGaugeSecondOrderJetBundleBaseSet period hPeriod index) := by
  apply (throatGaugeCovectorLocalSecondDerivative_contMDiffOn period hPeriod
    potential component index).congr
  intro current hCurrent
  unfold actualThroatGaugeSecondOrderJetLocalRepresentative
  split
  · rw [throatGaugeCovectorSecondOrderJetInBaseChartAt_secondDerivative]
  · contradiction

/-- The actual value, Jacobian and Hessian form a `C∞` raw framed second jet
on every fixed frame/chart patch. -/
theorem actualThroatGaugeSecondOrderJetLocalRepresentative_contMDiffOn
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2) (index : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners 𝓘(Real, GaugeJet) ∞
      (actualThroatGaugeSecondOrderJetLocalRepresentative period hPeriod
        potential component index)
      (throatGaugeSecondOrderJetBundleBaseSet period hPeriod index) := by
  have hValue :=
    actualThroatGaugeSecondOrderJetLocalRepresentative_value_contMDiffOn
      period hPeriod potential component index
  have hFirstDerivative :=
    actualThroatGaugeSecondOrderJetLocalRepresentative_firstDerivative_contMDiffOn
      period hPeriod potential component index
  have hSecondDerivative :=
    actualThroatGaugeSecondOrderJetLocalRepresentative_secondDerivative_contMDiffOn
      period hPeriod potential component index
  have hComponents : ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, FramedSecondOrderJetAmbient
        ThroatCoverCoordinates GaugeCovector) ∞
      (fun current : EffectiveThroat period hPeriod ↦
        ((actualThroatGaugeSecondOrderJetLocalRepresentative period hPeriod
            potential component index current).value,
          (actualThroatGaugeSecondOrderJetLocalRepresentative period hPeriod
            potential component index current).firstDerivative,
          (actualThroatGaugeSecondOrderJetLocalRepresentative period hPeriod
            potential component index current).secondDerivative))
      (throatGaugeSecondOrderJetBundleBaseSet period hPeriod index) := by
    rw [contMDiffOn_prod_module_iff]
    constructor
    · change ContMDiffOn throatCoverModelWithCorners _ ∞
        (fun current ↦
          (actualThroatGaugeSecondOrderJetLocalRepresentative period hPeriod
            potential component index current).value) _
      exact hValue
    · rw [contMDiffOn_prod_module_iff]
      constructor
      · change ContMDiffOn throatCoverModelWithCorners _ ∞
          (fun current ↦
            (actualThroatGaugeSecondOrderJetLocalRepresentative period hPeriod
              potential component index current).firstDerivative) _
        exact hFirstDerivative
      · change ContMDiffOn throatCoverModelWithCorners _ ∞
          (fun current ↦
            (actualThroatGaugeSecondOrderJetLocalRepresentative period hPeriod
              potential component index current).secondDerivative) _
        exact hSecondDerivative
  have hBack :=
    symmetrizedGaugeJetContinuousLinearMap.contMDiff.comp_contMDiffOn
      hComponents
  apply hBack.congr
  intro current _
  exact
    (symmetrizedGaugeJetContinuousLinearMap_components
      (actualThroatGaugeSecondOrderJetLocalRepresentative period hPeriod
        potential component index current)).symm

/-- In a core chart, the descended actual section has a `C∞` fiber
coordinate on that chart's base set. -/
theorem actualThroatGaugeSecondOrderJetVectorBundleSection_localCoordinate_contMDiffOn
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2) (index : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners 𝓘(Real, GaugeJet) ∞
      (fun current : EffectiveThroat period hPeriod ↦
        ((throatGaugeSecondOrderJetVectorBundleCore period hPeriod).localTriv
          index
          (actualThroatGaugeSecondOrderJetVectorBundleSection period hPeriod
            potential component current)).2)
      (throatGaugeSecondOrderJetBundleBaseSet period hPeriod index) := by
  apply (actualThroatGaugeSecondOrderJetLocalRepresentative_contMDiffOn
    period hPeriod potential component index).congr
  intro current hCurrent
  unfold actualThroatGaugeSecondOrderJetLocalRepresentative
  split
  · exact
      actualThroatGaugeSecondOrderJetVectorBundleSection_localTriv_snd
        period hPeriod potential component index current hCurrent
  · contradiction

end
end P0EFTJanusProgramPActualThroatGaugeSecondOrderJetLocalSectionSmoothness4D
end JanusFormal
