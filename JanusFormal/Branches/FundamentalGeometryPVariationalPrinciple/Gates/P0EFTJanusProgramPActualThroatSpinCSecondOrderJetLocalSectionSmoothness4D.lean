import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCSecondOrderJetBundleAtlasData4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCArbitraryTrivializationChartSecondOrderJetExtraction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFramedSecondOrderJetSemidirectTransportSmoothness4D

/-!
# Smooth local representatives of actual throat SpinC second jets

For a fixed SpinC trivialization/chart index, the value and first two
derivatives of a smooth primitive SpinC section form a `C∞` raw framed second
jet on the corresponding atlas patch.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatSpinCSecondOrderJetLocalSectionSmoothness4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 600000

noncomputable section

open Function Module Set
open scoped Manifold ContDiff Topology
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracDescent4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPActualThroatSpinCArbitraryTrivializationChartSecondOrderJetExtraction4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderJetBundleAtlasData4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatBase :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev SpinCJet :=
  FramedSecondOrderJet ThroatCoverCoordinates D9DoubledMatterFiber

private abbrev BundleIndex :=
  ThroatSpinCSecondOrderJetBundleIndex period hPeriod

private abbrev SpinCFirstDerivative :=
  ThroatCoverCoordinates →L[Real] D9DoubledMatterFiber

local instance spinCFirstDerivativeNormedAddCommGroup :
    NormedAddCommGroup SpinCFirstDerivative :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance spinCFirstDerivativeNormedSpace :
    NormedSpace Real SpinCFirstDerivative :=
  ContinuousLinearMap.toNormedSpace

local instance spinCFirstDerivativeFiniteDimensional :
    FiniteDimensional Real SpinCFirstDerivative :=
  ContinuousLinearMap.finiteDimensional

local instance throatBaseChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance throatBaseIsManifold :
    IsManifold throatCoverModelWithCorners ω (ThroatBase period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-! ## Retraction from arbitrary components to symmetric jets -/

private def symmetrizedSpinCJet
    (components : FramedSecondOrderJetAmbient
      ThroatCoverCoordinates D9DoubledMatterFiber) : SpinCJet where
  value := components.1
  firstDerivative := components.2.1
  secondDerivative :=
    (2 : Real)⁻¹ • (components.2.2 + components.2.2.flip)
  secondDerivative_symmetric first second := by
    simp only [smul_apply, add_apply, ContinuousLinearMap.flip_apply]
    rw [add_comm]

private def symmetrizedSpinCJetLinearMap :
    FramedSecondOrderJetAmbient ThroatCoverCoordinates D9DoubledMatterFiber
      →ₗ[Real] SpinCJet where
  toFun := symmetrizedSpinCJet
  map_add' first second := by
    apply FramedSecondOrderJet.ext_components
      ThroatCoverCoordinates D9DoubledMatterFiber
    · simp only [symmetrizedSpinCJet,
        FramedSecondOrderJet.add_value, Prod.fst_add]
    · simp only [symmetrizedSpinCJet,
        FramedSecondOrderJet.add_firstDerivative, Prod.snd_add,
        Prod.fst_add]
    · simp only [symmetrizedSpinCJet,
        FramedSecondOrderJet.add_secondDerivative, Prod.snd_add,
        ContinuousLinearMap.flip_add]
      module
  map_smul' scalar components := by
    apply FramedSecondOrderJet.ext_components
      ThroatCoverCoordinates D9DoubledMatterFiber
    · simp only [symmetrizedSpinCJet,
        FramedSecondOrderJet.smul_value, Prod.smul_fst,
        RingHom.id_apply]
    · simp only [symmetrizedSpinCJet,
        FramedSecondOrderJet.smul_firstDerivative, Prod.smul_snd,
        Prod.smul_fst, RingHom.id_apply]
    · simp only [symmetrizedSpinCJet,
        FramedSecondOrderJet.smul_secondDerivative, Prod.smul_snd,
        ContinuousLinearMap.flip_smul, RingHom.id_apply]
      module

private def symmetrizedSpinCJetContinuousLinearMap :
    FramedSecondOrderJetAmbient ThroatCoverCoordinates D9DoubledMatterFiber
      →L[Real] SpinCJet :=
  LinearMap.toContinuousLinearMap symmetrizedSpinCJetLinearMap

private theorem symmetrizedSpinCJetContinuousLinearMap_components
    (jet : SpinCJet) :
    symmetrizedSpinCJetContinuousLinearMap
        (jet.value, jet.firstDerivative, jet.secondDerivative) = jet := by
  change symmetrizedSpinCJet
    (jet.value, jet.firstDerivative, jet.secondDerivative) = jet
  apply FramedSecondOrderJet.ext_components
    ThroatCoverCoordinates D9DoubledMatterFiber
  · rfl
  · rfl
  · apply ContinuousLinearMap.ext
    intro first
    apply ContinuousLinearMap.ext
    intro second
    simp only [symmetrizedSpinCJet, smul_apply, add_apply,
      ContinuousLinearMap.flip_apply]
    rw [jet.secondDerivative_symmetric second first]
    module

/-! ## Smooth fixed-chart derivative fields -/

theorem d9PrimitiveSpinCLocalFirstDerivative_contMDiffOn
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (index : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, SpinCFirstDerivative) ∞
      (fun current : ThroatBase period hPeriod =>
        fderiv Real
          (d9PrimitiveSpinCSectionTrivializationChartRepresentative
            period hPeriod choice state index.1 index.2)
          (extChartAt throatCoverModelWithCorners index.2 current))
      (throatSpinCSecondOrderJetBundleBaseSet period hPeriod index) := by
  intro current hCurrent
  have hGerm :=
    d9PrimitiveSpinCSectionTrivializationChartRepresentative_contDiffAt_infty
      period hPeriod choice state index.1 index.2 current
        hCurrent.1 hCurrent.2
  have hDerivative := hGerm.fderiv_right (m := ∞) (by simp)
  have hChart : ContMDiffAt throatCoverModelWithCorners
      𝓘(Real, ThroatCoverCoordinates) ∞
      (extChartAt throatCoverModelWithCorners index.2) current := by
    apply contMDiffAt_extChartAt'
    simpa only [extChartAt_source] using hCurrent.2
  exact (hDerivative.contMDiffAt.comp current hChart).contMDiffWithinAt

theorem d9PrimitiveSpinCLocalSecondDerivative_contMDiffOn
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (index : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, ThroatCoverCoordinates →L[Real] SpinCFirstDerivative) ∞
      (fun current : ThroatBase period hPeriod =>
        fderiv Real
          (fderiv Real
            (d9PrimitiveSpinCSectionTrivializationChartRepresentative
              period hPeriod choice state index.1 index.2))
          (extChartAt throatCoverModelWithCorners index.2 current))
      (throatSpinCSecondOrderJetBundleBaseSet period hPeriod index) := by
  intro current hCurrent
  have hGerm :=
    d9PrimitiveSpinCSectionTrivializationChartRepresentative_contDiffAt_infty
      period hPeriod choice state index.1 index.2 current
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

/-- Totalized SpinC second-jet representative in one fixed atlas patch. -/
def actualThroatSpinCSecondOrderJetLocalRepresentative
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (index : BundleIndex period hPeriod)
    (current : ThroatBase period hPeriod) : SpinCJet := by
  classical
  exact if hCurrent : current ∈
      throatSpinCSecondOrderJetBundleBaseSet period hPeriod index then
    d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt period hPeriod
      choice state index.1 index.2 current hCurrent.1 hCurrent.2
  else 0

/-- On its atlas patch, the totalized representative is the arbitrary
trivialization/chart extraction. -/
theorem actualThroatSpinCSecondOrderJetLocalRepresentative_eq_of_mem
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (index : BundleIndex period hPeriod)
    (current : ThroatBase period hPeriod)
    (hCurrent : current ∈
      throatSpinCSecondOrderJetBundleBaseSet period hPeriod index) :
    actualThroatSpinCSecondOrderJetLocalRepresentative period hPeriod choice
        state index current =
      d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt period hPeriod
        choice state index.1 index.2 current hCurrent.1 hCurrent.2 := by
  simp only [actualThroatSpinCSecondOrderJetLocalRepresentative, dif_pos hCurrent]

private theorem actualThroatSpinCSecondOrderJetLocalRepresentative_value_contMDiffOn
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (index : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners 𝓘(Real, D9DoubledMatterFiber) ∞
      (fun current : ThroatBase period hPeriod =>
        (actualThroatSpinCSecondOrderJetLocalRepresentative period hPeriod
          choice state index current).value)
      (throatSpinCSecondOrderJetBundleBaseSet period hPeriod index) := by
  apply ((d9PrimitiveSpinCSmoothSectionLocalValue_contMDiffOn period hPeriod
    choice state index.1).mono (by
      intro current hCurrent
      exact hCurrent.1)).congr
  intro current hCurrent
  unfold actualThroatSpinCSecondOrderJetLocalRepresentative
  split
  · rw [d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt_value]
  · contradiction

private theorem actualThroatSpinCSecondOrderJetLocalRepresentative_firstDerivative_contMDiffOn
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (index : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, SpinCFirstDerivative) ∞
      (fun current : ThroatBase period hPeriod =>
        (actualThroatSpinCSecondOrderJetLocalRepresentative period hPeriod
          choice state index current).firstDerivative)
      (throatSpinCSecondOrderJetBundleBaseSet period hPeriod index) := by
  apply (d9PrimitiveSpinCLocalFirstDerivative_contMDiffOn period hPeriod
    choice state index).congr
  intro current hCurrent
  unfold actualThroatSpinCSecondOrderJetLocalRepresentative
  split
  · rw [d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt_firstDerivative]
  · contradiction

private theorem actualThroatSpinCSecondOrderJetLocalRepresentative_secondDerivative_contMDiffOn
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (index : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, ThroatCoverCoordinates →L[Real] SpinCFirstDerivative) ∞
      (fun current : ThroatBase period hPeriod =>
        (actualThroatSpinCSecondOrderJetLocalRepresentative period hPeriod
          choice state index current).secondDerivative)
      (throatSpinCSecondOrderJetBundleBaseSet period hPeriod index) := by
  apply (d9PrimitiveSpinCLocalSecondDerivative_contMDiffOn period hPeriod
    choice state index).congr
  intro current hCurrent
  unfold actualThroatSpinCSecondOrderJetLocalRepresentative
  split
  · rw [d9PrimitiveSpinCSectionSecondOrderJetInTrivializationChartAt_secondDerivative]
  · contradiction

/-- The value, Jacobian and Hessian of a smooth primitive SpinC section form
a `C∞` raw framed second jet on every fixed atlas patch. -/
theorem actualThroatSpinCSecondOrderJetLocalRepresentative_contMDiffOn
    (choice : NormalRootChoice)
    (state : D9PrimitiveSpinCSmoothSection period hPeriod choice)
    (index : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners 𝓘(Real, SpinCJet) ∞
      (actualThroatSpinCSecondOrderJetLocalRepresentative period hPeriod
        choice state index)
      (throatSpinCSecondOrderJetBundleBaseSet period hPeriod index) := by
  have hValue :=
    actualThroatSpinCSecondOrderJetLocalRepresentative_value_contMDiffOn
      period hPeriod choice state index
  have hFirstDerivative :=
    actualThroatSpinCSecondOrderJetLocalRepresentative_firstDerivative_contMDiffOn
      period hPeriod choice state index
  have hSecondDerivative :=
    actualThroatSpinCSecondOrderJetLocalRepresentative_secondDerivative_contMDiffOn
      period hPeriod choice state index
  have hComponents : ContMDiffOn throatCoverModelWithCorners
      𝓘(Real, FramedSecondOrderJetAmbient
        ThroatCoverCoordinates D9DoubledMatterFiber) ∞
      (fun current : ThroatBase period hPeriod =>
        ((actualThroatSpinCSecondOrderJetLocalRepresentative period hPeriod
            choice state index current).value,
          (actualThroatSpinCSecondOrderJetLocalRepresentative period hPeriod
            choice state index current).firstDerivative,
          (actualThroatSpinCSecondOrderJetLocalRepresentative period hPeriod
            choice state index current).secondDerivative))
      (throatSpinCSecondOrderJetBundleBaseSet period hPeriod index) := by
    rw [contMDiffOn_prod_module_iff]
    constructor
    · change ContMDiffOn throatCoverModelWithCorners _ ∞
        (fun current =>
          (actualThroatSpinCSecondOrderJetLocalRepresentative period hPeriod
            choice state index current).value) _
      exact hValue
    · rw [contMDiffOn_prod_module_iff]
      constructor
      · change ContMDiffOn throatCoverModelWithCorners _ ∞
          (fun current =>
            (actualThroatSpinCSecondOrderJetLocalRepresentative period hPeriod
              choice state index current).firstDerivative) _
        exact hFirstDerivative
      · change ContMDiffOn throatCoverModelWithCorners _ ∞
          (fun current =>
            (actualThroatSpinCSecondOrderJetLocalRepresentative period hPeriod
              choice state index current).secondDerivative) _
        exact hSecondDerivative
  have hBack :=
    symmetrizedSpinCJetContinuousLinearMap.contMDiff.comp_contMDiffOn
      hComponents
  apply hBack.congr
  intro current _
  exact
    (symmetrizedSpinCJetContinuousLinearMap_components
      (actualThroatSpinCSecondOrderJetLocalRepresentative period hPeriod
        choice state index current)).symm

/-! ## Global gauge-fixed wrapper -/

/-- Local SpinC second-jet representative of one physical sector. -/
def globalGaugeFixedSpinCMatterSecondOrderJetLocalRepresentative
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector)
    (index : BundleIndex period hPeriod) :
    ThroatBase period hPeriod → SpinCJet :=
  actualThroatSpinCSecondOrderJetLocalRepresentative period hPeriod
    .positiveQuarter (configuration.physical.spinCMatter sector) index

theorem globalGaugeFixedSpinCMatterSecondOrderJetLocalRepresentative_eq_of_mem
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector)
    (index : BundleIndex period hPeriod)
    (current : ThroatBase period hPeriod)
    (hCurrent : current ∈
      throatSpinCSecondOrderJetBundleBaseSet period hPeriod index) :
    globalGaugeFixedSpinCMatterSecondOrderJetLocalRepresentative period hPeriod
        configuration sector index current =
      globalGaugeFixedSpinCMatterSecondOrderJetInTrivializationChartAt
        period hPeriod configuration sector index.1 index.2 current
          hCurrent.1 hCurrent.2 :=
  actualThroatSpinCSecondOrderJetLocalRepresentative_eq_of_mem period hPeriod
    .positiveQuarter (configuration.physical.spinCMatter sector) index current
      hCurrent

/-- Every gauge-fixed physical SpinC sector has a `C∞` local second-jet
representative on each atlas patch. -/
theorem globalGaugeFixedSpinCMatterSecondOrderJetLocalRepresentative_contMDiffOn
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector)
    (index : BundleIndex period hPeriod) :
    ContMDiffOn throatCoverModelWithCorners 𝓘(Real, SpinCJet) ∞
      (globalGaugeFixedSpinCMatterSecondOrderJetLocalRepresentative period
        hPeriod configuration sector index)
      (throatSpinCSecondOrderJetBundleBaseSet period hPeriod index) :=
  actualThroatSpinCSecondOrderJetLocalRepresentative_contMDiffOn period hPeriod
    .positiveQuarter (configuration.physical.spinCMatter sector) index

end
end P0EFTJanusProgramPActualThroatSpinCSecondOrderJetLocalSectionSmoothness4D
end JanusFormal
