import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeAtlasDescent4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangePhysicalSectorSplit4D

/-!
# Atlas-descended physical-sector Euler system

This gate connects local atlas criticality to the non-SpinC bulk and primitive
SpinC matter equations after an algebraic identification with the actual
D10-free physical tangent.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeAtlasPhysicalSectorSystem4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Topology
open MeasureTheory
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeAtlasDescent4D
open P0EFTJanusProgramPGlobalEulerLagrangeBlockDecomposition4D
open P0EFTJanusProgramPGlobalEulerLagrangePhysicalSectorSplit4D
open P0EFTJanusProgramPFullCoupledHelmholtzAssembly4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D

universe u v

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

/-- Algebraic identification of a local chart model with the actual physical
tangent at the represented configuration. -/
structure GlobalCandidateALocalPhysicalTangentChartBridge
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (point : chart.Model) (hPoint : point ∈ chart.family.domain) where
  tangentEquiv :
    chart.Model ≃ₗ[Real]
      GlobalPhysicalFieldTangent period hPeriod
        (chart.family.datumAt point hPoint).1

/-- Local Euler covector transported to the actual physical tangent. -/
def globalCandidateALocalPhysicalEulerCovectorAt
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure}
    {point : chart.Model} {hPoint : point ∈ chart.family.domain}
    (bridge : GlobalCandidateALocalPhysicalTangentChartBridge
      period hPeriod chart point hPoint) :
    GlobalPhysicalFieldTangent period hPeriod
        (chart.family.datumAt point hPoint).1 →ₗ[Real] Real :=
  (globalCandidateALocalEulerLagrangeOperator period hPeriod chart point).toLinearMap.comp
    bridge.tangentEquiv.symm.toLinearMap

/-- Non-SpinC bulk component of the local physical Euler equation. -/
def globalCandidateALocalPhysicalBulkEulerCovectorAt
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure}
    {point : chart.Model} {hPoint : point ∈ chart.family.domain}
    (bridge : GlobalCandidateALocalPhysicalTangentChartBridge
      period hPeriod chart point hPoint) :
    GeneralMetricMatterFreeVariation period hPeriod →ₗ[Real] Real :=
  productCovectorFirst
    (globalCandidateALocalPhysicalEulerCovectorAt period hPeriod bridge)

/-- Primitive SpinC-matter component of the local physical Euler equation. -/
def globalCandidateALocalPhysicalSpinCMatterEulerCovectorAt
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure}
    {point : chart.Model} {hPoint : point ∈ chart.family.domain}
    (bridge : GlobalCandidateALocalPhysicalTangentChartBridge
      period hPeriod chart point hPoint) :
    (Sector → D9PrimitiveSpinCSmoothSection
      period hPeriod .positiveQuarter) →ₗ[Real] Real :=
  productCovectorSecond
    (globalCandidateALocalPhysicalEulerCovectorAt period hPeriod bridge)

/-- The transported local physical Euler covector is the exact nine-block
derivative sum at the admissible point. -/
theorem globalCandidateALocalPhysicalEulerCovectorAt_apply_eq_blockSum
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure}
    {point : chart.Model} {hPoint : point ∈ chart.family.domain}
    (bridge : GlobalCandidateALocalPhysicalTangentChartBridge
      period hPeriod chart point hPoint)
    (variation : GlobalPhysicalFieldTangent period hPeriod
      (chart.family.datumAt point hPoint).1) :
    globalCandidateALocalPhysicalEulerCovectorAt
        period hPeriod bridge variation =
      fullCoupledEulerBlockSum
        (globalCandidateAActionBlocks period hPeriod
          (chart.family.toActionFamily period hPeriod 0 chart.zero_mem_domain)
          measure)
        point (bridge.tangentEquiv.symm variation) := by
  let blocks := globalCandidateAActionBlocks period hPeriod
    (chart.family.toActionFamily period hPeriod 0 chart.zero_mem_domain) measure
  have hC2 : FullCoupledC2At blocks point :=
    fullCoupledC2WithinAt_toAt
      (chart.blocksC2Within point hPoint) chart.isOpen_domain hPoint
  unfold globalCandidateALocalPhysicalEulerCovectorAt
    globalCandidateALocalEulerLagrangeOperator
    globalCandidateALocalActionPullback
  change actionGradient (fullCoupledAction blocks) point
      (bridge.tangentEquiv.symm variation) = _
  rw [fullCoupledAction_gradient_apply_eq_blockSum blocks point hC2]

/-- Local bulk equation as the exact nine-block sum on a pure bulk tangent. -/
theorem globalCandidateALocalPhysicalBulkEulerCovectorAt_apply_eq_blockSum
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure}
    {point : chart.Model} {hPoint : point ∈ chart.family.domain}
    (bridge : GlobalCandidateALocalPhysicalTangentChartBridge
      period hPeriod chart point hPoint)
    (variation : GeneralMetricMatterFreeVariation period hPeriod) :
    globalCandidateALocalPhysicalBulkEulerCovectorAt
        period hPeriod bridge variation =
      fullCoupledEulerBlockSum
        (globalCandidateAActionBlocks period hPeriod
          (chart.family.toActionFamily period hPeriod 0 chart.zero_mem_domain)
          measure)
        point (bridge.tangentEquiv.symm (variation, 0)) := by
  change globalCandidateALocalPhysicalEulerCovectorAt
    period hPeriod bridge (variation, 0) = _
  exact globalCandidateALocalPhysicalEulerCovectorAt_apply_eq_blockSum
    period hPeriod bridge (variation, 0)

/-- Local SpinC equation as the exact nine-block sum on a pure matter tangent. -/
theorem globalCandidateALocalPhysicalSpinCMatterEulerCovectorAt_apply_eq_blockSum
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure}
    {point : chart.Model} {hPoint : point ∈ chart.family.domain}
    (bridge : GlobalCandidateALocalPhysicalTangentChartBridge
      period hPeriod chart point hPoint)
    (variation : Sector → D9PrimitiveSpinCSmoothSection
      period hPeriod .positiveQuarter) :
    globalCandidateALocalPhysicalSpinCMatterEulerCovectorAt
        period hPeriod bridge variation =
      fullCoupledEulerBlockSum
        (globalCandidateAActionBlocks period hPeriod
          (chart.family.toActionFamily period hPeriod 0 chart.zero_mem_domain)
          measure)
        point (bridge.tangentEquiv.symm (0, variation)) := by
  change globalCandidateALocalPhysicalEulerCovectorAt
    period hPeriod bridge (0, variation) = _
  exact globalCandidateALocalPhysicalEulerCovectorAt_apply_eq_blockSum
    period hPeriod bridge (0, variation)

/-- Local Euler vanishing is exactly the two-sector physical system. -/
theorem globalCandidateALocalEulerLagrangeOperator_eq_zero_iff_physicalSectors
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure}
    {point : chart.Model} {hPoint : point ∈ chart.family.domain}
    (bridge : GlobalCandidateALocalPhysicalTangentChartBridge
      period hPeriod chart point hPoint) :
    globalCandidateALocalEulerLagrangeOperator period hPeriod chart point = 0 ↔
      globalCandidateALocalPhysicalBulkEulerCovectorAt
          period hPeriod bridge = 0 ∧
        globalCandidateALocalPhysicalSpinCMatterEulerCovectorAt
          period hPeriod bridge = 0 := by
  let euler := globalCandidateALocalEulerLagrangeOperator
    period hPeriod chart point
  let physical := globalCandidateALocalPhysicalEulerCovectorAt
    period hPeriod bridge
  change euler = 0 ↔
    productCovectorFirst physical = 0 ∧ productCovectorSecond physical = 0
  rw [← productCovector_eq_zero_iff physical]
  constructor
  · intro h
    have hLinear : euler.toLinearMap = 0 := by rw [h]; rfl
    exact (covector_comp_equiv_symm_eq_zero_iff
      bridge.tangentEquiv euler.toLinearMap).2 hLinear
  · intro h
    have hLinear : euler.toLinearMap = 0 :=
      (covector_comp_equiv_symm_eq_zero_iff
        bridge.tangentEquiv euler.toLinearMap).1 h
    apply ContinuousLinearMap.ext
    intro direction
    have hApply := congrArg (fun map => map direction) hLinear
    simpa using hApply

/-- The descended atlas criticality predicate is exactly the physical
bulk/SpinC system in any represented, tangent-identified local chart. -/
theorem GlobalCandidateAVariationalAtlas.isEulerCritical_iff_physicalSectors
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (atlas : GlobalCandidateAVariationalAtlas.{u, v} period hPeriod
      (couplings := couplings) (NonNullFace := NonNullFace)
      (NullFace := NullFace) measure)
    (configuration : GlobalFieldConfiguration period hPeriod)
    (index : atlas.Index) (point : (atlas.chart index).Model)
    (hPoint : point ∈ (atlas.chart index).family.domain)
    (hRepresents : atlas.Represents period hPeriod configuration
      index point hPoint)
    (bridge : GlobalCandidateALocalPhysicalTangentChartBridge
      period hPeriod (atlas.chart index) point hPoint) :
    atlas.IsEulerCritical period hPeriod configuration ↔
      globalCandidateALocalPhysicalBulkEulerCovectorAt
          period hPeriod bridge = 0 ∧
        globalCandidateALocalPhysicalSpinCMatterEulerCovectorAt
          period hPeriod bridge = 0 := by
  rw [atlas.isEulerCritical_iff period hPeriod configuration index point
    hPoint hRepresents]
  exact globalCandidateALocalEulerLagrangeOperator_eq_zero_iff_physicalSectors
    period hPeriod bridge

end
end P0EFTJanusProgramPGlobalEulerLagrangeAtlasPhysicalSectorSystem4D
end JanusFormal
