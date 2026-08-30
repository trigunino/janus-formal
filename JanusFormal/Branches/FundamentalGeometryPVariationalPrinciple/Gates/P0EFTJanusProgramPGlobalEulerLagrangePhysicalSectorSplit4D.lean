import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeBlockDecomposition4D

/-!
# Physical-sector split of the global Euler--Lagrange equation

An identified variational-chart tangent is transported to the actual
D10-free physical tangent.  Its Euler equation is then equivalent to the two
component equations on the non-SpinC bulk sector and the SpinC matter sector.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangePhysicalSectorSplit4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open MeasureTheory
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalEulerLagrangeBlockDecomposition4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D

universe u v

/-- Inclusion of the first summand into a product module. -/
def productFirstInclusion
    (First : Type u) (Second : Type v)
    [AddCommGroup First] [Module Real First]
    [AddCommGroup Second] [Module Real Second] :
    First →ₗ[Real] (First × Second) where
  toFun := fun first => (first, 0)
  map_add' := by intro first second; ext <;> simp
  map_smul' := by intro scalar first; ext <;> simp

/-- Inclusion of the second summand into a product module. -/
def productSecondInclusion
    (First : Type u) (Second : Type v)
    [AddCommGroup First] [Module Real First]
    [AddCommGroup Second] [Module Real Second] :
    Second →ₗ[Real] (First × Second) where
  toFun := fun second => (0, second)
  map_add' := by intro first second; ext <;> simp
  map_smul' := by intro scalar second; ext <;> simp

/-- First component of a covector on a product tangent. -/
def productCovectorFirst
    {First : Type u} {Second : Type v}
    [AddCommGroup First] [Module Real First]
    [AddCommGroup Second] [Module Real Second]
    (covector : First × Second →ₗ[Real] Real) : First →ₗ[Real] Real :=
  covector.comp (productFirstInclusion First Second)

/-- Second component of a covector on a product tangent. -/
def productCovectorSecond
    {First : Type u} {Second : Type v}
    [AddCommGroup First] [Module Real First]
    [AddCommGroup Second] [Module Real Second]
    (covector : First × Second →ₗ[Real] Real) : Second →ₗ[Real] Real :=
  covector.comp (productSecondInclusion First Second)

/-- A product covector vanishes exactly when both sector restrictions vanish. -/
theorem productCovector_eq_zero_iff
    {First : Type u} {Second : Type v}
    [AddCommGroup First] [Module Real First]
    [AddCommGroup Second] [Module Real Second]
    (covector : First × Second →ₗ[Real] Real) :
    covector = 0 ↔
      productCovectorFirst covector = 0 ∧
        productCovectorSecond covector = 0 := by
  constructor
  · intro h
    subst covector
    constructor
    · apply LinearMap.ext
      intro first
      simp [productCovectorFirst]
    · apply LinearMap.ext
      intro second
      simp [productCovectorSecond]
  · rintro ⟨hFirst, hSecond⟩
    apply LinearMap.ext
    intro direction
    rcases direction with ⟨first, second⟩
    have hFirstApply : covector (first, 0) = 0 := by
      have h := congrArg (fun map => map first) hFirst
      simpa [productCovectorFirst, productFirstInclusion] using h
    have hSecondApply : covector (0, second) = 0 := by
      have h := congrArg (fun map => map second) hSecond
      simpa [productCovectorSecond, productSecondInclusion] using h
    rw [show (first, second) = (first, 0) + (0, second) by ext <;> simp,
      map_add, hFirstApply, hSecondApply]
    simp

/-- Pullback by a continuous linear equivalence reflects covector vanishing. -/
theorem covector_comp_equiv_symm_eq_zero_iff
    {Model : Type u} {Physical : Type v}
    [AddCommGroup Model] [Module Real Model]
    [AddCommGroup Physical] [Module Real Physical]
    (equiv : Model ≃ₗ[Real] Physical)
    (covector : Model →ₗ[Real] Real) :
    covector.comp equiv.symm.toLinearMap = 0 ↔ covector = 0 := by
  constructor
  · intro h
    apply LinearMap.ext
    intro direction
    have hApply := congrArg (fun map => map (equiv direction)) h
    simpa using hApply
  · intro h
    subst covector
    simp

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
  GlobalCandidateAVariationalChart.normedAddCommGroup
  GlobalCandidateAVariationalChart.normedSpace

/-- Identification of a chart tangent with the actual D10-free physical
tangent at the represented global configuration. -/
structure GlobalCandidateAPhysicalTangentChartBridge
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (point : chart.Configuration) where
  physicalConfiguration : GlobalFieldConfiguration period hPeriod
  represents :
    chart.family.configurationAt point = physicalConfiguration
  tangentEquiv :
    chart.Configuration ≃ₗ[Real]
      GlobalPhysicalFieldTangent period hPeriod physicalConfiguration

/-- Euler covector transported from the chart to the actual physical tangent. -/
def globalPhysicalEulerCovectorAt
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure}
    {point : chart.Configuration}
    (bridge : GlobalCandidateAPhysicalTangentChartBridge
      period hPeriod chart point) :
    GlobalPhysicalFieldTangent period hPeriod bridge.physicalConfiguration
      →ₗ[Real] Real :=
  (globalEulerLagrangeOperator period hPeriod chart point).toLinearMap.comp
    bridge.tangentEquiv.symm.toLinearMap

/-- Non-SpinC bulk component of the transported physical Euler covector. -/
def globalPhysicalBulkEulerCovectorAt
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure}
    {point : chart.Configuration}
    (bridge : GlobalCandidateAPhysicalTangentChartBridge
      period hPeriod chart point) :
    GeneralMetricMatterFreeVariation period hPeriod →ₗ[Real] Real :=
  productCovectorFirst (globalPhysicalEulerCovectorAt period hPeriod bridge)

/-- Primitive SpinC-matter component of the transported Euler covector. -/
def globalPhysicalSpinCMatterEulerCovectorAt
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure}
    {point : chart.Configuration}
    (bridge : GlobalCandidateAPhysicalTangentChartBridge
      period hPeriod chart point) :
    (Sector → D9PrimitiveSpinCSmoothSection
      period hPeriod .positiveQuarter) →ₗ[Real] Real :=
  productCovectorSecond (globalPhysicalEulerCovectorAt period hPeriod bridge)

/-- The physical Euler covector evaluates as the exact nine-block sum on the
corresponding chart direction. -/
theorem globalPhysicalEulerCovectorAt_apply_eq_blockSum
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure}
    {point : chart.Configuration}
    (bridge : GlobalCandidateAPhysicalTangentChartBridge
      period hPeriod chart point)
    (variation : GlobalPhysicalFieldTangent period hPeriod
      bridge.physicalConfiguration) :
    globalPhysicalEulerCovectorAt period hPeriod bridge variation =
      fullCoupledEulerBlockSum
        (globalCandidateAActionBlocks period hPeriod chart.family measure)
        point (bridge.tangentEquiv.symm variation) := by
  unfold globalPhysicalEulerCovectorAt
  rw [globalEulerLagrangeOperator_eq_blockSum period hPeriod chart]
  rfl

/-- Bulk-sector equation as the nine-block sum on a pure bulk variation. -/
theorem globalPhysicalBulkEulerCovectorAt_apply_eq_blockSum
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure}
    {point : chart.Configuration}
    (bridge : GlobalCandidateAPhysicalTangentChartBridge
      period hPeriod chart point)
    (variation : GeneralMetricMatterFreeVariation period hPeriod) :
    globalPhysicalBulkEulerCovectorAt period hPeriod bridge variation =
      fullCoupledEulerBlockSum
        (globalCandidateAActionBlocks period hPeriod chart.family measure)
        point (bridge.tangentEquiv.symm (variation, 0)) := by
  change globalPhysicalEulerCovectorAt period hPeriod bridge (variation, 0) = _
  exact globalPhysicalEulerCovectorAt_apply_eq_blockSum
    period hPeriod bridge (variation, 0)

/-- SpinC-sector equation as the nine-block sum on a pure matter variation. -/
theorem globalPhysicalSpinCMatterEulerCovectorAt_apply_eq_blockSum
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure}
    {point : chart.Configuration}
    (bridge : GlobalCandidateAPhysicalTangentChartBridge
      period hPeriod chart point)
    (variation : Sector → D9PrimitiveSpinCSmoothSection
      period hPeriod .positiveQuarter) :
    globalPhysicalSpinCMatterEulerCovectorAt period hPeriod bridge variation =
      fullCoupledEulerBlockSum
        (globalCandidateAActionBlocks period hPeriod chart.family measure)
        point (bridge.tangentEquiv.symm (0, variation)) := by
  change globalPhysicalEulerCovectorAt period hPeriod bridge (0, variation) = _
  exact globalPhysicalEulerCovectorAt_apply_eq_blockSum
    period hPeriod bridge (0, variation)

/-- The chart Euler equation is exactly the coupled bulk and SpinC-matter
sector system on the actual D10-free physical tangent. -/
theorem globalEulerLagrangeOperator_eq_zero_iff_physicalSectors
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure}
    {point : chart.Configuration}
    (bridge : GlobalCandidateAPhysicalTangentChartBridge
      period hPeriod chart point) :
    globalEulerLagrangeOperator period hPeriod chart point = 0 ↔
      globalPhysicalBulkEulerCovectorAt period hPeriod bridge = 0 ∧
        globalPhysicalSpinCMatterEulerCovectorAt period hPeriod bridge = 0 := by
  let euler := globalEulerLagrangeOperator period hPeriod chart point
  let physical := globalPhysicalEulerCovectorAt period hPeriod bridge
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

end
end P0EFTJanusProgramPGlobalEulerLagrangePhysicalSectorSplit4D
end JanusFormal
