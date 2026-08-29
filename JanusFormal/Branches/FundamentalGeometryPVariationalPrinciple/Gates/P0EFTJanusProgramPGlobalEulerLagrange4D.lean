import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCovariantAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFullCoupledHelmholtzAssembly4D

/-!
# Global Euler--Lagrange operator for the assembled Candidate-A action

The global field space is a nonlinear regular domain, so its differential is
defined chartwise.  A variational chart below is not a second action: every
one of its nine blocks is definitionally one of the terms of
`globalCandidateACovariantAction`.  The only chart data are the common
configuration parametrization and the termwise `C²` regularity needed for
Fréchet calculus.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrange4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open scoped Manifold ContDiff
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPFullCoupledHelmholtzAssembly4D
open P0EFTJanusConvexHelmholtzReconstruction

universe u

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

/-- One parametrized family of the exact global action data. -/
structure GlobalCandidateAActionFamily
    (Configuration : Type u)
    (couplings : GlobalCandidateAActionCouplings)
    (NonNullFace NullFace : Type*)
    [Fintype NonNullFace] [Fintype NullFace] where
  configurationAt :
    Configuration → GlobalFieldConfiguration period hPeriod
  dataAt : ∀ configuration,
    GlobalCandidateAActionData period hPeriod
      (configurationAt configuration) couplings NonNullFace NullFace

/-- The nine exact blocks of the global Candidate-A action in one common
configuration chart.  `robin` is the non-null GHY block and `finiteBV` is the
finite null-face/counterterm/joint block. -/
def globalCandidateAActionBlocks
    {Configuration : Type u}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (family : GlobalCandidateAActionFamily period hPeriod Configuration
      couplings NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod)) :
    FullCoupledActionBlocks Configuration where
  candidateA := fun configuration =>
    globalCandidateAInteractionAction period hPeriod
      (family.dataAt configuration) measure
  matter := fun configuration =>
    globalCandidateAMatterAction period hPeriod
      (family.configurationAt configuration) couplings
  robin := fun configuration =>
    globalCandidateAGHYAction period hPeriod
      (family.dataAt configuration)
  ll := fun configuration =>
    globalCandidateALLAction period hPeriod
      (family.dataAt configuration)
  einsteinHilbertPlus := fun configuration =>
    intrinsicEinsteinHilbertAction period hPeriod couplings.plusEinstein
      (family.dataAt configuration).plusGravity measure
  einsteinHilbertMinus := fun configuration =>
    intrinsicEinsteinHilbertAction period hPeriod couplings.minusEinstein
      (family.dataAt configuration).minusGravity measure
  maxwellPlus := fun configuration =>
    couplings.plusMaxwellScale *
      intrinsicMaxwellAction period hPeriod
        (family.dataAt configuration).plusGravity.metric
        (family.dataAt configuration).plusMaxwell.basePairing measure
  maxwellMinus := fun configuration =>
    couplings.minusMaxwellScale *
      intrinsicMaxwellAction period hPeriod
        (family.dataAt configuration).minusGravity.metric
        (family.dataAt configuration).minusMaxwell.basePairing measure
  finiteBV := fun configuration =>
    globalCandidateANullBoundaryAction period hPeriod
      (family.dataAt configuration)

/-- The nine-block presentation is exactly the already assembled global
action, not merely an action with the same equations. -/
theorem globalCandidateAActionBlocks_sum
    {Configuration : Type u}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (family : GlobalCandidateAActionFamily period hPeriod Configuration
      couplings NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (configuration : Configuration) :
    fullCoupledAction
        (globalCandidateAActionBlocks period hPeriod family measure)
        configuration =
      globalCandidateACovariantAction period hPeriod
        (family.dataAt configuration) measure := by
  unfold fullCoupledAction globalCandidateAActionBlocks
    globalCandidateACovariantAction
    globalCandidateAEinsteinHilbertAction
    globalCandidateAMaxwellAction
  ring

/-- A regular chart of the nonlinear physical configuration domain.
Regularity is recorded term by term on the exact action blocks. -/
structure GlobalCandidateAVariationalChart
    (couplings : GlobalCandidateAActionCouplings)
    (NonNullFace NullFace : Type*)
    [Fintype NonNullFace] [Fintype NullFace]
    (measure : Measure (EffectiveQuotient period hPeriod)) where
  Configuration : Type u
  normedAddCommGroup : NormedAddCommGroup Configuration
  normedSpace : NormedSpace Real Configuration
  family :
    GlobalCandidateAActionFamily period hPeriod Configuration couplings
      NonNullFace NullFace
  blocksC2 : ∀ configuration,
    @FullCoupledC2At Configuration normedAddCommGroup normedSpace
      (globalCandidateAActionBlocks period hPeriod family measure)
      configuration

attribute [local instance]
  GlobalCandidateAVariationalChart.normedAddCommGroup
  GlobalCandidateAVariationalChart.normedSpace

/-- Pullback of the exact physical action to one admissible chart. -/
def globalCandidateAActionPullback
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure) :
    chart.Configuration → Real :=
  fun configuration =>
    globalCandidateACovariantAction period hPeriod
      (chart.family.dataAt configuration) measure

theorem globalCandidateAActionPullback_eq_blocks
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure) :
    globalCandidateAActionPullback period hPeriod chart =
      fullCoupledAction
        (globalCandidateAActionBlocks period hPeriod chart.family measure) := by
  funext configuration
  exact (globalCandidateAActionBlocks_sum period hPeriod chart.family measure
    configuration).symm

/-- The full exact action is genuinely `C²` on every admissible chart. -/
theorem globalCandidateAActionPullback_contDiff_two
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure) :
    ContDiff Real 2
      (globalCandidateAActionPullback period hPeriod chart) := by
  rw [globalCandidateAActionPullback_eq_blocks period hPeriod chart]
  rw [contDiff_iff_contDiffAt]
  intro configuration
  exact fullCoupledAction_contDiffAt
    (globalCandidateAActionBlocks period hPeriod chart.family measure)
    configuration (chart.blocksC2 configuration)

/-- Complete chartwise Euler--Lagrange one-form of the exact global action. -/
noncomputable def globalEulerLagrangeOperator
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure) :
    EulerOneForm chart.Configuration :=
  actionGradient (globalCandidateAActionPullback period hPeriod chart)

/-- The displayed Euler one-form is the actual Fréchet derivative of the
same assembled action in every chart and at every configuration. -/
theorem globalCandidateAAction_hasFDerivAt
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (configuration : chart.Configuration) :
    HasFDerivAt
      (globalCandidateAActionPullback period hPeriod chart)
      (globalEulerLagrangeOperator period hPeriod chart configuration)
      configuration := by
  exact
    (globalCandidateAActionPullback_contDiff_two period hPeriod chart
      |>.contDiffAt).differentiableAt (by norm_num) |>.hasFDerivAt

@[simp]
theorem globalEulerLagrangeOperator_apply
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (configuration direction : chart.Configuration) :
    globalEulerLagrangeOperator period hPeriod chart configuration direction =
      fderiv Real (globalCandidateAActionPullback period hPeriod chart)
        configuration direction :=
  rfl

/-- Concrete global Euler closure certificate on every regular physical
chart: exact action identity, `C²` regularity, actual first derivative and
all-direction evaluation. -/
theorem global_euler_lagrange_gate
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure) :
    globalCandidateAActionPullback period hPeriod chart =
        fullCoupledAction
          (globalCandidateAActionBlocks period hPeriod chart.family measure) ∧
      ContDiff Real 2
        (globalCandidateAActionPullback period hPeriod chart) ∧
      (∀ configuration,
        HasFDerivAt
          (globalCandidateAActionPullback period hPeriod chart)
          (globalEulerLagrangeOperator period hPeriod chart configuration)
          configuration) ∧
      (∀ configuration direction,
        globalEulerLagrangeOperator period hPeriod chart configuration
            direction =
          fderiv Real
            (globalCandidateAActionPullback period hPeriod chart)
            configuration direction) := by
  exact ⟨globalCandidateAActionPullback_eq_blocks period hPeriod chart,
    globalCandidateAActionPullback_contDiff_two period hPeriod chart,
    globalCandidateAAction_hasFDerivAt period hPeriod chart,
    globalEulerLagrangeOperator_apply period hPeriod chart⟩

end
end P0EFTJanusProgramPGlobalEulerLagrange4D
end JanusFormal
