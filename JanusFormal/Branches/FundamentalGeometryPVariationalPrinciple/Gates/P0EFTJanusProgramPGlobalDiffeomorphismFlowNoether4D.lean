import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalNoether4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusNonlinearGaugeFlowNoether

/-!
# Nonlinear diffeomorphism-flow Noether bridge for Candidate A

The existing nine-block invariant interface accepts arbitrary transformations,
while the earlier global diffeomorphism specialization uses affine chart
lines.  This gate supplies the complementary nonlinear interface: every
smooth ghost may carry a complete, field-dependent flow on one variational
chart, and invariance is checked termwise along that actual flow.

The chart measure remains fixed.  A concrete transported-measure action must
therefore either prove that its flow preserves this measure or provide a
separate identification with the fixed-measure chart.

This file deliberately gives an abstract Noether interface.  Merely indexing
a flow by a diffeomorphism ghost does not identify it with geometric pullback;
in particular, the identity flow is not excluded until a separate chart
realization is supplied.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalDiffeomorphismFlowNoether4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPFullCoupledHelmholtzAssembly4D
open P0EFTJanusProgramPGlobalNoether4D
open P0EFTJanusNonlinearGaugeFlowNoether

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

/-- Translation by one fixed chart direction as a complete gauge flow. -/
def constantTranslationGaugeFlow
    {Configuration : Type*}
    [NormedAddCommGroup Configuration] [NormedSpace Real Configuration]
    (direction : Configuration) :
    CompleteGaugeFlow Configuration where
  flow := fun parameter configuration =>
    configuration + parameter • direction
  generator := fun _ => direction
  flow_zero := by
    intro configuration
    simp
  flow_add := by
    intro first second configuration
    simp only [add_smul]
    abel
  orbit_hasDerivAt := by
    intro configuration parameter
    have hConstant :
        HasDerivAt (fun _ : Real => configuration) 0 parameter :=
      hasDerivAt_const (x := parameter) (c := configuration)
    have hLinear :=
      (hasDerivAt_id parameter).smul_const direction
    have hSum := hConstant.add hLinear
    exact hSum.congr_deriv (by simp)

/-- Abstract complete nonlinear chart flows indexed by smooth diffeomorphism
ghosts, with invariance verified separately on all nine Candidate-A blocks.
A separate geometric realization must tie these flows to actual pullback. -/
structure GlobalCandidateADiffeomorphismFlowSymmetry
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure) where
  flow :
    CInfinityDiffeomorphismGhost period hPeriod →
      CompleteGaugeFlow chart.Configuration
  blocksInvariant : ∀ ghost,
    FullCoupledInvariantUnder
      (globalCandidateAActionBlocks period hPeriod chart.family measure)
      (flow ghost).flow

/-- Every earlier affine diffeomorphism symmetry is a special case of the
nonlinear flow interface, using constant translation in its chart direction. -/
def globalCandidateADiffeomorphismGaugeSymmetry_toFlow
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure}
    (symmetry :
      GlobalCandidateADiffeomorphismGaugeSymmetry period hPeriod chart) :
    GlobalCandidateADiffeomorphismFlowSymmetry period hPeriod chart where
  flow := fun ghost =>
    constantTranslationGaugeFlow (symmetry.generator ghost)
  blocksInvariant := fun ghost => by
    constructor <;> intro parameter configuration
    · simpa [constantTranslationGaugeFlow,
        globalLinearGaugeAffineTransform] using
        symmetry.blocksInvariant.candidateA (ghost, parameter) configuration
    · simpa [constantTranslationGaugeFlow,
        globalLinearGaugeAffineTransform] using
        symmetry.blocksInvariant.matter (ghost, parameter) configuration
    · simpa [constantTranslationGaugeFlow,
        globalLinearGaugeAffineTransform] using
        symmetry.blocksInvariant.robin (ghost, parameter) configuration
    · simpa [constantTranslationGaugeFlow,
        globalLinearGaugeAffineTransform] using
        symmetry.blocksInvariant.ll (ghost, parameter) configuration
    · simpa [constantTranslationGaugeFlow,
        globalLinearGaugeAffineTransform] using
        symmetry.blocksInvariant.einsteinHilbertPlus
          (ghost, parameter) configuration
    · simpa [constantTranslationGaugeFlow,
        globalLinearGaugeAffineTransform] using
        symmetry.blocksInvariant.einsteinHilbertMinus
          (ghost, parameter) configuration
    · simpa [constantTranslationGaugeFlow,
        globalLinearGaugeAffineTransform] using
        symmetry.blocksInvariant.maxwellPlus (ghost, parameter) configuration
    · simpa [constantTranslationGaugeFlow,
        globalLinearGaugeAffineTransform] using
        symmetry.blocksInvariant.maxwellMinus (ghost, parameter) configuration
    · simpa [constantTranslationGaugeFlow,
        globalLinearGaugeAffineTransform] using
        symmetry.blocksInvariant.finiteBV (ghost, parameter) configuration

/-- Termwise invariance along one supplied ghost flow implies invariance of
the exact assembled Candidate-A action along that same nonlinear flow. -/
theorem globalCandidateAAction_diffeomorphismFlow_invariant
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (symmetry :
      GlobalCandidateADiffeomorphismFlowSymmetry period hPeriod chart)
    (ghost : CInfinityDiffeomorphismGhost period hPeriod) :
    FlowGaugeInvariant (symmetry.flow ghost)
      (globalCandidateAActionPullback period hPeriod chart) := by
  intro configuration parameter
  rw [globalCandidateAActionPullback_eq_blocks period hPeriod chart]
  exact fullCoupledAction_invariant
    (globalCandidateAActionBlocks period hPeriod chart.family measure)
    (symmetry.flow ghost).flow (symmetry.blocksInvariant ghost)
    parameter configuration

/-- The actual Euler derivative annihilates the field-dependent generator of
every supplied invariant diffeomorphism flow. -/
theorem globalEuler_annihilates_diffeomorphismFlowGenerator
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (symmetry :
      GlobalCandidateADiffeomorphismFlowSymmetry period hPeriod chart)
    (ghost : CInfinityDiffeomorphismGhost period hPeriod) :
    EulerAnnihilatesGenerator (symmetry.flow ghost)
      (globalEulerLagrangeOperator period hPeriod chart) := by
  exact euler_annihilates_generator_of_flow_gauge_invariant
    (symmetry.flow ghost)
    (globalEulerLagrangeOperator period hPeriod chart)
    (globalCandidateAActionPullback period hPeriod chart)
    (globalCandidateAAction_hasFDerivAt period hPeriod chart)
    (globalCandidateAAction_diffeomorphismFlow_invariant
      period hPeriod chart symmetry ghost)

end
end P0EFTJanusProgramPGlobalDiffeomorphismFlowNoether4D
end JanusFormal
