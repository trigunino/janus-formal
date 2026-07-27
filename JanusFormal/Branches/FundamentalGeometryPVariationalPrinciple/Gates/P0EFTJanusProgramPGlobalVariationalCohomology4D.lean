import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHelmholtzReconstruction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalNaturalClassification4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusBoundaryCountertermHelmholtz

/-!
# Global functional variational cohomology for Candidate A

On each regular convex chart, the global Euler one-form is exact.  Functional
null Lagrangians are therefore precisely constants, two primitives with the
same Euler form differ by one constant, and normalization removes that
ambiguity.  The finite six-invariant natural evaluator has no hidden kernel.
The already assembled physical boundary residual remains identically zero.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalVariationalCohomology4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open scoped Manifold ContDiff
open MeasureTheory Set
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalBoundaryCompletion4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalHelmholtzReconstruction4D
open P0EFTJanusProgramPGlobalNaturalClassification4D
open P0EFTJanusProgramPNaturalOperatorClassification4D
open P0EFTJanusNaturalLowerOrderFreedom
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusBoundaryCountertermHelmholtz

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

attribute [local instance]
  GlobalCandidateAVariationalChart.normedAddCommGroup
  GlobalCandidateAVariationalChart.normedSpace

/-- A functional null Lagrangian has zero actual Fréchet derivative
everywhere on its normed chart. -/
def VariationallyNull
    {Configuration : Type u}
    [NormedAddCommGroup Configuration] [NormedSpace Real Configuration]
    (lagrangian : Configuration → Real) : Prop :=
  ∀ configuration,
    HasFDerivAt lagrangian (0 : Configuration →L[Real] Real) configuration

/-- Complete functional null-Lagrangian classification on a real normed
vector chart: zero variation is equivalent to being constant. -/
theorem variationallyNull_iff_exists_constant
    {Configuration : Type u}
    [NormedAddCommGroup Configuration] [NormedSpace Real Configuration]
    (lagrangian : Configuration → Real) :
    VariationallyNull lagrangian ↔
      ∃ constant : Real, ∀ configuration, lagrangian configuration = constant := by
  constructor
  · intro hNull
    obtain ⟨constant, hConstant⟩ :=
      convex_actions_same_euler_differ_by_constant
        (domain := Set.univ)
        (euler := fun _ => (0 : Configuration →L[Real] Real))
        (firstAction := lagrangian)
        (secondAction := fun _ => (0 : Real))
        convex_univ Set.univ_nonempty
        (by intro configuration _; exact hNull configuration)
        (by
          intro configuration _
          exact hasFDerivAt_const (x := configuration) (c := (0 : Real)))
    exact ⟨constant, fun configuration => by
      simpa using hConstant configuration (Set.mem_univ configuration)⟩
  · rintro ⟨constant, hConstant⟩ configuration
    have hFunction : lagrangian = fun _ => constant := by
      funext point
      exact hConstant point
    rw [hFunction]
    exact hasFDerivAt_const (x := configuration) (c := constant)

/-- Vanishing of the global functional variational obstruction means that the
Euler one-form is the actual derivative of a scalar action. -/
def GlobalVariationalObstructionVanishes
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure) : Prop :=
  ∃ action : chart.Configuration → Real,
    ∀ configuration,
      HasFDerivAt action
        (globalEulerLagrangeOperator period hPeriod chart configuration)
        configuration

/-- The global functional obstruction vanishes for the exact assembled
Candidate-A action.  This is deliberately not a claim about the full local
horizontal variational bicomplex of jet densities. -/
theorem globalFunctionalVariationalObstructionVanishing
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure) :
    GlobalVariationalObstructionVanishes period hPeriod chart := by
  exact ⟨globalCandidateAActionPullback period hPeriod chart,
    globalCandidateAAction_hasFDerivAt period hPeriod chart⟩

/-- Two global action representatives with the same actual Euler derivative
have only the expected additive ambiguity. -/
theorem sameGlobalEulerActions_differ_by_constant
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (firstAction secondAction : chart.Configuration → Real)
    (hFirst : ∀ configuration,
      HasFDerivAt firstAction
        (globalEulerLagrangeOperator period hPeriod chart configuration)
        configuration)
    (hSecond : ∀ configuration,
      HasFDerivAt secondAction
        (globalEulerLagrangeOperator period hPeriod chart configuration)
        configuration) :
    ∃ constant : Real, ∀ configuration,
      firstAction configuration = secondAction configuration + constant := by
  simpa using
    (convex_actions_same_euler_differ_by_constant
      (domain := Set.univ)
      (euler := globalEulerLagrangeOperator period hPeriod chart)
      (firstAction := firstAction) (secondAction := secondAction)
      convex_univ Set.univ_nonempty
      (by intro configuration _; exact hFirst configuration)
      (by intro configuration _; exact hSecond configuration))

/-- Zero coefficient family in the classified six-invariant EFT truncation. -/
def zeroJanusNaturalLocalCoefficients :
    JanusNaturalLocalCoefficients :=
  fun _ => zeroNaturalCouplings

theorem janusNaturalLocalEvaluator_zero :
    janusNaturalLocalEvaluator zeroJanusNaturalLocalCoefficients = 0 := by
  funext sector jet
  simp [janusNaturalLocalEvaluator, programPLowerOrderEvaluator,
    zeroJanusNaturalLocalCoefficients, naturalPotential,
    zeroNaturalCouplings]

/-- There are no hidden null local combinations inside the classified
six-invariant natural basis. -/
theorem janusNaturalNullCoefficient_iff_zero
    (coefficients : JanusNaturalLocalCoefficients) :
    janusNaturalLocalEvaluator coefficients = 0 ↔
      coefficients = zeroJanusNaturalLocalCoefficients := by
  constructor
  · intro hZero
    apply janusNaturalLocalEvaluator_injective
    rw [hZero, janusNaturalLocalEvaluator_zero]
  · rintro rfl
    exact janusNaturalLocalEvaluator_zero

/-- Any two cancelling boundary counterterms for the same global Euler flux
differ by one constant. -/
theorem globalBoundaryCounterterms_differ_by_constant
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (firstCounterterm secondCounterterm : chart.Configuration → Real)
    (hFirst : ∀ configuration,
      HasFDerivAt firstCounterterm
        (-globalEulerLagrangeOperator period hPeriod chart configuration)
        configuration)
    (hSecond : ∀ configuration,
      HasFDerivAt secondCounterterm
        (-globalEulerLagrangeOperator period hPeriod chart configuration)
        configuration) :
    ∃ constant : Real, ∀ configuration,
      firstCounterterm configuration =
        secondCounterterm configuration + constant :=
  cancelling_counterterms_differ_by_constant
    (globalEulerLagrangeOperator period hPeriod chart)
    firstCounterterm secondCounterterm hFirst hSecond

/-- The physical GHY/null/joint/LL residual attached to every chart point is
already zero on arbitrary LL directions. -/
theorem globalPhysicalBoundaryResidual_eq_zero
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (configuration : chart.Configuration)
    (llDirection : SmoothThroatField period hPeriod LLFieldFiber) :
    (chart.family.dataAt configuration).boundary.totalResidual
        period hPeriod llDirection = 0 :=
  (chart.family.dataAt configuration).boundary.totalResidual_eq_zero
    period hPeriod llDirection

/-- Global variational-cohomology closure: exact Euler class, complete
functional null classification, faithful finite natural basis, additive
boundary ambiguity and physical boundary cancellation. -/
theorem global_variational_cohomology_gate
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure) :
    GlobalVariationalObstructionVanishes period hPeriod chart ∧
      (∀ lagrangian : chart.Configuration → Real,
        VariationallyNull lagrangian ↔
          ∃ constant : Real, ∀ configuration,
            lagrangian configuration = constant) ∧
      (∀ coefficients : JanusNaturalLocalCoefficients,
        janusNaturalLocalEvaluator coefficients = 0 ↔
          coefficients = zeroJanusNaturalLocalCoefficients) ∧
      (∀ firstCounterterm secondCounterterm : chart.Configuration → Real,
        (∀ configuration,
          HasFDerivAt firstCounterterm
            (-globalEulerLagrangeOperator period hPeriod chart configuration)
            configuration) →
        (∀ configuration,
          HasFDerivAt secondCounterterm
            (-globalEulerLagrangeOperator period hPeriod chart configuration)
            configuration) →
        ∃ constant : Real, ∀ configuration,
          firstCounterterm configuration =
            secondCounterterm configuration + constant) ∧
      (∀ configuration llDirection,
        (chart.family.dataAt configuration).boundary.totalResidual
          period hPeriod llDirection = 0) := by
  exact ⟨globalFunctionalVariationalObstructionVanishing period hPeriod chart,
    variationallyNull_iff_exists_constant,
    janusNaturalNullCoefficient_iff_zero,
    globalBoundaryCounterterms_differ_by_constant period hPeriod chart,
    globalPhysicalBoundaryResidual_eq_zero period hPeriod chart⟩

end
end P0EFTJanusProgramPGlobalVariationalCohomology4D
end JanusFormal
