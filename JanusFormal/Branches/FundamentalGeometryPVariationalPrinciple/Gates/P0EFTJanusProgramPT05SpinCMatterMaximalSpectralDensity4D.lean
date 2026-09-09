import Mathlib.Topology.Sequences
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT05SpinCMatterSmoothLocalDensityBridge4D

/-!
# T05 maximal SpinC spectral-density bridge

Every state of the exact SpinC graph consists of two square-summable signed
mode families: the field and its Hessian image.  Their coordinatewise real
pairing is therefore summable by the `ℓ²` Cauchy--Schwarz theorem.  This module
packages that pairing as an honest discrete spectral density and proves that
its sum is exactly the maximal graph action.

On the dense finite graph core, the same sum is the integral of Gate 836's
continuous spacetime density.  Consequently every maximal graph action is a
limit of genuine smooth local-density integrals.

This does not construct a spacetime density for an arbitrary maximal state.
The geometric `L²` carrier is currently a `UniformSpace.Completion` of smooth
sections; the API has no realization into `MeasureTheory.Lp` or `AEEqFun`, no
almost-everywhere evaluation, and no pointwise-product map from the two graph
components into spacetime `L¹`.  Those are the exact missing ingredients for
transporting the spectral density proved here to the throat.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT05SpinCMatterMaximalSpectralDensity4D

set_option autoImplicit false
noncomputable section

open Filter Set Topology
open scoped BigOperators ENNReal lp
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPT05BulkActionLocalDensityBridge4D
open P0EFTJanusProgramPT05SpinCMatterSmoothLocalDensityBridge4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance spinCMatterHilbertRealInnerProductSpace :
    InnerProductSpace Real
      (ProgramPPrimitiveSpinCMatterHilbert) :=
  InnerProductSpace.complexToReal

/-- Coordinatewise action density on the discrete two-sector signed-mode
carrier of an arbitrary maximal graph state. -/
def programPT05SpinCMatterMaximalSpectralDensity
    (massSquared : Real)
    (state : ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
      massSquared) :
    ProgramPPrimitiveSpinCMatterMode → Real :=
  fun mode =>
    (1 / 2 : Real) *
      (inner Complex (state.1.1 mode) (state.1.2 mode)).re

/-- The maximal spectral density is a genuine discrete `L¹` family. -/
theorem programPT05SpinCMatterMaximalSpectralDensity_summable
    (massSquared : Real)
    (state : ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
      massSquared) :
    Summable
      (programPT05SpinCMatterMaximalSpectralDensity period hPeriod
        massSquared state) := by
  have hComplex : Summable (fun mode : ProgramPPrimitiveSpinCMatterMode =>
      inner Complex (state.1.1 mode) (state.1.2 mode)) :=
    lp.summable_inner (𝕜 := Complex) state.1.1 state.1.2
  have hReal : Summable (fun mode : ProgramPPrimitiveSpinCMatterMode =>
      (inner Complex (state.1.1 mode) (state.1.2 mode)).re) :=
    (Complex.hasSum_re hComplex.hasSum).summable
  unfold programPT05SpinCMatterMaximalSpectralDensity
  exact Summable.mul_left (1 / 2 : Real) hReal

/-- Summing the discrete maximal density gives exactly the closed-graph
SpinC action. -/
theorem programPT05SpinCMatterMaximalSpectralDensity_tsum_eq_graphAction
    (massSquared : Real)
    (state : ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
      massSquared) :
    (∑' mode,
      programPT05SpinCMatterMaximalSpectralDensity period hPeriod
        massSquared state mode) =
      programPPrimitiveSpinCMatterGraphAction period hPeriod massSquared
        state := by
  let term : ProgramPPrimitiveSpinCMatterMode → Complex := fun mode =>
    inner Complex (state.1.1 mode) (state.1.2 mode)
  have hComplex : Summable term :=
    lp.summable_inner (𝕜 := Complex) state.1.1 state.1.2
  have hReal : Summable (fun mode => (term mode).re) :=
    (Complex.hasSum_re hComplex.hasSum).summable
  calc
    (∑' mode,
        programPT05SpinCMatterMaximalSpectralDensity period hPeriod
          massSquared state mode) =
        (1 / 2 : Real) * ∑' mode, (term mode).re := by
      change (∑' mode, (1 / 2 : Real) * (term mode).re) =
        (1 / 2 : Real) * ∑' mode, (term mode).re
      exact hReal.tsum_mul_left (1 / 2 : Real)
    _ = (1 / 2 : Real) * (∑' mode, term mode).re := by
      rw [Complex.re_tsum hComplex]
    _ = programPPrimitiveSpinCMatterGraphAction period hPeriod massSquared
        state := by
      rw [programPPrimitiveSpinCMatterGraphAction,
        programPPrimitiveSpinCMatterGraphForm_apply,
        real_inner_eq_re_inner, lp.inner_eq_tsum]
      rfl

/-- Gate 836's spacetime density integral agrees with the graph action on the
entire finite signed-mode core. -/
theorem programPT05SpinCMatterFiniteCoreLocalDensityIntegral_eq_graphAction
    (massSquared : Real)
    (coefficients : ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    programPT05SpinCMatterSmoothLocalDensityIntegral period hPeriod
        massSquared
        (programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
          coefficients) =
      programPPrimitiveSpinCMatterGraphAction period hPeriod massSquared
        (programPPrimitiveSpinCMatterGraphFinite period hPeriod massSquared
          coefficients) :=
  (programPT05SpinCMatterSmoothLocalDensityIntegral_eq_smoothAction
    period hPeriod massSquared
      (programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
        coefficients)).trans
    (programPPrimitiveSpinCMatterSmoothAction_finite_eq_graphAction
      period hPeriod massSquared coefficients)

/-- On the finite core, integrating the continuous spacetime density and
summing the maximal spectral density are literally the same scalar. -/
theorem programPT05SpinCMatterFiniteCoreLocalDensityIntegral_eq_spectralTsum
    (massSquared : Real)
    (coefficients : ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    programPT05SpinCMatterSmoothLocalDensityIntegral period hPeriod
        massSquared
        (programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
          coefficients) =
      ∑' mode,
        programPT05SpinCMatterMaximalSpectralDensity period hPeriod
          massSquared
          (programPPrimitiveSpinCMatterGraphFinite period hPeriod massSquared
            coefficients) mode :=
  (programPT05SpinCMatterFiniteCoreLocalDensityIntegral_eq_graphAction
    period hPeriod massSquared coefficients).trans
    (programPT05SpinCMatterMaximalSpectralDensity_tsum_eq_graphAction
      period hPeriod massSquared
      (programPPrimitiveSpinCMatterGraphFinite period hPeriod massSquared
        coefficients)).symm

/-- Every maximal graph state is approximated in graph norm by finite smooth
states, and their genuine Gate-836 spacetime-density integrals converge to its
maximal spectral-density sum. -/
theorem programPT05SpinCMatter_exists_finiteCoreLocalDensityApproximation
    (massSquared : Real)
    (state : ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod
      massSquared) :
    ∃ coefficients : ℕ → ProgramPPrimitiveSpinCMatterFiniteCoefficients,
      Tendsto
          (fun index =>
            programPPrimitiveSpinCMatterGraphFinite period hPeriod massSquared
              (coefficients index))
          atTop (𝓝 state) ∧
        Tendsto
          (fun index =>
            programPT05SpinCMatterSmoothLocalDensityIntegral period hPeriod
              massSquared
              (programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
                (coefficients index)))
          atTop
          (𝓝 (∑' mode,
            programPT05SpinCMatterMaximalSpectralDensity period hPeriod
              massSquared state mode)) := by
  have hClosure : state ∈ closure
      (Set.range
        (programPPrimitiveSpinCMatterGraphFiniteLinearMap period hPeriod
          massSquared)) :=
    programPPrimitiveSpinCMatterGraphFiniteLinearMap_denseRange period hPeriod
      massSquared state
  obtain ⟨graphSequence, hGraphRange, hGraphTendsto⟩ :=
    (mem_closure_iff_seq_limit).1 hClosure
  choose coefficients hCoefficients using hGraphRange
  have hFiniteGraph : Tendsto
      (fun index =>
        programPPrimitiveSpinCMatterGraphFinite period hPeriod massSquared
          (coefficients index))
      atTop (𝓝 state) := by
    apply hGraphTendsto.congr'
    filter_upwards with index
    exact (hCoefficients index).symm
  refine ⟨coefficients, hFiniteGraph, ?_⟩
  have hActionTendsto : Tendsto
      (fun index =>
        programPPrimitiveSpinCMatterGraphAction period hPeriod massSquared
          (programPPrimitiveSpinCMatterGraphFinite period hPeriod massSquared
            (coefficients index)))
      atTop
      (𝓝 (programPPrimitiveSpinCMatterGraphAction period hPeriod massSquared
        state)) :=
    ((programPPrimitiveSpinCMatterGraphAction_contDiff period hPeriod
      massSquared).continuous.tendsto state).comp hFiniteGraph
  have hIntegralTendsto : Tendsto
      (fun index =>
        programPT05SpinCMatterSmoothLocalDensityIntegral period hPeriod
          massSquared
          (programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
            (coefficients index)))
      atTop
      (𝓝 (programPPrimitiveSpinCMatterGraphAction period hPeriod massSquared
        state)) := by
    apply hActionTendsto.congr'
    filter_upwards with index
    exact
      (programPT05SpinCMatterFiniteCoreLocalDensityIntegral_eq_graphAction
        period hPeriod massSquared (coefficients index)).symm
  rw [programPT05SpinCMatterMaximalSpectralDensity_tsum_eq_graphAction]
  exact hIntegralTendsto

/-- Spectral density carried by Gate 828's maximal SpinC frontier. -/
def programPT05BulkSpinCFrontierMaximalSpectralDensity
    (massSquared : Real)
    (frontier : ProgramPT05BulkSpinCLocalDensityFrontier period hPeriod
      massSquared) :
    ProgramPPrimitiveSpinCMatterMode → Real :=
  programPT05SpinCMatterMaximalSpectralDensity period hPeriod massSquared
    frontier.graphState

/-- The spectral density carried by a Gate-828 frontier is summable. -/
theorem programPT05BulkSpinCFrontierMaximalSpectralDensity_summable
    (massSquared : Real)
    (frontier : ProgramPT05BulkSpinCLocalDensityFrontier period hPeriod
      massSquared) :
    Summable
      (programPT05BulkSpinCFrontierMaximalSpectralDensity period hPeriod
        massSquared frontier) :=
  programPT05SpinCMatterMaximalSpectralDensity_summable period hPeriod
    massSquared frontier.graphState

/-- The Gate-828 SpinC frontier is exactly the sum of its summable maximal
spectral density. -/
theorem programPT05BulkSpinCFrontierMaximalSpectralDensity_tsum_eq_action
    (massSquared : Real)
    (frontier : ProgramPT05BulkSpinCLocalDensityFrontier period hPeriod
      massSquared) :
    (∑' mode,
      programPT05BulkSpinCFrontierMaximalSpectralDensity period hPeriod
        massSquared frontier mode) =
      programPPrimitiveSpinCMatterGraphAction period hPeriod massSquared
        frontier.graphState := by
  exact programPT05SpinCMatterMaximalSpectralDensity_tsum_eq_graphAction
    period hPeriod massSquared frontier.graphState

/-- Coupling-indexed form of the same identity for Gate 828's frontier
action wrapper. -/
theorem programPT05BulkSpinCFrontierMaximalSpectralDensity_tsum_eq_frontierAction
    (couplings : GlobalCandidateAActionCouplings)
    (frontier : ProgramPT05BulkSpinCLocalDensityFrontier period hPeriod
      couplings.matterMassSquared) :
    (∑' mode,
      programPT05BulkSpinCFrontierMaximalSpectralDensity period hPeriod
        couplings.matterMassSquared frontier mode) =
      programPT05BulkSpinCFrontierAction period hPeriod couplings frontier := by
  exact programPT05BulkSpinCFrontierMaximalSpectralDensity_tsum_eq_action
    period hPeriod couplings.matterMassSquared frontier

end
end P0EFTJanusProgramPT05SpinCMatterMaximalSpectralDensity4D
end JanusFormal
