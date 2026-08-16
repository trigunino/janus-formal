import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryHistoricalTerminalActionClosure4D

/-!
# Fréchet calculus for the Candidate-A normal-boundary action germ

The geometric H10 comparison is an equality of the completed Candidate-A GHY
action with the historical mobile Gauss action on a genuine open neighbourhood
of the zero variation.  Once that action-level equality is available, equality
of the first and second Fréchet derivatives is not an additional analytic or
physical datum.

This module proves the reusable local calculus.  It deliberately works with an
arbitrary normed variation space and arbitrary real actions, so no second
boundary geometry, frame, normal, measure or action is introduced.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateANormalBoundaryActionGermCalculus4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open Filter Set Topology
open scoped Topology

universe u

variable {Variation : Type u}
  [NormedAddCommGroup Variation]
  [NormedSpace Real Variation]

/-- Two real actions represent the same local action germ at `base` when they
agree on an open neighbourhood containing `base`. -/
structure SameRealActionGermAt
    (completed historical : Variation → Real)
    (base : Variation) : Prop where
  domain : Set Variation
  isOpen_domain : IsOpen domain
  base_mem_domain : base ∈ domain
  eqOn_domain : Set.EqOn completed historical domain

/-- Equality on an open set gives equality of the Fréchet derivatives at every
point of that set.  No differentiability hypothesis is needed: `fderiv` is a
total operation and is local. -/
theorem fderiv_eqOn_of_eqOn_open
    {completed historical : Variation → Real}
    {domain : Set Variation}
    (hOpen : IsOpen domain)
    (hEq : Set.EqOn completed historical domain) :
    Set.EqOn
      (fun point => fderiv Real completed point)
      (fun point => fderiv Real historical point)
      domain := by
  intro point hPoint
  have hEventually : completed =ᶠ[𝓝 point] historical := by
    filter_upwards [hOpen.mem_nhds hPoint] with nearby hNearby
    exact hEq hNearby
  exact hEventually.fderiv_eq

/-- Equality on an open set also gives equality of the genuine second Fréchet
derivatives at every point of that set. -/
theorem second_fderiv_eqOn_of_eqOn_open
    {completed historical : Variation → Real}
    {domain : Set Variation}
    (hOpen : IsOpen domain)
    (hEq : Set.EqOn completed historical domain) :
    Set.EqOn
      (fun point =>
        fderiv Real (fun state => fderiv Real completed state) point)
      (fun point =>
        fderiv Real (fun state => fderiv Real historical state) point)
      domain := by
  have hFirst := fderiv_eqOn_of_eqOn_open hOpen hEq
  intro point hPoint
  have hEventually :
      (fun state => fderiv Real completed state) =ᶠ[𝓝 point]
        (fun state => fderiv Real historical state) := by
    filter_upwards [hOpen.mem_nhds hPoint] with nearby hNearby
    exact hFirst hNearby
  exact hEventually.fderiv_eq

/-- First Fréchet derivatives agree at the anchor of a same-action germ. -/
theorem SameRealActionGermAt.fderiv_eq
    {completed historical : Variation → Real}
    {base : Variation}
    (germ : SameRealActionGermAt completed historical base) :
    fderiv Real completed base = fderiv Real historical base :=
  fderiv_eqOn_of_eqOn_open germ.isOpen_domain germ.eqOn_domain
    germ.base_mem_domain

/-- Second Fréchet derivatives agree at the anchor of a same-action germ.  This
is the generic calculus step needed by H10. -/
theorem SameRealActionGermAt.second_fderiv_eq
    {completed historical : Variation → Real}
    {base : Variation}
    (germ : SameRealActionGermAt completed historical base) :
    fderiv Real (fun state => fderiv Real completed state) base =
      fderiv Real (fun state => fderiv Real historical state) base :=
  second_fderiv_eqOn_of_eqOn_open germ.isOpen_domain germ.eqOn_domain
    germ.base_mem_domain

/-- If the completed action is `C²` at the germ anchor, then so is the
historical representative.  The proof uses only locality of `ContDiffAt`. -/
theorem SameRealActionGermAt.historical_contDiffAt_two
    {completed historical : Variation → Real}
    {base : Variation}
    (germ : SameRealActionGermAt completed historical base)
    (hCompleted : ContDiffAt Real 2 completed base) :
    ContDiffAt Real 2 historical base := by
  have hEventually : completed =ᶠ[𝓝 base] historical := by
    filter_upwards [germ.isOpen_domain.mem_nhds germ.base_mem_domain] with
      nearby hNearby
    exact germ.eqOn_domain hNearby
  exact hCompleted.congr_of_eventuallyEq hEventually.symm

/-- Symmetry of the completed second Fréchet derivative transfers to the
historical representative through the same action germ. -/
theorem SameRealActionGermAt.historical_second_fderiv_symmetric
    {completed historical : Variation → Real}
    {base : Variation}
    (germ : SameRealActionGermAt completed historical base)
    (hSymmetric : ∀ first second : Variation,
      fderiv Real (fun state => fderiv Real completed state) base first second =
        fderiv Real (fun state => fderiv Real completed state) base second first) :
    ∀ first second : Variation,
      fderiv Real (fun state => fderiv Real historical state) base first second =
        fderiv Real (fun state => fderiv Real historical state) base second first := by
  intro first second
  rw [← germ.second_fderiv_eq]
  exact hSymmetric first second

/-- Public gate: action-level germ equality supplies all derivative-level
identifications required by the terminal normal-boundary Hessian closure. -/
theorem candidate_a_normal_boundary_same_action_germ_calculus_gate
    {completed historical : Variation → Real}
    {base : Variation}
    (germ : SameRealActionGermAt completed historical base) :
    fderiv Real completed base = fderiv Real historical base ∧
      fderiv Real (fun state => fderiv Real completed state) base =
        fderiv Real (fun state => fderiv Real historical state) base :=
  ⟨germ.fderiv_eq, germ.second_fderiv_eq⟩

end
end P0EFTJanusProgramPGlobalCandidateANormalBoundaryActionGermCalculus4D
end JanusFormal
