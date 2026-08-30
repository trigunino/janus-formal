import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryGHYFactorGerm4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyPhysicalC2Reduction4D

/-!
# Transfer of the completed normal-boundary `C²` block to the Robin action

H10 constructs the completed two-sheet GHY action as a `C²` function on an open
variation domain.  The geometric comparison identifies it with the historical
mobile Candidate-A boundary action on that same domain.  Therefore the Robin
block used by the local Candidate-A family is automatically `C²`; asking for a
second regularity proof would duplicate the action.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateANormalBoundaryRobinC2Transfer4D

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

open P0EFTJanusProgramPGlobalCandidateANormalBoundaryActionGermCalculus4D

/-- Equality of two actions on an open set transfers `C²` regularity at each
point of that set. -/
theorem contDiffWithinAt_two_of_eqOn_open
    {completed historical : Variation → Real}
    {domain : Set Variation}
    {point : Variation}
    (hOpen : IsOpen domain)
    (hPoint : point ∈ domain)
    (hEq : Set.EqOn completed historical domain)
    (hCompleted : ContDiffWithinAt Real 2 completed domain point) :
    ContDiffWithinAt Real 2 historical domain point := by
  have hCompletedAt : ContDiffAt Real 2 completed point :=
    hCompleted.contDiffAt (hOpen.mem_nhds hPoint)
  have hEventually : completed =ᶠ[𝓝 point] historical := by
    filter_upwards [hOpen.mem_nhds hPoint] with nearby hNearby
    exact hEq hNearby
  exact (hCompletedAt.congr_of_eventuallyEq hEventually.symm).contDiffWithinAt

/-- A single open-domain equality transfers the full `C²` family. -/
theorem contDiffWithin_two_of_eqOn_open
    {completed historical : Variation → Real}
    {domain : Set Variation}
    (hOpen : IsOpen domain)
    (hEq : Set.EqOn completed historical domain)
    (hCompleted : ContDiffOn Real 2 completed domain) :
    ContDiffOn Real 2 historical domain := by
  intro point hPoint
  exact contDiffWithinAt_two_of_eqOn_open hOpen hPoint hEq
    (hCompleted point hPoint)

/-- Data produced by the completed H10 action together with its historical
same-action germ. -/
structure NormalBoundaryRobinC2TransferData
    (completed historical : Variation → Real) where
  domain : Set Variation
  isOpen_domain : IsOpen domain
  completed_contDiffWithin_two : ContDiffOn Real 2 completed domain
  sameAction : Set.EqOn completed historical domain

/-- The historical/mobile Robin action is `C²` on exactly the completed H10
domain. -/
theorem NormalBoundaryRobinC2TransferData.historical_contDiffWithin_two
    {completed historical : Variation → Real}
    (data : NormalBoundaryRobinC2TransferData completed historical) :
    ContDiffOn Real 2 historical data.domain :=
  contDiffWithin_two_of_eqOn_open data.isOpen_domain data.sameAction
    data.completed_contDiffWithin_two

/-- Pointwise `C²` form used directly by the seven-physical-block family. -/
theorem NormalBoundaryRobinC2TransferData.historical_contDiffWithinAt_two
    {completed historical : Variation → Real}
    (data : NormalBoundaryRobinC2TransferData completed historical)
    {point : Variation}
    (hPoint : point ∈ data.domain) :
    ContDiffWithinAt Real 2 historical data.domain point :=
  data.historical_contDiffWithin_two point hPoint

/-- The same packet also transports the second Fréchet derivative at every
chosen anchor. -/
theorem NormalBoundaryRobinC2TransferData.second_fderiv_eq
    {completed historical : Variation → Real}
    (data : NormalBoundaryRobinC2TransferData completed historical)
    {base : Variation}
    (hBase : base ∈ data.domain) :
    fderiv Real (fun state => fderiv Real completed state) base =
      fderiv Real (fun state => fderiv Real historical state) base := by
  let germ : SameRealActionGermAt completed historical base :=
    { domain := data.domain
      isOpen_domain := data.isOpen_domain
      base_mem_domain := hBase
      eqOn_domain := data.sameAction }
  exact germ.second_fderiv_eq

/-- Public bridge from H10 to the Robin slot of the Candidate-A local family. -/
theorem candidate_a_normal_boundary_robin_c2_transfer_gate
    {completed historical : Variation → Real}
    (data : NormalBoundaryRobinC2TransferData completed historical) :
    ContDiffOn Real 2 historical data.domain ∧
      ∀ base, base ∈ data.domain →
        fderiv Real (fun state => fderiv Real completed state) base =
          fderiv Real (fun state => fderiv Real historical state) base :=
  ⟨data.historical_contDiffWithin_two,
    fun _ hBase => data.second_fderiv_eq hBase⟩

end
end P0EFTJanusProgramPGlobalCandidateANormalBoundaryRobinC2Transfer4D
end JanusFormal
