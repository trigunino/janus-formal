import JanusFormal.Legacy.P0.Gates.P0OrbifoldActionProgram

namespace JanusFormal
namespace P0OrbifoldBoundaryNoether

open P0OrbifoldActionProgram

set_option autoImplicit false

structure OrbifoldBoundaryNoetherContext (Action : Type) where
  actionProblem : OrbifoldActionProblem Action
  action : Action
  topology : OrbifoldTopologicalInvariants

def globalNoetherObligation
    {Action : Type}
    (c : OrbifoldBoundaryNoetherContext Action) : Prop :=
  c.actionProblem.diffInvariant c.action

def splitNoetherObligation
    {Action : Type}
    (c : OrbifoldBoundaryNoetherContext Action) : Prop :=
  noetherSplitClosed c.actionProblem c.action c.topology

theorem diff_invariance_gives_global_noether
    {Action : Type}
    (c : OrbifoldBoundaryNoetherContext Action) :
    c.actionProblem.diffInvariant c.action ->
    globalNoetherObligation c := by
  intro hDiff
  exact hDiff

theorem topology_with_boundary_leak_supports_split_noether
    {Action : Type}
    (c : OrbifoldBoundaryNoetherContext Action) :
    globalNoetherObligation c ->
    topologyConservationReady c.topology ->
    splitNoetherObligation c := by
  intro hGlobal hTopology
  exact And.intro hGlobal hTopology

theorem split_obligation_forbids_ignoring_diff :
    Not (forall {Action : Type}
      (p : OrbifoldActionProblem Action)
      (s : Action)
      (t : OrbifoldTopologicalInvariants),
      topologyConservationReady t ->
      p.diffInvariant s) := by
  intro h
  let pBad : OrbifoldActionProblem Unit :=
    { lagrangian4D := fun _ => True
      diffInvariant := fun _ => False
      ptCompatible := fun _ => True
      boundaryVariationWellPosed := fun _ => True
      matterVariationWellPosed := fun _ => True
      solderVariationWellPosed := fun _ => True }
  let t : OrbifoldTopologicalInvariants :=
    { defectClassFixed := True
      boundaryLeakForbidden := True
      sectorChargeConserved := True
      ptFixedSetCompatible := True }
  have hNoether : pBad.diffInvariant () := h pBad () t (by
    exact ⟨True.intro, True.intro, True.intro, True.intro⟩)
  exact hNoether

end P0OrbifoldBoundaryNoether
end JanusFormal
