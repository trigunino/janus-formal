import JanusFormal.Legacy.P0.Gates.P0ClosureAxiomatics

namespace JanusFormal
namespace P0OrbifoldActionProgram

open P0ClosureAxiomatics

set_option autoImplicit false

structure PTInvolution (M : Type) where
  pt : M -> M
  pt_twice : forall x, pt (pt x) = x

theorem pt_has_preimage
    {M : Type}
    (i : PTInvolution M) :
    forall y, exists x, i.pt x = y := by
  intro y
  exact Exists.intro (i.pt y) (i.pt_twice y)

structure OrbifoldActionProblem (Action : Type) where
  lagrangian4D : Action -> Prop
  diffInvariant : Action -> Prop
  ptCompatible : Action -> Prop
  boundaryVariationWellPosed : Action -> Prop
  matterVariationWellPosed : Action -> Prop
  solderVariationWellPosed : Action -> Prop

def acceptedOrbifoldAction
    {Action : Type}
    (p : OrbifoldActionProblem Action)
    (s : Action) : Prop :=
  p.lagrangian4D s /\
  p.diffInvariant s /\
  p.ptCompatible s /\
  p.boundaryVariationWellPosed s /\
  p.matterVariationWellPosed s /\
  p.solderVariationWellPosed s

def uniqueOrbifoldAction
    {Action : Type}
    (p : OrbifoldActionProblem Action) : Prop :=
  ExistsUnique (acceptedOrbifoldAction p)

structure UniqueOrbifoldActionCertificate
    {Action : Type}
    (p : OrbifoldActionProblem Action) where
  candidate : Action
  candidateAccepted : acceptedOrbifoldAction p candidate
  allAcceptedEqualCandidate :
    forall s, acceptedOrbifoldAction p s -> s = candidate

theorem certificate_implies_unique_orbifold_action
    {Action : Type}
    (p : OrbifoldActionProblem Action)
    (c : UniqueOrbifoldActionCertificate p) :
    uniqueOrbifoldAction p := by
  refine Exists.intro c.candidate ?_
  exact And.intro c.candidateAccepted c.allAcceptedEqualCandidate

theorem accepted_action_has_variation_equations
    {Action : Type}
    {p : OrbifoldActionProblem Action}
    {s : Action}
    (h : acceptedOrbifoldAction p s) :
    p.boundaryVariationWellPosed s /\
    p.matterVariationWellPosed s /\
    p.solderVariationWellPosed s := by
  exact And.intro h.right.right.right.left
    (And.intro h.right.right.right.right.left h.right.right.right.right.right)

structure TwoMetricBreaking (Metric : Type) where
  plusMetric : Metric
  minusMetric : Metric
  branchesDistinct : Not (plusMetric = minusMetric)
  ptRelated : Prop
  inverseMassTimeOrientation : Prop
  generatedByActionVariation : Prop

def metricBreakingClosed {Metric : Type} (b : TwoMetricBreaking Metric) : Prop :=
  b.ptRelated /\ b.inverseMassTimeOrientation /\ b.generatedByActionVariation

structure OrbifoldTopologicalInvariants where
  defectClassFixed : Prop
  boundaryLeakForbidden : Prop
  sectorChargeConserved : Prop
  ptFixedSetCompatible : Prop

def topologyConservationReady (t : OrbifoldTopologicalInvariants) : Prop :=
  t.defectClassFixed /\
  t.boundaryLeakForbidden /\
  t.sectorChargeConserved /\
  t.ptFixedSetCompatible

def noetherSplitClosed
    {Action : Type}
    (p : OrbifoldActionProblem Action)
    (s : Action)
    (t : OrbifoldTopologicalInvariants) : Prop :=
  p.diffInvariant s /\ topologyConservationReady t

structure TopologyVsDiff where
  topologicalInvariant : Prop
  diffInvariant : Prop

theorem topology_alone_does_not_imply_diff_invariance :
    Not (forall x : TopologyVsDiff, x.topologicalInvariant -> x.diffInvariant) := by
  intro h
  let bad : TopologyVsDiff := { topologicalInvariant := True, diffInvariant := False }
  exact h bad trivial

structure OrbifoldProgramData
    (Action Metric Bridge Measure : Type) where
  actionProblem : OrbifoldActionProblem Action
  action : Action
  metricBreaking : TwoMetricBreaking Metric
  topology : OrbifoldTopologicalInvariants
  bridgeSelectedByOrbifoldVariation : Prop
  sameBridgeForKAndQcross : Prop
  b4volSelectedBySourceMeasure : Prop
  pressureAndPiTransportClosed : Prop
  noScalarAbsorption : Prop

def actionVariationBlockClosed
    {Action Metric Bridge Measure : Type}
    (d : OrbifoldProgramData Action Metric Bridge Measure) : Prop :=
  d.actionProblem.boundaryVariationWellPosed d.action /\
  d.actionProblem.matterVariationWellPosed d.action /\
  d.actionProblem.solderVariationWellPosed d.action /\
  metricBreakingClosed d.metricBreaking

def dynamicAxiomsFromOrbifoldProgram
    {Action Metric Bridge Measure : Type}
    (d : OrbifoldProgramData Action Metric Bridge Measure) :
    DynamicActionAxioms :=
  { sourceActionExists :=
      acceptedOrbifoldAction d.actionProblem d.action /\
      uniqueOrbifoldAction d.actionProblem
    actionVariationEquationsWritten := actionVariationBlockClosed d
    bridgeSelectedByEulerLagrange := d.bridgeSelectedByOrbifoldVariation
    sameBridgeForKAndQcross := d.sameBridgeForKAndQcross
    b4volSelectedBySourceMeasure := d.b4volSelectedBySourceMeasure
    pressureAndPiTransportClosed := d.pressureAndPiTransportClosed
    splitNoetherIdentitiesClosed :=
      noetherSplitClosed d.actionProblem d.action d.topology
    noScalarAbsorption := d.noScalarAbsorption }

structure OrbifoldProgramCertificate
    {Action Metric Bridge Measure : Type}
    (d : OrbifoldProgramData Action Metric Bridge Measure) where
  acceptedAction : acceptedOrbifoldAction d.actionProblem d.action
  uniqueAction : uniqueOrbifoldAction d.actionProblem
  metricBreaking : metricBreakingClosed d.metricBreaking
  topologyReady : topologyConservationReady d.topology
  bridgeSelected : d.bridgeSelectedByOrbifoldVariation
  sameBridge : d.sameBridgeForKAndQcross
  b4volSelected : d.b4volSelectedBySourceMeasure
  pressurePiClosed : d.pressureAndPiTransportClosed
  noScalarAbsorb : d.noScalarAbsorption

theorem certificate_gives_dynamic_axioms
    {Action Metric Bridge Measure : Type}
    (d : OrbifoldProgramData Action Metric Bridge Measure)
    (c : OrbifoldProgramCertificate d) :
    allDynamicAxiomsHold (dynamicAxiomsFromOrbifoldProgram d) := by
  constructor
  exact And.intro c.acceptedAction c.uniqueAction
  constructor
  exact And.intro (accepted_action_has_variation_equations c.acceptedAction).left
    (And.intro (accepted_action_has_variation_equations c.acceptedAction).right.left
      (And.intro (accepted_action_has_variation_equations c.acceptedAction).right.right
        c.metricBreaking))
  constructor
  exact c.bridgeSelected
  constructor
  exact c.sameBridge
  constructor
  exact c.b4volSelected
  constructor
  exact c.pressurePiClosed
  constructor
  exact And.intro c.acceptedAction.right.left c.topologyReady
  exact c.noScalarAbsorb

theorem orbifold_program_certificate_gives_conditional_prediction
    {Action Metric Bridge Measure : Type}
    (d : OrbifoldProgramData Action Metric Bridge Measure)
    (c : OrbifoldProgramCertificate d) :
    (closureTargetFromAxioms
      (dynamicAxiomsFromOrbifoldProgram d)).predictionReady := by
  exact conditional_closure_from_dynamic_action_axioms
    (dynamicAxiomsFromOrbifoldProgram d)
    (certificate_gives_dynamic_axioms d c)

theorem missing_unique_action_blocks_prediction
    {Action Metric Bridge Measure : Type}
    (d : OrbifoldProgramData Action Metric Bridge Measure)
    (hMissing : Not (uniqueOrbifoldAction d.actionProblem)) :
    Not (closureTargetFromAxioms
      (dynamicAxiomsFromOrbifoldProgram d)).predictionReady := by
  apply prediction_blocked_by_missing_dynamic_axiom
    (m := DynamicAxiomName.sourceAction)
  intro hSource
  exact hMissing hSource.right

theorem missing_metric_breaking_blocks_prediction
    {Action Metric Bridge Measure : Type}
    (d : OrbifoldProgramData Action Metric Bridge Measure)
    (hMissing : Not (metricBreakingClosed d.metricBreaking)) :
    Not (closureTargetFromAxioms
      (dynamicAxiomsFromOrbifoldProgram d)).predictionReady := by
  apply prediction_blocked_by_missing_dynamic_axiom
    (m := DynamicAxiomName.actionVariation)
  intro hVariation
  exact hMissing hVariation.right.right.right

theorem missing_topology_blocks_split_noether
    {Action Metric Bridge Measure : Type}
    (d : OrbifoldProgramData Action Metric Bridge Measure)
    (hMissing : Not (topologyConservationReady d.topology)) :
    Not (closureTargetFromAxioms
      (dynamicAxiomsFromOrbifoldProgram d)).predictionReady := by
  apply prediction_blocked_by_missing_dynamic_axiom
    (m := DynamicAxiomName.splitNoether)
  intro hNoether
  exact hMissing hNoether.right

end P0OrbifoldActionProgram
end JanusFormal
