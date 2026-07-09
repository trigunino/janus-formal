import JanusFormal.Branches.P0EarlyProgram.Gates.P0ClosureAxiomatics

namespace JanusFormal
namespace P0MatterMeasureObligations

open P0ClosureAxiomatics

set_option autoImplicit false

structure MatterMeasureProblem (Measure : Type) where
  sourceMeasure : Measure -> Prop
  actionVariationSelects : Measure -> Prop
  transportedContinuity : Measure -> Prop
  lapseSliceCompatible : Measure -> Prop

def measureClosed {Measure : Type} (p : MatterMeasureProblem Measure) (m : Measure) : Prop :=
  p.sourceMeasure m /\
  p.actionVariationSelects m /\
  p.transportedContinuity m /\
  p.lapseSliceCompatible m

def measureUnique {Measure : Type} (p : MatterMeasureProblem Measure) : Prop :=
  ExistsUnique (measureClosed p)

structure MatterMeasureCertificate {Measure : Type} (p : MatterMeasureProblem Measure) where
  candidate : Measure
  candidateClosed : measureClosed p candidate
  allClosedEqualCandidate : forall m, measureClosed p m -> m = candidate

theorem certificate_implies_unique_measure
    {Measure : Type}
    (p : MatterMeasureProblem Measure)
    (c : MatterMeasureCertificate p) :
    measureUnique p := by
  exact ⟨c.candidate, c.candidateClosed, c.allClosedEqualCandidate⟩

theorem closed_measure_provides_b4vol_axiom
    {Measure : Type}
    (p : MatterMeasureProblem Measure)
    (m : Measure)
    (h : measureClosed p m) :
    p.sourceMeasure m /\ p.actionVariationSelects m /\ p.transportedContinuity m := by
  exact ⟨h.left, h.right.left, h.right.right.left⟩

theorem continuity_without_action_selection_not_closed
    {Measure : Type}
    (p : MatterMeasureProblem Measure)
    (m : Measure)
    (_hContinuity : p.transportedContinuity m)
    (hNoSelection : Not (p.actionVariationSelects m)) :
    Not (measureClosed p m) := by
  intro hClosed
  exact hNoSelection hClosed.right.left

theorem missing_unique_measure_blocks_measure_route
    {Measure : Type}
    (p : MatterMeasureProblem Measure)
    (hMissing : Not (measureUnique p)) :
    Not (Nonempty (MatterMeasureCertificate p)) := by
  intro hCert
  rcases hCert with ⟨c⟩
  exact hMissing (certificate_implies_unique_measure p c)

def dynamicAxiomsWithMeasure
    {Measure : Type}
    (a : DynamicActionAxioms)
    (p : MatterMeasureProblem Measure)
    (m : Measure) :
    DynamicActionAxioms :=
  { a with b4volSelectedBySourceMeasure := measureClosed p m }

theorem closed_measure_fills_b4vol_dynamic_axiom
    {Measure : Type}
    (a : DynamicActionAxioms)
    (p : MatterMeasureProblem Measure)
    (m : Measure)
    (hClosed : measureClosed p m) :
    (dynamicAxiomsWithMeasure a p m).b4volSelectedBySourceMeasure := by
  exact hClosed

theorem missing_measure_selection_blocks_prediction
    {Measure : Type}
    (a : DynamicActionAxioms)
    (p : MatterMeasureProblem Measure)
    (m : Measure)
    (hMissing : Not (measureClosed p m)) :
    Not (closureTargetFromAxioms (dynamicAxiomsWithMeasure a p m)).predictionReady := by
  apply prediction_blocked_by_missing_dynamic_axiom
    (m := DynamicAxiomName.b4volMeasure)
  exact hMissing

end P0MatterMeasureObligations
end JanusFormal
