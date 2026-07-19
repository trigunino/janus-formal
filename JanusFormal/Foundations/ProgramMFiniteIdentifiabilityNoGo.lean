import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# MF-ID-001: one finite observation cannot identify its generator universally

This is an information-theoretic no-go.  It does not depend on a particular
geometric diagnostic.
-/

namespace JanusFormal.ProgramM

universe u v

/-- A named generative law for one finite observation type. -/
structure FiniteObservationLaw (Outcome : Type u) where
  identifier : String
  identifier_nonempty : identifier ≠ ""
  distribution : PMF Outcome

def FiniteObservationLaw.compatible
    {Outcome : Type u} (law : FiniteObservationLaw Outcome) (x : Outcome) : Prop :=
  0 < law.distribution x

/-- If two distinct models can both produce the observation, a deterministic
inference from that observation is wrong for at least one model. -/
theorem singleObservation_not_universally_identifying
    {Model : Type u} {Outcome : Type v}
    (first second : Model) (hmodels : first ≠ second)
    (infer : Outcome → Model) (observed : Outcome) :
    infer observed ≠ first ∨ infer observed ≠ second := by
  by_cases hfirst : infer observed = first
  · right
    intro hsecond
    exact hmodels (hfirst.symm.trans hsecond)
  · exact Or.inl hfirst

/-- Compatibility assumptions make the no-go operational: both named laws
assign positive mass to the same observed finite object. -/
theorem overlappingLaws_not_identifiedByOneObservation
    {Model : Type u} {Outcome : Type v}
    (law : Model → FiniteObservationLaw Outcome)
    (first second : Model) (hmodels : first ≠ second)
    (observed : Outcome)
    (_ : (law first).compatible observed)
    (_ : (law second).compatible observed)
    (infer : Outcome → Model) :
    infer observed ≠ first ∨ infer observed ≠ second :=
  singleObservation_not_universally_identifying first second hmodels infer observed

/-- Even identical observational laws may carry different model labels. -/
theorem equalLaws_overlap_on_support
    {Model : Type u} {Outcome : Type v}
    (law : Model → FiniteObservationLaw Outcome)
    (first second : Model)
    (hlaw : (law first).distribution = (law second).distribution)
    (observed : Outcome) (hpositive : 0 < (law first).distribution observed) :
    (law first).compatible observed ∧ (law second).compatible observed := by
  constructor
  · exact hpositive
  · simpa [FiniteObservationLaw.compatible, ← hlaw] using hpositive

end JanusFormal.ProgramM
