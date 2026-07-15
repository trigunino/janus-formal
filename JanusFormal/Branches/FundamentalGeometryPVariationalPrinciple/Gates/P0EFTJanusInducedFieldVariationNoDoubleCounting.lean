import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Prod
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFrechetPullbackSecondVariation

namespace JanusFormal
namespace P0EFTJanusInducedFieldVariationNoDoubleCounting

set_option autoImplicit false

noncomputable section

variable {Bulk Induced : Type*}
variable [NormedAddCommGroup Bulk] [NormedSpace ℝ Bulk]
variable [NormedAddCommGroup Induced] [NormedSpace ℝ Induced]

/-- The graph used when the second field is induced by the bulk field. -/
def inducedGraph (induced : Bulk → Induced) : Bulk → Bulk × Induced :=
  fun bulk => (bulk, induced bulk)

/-- Actual tangent map of the induced-field graph. -/
def inducedGraphDerivative (dInduced : Bulk →L[ℝ] Induced) :
    Bulk →L[ℝ] Bulk × Induced :=
  (ContinuousLinearMap.id ℝ Bulk).prod dInduced

/-- Euler one-form obtained by varying only the independent bulk slot. -/
def bulkPartial (jointEuler : (Bulk × Induced) →L[ℝ] ℝ) :
    Bulk →L[ℝ] ℝ :=
  jointEuler.comp (ContinuousLinearMap.inl ℝ Bulk Induced)

/-- Euler one-form obtained by varying the second slot independently. -/
def inducedPartial (jointEuler : (Bulk × Induced) →L[ℝ] ℝ) :
    Induced →L[ℝ] ℝ :=
  jointEuler.comp (ContinuousLinearMap.inr ℝ Bulk Induced)

/-- Correct Euler one-form after imposing that the second field is induced. -/
def constrainedEuler
    (jointEuler : (Bulk × Induced) →L[ℝ] ℝ)
    (dInduced : Bulk →L[ℝ] Induced) : Bulk →L[ℝ] ℝ :=
  bulkPartial jointEuler + (inducedPartial jointEuler).comp dInduced

/-- The graph chain rule is exactly the bulk Euler term plus the pullback of
the induced-slot Euler term. -/
theorem jointEuler_comp_inducedGraphDerivative
    (jointEuler : (Bulk × Induced) →L[ℝ] ℝ)
    (dInduced : Bulk →L[ℝ] Induced) :
    jointEuler.comp (inducedGraphDerivative dInduced) =
      constrainedEuler jointEuler dInduced := by
  ext variation
  change jointEuler (variation, dInduced variation) =
    jointEuler (variation, 0) + jointEuler (0, dInduced variation)
  simpa using jointEuler.map_add (variation, 0) (0, dInduced variation)

/-- Genuine Fréchet derivative of an action restricted to an induced-field
graph.  The second-slot Euler term is pulled back; it is not an additional
independent field equation. -/
theorem inducedAction_hasFDerivAt
    (jointAction : Bulk × Induced → ℝ)
    (induced : Bulk → Induced)
    (bulk : Bulk)
    (jointEuler : (Bulk × Induced) →L[ℝ] ℝ)
    (dInduced : Bulk →L[ℝ] Induced)
    (hAction : HasFDerivAt jointAction jointEuler (bulk, induced bulk))
    (hInduced : HasFDerivAt induced dInduced bulk) :
    HasFDerivAt (fun variedBulk =>
        jointAction (inducedGraph induced variedBulk))
      (constrainedEuler jointEuler dInduced) bulk := by
  have hGraph :
      HasFDerivAt (inducedGraph induced)
        (inducedGraphDerivative dInduced) bulk := by
    exact (hasFDerivAt_id bulk).prodMk hInduced
  have hChain := hAction.comp bulk hGraph
  rw [jointEuler_comp_inducedGraphDerivative] at hChain
  change HasFDerivAt (jointAction ∘ inducedGraph induced)
    (constrainedEuler jointEuler dInduced) bulk
  exact hChain

/-- Treating both slots as independent imposes two equations. -/
def IndependentlyStationary
    (jointEuler : (Bulk × Induced) →L[ℝ] ℝ) : Prop :=
  bulkPartial jointEuler = 0 ∧ inducedPartial jointEuler = 0

/-- On the induced graph there is only the pulled-back combined equation. -/
def ConstrainedStationary
    (jointEuler : (Bulk × Induced) →L[ℝ] ℝ)
    (dInduced : Bulk →L[ℝ] Induced) : Prop :=
  constrainedEuler jointEuler dInduced = 0

/-- Independent stationarity is sufficient for constrained stationarity. -/
theorem independentlyStationary_implies_constrainedStationary
    (jointEuler : (Bulk × Induced) →L[ℝ] ℝ)
    (dInduced : Bulk →L[ℝ] Induced)
    (hIndependent : IndependentlyStationary jointEuler) :
    ConstrainedStationary jointEuler dInduced := by
  rcases hIndependent with ⟨hBulk, hInduced⟩
  simp [ConstrainedStationary, constrainedEuler, hBulk, hInduced]

/-- If the induced-slot Euler term is separately known to vanish, the correct
constrained equation recovers the independent bulk equation. -/
theorem constrainedStationary_and_inducedPartial_zero
    (jointEuler : (Bulk × Induced) →L[ℝ] ℝ)
    (dInduced : Bulk →L[ℝ] Induced)
    (hConstrained : ConstrainedStationary jointEuler dInduced)
    (hInduced : inducedPartial jointEuler = 0) :
    bulkPartial jointEuler = 0 := by
  simpa [ConstrainedStationary, constrainedEuler, hInduced] using hConstrained

section Counterexample

/-- A joint action whose two independent Euler equations are nonzero. -/
def cancellationAction : ℝ × ℝ → ℝ :=
  fun fields => fields.1 - fields.2

/-- Its constant joint Euler one-form. -/
def cancellationEuler : (ℝ × ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.fst ℝ ℝ ℝ -
    ContinuousLinearMap.snd ℝ ℝ ℝ

theorem cancellationAction_hasFDerivAt (fields : ℝ × ℝ) :
    HasFDerivAt cancellationAction cancellationEuler fields := by
  change HasFDerivAt (fun pair : ℝ × ℝ => cancellationEuler pair)
    cancellationEuler fields
  exact cancellationEuler.hasFDerivAt

/-- The diagonal identification makes the restricted action identically zero. -/
@[simp]
theorem cancellationAction_on_diagonal (x : ℝ) :
    cancellationAction (x, x) = 0 := by
  simp [cancellationAction]

/-- The correct constrained Euler equation vanishes by cancellation. -/
theorem cancellation_constrainedStationary :
    ConstrainedStationary cancellationEuler
      (ContinuousLinearMap.id ℝ ℝ) := by
  simp [ConstrainedStationary, constrainedEuler, bulkPartial,
    inducedPartial, cancellationEuler]

/-- The diagonal restriction has the zero continuous linear map as its actual
Fréchet derivative. -/
theorem cancellationRestrictedAction_hasFDerivAt (x : ℝ) :
    HasFDerivAt (fun varied : ℝ => cancellationAction (varied, varied))
      (0 : ℝ →L[ℝ] ℝ) x := by
  have hChain := inducedAction_hasFDerivAt cancellationAction
    (fun varied : ℝ => varied) x cancellationEuler
    (ContinuousLinearMap.id ℝ ℝ)
    (cancellationAction_hasFDerivAt (x, x)) (hasFDerivAt_id x)
  have hZero : constrainedEuler cancellationEuler
      (ContinuousLinearMap.id ℝ ℝ) = 0 :=
    cancellation_constrainedStationary
  rw [hZero] at hChain
  simpa [inducedGraph] using hChain

@[simp]
theorem cancellationRestrictedAction_fderiv (x : ℝ) :
    fderiv ℝ (fun varied : ℝ => cancellationAction (varied, varied)) x = 0 :=
  (cancellationRestrictedAction_hasFDerivAt x).fderiv

/-- The independent bulk-slot equation is genuinely nonzero. -/
theorem cancellation_bulkPartial_ne_zero :
    bulkPartial cancellationEuler ≠ 0 := by
  intro hBulk
  have hAtOne := congrArg
    (fun functional : ℝ →L[ℝ] ℝ => functional 1) hBulk
  norm_num [bulkPartial, cancellationEuler] at hAtOne

/-- The independent induced-slot equation is genuinely nonzero as well. -/
theorem cancellation_inducedPartial_ne_zero :
    inducedPartial cancellationEuler ≠ 0 := by
  intro hInduced
  have hAtOne := congrArg
    (fun functional : ℝ →L[ℝ] ℝ => functional 1) hInduced
  norm_num [inducedPartial, cancellationEuler] at hAtOne

/-- Thus promoting the induced field to an independent variable would add
two nonzero equations not implied by the constrained variational problem. -/
theorem cancellation_not_independentlyStationary :
    ¬ IndependentlyStationary cancellationEuler := by
  intro hIndependent
  exact cancellation_bulkPartial_ne_zero hIndependent.1

/-- Exact no-double-counting witness: constrained stationarity holds while the
joint action is not independently stationary.  The preceding theorem computes
the zero actual derivative of the restricted action. -/
theorem constrained_stationarity_does_not_imply_independent :
    ConstrainedStationary cancellationEuler
        (ContinuousLinearMap.id ℝ ℝ) ∧
      ¬ IndependentlyStationary cancellationEuler :=
  ⟨cancellation_constrainedStationary,
    cancellation_not_independentlyStationary⟩

end Counterexample

end

end P0EFTJanusInducedFieldVariationNoDoubleCounting
end JanusFormal
