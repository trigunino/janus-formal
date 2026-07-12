import Mathlib
import JanusFormal.Branches.FundamentalGeometryD10DerivedModuliPotential.Gates.P0EFTJanusBulkReducedPotential
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusUniversalActionProperty

namespace JanusFormal
namespace P0EFTJanusBulkUniversalHelmholtzSynthesis

set_option autoImplicit false

open P0EFTJanusBulkReducedPotential
open P0EFTJanusUniversalActionProperty

/-- Action specification induced by a positive bulk Schur complement. -/
noncomputable def bulkReducedSpecification
    (bulk : QuadraticBulkBoundaryData)
    (hPositive : 0 < reducedBoundaryHessian bulk) :
    ActionSpecification :=
  { hessian := reducedBoundaryHessian bulk
    criticalPoint := 0
    referenceValue := 0
    hessianNonzero := ne_of_gt hPositive }

/-- The universal quadratic action selected by the bulk-reduced specification. -/
noncomputable def bulkCanonicalAction
    (bulk : QuadraticBulkBoundaryData)
    (hPositive : 0 < reducedBoundaryHessian bulk) : QuadraticAction :=
  canonicalAction (bulkReducedSpecification bulk hPositive)

/-- The on-shell bulk action equals the canonical P-A representative. -/
theorem reduced_boundary_action_is_bulk_canonical_action
    (bulk : QuadraticBulkBoundaryData)
    (hPositive : 0 < reducedBoundaryHessian bulk)
    (boundary : ℝ) :
    reducedBoundaryAction bulk boundary =
      actionValue (bulkCanonicalAction bulk hPositive) boundary := by
  rw [reduced_boundary_action_formula]
  unfold actionValue bulkCanonicalAction canonicalAction
    bulkReducedSpecification
  ring

/-- The reduced bulk action realizes the relative universal specification. -/
theorem bulk_canonical_action_realizes_specification
    (bulk : QuadraticBulkBoundaryData)
    (hPositive : 0 < reducedBoundaryHessian bulk) :
    RealizesSpecification
      (bulkReducedSpecification bulk hPositive)
      (bulkCanonicalAction bulk hPositive) := by
  exact canonical_action_realizes_specification
    (bulkReducedSpecification bulk hPositive)

/-- Any other quadratic throat action with the same reduced Hessian, vacuum and normalization is identical. -/
theorem bulk_reduced_action_unique_relative_to_parent
    (bulk : QuadraticBulkBoundaryData)
    (hPositive : 0 < reducedBoundaryHessian bulk)
    (candidate : QuadraticAction)
    (hCandidate :
      RealizesSpecification
        (bulkReducedSpecification bulk hPositive) candidate) :
    candidate = bulkCanonicalAction bulk hPositive :=
  realization_action_unique
    (bulkReducedSpecification bulk hPositive)
    candidate hCandidate

/-- Changing the parent bulk coupling changes the selected boundary Hessian. -/
theorem different_parent_bulk_data_can_select_different_actions :
    ∃ first second : QuadraticBulkBoundaryData,
      reducedBoundaryHessian first ≠
        reducedBoundaryHessian second := by
  refine ⟨
    { bulkCoefficient := 1
      coupling := 0
      boundaryCoefficient := 2
      bulkCoefficientNonzero := by norm_num },
    { bulkCoefficient := 1
      coupling := 1
      boundaryCoefficient := 2
      bulkCoefficientNonzero := by norm_num },
    ?_⟩
  norm_num [reducedBoundaryHessian]

/-- Overall parent-action normalization rescales the selected throat Hessian. -/
theorem parent_normalization_rescales_boundary_hessian
    (scale : ℝ)
    (bulk : QuadraticBulkBoundaryData)
    (hScale : scale ≠ 0) :
    reducedBoundaryHessian
        (rescaleQuadraticData scale bulk hScale) =
      scale * reducedBoundaryHessian bulk :=
  reduced_hessian_rescaling scale bulk hScale

/--
Strongest current P-A/P-C synthesis: a well-posed parent bulk variational
problem supplies an integrable, self-adjoint boundary Hessian and a relative
universal action. It is canonical relative to the parent action and boundary
conditions, not from the throat moduli alone.
-/
structure BulkUniversalPhysicalStatus where
  parentBulkActionDerived : Prop
  boundaryAndJunctionTermsDerived : Prop
  wellPosedBulkBoundaryProblemProved : Prop
  uniqueBulkSolutionForBoundaryDataProved : Prop
  onShellBoundaryActionConstructed : Prop
  dirichletToNeumannHessianDerived : Prop
  hessianSelfAdjointAndElliptic : Prop
  paUniversalSpecificationDerived : Prop
  pcHelmholtzIntegrabilityProved : Prop
  boundaryActionUniqueRelativeToParent : Prop
  parentNormalizationDerived : Prop
  localFiniteCountertermsFixed : Prop
  noObservedScaleImported : Prop


def bulkUniversalPhysicalClosure
    (s : BulkUniversalPhysicalStatus) : Prop :=
  s.parentBulkActionDerived /\
  s.boundaryAndJunctionTermsDerived /\
  s.wellPosedBulkBoundaryProblemProved /\
  s.uniqueBulkSolutionForBoundaryDataProved /\
  s.onShellBoundaryActionConstructed /\
  s.dirichletToNeumannHessianDerived /\
  s.hessianSelfAdjointAndElliptic /\
  s.paUniversalSpecificationDerived /\
  s.pcHelmholtzIntegrabilityProved /\
  s.boundaryActionUniqueRelativeToParent /\
  s.parentNormalizationDerived /\
  s.localFiniteCountertermsFixed /\
  s.noObservedScaleImported

end P0EFTJanusBulkUniversalHelmholtzSynthesis
end JanusFormal
