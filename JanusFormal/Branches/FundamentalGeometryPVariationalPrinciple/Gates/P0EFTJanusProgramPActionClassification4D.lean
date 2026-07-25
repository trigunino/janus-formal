import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusConvexHelmholtzReconstruction
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNaturalOperatorClassification4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPTFlatBimetricCoefficientClassification4D

/-!
# Program-P action classification modulo variationally trivial terms

On a convex configuration domain, the complete Euler one-form determines an
action up to one additive constant.  If the Euler form satisfies the nonlinear
Helmholtz condition, the radial primitive supplies the normalized action.

This is the strongest unconditional uniqueness statement available from the
inverse problem.  Principal symbols, PT symmetry and Helmholtz symmetry alone
do not determine the Euler one-form because lower-order couplings remain free.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActionClassification4D

set_option autoImplicit false

noncomputable section

open Set
open P0EFTJanusConvexHelmholtzReconstruction

/-- Functional equivalence after quotienting the additive term invisible to
the first variation. -/
def DifferByConstantOn
    {Configuration : Type*}
    (domain : Set Configuration)
    (first second : Configuration → ℝ) : Prop :=
  ∃ constant : ℝ, ∀ x ∈ domain,
    first x = second x + constant

/-- Complete action classification for a fixed Euler one-form on a nonempty
convex domain. -/
theorem sameEuler_implies_sameActionClass
    {Configuration : Type*}
    [NormedAddCommGroup Configuration] [NormedSpace ℝ Configuration]
    {domain : Set Configuration}
    (hConvex : Convex ℝ domain)
    (hNonempty : domain.Nonempty)
    (euler : EulerOneForm Configuration)
    (first second : Configuration → ℝ)
    (hFirst : ∀ x ∈ domain, HasFDerivAt first (euler x) x)
    (hSecond : ∀ x ∈ domain, HasFDerivAt second (euler x) x) :
    DifferByConstantOn domain first second := by
  exact convex_actions_same_euler_differ_by_constant
    hConvex hNonempty hFirst hSecond

/-- Nonlinear Helmholtz reconstructs a normalized action on the whole
configuration space, and that normalized representative is unique. -/
theorem normalizedRadialAction_unique
    {Configuration : Type*}
    [NormedAddCommGroup Configuration] [NormedSpace ℝ Configuration]
    (euler : EulerOneForm Configuration)
    (hDifferentiable : Differentiable ℝ euler)
    (hHelmholtz : ∀ x, HelmholtzJacobianAt euler x)
    (base : Configuration)
    (action : Configuration → ℝ)
    (hAction : ∀ x, HasFDerivAt action (euler x) x)
    (hNormalized : action base = 0) :
    ∀ x, action x = radialAction base euler x := by
  have hRadial :
      ∀ x, HasFDerivAt (radialAction base euler) (euler x) x :=
    fun x => radial_action_hasFDerivAt
      euler hDifferentiable hHelmholtz base x
  have hBase :
      action base = radialAction base euler base := by
    rw [hNormalized, radial_action_at_base]
  have hEqOn :=
    convex_actions_same_euler_eqOn_of_eq_at_base
      (domain := (Set.univ : Set Configuration))
      convex_univ
      (fun x _ => hAction x)
      (fun x _ => hRadial x)
      (Set.mem_univ base) hBase
  intro x
  exact hEqOn (Set.mem_univ x)

/-- A normalized quadratic scalar action with one freely selectable natural
zero-order mass.  The leading kinetic normalization is fixed to one. -/
def scalarEFTAction (massSquared field : ℝ) : ℝ :=
  ((1 + massSquared) / 2) * field ^ 2

/-- Its complete Euler operator. -/
def scalarEFTEuler (massSquared field : ℝ) : ℝ :=
  ((1 + massSquared) / 2) * (2 * field)

/-- Every member is PT-even. -/
theorem scalarEFTAction_ptEven
    (massSquared field : ℝ) :
    scalarEFTAction massSquared (-field) =
      scalarEFTAction massSquared field := by
  unfold scalarEFTAction
  ring

/-- Every member has the same zero normalization. -/
@[simp]
theorem scalarEFTAction_zero
    (massSquared : ℝ) :
    scalarEFTAction massSquared 0 = 0 := by
  simp [scalarEFTAction]

/-- The actual linearized Euler map is symmetric for every mass. -/
theorem scalarEFTEuler_helmholtz
    (massSquared first second : ℝ) :
    ((1 + massSquared) * first) * second =
      first * ((1 + massSquared) * second) := by
  ring

/-- Distinct lower-order masses give distinct PT-even, normalized,
Helmholtz-compatible actions despite the same fixed leading normalization. -/
theorem scalar_symbol_pt_helmholtz_do_not_fix_action :
    scalarEFTAction 0 ≠ scalarEFTAction 1 := by
  intro hEqual
  have hAtOne := congrFun hEqual 1
  norm_num [scalarEFTAction] at hAtOne

/-- Exact verdict: uniqueness is relative to the full Euler operator, not to
its principal symbol or symmetry class. -/
theorem fullEuler_normalization_unique_but_symbolData_not_unique :
    (∀ massSquared,
        (∀ field,
          scalarEFTAction massSquared (-field) =
            scalarEFTAction massSquared field) ∧
        scalarEFTAction massSquared 0 = 0 ∧
        (∀ first second,
          ((1 + massSquared) * first) * second =
            first * ((1 + massSquared) * second))) ∧
      scalarEFTAction 0 ≠ scalarEFTAction 1 := by
  constructor
  · intro massSquared
    exact ⟨scalarEFTAction_ptEven massSquared,
      scalarEFTAction_zero massSquared,
      scalarEFTEuler_helmholtz massSquared⟩
  · exact scalar_symbol_pt_helmholtz_do_not_fix_action

end

end P0EFTJanusProgramPActionClassification4D
end JanusFormal
