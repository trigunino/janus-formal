import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare

namespace JanusFormal
namespace P0EFTJanusConvexHelmholtzReconstruction

set_option autoImplicit false

open Set

/-- An Euler one-form on a real normed configuration space. -/
abbrev EulerOneForm (Configuration : Type*)
    [NormedAddCommGroup Configuration] [NormedSpace ℝ Configuration] :=
  Configuration → Configuration →L[ℝ] ℝ

/-- Pointwise nonlinear Helmholtz condition: the actual Jacobian is symmetric. -/
def HelmholtzJacobianAt
    {Configuration : Type*}
    [NormedAddCommGroup Configuration] [NormedSpace ℝ Configuration]
    (euler : EulerOneForm Configuration) (x : Configuration) : Prop :=
  ∀ u v,
    fderiv ℝ euler x u v = fderiv ℝ euler x v u

/-- Nonlinear Helmholtz condition on a configuration-space domain. -/
def HelmholtzJacobianOn
    {Configuration : Type*}
    [NormedAddCommGroup Configuration] [NormedSpace ℝ Configuration]
    (domain : Set Configuration) (euler : EulerOneForm Configuration) : Prop :=
  ∀ x ∈ domain, HelmholtzJacobianAt euler x

/-- The actual Fréchet gradient field of an action. -/
noncomputable def actionGradient
    {Configuration : Type*}
    [NormedAddCommGroup Configuration] [NormedSpace ℝ Configuration]
    (action : Configuration → ℝ) : EulerOneForm Configuration :=
  fun x => fderiv ℝ action x

/-- Every twice continuously differentiable action has a Helmholtz-symmetric
actual gradient Jacobian. -/
theorem action_gradient_helmholtz_at
    {Configuration : Type*}
    [NormedAddCommGroup Configuration] [NormedSpace ℝ Configuration]
    (action : Configuration → ℝ) (x : Configuration)
    (hSmooth : ContDiffAt ℝ 2 action x) :
    HelmholtzJacobianAt (actionGradient action) x := by
  intro u v
  change fderiv ℝ (fun y => fderiv ℝ action y) x u v =
    fderiv ℝ (fun y => fderiv ℝ action y) x v u
  exact (hSmooth.isSymmSndFDerivAt (by simp)).eq u v

/-- Poincaré--Helmholtz reconstruction on an open convex domain: a
differentiable Euler one-form with symmetric actual Jacobian is the exact
Fréchet derivative of a scalar action throughout that domain. -/
theorem convex_open_helmholtz_reconstruction
    {Configuration : Type*}
    [NormedAddCommGroup Configuration] [NormedSpace ℝ Configuration]
    {domain : Set Configuration} (euler : EulerOneForm Configuration)
    (hConvex : Convex ℝ domain) (hOpen : IsOpen domain)
    (hDifferentiable : DifferentiableOn ℝ euler domain)
    (hHelmholtz : HelmholtzJacobianOn domain euler) :
    ∃ action : Configuration → ℝ,
      ∀ x ∈ domain, HasFDerivAt action (euler x) x := by
  exact hConvex.exists_forall_hasFDerivAt_of_fderiv_symmetric
    hOpen hDifferentiable hHelmholtz

/-- The canonical straight-segment primitive normalized at a chosen base. -/
noncomputable def radialAction
    {Configuration : Type*}
    [NormedAddCommGroup Configuration] [NormedSpace ℝ Configuration]
    (base : Configuration) (euler : EulerOneForm Configuration)
    (x : Configuration) : ℝ :=
  curveIntegral euler (Path.segment base x)

/-- On the whole configuration space, the straight-segment primitive has the
prescribed Euler one-form as its actual Fréchet derivative. -/
theorem radial_action_hasFDerivAt
    {Configuration : Type*}
    [NormedAddCommGroup Configuration] [NormedSpace ℝ Configuration]
    (euler : EulerOneForm Configuration)
    (hDifferentiable : Differentiable ℝ euler)
    (hHelmholtz : ∀ x, HelmholtzJacobianAt euler x)
    (base x : Configuration) :
    HasFDerivAt (radialAction base euler) (euler x) x := by
  have hWithin :
      HasFDerivWithinAt
        (fun y => curveIntegral euler (Path.segment base y))
        (euler x) Set.univ x := by
    refine Convex.hasFDerivWithinAt_curveIntegral_segment_of_hasFDerivWithinAt_symmetric
      (s := Set.univ) (a := base) (b := x)
      (dω := fun y => fderiv ℝ euler y)
      convex_univ ?_ ?_ (by simp) (by simp)
    · intro y _
      exact (hDifferentiable y).hasFDerivAt.hasFDerivWithinAt
    · intro y _ u _ v _
      exact hHelmholtz y u v
  change HasFDerivAt
    (fun y => curveIntegral euler (Path.segment base y)) (euler x) x
  exact hWithin.hasFDerivAt (isOpen_univ.mem_nhds (Set.mem_univ x))

/-- The straight-segment primitive fixes the affine ambiguity by vanishing at
its chosen base point. -/
@[simp] theorem radial_action_at_base
    {Configuration : Type*}
    [NormedAddCommGroup Configuration] [NormedSpace ℝ Configuration]
    (base : Configuration) (euler : EulerOneForm Configuration) :
    radialAction base euler base = 0 := by
  simp [radialAction]

/-- On a convex domain, two actions with the same actual Euler one-form have
constant difference.  The constant is evaluated at any chosen base point in
the domain. -/
theorem convex_actions_same_euler_difference_eq_base_difference
    {Configuration : Type*}
    [NormedAddCommGroup Configuration] [NormedSpace ℝ Configuration]
    {domain : Set Configuration}
    {euler : EulerOneForm Configuration}
    {firstAction secondAction : Configuration → ℝ}
    (hConvex : Convex ℝ domain)
    (hFirst : ∀ x ∈ domain,
      HasFDerivAt firstAction (euler x) x)
    (hSecond : ∀ x ∈ domain,
      HasFDerivAt secondAction (euler x) x)
    {base x : Configuration} (hBase : base ∈ domain) (hx : x ∈ domain) :
    firstAction x - secondAction x =
      firstAction base - secondAction base := by
  have hDifference :
      ∀ y ∈ domain,
        HasFDerivWithinAt
          (fun z => firstAction z - secondAction z)
          (0 : Configuration →L[ℝ] ℝ) domain y := by
    intro y hy
    exact ((hFirst y hy).sub (hSecond y hy)).congr_fderiv
      (sub_self (euler y)) |>.hasFDerivWithinAt
  have hEstimate :
      ‖(firstAction x - secondAction x) -
          (firstAction base - secondAction base)‖ ≤
        (0 : ℝ) * ‖x - base‖ :=
    hConvex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      hDifference (fun _ _ => by simp) hBase hx
  simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using hEstimate

/-- Existence of the additive constant relating two actions with the same
actual Euler one-form on a nonempty convex domain. -/
theorem convex_actions_same_euler_differ_by_constant
    {Configuration : Type*}
    [NormedAddCommGroup Configuration] [NormedSpace ℝ Configuration]
    {domain : Set Configuration}
    {euler : EulerOneForm Configuration}
    {firstAction secondAction : Configuration → ℝ}
    (hConvex : Convex ℝ domain) (hNonempty : domain.Nonempty)
    (hFirst : ∀ x ∈ domain,
      HasFDerivAt firstAction (euler x) x)
    (hSecond : ∀ x ∈ domain,
      HasFDerivAt secondAction (euler x) x) :
    ∃ constant : ℝ, ∀ x ∈ domain,
      firstAction x = secondAction x + constant := by
  rcases hNonempty with ⟨base, hBase⟩
  refine ⟨firstAction base - secondAction base, ?_⟩
  intro x hx
  have hDifference :=
    convex_actions_same_euler_difference_eq_base_difference
      hConvex hFirst hSecond hBase hx
  linarith

/-- Fixing the value at one base point removes the additive ambiguity: two
actions with the same actual Euler one-form agree throughout the convex
domain. -/
theorem convex_actions_same_euler_eqOn_of_eq_at_base
    {Configuration : Type*}
    [NormedAddCommGroup Configuration] [NormedSpace ℝ Configuration]
    {domain : Set Configuration}
    {euler : EulerOneForm Configuration}
    {firstAction secondAction : Configuration → ℝ}
    (hConvex : Convex ℝ domain)
    (hFirst : ∀ x ∈ domain,
      HasFDerivAt firstAction (euler x) x)
    (hSecond : ∀ x ∈ domain,
      HasFDerivAt secondAction (euler x) x)
    {base : Configuration} (hBase : base ∈ domain)
    (hEqualAtBase : firstAction base = secondAction base) :
    domain.EqOn firstAction secondAction := by
  intro x hx
  apply sub_eq_zero.mp
  calc
    firstAction x - secondAction x =
        firstAction base - secondAction base :=
      convex_actions_same_euler_difference_eq_base_difference
        hConvex hFirst hSecond hBase hx
    _ = 0 := sub_eq_zero.mpr hEqualAtBase

end P0EFTJanusConvexHelmholtzReconstruction
end JanusFormal
