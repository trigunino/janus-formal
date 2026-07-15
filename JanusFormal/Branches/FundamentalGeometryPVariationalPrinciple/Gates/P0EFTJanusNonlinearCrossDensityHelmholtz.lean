import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusConvexHelmholtzReconstruction

namespace JanusFormal
namespace P0EFTJanusNonlinearCrossDensityHelmholtz

set_option autoImplicit false

noncomputable section

open Set
open P0EFTJanusConvexHelmholtzReconstruction

variable {Plus Minus Matter : Type*}
variable [NormedAddCommGroup Plus] [NormedSpace ℝ Plus]
variable [NormedAddCommGroup Minus] [NormedSpace ℝ Minus]
variable [NormedAddCommGroup Matter] [NormedSpace ℝ Matter]

/-- Genuine three-sector product configuration space. -/
abbrev ThreeFieldConfiguration := Plus × (Minus × Matter)

/-- Pure plus-sector direction in the product space. -/
def plusDirection (direction : Plus) :
    ThreeFieldConfiguration (Plus := Plus) (Minus := Minus) (Matter := Matter) :=
  (direction, (0, 0))

/-- Pure minus-sector direction in the product space. -/
def minusDirection (direction : Minus) :
    ThreeFieldConfiguration (Plus := Plus) (Minus := Minus) (Matter := Matter) :=
  (0, (direction, 0))

/-- Pure matter direction in the product space. -/
def matterDirection (direction : Matter) :
    ThreeFieldConfiguration (Plus := Plus) (Minus := Minus) (Matter := Matter) :=
  (0, (0, direction))

omit [NormedSpace ℝ Plus] [NormedSpace ℝ Minus]
    [NormedSpace ℝ Matter] in
theorem threeField_decomposition
    (direction : ThreeFieldConfiguration
      (Plus := Plus) (Minus := Minus) (Matter := Matter)) :
    direction = plusDirection direction.1 +
      minusDirection direction.2.1 + matterDirection direction.2.2 := by
  ext <;> simp [plusDirection, minusDirection, matterDirection]

/--
All six nonlinear block Helmholtz conditions at one product-space point:
three diagonal blocks must be symmetric and the three ordered cross blocks
must be reciprocal.  The conditions concern the actual Fréchet derivative of
the full Euler one-form, not symbolic source coefficients.
-/
structure BlockDerivativeReciprocityAt
    (euler : EulerOneForm
      (ThreeFieldConfiguration (Plus := Plus) (Minus := Minus)
        (Matter := Matter)))
    (x : ThreeFieldConfiguration (Plus := Plus) (Minus := Minus)
      (Matter := Matter)) : Prop where
  plusDiagonal : ∀ first second : Plus,
    fderiv ℝ euler x (plusDirection first) (plusDirection second) =
      fderiv ℝ euler x (plusDirection second) (plusDirection first)
  minusDiagonal : ∀ first second : Minus,
    fderiv ℝ euler x (minusDirection first) (minusDirection second) =
      fderiv ℝ euler x (minusDirection second) (minusDirection first)
  matterDiagonal : ∀ first second : Matter,
    fderiv ℝ euler x (matterDirection first) (matterDirection second) =
      fderiv ℝ euler x (matterDirection second) (matterDirection first)
  plusMinus : ∀ plus minus,
    fderiv ℝ euler x (plusDirection plus) (minusDirection minus) =
      fderiv ℝ euler x (minusDirection minus) (plusDirection plus)
  plusMatter : ∀ plus matter,
    fderiv ℝ euler x (plusDirection plus) (matterDirection matter) =
      fderiv ℝ euler x (matterDirection matter) (plusDirection plus)
  minusMatter : ∀ minus matter,
    fderiv ℝ euler x (minusDirection minus) (matterDirection matter) =
      fderiv ℝ euler x (matterDirection matter) (minusDirection minus)

/-- Product-space block reciprocity is exactly self-adjointness of the total
actual Euler derivative.  This equivalence is pointwise and allows arbitrary
nonlinear dependence of the blocks on `x`. -/
theorem blockDerivativeReciprocityAt_iff_helmholtzJacobianAt
    (euler : EulerOneForm
      (ThreeFieldConfiguration (Plus := Plus) (Minus := Minus)
        (Matter := Matter)))
    (x : ThreeFieldConfiguration (Plus := Plus) (Minus := Minus)
      (Matter := Matter)) :
    BlockDerivativeReciprocityAt euler x ↔
      HelmholtzJacobianAt euler x := by
  constructor
  · intro hBlocks first second
    have hPP := hBlocks.plusDiagonal first.1 second.1
    have hMM := hBlocks.minusDiagonal first.2.1 second.2.1
    have hTT := hBlocks.matterDiagonal first.2.2 second.2.2
    have hPM := hBlocks.plusMinus first.1 second.2.1
    have hMP := hBlocks.plusMinus second.1 first.2.1
    have hPT := hBlocks.plusMatter first.1 second.2.2
    have hTP := hBlocks.plusMatter second.1 first.2.2
    have hMT := hBlocks.minusMatter first.2.1 second.2.2
    have hTM := hBlocks.minusMatter second.2.1 first.2.2
    rw [threeField_decomposition first, threeField_decomposition second]
    simp only [map_add, add_apply]
    linarith
  · intro hTotal
    exact {
      plusDiagonal := fun first second =>
        hTotal (plusDirection first) (plusDirection second)
      minusDiagonal := fun first second =>
        hTotal (minusDirection first) (minusDirection second)
      matterDiagonal := fun first second =>
        hTotal (matterDirection first) (matterDirection second)
      plusMinus := fun plus minus =>
        hTotal (plusDirection plus) (minusDirection minus)
      plusMatter := fun plus matter =>
        hTotal (plusDirection plus) (matterDirection matter)
      minusMatter := fun minus matter =>
        hTotal (minusDirection minus) (matterDirection matter) }

/-- Nonlinear block reciprocity throughout a product-space domain. -/
def BlockDerivativeReciprocityOn
    (domain : Set (ThreeFieldConfiguration
      (Plus := Plus) (Minus := Minus) (Matter := Matter)))
    (euler : EulerOneForm
      (ThreeFieldConfiguration (Plus := Plus) (Minus := Minus)
        (Matter := Matter))) : Prop :=
  ∀ x ∈ domain, BlockDerivativeReciprocityAt euler x

/-- Domain-level form of the exact block/total equivalence. -/
theorem blockDerivativeReciprocityOn_iff_helmholtzJacobianOn
    (domain : Set (ThreeFieldConfiguration
      (Plus := Plus) (Minus := Minus) (Matter := Matter)))
    (euler : EulerOneForm
      (ThreeFieldConfiguration (Plus := Plus) (Minus := Minus)
        (Matter := Matter))) :
    BlockDerivativeReciprocityOn domain euler ↔
      HelmholtzJacobianOn domain euler := by
  constructor
  · intro hBlocks x hx
    exact (blockDerivativeReciprocityAt_iff_helmholtzJacobianAt
      euler x).mp (hBlocks x hx)
  · intro hTotal x hx
    exact (blockDerivativeReciprocityAt_iff_helmholtzJacobianAt
      euler x).mpr (hTotal x hx)

/-- A normalized common action on a domain.  Only its actual derivative on
the domain and its chosen base value are asserted. -/
def IsNormalizedCommonActionOn
    (domain : Set (ThreeFieldConfiguration
      (Plus := Plus) (Minus := Minus) (Matter := Matter)))
    (euler : EulerOneForm
      (ThreeFieldConfiguration (Plus := Plus) (Minus := Minus)
        (Matter := Matter)))
    (base : ThreeFieldConfiguration (Plus := Plus) (Minus := Minus)
      (Matter := Matter))
    (action : ThreeFieldConfiguration (Plus := Plus) (Minus := Minus)
      (Matter := Matter) → ℝ) : Prop :=
  base ∈ domain ∧ action base = 0 ∧
    ∀ x ∈ domain, HasFDerivAt action (euler x) x

/--
Nonlinear product-space acceptance theorem.  On an open convex domain, actual
block reciprocity plus differentiability reconstructs a common scalar action,
normalized at any supplied base in the domain.
-/
theorem open_convex_block_reciprocity_reconstructs_normalized_action
    {domain : Set (ThreeFieldConfiguration
      (Plus := Plus) (Minus := Minus) (Matter := Matter))}
    (euler : EulerOneForm
      (ThreeFieldConfiguration (Plus := Plus) (Minus := Minus)
        (Matter := Matter)))
    (hConvex : Convex ℝ domain)
    (hOpen : IsOpen domain)
    (hDifferentiable : DifferentiableOn ℝ euler domain)
    (hBlocks : BlockDerivativeReciprocityOn domain euler)
    (base : ThreeFieldConfiguration (Plus := Plus) (Minus := Minus)
      (Matter := Matter))
    (hBase : base ∈ domain) :
    ∃ action, IsNormalizedCommonActionOn domain euler base action := by
  have hHelmholtz : HelmholtzJacobianOn domain euler :=
    (blockDerivativeReciprocityOn_iff_helmholtzJacobianOn
      domain euler).mp hBlocks
  obtain ⟨action, hAction⟩ := convex_open_helmholtz_reconstruction
    euler hConvex hOpen hDifferentiable hHelmholtz
  let normalized := fun x => action x - action base
  refine ⟨normalized, hBase, ?_, ?_⟩
  · simp [normalized]
  · intro x hx
    exact (hAction x hx).sub_const (action base)

/-- Normalization removes the additive ambiguity on the convex domain. -/
theorem normalized_common_action_unique_on_domain
    {domain : Set (ThreeFieldConfiguration
      (Plus := Plus) (Minus := Minus) (Matter := Matter))}
    {euler : EulerOneForm
      (ThreeFieldConfiguration (Plus := Plus) (Minus := Minus)
        (Matter := Matter))}
    {base : ThreeFieldConfiguration (Plus := Plus) (Minus := Minus)
      (Matter := Matter)}
    {firstAction secondAction :
      ThreeFieldConfiguration (Plus := Plus) (Minus := Minus)
        (Matter := Matter) → ℝ}
    (hConvex : Convex ℝ domain)
    (hFirst : IsNormalizedCommonActionOn domain euler base firstAction)
    (hSecond : IsNormalizedCommonActionOn domain euler base secondAction) :
    domain.EqOn firstAction secondAction := by
  exact convex_actions_same_euler_eqOn_of_eq_at_base
    hConvex hFirst.2.2 hSecond.2.2 hFirst.1
      (hFirst.2.1.trans hSecond.2.1.symm)

/-- A global C² common-action witness, used only for the obstruction theorem
below. -/
def HasGlobalC2CommonAction
    (euler : EulerOneForm
      (ThreeFieldConfiguration (Plus := Plus) (Minus := Minus)
        (Matter := Matter))) : Prop :=
  ∃ action : ThreeFieldConfiguration (Plus := Plus) (Minus := Minus)
      (Matter := Matter) → ℝ,
    ContDiff ℝ 2 action ∧
      ∀ x, HasFDerivAt action (euler x) x

/-- Every genuine global C² common action forces all nonlinear block
reciprocities at every point. -/
theorem global_common_action_forces_block_reciprocity
    (euler : EulerOneForm
      (ThreeFieldConfiguration (Plus := Plus) (Minus := Minus)
        (Matter := Matter)))
    (hAction : HasGlobalC2CommonAction euler)
    (x : ThreeFieldConfiguration (Plus := Plus) (Minus := Minus)
      (Matter := Matter)) :
    BlockDerivativeReciprocityAt euler x := by
  obtain ⟨action, hSmooth, hGradient⟩ := hAction
  have hGradientEq : actionGradient action = euler := by
    funext point
    exact (hGradient point).fderiv
  have hTotal := action_gradient_helmholtz_at action x hSmooth.contDiffAt
  rw [hGradientEq] at hTotal
  exact (blockDerivativeReciprocityAt_iff_helmholtzJacobianAt
    euler x).mpr hTotal

/--
Explicit failed-block no-go: one exhibited plus/minus reciprocity failure of
the actual derivative excludes a global C² common action with that Euler
one-form.  The theorem does not assert that M30 supplies such a block or such
a mismatch; its cross functionals must first be made explicit and varied.
-/
theorem failed_plus_minus_block_no_global_common_action
    (euler : EulerOneForm
      (ThreeFieldConfiguration (Plus := Plus) (Minus := Minus)
        (Matter := Matter)))
    (x : ThreeFieldConfiguration (Plus := Plus) (Minus := Minus)
      (Matter := Matter))
    (plus : Plus) (minus : Minus)
    (hFailure :
      fderiv ℝ euler x (plusDirection plus) (minusDirection minus) ≠
        fderiv ℝ euler x (minusDirection minus) (plusDirection plus)) :
    ¬ HasGlobalC2CommonAction euler := by
  intro hAction
  exact hFailure
    ((global_common_action_forces_block_reciprocity
      euler hAction x).plusMinus plus minus)

end

end P0EFTJanusNonlinearCrossDensityHelmholtz
end JanusFormal
