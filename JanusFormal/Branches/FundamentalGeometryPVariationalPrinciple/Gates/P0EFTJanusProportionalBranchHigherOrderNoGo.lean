import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProportionalBranchTransverseNoGo

namespace JanusFormal
namespace P0EFTJanusProportionalBranchHigherOrderNoGo

set_option autoImplicit false

open P0EFTJanusPTFlatBimetricVariationalBridge
open P0EFTJanusPTSymmetricFlatBimetricBranch
open P0EFTJanusProportionalBranchTransverseNoGo

/-- A quadratic transverse extension of the reduced proportional action. -/
def quadraticReferenceExtension
    (beta1 beta2 kappa : ℝ) (point : ℝ × ℝ) : ℝ :=
  proportionalInteractionEnergy beta1 beta2 point.1 + kappa * point.2 ^ 2

/-- A quartic deformation invisible to the transverse two-jet at `y = 0`. -/
def quarticDeformedExtension
    (beta1 beta2 kappa lambda : ℝ) (point : ℝ × ℝ) : ℝ :=
  quadraticReferenceExtension beta1 beta2 kappa point + lambda * point.2 ^ 4

theorem extensions_agree_on_proportional_branch
    (beta1 beta2 kappa lambda c : ℝ) :
    quadraticReferenceExtension beta1 beta2 kappa (c, 0) =
      quarticDeformedExtension beta1 beta2 kappa lambda (c, 0) := by
  simp [quadraticReferenceExtension, quarticDeformedExtension]

theorem quadraticReferenceExtension_hasDerivAt_along_branch
    (beta1 beta2 kappa c : ℝ) :
    HasDerivAt
      (fun x => quadraticReferenceExtension beta1 beta2 kappa (x, 0))
      (proportionalInteractionForce beta1 beta2 c) c := by
  simpa [quadraticReferenceExtension] using
    proportionalInteractionEnergy_hasDerivAt beta1 beta2 c

theorem quarticDeformedExtension_hasDerivAt_along_branch
    (beta1 beta2 kappa lambda c : ℝ) :
    HasDerivAt
      (fun x => quarticDeformedExtension beta1 beta2 kappa lambda (x, 0))
      (proportionalInteractionForce beta1 beta2 c) c := by
  simpa [quarticDeformedExtension, quadraticReferenceExtension] using
    proportionalInteractionEnergy_hasDerivAt beta1 beta2 c

theorem longitudinal_derivatives_agree_on_branch
    (beta1 beta2 kappa lambda c : ℝ) :
    deriv (fun x => quadraticReferenceExtension beta1 beta2 kappa (x, 0)) c =
      deriv
        (fun x => quarticDeformedExtension beta1 beta2 kappa lambda (x, 0)) c := by
  rw [(quadraticReferenceExtension_hasDerivAt_along_branch
      beta1 beta2 kappa c).deriv,
    (quarticDeformedExtension_hasDerivAt_along_branch
      beta1 beta2 kappa lambda c).deriv]

theorem quadraticReferenceExtension_hasDerivAt_transverse
    (beta1 beta2 kappa c y : ℝ) :
    HasDerivAt
      (fun z => quadraticReferenceExtension beta1 beta2 kappa (c, z))
      (2 * kappa * y) y := by
  simpa [quadraticReferenceExtension, transverseQuadraticExtension] using
    transverseQuadraticExtension_hasDerivAt_transverse beta1 beta2 kappa c y

theorem quarticDeformedExtension_hasDerivAt_transverse
    (beta1 beta2 kappa lambda c y : ℝ) :
    HasDerivAt
      (fun z => quarticDeformedExtension beta1 beta2 kappa lambda (c, z))
      (2 * kappa * y + 4 * lambda * y ^ 3) y := by
  have hReference :=
    quadraticReferenceExtension_hasDerivAt_transverse beta1 beta2 kappa c y
  have hQuartic :
      HasDerivAt (fun z : ℝ => lambda * z ^ 4) (lambda * (4 * y ^ 3)) y := by
    simpa [id] using ((hasDerivAt_id y).pow 4).const_mul lambda
  unfold quarticDeformedExtension
  convert hReference.add hQuartic using 1
  all_goals
    first
    | rfl
    | ring

theorem transverse_first_derivatives_agree_on_branch
    (beta1 beta2 kappa lambda c : ℝ) :
    deriv (fun y => quadraticReferenceExtension beta1 beta2 kappa (c, y)) 0 =
      deriv
        (fun y => quarticDeformedExtension beta1 beta2 kappa lambda (c, y)) 0 := by
  rw [(quadraticReferenceExtension_hasDerivAt_transverse
      beta1 beta2 kappa c 0).deriv,
    (quarticDeformedExtension_hasDerivAt_transverse
      beta1 beta2 kappa lambda c 0).deriv]
  ring

theorem quadraticReferenceExtension_second_hasDerivAt_transverse
    (beta1 beta2 kappa c y : ℝ) :
    HasDerivAt
      (fun u => deriv
        (fun z => quadraticReferenceExtension beta1 beta2 kappa (c, z)) u)
      (2 * kappa) y := by
  have hDeriv :
      (fun u => deriv
        (fun z => quadraticReferenceExtension beta1 beta2 kappa (c, z)) u) =
        fun u => 2 * kappa * u := by
    funext u
    exact
      (quadraticReferenceExtension_hasDerivAt_transverse
        beta1 beta2 kappa c u).deriv
  rw [hDeriv]
  simpa [id] using (hasDerivAt_id y).const_mul (2 * kappa)

theorem quarticDeformedExtension_second_hasDerivAt_transverse
    (beta1 beta2 kappa lambda c y : ℝ) :
    HasDerivAt
      (fun u => deriv
        (fun z => quarticDeformedExtension beta1 beta2 kappa lambda (c, z)) u)
      (2 * kappa + 12 * lambda * y ^ 2) y := by
  have hDeriv :
      (fun u => deriv
        (fun z => quarticDeformedExtension beta1 beta2 kappa lambda (c, z)) u) =
        fun u => 2 * kappa * u + 4 * lambda * u ^ 3 := by
    funext u
    exact
      (quarticDeformedExtension_hasDerivAt_transverse
        beta1 beta2 kappa lambda c u).deriv
  rw [hDeriv]
  have hLinear :
      HasDerivAt (fun u : ℝ => 2 * kappa * u) (2 * kappa) y := by
    simpa [id] using (hasDerivAt_id y).const_mul (2 * kappa)
  have hCubic :
      HasDerivAt (fun u : ℝ => 4 * lambda * u ^ 3)
        ((4 * lambda) * (3 * y ^ 2)) y := by
    simpa [id] using ((hasDerivAt_id y).pow 3).const_mul (4 * lambda)
  convert hLinear.add hCubic using 1
  all_goals
    first
    | rfl
    | ring

theorem transverse_hessians_agree_on_branch
    (beta1 beta2 kappa lambda c : ℝ) :
    deriv
        (fun y => deriv
          (fun z => quadraticReferenceExtension beta1 beta2 kappa (c, z)) y) 0 =
      deriv
        (fun y => deriv
          (fun z => quarticDeformedExtension beta1 beta2 kappa lambda (c, z)) y) 0 := by
  rw [(quadraticReferenceExtension_second_hasDerivAt_transverse
      beta1 beta2 kappa c 0).deriv,
    (quarticDeformedExtension_second_hasDerivAt_transverse
      beta1 beta2 kappa lambda c 0).deriv]
  ring

/-- The two actions disagree away from the proportional branch whenever the
quartic coupling and transverse coordinate are nonzero. -/
theorem extensions_differ_off_proportional_branch
    (beta1 beta2 kappa lambda c y : ℝ)
    (hLambda : lambda ≠ 0) (hY : y ≠ 0) :
    quadraticReferenceExtension beta1 beta2 kappa (c, y) ≠
      quarticDeformedExtension beta1 beta2 kappa lambda (c, y) := by
  unfold quarticDeformedExtension
  intro hEqual
  have hQuartic : lambda * y ^ 4 = 0 := by
    linarith
  exact (mul_ne_zero hLambda (pow_ne_zero 4 hY)) hQuartic

/-- Genuine longitudinal derivatives and the complete transverse two-jet on
`y = 0` do not determine the nonlinear extension away from that branch.
This is a reduced two-variable reconstruction no-go, not a statement about
the full Janus metric field space. -/
theorem branch_and_transverse_twoJet_do_not_determine_nonlinear_extension
    (beta1 beta2 kappa lambda c y : ℝ)
    (hLambda : lambda ≠ 0) (hY : y ≠ 0) :
    (∀ x,
      quadraticReferenceExtension beta1 beta2 kappa (x, 0) =
        quarticDeformedExtension beta1 beta2 kappa lambda (x, 0)) ∧
    (∀ x,
      HasDerivAt
        (fun t => quadraticReferenceExtension beta1 beta2 kappa (t, 0))
        (proportionalInteractionForce beta1 beta2 x) x ∧
      HasDerivAt
        (fun t => quarticDeformedExtension beta1 beta2 kappa lambda (t, 0))
        (proportionalInteractionForce beta1 beta2 x) x) ∧
    (∀ x,
      HasDerivAt
        (fun z => quadraticReferenceExtension beta1 beta2 kappa (x, z)) 0 0 ∧
      HasDerivAt
        (fun z => quarticDeformedExtension beta1 beta2 kappa lambda (x, z)) 0 0) ∧
    (∀ x,
      HasDerivAt
        (fun u => deriv
          (fun z => quadraticReferenceExtension beta1 beta2 kappa (x, z)) u)
        (2 * kappa) 0 ∧
      HasDerivAt
        (fun u => deriv
          (fun z => quarticDeformedExtension beta1 beta2 kappa lambda (x, z)) u)
        (2 * kappa) 0) ∧
    quadraticReferenceExtension beta1 beta2 kappa (c, y) ≠
      quarticDeformedExtension beta1 beta2 kappa lambda (c, y) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x
    exact extensions_agree_on_proportional_branch beta1 beta2 kappa lambda x
  · intro x
    exact ⟨quadraticReferenceExtension_hasDerivAt_along_branch
        beta1 beta2 kappa x,
      quarticDeformedExtension_hasDerivAt_along_branch
        beta1 beta2 kappa lambda x⟩
  · intro x
    constructor
    · simpa using
        quadraticReferenceExtension_hasDerivAt_transverse
          beta1 beta2 kappa x 0
    · simpa using
        quarticDeformedExtension_hasDerivAt_transverse
          beta1 beta2 kappa lambda x 0
  · intro x
    constructor
    · exact quadraticReferenceExtension_second_hasDerivAt_transverse
        beta1 beta2 kappa x 0
    · simpa using
        quarticDeformedExtension_second_hasDerivAt_transverse
          beta1 beta2 kappa lambda x 0
  · exact extensions_differ_off_proportional_branch
      beta1 beta2 kappa lambda c y hLambda hY

end P0EFTJanusProportionalBranchHigherOrderNoGo
end JanusFormal
