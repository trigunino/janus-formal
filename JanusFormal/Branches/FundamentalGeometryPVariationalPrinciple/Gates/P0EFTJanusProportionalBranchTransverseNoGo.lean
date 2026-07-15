import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPTFlatBimetricVariationalBridge

namespace JanusFormal
namespace P0EFTJanusProportionalBranchTransverseNoGo

set_option autoImplicit false

open P0EFTJanusPTFlatBimetricVariationalBridge
open P0EFTJanusPTSymmetricFlatBimetricBranch

/-- Extension which is constant in the direction transverse to the
proportional branch. -/
def branchConstantExtension
    (beta1 beta2 : ℝ) (point : ℝ × ℝ) : ℝ :=
  proportionalInteractionEnergy beta1 beta2 point.1

/-- A family of extensions with an independently adjustable transverse
quadratic term. -/
def transverseQuadraticExtension
    (beta1 beta2 lambda : ℝ) (point : ℝ × ℝ) : ℝ :=
  proportionalInteractionEnergy beta1 beta2 point.1 + lambda * point.2 ^ 2

/-- Both extensions have exactly the same restriction to the proportional
branch `y = 0`. -/
theorem extensions_agree_on_proportional_branch
    (beta1 beta2 lambda c : ℝ) :
    branchConstantExtension beta1 beta2 (c, 0) =
      transverseQuadraticExtension beta1 beta2 lambda (c, 0) := by
  simp [branchConstantExtension, transverseQuadraticExtension]

/-- The first extension inherits the genuine derivative already proved for
the reduced proportional interaction energy. -/
theorem branchConstantExtension_hasDerivAt_along_branch
    (beta1 beta2 c : ℝ) :
    HasDerivAt (fun x => branchConstantExtension beta1 beta2 (x, 0))
      (proportionalInteractionForce beta1 beta2 c) c := by
  simpa [branchConstantExtension] using
    proportionalInteractionEnergy_hasDerivAt beta1 beta2 c

/-- Every member of the transverse family has the same genuine derivative
along the proportional branch. -/
theorem transverseQuadraticExtension_hasDerivAt_along_branch
    (beta1 beta2 lambda c : ℝ) :
    HasDerivAt (fun x => transverseQuadraticExtension beta1 beta2 lambda (x, 0))
      (proportionalInteractionForce beta1 beta2 c) c := by
  simpa [transverseQuadraticExtension] using
    proportionalInteractionEnergy_hasDerivAt beta1 beta2 c

theorem branchConstantExtension_hasDerivAt_transverse
    (beta1 beta2 c y : ℝ) :
    HasDerivAt (fun z => branchConstantExtension beta1 beta2 (c, z)) 0 y := by
  simpa [branchConstantExtension] using
    hasDerivAt_const y (proportionalInteractionEnergy beta1 beta2 c)

theorem transverseQuadraticExtension_hasDerivAt_transverse
    (beta1 beta2 lambda c y : ℝ) :
    HasDerivAt (fun z => transverseQuadraticExtension beta1 beta2 lambda (c, z))
      (2 * lambda * y) y := by
  have hConstant :
      HasDerivAt
        (fun _z : ℝ => proportionalInteractionEnergy beta1 beta2 c) 0 y :=
    hasDerivAt_const y (proportionalInteractionEnergy beta1 beta2 c)
  have hQuadratic :
      HasDerivAt (fun z : ℝ => lambda * z ^ 2) (lambda * (2 * y)) y := by
    simpa [id] using ((hasDerivAt_id y).pow 2).const_mul lambda
  unfold transverseQuadraticExtension
  convert hConstant.add hQuadratic using 1
  all_goals
    first
    | rfl
    | ring

/-- The actual transverse second derivative of the constant extension
vanishes. -/
theorem branchConstantExtension_second_hasDerivAt_transverse
    (beta1 beta2 c : ℝ) :
    HasDerivAt
      (fun y => deriv (fun z => branchConstantExtension beta1 beta2 (c, z)) y)
      0 0 := by
  have hDeriv :
      (fun y => deriv (fun z => branchConstantExtension beta1 beta2 (c, z)) y) =
        fun _y : ℝ => 0 := by
    funext y
    exact (branchConstantExtension_hasDerivAt_transverse beta1 beta2 c y).deriv
  rw [hDeriv]
  exact hasDerivAt_const 0 0

/-- The actual transverse second derivative of the quadratic extension is
`2 * lambda`. -/
theorem transverseQuadraticExtension_second_hasDerivAt_transverse
    (beta1 beta2 lambda c : ℝ) :
    HasDerivAt
      (fun y => deriv
        (fun z => transverseQuadraticExtension beta1 beta2 lambda (c, z)) y)
      (2 * lambda) 0 := by
  have hDeriv :
      (fun y => deriv
        (fun z => transverseQuadraticExtension beta1 beta2 lambda (c, z)) y) =
        fun y => 2 * lambda * y := by
    funext y
    exact
      (transverseQuadraticExtension_hasDerivAt_transverse
        beta1 beta2 lambda c y).deriv
  rw [hDeriv]
  simpa [id] using (hasDerivAt_id 0).const_mul (2 * lambda)

/-- For nonzero transverse coupling, two extensions indistinguishable on the
entire proportional branch have different genuine transverse curvatures.
Thus proportional scalar data cannot reconstruct a bimetric/transverse
extension.  This is a reconstruction no-go, not a construction of the full
Janus metric action. -/
theorem proportional_branch_does_not_determine_transverse_curvature
    (beta1 beta2 lambda c : ℝ) (hLambda : lambda ≠ 0) :
    deriv
        (fun y => deriv
          (fun z => branchConstantExtension beta1 beta2 (c, z)) y) 0 ≠
      deriv
        (fun y => deriv
          (fun z => transverseQuadraticExtension beta1 beta2 lambda (c, z)) y) 0 := by
  rw [(branchConstantExtension_second_hasDerivAt_transverse
      beta1 beta2 c).deriv,
    (transverseQuadraticExtension_second_hasDerivAt_transverse
      beta1 beta2 lambda c).deriv]
  exact Ne.symm (mul_ne_zero (by norm_num) hLambda)

/-- The two extensions also differ away from the proportional branch whenever
both the transverse coordinate and its coupling are nonzero. -/
theorem extensions_differ_off_proportional_branch
    (beta1 beta2 lambda c y : ℝ)
    (hLambda : lambda ≠ 0) (hY : y ≠ 0) :
    branchConstantExtension beta1 beta2 (c, y) ≠
      transverseQuadraticExtension beta1 beta2 lambda (c, y) := by
  unfold branchConstantExtension transverseQuadraticExtension
  intro hEqual
  have hQuadratic : lambda * y ^ 2 = 0 := by
    linarith
  exact (mul_ne_zero hLambda (pow_ne_zero 2 hY)) hQuadratic

end P0EFTJanusProportionalBranchTransverseNoGo
end JanusFormal
