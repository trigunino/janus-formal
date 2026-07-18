import JanusFormal.Branches.FundamentalGeometryD10QuillenAnomaly.Gates.P0EFTJanusCircleBoundedTransformSpectralFlow
import Mathlib.LinearAlgebra.Contraction

/-!
# Determinant-line family of the bounded circle Dirac family

The fibers here are the actual Fredholm determinant lines
`Hom(det coker Fₐ, det ker Fₐ)`.  Fourier zero-mode coordinates give a
nonzero algebraic frame in every fiber.  Large gauge relabeling gives an
actual linear equivalence of the determinant fibers at the two endpoints.

No topology is put on the disjoint union of the dependent fibers.  Therefore
the result below is an algebraic family, not yet a Mathlib `FiberBundle`,
Quillen metric/connection, or Bismut--Freed holonomy construction.
-/

namespace JanusFormal
namespace P0EFTJanusCircleDeterminantLineFamily

set_option autoImplicit false

noncomputable section

open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusCircleUnboundedDiracDomain
open P0EFTJanusCircleHolonomyCommonDomainCompactResolvent
open P0EFTJanusCircleGraphFredholmIndex
open P0EFTJanusCircleBoundedTransformSpectralFlow
open scoped ENNReal lp

/-! ## Actual pointwise Fredholm determinant fibers -/

noncomputable def circleBoundedKernelZeroModeEquiv
    (fold : Fold) (twist : CircleTwist) :
    LinearMap.ker (circleBoundedTransform fold twist).toLinearMap ≃ₗ[ℂ]
      (CircleZeroMode fold twist → ℂ) :=
  LinearEquiv.ofBijective
    (circleBoundedKernelZeroRestriction fold twist)
    ⟨circleBoundedKernelZeroRestriction_injective fold twist,
      circleBoundedKernelZeroRestriction_surjective fold twist⟩

noncomputable def circleBoundedCokernelZeroModeEquiv
    (fold : Fold) (twist : CircleTwist) :
    CircleBoundedTransformCokernel fold twist ≃ₗ[ℂ]
      (CircleZeroMode fold twist → ℂ) := by
  let quotientEquivalence :
      CircleBoundedTransformCokernel fold twist ≃ₗ[ℂ]
        (CircleHilbert ⧸ LinearMap.ker (circleZeroRestriction fold twist)) :=
    Submodule.quotEquivOfEq _ _
      (circleBoundedTransform_range_eq_zeroRestriction_ker fold twist)
  let rangeEquivalence :=
    (circleZeroRestriction fold twist).quotKerEquivRange
  have hRange : LinearMap.range (circleZeroRestriction fold twist) = ⊤ :=
    LinearMap.range_eq_top.mpr (circleZeroRestriction_surjective fold twist)
  let topEquivalence :
      LinearMap.range (circleZeroRestriction fold twist) ≃ₗ[ℂ]
        (CircleZeroMode fold twist → ℂ) :=
    LinearEquiv.ofTop _ hRange
  exact quotientEquivalence.trans
    (rangeEquivalence.trans topEquivalence)

noncomputable def circleBoundedCokernelKernelEquiv
    (fold : Fold) (twist : CircleTwist) :
    CircleBoundedTransformCokernel fold twist ≃ₗ[ℂ]
      LinearMap.ker (circleBoundedTransform fold twist).toLinearMap :=
  (circleBoundedCokernelZeroModeEquiv fold twist).trans
    (circleBoundedKernelZeroModeEquiv fold twist).symm

noncomputable instance circleBoundedKernelFree
    (fold : Fold) (twist : CircleTwist) :
    Module.Free ℂ
      (LinearMap.ker (circleBoundedTransform fold twist).toLinearMap) :=
  Module.Free.of_equiv (circleBoundedKernelZeroModeEquiv fold twist).symm

noncomputable instance circleBoundedCokernelFree
    (fold : Fold) (twist : CircleTwist) :
    Module.Free ℂ (CircleBoundedTransformCokernel fold twist) :=
  Module.Free.of_equiv (circleBoundedCokernelZeroModeEquiv fold twist).symm

/-- Common top-exterior degree of kernel and cokernel. -/
abbrev CircleDeterminantDegree (fold : Fold) (twist : CircleTwist) : ℕ :=
  Module.finrank ℂ (CircleZeroMode fold twist → ℂ)

abbrev CircleBoundedKernelTop (fold : Fold) (twist : CircleTwist) :=
  ⋀[ℂ]^(CircleDeterminantDegree fold twist)
    (LinearMap.ker (circleBoundedTransform fold twist).toLinearMap)

abbrev CircleBoundedCokernelTop (fold : Fold) (twist : CircleTwist) :=
  ⋀[ℂ]^(CircleDeterminantDegree fold twist)
    (CircleBoundedTransformCokernel fold twist)

/-- Actual determinant-line fiber `Hom(det coker, det ker)`. -/
abbrev CircleBoundedDeterminantLine (fold : Fold) (twist : CircleTwist) :=
  CircleBoundedCokernelTop fold twist →ₗ[ℂ]
    CircleBoundedKernelTop fold twist

/-- Fourier-coordinate frame; this is not the vanishing Fredholm determinant section. -/
noncomputable def circleDeterminantFourierFrame
    (fold : Fold) (twist : CircleTwist) :
    CircleBoundedDeterminantLine fold twist :=
  exteriorPower.map (CircleDeterminantDegree fold twist)
    (circleBoundedCokernelKernelEquiv fold twist).toLinearMap

theorem circleBoundedKernelTop_finrank_one
    (fold : Fold) (twist : CircleTwist) :
    Module.finrank ℂ (CircleBoundedKernelTop fold twist) = 1 := by
  rw [exteriorPower.finrank_eq,
    circleBoundedTransformKernel_finrank_eq_zeroModes, Nat.choose_self]

theorem circleBoundedCokernelTop_finrank_one
    (fold : Fold) (twist : CircleTwist) :
    Module.finrank ℂ (CircleBoundedCokernelTop fold twist) = 1 := by
  rw [exteriorPower.finrank_eq,
    circleBoundedTransformCokernel_finrank_eq_zeroModes, Nat.choose_self]

theorem circleBoundedDeterminantLine_finrank_one
    (fold : Fold) (twist : CircleTwist) :
    Module.finrank ℂ (CircleBoundedDeterminantLine fold twist) = 1 := by
  rw [Module.finrank_linearMap,
    circleBoundedCokernelTop_finrank_one,
    circleBoundedKernelTop_finrank_one]

theorem circleDeterminantFourierFrame_injective
    (fold : Fold) (twist : CircleTwist) :
    Function.Injective (circleDeterminantFourierFrame fold twist) := by
  exact exteriorPower.map_injective_field
    (circleBoundedCokernelKernelEquiv fold twist).injective

theorem circleDeterminantFourierFrame_ne_zero
    (fold : Fold) (twist : CircleTwist) :
    circleDeterminantFourierFrame fold twist ≠ 0 := by
  letI : Nontrivial (CircleBoundedCokernelTop fold twist) :=
    Module.nontrivial_of_finrank_eq_succ (R := ℂ)
      (circleBoundedCokernelTop_finrank_one fold twist)
  exact LinearMap.ne_zero_of_injective
    (circleDeterminantFourierFrame_injective fold twist)

/-! ## Large-gauge transition of the endpoint determinant fibers -/

noncomputable def complexExteriorPowerEquiv
    {first second : Type*}
    [AddCommGroup first] [Module ℂ first]
    [AddCommGroup second] [Module ℂ second]
    (degree : ℕ) (equivalence : first ≃ₗ[ℂ] second) :
    ⋀[ℂ]^degree first ≃ₗ[ℂ] ⋀[ℂ]^degree second :=
  LinearEquiv.ofBijective
    (exteriorPower.map degree equivalence.toLinearMap)
    ⟨exteriorPower.map_injective_field equivalence.injective,
      exteriorPower.map_surjective equivalence.surjective⟩

noncomputable def complexExteriorPowerCast
    {space : Type*} [AddCommGroup space] [Module ℂ space]
    {first second : ℕ} (hDegree : first = second) :
    ⋀[ℂ]^first space ≃ₗ[ℂ] ⋀[ℂ]^second space := by
  subst second
  exact LinearEquiv.refl ℂ _

/-- Reindex zero-mode coefficients by the exact large-gauge endpoint shift. -/
noncomputable def endpointZeroCoefficientEquiv (fold : Fold) :
    (CircleZeroMode fold unitCircleTwist → ℂ) ≃ₗ[ℂ]
      (CircleZeroMode fold periodicTwist → ℂ) :=
  LinearEquiv.piCongrLeft ℂ
    (fun _ : CircleZeroMode fold periodicTwist => ℂ)
    (unitPeriodicZeroModeEquiv fold)

noncomputable def endpointKernelEquiv (fold : Fold) :
    LinearMap.ker (circleBoundedTransform fold unitCircleTwist).toLinearMap ≃ₗ[ℂ]
      LinearMap.ker (circleBoundedTransform fold periodicTwist).toLinearMap :=
  (circleBoundedKernelZeroModeEquiv fold unitCircleTwist).trans
    ((endpointZeroCoefficientEquiv fold).trans
      (circleBoundedKernelZeroModeEquiv fold periodicTwist).symm)

noncomputable def endpointCokernelEquiv (fold : Fold) :
    CircleBoundedTransformCokernel fold unitCircleTwist ≃ₗ[ℂ]
      CircleBoundedTransformCokernel fold periodicTwist :=
  (circleBoundedCokernelZeroModeEquiv fold unitCircleTwist).trans
    ((endpointZeroCoefficientEquiv fold).trans
      (circleBoundedCokernelZeroModeEquiv fold periodicTwist).symm)

theorem endpointDeterminantDegree_eq (fold : Fold) :
    CircleDeterminantDegree fold unitCircleTwist =
      CircleDeterminantDegree fold periodicTwist :=
  (endpointZeroCoefficientEquiv fold).finrank_eq

noncomputable def endpointKernelTopEquiv (fold : Fold) :
    CircleBoundedKernelTop fold unitCircleTwist ≃ₗ[ℂ]
      CircleBoundedKernelTop fold periodicTwist :=
  (complexExteriorPowerEquiv
      (CircleDeterminantDegree fold unitCircleTwist)
      (endpointKernelEquiv fold)).trans
    (complexExteriorPowerCast (endpointDeterminantDegree_eq fold))

noncomputable def endpointCokernelTopEquiv (fold : Fold) :
    CircleBoundedCokernelTop fold unitCircleTwist ≃ₗ[ℂ]
      CircleBoundedCokernelTop fold periodicTwist :=
  (complexExteriorPowerEquiv
      (CircleDeterminantDegree fold unitCircleTwist)
      (endpointCokernelEquiv fold)).trans
    (complexExteriorPowerCast (endpointDeterminantDegree_eq fold))

/-- Actual large-gauge transition between the two endpoint determinant fibers. -/
noncomputable def circleLargeGaugeDeterminantTransition (fold : Fold) :
    CircleBoundedDeterminantLine fold unitCircleTwist ≃ₗ[ℂ]
      CircleBoundedDeterminantLine fold periodicTwist :=
  (endpointCokernelTopEquiv fold).arrowCongr
    (endpointKernelTopEquiv fold)

theorem circleLargeGaugeDeterminantTransition_bijective
    (fold : Fold) :
    Function.Bijective (circleLargeGaugeDeterminantTransition fold) :=
  (circleLargeGaugeDeterminantTransition fold).bijective

end


end P0EFTJanusCircleDeterminantLineFamily
end JanusFormal
