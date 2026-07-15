import Mathlib.LinearAlgebra.Quotient.Bilinear
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFrechetPullbackGaugeDegeneracy

namespace JanusFormal
namespace P0EFTJanusFrechetPullbackQuotientHessian

set_option autoImplicit false

noncomputable section

open P0EFTJanusFrechetPullbackSecondVariation
open P0EFTJanusFrechetPullbackHelmholtz
open P0EFTJanusFrechetPullbackGaugeDegeneracy

universe u v

variable {Source : Type u} {Target : Type v}
variable [NormedAddCommGroup Source] [NormedSpace ℝ Source]
variable [NormedAddCommGroup Target] [NormedSpace ℝ Target]

/-- The algebraic bilinear form underlying a curried continuous Hessian. -/
def continuousHessianToLinear
    (hessian : Source →L[ℝ] Source →L[ℝ] ℝ) :
    Source →ₗ[ℝ] Source →ₗ[ℝ] ℝ where
  toFun first := (hessian first).toLinearMap
  map_add' first second := by
    ext direction
    simp
  map_smul' scalar first := by
    ext direction
    simp

@[simp]
theorem continuousHessianToLinear_apply
    (hessian : Source →L[ℝ] Source →L[ℝ] ℝ)
    (first second : Source) :
    continuousHessianToLinear hessian first second = hessian first second := rfl

/-- A bilinear Hessian that vanishes on a gauge submodule in both arguments
descends to the algebraic quotient.  This construction makes no topology or
smooth-quotient claim. -/
def quotientHessian
    (hessian : Source →ₗ[ℝ] Source →ₗ[ℝ] ℝ)
    (gaugeDirections : Submodule ℝ Source)
    (hLeft : ∀ gauge ∈ gaugeDirections, ∀ direction, hessian gauge direction = 0)
    (hRight : ∀ gauge ∈ gaugeDirections, ∀ direction, hessian direction gauge = 0) :
    (Source ⧸ gaugeDirections) →ₗ[ℝ]
      (Source ⧸ gaugeDirections) →ₗ[ℝ] ℝ :=
  hessian.liftQ₂ gaugeDirections gaugeDirections
    (by
      intro gauge hGauge
      ext direction
      exact hLeft gauge hGauge direction)
    (by
      intro gauge hGauge
      ext direction
      exact hRight gauge hGauge direction)

@[simp]
theorem quotientHessian_mkQ
    (hessian : Source →ₗ[ℝ] Source →ₗ[ℝ] ℝ)
    (gaugeDirections : Submodule ℝ Source)
    (hLeft : ∀ gauge ∈ gaugeDirections, ∀ direction, hessian gauge direction = 0)
    (hRight : ∀ gauge ∈ gaugeDirections, ∀ direction, hessian direction gauge = 0)
    (first second : Source) :
    quotientHessian hessian gaugeDirections hLeft hRight
        (gaugeDirections.mkQ first) (gaugeDirections.mkQ second) =
      hessian first second := rfl

/-- Symmetry of a Hessian passes to its quotient descent. -/
theorem quotientHessian_symmetric
    (hessian : Source →ₗ[ℝ] Source →ₗ[ℝ] ℝ)
    (gaugeDirections : Submodule ℝ Source)
    (hLeft : ∀ gauge ∈ gaugeDirections, ∀ direction, hessian gauge direction = 0)
    (hRight : ∀ gauge ∈ gaugeDirections, ∀ direction, hessian direction gauge = 0)
    (hSymmetric : ∀ first second, hessian first second = hessian second first)
    (first second : Source ⧸ gaugeDirections) :
    quotientHessian hessian gaugeDirections hLeft hRight first second =
      quotientHessian hessian gaugeDirections hLeft hRight second first := by
  obtain ⟨first, rfl⟩ := gaugeDirections.mkQ_surjective first
  obtain ⟨second, rfl⟩ := gaugeDirections.mkQ_surjective second
  exact hSymmetric first second

/-- The descended Hessian is the unique bilinear form with the prescribed
values on quotient classes. -/
theorem quotientHessian_unique
    (hessian : Source →ₗ[ℝ] Source →ₗ[ℝ] ℝ)
    (gaugeDirections : Submodule ℝ Source)
    (hLeft : ∀ gauge ∈ gaugeDirections, ∀ direction, hessian gauge direction = 0)
    (hRight : ∀ gauge ∈ gaugeDirections, ∀ direction, hessian direction gauge = 0)
    (candidate :
      (Source ⧸ gaugeDirections) →ₗ[ℝ]
        (Source ⧸ gaugeDirections) →ₗ[ℝ] ℝ)
    (hCandidate : ∀ first second,
      candidate (gaugeDirections.mkQ first) (gaugeDirections.mkQ second) =
        hessian first second) :
    candidate = quotientHessian hessian gaugeDirections hLeft hRight := by
  apply LinearMap.ext
  intro first
  obtain ⟨first, rfl⟩ := gaugeDirections.mkQ_surjective first
  apply LinearMap.ext
  intro second
  obtain ⟨second, rfl⟩ := gaugeDirections.mkQ_surjective second
  exact hCandidate first second

/-- The algebraic bilinear form underlying the genuine second Fréchet
derivative of the pullback action at a point. -/
noncomputable def actualPullbackHessianLinear
    (targetAction : Target → ℝ)
    (compatibleMap : Source → Target)
    (x : Source) : Source →ₗ[ℝ] Source →ₗ[ℝ] ℝ :=
  continuousHessianToLinear
    (fderiv ℝ
      (fun y ↦ fderiv ℝ
        (pulledBackAction targetAction compatibleMap) y) x)

omit [NormedAddCommGroup Target] [NormedSpace ℝ Target] in
@[simp]
theorem actualPullbackHessianLinear_apply
    (targetAction : Target → ℝ)
    (compatibleMap : Source → Target)
    (x first second : Source) :
    actualPullbackHessianLinear targetAction compatibleMap x first second =
      fderiv ℝ
        (fun y ↦ fderiv ℝ
          (pulledBackAction targetAction compatibleMap) y) x first second := rfl

/-- At a target critical point, every source submodule contained in the
actual Jacobian kernel is annihilated by the genuine pullback Hessian in both
arguments.  These are precisely the hypotheses needed by `quotientHessian`.
-/
theorem actualPullbackHessianLinear_annihilates_gauge_submodule
    (targetAction : Target → ℝ)
    (compatibleMap : Source → Target)
    (hTarget : Differentiable ℝ targetAction)
    (hMap : Differentiable ℝ compatibleMap)
    (x : Source)
    (secondJet : SourceSecondJet (Source := Source) (Target := Target))
    (targetHessian : TargetHessian (Target := Target))
    (hSecondJet :
      HasFDerivAt (fun y ↦ fderiv ℝ compatibleMap y) secondJet x)
    (hTargetHessian :
      HasFDerivAt (fun z ↦ fderiv ℝ targetAction z)
        targetHessian (compatibleMap x))
    (hCritical : fderiv ℝ targetAction (compatibleMap x) = 0)
    (gaugeDirections : Submodule ℝ Source)
    (hGaugeKernel : ∀ gauge ∈ gaugeDirections,
      (fderiv ℝ compatibleMap x) gauge = 0) :
    (∀ gauge ∈ gaugeDirections, ∀ direction,
      actualPullbackHessianLinear targetAction compatibleMap x
        gauge direction = 0) ∧
    (∀ gauge ∈ gaugeDirections, ∀ direction,
      actualPullbackHessianLinear targetAction compatibleMap x
        direction gauge = 0) := by
  constructor
  · intro gauge hGauge direction
    exact (pulledBackAction_second_fderiv_annihilates_jacobian_kernel
      targetAction compatibleMap hTarget hMap x secondJet targetHessian
      hSecondJet hTargetHessian hCritical gauge direction
      (hGaugeKernel gauge hGauge)).1
  · intro gauge hGauge direction
    exact (pulledBackAction_second_fderiv_annihilates_jacobian_kernel
      targetAction compatibleMap hTarget hMap x secondJet targetHessian
      hSecondJet hTargetHessian hCritical gauge direction
      (hGaugeKernel gauge hGauge)).2

/-- The genuine critical pullback Hessian therefore admits a unique symmetric
bilinear descent to any algebraic gauge quotient contained in the Jacobian
kernel. -/
theorem actualPullbackHessian_descends_to_gauge_quotient
    (targetAction : Target → ℝ)
    (compatibleMap : Source → Target)
    (hTarget : Differentiable ℝ targetAction)
    (hMap : Differentiable ℝ compatibleMap)
    (x : Source)
    (secondJet : SourceSecondJet (Source := Source) (Target := Target))
    (targetHessian : TargetHessian (Target := Target))
    (hSecondJet :
      HasFDerivAt (fun y ↦ fderiv ℝ compatibleMap y) secondJet x)
    (hTargetHessian :
      HasFDerivAt (fun z ↦ fderiv ℝ targetAction z)
        targetHessian (compatibleMap x))
    (hCritical : fderiv ℝ targetAction (compatibleMap x) = 0)
    (gaugeDirections : Submodule ℝ Source)
    (hGaugeKernel : ∀ gauge ∈ gaugeDirections,
      (fderiv ℝ compatibleMap x) gauge = 0) :
    ∃ descended :
        (Source ⧸ gaugeDirections) →ₗ[ℝ]
          (Source ⧸ gaugeDirections) →ₗ[ℝ] ℝ,
      (∀ first second,
        descended (gaugeDirections.mkQ first) (gaugeDirections.mkQ second) =
          actualPullbackHessianLinear targetAction compatibleMap x
            first second) ∧
      (∀ first second, descended first second = descended second first) ∧
      (∀ candidate :
          (Source ⧸ gaugeDirections) →ₗ[ℝ]
            (Source ⧸ gaugeDirections) →ₗ[ℝ] ℝ,
        (∀ first second,
          candidate (gaugeDirections.mkQ first)
              (gaugeDirections.mkQ second) =
            actualPullbackHessianLinear targetAction compatibleMap x
              first second) →
        candidate = descended) := by
  let hessian := actualPullbackHessianLinear targetAction compatibleMap x
  obtain ⟨hLeft, hRight⟩ :=
    actualPullbackHessianLinear_annihilates_gauge_submodule
      targetAction compatibleMap hTarget hMap x secondJet targetHessian
      hSecondJet hTargetHessian hCritical gaugeDirections hGaugeKernel
  let descended := quotientHessian hessian gaugeDirections hLeft hRight
  refine ⟨descended, ?_, ?_, ?_⟩
  · intro first second
    exact quotientHessian_mkQ hessian gaugeDirections hLeft hRight first second
  · have hSymmetric : ∀ first second,
        hessian first second = hessian second first := by
      intro first second
      rw [show hessian first second =
          fderiv ℝ
            (fun y ↦ fderiv ℝ
              (pulledBackAction targetAction compatibleMap) y) x
              first second by rfl]
      rw [show hessian second first =
          fderiv ℝ
            (fun y ↦ fderiv ℝ
              (pulledBackAction targetAction compatibleMap) y) x
              second first by rfl]
      rw [pulledBackAction_second_fderiv_at_critical
        targetAction compatibleMap hTarget hMap x secondJet targetHessian
        hSecondJet hTargetHessian hCritical]
      exact jacobianPullbackHessian_symmetric_at_critical
        targetAction compatibleMap hTarget hMap x secondJet targetHessian
        hSecondJet hTargetHessian hCritical first second
    exact quotientHessian_symmetric hessian gaugeDirections hLeft hRight
      hSymmetric
  · intro candidate hCandidate
    exact quotientHessian_unique hessian gaugeDirections hLeft hRight
      candidate hCandidate

end

end P0EFTJanusFrechetPullbackQuotientHessian
end JanusFormal
