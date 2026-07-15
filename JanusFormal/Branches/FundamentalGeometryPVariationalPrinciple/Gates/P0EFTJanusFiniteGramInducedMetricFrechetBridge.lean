import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Operator.NormedSpace
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusInducedFieldVariationNoDoubleCounting

/-!
# Finite Euclidean induced-metric Fréchet bridge

For a real Hilbert-space linear one-jet
`F : Tangent →L[ℝ] Ambient`, this file constructs the Gram tensor

`g_F(u,v) = ⟪F u, F v⟫_ℝ`

as an actual map between normed spaces.  It computes its first and second
Fréchet derivatives, packages the graph compatibility map `K(F) = (F,g_F)`
and its Jacobian, and instantiates the existing induced-field chain rule.

It is positive definite only on the explicitly injective immersion domain.
This fixed finite-dimensional Euclidean model does not construct a Lorentzian
metric, a GHY/null/corner functional, or a global Janus boundary problem.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteGramInducedMetricFrechetBridge

set_option autoImplicit false

noncomputable section

open scoped InnerProductSpace
open P0EFTJanusFrechetPullbackSecondVariation
open P0EFTJanusInducedFieldVariationNoDoubleCounting

universe u v

variable {Tangent : Type u} {Ambient : Type v}
variable [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
variable [NormedAddCommGroup Ambient] [InnerProductSpace ℝ Ambient]

/-- Ambient vector space of finite Euclidean linear one-jets.  Injectivity is
an admissibility condition, not part of this vector-space type. -/
abbrev ImmersionOneJet := Tangent →L[ℝ] Ambient

def ImmersionAdmissible
    (F : ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient)) : Prop :=
  Function.Injective F

/-- Continuous covariant two-tensors on the tangent model. -/
abbrev GramMetricTensor := Tangent →L[ℝ] Tangent →L[ℝ] ℝ

local instance immersionOneJetNormedAddCommGroup :
    NormedAddCommGroup
      (ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient)) :=
  inferInstance

local instance immersionOneJetNormedSpace :
    NormedSpace ℝ
      (ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient)) :=
  inferInstance

local instance gramMetricTensorNormedAddCommGroup :
    NormedAddCommGroup (GramMetricTensor (Tangent := Tangent)) :=
  inferInstance

local instance gramMetricTensorNormedSpace :
    NormedSpace ℝ (GramMetricTensor (Tangent := Tangent)) :=
  inferInstance

local instance immersionOneJetTopologicalSpace :
    TopologicalSpace
      (ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient)) :=
  immersionOneJetNormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

local instance immersionOneJetAddCommGroup :
    AddCommGroup
      (ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient)) :=
  immersionOneJetNormedAddCommGroup.toAddCommGroup

local instance immersionOneJetModule :
    Module ℝ (ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient)) :=
  immersionOneJetNormedSpace.toModule

local instance gramMetricTensorTopologicalSpace :
    TopologicalSpace (GramMetricTensor (Tangent := Tangent)) :=
  gramMetricTensorNormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

local instance gramMetricTensorAddCommGroup :
    AddCommGroup (GramMetricTensor (Tangent := Tangent)) :=
  gramMetricTensorNormedAddCommGroup.toAddCommGroup

local instance gramMetricTensorModule :
    Module ℝ (GramMetricTensor (Tangent := Tangent)) :=
  gramMetricTensorNormedSpace.toModule

local instance gramMetricDerivativeNormedAddCommGroup :
    NormedAddCommGroup
      (ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient) →L[ℝ]
        GramMetricTensor (Tangent := Tangent)) :=
  inferInstance

local instance gramMetricDerivativeNormedSpace :
    NormedSpace ℝ
      (ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient) →L[ℝ]
        GramMetricTensor (Tangent := Tangent)) :=
  inferInstance

local instance gramMetricDerivativeTopologicalSpace :
    TopologicalSpace
      (ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient) →L[ℝ]
        GramMetricTensor (Tangent := Tangent)) :=
  gramMetricDerivativeNormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

local instance gramMetricDerivativeAddCommGroup :
    AddCommGroup
      (ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient) →L[ℝ]
        GramMetricTensor (Tangent := Tangent)) :=
  gramMetricDerivativeNormedAddCommGroup.toAddCommGroup

local instance gramMetricDerivativeModule :
    Module ℝ
      (ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient) →L[ℝ]
        GramMetricTensor (Tangent := Tangent)) :=
  gramMetricDerivativeNormedSpace.toModule

/-- Continuous bilinear Gram pairing `(F,G) ↦ ((u,v) ↦ ⟪F u,G v⟫)`. -/
def gramBilinear :
    ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient) →L[ℝ]
      ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient) →L[ℝ]
        GramMetricTensor (Tangent := Tangent) :=
  let raw :
      ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient) →ₗ[ℝ]
        ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient) →ₗ[ℝ]
          GramMetricTensor (Tangent := Tangent) :=
    LinearMap.mk₂ ℝ
      (fun first second => (innerSL ℝ).bilinearComp first second)
      (fun first second third => by
        apply ContinuousLinearMap.ext
        intro u
        apply ContinuousLinearMap.ext
        intro v
        exact inner_add_left _ _ _)
      (fun scalar first second => by
        apply ContinuousLinearMap.ext
        intro u
        apply ContinuousLinearMap.ext
        intro v
        simp [smul_eq_mul])
      (fun first second third => by
        apply ContinuousLinearMap.ext
        intro u
        apply ContinuousLinearMap.ext
        intro v
        exact inner_add_right _ _ _)
      (fun scalar first second => by
        apply ContinuousLinearMap.ext
        intro u
        apply ContinuousLinearMap.ext
        intro v
        simp [smul_eq_mul])
  raw.mkContinuous₂ 1 (fun first second => by
    rw [one_mul]
    refine ContinuousLinearMap.opNorm_le_bound₂ _
      (mul_nonneg (norm_nonneg first) (norm_nonneg second)) ?_
    intro u v
    change ‖⟪first u, second v⟫_ℝ‖ ≤
      (‖first‖ * ‖second‖) * ‖u‖ * ‖v‖
    calc
      ‖⟪first u, second v⟫_ℝ‖ ≤ ‖first u‖ * ‖second v‖ :=
        norm_inner_le_norm _ _
      _ ≤ (‖first‖ * ‖u‖) * (‖second‖ * ‖v‖) := by
        exact mul_le_mul (first.le_opNorm u) (second.le_opNorm v)
          (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = (‖first‖ * ‖second‖) * ‖u‖ * ‖v‖ := by ring)

@[simp]
theorem gramBilinear_apply
    (first second : ImmersionOneJet (Tangent := Tangent)
      (Ambient := Ambient))
    (u v : Tangent) :
    gramBilinear first second u v = ⟪first u, second v⟫_ℝ := by
  rfl

/-- The Gram tensor induced by the Euclidean linear one-jet. It is a metric on
the injective domain characterized below. -/
def inducedGramMetric
    (F : ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient)) :
    GramMetricTensor (Tangent := Tangent) :=
  gramBilinear F F

@[simp]
theorem inducedGramMetric_apply
    (F : ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient))
    (u v : Tangent) :
    inducedGramMetric F u v = ⟪F u, F v⟫_ℝ := by
  rfl

/-- On the genuine immersion domain the Gram tensor is positive definite. -/
theorem inducedGramMetric_pos_of_admissible
    (F : ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient))
    (hAdmissible : ImmersionAdmissible F)
    (u : Tangent) (hNonzero : u ≠ 0) :
    0 < inducedGramMetric F u u := by
  rw [inducedGramMetric_apply]
  apply (real_inner_self_pos).2
  intro hZero
  apply hNonzero
  apply hAdmissible
  simpa using hZero

/-- Constant second derivative of the quadratic Gram map. -/
def inducedGramSecondDerivative :
    ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient) →L[ℝ]
      ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient) →L[ℝ]
        GramMetricTensor (Tangent := Tangent) :=
  gramBilinear +
    gramBilinear.precompL
      (ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient))
      (ContinuousLinearMap.id ℝ
        (ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient)))

/-- First derivative of the Gram map at `F`. -/
def inducedGramDerivative
    (F : ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient)) :
    ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient) →L[ℝ]
      GramMetricTensor (Tangent := Tangent) :=
  inducedGramSecondDerivative F

@[simp]
theorem inducedGramDerivative_apply
    (F H : ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient))
    (u v : Tangent) :
    inducedGramDerivative F H u v =
      ⟪H u, F v⟫_ℝ + ⟪F u, H v⟫_ℝ := by
  simp [inducedGramDerivative, inducedGramSecondDerivative, add_comm]

@[simp]
theorem inducedGramSecondDerivative_apply
    (H K : ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient))
    (u v : Tangent) :
    inducedGramSecondDerivative H K u v =
      ⟪H u, K v⟫_ℝ + ⟪K u, H v⟫_ℝ := by
  rfl

/-- Genuine first Fréchet derivative of `F ↦ F*F`. -/
theorem inducedGramMetric_hasFDerivAt
    (F : ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient)) :
    HasFDerivAt inducedGramMetric (inducedGramDerivative F) F := by
  change @HasFDerivAt ℝ _
    (ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient))
    immersionOneJetNormedAddCommGroup.toAddCommGroup
    immersionOneJetNormedSpace.toModule
    immersionOneJetNormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    (GramMetricTensor (Tangent := Tangent))
    gramMetricTensorNormedAddCommGroup.toAddCommGroup
    gramMetricTensorNormedSpace.toModule
    gramMetricTensorNormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    (fun varied => gramBilinear varied varied) (inducedGramDerivative F) F
  have h := (gramBilinear
    (Tangent := Tangent) (Ambient := Ambient)).hasFDerivAt_of_bilinear
      (hasFDerivAt_id F) (hasFDerivAt_id F)
  simpa [inducedGramDerivative, inducedGramSecondDerivative] using h

/-- Exact actual derivative of the Gram map. -/
theorem inducedGramMetric_fderiv
    (F : ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient)) :
    fderiv ℝ inducedGramMetric F = inducedGramDerivative F :=
  (inducedGramMetric_hasFDerivAt F).fderiv

/-- The first derivative varies linearly with constant derivative `D²g`. -/
theorem inducedGramDerivative_hasFDerivAt
    (F : ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient)) :
    HasFDerivAt inducedGramDerivative inducedGramSecondDerivative F := by
  exact (inducedGramSecondDerivative
    (Tangent := Tangent) (Ambient := Ambient)).hasFDerivAt

/-- Genuine second Fréchet derivative of the induced Gram metric. -/
theorem inducedGramMetric_second_fderiv
    (F : ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient)) :
    fderiv ℝ (fun G => fderiv ℝ inducedGramMetric G) F =
      inducedGramSecondDerivative := by
  have hFunction :
      (fun G : ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient) =>
        fderiv ℝ inducedGramMetric G) = inducedGramDerivative := by
    funext G
    exact inducedGramMetric_fderiv G
  rw [hFunction]
  exact (inducedGramDerivative_hasFDerivAt F).fderiv

/-- Symmetry of the actual Gram second jet in its two variation slots. -/
theorem inducedGramSecondDerivative_symmetric
    (H K : ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient)) :
    inducedGramSecondDerivative H K = inducedGramSecondDerivative K H := by
  ext u v
  simp [inducedGramSecondDerivative_apply, add_comm]

/-- Concrete compatibility map `K(F) = (F,g_F)`. -/
def gramCompatibilityMap
    (F : ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient)) :
    ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient) ×
      GramMetricTensor (Tangent := Tangent) :=
  inducedGraph inducedGramMetric F

/-- Concrete Jacobian `J_F(H) = (H,Dg_F(H))`. -/
def gramJacobian
    (F : ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient)) :
    ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient) →L[ℝ]
      (ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient) ×
        GramMetricTensor (Tangent := Tangent)) :=
  inducedGraphDerivative (inducedGramDerivative F)

@[simp]
theorem gramCompatibilityMap_apply
    (F : ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient)) :
    gramCompatibilityMap F = (F, inducedGramMetric F) := by
  rfl

@[simp]
theorem gramJacobian_apply
    (F H : ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient)) :
    gramJacobian F H = (H, inducedGramDerivative F H) := by
  rfl

/-- The displayed `J_F` is the genuine derivative of the concrete `K`. -/
theorem gramCompatibilityMap_hasFDerivAt
    (F : ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient)) :
    HasFDerivAt gramCompatibilityMap (gramJacobian F) F := by
  exact (hasFDerivAt_id F).prodMk (inducedGramMetric_hasFDerivAt F)

/-- Actual Jacobian of the concrete compatibility map. -/
theorem gramCompatibilityMap_fderiv
    (F : ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient)) :
    fderiv ℝ gramCompatibilityMap F = gramJacobian F :=
  (gramCompatibilityMap_hasFDerivAt F).fderiv

/-- The existing induced-field chain rule instantiated by the actual Gram map. -/
theorem gramRestrictedAction_hasFDerivAt
    (jointAction :
      (ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient) ×
        GramMetricTensor (Tangent := Tangent)) → ℝ)
    (F : ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient))
    (jointEuler :
      (ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient) ×
        GramMetricTensor (Tangent := Tangent)) →L[ℝ] ℝ)
    (hAction : HasFDerivAt jointAction jointEuler (gramCompatibilityMap F)) :
    HasFDerivAt (fun varied => jointAction (gramCompatibilityMap varied))
      (constrainedEuler jointEuler (inducedGramDerivative F)) F := by
  exact inducedAction_hasFDerivAt jointAction inducedGramMetric F jointEuler
    (inducedGramDerivative F) hAction (inducedGramMetric_hasFDerivAt F)

/-- The generic pullback chain rule also specializes to the concrete `K` and
`J`, without treating the induced metric as an independent field. -/
theorem gramPulledBackAction_hasFDerivAt
    (targetAction :
      (ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient) ×
        GramMetricTensor (Tangent := Tangent)) → ℝ)
    (F : ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient))
    (targetGradient :
      (ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient) ×
        GramMetricTensor (Tangent := Tangent)) →L[ℝ] ℝ)
    (hTarget : HasFDerivAt targetAction targetGradient
      (gramCompatibilityMap F)) :
    HasFDerivAt (pulledBackAction targetAction gramCompatibilityMap)
      (targetGradient.comp (gramJacobian F)) F := by
  exact pulledBackAction_hasFDerivAt targetAction gramCompatibilityMap F
    targetGradient (gramJacobian F) hTarget
    (gramCompatibilityMap_hasFDerivAt F)

end

end P0EFTJanusFiniteGramInducedMetricFrechetBridge
end JanusFormal
