import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteGramInducedMetricFrechetBridge

/-!
# Finite first-jet compatibility naturality

This gate treats a Euclidean immersion one-jet `F` as the independent datum.
The concrete compatibility operator is

`K(F)(u,v) = ⟪F u, F v⟫`,

and its actual Fréchet linearization is

`J_F(H)(u,v) = ⟪H u, F v⟫ + ⟪F u, H v⟫`.

We prove naturality under arbitrary continuous source-frame changes and under
ambient linear isometries, together with the corresponding transformation
laws for `J`.  Ambient infinitesimal isometries give explicit directions in
`ker J_F`.

The scope is deliberately pointwise and first-jet finite-dimensional-style.
It does not construct a differential compatibility complex, a Lorentzian
symbol, or a global PDE operator.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteJetCompatibilityNaturality

set_option autoImplicit false

noncomputable section

open scoped InnerProductSpace
open P0EFTJanusFiniteGramInducedMetricFrechetBridge

universe u v

variable {Tangent : Type u} {Ambient : Type v}
variable [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
variable [NormedAddCommGroup Ambient] [InnerProductSpace ℝ Ambient]

/-- Concrete first-jet compatibility operator `K : F ↦ F*⟪·,·⟫`. -/
def finiteJetCompatibilityOperator
    (F : ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient)) :
    GramMetricTensor (Tangent := Tangent) :=
  inducedGramMetric F

/-- Concrete linearization `J_F = D K|_F`. -/
def finiteJetCompatibilityLinearization
    (F : ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient)) :
    ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient) →L[ℝ]
      GramMetricTensor (Tangent := Tangent) :=
  inducedGramDerivative F

@[simp]
theorem finiteJetCompatibilityOperator_apply
    (F : ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient))
    (x y : Tangent) :
    finiteJetCompatibilityOperator F x y = ⟪F x, F y⟫_ℝ := by
  rfl

@[simp]
theorem finiteJetCompatibilityLinearization_apply
    (F H : ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient))
    (x y : Tangent) :
    finiteJetCompatibilityLinearization F H x y =
      ⟪H x, F y⟫_ℝ + ⟪F x, H y⟫_ℝ := by
  exact inducedGramDerivative_apply F H x y

/-- `J_F` is the actual Fréchet derivative of the displayed `K`. -/
theorem finiteJetCompatibilityOperator_hasFDerivAt
    (F : ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient)) :
    HasFDerivAt finiteJetCompatibilityOperator
      (finiteJetCompatibilityLinearization F) F := by
  exact inducedGramMetric_hasFDerivAt F

theorem finiteJetCompatibilityOperator_fderiv
    (F : ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient)) :
    fderiv ℝ finiteJetCompatibilityOperator F =
      finiteJetCompatibilityLinearization F :=
  (finiteJetCompatibilityOperator_hasFDerivAt F).fderiv

/-- Right action of a source-frame change on an immersion one-jet. -/
def sourceFrameAction
    (frame : Tangent ≃L[ℝ] Tangent)
    (F : ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient)) :
    ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient) :=
  F.comp frame.toContinuousLinearMap

/-- Pullback action of a source-frame change on a covariant two-tensor. -/
def sourceTensorPullback
    (frame : Tangent ≃L[ℝ] Tangent)
    (metric : GramMetricTensor (Tangent := Tangent)) :
    GramMetricTensor (Tangent := Tangent) :=
  metric.bilinearComp frame.toContinuousLinearMap frame.toContinuousLinearMap

@[simp]
theorem sourceFrameAction_apply
    (frame : Tangent ≃L[ℝ] Tangent)
    (F : ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient))
    (x : Tangent) :
    sourceFrameAction frame F x = F (frame x) := by
  rfl

@[simp]
theorem sourceTensorPullback_apply
    (frame : Tangent ≃L[ℝ] Tangent)
    (metric : GramMetricTensor (Tangent := Tangent))
    (x y : Tangent) :
    sourceTensorPullback frame metric x y = metric (frame x) (frame y) := by
  rfl

/-- Naturality of `K` under an arbitrary invertible source-frame change. -/
theorem finiteJetCompatibilityOperator_source_natural
    (frame : Tangent ≃L[ℝ] Tangent)
    (F : ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient)) :
    finiteJetCompatibilityOperator (sourceFrameAction frame F) =
      sourceTensorPullback frame (finiteJetCompatibilityOperator F) := by
  ext x y
  rfl

/-- The actual `J` intertwines the source action with tensor pullback. -/
theorem finiteJetCompatibilityLinearization_source_intertwines
    (frame : Tangent ≃L[ℝ] Tangent)
    (F H : ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient)) :
    finiteJetCompatibilityLinearization (sourceFrameAction frame F)
        (sourceFrameAction frame H) =
      sourceTensorPullback frame (finiteJetCompatibilityLinearization F H) := by
  ext x y
  rfl

/-- Left action of an ambient linear isometry on an immersion one-jet. -/
def ambientIsometryAction
    (ambientFrame : Ambient ≃ₗᵢ[ℝ] Ambient)
    (F : ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient)) :
    ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient) :=
  ambientFrame.toContinuousLinearEquiv.toContinuousLinearMap.comp F

@[simp]
theorem ambientIsometryAction_apply
    (ambientFrame : Ambient ≃ₗᵢ[ℝ] Ambient)
    (F : ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient))
    (x : Tangent) :
    ambientIsometryAction ambientFrame F x = ambientFrame (F x) := by
  rfl

/-- Ambient isometries leave `K` invariant. -/
theorem finiteJetCompatibilityOperator_ambient_invariant
    (ambientFrame : Ambient ≃ₗᵢ[ℝ] Ambient)
    (F : ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient)) :
    finiteJetCompatibilityOperator (ambientIsometryAction ambientFrame F) =
      finiteJetCompatibilityOperator F := by
  ext x y
  exact ambientFrame.inner_map_map (F x) (F y)

/-- Simultaneously transforming the base jet and variation leaves `J`
unchanged under an ambient isometry. -/
theorem finiteJetCompatibilityLinearization_ambient_intertwines
    (ambientFrame : Ambient ≃ₗᵢ[ℝ] Ambient)
    (F H : ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient)) :
    finiteJetCompatibilityLinearization (ambientIsometryAction ambientFrame F)
        (ambientIsometryAction ambientFrame H) =
      finiteJetCompatibilityLinearization F H := by
  ext x y
  simp only [finiteJetCompatibilityLinearization_apply,
    ambientIsometryAction_apply, ambientFrame.inner_map_map]

/-- Pointwise Lie-algebra condition for an ambient infinitesimal isometry. -/
def AmbientInfinitesimalIsometry
    (generator : Ambient →L[ℝ] Ambient) : Prop :=
  ∀ x y, ⟪generator x, y⟫_ℝ + ⟪x, generator y⟫_ℝ = 0

/-- Infinitesimal ambient action on an immersion one-jet. -/
def ambientInfinitesimalDirection
    (generator : Ambient →L[ℝ] Ambient)
    (F : ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient)) :
    ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient) :=
  generator.comp F

@[simp]
theorem ambientInfinitesimalDirection_apply
    (generator : Ambient →L[ℝ] Ambient)
    (F : ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient))
    (x : Tangent) :
    ambientInfinitesimalDirection generator F x = generator (F x) := by
  rfl

/-- Every ambient infinitesimal isometry is killed by the concrete `J_F`. -/
theorem finiteJetCompatibilityLinearization_ambientInfinitesimal_eq_zero
    (generator : Ambient →L[ℝ] Ambient)
    (hGenerator : AmbientInfinitesimalIsometry generator)
    (F : ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient)) :
    finiteJetCompatibilityLinearization F
        (ambientInfinitesimalDirection generator F) = 0 := by
  ext x y
  simpa only [finiteJetCompatibilityLinearization_apply,
    ambientInfinitesimalDirection_apply, zero_apply] using
    hGenerator (F x) (F y)

/-- Kernel formulation of ambient infinitesimal gauge directions. -/
theorem ambientInfinitesimalDirection_mem_ker
    (generator : Ambient →L[ℝ] Ambient)
    (hGenerator : AmbientInfinitesimalIsometry generator)
    (F : ImmersionOneJet (Tangent := Tangent) (Ambient := Ambient)) :
    ambientInfinitesimalDirection generator F ∈
      LinearMap.ker (finiteJetCompatibilityLinearization F).toLinearMap := by
  rw [LinearMap.mem_ker]
  exact finiteJetCompatibilityLinearization_ambientInfinitesimal_eq_zero
    generator hGenerator F

end

end P0EFTJanusFiniteJetCompatibilityNaturality
end JanusFormal
