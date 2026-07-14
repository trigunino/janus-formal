import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusNormalConnectionFromFrameJet

namespace JanusFormal
namespace P0EFTJanusNormalFrameConnectionGaugeLaw

set_option autoImplicit false

noncomputable section

open scoped InnerProductSpace
open P0EFTJanusMetricNormalConnectionCurvature
open P0EFTJanusNormalConnectionFromFrameJet

universe u v w

variable {Tangent : Type u} {Normal : Type v} {Ambient : Type w}
variable [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
variable [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
variable [NormedAddCommGroup Ambient] [InnerProductSpace ℝ Ambient]
variable [FiniteDimensional ℝ Tangent]
variable [FiniteDimensional ℝ Normal]

/-- One-jet of a varying orthogonal normal-coordinate change `g`.

The convention below changes a normal frame by

`E' = E ∘ g`.

`derivative x` is `d_x g`. The differentiated orthogonality identity is stored
explicitly. -/
structure OrthogonalNormalGaugeOneJet
    (Tangent : Type u) (Normal : Type v)
    [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
    [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal] where
  value : Normal ≃ₗᵢ[ℝ] Normal
  derivative : Tangent →ₗ[ℝ] Normal →L[ℝ] Normal
  derivative_metric : ∀ x firstNormal secondNormal,
    ⟪derivative x firstNormal, value secondNormal⟫_ℝ +
      ⟪value firstNormal, derivative x secondNormal⟫_ℝ = 0

/-- Conjugation of a normal endomorphism by an orthogonal map. -/
def orthogonalConjugate
    (gauge : Normal ≃ₗᵢ[ℝ] Normal)
    (operator : Normal →L[ℝ] Normal) : Normal →L[ℝ] Normal :=
  gauge.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (operator.comp gauge.toContinuousLinearEquiv.toContinuousLinearMap)

@[simp]
theorem orthogonalConjugate_apply
    (gauge : Normal ≃ₗᵢ[ℝ] Normal)
    (operator : Normal →L[ℝ] Normal)
    (normal : Normal) :
    orthogonalConjugate gauge operator normal =
      gauge.symm (operator (gauge normal)) := by
  rfl

/-- Orthogonal conjugation preserves skew-adjointness. -/
theorem orthogonalConjugate_skew
    (gauge : Normal ≃ₗᵢ[ℝ] Normal)
    {operator : Normal →L[ℝ] Normal}
    (hOperator : IsSkewAdjointOperator operator) :
    IsSkewAdjointOperator (orthogonalConjugate gauge operator) := by
  intro firstNormal secondNormal
  calc
    ⟪orthogonalConjugate gauge operator firstNormal, secondNormal⟫_ℝ =
      ⟪gauge (gauge.symm (operator (gauge firstNormal))),
        gauge secondNormal⟫_ℝ :=
      (gauge.inner_map_map _ _).symm
    _ = ⟪operator (gauge firstNormal), gauge secondNormal⟫_ℝ := by
      rw [gauge.apply_symm_apply]
    _ = -⟪gauge firstNormal, operator (gauge secondNormal)⟫_ℝ :=
      hOperator (gauge firstNormal) (gauge secondNormal)
    _ = -⟪gauge firstNormal,
        gauge (gauge.symm (operator (gauge secondNormal)))⟫_ℝ := by
      rw [gauge.apply_symm_apply]
    _ = -⟪firstNormal,
        orthogonalConjugate gauge operator secondNormal⟫_ℝ := by
      rw [gauge.inner_map_map]
      rfl

/-- Left Maurer--Cartan coefficient `g⁻¹ dg` in the convention `E' = E ∘ g`. -/
def gaugeLogDerivative
    (gauge : OrthogonalNormalGaugeOneJet Tangent Normal)
    (x : Tangent) : Normal →L[ℝ] Normal :=
  gauge.value.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (gauge.derivative x)

@[simp]
theorem gaugeLogDerivative_apply
    (gauge : OrthogonalNormalGaugeOneJet Tangent Normal)
    (x : Tangent) (normal : Normal) :
    gaugeLogDerivative gauge x normal =
      gauge.value.symm (gauge.derivative x normal) := by
  rfl

/-- The differentiated orthogonality relation makes `g⁻¹ dg` skew-adjoint. -/
theorem gaugeLogDerivative_skew
    (gauge : OrthogonalNormalGaugeOneJet Tangent Normal)
    (x : Tangent) :
    IsSkewAdjointOperator (gaugeLogDerivative gauge x) := by
  intro firstNormal secondNormal
  calc
    ⟪gaugeLogDerivative gauge x firstNormal, secondNormal⟫_ℝ =
      ⟪gauge.value (gauge.value.symm
          (gauge.derivative x firstNormal)),
        gauge.value secondNormal⟫_ℝ :=
      (gauge.value.inner_map_map _ _).symm
    _ = ⟪gauge.derivative x firstNormal,
        gauge.value secondNormal⟫_ℝ := by
      rw [gauge.value.apply_symm_apply]
    _ = -⟪gauge.value firstNormal,
        gauge.derivative x secondNormal⟫_ℝ := by
      linarith [gauge.derivative_metric x firstNormal secondNormal]
    _ = -⟪gauge.value firstNormal,
        gauge.value (gauge.value.symm
          (gauge.derivative x secondNormal))⟫_ℝ := by
      rw [gauge.value.apply_symm_apply]
    _ = -⟪firstNormal, gaugeLogDerivative gauge x secondNormal⟫_ℝ := by
      rw [gauge.value.inner_map_map]
      rfl

/-- Zeroth-order frame after `E' = E ∘ g`. -/
def gaugeChangedFrameValue
    (frame : OrthonormalNormalFrameTwoJet Tangent Normal Ambient)
    (gauge : OrthogonalNormalGaugeOneJet Tangent Normal) :
    Normal →ₗᵢ[ℝ] Ambient :=
  frame.value.comp gauge.value.toLinearIsometry

@[simp]
theorem gaugeChangedFrameValue_apply
    (frame : OrthonormalNormalFrameTwoJet Tangent Normal Ambient)
    (gauge : OrthogonalNormalGaugeOneJet Tangent Normal)
    (normal : Normal) :
    gaugeChangedFrameValue frame gauge normal =
      frame.value (gauge.value normal) := by
  rfl

/-- First derivative of the changed frame. -/
def gaugeChangedFrameFirst
    (frame : OrthonormalNormalFrameTwoJet Tangent Normal Ambient)
    (gauge : OrthogonalNormalGaugeOneJet Tangent Normal)
    (x : Tangent) : Normal →L[ℝ] Ambient :=
  (frame.first x).comp
      gauge.value.toContinuousLinearEquiv.toContinuousLinearMap +
    frame.value.toContinuousLinearMap.comp (gauge.derivative x)

@[simp]
theorem gaugeChangedFrameFirst_apply
    (frame : OrthonormalNormalFrameTwoJet Tangent Normal Ambient)
    (gauge : OrthogonalNormalGaugeOneJet Tangent Normal)
    (x : Tangent) (normal : Normal) :
    gaugeChangedFrameFirst frame gauge x normal =
      frame.first x (gauge.value normal) +
        frame.value (gauge.derivative x normal) := by
  rfl

/-- The changed frame remains orthonormal to first order. -/
theorem gaugeChangedFrame_first_metric
    (frame : OrthonormalNormalFrameTwoJet Tangent Normal Ambient)
    (gauge : OrthogonalNormalGaugeOneJet Tangent Normal)
    (x : Tangent) (firstNormal secondNormal : Normal) :
    ⟪gaugeChangedFrameFirst frame gauge x firstNormal,
        gaugeChangedFrameValue frame gauge secondNormal⟫_ℝ +
      ⟪gaugeChangedFrameValue frame gauge firstNormal,
        gaugeChangedFrameFirst frame gauge x secondNormal⟫_ℝ = 0 := by
  simp only [gaugeChangedFrameFirst_apply, gaugeChangedFrameValue_apply,
    inner_add_left, inner_add_right]
  rw [frame.value.inner_map_map, frame.value.inner_map_map]
  linarith [frame.first_metric x (gauge.value firstNormal)
      (gauge.value secondNormal),
    gauge.derivative_metric x firstNormal secondNormal]

/-- Bilinear form defining the connection coefficient of the changed frame. -/
def gaugeChangedFrameCoefficientBilinearLinear
    (frame : OrthonormalNormalFrameTwoJet Tangent Normal Ambient)
    (gauge : OrthogonalNormalGaugeOneJet Tangent Normal)
    (x : Tangent) : Normal →ₗ[ℝ] Normal →ₗ[ℝ] ℝ where
  toFun := fun firstNormal =>
    { toFun := fun secondNormal =>
        ⟪gaugeChangedFrameFirst frame gauge x firstNormal,
          gaugeChangedFrameValue frame gauge secondNormal⟫_ℝ
      map_add' := by
        intro first second
        rw [map_add, inner_add_right]
      map_smul' := by
        intro scalar normal
        rw [map_smul, inner_smul_right]
        rfl }
  map_add' := by
    intro first second
    apply LinearMap.ext
    intro normal
    change
      ⟪gaugeChangedFrameFirst frame gauge x (first + second),
        gaugeChangedFrameValue frame gauge normal⟫_ℝ =
      ⟪gaugeChangedFrameFirst frame gauge x first,
        gaugeChangedFrameValue frame gauge normal⟫_ℝ +
      ⟪gaugeChangedFrameFirst frame gauge x second,
        gaugeChangedFrameValue frame gauge normal⟫_ℝ
    rw [map_add, inner_add_left]
  map_smul' := by
    intro scalar normal
    apply LinearMap.ext
    intro secondNormal
    change
      ⟪gaugeChangedFrameFirst frame gauge x (scalar • normal),
        gaugeChangedFrameValue frame gauge secondNormal⟫_ℝ =
      scalar *
        ⟪gaugeChangedFrameFirst frame gauge x normal,
          gaugeChangedFrameValue frame gauge secondNormal⟫_ℝ
    rw [map_smul, inner_smul_left]
    rfl

/-- Continuous changed-frame coefficient form. -/
def gaugeChangedFrameCoefficientBilinear
    (frame : OrthonormalNormalFrameTwoJet Tangent Normal Ambient)
    (gauge : OrthogonalNormalGaugeOneJet Tangent Normal)
    (x : Tangent) : Normal →L[ℝ] Normal →L[ℝ] ℝ :=
  LinearMap.toContinuousBilinearMap
    (gaugeChangedFrameCoefficientBilinearLinear frame gauge x)

/-- Connection coefficient extracted from the changed frame. -/
def gaugeChangedFrameConnectionCoefficient
    (frame : OrthonormalNormalFrameTwoJet Tangent Normal Ambient)
    (gauge : OrthogonalNormalGaugeOneJet Tangent Normal)
    (x : Tangent) : Normal →L[ℝ] Normal :=
  InnerProductSpace.continuousLinearMapOfBilin
    (gaugeChangedFrameCoefficientBilinear frame gauge x)

@[simp]
theorem gaugeChangedFrameConnectionCoefficient_inner
    (frame : OrthonormalNormalFrameTwoJet Tangent Normal Ambient)
    (gauge : OrthogonalNormalGaugeOneJet Tangent Normal)
    (x : Tangent) (firstNormal secondNormal : Normal) :
    ⟪gaugeChangedFrameConnectionCoefficient frame gauge x firstNormal,
      secondNormal⟫_ℝ =
      ⟪gaugeChangedFrameFirst frame gauge x firstNormal,
        gaugeChangedFrameValue frame gauge secondNormal⟫_ℝ := by
  change
    ⟪InnerProductSpace.continuousLinearMapOfBilin
        (gaugeChangedFrameCoefficientBilinear frame gauge x) firstNormal,
      secondNormal⟫_ℝ = _
  rw [InnerProductSpace.continuousLinearMapOfBilin_apply]
  rfl

/-- Main local frame-gauge law in the convention `E' = E ∘ g`:

`omega' = g⁻¹ omega g + g⁻¹ dg`. -/
theorem gaugeChangedFrame_connection_law
    (frame : OrthonormalNormalFrameTwoJet Tangent Normal Ambient)
    (gauge : OrthogonalNormalGaugeOneJet Tangent Normal)
    (x : Tangent) :
    gaugeChangedFrameConnectionCoefficient frame gauge x =
      orthogonalConjugate gauge.value
          (frameNormalConnectionCoefficient frame x) +
        gaugeLogDerivative gauge x := by
  apply ContinuousLinearMap.ext
  intro firstNormal
  apply ext_inner_right ℝ
  intro secondNormal
  rw [gaugeChangedFrameConnectionCoefficient_inner]
  change
    ⟪frame.first x (gauge.value firstNormal) +
        frame.value (gauge.derivative x firstNormal),
      frame.value (gauge.value secondNormal)⟫_ℝ =
      ⟪gauge.value.symm
          (frameNormalConnectionCoefficient frame x
            (gauge.value firstNormal)) +
        gauge.value.symm (gauge.derivative x firstNormal),
        secondNormal⟫_ℝ
  rw [inner_add_left, inner_add_left,
    ← frameNormalConnectionCoefficient_inner frame x
      (gauge.value firstNormal) (gauge.value secondNormal),
    frame.value.inner_map_map]
  have hFirst :
      ⟪gauge.value.symm
          (frameNormalConnectionCoefficient frame x
            (gauge.value firstNormal)), secondNormal⟫_ℝ =
        ⟪frameNormalConnectionCoefficient frame x
            (gauge.value firstNormal), gauge.value secondNormal⟫_ℝ := by
    calc
      _ = ⟪gauge.value
          (gauge.value.symm
            (frameNormalConnectionCoefficient frame x
              (gauge.value firstNormal))),
          gauge.value secondNormal⟫_ℝ :=
        (gauge.value.inner_map_map _ _).symm
      _ = _ := by rw [gauge.value.apply_symm_apply]
  have hSecond :
      ⟪gauge.value.symm (gauge.derivative x firstNormal),
          secondNormal⟫_ℝ =
        ⟪gauge.derivative x firstNormal,
          gauge.value secondNormal⟫_ℝ := by
    calc
      _ = ⟪gauge.value
          (gauge.value.symm (gauge.derivative x firstNormal)),
          gauge.value secondNormal⟫_ℝ :=
        (gauge.value.inner_map_map _ _).symm
      _ = _ := by rw [gauge.value.apply_symm_apply]
  rw [hFirst, hSecond]

/-- The transformed coefficient is automatically skew-adjoint. -/
theorem gaugeChangedFrameConnectionCoefficient_skew
    (frame : OrthonormalNormalFrameTwoJet Tangent Normal Ambient)
    (gauge : OrthogonalNormalGaugeOneJet Tangent Normal)
    (x : Tangent) :
    IsSkewAdjointOperator
      (gaugeChangedFrameConnectionCoefficient frame gauge x) := by
  rw [gaugeChangedFrame_connection_law]
  exact skewAdjoint_add
    (orthogonalConjugate_skew gauge.value
      (frameNormalConnectionCoefficient_skew frame x))
    (gaugeLogDerivative_skew gauge x)

/-- Exact boundary of the local coefficient gauge law. -/
structure NormalFrameConnectionGaugeLawStatus where
  orthogonalGaugeOneJetDefined : Prop
  logarithmicDerivativeConstructed : Prop
  logarithmicDerivativeSkewProved : Prop
  changedFrameFirstJetConstructed : Prop
  changedFrameMetricIdentityProved : Prop
  connectionCoefficientGaugeLawProved : Prop
  curvatureGaugeLawProved : Prop
  smoothGaugeFieldInserted : Prop
  secondGaugeJetInserted : Prop
  manifoldOverlapConnectionLawProved : Prop
  globalNormalBundleConnectionConstructed : Prop

/-- Closure of the manifold-level gauge stage. -/
def normalFrameConnectionGaugeLawClosed
    (s : NormalFrameConnectionGaugeLawStatus) : Prop :=
  s.orthogonalGaugeOneJetDefined /\
  s.logarithmicDerivativeConstructed /\
  s.logarithmicDerivativeSkewProved /\
  s.changedFrameFirstJetConstructed /\
  s.changedFrameMetricIdentityProved /\
  s.connectionCoefficientGaugeLawProved /\
  s.curvatureGaugeLawProved /\
  s.smoothGaugeFieldInserted /\
  s.secondGaugeJetInserted /\
  s.manifoldOverlapConnectionLawProved /\
  s.globalNormalBundleConnectionConstructed

/-- The coefficient law alone does not yet imply the curvature law without the
second jet/Maurer--Cartan identity of the gauge field. -/
theorem missing_second_gauge_jet_blocks_curvature_law
    (s : NormalFrameConnectionGaugeLawStatus)
    (hMissing : Not s.secondGaugeJetInserted) :
    Not (normalFrameConnectionGaugeLawClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.2.2.1

end

end P0EFTJanusNormalFrameConnectionGaugeLaw
end JanusFormal
