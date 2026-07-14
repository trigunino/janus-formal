import Mathlib
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusRieszShapeOperatorSmoothReducedJetBase

namespace JanusFormal
namespace P0EFTJanusRieszShapeOperatorContinuousStructuredJetReduction

set_option autoImplicit false

noncomputable section

open Module
open scoped ContDiff InnerProductSpace
open P0EFTJanusLowOrderStructuredBackground
open P0EFTJanusRieszShapeOperatorSmoothReducedJetBase

universe u v

abbrev ContinuousTangentialQuadratic
    (Tangent : Type u) [NormedAddCommGroup Tangent] [NormedSpace ℝ Tangent] :=
  Tangent →L[ℝ] Tangent →L[ℝ] Tangent

abbrev ContinuousConnectionValue
    (Tangent : Type u) [NormedAddCommGroup Tangent] [NormedSpace ℝ Tangent] :=
  Tangent →L[ℝ] ℝ

abbrev ContinuousConnectionDerivative
    (Tangent : Type u) [NormedAddCommGroup Tangent] [NormedSpace ℝ Tangent] :=
  Tangent →L[ℝ] Tangent →L[ℝ] ℝ

abbrev SmoothSplitImmersionSecondJet
    (Tangent : Type u) (Normal : Type v)
    [NormedAddCommGroup Tangent] [NormedSpace ℝ Tangent]
    [NormedAddCommGroup Normal] [NormedSpace ℝ Normal] :=
  ContinuousTangentialQuadratic Tangent ×
    ContinuousSecondFundamentalForm
      (Tangent := Tangent) (Normal := Normal)

abbrev SmoothConnectionOneJet
    (Tangent : Type u) [NormedAddCommGroup Tangent] [NormedSpace ℝ Tangent] :=
  ContinuousConnectionValue Tangent × ContinuousConnectionDerivative Tangent

abbrev SmoothLowOrderStructuredJet
    (Tangent : Type u) (Normal : Type v)
    [NormedAddCommGroup Tangent] [NormedSpace ℝ Tangent]
    [NormedAddCommGroup Normal] [NormedSpace ℝ Normal] :=
  SmoothSplitImmersionSecondJet Tangent Normal ×
    SmoothConnectionOneJet Tangent

variable {Tangent : Type u} {Normal : Type v}
variable [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
variable [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
variable [FiniteDimensional ℝ Tangent]
variable [FiniteDimensional ℝ Normal]

def SmoothLowOrderStructuredJet.IsGeometric
    (jet : SmoothLowOrderStructuredJet Tangent Normal) : Prop :=
  (∀ first second, jet.1.1 first second = jet.1.1 second first) ∧
    (∀ first second, jet.1.2 first second = jet.1.2 second first)

def structuredNormalQuadraticProjection :
    SmoothLowOrderStructuredJet Tangent Normal →L[ℝ]
      ContinuousSecondFundamentalForm
        (Tangent := Tangent) (Normal := Normal) :=
  (ContinuousLinearMap.snd ℝ
      (ContinuousTangentialQuadratic Tangent)
      (ContinuousSecondFundamentalForm
        (Tangent := Tangent) (Normal := Normal))).comp
    (ContinuousLinearMap.fst ℝ
      (SmoothSplitImmersionSecondJet Tangent Normal)
      (SmoothConnectionOneJet Tangent))

def structuredConnectionDerivativeProjection :
    SmoothLowOrderStructuredJet Tangent Normal →L[ℝ]
      ContinuousConnectionDerivative Tangent :=
  (ContinuousLinearMap.snd ℝ
      (ContinuousConnectionValue Tangent)
      (ContinuousConnectionDerivative Tangent)).comp
    (ContinuousLinearMap.snd ℝ
      (SmoothSplitImmersionSecondJet Tangent Normal)
      (SmoothConnectionOneJet Tangent))

def continuousDerivativeFlip :
    ContinuousConnectionDerivative Tangent →L[ℝ]
      ContinuousConnectionDerivative Tangent :=
  (ContinuousLinearMap.flipₗᵢ ℝ Tangent Tangent ℝ :
    ContinuousConnectionDerivative Tangent →L[ℝ]
      ContinuousConnectionDerivative Tangent)

@[simp]
theorem continuousDerivativeFlip_apply
    (derivative : ContinuousConnectionDerivative Tangent)
    (first second : Tangent) :
    continuousDerivativeFlip derivative first second =
      derivative second first := by
  simp [continuousDerivativeFlip]

def continuousCurvatureFromDerivative :
    ContinuousConnectionDerivative Tangent →L[ℝ]
      ContinuousConnectionDerivative Tangent :=
  ((ContinuousLinearMap.id ℝ
      (ContinuousConnectionDerivative Tangent)) :
    ContinuousConnectionDerivative Tangent →L[ℝ]
      ContinuousConnectionDerivative Tangent) -
    continuousDerivativeFlip

@[simp]
theorem continuousCurvatureFromDerivative_apply
    (derivative : ContinuousConnectionDerivative Tangent)
    (first second : Tangent) :
    continuousCurvatureFromDerivative derivative first second =
      derivative first second - derivative second first := by
  simp [continuousCurvatureFromDerivative]

def structuredGaugeCurvatureProjection :
    SmoothLowOrderStructuredJet Tangent Normal →L[ℝ]
      ContinuousGaugeCurvature (Tangent := Tangent) :=
  continuousCurvatureFromDerivative.comp
    structuredConnectionDerivativeProjection

def smoothLowOrderReduction :
    SmoothLowOrderStructuredJet Tangent Normal →L[ℝ]
      SmoothLowOrderReducedJet
        (Tangent := Tangent) (Normal := Normal) :=
  structuredNormalQuadraticProjection.prod
    structuredGaugeCurvatureProjection

@[simp]
theorem smoothLowOrderReduction_secondFundamental
    (jet : SmoothLowOrderStructuredJet Tangent Normal) :
    (smoothLowOrderReduction jet).1 = jet.1.2 := by
  rfl

@[simp]
theorem smoothLowOrderReduction_curvature_apply
    (jet : SmoothLowOrderStructuredJet Tangent Normal)
    (first second : Tangent) :
    (smoothLowOrderReduction jet).2 first second =
      jet.2.2 first second - jet.2.2 second first := by
  simp [smoothLowOrderReduction, structuredGaugeCurvatureProjection,
    structuredConnectionDerivativeProjection]

theorem smoothLowOrderReduction_contDiff :
    ContDiff ℝ ∞
      (smoothLowOrderReduction (Tangent := Tangent) (Normal := Normal)) :=
  (smoothLowOrderReduction (Tangent := Tangent) (Normal := Normal)).contDiff

def forgetContinuousLowOrderStructuredJet
    (jet : SmoothLowOrderStructuredJet Tangent Normal) :
    LowOrderStructuredJet Tangent Normal where
  immersion :=
    { tangentialQuadratic := fun first second => jet.1.1 first second
      normalQuadratic := fun first second => jet.1.2 first second }
  connection :=
    { value := fun tangent => jet.2.1 tangent
      derivative := fun first second => jet.2.2 first second }

def continuousReductionLiftsAlgebraic
    (jet : SmoothLowOrderStructuredJet Tangent Normal) :
    ContinuousLiftOfLowOrderReducedData
      (reduceLowOrderJet (forgetContinuousLowOrderStructuredJet jet)) where
  smoothJet := smoothLowOrderReduction jet
  secondFundamental_apply := by
    intro first second
    rfl
  gaugeCurvature_apply := by
    intro first second
    rfl

theorem smoothLowOrderReduction_isGeometric
    (jet : SmoothLowOrderStructuredJet Tangent Normal)
    (hJet : jet.IsGeometric) :
    (smoothLowOrderReduction jet).IsGeometric := by
  constructor
  · intro first second
    exact hJet.2 first second
  · intro first second
    simp

structure ContinuousStructuredJetReductionStatus where
  continuousStructuredJetModelConstructed : Prop
  continuousCurvatureProjectionConstructed : Prop
  continuousReductionMapConstructed : Prop
  reductionMapSmooth : Prop
  algebraicReductionCompatibilityProved : Prop
  geometricityPreserved : Prop
  genuineJanusJetFamilyConstructed : Prop

def continuousStructuredJetReductionClosed
    (s : ContinuousStructuredJetReductionStatus) : Prop :=
  s.continuousStructuredJetModelConstructed ∧
  s.continuousCurvatureProjectionConstructed ∧
  s.continuousReductionMapConstructed ∧
  s.reductionMapSmooth ∧
  s.algebraicReductionCompatibilityProved ∧
  s.geometricityPreserved ∧
  s.genuineJanusJetFamilyConstructed

theorem missing_genuine_janus_jet_family_blocks_closure
    (s : ContinuousStructuredJetReductionStatus)
    (hMissing : Not s.genuineJanusJetFamilyConstructed) :
    Not (continuousStructuredJetReductionClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2

end

end P0EFTJanusRieszShapeOperatorContinuousStructuredJetReduction
end JanusFormal
