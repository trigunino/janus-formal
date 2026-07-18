import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFixedD8DiffeomorphismCategory4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricDiffeomorphismPullback4D

/-!
# General Lorentz metric functor on the fixed D8 category

The unconditional smooth pullback of arbitrary Lorentz metrics is proved to
respect the identity diffeomorphism and composition.  Hence genuine general
Lorentz metric fields form a contravariant section functor on the fixed D8
symmetry category.
-/

namespace JanusFormal
namespace P0EFTJanusFixedD8GeneralLorentzMetricFunctor4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 300000

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusSpinCImmersionCategory
open P0EFTJanusNaturalBundleFunctor
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusDiagonalDiffeomorphismAction4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarDensityFrameCovariance4D
open P0EFTJanusMappingTorusGeneralLorentzMetricDiffeomorphismPullback4D
open P0EFTJanusFixedD8DiffeomorphismCategory4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- A general Lorentz metric is determined by its bundled covariant tensor;
the musical equivalence is tied to that tensor by construction. -/
theorem smoothGeneralLorentzMetric_ext
    {first second : SmoothGeneralLorentzMetric period hPeriod}
    (hTensor : first.tensor = second.tensor) : first = second := by
  cases first with
  | mk firstTensor firstMusical firstEq firstLorentzian =>
    cases second with
    | mk secondTensor secondMusical secondEq secondLorentzian =>
      dsimp at hTensor
      subst secondTensor
      have hMusical : firstMusical = secondMusical := by
        funext point
        apply ContinuousLinearEquiv.ext
        funext vector
        have hFirst := congrArg (fun current => current vector) (firstEq point)
        have hSecond := congrArg (fun current => current vector) (secondEq point)
        exact hFirst.trans hSecond.symm
      subst secondMusical
      rfl

/-- Tensor pullback by the identity is exactly the original smooth tensor. -/
theorem smoothDiffeomorphismTensorPullback_refl
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    smoothDiffeomorphismTensorPullback period hPeriod
        (Diffeomorph.refl coverModelWithCorners
          (EffectiveQuotient period hPeriod) ω) tensor = tensor := by
  apply SmoothSymmetricCovariantTwoTensor.ext
  apply ContMDiffSection.ext
  intro point
  apply ContinuousLinearMap.ext
  intro first
  apply ContinuousLinearMap.ext
  intro second
  change tensor.tensor point
      (mfderiv coverModelWithCorners coverModelWithCorners
        (id : EffectiveQuotient period hPeriod →
          EffectiveQuotient period hPeriod) point first)
      (mfderiv coverModelWithCorners coverModelWithCorners
        (id : EffectiveQuotient period hPeriod →
          EffectiveQuotient period hPeriod) point second) =
    tensor.tensor point first second
  rw [mfderiv_id]
  rfl

/-- Pullback of smooth covariant tensors is contravariantly functorial. -/
theorem smoothDiffeomorphismTensorPullback_trans
    (first second : SpacetimeDiffeomorphism period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    smoothDiffeomorphismTensorPullback period hPeriod first
        (smoothDiffeomorphismTensorPullback period hPeriod second tensor) =
      smoothDiffeomorphismTensorPullback period hPeriod
        (first.trans second) tensor := by
  apply SmoothSymmetricCovariantTwoTensor.ext
  apply ContMDiffSection.ext
  intro point
  apply ContinuousLinearMap.ext
  intro firstTangent
  apply ContinuousLinearMap.ext
  intro secondTangent
  have hOuter := second.contMDiff.mdifferentiableAt
    (x := first point) (by simp)
  have hInner := first.contMDiff.mdifferentiableAt
    (x := point) (by simp)
  change tensor.tensor (second (first point))
      (mfderiv coverModelWithCorners coverModelWithCorners second (first point)
        (mfderiv coverModelWithCorners coverModelWithCorners first point
          firstTangent))
      (mfderiv coverModelWithCorners coverModelWithCorners second (first point)
        (mfderiv coverModelWithCorners coverModelWithCorners first point
          secondTangent)) =
    tensor.tensor ((first.trans second) point)
      (mfderiv coverModelWithCorners coverModelWithCorners
        (first.trans second) point firstTangent)
      (mfderiv coverModelWithCorners coverModelWithCorners
        (first.trans second) point secondTangent)
  rw [show (first.trans second : EffectiveQuotient period hPeriod →
      EffectiveQuotient period hPeriod) = second ∘ first by rfl]
  rw [mfderiv_comp point hOuter hInner]
  rfl

theorem smoothGeneralLorentzMetricDiffeomorphismPullback_refl
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    smoothGeneralLorentzMetricDiffeomorphismPullback period hPeriod
        (Diffeomorph.refl coverModelWithCorners
          (EffectiveQuotient period hPeriod) ω) metric = metric := by
  apply smoothGeneralLorentzMetric_ext period hPeriod
  exact smoothDiffeomorphismTensorPullback_refl period hPeriod metric.tensor

theorem smoothGeneralLorentzMetricDiffeomorphismPullback_trans
    (first second : SpacetimeDiffeomorphism period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    smoothGeneralLorentzMetricDiffeomorphismPullback period hPeriod first
        (smoothGeneralLorentzMetricDiffeomorphismPullback period hPeriod
          second metric) =
      smoothGeneralLorentzMetricDiffeomorphismPullback period hPeriod
        (first.trans second) metric := by
  apply smoothGeneralLorentzMetric_ext period hPeriod
  exact smoothDiffeomorphismTensorPullback_trans period hPeriod
    first second metric.tensor

/-- General Lorentz metrics are a contravariant section functor on the fixed
D8 diffeomorphism category. -/
def fixedD8GeneralLorentzMetricSectionFunctor :
    NaturalSectionFunctor (fixedD8DiffeomorphismCategory period hPeriod) where
  Section := fun _ => SmoothGeneralLorentzMetric period hPeriod
  pullback := fun morphism metric =>
    smoothGeneralLorentzMetricDiffeomorphismPullback period hPeriod
      morphism.morphism metric
  pullbackIdentity := by
    intro object metric
    exact smoothGeneralLorentzMetricDiffeomorphismPullback_refl period hPeriod
      metric
  pullbackComposition := by
    intro first second third secondMorphism firstMorphism metric
    exact (smoothGeneralLorentzMetricDiffeomorphismPullback_trans period hPeriod
      firstMorphism.morphism secondMorphism.morphism metric).symm

end

end P0EFTJanusFixedD8GeneralLorentzMetricFunctor4D
end JanusFormal
