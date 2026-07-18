import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzTensor4D
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusSmoothPTInvolution

/-!
# PT action on general Lorentz tensor fields

This gate installs the exact algebraic pullback action of the analytic PT
involution on general covariant two-tensor fields.  Smooth bundling of the
pulled-back dependent section remains a separate analytic obligation.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGeneralLorentzTensorPTAction4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusPTInvolution
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothPTInvolution
open P0EFTJanusMappingTorusGeneralLorentzTensor4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private abbrev TangentFiber (point : EffectiveQuotient period hPeriod) :=
  TangentSpace coverModelWithCorners point

private abbrev CotangentFiber (point : EffectiveQuotient period hPeriod) :=
  TangentFiber period hPeriod point →L[Real] Real

private abbrev CovariantTwoTensorFiber
    (point : EffectiveQuotient period hPeriod) :=
  TangentFiber period hPeriod point →L[Real]
    CotangentFiber period hPeriod point

private abbrev CovariantTwoTensorModel :=
  CoverCoordinates →L[Real] CoverCoordinates →L[Real] Real

/-- The differential of the analytic PT involution is itself involutive. -/
theorem reflectedSpherePT_mfderiv_involutive
    (point : EffectiveQuotient period hPeriod)
    (vector : TangentFiber period hPeriod point) :
    mfderiv coverModelWithCorners coverModelWithCorners
        (reflectedSpherePT period hPeriod)
        (reflectedSpherePT period hPeriod point)
        (mfderiv coverModelWithCorners coverModelWithCorners
          (reflectedSpherePT period hPeriod) point vector) = vector := by
  have hSmooth := reflectedSpherePT_contMDiff period hPeriod
  have hComposition := mfderiv_comp_apply point
    (hSmooth.mdifferentiable (by simp)
      (reflectedSpherePT period hPeriod point))
    (hSmooth.mdifferentiable (by simp) point) vector
  have hInvolution :
      (reflectedSpherePT period hPeriod) ∘
          (reflectedSpherePT period hPeriod) =
        (id : EffectiveQuotient period hPeriod →
          EffectiveQuotient period hPeriod) := by
    funext current
    exact reflectedSpherePT_involutive period hPeriod current
  rw [hInvolution, mfderiv_id] at hComposition
  exact hComposition.symm

/-- PT pullback of an arbitrary covariant two-tensor field. -/
def ptTensorPullback
    (tensor : CovariantTwoTensorField period hPeriod) :
    CovariantTwoTensorField period hPeriod :=
  fun point => pullbackTensorValue period hPeriod
    (reflectedSpherePTDiffeomorph period hPeriod) tensor point

@[simp]
theorem ptTensorPullback_apply
    (tensor : CovariantTwoTensorField period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (first second : TangentFiber period hPeriod point) :
    ptTensorPullback period hPeriod tensor point first second =
      tensor (reflectedSpherePT period hPeriod point)
        (mfderiv coverModelWithCorners coverModelWithCorners
          (reflectedSpherePT period hPeriod) point first)
        (mfderiv coverModelWithCorners coverModelWithCorners
          (reflectedSpherePT period hPeriod) point second) := by
  rfl

@[simp]
theorem ptTensorPullback_involutive
    (tensor : CovariantTwoTensorField period hPeriod) :
    ptTensorPullback period hPeriod
        (ptTensorPullback period hPeriod tensor) = tensor := by
  funext point
  apply ContinuousLinearMap.ext
  intro first
  apply ContinuousLinearMap.ext
  intro second
  simp only [ptTensorPullback_apply]
  rw [reflectedSpherePT_mfderiv_involutive period hPeriod point first,
    reflectedSpherePT_mfderiv_involutive period hPeriod point second,
    reflectedSpherePT_involutive]

/-- PT pullback preserves pointwise symmetry. -/
theorem ptTensorPullback_symmetric
    (tensor : CovariantTwoTensorField period hPeriod)
    (hTensor : ∀ point first second,
      tensor point first second = tensor point second first) :
    ∀ point first second,
      ptTensorPullback period hPeriod tensor point first second =
        ptTensorPullback period hPeriod tensor point second first := by
  intro point first second
  exact pullbackTensorValue_symmetric period hPeriod
    (reflectedSpherePTDiffeomorph period hPeriod) tensor hTensor
    point first second

/-- PT pullback preserves nondegeneracy in every fiber. -/
theorem ptTensorPullback_nondegenerate
    (tensor : CovariantTwoTensorField period hPeriod)
    (hTensor : ∀ point,
      FiberIsNondegenerate period hPeriod (tensor point)) :
    ∀ point, FiberIsNondegenerate period hPeriod
      (ptTensorPullback period hPeriod tensor point) := by
  intro point
  exact pullbackTensorValue_nondegenerate period hPeriod
    (reflectedSpherePTDiffeomorph period hPeriod) tensor point
    (hTensor (reflectedSpherePT period hPeriod point))

/-- PT pullback preserves Lorentz inertia `(3,1)` in every fiber. -/
theorem ptTensorPullback_lorentzian
    (tensor : CovariantTwoTensorField period hPeriod)
    (hTensor : ∀ point, FiberIsLorentzian period hPeriod (tensor point)) :
    ∀ point, FiberIsLorentzian period hPeriod
      (ptTensorPullback period hPeriod tensor point) := by
  intro point
  exact pullbackTensorValue_lorentzian period hPeriod
    (reflectedSpherePTDiffeomorph period hPeriod) tensor point
    (hTensor (reflectedSpherePT period hPeriod point))

/-! ## Smooth bundling of the analytic PT pullback -/

/-- Atomic local regularity statement for the dependent rank-two Hom bundle.
This is the exact point not covered by Mathlib's vector-field pullback API. -/
def PTTensorPullbackSmoothAt
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) : Prop :=
  ContMDiffAt coverModelWithCorners
    (coverModelWithCorners.prod 𝓘(Real, CovariantTwoTensorModel)) ∞
    (fun current => TotalSpace.mk' CovariantTwoTensorModel
      (E := CovariantTwoTensorFiber period hPeriod) current
      (ptTensorPullback period hPeriod tensor.tensor.toTensorField current))
    point

/-- Local-to-global contract for the one missing dependent-Hom naturality
lemma.  Every other part of the PT action is discharged below. -/
def AnalyticPTTensorPullbackLocalSmoothness : Prop :=
  ∀ (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) point,
    PTTensorPullbackSmoothAt period hPeriod tensor point

theorem ptTensorPullback_contMDiff_of_smoothAt
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (regularity : ∀ point,
      PTTensorPullbackSmoothAt period hPeriod tensor point) :
    ContMDiff coverModelWithCorners
      (coverModelWithCorners.prod 𝓘(Real, CovariantTwoTensorModel)) ∞
      (fun point => TotalSpace.mk' CovariantTwoTensorModel
        (E := CovariantTwoTensorFiber period hPeriod) point
        (ptTensorPullback period hPeriod
          tensor.tensor.toTensorField point)) :=
  regularity

/-- Genuine smooth symmetric tensor obtained from the analytic PT formula. -/
def smoothPTTensorPullback
    (regularity : AnalyticPTTensorPullbackLocalSmoothness period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    SmoothSymmetricCovariantTwoTensor period hPeriod where
  tensor :=
    { toFun := ptTensorPullback period hPeriod tensor.tensor.toTensorField
      contMDiff_toFun := ptTensorPullback_contMDiff_of_smoothAt
        period hPeriod tensor (regularity tensor) }
  symmetric := ptTensorPullback_symmetric period hPeriod
    tensor.tensor.toTensorField tensor.symmetric

@[simp]
theorem smoothPTTensorPullback_apply
    (regularity : AnalyticPTTensorPullbackLocalSmoothness period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (first second : TangentFiber period hPeriod point) :
    (smoothPTTensorPullback period hPeriod regularity tensor).tensor
        point first second =
      tensor.tensor (reflectedSpherePT period hPeriod point)
        (mfderiv coverModelWithCorners coverModelWithCorners
          (reflectedSpherePT period hPeriod) point first)
        (mfderiv coverModelWithCorners coverModelWithCorners
          (reflectedSpherePT period hPeriod) point second) :=
  rfl

@[simp]
theorem smoothPTTensorPullback_involutive
    (regularity : AnalyticPTTensorPullbackLocalSmoothness period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    smoothPTTensorPullback period hPeriod regularity
        (smoothPTTensorPullback period hPeriod regularity tensor) = tensor := by
  apply SmoothSymmetricCovariantTwoTensor.ext
  apply ContMDiffSection.ext
  intro point
  exact congrFun
    (ptTensorPullback_involutive period hPeriod
      tensor.tensor.toTensorField) point

/-- The bundled PT action preserves fiberwise nondegeneracy everywhere. -/
theorem smoothPTTensorPullback_nondegenerate
    (regularity : AnalyticPTTensorPullbackLocalSmoothness period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hTensor : IsEverywhereNondegenerate period hPeriod tensor) :
    IsEverywhereNondegenerate period hPeriod
      (smoothPTTensorPullback period hPeriod regularity tensor) := by
  intro point
  exact ptTensorPullback_nondegenerate period hPeriod
    tensor.tensor.toTensorField hTensor point

/-- The bundled PT action preserves Lorentz inertia `(3,1)` everywhere. -/
theorem smoothPTTensorPullback_lorentzian
    (regularity : AnalyticPTTensorPullbackLocalSmoothness period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hTensor : IsEverywhereLorentzian period hPeriod tensor) :
    IsEverywhereLorentzian period hPeriod
      (smoothPTTensorPullback period hPeriod regularity tensor) := by
  intro point
  exact ptTensorPullback_lorentzian period hPeriod
    tensor.tensor.toTensorField hTensor point

/-- Smooth Lorentz tensors, retaining both algebraic conditions explicitly. -/
def SmoothLorentzTensorDomain :=
  {tensor : SmoothSymmetricCovariantTwoTensor period hPeriod //
    IsEverywhereNondegenerate period hPeriod tensor ∧
      IsEverywhereLorentzian period hPeriod tensor}

/-- PT is an endomorphism of the genuine smooth Lorentz tensor domain. -/
def smoothLorentzTensorPTPullback
    (regularity : AnalyticPTTensorPullbackLocalSmoothness period hPeriod)
    (tensor : SmoothLorentzTensorDomain period hPeriod) :
    SmoothLorentzTensorDomain period hPeriod :=
  ⟨smoothPTTensorPullback period hPeriod regularity tensor.1,
    smoothPTTensorPullback_nondegenerate period hPeriod regularity tensor.1
      tensor.2.1,
    smoothPTTensorPullback_lorentzian period hPeriod regularity tensor.1
      tensor.2.2⟩

@[simp]
theorem smoothLorentzTensorPTPullback_involutive
    (regularity : AnalyticPTTensorPullbackLocalSmoothness period hPeriod)
    (tensor : SmoothLorentzTensorDomain period hPeriod) :
    smoothLorentzTensorPTPullback period hPeriod regularity
        (smoothLorentzTensorPTPullback period hPeriod regularity tensor) =
      tensor := by
  apply Subtype.ext
  exact smoothPTTensorPullback_involutive period hPeriod regularity tensor.1

/-- PT plus sector exchange on a pair of general tensor fields. -/
def generalTensorPTExchange
    (metrics : CovariantTwoTensorField period hPeriod ×
      CovariantTwoTensorField period hPeriod) :
    CovariantTwoTensorField period hPeriod ×
      CovariantTwoTensorField period hPeriod :=
  (ptTensorPullback period hPeriod metrics.2,
    ptTensorPullback period hPeriod metrics.1)

@[simp]
theorem generalTensorPTExchange_involutive
    (metrics : CovariantTwoTensorField period hPeriod ×
      CovariantTwoTensorField period hPeriod) :
    generalTensorPTExchange period hPeriod
        (generalTensorPTExchange period hPeriod metrics) = metrics := by
  simp [generalTensorPTExchange]

end

end P0EFTJanusMappingTorusGeneralLorentzTensorPTAction4D
end JanusFormal
