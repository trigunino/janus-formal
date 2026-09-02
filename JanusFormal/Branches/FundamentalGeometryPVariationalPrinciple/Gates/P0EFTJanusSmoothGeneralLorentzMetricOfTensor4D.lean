import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D

/-!
# General Lorentz metric from a certified Lorentzian tensor

A pointwise Lorentz frame supplies the genuine musical equivalence of any
smooth symmetric tensor already certified to have Lorentz inertia `(3,1)`.
-/

namespace JanusFormal
namespace P0EFTJanusSmoothGeneralLorentzMetricOfTensor4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace
open Module
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance : IsManifold coverModelWithCorners ω
    (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private abbrev TangentFiber (point : EffectiveQuotient period hPeriod) :=
  TangentSpace coverModelWithCorners point

private abbrev CotangentFiber (point : EffectiveQuotient period hPeriod) :=
  TangentFiber period hPeriod point →L[Real] Real

private def modelSpatialMusical :
    EuclideanSpace Real (Fin 3) ≃L[Real]
      (EuclideanSpace Real (Fin 3) →L[Real] Real) :=
  (InnerProductSpace.toDual Real
    (EuclideanSpace Real (Fin 3))).toContinuousLinearEquiv

private def modelTimeMusical : Real ≃L[Real] (Real →L[Real] Real) :=
  (ContinuousLinearEquiv.neg Real).trans
    (InnerProductSpace.toDual Real Real).toContinuousLinearEquiv

private def modelMinkowskiMusical :
    CoverCoordinates ≃L[Real] (CoverCoordinates →L[Real] Real) :=
  (ContinuousLinearEquiv.prodCongr modelSpatialMusical modelTimeMusical).trans
    (ContinuousLinearMap.coprodEquivL Real)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
private theorem modelMinkowskiMusical_apply
    (first second : CoverCoordinates) :
    modelMinkowskiMusical first second = modelMinkowskiPair first second := by
  simp [modelMinkowskiMusical, modelSpatialMusical, modelTimeMusical,
    ContinuousLinearMap.coprodEquivL, ContinuousLinearMap.coprodEquiv,
    ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.neg_apply,
    modelMinkowskiPair]
  change inner Real first.1 second.1 + -inner Real first.2 second.2 =
    inner Real first.1 second.1 - first.2 * second.2
  rw [Real.inner_apply]
  rfl

/-- A pointwise Lorentz frame selected from the inertia certificate. -/
def lorentzFrameOfTensor
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hLorentz : IsEverywhereLorentzian period hPeriod tensor)
    (point : EffectiveQuotient period hPeriod) :
    TangentFiber period hPeriod point ≃L[Real] CoverCoordinates :=
  Classical.choose (hLorentz point)

theorem lorentzFrameOfTensor_pair
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hLorentz : IsEverywhereLorentzian period hPeriod tensor)
    (point : EffectiveQuotient period hPeriod)
    (first second : TangentFiber period hPeriod point) :
    tensor.tensor point first second =
      modelMinkowskiPair
        (lorentzFrameOfTensor period hPeriod tensor hLorentz point first)
        (lorentzFrameOfTensor period hPeriod tensor hLorentz point second) :=
  Classical.choose_spec (hLorentz point) first second

/-- The tensor musical, transported from the fixed model Minkowski musical. -/
def smoothGeneralLorentzMetricMusicalOfTensor
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hLorentz : IsEverywhereLorentzian period hPeriod tensor)
    (point : EffectiveQuotient period hPeriod) :
    TangentFiber period hPeriod point ≃L[Real]
      CotangentFiber period hPeriod point :=
  let frame := lorentzFrameOfTensor period hPeriod tensor hLorentz point
  (frame.trans modelMinkowskiMusical).trans
    (frame.symm.arrowCongr (ContinuousLinearEquiv.refl Real Real))

theorem smoothGeneralLorentzMetricMusicalOfTensor_eq_tensor
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hLorentz : IsEverywhereLorentzian period hPeriod tensor)
    (point : EffectiveQuotient period hPeriod) :
    (smoothGeneralLorentzMetricMusicalOfTensor period hPeriod tensor hLorentz point :
        TangentFiber period hPeriod point →L[Real]
          CotangentFiber period hPeriod point) = tensor.tensor point := by
  apply ContinuousLinearMap.ext
  intro first
  apply ContinuousLinearMap.ext
  intro second
  have hMusical :
      smoothGeneralLorentzMetricMusicalOfTensor period hPeriod tensor hLorentz
          point first second =
        modelMinkowskiPair
          (lorentzFrameOfTensor period hPeriod tensor hLorentz point first)
          (lorentzFrameOfTensor period hPeriod tensor hLorentz point second) := by
    simp [smoothGeneralLorentzMetricMusicalOfTensor,
      modelMinkowskiMusical_apply]
  change smoothGeneralLorentzMetricMusicalOfTensor period hPeriod tensor
      hLorentz point first second = tensor.tensor point first second
  rw [hMusical]
  exact (lorentzFrameOfTensor_pair period hPeriod tensor hLorentz point
    first second).symm

/-- Package a certified smooth Lorentzian tensor as a general Lorentz metric. -/
def smoothGeneralLorentzMetricOfTensor
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hLorentz : IsEverywhereLorentzian period hPeriod tensor) :
    SmoothGeneralLorentzMetric period hPeriod where
  tensor := tensor
  musical := smoothGeneralLorentzMetricMusicalOfTensor period hPeriod tensor hLorentz
  musical_eq_tensor :=
    smoothGeneralLorentzMetricMusicalOfTensor_eq_tensor period hPeriod tensor hLorentz
  lorentzian := hLorentz

@[simp]
theorem smoothGeneralLorentzMetricOfTensor_tensor
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hLorentz : IsEverywhereLorentzian period hPeriod tensor) :
    (smoothGeneralLorentzMetricOfTensor period hPeriod tensor hLorentz).tensor =
      tensor :=
  rfl

@[simp]
theorem smoothGeneralLorentzMetricOfTensor_musical_apply
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hLorentz : IsEverywhereLorentzian period hPeriod tensor)
    (point : EffectiveQuotient period hPeriod)
    (first second : TangentFiber period hPeriod point) :
    (smoothGeneralLorentzMetricOfTensor period hPeriod tensor hLorentz).musical
        point first second = tensor.tensor point first second := by
  change smoothGeneralLorentzMetricMusicalOfTensor period hPeriod tensor
      hLorentz point first second = tensor.tensor point first second
  have hFirst := DFunLike.congr_fun
    (smoothGeneralLorentzMetricMusicalOfTensor_eq_tensor period hPeriod tensor
      hLorentz point) first
  exact DFunLike.congr_fun hFirst second

/-- Gate marker: every certified Lorentzian tensor has a metric realization
with exactly the supplied covariant tensor. -/
theorem smooth_general_lorentz_metric_of_tensor_gate
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (hLorentz : IsEverywhereLorentzian period hPeriod tensor) :
    ∃ metric : SmoothGeneralLorentzMetric period hPeriod,
      metric.tensor = tensor :=
  ⟨smoothGeneralLorentzMetricOfTensor period hPeriod tensor hLorentz, rfl⟩

end
end P0EFTJanusSmoothGeneralLorentzMetricOfTensor4D
end JanusFormal
