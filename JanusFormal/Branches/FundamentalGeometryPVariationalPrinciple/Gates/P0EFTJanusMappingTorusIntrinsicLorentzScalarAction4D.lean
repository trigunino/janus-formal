import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicLorentzCertificate4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D

/-!
# Intrinsic quotient Lorentz metric and scalar-action bridge

This gate turns the unconditional intrinsic Lorentz certificate into the
general metric object consumed by the holonomic scalar-density API.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace
open Bundle MeasureTheory Module
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusIntrinsicLorentzMetricDescent4D
open P0EFTJanusMappingTorusIntrinsicLorentzCertificate4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

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

private def quotientLorentzFrame
    (point : EffectiveQuotient period hPeriod) :
    TangentFiber period hPeriod point ≃L[Real] CoverCoordinates :=
  Classical.choose
    (intrinsicQuotientTensor_isEverywhereLorentzian period hPeriod point)

private theorem quotientLorentzFrame_pair
    (point : EffectiveQuotient period hPeriod)
    (first second : TangentFiber period hPeriod point) :
    (intrinsicTensorQuotientDescent period hPeriod).toSymmetricTensor.tensor
        point first second =
      modelMinkowskiPair (quotientLorentzFrame period hPeriod point first)
        (quotientLorentzFrame period hPeriod point second) :=
  Classical.choose_spec
    (intrinsicQuotientTensor_isEverywhereLorentzian period hPeriod point)
      first second

private def quotientMusical
    (point : EffectiveQuotient period hPeriod) :
    TangentFiber period hPeriod point ≃L[Real]
      CotangentFiber period hPeriod point :=
  let frame := quotientLorentzFrame period hPeriod point
  (frame.trans modelMinkowskiMusical).trans
    (frame.symm.arrowCongr (ContinuousLinearEquiv.refl Real Real))

def intrinsicSmoothGeneralLorentzMetric :
    SmoothGeneralLorentzMetric period hPeriod where
  tensor := (intrinsicTensorQuotientDescent period hPeriod).toSymmetricTensor
  musical := quotientMusical period hPeriod
  musical_eq_tensor := by
    intro point
    apply ContinuousLinearMap.ext
    intro first
    apply ContinuousLinearMap.ext
    intro second
    have hMusical : quotientMusical period hPeriod point first second =
      modelMinkowskiPair
        (quotientLorentzFrame period hPeriod point first)
        (quotientLorentzFrame period hPeriod point second) := by
      simp [quotientMusical, modelMinkowskiMusical_apply]
    change quotientMusical period hPeriod point first second = _
    rw [hMusical]
    exact (quotientLorentzFrame_pair period hPeriod point first second).symm
  lorentzian := intrinsicQuotientTensor_isEverywhereLorentzian period hPeriod

theorem intrinsicSmoothGeneralLorentzMetric_nondegenerate :
    IsEverywhereNondegenerate period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor :=
  metric_everywhere_nondegenerate period hPeriod
    (intrinsicSmoothGeneralLorentzMetric period hPeriod)

private def coverCoordinateBasis : Basis (Fin 4) Real CoverCoordinates := by
  let basis := Module.finBasis Real CoverCoordinates
  have hDimension : Module.finrank Real CoverCoordinates = 4 := by
    simp [CoverCoordinates]
  simpa [hDimension] using basis

/-- Pointwise Lorentz frame selected by the intrinsic inertia certificate.
No global smoothness assertion is made for this choice. -/
def intrinsicPointwiseFrame
    (point : EffectiveQuotient period hPeriod) :
    Fin 4 → TangentFiber period hPeriod point :=
  fun index => (quotientLorentzFrame period hPeriod point).symm
    (coverCoordinateBasis index)

/-- Intrinsic scalar density evaluated in the certified pointwise frame. -/
def intrinsicHolonomicScalarDensity
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod)
    (point : EffectiveQuotient period hPeriod) : Real :=
  holonomicScalarDensity period hPeriod
    (intrinsicSmoothGeneralLorentzMetric period hPeriod) massSquared field point
    (intrinsicPointwiseFrame period hPeriod point)

def intrinsicHolonomicScalarFirstVariation
    (massSquared : Real)
    (field variation : SmoothScalarField period hPeriod)
    (point : EffectiveQuotient period hPeriod) : Real :=
  holonomicScalarDensityFirstVariation period hPeriod
    (intrinsicSmoothGeneralLorentzMetric period hPeriod) massSquared
    field variation point (intrinsicPointwiseFrame period hPeriod point)

def intrinsicHolonomicScalarQuadraticRemainder
    (massSquared : Real)
    (variation : SmoothScalarField period hPeriod)
    (point : EffectiveQuotient period hPeriod) : Real :=
  holonomicScalarDensityQuadraticRemainder period hPeriod
    (intrinsicSmoothGeneralLorentzMetric period hPeriod) massSquared variation
    point (intrinsicPointwiseFrame period hPeriod point)

/-- Exact affine scalar variation for the actual intrinsic quotient metric. -/
theorem intrinsicHolonomicScalarDensity_line_expansion
    (massSquared : Real)
    (field variation : SmoothScalarField period hPeriod)
    (epsilon : Real)
    (point : EffectiveQuotient period hPeriod) :
    intrinsicHolonomicScalarDensity period hPeriod massSquared
        (scalarFieldLine period hPeriod field variation epsilon) point =
      intrinsicHolonomicScalarDensity period hPeriod massSquared field point +
        epsilon * intrinsicHolonomicScalarFirstVariation period hPeriod
          massSquared field variation point +
        epsilon ^ 2 * intrinsicHolonomicScalarQuadraticRemainder period hPeriod
          massSquared variation point := by
  exact holonomicScalarDensity_line_expansion period hPeriod
    (intrinsicSmoothGeneralLorentzMetric period hPeriod) massSquared
      field variation epsilon point (intrinsicPointwiseFrame period hPeriod point)

/-- The density is unconditionally integrable for the finite zero measure.
Nonzero finite measures require the local-frame regularity bridge. -/
theorem intrinsicHolonomicScalarDensity_integrable_zeroMeasure
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod) :
    Integrable (intrinsicHolonomicScalarDensity period hPeriod massSquared field)
      (0 : Measure (EffectiveQuotient period hPeriod)) :=
  integrable_zero_measure

/-- Unconditional integrated branch before a nonzero local-frame measure
construction is supplied. -/
def intrinsicHolonomicScalarActionZeroMeasure
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod) : Real :=
  ∫ point, intrinsicHolonomicScalarDensity period hPeriod massSquared field point
    ∂(0 : Measure (EffectiveQuotient period hPeriod))

@[simp]
theorem intrinsicHolonomicScalarActionZeroMeasure_eq_zero
    (massSquared : Real)
    (field : SmoothScalarField period hPeriod) :
    intrinsicHolonomicScalarActionZeroMeasure period hPeriod massSquared field = 0 := by
  simp [intrinsicHolonomicScalarActionZeroMeasure]

theorem intrinsicHolonomicScalarActionZeroMeasure_line_hasDerivAt
    (massSquared : Real)
    (field variation : SmoothScalarField period hPeriod) :
    HasDerivAt
      (fun epsilon => intrinsicHolonomicScalarActionZeroMeasure period hPeriod
        massSquared (scalarFieldLine period hPeriod field variation epsilon))
      0 0 := by
  simpa using (hasDerivAt_const (x := (0 : Real)) (c := (0 : Real)))

end
end P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
end JanusFormal
