import Mathlib.Analysis.Calculus.FDeriv.Add
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlas4D

/-!
# Linearity of the physical scalar Euler residual

For the fixed intrinsic Lorentz metric, every operation entering

`box_g phi - m² phi`

is linear in the scalar field: pullback to a chart, first derivative, second
derivative, Christoffel correction and inverse-metric contraction.  This file
proves those identities directly.

Consequently the atlas residual and the selected global residual are linear
without any additional analytic hypothesis.  A physical globalization package
therefore needs only overlap compatibility and continuity; the smooth-core to
bulk-L2 linear operator follows automatically.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerLinearity4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff ENNReal
open MeasureTheory Set Topology
open P0EFTJanusMetricCoupledScalarMatterJetVariation
open P0EFTJanusScalarStressCovariantJetConservation4D
open P0EFTJanusScalarStressCoordinateConnectionJet4D
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarJet4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlas4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev Vector4 :=
  P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

/-- Coordinate representatives are additive in the scalar field. -/
theorem localScalarRepresentative_add
    (first second : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    localScalarRepresentative period hPeriod (first + second) patch =
      localScalarRepresentative period hPeriod first patch +
        localScalarRepresentative period hPeriod second patch :=
  rfl

/-- Coordinate representatives are homogeneous in the scalar field. -/
theorem localScalarRepresentative_smul
    (scalar : Real)
    (field : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    localScalarRepresentative period hPeriod (scalar • field) patch =
      scalar • localScalarRepresentative period hPeriod field patch :=
  rfl

/-- Local first derivatives are additive. -/
theorem localScalarGradient_add
    (first second : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    localScalarGradient period hPeriod (first + second) patch coordinate =
      localScalarGradient period hPeriod first patch coordinate +
        localScalarGradient period hPeriod second patch coordinate := by
  ext index
  unfold localScalarGradient
  rw [localScalarRepresentative_add]
  rw [fderiv_add
    ((localScalarRepresentative_contDiff
      period hPeriod first patch).differentiable (by simp)).differentiableAt
    ((localScalarRepresentative_contDiff
      period hPeriod second patch).differentiable (by simp)).differentiableAt]
  rfl

/-- Local first derivatives are homogeneous. -/
theorem localScalarGradient_smul
    (scalar : Real)
    (field : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    localScalarGradient period hPeriod (scalar • field) patch coordinate =
      scalar • localScalarGradient period hPeriod field patch coordinate := by
  ext index
  unfold localScalarGradient
  rw [localScalarRepresentative_smul]
  rw [fderiv_const_smul_field]
  rfl

/-- The function-valued first derivative is additive. -/
theorem fderiv_localScalarRepresentative_add
    (first second : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    fderiv Real
        (localScalarRepresentative period hPeriod (first + second) patch) =
      fderiv Real (localScalarRepresentative period hPeriod first patch) +
        fderiv Real (localScalarRepresentative period hPeriod second patch) := by
  funext coordinate
  rw [localScalarRepresentative_add]
  exact fderiv_add
    ((localScalarRepresentative_contDiff
      period hPeriod first patch).differentiable (by simp)).differentiableAt
    ((localScalarRepresentative_contDiff
      period hPeriod second patch).differentiable (by simp)).differentiableAt

/-- The function-valued first derivative is homogeneous. -/
theorem fderiv_localScalarRepresentative_smul
    (scalar : Real)
    (field : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    fderiv Real
        (localScalarRepresentative period hPeriod (scalar • field) patch) =
      scalar • fderiv Real
        (localScalarRepresentative period hPeriod field patch) := by
  rw [localScalarRepresentative_smul]
  exact fderiv_const_smul_field scalar

/-- Local second coordinate derivatives are additive. -/
theorem localScalarPartialGradient_add
    (first second : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    localScalarPartialGradient period hPeriod (first + second) patch coordinate =
      localScalarPartialGradient period hPeriod first patch coordinate +
        localScalarPartialGradient period hPeriod second patch coordinate := by
  ext firstIndex secondIndex
  unfold localScalarPartialGradient
  simp only [Matrix.add_apply]
  rw [fderiv_localScalarRepresentative_add]
  rw [fderiv_add
    (((localScalarRepresentative_contDiff period hPeriod first patch).fderiv_right
      (m := ∞) (by simp)).differentiable (by simp)).differentiableAt
    (((localScalarRepresentative_contDiff period hPeriod second patch).fderiv_right
      (m := ∞) (by simp)).differentiable (by simp)).differentiableAt]
  rfl

/-- Local second coordinate derivatives are homogeneous. -/
theorem localScalarPartialGradient_smul
    (scalar : Real)
    (field : SmoothScalarField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    localScalarPartialGradient period hPeriod (scalar • field) patch coordinate =
      scalar • localScalarPartialGradient period hPeriod field patch coordinate := by
  ext firstIndex secondIndex
  unfold localScalarPartialGradient
  simp only [Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  rw [fderiv_localScalarRepresentative_smul]
  change (fderiv Real
      (scalar • fderiv Real
        (localScalarRepresentative period hPeriod field patch)) coordinate) _ _ = _
  have hDerivative :
      fderiv Real (scalar • fderiv Real
          (localScalarRepresentative period hPeriod field patch)) =
        scalar • fderiv Real (fderiv Real
          (localScalarRepresentative period hPeriod field patch)) :=
    fderiv_const_smul_field (𝕜 := Real) (R := Real)
      (f := fderiv Real
        (localScalarRepresentative period hPeriod field patch)) scalar
  rw [congrFun hDerivative coordinate]
  rfl

/-- Covariant Hessians are additive in the scalar field. -/
theorem localCovariantScalarJet_hessian_add
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (first second : SmoothScalarField period hPeriod)
    (coordinate : Vector4) :
    (localCovariantScalarJet period hPeriod metric patch
      (first + second) coordinate).hessian =
      (localCovariantScalarJet period hPeriod metric patch first coordinate).hessian +
        (localCovariantScalarJet period hPeriod metric patch second coordinate).hessian := by
  ext firstIndex secondIndex
  simp only [localCovariantScalarJet, coordinateScalarJetNormalForm,
    coordinateCovariantHessian, localCoordinateScalarJet]
  rw [localScalarPartialGradient_add, localScalarGradient_add]
  simp only [Matrix.add_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  simp only [coordinateCovariantHessian, localCoordinateScalarJet]
  ring

/-- Covariant Hessians are homogeneous in the scalar field. -/
theorem localCovariantScalarJet_hessian_smul
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (scalar : Real)
    (field : SmoothScalarField period hPeriod)
    (coordinate : Vector4) :
    (localCovariantScalarJet period hPeriod metric patch
      (scalar • field) coordinate).hessian =
      scalar •
        (localCovariantScalarJet period hPeriod metric patch field coordinate).hessian := by
  ext firstIndex secondIndex
  simp only [localCovariantScalarJet, coordinateScalarJetNormalForm,
    coordinateCovariantHessian, localCoordinateScalarJet]
  rw [localScalarPartialGradient_smul, localScalarGradient_smul]
  simp only [Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  simp only [coordinateCovariantHessian, localCoordinateScalarJet]
  have hSum : (∑ upper,
      (localLeviCivitaConnectionJet period hPeriod metric patch coordinate).christoffel
          upper firstIndex secondIndex *
        (scalar * localScalarGradient period hPeriod field patch coordinate upper)) =
      scalar * ∑ upper,
        (localLeviCivitaConnectionJet period hPeriod metric patch coordinate).christoffel
          upper firstIndex secondIndex *
        localScalarGradient period hPeriod field patch coordinate upper := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro upper _
    ring
  rw [hSum]
  ring

/-- The local covariant wave contraction is additive. -/
theorem localCovariantScalarWave_add
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (first second : SmoothScalarField period hPeriod)
    (coordinate : Vector4) :
    covariantScalarJetWave
        (localFixedSignMetric period hPeriod metric patch coordinate)
        (localCovariantScalarJet period hPeriod metric patch
          (first + second) coordinate) =
      covariantScalarJetWave
          (localFixedSignMetric period hPeriod metric patch coordinate)
          (localCovariantScalarJet period hPeriod metric patch first coordinate) +
        covariantScalarJetWave
          (localFixedSignMetric period hPeriod metric patch coordinate)
          (localCovariantScalarJet period hPeriod metric patch second coordinate) := by
  unfold covariantScalarJetWave
  rw [localCovariantScalarJet_hessian_add]
  simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib]

/-- The local covariant wave contraction is homogeneous. -/
theorem localCovariantScalarWave_smul
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (scalar : Real)
    (field : SmoothScalarField period hPeriod)
    (coordinate : Vector4) :
    covariantScalarJetWave
        (localFixedSignMetric period hPeriod metric patch coordinate)
        (localCovariantScalarJet period hPeriod metric patch
          (scalar • field) coordinate) =
      scalar * covariantScalarJetWave
        (localFixedSignMetric period hPeriod metric patch coordinate)
        (localCovariantScalarJet period hPeriod metric patch field coordinate) := by
  unfold covariantScalarJetWave
  rw [localCovariantScalarJet_hessian_smul]
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro firstIndex _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro secondIndex _
  ring

/-- The zero-source local Euler residual is additive. -/
theorem localSmoothScalarEulerResidual_add_zeroSource
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (massSquared : Real)
    (first second : SmoothScalarField period hPeriod)
    (coordinate : Vector4) :
    localSmoothScalarEulerResidual period hPeriod metric patch
        (first + second) massSquared 0 coordinate =
      localSmoothScalarEulerResidual period hPeriod metric patch
          first massSquared 0 coordinate +
        localSmoothScalarEulerResidual period hPeriod metric patch
          second massSquared 0 coordinate := by
  unfold localSmoothScalarEulerResidual covariantScalarStressEulerResidual
    pointwiseScalarPotentialSlope
  rw [localCovariantScalarWave_add]
  rw [localScalarRepresentative_add]
  simp only [Pi.add_apply]
  ring

/-- The zero-source local Euler residual is homogeneous. -/
theorem localSmoothScalarEulerResidual_smul_zeroSource
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (massSquared scalar : Real)
    (field : SmoothScalarField period hPeriod)
    (coordinate : Vector4) :
    localSmoothScalarEulerResidual period hPeriod metric patch
        (scalar • field) massSquared 0 coordinate =
      scalar * localSmoothScalarEulerResidual period hPeriod metric patch
        field massSquared 0 coordinate := by
  unfold localSmoothScalarEulerResidual covariantScalarStressEulerResidual
    pointwiseScalarPotentialSlope
  rw [localCovariantScalarWave_smul]
  rw [localScalarRepresentative_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- The concrete physical atlas residual is additive. -/
theorem canonicalPhysicalScalarEulerAtlasResidual_add
    (massSquared : Real)
    (first second : SmoothScalarField period hPeriod) :
    canonicalPhysicalScalarEulerAtlasResidual period hPeriod massSquared
        (first + second) =
      canonicalPhysicalScalarEulerAtlasResidual period hPeriod massSquared first +
        canonicalPhysicalScalarEulerAtlasResidual period hPeriod massSquared second := by
  funext patch coordinate
  exact localSmoothScalarEulerResidual_add_zeroSource
    period hPeriod (intrinsicSmoothGeneralLorentzMetric period hPeriod)
      patch massSquared first second coordinate

/-- The concrete physical atlas residual is homogeneous. -/
theorem canonicalPhysicalScalarEulerAtlasResidual_smul
    (massSquared scalar : Real)
    (field : SmoothScalarField period hPeriod) :
    canonicalPhysicalScalarEulerAtlasResidual period hPeriod massSquared
        (scalar • field) =
      scalar • canonicalPhysicalScalarEulerAtlasResidual
        period hPeriod massSquared field := by
  funext patch coordinate
  exact localSmoothScalarEulerResidual_smul_zeroSource
    period hPeriod (intrinsicSmoothGeneralLorentzMetric period hPeriod)
      patch massSquared scalar field coordinate

/-- Atlas residual as a genuine linear map. -/
def canonicalPhysicalScalarEulerAtlasLinearMap
    (massSquared : Real) :
    SmoothScalarField period hPeriod →ₗ[Real]
      CanonicalPhysicalScalarEulerAtlasTarget period hPeriod where
  toFun := canonicalPhysicalScalarEulerAtlasResidual
    period hPeriod massSquared
  map_add' := canonicalPhysicalScalarEulerAtlasResidual_add
    period hPeriod massSquared
  map_smul' := canonicalPhysicalScalarEulerAtlasResidual_smul
    period hPeriod massSquared

/-- The selected global residual is additive. -/
theorem canonicalPhysicalScalarEulerGlobalResidual_add
    (massSquared : Real)
    (first second : SmoothScalarField period hPeriod) :
    canonicalPhysicalScalarEulerGlobalResidual period hPeriod massSquared
        (first + second) =
      canonicalPhysicalScalarEulerGlobalResidual period hPeriod massSquared first +
        canonicalPhysicalScalarEulerGlobalResidual period hPeriod massSquared second := by
  funext point
  unfold canonicalPhysicalScalarEulerGlobalResidual
  exact congrFun (congrFun
    (canonicalPhysicalScalarEulerAtlasResidual_add
      period hPeriod massSquared first second)
    (canonicalPhysicalScalarEulerChartWitness period hPeriod point).patch)
    (canonicalPhysicalScalarEulerChartWitness period hPeriod point).coordinate

/-- The selected global residual is homogeneous. -/
theorem canonicalPhysicalScalarEulerGlobalResidual_smul
    (massSquared scalar : Real)
    (field : SmoothScalarField period hPeriod) :
    canonicalPhysicalScalarEulerGlobalResidual period hPeriod massSquared
        (scalar • field) =
      scalar • canonicalPhysicalScalarEulerGlobalResidual
        period hPeriod massSquared field := by
  funext point
  unfold canonicalPhysicalScalarEulerGlobalResidual
  exact congrFun (congrFun
    (canonicalPhysicalScalarEulerAtlasResidual_smul
      period hPeriod massSquared scalar field)
    (canonicalPhysicalScalarEulerChartWitness period hPeriod point).patch)
    (canonicalPhysicalScalarEulerChartWitness period hPeriod point).coordinate

/-- Globalization data now contain only geometric compatibility and continuity. -/
structure CanonicalPhysicalScalarEulerGlobalizationData
    (massSquared : Real) where
  compatible : ∀ field : SmoothScalarField period hPeriod,
    CanonicalPhysicalScalarEulerAtlasCompatible
      period hPeriod massSquared field
  continuous : ∀ field : SmoothScalarField period hPeriod,
    Continuous (canonicalPhysicalScalarEulerGlobalResidual
      period hPeriod massSquared field)
  ae_zero_eq_zero : ∀ field : SmoothScalarField period hPeriod,
    canonicalPhysicalScalarEulerGlobalResidual
        period hPeriod massSquared field =ᵐ[
          intrinsicCanonicalLorentzVolumeMeasure period hPeriod] 0 →
      canonicalPhysicalScalarEulerGlobalResidual
        period hPeriod massSquared field = 0

namespace CanonicalPhysicalScalarEulerGlobalizationData

variable {period : Real} {hPeriod : period ≠ 0} {massSquared : Real}

/-- Conversion to the original operator-data interface, with linearity filled
by theorem. -/
def toOperatorData
    (globalization : CanonicalPhysicalScalarEulerGlobalizationData
      period hPeriod massSquared) :
    CanonicalPhysicalScalarEulerGlobalOperatorData
      period hPeriod massSquared where
  compatible := globalization.compatible
  continuous := globalization.continuous
  ae_zero_eq_zero := globalization.ae_zero_eq_zero
  map_add := canonicalPhysicalScalarEulerGlobalResidual_add
    period hPeriod massSquared
  map_smul := canonicalPhysicalScalarEulerGlobalResidual_smul
    period hPeriod massSquared

/-- Genuine physical bulk-L2 Euler operator from compatibility and continuity
alone. -/
def toBulkL2LinearMap
    (globalization : CanonicalPhysicalScalarEulerGlobalizationData
      period hPeriod massSquared) :
    SmoothScalarField period hPeriod →ₗ[Real]
      CanonicalPhysicalBulkL2 period hPeriod :=
  globalization.toOperatorData.toBulkL2LinearMap

/-- Euler equation is the zero set of the constructed L2 operator. -/
theorem eulerEquation_iff_operator_eq_zero
    (globalization : CanonicalPhysicalScalarEulerGlobalizationData
      period hPeriod massSquared)
    (field : SmoothScalarField period hPeriod) :
    CanonicalPhysicalScalarEulerEquation period hPeriod massSquared field ↔
      globalization.toBulkL2LinearMap field = 0 :=
  globalization.toOperatorData.eulerEquation_iff_operator_eq_zero field

/-- Linearity-closure certificate. -/
theorem certificate
    (globalization : CanonicalPhysicalScalarEulerGlobalizationData
      period hPeriod massSquared) :
    (∀ first second : SmoothScalarField period hPeriod,
      canonicalPhysicalScalarEulerGlobalResidual period hPeriod massSquared
          (first + second) =
        canonicalPhysicalScalarEulerGlobalResidual period hPeriod massSquared first +
          canonicalPhysicalScalarEulerGlobalResidual period hPeriod massSquared second) ∧
      (∀ (scalar : Real) (field : SmoothScalarField period hPeriod),
        canonicalPhysicalScalarEulerGlobalResidual period hPeriod massSquared
            (scalar • field) =
          scalar • canonicalPhysicalScalarEulerGlobalResidual
            period hPeriod massSquared field) :=
  ⟨canonicalPhysicalScalarEulerGlobalResidual_add period hPeriod massSquared,
    canonicalPhysicalScalarEulerGlobalResidual_smul period hPeriod massSquared⟩

end CanonicalPhysicalScalarEulerGlobalizationData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerLinearity4D
end JanusFormal
