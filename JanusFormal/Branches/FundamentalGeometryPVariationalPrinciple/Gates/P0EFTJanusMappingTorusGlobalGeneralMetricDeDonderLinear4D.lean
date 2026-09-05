import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalGeneralMetricDeDonder4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCompleteVariationModuleCore4D

/-
Copyright (c) 2026 JanusFormal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JanusFormal
-/

/-!
# Linear global de Donder operator

The already constructed smooth global de Donder one-form is linear in the
genuine smooth symmetric metric perturbation.  This gate proves linearity
from the local coefficient derivative, covariant derivative, contracted
divergence and smooth trace bricks, then bundles the result as a `LinearMap`.

No topology on the raw smooth-section space, formal adjoint, Green identity
or Fredholm claim is introduced here.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGlobalGeneralMetricDeDonder4D

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralMetricSymmetricTensorCovariantDerivative4D
open P0EFTJanusMappingTorusGeneralMetricSymmetricTensorDivergence4D
open P0EFTJanusMappingTorusGeneralMetricSymmetricTensorDivergenceIntrinsic4D
open P0EFTJanusMappingTorusGlobalGeneralMetricSymmetricTensorDivergence4D
open P0EFTJanusMappingTorusGeneralMetricSmoothTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlas4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusEffectiveD8SmoothCovectorFieldFunctor4D
open P0EFTJanusCompleteVariationModuleCore4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev LinearEffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev LinearVector4 :=
  P0EFTJanusMappingTorusGeneralMetricSymmetricTensorCovariantDerivative4D.Vector4

private abbrev LinearIndex4 :=
  P0EFTJanusMappingTorusGeneralMetricSymmetricTensorCovariantDerivative4D.Index4

local instance linearEffectiveQuotientChartedSpace :
    ChartedSpace CoverModel (LinearEffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance linearEffectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (LinearEffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private theorem localCoefficient_add
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstIndex secondIndex : LinearIndex4) :
    localSymmetricTensorCoefficient period hPeriod (first + second) patch
        firstIndex secondIndex =
      localSymmetricTensorCoefficient period hPeriod first patch
          firstIndex secondIndex +
        localSymmetricTensorCoefficient period hPeriod second patch
          firstIndex secondIndex := by
  rfl

private theorem localCoefficient_smul
    (scalar : Real)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstIndex secondIndex : LinearIndex4) :
    localSymmetricTensorCoefficient period hPeriod (scalar • tensor) patch
        firstIndex secondIndex =
      scalar • localSymmetricTensorCoefficient period hPeriod tensor patch
        firstIndex secondIndex := by
  rfl

private theorem localDerivative_add
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : LinearVector4)
    (derivative firstIndex secondIndex : LinearIndex4) :
    localSymmetricTensorDerivative period hPeriod (first + second) patch
        coordinate derivative firstIndex secondIndex =
      localSymmetricTensorDerivative period hPeriod first patch coordinate
          derivative firstIndex secondIndex +
        localSymmetricTensorDerivative period hPeriod second patch coordinate
          derivative firstIndex secondIndex := by
  unfold localSymmetricTensorDerivative
  rw [localCoefficient_add]
  rw [fderiv_add
    ((localSymmetricTensorCoefficient_contDiff period hPeriod first patch
      firstIndex secondIndex).differentiable (by simp)).differentiableAt
    ((localSymmetricTensorCoefficient_contDiff period hPeriod second patch
      firstIndex secondIndex).differentiable (by simp)).differentiableAt]
  rfl

private theorem localDerivative_smul
    (scalar : Real)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : LinearVector4)
    (derivative firstIndex secondIndex : LinearIndex4) :
    localSymmetricTensorDerivative period hPeriod (scalar • tensor) patch
        coordinate derivative firstIndex secondIndex =
      scalar • localSymmetricTensorDerivative period hPeriod tensor patch
        coordinate derivative firstIndex secondIndex := by
  unfold localSymmetricTensorDerivative
  rw [localCoefficient_smul]
  rw [fderiv_const_smul_field]
  rfl

private theorem localCovariantDerivative_add
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : LinearVector4)
    (derivative firstIndex secondIndex : LinearIndex4) :
    localSymmetricTensorCovariantDerivative period hPeriod metric
        (first + second) patch coordinate derivative firstIndex secondIndex =
      localSymmetricTensorCovariantDerivative period hPeriod metric first patch
          coordinate derivative firstIndex secondIndex +
        localSymmetricTensorCovariantDerivative period hPeriod metric second
          patch coordinate derivative firstIndex secondIndex := by
  simp only [localSymmetricTensorCovariantDerivative, localDerivative_add,
    localCoefficient_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  ring

private theorem localCovariantDerivative_smul
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (scalar : Real)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : LinearVector4)
    (derivative firstIndex secondIndex : LinearIndex4) :
    localSymmetricTensorCovariantDerivative period hPeriod metric
        (scalar • tensor) patch coordinate derivative firstIndex secondIndex =
      scalar • localSymmetricTensorCovariantDerivative period hPeriod metric
        tensor patch coordinate derivative firstIndex secondIndex := by
  simp only [localSymmetricTensorCovariantDerivative, localDerivative_smul,
    localCoefficient_smul, Pi.smul_apply, smul_eq_mul]
  ring_nf
  simp only [Finset.mul_sum]
  ring_nf

private theorem localDivergenceCoefficient_add
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : LinearVector4) (last : LinearIndex4) :
    localSymmetricTensorDivergenceCoefficient period hPeriod metric
        (first + second) patch coordinate last =
      localSymmetricTensorDivergenceCoefficient period hPeriod metric first
          patch coordinate last +
        localSymmetricTensorDivergenceCoefficient period hPeriod metric second
          patch coordinate last := by
  simp only [localSymmetricTensorDivergenceCoefficient,
    localCovariantDerivative_add, mul_add, Finset.sum_add_distrib]

private theorem localDivergenceCoefficient_smul
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (scalar : Real)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : LinearVector4) (last : LinearIndex4) :
    localSymmetricTensorDivergenceCoefficient period hPeriod metric
        (scalar • tensor) patch coordinate last =
      scalar • localSymmetricTensorDivergenceCoefficient period hPeriod metric
        tensor patch coordinate last := by
  simp only [localSymmetricTensorDivergenceCoefficient,
    localCovariantDerivative_smul, smul_eq_mul]
  calc
    (∑ derivative : LinearIndex4, ∑ firstIndex : LinearIndex4,
        (localMetricMatrix period hPeriod metric patch coordinate)⁻¹
            derivative firstIndex *
          (scalar *
            localSymmetricTensorCovariantDerivative period hPeriod metric
              tensor patch coordinate derivative firstIndex last)) =
        ∑ derivative : LinearIndex4, ∑ firstIndex : LinearIndex4,
          scalar *
            ((localMetricMatrix period hPeriod metric patch coordinate)⁻¹
                derivative firstIndex *
              localSymmetricTensorCovariantDerivative period hPeriod metric
                tensor patch coordinate derivative firstIndex last) := by
      apply Finset.sum_congr rfl
      intro derivative _
      apply Finset.sum_congr rfl
      intro firstIndex _
      ring
    _ = _ := by
      simp only [Finset.mul_sum]

private theorem localDivergenceModelCovector_add
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : LinearVector4) :
    localSymmetricTensorDivergenceModelCovector period hPeriod metric
        (first + second) patch coordinate =
      localSymmetricTensorDivergenceModelCovector period hPeriod metric first
          patch coordinate +
        localSymmetricTensorDivergenceModelCovector period hPeriod metric second
          patch coordinate := by
  apply ContinuousLinearMap.ext
  intro vector
  simp only [localSymmetricTensorDivergenceModelCovector, add_apply]
  change
    (∑ last : LinearIndex4,
      localSymmetricTensorDivergenceCoefficient period hPeriod metric
        (first + second) patch coordinate last * vector last) =
      (∑ last : LinearIndex4,
        localSymmetricTensorDivergenceCoefficient period hPeriod metric first
          patch coordinate last * vector last) +
      ∑ last : LinearIndex4,
        localSymmetricTensorDivergenceCoefficient period hPeriod metric second
          patch coordinate last * vector last
  simp_rw [localDivergenceCoefficient_add]
  simp only [add_mul, Finset.sum_add_distrib]

private theorem localDivergenceModelCovector_smul
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (scalar : Real)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : LinearVector4) :
    localSymmetricTensorDivergenceModelCovector period hPeriod metric
        (scalar • tensor) patch coordinate =
      scalar • localSymmetricTensorDivergenceModelCovector period hPeriod metric
        tensor patch coordinate := by
  apply ContinuousLinearMap.ext
  intro vector
  simp only [localSymmetricTensorDivergenceModelCovector, smul_apply]
  change
    (∑ last : LinearIndex4,
      localSymmetricTensorDivergenceCoefficient period hPeriod metric
        (scalar • tensor) patch coordinate last * vector last) =
      scalar *
        ∑ last : LinearIndex4,
          localSymmetricTensorDivergenceCoefficient period hPeriod metric tensor
            patch coordinate last * vector last
  simp_rw [localDivergenceCoefficient_smul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro last _
  ring

private theorem localDivergenceIntrinsicCovector_add
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : LinearVector4) :
    localSymmetricTensorDivergenceIntrinsicCovector period hPeriod metric
        (first + second) patch coordinate =
      localSymmetricTensorDivergenceIntrinsicCovector period hPeriod metric first
          patch coordinate +
        localSymmetricTensorDivergenceIntrinsicCovector period hPeriod metric
          second patch coordinate := by
  apply ContinuousLinearMap.ext
  intro vector
  unfold localSymmetricTensorDivergenceIntrinsicCovector
  change
    localSymmetricTensorDivergenceModelCovector period hPeriod metric
        (first + second) patch coordinate _ =
      localSymmetricTensorDivergenceModelCovector period hPeriod metric first
          patch coordinate _ +
        localSymmetricTensorDivergenceModelCovector period hPeriod metric second
          patch coordinate _
  rw [localDivergenceModelCovector_add]
  rfl

private theorem localDivergenceIntrinsicCovector_smul
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (scalar : Real)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : LinearVector4) :
    localSymmetricTensorDivergenceIntrinsicCovector period hPeriod metric
        (scalar • tensor) patch coordinate =
      scalar • localSymmetricTensorDivergenceIntrinsicCovector period hPeriod
        metric tensor patch coordinate := by
  apply ContinuousLinearMap.ext
  intro vector
  unfold localSymmetricTensorDivergenceIntrinsicCovector
  change
    localSymmetricTensorDivergenceModelCovector period hPeriod metric
        (scalar • tensor) patch coordinate _ =
      scalar *
        localSymmetricTensorDivergenceModelCovector period hPeriod metric tensor
          patch coordinate _
  rw [localDivergenceModelCovector_smul]
  rfl

private theorem globalDivergenceAt_add
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : LinearEffectiveQuotient period hPeriod) :
    globalGeneralMetricSymmetricTensorDivergenceAt period hPeriod metric
        (first + second) point =
      globalGeneralMetricSymmetricTensorDivergenceAt period hPeriod metric first
          point +
        globalGeneralMetricSymmetricTensorDivergenceAt period hPeriod metric
          second point := by
  let witness :=
    canonicalPhysicalScalarEulerChartWitness period hPeriod point
  rw [← witness.coordinate_eq]
  rw [globalGeneralMetricSymmetricTensorDivergenceAt_eq_local,
    globalGeneralMetricSymmetricTensorDivergenceAt_eq_local,
    globalGeneralMetricSymmetricTensorDivergenceAt_eq_local]
  exact localDivergenceIntrinsicCovector_add period hPeriod metric first second
    witness.patch witness.coordinate

private theorem globalDivergenceAt_smul
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (scalar : Real)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : LinearEffectiveQuotient period hPeriod) :
    globalGeneralMetricSymmetricTensorDivergenceAt period hPeriod metric
        (scalar • tensor) point =
      scalar • globalGeneralMetricSymmetricTensorDivergenceAt period hPeriod
        metric tensor point := by
  let witness :=
    canonicalPhysicalScalarEulerChartWitness period hPeriod point
  rw [← witness.coordinate_eq]
  rw [globalGeneralMetricSymmetricTensorDivergenceAt_eq_local,
    globalGeneralMetricSymmetricTensorDivergenceAt_eq_local]
  exact localDivergenceIntrinsicCovector_smul period hPeriod metric scalar tensor
    witness.patch witness.coordinate

private theorem globalDivergence_add
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    globalGeneralMetricSymmetricTensorDivergence period hPeriod metric
        (first + second) =
      globalGeneralMetricSymmetricTensorDivergence period hPeriod metric first +
        globalGeneralMetricSymmetricTensorDivergence period hPeriod metric
          second := by
  apply ContMDiffSection.ext
  intro point
  exact globalDivergenceAt_add period hPeriod metric first second point

private theorem globalDivergence_smul
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (scalar : Real)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    globalGeneralMetricSymmetricTensorDivergence period hPeriod metric
        (scalar • tensor) =
      scalar • globalGeneralMetricSymmetricTensorDivergence period hPeriod
        metric tensor := by
  apply ContMDiffSection.ext
  intro point
  exact globalDivergenceAt_smul period hPeriod metric scalar tensor point

private theorem tensor_add_eq_smoothTensorAdd
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    first + second =
      smoothSymmetricTensorAdd period hPeriod first second := by
  apply SmoothSymmetricCovariantTwoTensor.ext
  rfl

private theorem tensor_smul_eq_smoothTensorSMul
    (scalar : Real)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    scalar • tensor =
      smoothSymmetricTensorSMul period hPeriod scalar tensor := by
  apply SmoothSymmetricCovariantTwoTensor.ext
  rfl

private theorem traceAt_add
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : LinearEffectiveQuotient period hPeriod) :
    generalMetricTensorTraceAt period hPeriod metric (first + second) point =
      generalMetricTensorTraceAt period hPeriod metric first point +
        generalMetricTensorTraceAt period hPeriod metric second point := by
  rw [tensor_add_eq_smoothTensorAdd,
    generalMetricTensorTraceAt_add]

private theorem traceAt_smul
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (scalar : Real)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : LinearEffectiveQuotient period hPeriod) :
    generalMetricTensorTraceAt period hPeriod metric (scalar • tensor) point =
      scalar • generalMetricTensorTraceAt period hPeriod metric tensor point := by
  rw [tensor_smul_eq_smoothTensorSMul,
    generalMetricTensorTraceAt_smul]
  rfl

private theorem traceDifferential_add
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    generalMetricTensorTraceDifferential period hPeriod metric
        (first + second) =
      generalMetricTensorTraceDifferential period hPeriod metric first +
        generalMetricTensorTraceDifferential period hPeriod metric second := by
  apply ContMDiffSection.ext
  intro point
  change mfderiv coverModelWithCorners _
    (generalMetricTensorTrace period hPeriod metric (first + second)).toFun
      point = _
  have hFunction :
      (generalMetricTensorTrace period hPeriod metric
          (first + second)).toFun =
        (generalMetricTensorTrace period hPeriod metric first).toFun +
          (generalMetricTensorTrace period hPeriod metric second).toFun := by
    funext current
    exact traceAt_add period hPeriod metric first second current
  rw [hFunction]
  rw [mfderiv_add
    ((generalMetricTensorTrace period hPeriod metric first).contMDiff_toFun
      |>.mdifferentiableAt (by simp))
    ((generalMetricTensorTrace period hPeriod metric second).contMDiff_toFun
      |>.mdifferentiableAt (by simp))]
  ext tangent
  rfl

private theorem traceDifferential_smul
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (scalar : Real)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    generalMetricTensorTraceDifferential period hPeriod metric
        (scalar • tensor) =
      scalar • generalMetricTensorTraceDifferential period hPeriod metric
        tensor := by
  apply ContMDiffSection.ext
  intro point
  change mfderiv coverModelWithCorners _
    (generalMetricTensorTrace period hPeriod metric
      (scalar • tensor)).toFun point = _
  have hFunction :
      (generalMetricTensorTrace period hPeriod metric
          (scalar • tensor)).toFun =
        scalar •
          (generalMetricTensorTrace period hPeriod metric tensor).toFun := by
    funext current
    exact traceAt_smul period hPeriod metric scalar tensor current
  rw [hFunction]
  rw [const_smul_mfderiv
    ((generalMetricTensorTrace period hPeriod metric tensor).contMDiff_toFun
      |>.mdifferentiableAt (by simp)) scalar]
  ext tangent
  rfl

theorem globalGeneralMetricDeDonder_add
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    globalGeneralMetricDeDonder period hPeriod metric (first + second) =
      globalGeneralMetricDeDonder period hPeriod metric first +
        globalGeneralMetricDeDonder period hPeriod metric second := by
  unfold globalGeneralMetricDeDonder generalMetricDeDonderTraceCorrection
  have hTensor : (first + second).tensor = first.tensor + second.tensor := rfl
  rw [hTensor]
  rw [globalDivergence_add, traceDifferential_add]
  module

theorem globalGeneralMetricDeDonder_smul
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (scalar : Real)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    globalGeneralMetricDeDonder period hPeriod metric (scalar • tensor) =
      scalar • globalGeneralMetricDeDonder period hPeriod metric tensor := by
  unfold globalGeneralMetricDeDonder generalMetricDeDonderTraceCorrection
  have hTensor : (scalar • tensor).tensor = scalar • tensor.tensor := rfl
  rw [hTensor]
  rw [globalDivergence_smul, traceDifferential_smul]
  module

/-- The de Donder one-form as an algebraic linear operator on genuine smooth
metric perturbations. -/
def globalGeneralMetricDeDonderLinearMap
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    SmoothSymmetricCovariantTwoTensor period hPeriod →ₗ[Real]
      EffectiveD8SmoothCovectorField
        (generalMetricDivergenceBackground period hPeriod) where
  toFun := globalGeneralMetricDeDonder period hPeriod metric
  map_add' := globalGeneralMetricDeDonder_add period hPeriod metric
  map_smul' := globalGeneralMetricDeDonder_smul period hPeriod metric

@[simp]
theorem globalGeneralMetricDeDonderLinearMap_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    globalGeneralMetricDeDonderLinearMap period hPeriod metric tensor =
      globalGeneralMetricDeDonder period hPeriod metric tensor :=
  rfl

end
end P0EFTJanusMappingTorusGlobalGeneralMetricDeDonder4D
end JanusFormal
