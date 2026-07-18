import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusDiagonalDiffeomorphismAction4D

/-!
# General symmetric covariant tensors on the effective D8 quotient

This gate builds the intrinsic smooth covariant rank-two tensor space on the
actual quotient.  Tensorial pullback and the nondegenerate/Lorentz domains are
kept separate from fixed-frame coefficient matrices.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGeneralLorentzTensor4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothDiagonalLorentzFields4D
open P0EFTJanusMappingTorusDiagonalDiffeomorphismAction4D

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
  TangentFiber period hPeriod point →L[Real] CotangentFiber period hPeriod point

private abbrev CovariantTwoTensorModel :=
  CoverCoordinates →L[Real] CoverCoordinates →L[Real] Real

/-- Genuine smooth covariant rank-two tensor fields on the quotient tangent
bundle. -/
abbrev SmoothCovariantTwoTensor :=
  ContMDiffSection coverModelWithCorners CovariantTwoTensorModel ∞
    (CovariantTwoTensorFiber period hPeriod)

/-- A covariant rank-two tensor field before imposing smoothness. -/
abbrev CovariantTwoTensorField :=
  ∀ point, CovariantTwoTensorFiber period hPeriod point

def SmoothCovariantTwoTensor.toTensorField
    (tensor : SmoothCovariantTwoTensor period hPeriod) :
    CovariantTwoTensorField period hPeriod :=
  fun point => tensor point

/-- Pointwise symmetry of an intrinsic covariant two-tensor. -/
def IsSymmetric
    (tensor : SmoothCovariantTwoTensor period hPeriod) : Prop :=
  ∀ point first second,
    tensor point first second = tensor point second first

/-- Smooth symmetric covariant rank-two tensor fields. -/
structure SmoothSymmetricCovariantTwoTensor where
  tensor : SmoothCovariantTwoTensor period hPeriod
  symmetric : IsSymmetric period hPeriod tensor

@[ext]
theorem SmoothSymmetricCovariantTwoTensor.ext
    {first second : SmoothSymmetricCovariantTwoTensor period hPeriod}
    (hTensor : first.tensor = second.tensor) : first = second := by
  cases first
  cases second
  cases hTensor
  rfl

/-- The zero tensor shows that the unrestricted smooth symmetric tensor space
is nonempty; no nondegeneracy claim is attached to this witness. -/
def zeroSymmetricTensor :
    SmoothSymmetricCovariantTwoTensor period hPeriod where
  tensor := 0
  symmetric := by
    intro point first second
    rfl

theorem smoothSymmetricCovariantTwoTensor_nonempty :
    Nonempty (SmoothSymmetricCovariantTwoTensor period hPeriod) :=
  ⟨zeroSymmetricTensor period hPeriod⟩

/-- Fiberwise tensorial pullback formula.  Both tangent arguments are moved by
the actual manifold derivative. -/
def pullbackTensorValue
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (tensor : CovariantTwoTensorField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    CovariantTwoTensorFiber period hPeriod point :=
  let derivative := diffeomorphism.mfderivToContinuousLinearEquiv
    (I := coverModelWithCorners) (J := coverModelWithCorners) (by simp) point
  let covectorPullback := derivative.symm.arrowCongr
    (ContinuousLinearEquiv.refl Real Real)
  derivative.symm.arrowCongr covectorPullback
    (tensor (diffeomorphism point))

@[simp]
theorem pullbackTensorValue_apply
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (tensor : CovariantTwoTensorField period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (first second : TangentFiber period hPeriod point) :
    pullbackTensorValue period hPeriod diffeomorphism tensor point first second =
      tensor (diffeomorphism point)
        (mfderiv coverModelWithCorners coverModelWithCorners
          diffeomorphism point first)
        (mfderiv coverModelWithCorners coverModelWithCorners
          diffeomorphism point second) :=
  rfl

theorem pullbackTensorValue_symmetric
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (tensor : CovariantTwoTensorField period hPeriod)
    (hTensor : ∀ point first second,
      tensor point first second = tensor point second first)
    (point : EffectiveQuotient period hPeriod)
    (first second : TangentFiber period hPeriod point) :
    pullbackTensorValue period hPeriod diffeomorphism tensor point first second =
      pullbackTensorValue period hPeriod diffeomorphism tensor point second first := by
  simp only [pullbackTensorValue_apply]
  exact hTensor _ _ _

/-- Algebraic nondegeneracy of one covariant tensor fiber. -/
def FiberIsNondegenerate
    {point : EffectiveQuotient period hPeriod}
    (tensor : CovariantTwoTensorFiber period hPeriod point) : Prop :=
  Function.Injective tensor

/-- Algebraic nondegeneracy of the metric map into the cotangent fiber. -/
def IsNondegenerateAt
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) : Prop :=
  FiberIsNondegenerate period hPeriod (tensor.tensor point)

def IsEverywhereNondegenerate
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) : Prop :=
  ∀ point, IsNondegenerateAt period hPeriod tensor point

/-- The model Minkowski pairing, with the real mapping-torus direction as the
single timelike coordinate. -/
def modelMinkowskiPair (first second : CoverCoordinates) : Real :=
  @inner Real (EuclideanSpace Real (Fin 3)) _ first.1 second.1 -
    first.2 * second.2

/-- Lorentz inertia `(3,1)` for one covariant tensor fiber. -/
def FiberIsLorentzian
    {point : EffectiveQuotient period hPeriod}
    (tensor : CovariantTwoTensorFiber period hPeriod point) : Prop :=
  ∃ frame : TangentFiber period hPeriod point ≃L[Real] CoverCoordinates,
    ∀ first second,
      tensor first second = modelMinkowskiPair (frame first) (frame second)

/-- A symmetric tensor is Lorentzian at a point precisely when a continuous
linear frame identifies it with the model form of inertia `(3,1)`. -/
def IsLorentzianAt
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) : Prop :=
  FiberIsLorentzian period hPeriod (tensor.tensor point)

def IsEverywhereLorentzian
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) : Prop :=
  ∀ point, IsLorentzianAt period hPeriod tensor point

/-- Diffeomorphism pullback preserves fiberwise nondegeneracy. -/
theorem pullbackTensorValue_nondegenerate
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (tensor : CovariantTwoTensorField period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (hTensor : FiberIsNondegenerate period hPeriod
      (tensor (diffeomorphism point))) :
    FiberIsNondegenerate period hPeriod
      (pullbackTensorValue period hPeriod diffeomorphism tensor point) := by
  let derivative := diffeomorphism.mfderivToContinuousLinearEquiv
    (I := coverModelWithCorners) (J := coverModelWithCorners) (by simp) point
  have hDerivative :
      (derivative : TangentFiber period hPeriod point →L[Real]
        TangentFiber period hPeriod (diffeomorphism point)) =
        mfderiv coverModelWithCorners coverModelWithCorners
          diffeomorphism point :=
    Diffeomorph.mfderivToContinuousLinearEquiv_coe diffeomorphism (by simp)
  intro first second hEqual
  apply derivative.injective
  apply hTensor
  apply ContinuousLinearMap.ext
  intro tangent
  obtain ⟨preimage, rfl⟩ := derivative.surjective tangent
  have hEvaluation := congrArg (fun covector => covector preimage) hEqual
  have hDerivativeApply (vector : TangentFiber period hPeriod point) :
      derivative vector = mfderiv coverModelWithCorners coverModelWithCorners
        diffeomorphism point vector :=
    DFunLike.congr_fun hDerivative vector
  rw [hDerivativeApply first, hDerivativeApply second,
    hDerivativeApply preimage]
  simpa only [pullbackTensorValue_apply] using hEvaluation

/-- Diffeomorphism pullback preserves Lorentz inertia. -/
theorem pullbackTensorValue_lorentzian
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (tensor : CovariantTwoTensorField period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (hTensor : FiberIsLorentzian period hPeriod
      (tensor (diffeomorphism point))) :
    FiberIsLorentzian period hPeriod
      (pullbackTensorValue period hPeriod diffeomorphism tensor point) := by
  let derivative := diffeomorphism.mfderivToContinuousLinearEquiv
    (I := coverModelWithCorners) (J := coverModelWithCorners) (by simp) point
  rcases hTensor with ⟨frame, hFrame⟩
  refine ⟨derivative.trans frame, ?_⟩
  intro first second
  rw [pullbackTensorValue_apply]
  change tensor (diffeomorphism point) (derivative first) (derivative second) = _
  rw [hFrame]
  rfl

end

end P0EFTJanusMappingTorusGeneralLorentzTensor4D
end JanusFormal
