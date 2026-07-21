import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkAmbientTensorPullback4D

/-!
# Lorentz algebra of the ambient tensor pullback on the cut bulk
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkAmbientTensorPullbackLorentz4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusCutBulkGlobalChartedSpace4D
open P0EFTJanusMappingTorusCutBulkGlobalIsManifold4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusCutBulkAmbientTensorPullback4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance quotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance cutBulkChartedSpace :
    ChartedSpace CutCollarModel
      (PositiveHemisphereCutBulk period hPeriod) :=
  cutBulkGlobalChartedSpace period hPeriod

abbrev AmbientTangentFiber
    (point : PositiveHemisphereCutBulk period hPeriod) :=
  TangentSpace coverModelWithCorners (cutBulkToAmbient period hPeriod point)

/-- The remaining geometric condition needed to transport Lorentz inertia. -/
def CutBulkDerivativeIsomorphismAt
    (point : PositiveHemisphereCutBulk period hPeriod) : Prop :=
  ∃ derivative : CutBulkTangentFiber period hPeriod point ≃L[Real]
      AmbientTangentFiber period hPeriod point,
    (derivative : CutBulkTangentFiber period hPeriod point →L[Real]
      AmbientTangentFiber period hPeriod point) =
      mfderiv cutCollarModelWithCorners coverModelWithCorners
        (cutBulkToAmbient period hPeriod) point

def CutBulkFiberIsNondegenerate
    {point : PositiveHemisphereCutBulk period hPeriod}
    (tensor : CutBulkCovariantTwoTensorFiber period hPeriod point) : Prop :=
  Function.Injective tensor

def CutBulkFiberIsLorentzian
    {point : PositiveHemisphereCutBulk period hPeriod}
    (tensor : CutBulkCovariantTwoTensorFiber period hPeriod point) : Prop :=
  ∃ frame : CutBulkTangentFiber period hPeriod point ≃L[Real] CoverCoordinates,
    ∀ first second,
      tensor first second = modelMinkowskiPair (frame first) (frame second)

theorem cutBulkAmbientTensorPullback_nondegenerate
    (tensor : CovariantTwoTensorField period hPeriod)
    (point : PositiveHemisphereCutBulk period hPeriod)
    (hDerivative : CutBulkDerivativeIsomorphismAt period hPeriod point)
    (hTensor : FiberIsNondegenerate period hPeriod
      (tensor (cutBulkToAmbient period hPeriod point))) :
    CutBulkFiberIsNondegenerate period hPeriod
      (cutBulkAmbientTensorPullback period hPeriod tensor point) := by
  rcases hDerivative with ⟨derivative, hDerivative⟩
  intro first second hEqual
  apply derivative.injective
  apply hTensor
  apply ContinuousLinearMap.ext
  intro tangent
  obtain ⟨preimage, rfl⟩ := derivative.surjective tangent
  have hEvaluation := congrArg (fun covector => covector preimage) hEqual
  have hApply (vector : CutBulkTangentFiber period hPeriod point) :
      derivative vector =
        mfderiv cutCollarModelWithCorners coverModelWithCorners
          (cutBulkToAmbient period hPeriod) point vector :=
    DFunLike.congr_fun hDerivative vector
  rw [hApply first, hApply second, hApply preimage]
  simpa only [cutBulkAmbientTensorPullback_apply] using hEvaluation

theorem cutBulkAmbientTensorPullback_lorentzian
    (tensor : CovariantTwoTensorField period hPeriod)
    (point : PositiveHemisphereCutBulk period hPeriod)
    (hDerivative : CutBulkDerivativeIsomorphismAt period hPeriod point)
    (hTensor : FiberIsLorentzian period hPeriod
      (tensor (cutBulkToAmbient period hPeriod point))) :
    CutBulkFiberIsLorentzian period hPeriod
      (cutBulkAmbientTensorPullback period hPeriod tensor point) := by
  rcases hDerivative with ⟨derivative, hDerivative⟩
  rcases hTensor with ⟨frame, hFrame⟩
  refine ⟨derivative.trans frame, ?_⟩
  intro first second
  rw [cutBulkAmbientTensorPullback_apply, ← hDerivative]
  exact hFrame _ _

end
end P0EFTJanusMappingTorusCutBulkAmbientTensorPullbackLorentz4D
end JanusFormal
