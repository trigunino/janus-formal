import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkCanonicalCutoffCollarDerivative4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalNormalLiftContinuityReduction4D

/-!
# Full collar differential of the genuine global cutoff
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutBulkCanonicalCutoffCollarMFDeriv4D

set_option autoImplicit false
noncomputable section

open Set Topology
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalNormalLiftContinuityReduction4D
open P0EFTJanusMappingTorusCanonicalLatitudeCutoffNormalField4D
open P0EFTJanusMappingTorusCutBulkCanonicalCollarMeasure4D
open P0EFTJanusMappingTorusCutBulkCanonicalCutoffGlobalSmooth4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance canonicalLatitudeBaseChartedSpace :
    ChartedSpace CanonicalLatitudeBaseModel CanonicalLatitudeBase := inferInstance

local instance canonicalLatitudeParameterChartedSpace :
    ChartedSpace CanonicalLatitudeParameterModel CanonicalLatitudeParameter := inferInstance

/-- Pullback of the genuine cut-bulk cutoff to the canonical collar product. -/
def cutBulkCanonicalCutoffCollarPullback
    (parameter : CanonicalLatitudeParameter) : Real :=
  cutBulkCanonicalCutoff period hPeriod
    (canonicalLatitudeCutBulkCollarMap period hPeriod parameter)

private theorem cutBulkCanonicalCutoffCollarPullback_eventuallyEq
    (base : CanonicalLatitudeBase) (normal : Real)
    (hNormal : normal ∈ Ioo (0 : Real) 1) :
    Filter.EventuallyEq (nhds (base, normal))
      (cutBulkCanonicalCutoffCollarPullback period hPeriod)
      (fun parameter : CanonicalLatitudeParameter =>
        canonicalLatitudeCollarCutoff parameter.2) := by
  have hNeighborhood :
      Prod.snd ⁻¹' Ioo (0 : Real) 1 ∈ 𝓝 (base, normal) :=
    (isOpen_Ioo.preimage continuous_snd).mem_nhds hNormal
  filter_upwards [hNeighborhood] with parameter hParameter
  exact cutBulkCanonicalCutoff_canonicalLatitudeCutBulkCollarMap
    period hPeriod parameter.1 parameter.2 ⟨hParameter.1.le, hParameter.2.le⟩

/-- The full manifold differential of the genuine cutoff pullback is the
one-dimensional bump derivative times the normal tangent component. -/
theorem mfderiv_cutBulkCanonicalCutoffCollarPullback_apply
    (base : CanonicalLatitudeBase) (normal : Real)
    (hNormal : normal ∈ Ioo (0 : Real) 1)
    (tangent : TangentSpace canonicalLatitudeParameterModelWithCorners
      (base, normal)) :
    mfderiv canonicalLatitudeParameterModelWithCorners
        (modelWithCornersSelf Real Real)
        (cutBulkCanonicalCutoffCollarPullback period hPeriod) (base, normal)
        tangent =
      deriv canonicalLatitudeCollarCutoff normal * tangent.2 := by
  have hDerivative : HasDerivAt canonicalLatitudeCollarCutoff
      (deriv canonicalLatitudeCollarCutoff normal) normal :=
    (canonicalLatitudeCollarCutoff_contDiff.differentiable
      (by simp)).differentiableAt.hasDerivAt
  calc
    _ = mfderiv canonicalLatitudeParameterModelWithCorners
        (modelWithCornersSelf Real Real)
        (fun parameter : CanonicalLatitudeParameter =>
          canonicalLatitudeCollarCutoff parameter.2) (base, normal) tangent := by
      exact DFunLike.congr_fun
        ((cutBulkCanonicalCutoffCollarPullback_eventuallyEq
          period hPeriod base normal hNormal).mfderiv_eq) tangent
    _ = mfderiv (modelWithCornersSelf Real Real)
        (modelWithCornersSelf Real Real) canonicalLatitudeCollarCutoff normal
          (mfderiv canonicalLatitudeParameterModelWithCorners
            (modelWithCornersSelf Real Real) Prod.snd (base, normal) tangent) := by
      exact mfderiv_comp_apply (base, normal)
        hDerivative.hasFDerivAt.hasMFDerivAt.mdifferentiableAt
        (mdifferentiableAt_snd
          (I := canonicalLatitudeBaseModelWithCorners)
          (I' := modelWithCornersSelf Real Real)) tangent
    _ = _ := by
      rw [mfderiv_snd, mfderiv_eq_fderiv,
        hDerivative.hasFDerivAt.fderiv]
      change tangent.2 * deriv canonicalLatitudeCollarCutoff normal =
        deriv canonicalLatitudeCollarCutoff normal * tangent.2
      ring

end
end P0EFTJanusMappingTorusCutBulkCanonicalCutoffCollarMFDeriv4D
end JanusFormal
