import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusTubularBandToAmbientCoverDerivativeIsomorphism4D

/-!
# Differential certificate from product cut-collar coordinates to the ambient quotient
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCutCollarProductToAmbientDerivativeIsomorphism4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCutThroatSmoothFiniteCollar4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCutCollarTubularSpacetimeDerivativeIsomorphism4D
open P0EFTJanusMappingTorusTubularBandToAmbientCoverDerivativeIsomorphism4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance quotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

/-- Product collar coordinates mapped through the tubular band to the quotient. -/
def cutCollarProductToAmbient
    (parameter : (EquatorialTwoSphere × Real) × CutCollarInterval) :
    EffectiveQuotient period hPeriod :=
  tubularBandSpacetimeToAmbient period hPeriod
    (cutCollarTubularSpacetimeMap parameter)

theorem cutCollarProductToAmbient_contMDiff :
    ContMDiff
      (((𝓡 2).prod (modelWithCornersSelf Real Real)).prod
        (modelWithCornersEuclideanHalfSpace 1))
      coverModelWithCorners ∞ (cutCollarProductToAmbient period hPeriod) :=
  (tubularBandSpacetimeToAmbient_isLocalDiffeomorph period hPeriod).contMDiff.comp
    cutCollarTubularSpacetimeMap_contMDiff

set_option backward.isDefEq.respectTransparency false in
theorem cutCollarProductToAmbient_derivative_isomorphism
    (parameter : (EquatorialTwoSphere × Real) × CutCollarInterval) :
    ∃ derivative :
        TangentSpace
          (((𝓡 2).prod (modelWithCornersSelf Real Real)).prod
            (modelWithCornersEuclideanHalfSpace 1)) parameter ≃L[Real]
          TangentSpace coverModelWithCorners
            (cutCollarProductToAmbient period hPeriod parameter),
      (derivative :
          TangentSpace
            (((𝓡 2).prod (modelWithCornersSelf Real Real)).prod
              (modelWithCornersEuclideanHalfSpace 1)) parameter →L[Real]
            TangentSpace coverModelWithCorners
              (cutCollarProductToAmbient period hPeriod parameter)) =
        mfderiv
          (((𝓡 2).prod (modelWithCornersSelf Real Real)).prod
            (modelWithCornersEuclideanHalfSpace 1))
          coverModelWithCorners (cutCollarProductToAmbient period hPeriod) parameter := by
  unfold cutCollarProductToAmbient
  let collarDerivative :=
    (cutCollarTubularSpacetimeMap_derivative_isomorphism parameter).choose
  have hCollarDerivative :=
    (cutCollarTubularSpacetimeMap_derivative_isomorphism parameter).choose_spec
  let ambientDerivative :=
    (tubularBandSpacetimeToAmbient_derivative_isomorphism period hPeriod
      (cutCollarTubularSpacetimeMap parameter)).choose
  have hAmbientDerivative :=
    (tubularBandSpacetimeToAmbient_derivative_isomorphism period hPeriod
      (cutCollarTubularSpacetimeMap parameter)).choose_spec
  let derivative := collarDerivative.trans ambientDerivative
  refine ⟨derivative, ?_⟩
  have hCollar := cutCollarTubularSpacetimeMap_contMDiff.mdifferentiableAt
    (x := parameter) (by simp)
  have hAmbient :=
    (tubularBandSpacetimeToAmbient_isLocalDiffeomorph period hPeriod).contMDiff
      |>.mdifferentiableAt (x := cutCollarTubularSpacetimeMap parameter) (by simp)
  have hComp := mfderiv_comp parameter hAmbient hCollar
  ext vector
  change ambientDerivative (collarDerivative vector) = _
  rw [show collarDerivative vector =
      mfderiv
        (((𝓡 2).prod (modelWithCornersSelf Real Real)).prod
          (modelWithCornersEuclideanHalfSpace 1))
        ((𝓡 3).prod (modelWithCornersSelf Real Real))
        cutCollarTubularSpacetimeMap parameter vector by
    exact DFunLike.congr_fun hCollarDerivative vector,
    show ambientDerivative
        (mfderiv
          (((𝓡 2).prod (modelWithCornersSelf Real Real)).prod
            (modelWithCornersEuclideanHalfSpace 1))
          ((𝓡 3).prod (modelWithCornersSelf Real Real))
          cutCollarTubularSpacetimeMap parameter vector) =
      mfderiv coverModelWithCorners coverModelWithCorners
        (tubularBandSpacetimeToAmbient period hPeriod)
        (cutCollarTubularSpacetimeMap parameter)
        (mfderiv
          (((𝓡 2).prod (modelWithCornersSelf Real Real)).prod
            (modelWithCornersEuclideanHalfSpace 1))
          ((𝓡 3).prod (modelWithCornersSelf Real Real))
          cutCollarTubularSpacetimeMap parameter vector) by
    exact DFunLike.congr_fun hAmbientDerivative _]
  exact DFunLike.congr_fun hComp.symm vector

end
end P0EFTJanusMappingTorusCutCollarProductToAmbientDerivativeIsomorphism4D
end JanusFormal
