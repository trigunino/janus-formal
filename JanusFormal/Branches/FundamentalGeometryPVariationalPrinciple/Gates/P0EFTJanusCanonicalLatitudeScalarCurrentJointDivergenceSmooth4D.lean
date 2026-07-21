import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCanonicalLatitudeScalarCurrentJointSmooth4D

/-!
# Joint smoothness of the canonical scalar-current divergence

The divergence is the derivative of the jointly smooth cutoff current density
along the already constructed smooth vertical unit tangent section.
-/

namespace JanusFormal
namespace P0EFTJanusCanonicalLatitudeScalarCurrentJointDivergenceSmooth4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalNormalLiftContinuityReduction4D
open P0EFTJanusMappingTorusCanonicalLatitudeCutoffCurrentLocalStokes4D
open P0EFTJanusCanonicalLatitudeScalarCurrentJointSmooth4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance : ChartedSpace (EuclideanSpace Real (Fin 2))
    (Metric.sphere (0 : EuclideanR3) 1) := inferInstance

local instance : ChartedSpace CanonicalLatitudeParameterModel
    CanonicalLatitudeParameter := inferInstance

/-- Joint normal derivative of the cutoff scalar-current density. -/
def jointCutoffCollarScalarCurrentDivergence
    (field test : SmoothQuotientField period hPeriod Real)
    (parameter : CanonicalLatitudeParameter) : Real :=
  (tangentMap canonicalLatitudeParameterModelWithCorners 𝓘(Real, Real)
    (jointCutoffCollarScalarCurrentDensity period hPeriod field test)
    (canonicalLatitudeVerticalTangentLift parameter)).2

theorem jointCutoffCollarScalarCurrentDivergence_contMDiff
    (field test : SmoothQuotientField period hPeriod Real) :
    ContMDiff canonicalLatitudeParameterModelWithCorners 𝓘(Real, Real) ∞
      (jointCutoffCollarScalarCurrentDivergence period hPeriod field test) := by
  exact (contMDiff_snd_tangentBundle_modelSpace Real 𝓘(Real, Real)).comp
    (((jointCutoffCollarScalarCurrentDensity_contMDiff period hPeriod field test)
      |>.contMDiff_tangentMap (by simp)).comp
        canonicalLatitudeVerticalTangentLift_contMDiff)

theorem jointCutoffCollarScalarCurrentDivergence_eq
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (parameter : CanonicalLatitudeParameter) :
    jointCutoffCollarScalarCurrentDivergence period hPeriod field test parameter =
      cutoffCollarScalarCurrentDensitizedDivergence period hPeriod massSquared
        field test parameter.1 parameter.2 := by
  let slice : Real → CanonicalLatitudeParameter :=
    fun normal ↦ (parameter.1, normal)
  have hDensityAt : MDifferentiableAt canonicalLatitudeParameterModelWithCorners
      𝓘(Real, Real)
      (jointCutoffCollarScalarCurrentDensity period hPeriod field test) parameter :=
    (jointCutoffCollarScalarCurrentDensity_contMDiff period hPeriod field test)
      |>.mdifferentiableAt (by simp)
  have hSliceAt : MDifferentiableAt 𝓘(Real, Real)
      canonicalLatitudeParameterModelWithCorners slice parameter.2 :=
    mdifferentiableAt_const.prodMk mdifferentiableAt_id
  have hComp := tangentMap_comp_at
    (I := 𝓘(Real, Real))
    (I' := canonicalLatitudeParameterModelWithCorners)
    (I'' := 𝓘(Real, Real))
    (f := slice)
    (g := jointCutoffCollarScalarCurrentDensity period hPeriod field test)
    (⟨parameter.2, 1⟩ : TangentBundle 𝓘(Real, Real) Real)
    hDensityAt hSliceAt
  rw [tangentMap_prod_right] at hComp
  have hSecond := congrArg (fun tangent ↦ tangent.2) hComp
  change
    mfderiv 𝓘(Real, Real) 𝓘(Real, Real)
        (fun normal ↦ jointCutoffCollarScalarCurrentDensity period hPeriod
          field test (parameter.1, normal)) parameter.2 1 =
      jointCutoffCollarScalarCurrentDivergence period hPeriod field test parameter
    at hSecond
  rw [mfderiv_eq_fderiv] at hSecond
  change deriv (fun normal ↦
      jointCutoffCollarScalarCurrentDensity period hPeriod field test
        (parameter.1, normal)) parameter.2 =
    jointCutoffCollarScalarCurrentDivergence period hPeriod field test parameter
    at hSecond
  have hFunctions :
      (fun normal ↦ jointCutoffCollarScalarCurrentDensity period hPeriod
        field test (parameter.1, normal)) =
      cutoffCollarScalarCurrentDensity period hPeriod field test parameter.1 := by
    funext normal
    exact jointCutoffCollarScalarCurrentDensity_eq period hPeriod field test
      (parameter.1, normal)
  rw [hFunctions] at hSecond
  exact hSecond.symm.trans
    (cutoffCollarScalarCurrentDensity_hasDerivAt period hPeriod massSquared
      field test parameter.1 parameter.2).deriv

end
end P0EFTJanusCanonicalLatitudeScalarCurrentJointDivergenceSmooth4D
end JanusFormal
