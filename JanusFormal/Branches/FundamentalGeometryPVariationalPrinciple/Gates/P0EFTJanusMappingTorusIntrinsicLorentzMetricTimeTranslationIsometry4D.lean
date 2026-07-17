import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicCoverLorentzTensor4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCompleteTimeFlow4D

/-!
# Time-translation isometry of the intrinsic D8 Lorentz tensor

This downstream gate combines the already constructed intrinsic cover tensor
with the complete time flow.  The foundational tensor gate remains independent
of the later flow construction.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusIntrinsicCoverLorentzTensor4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompleteTimeFlow4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveCover :=
  MappingTorusCover (reflectedSphereData period hPeriod)

local instance timeTranslationEffectiveCoverChartedSpace :
    ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod

local instance timeTranslationEffectiveCoverIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveCover period hPeriod) :=
  reflectedSphereCover_isManifold period hPeriod

private def productTimeTranslation (shift : Real)
    (point : UnitThreeSphere × Real) : UnitThreeSphere × Real :=
  (point.1, point.2 + shift)

private theorem productTimeTranslation_contMDiff (shift : Real) :
    ContMDiff coverModelWithCorners coverModelWithCorners ω
      (productTimeTranslation shift) := by
  have hTime : ContMDiff 𝓘(Real, Real) 𝓘(Real, Real) ω
      (fun time : Real => time + shift) :=
    (contDiff_id.add contDiff_const).contMDiff
  exact (contMDiff_id.prodMap hTime).congr fun _ => rfl

@[simp]
private theorem mfderiv_realTimeTranslation
    (shift time : Real) :
    mfderiv 𝓘(Real, Real) 𝓘(Real, Real)
        (fun current : Real => current + shift) time =
      ContinuousLinearMap.id Real Real := by
  rw [mfderiv_eq_fderiv]
  exact ((ContinuousLinearMap.id Real Real).hasFDerivAt.add_const shift).fderiv

@[simp]
private theorem mfderiv_productTimeTranslation
    (shift : Real) (point : UnitThreeSphere × Real) :
    mfderiv coverModelWithCorners coverModelWithCorners
        (productTimeTranslation shift) point =
      ContinuousLinearMap.id Real CoverCoordinates := by
  have hSphere : MDifferentiableAt (𝓡 3) (𝓡 3)
      (id : UnitThreeSphere → UnitThreeSphere) point.1 :=
    mdifferentiableAt_id
  have hTimeCont : ContDiff Real ω
      (fun time : Real => time + shift) :=
    contDiff_id.add contDiff_const
  have hTime : MDifferentiableAt 𝓘(Real, Real) 𝓘(Real, Real)
      (fun time : Real => time + shift) point.2 :=
    hTimeCont.contMDiff.mdifferentiableAt (by simp)
  rw [show productTimeTranslation shift =
      Prod.map (id : UnitThreeSphere → UnitThreeSphere)
        (fun time : Real => time + shift) by rfl]
  rw [mfderiv_prodMap hSphere hTime, mfderiv_id,
    mfderiv_realTimeTranslation]
  apply ContinuousLinearMap.ext
  intro vector
  rfl

/-- Product-coordinate naturality of the cover derivative under real time
translation.  This uses only the public product model. -/
theorem coverProductDerivative_timeTranslation_natural
    (shift : Real) (point : EffectiveCover period hPeriod)
    (vector : TangentSpace coverModelWithCorners point) :
    coverProductDerivative period hPeriod
        (coverTimeTranslation (reflectedSphereData period hPeriod) shift point)
        (mfderiv coverModelWithCorners coverModelWithCorners
          (coverTimeTranslation (reflectedSphereData period hPeriod) shift)
          point vector) =
      coverProductDerivative period hPeriod point vector := by
  have hProduct := productTimeTranslation_contMDiff shift
  have hCover := chartedSpacePullback_toFun_contMDiff
    coverModelWithCorners ω
    (coverHomeomorphProd (reflectedSphereData period hPeriod))
  have hTranslation :=
    effectiveCoverTimeTranslation_contMDiff period hPeriod shift
  have hMaps :
      coverHomeomorphProd (reflectedSphereData period hPeriod) ∘
          coverTimeTranslation (reflectedSphereData period hPeriod) shift =
        productTimeTranslation shift ∘
          coverHomeomorphProd (reflectedSphereData period hPeriod) := by
    funext current
    apply Prod.ext <;> rfl
  have hLeft := mfderiv_comp_apply point
    (hCover.mdifferentiable (by simp)
      (coverTimeTranslation (reflectedSphereData period hPeriod) shift point))
    (hTranslation.mdifferentiable (by simp) point) vector
  have hRight := mfderiv_comp_apply point
    (hProduct.mdifferentiable (by simp)
      (coverHomeomorphProd (reflectedSphereData period hPeriod) point))
    (hCover.mdifferentiable (by simp) point) vector
  rw [hMaps] at hLeft
  have hNatural := hLeft.symm.trans hRight
  change coverProductDerivative period hPeriod
      (coverTimeTranslation (reflectedSphereData period hPeriod) shift point)
        (mfderiv coverModelWithCorners coverModelWithCorners
          (coverTimeTranslation (reflectedSphereData period hPeriod) shift)
          point vector) =
    mfderiv coverModelWithCorners coverModelWithCorners
      (productTimeTranslation shift)
      (coverHomeomorphProd (reflectedSphereData period hPeriod) point)
      (coverProductDerivative period hPeriod point vector) at hNatural
  rw [mfderiv_productTimeTranslation] at hNatural
  rw [ContinuousLinearMap.id_apply] at hNatural
  exact hNatural

/-- Every real cover-time translation is an exact isometry of the intrinsic
ambient-pullback Lorentz tensor. -/
theorem intrinsicCoverLorentzTensor_timeTranslation_isometry
    (shift : Real) (point : EffectiveCover period hPeriod)
    (first second : TangentSpace coverModelWithCorners point) :
    intrinsicCoverLorentzTensor period hPeriod
        (coverTimeTranslation (reflectedSphereData period hPeriod) shift point)
        (mfderiv coverModelWithCorners coverModelWithCorners
          (coverTimeTranslation (reflectedSphereData period hPeriod) shift)
          point first)
        (mfderiv coverModelWithCorners coverModelWithCorners
          (coverTimeTranslation (reflectedSphereData period hPeriod) shift)
          point second) =
      intrinsicCoverLorentzTensor period hPeriod point first second := by
  rw [intrinsicCoverLorentzTensor_apply,
    intrinsicCoverLorentzTensor_apply]
  simp_rw [coverAmbientDerivative_apply_product]
  simp only [coverTimeTranslation_fiber]
  rw [coverProductDerivative_timeTranslation_natural,
    coverProductDerivative_timeTranslation_natural]

end

end P0EFTJanusMappingTorusIntrinsicCoverLorentzTensor4D
end JanusFormal
