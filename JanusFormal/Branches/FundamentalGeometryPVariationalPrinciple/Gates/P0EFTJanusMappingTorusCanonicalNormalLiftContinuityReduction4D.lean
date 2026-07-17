import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D

/-!
# Canonical normal-lift continuity reduced to joint `C¹`

The canonical normal vector is the tangent map of the full latitude collar
applied to its smooth vertical unit section.  Consequently the former tangent
bundle continuity obligation follows from one joint `C¹` statement for the
explicit collar map.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalNormalLiftContinuityReduction4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)
private abbrev EffectiveCover := MappingTorusCover (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveCoverChartedSpace :
    ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod

local instance effectiveCoverIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveCover period hPeriod) :=
  reflectedSphereCover_isManifold period hPeriod

local instance canonicalLatitudeSphereFinrank :
    Fact (Module.finrank Real EuclideanR3 = 2 + 1) := ⟨by simp⟩

local instance canonicalLatitudeTargetSphereFinrank :
    Fact (Module.finrank Real EuclideanR4 = 3 + 1) := ⟨by simp⟩

local instance canonicalLatitudeSphereChartedSpace :
    ChartedSpace (EuclideanSpace Real (Fin 2))
      (Metric.sphere (0 : EuclideanR3) 1) := inferInstance

abbrev CanonicalLatitudeBaseCoordinates :=
  EuclideanSpace Real (Fin 2) × Real

abbrev CanonicalLatitudeBaseModel :=
  ModelProd (EuclideanSpace Real (Fin 2)) Real

abbrev canonicalLatitudeBaseModelWithCorners :
    ModelWithCorners Real CanonicalLatitudeBaseCoordinates
      CanonicalLatitudeBaseModel :=
  (𝓡 2).prod 𝓘(Real, Real)

abbrev CanonicalLatitudeParameterCoordinates :=
  CanonicalLatitudeBaseCoordinates × Real

abbrev CanonicalLatitudeParameterModel :=
  ModelProd CanonicalLatitudeBaseModel Real

abbrev canonicalLatitudeParameterModelWithCorners :
    ModelWithCorners Real CanonicalLatitudeParameterCoordinates
      CanonicalLatitudeParameterModel :=
  canonicalLatitudeBaseModelWithCorners.prod 𝓘(Real, Real)

local instance canonicalLatitudeBaseChartedSpace :
    ChartedSpace CanonicalLatitudeBaseModel CanonicalLatitudeBase :=
  inferInstance

local instance canonicalLatitudeParameterChartedSpace :
    ChartedSpace CanonicalLatitudeParameterModel CanonicalLatitudeParameter :=
  inferInstance

/-- The remaining analytic input after separating tangent-bundle algebra. -/
def CanonicalLatitudeCollarContMDiffOne : Prop :=
  ContMDiff canonicalLatitudeParameterModelWithCorners
    coverModelWithCorners 1 (canonicalLatitudeCollarMap period hPeriod)

/-- The collar `C¹` input stripped to the elementary sphere-latitude map. -/
def EquatorialLatitudeJointContMDiffOne : Prop :=
  ContMDiff ((𝓡 2).prod 𝓘(Real, Real)) (𝓡 3) 1
    equatorialLatitudeUncurried

/-- The explicit latitude formula is jointly analytic in the equatorial point
and the normal coordinate. -/
theorem equatorialLatitude_joint_contMDiff :
    ContMDiff ((𝓡 2).prod 𝓘(Real, Real)) (𝓡 3) ∞
      equatorialLatitudeUncurried := by
  have hEquatorToStandard : ContMDiff (𝓡 2) (𝓡 2) ∞
      equatorialTwoSphereHomeomorph :=
    chartedSpacePullback_toFun_contMDiff (𝓡 2) ∞
      equatorialTwoSphereHomeomorph
  have hStandardCoe : ContMDiff (𝓡 2) 𝓘(Real, EuclideanR3) ∞
      (fun point : EquatorialTwoSphere =>
        (equatorialTwoSphereHomeomorph point).1) :=
    contMDiff_coe_sphere.comp hEquatorToStandard
  have hStandardCoordinates :
      ContMDiff (𝓡 2) 𝓘(Real, Fin 3 → Real) ∞
        (fun point : EquatorialTwoSphere =>
          EuclideanSpace.equiv (Fin 3) Real
            (equatorialTwoSphereHomeomorph point).1) :=
    (EuclideanSpace.equiv (Fin 3) Real).toContinuousLinearMap.contDiff.contMDiff.comp
      hStandardCoe
  have hCoordinatesOnProduct :
      ContMDiff ((𝓡 2).prod 𝓘(Real, Real)) 𝓘(Real, Fin 3 → Real) ∞
        (fun parameter : EquatorialTwoSphere × Real =>
          EuclideanSpace.equiv (Fin 3) Real
            (equatorialTwoSphereHomeomorph parameter.1).1) :=
    hStandardCoordinates.comp contMDiff_fst
  have hRaw : ContMDiff ((𝓡 2).prod 𝓘(Real, Real))
      𝓘(Real, Fin 4 → Real) ∞
      (fun parameter : EquatorialTwoSphere × Real =>
        fun index : Fin 4 =>
          Fin.cases (motive := fun _ => Real) (Real.sin parameter.2)
            (fun tail : Fin 3 => Real.cos parameter.2 *
              (EuclideanSpace.equiv (Fin 3) Real
                (equatorialTwoSphereHomeomorph parameter.1).1) tail)
            index) := by
    rw [contMDiff_pi_space]
    intro index
    refine Fin.cases ?_ (fun tail => ?_) index
    · exact Real.contDiff_sin.contMDiff.comp contMDiff_snd
    · exact (Real.contDiff_cos.contMDiff.comp contMDiff_snd).mul
        ((contMDiff_pi_space.mp hCoordinatesOnProduct) tail)
  have hAmbient : ContMDiff ((𝓡 2).prod 𝓘(Real, Real))
      𝓘(Real, EuclideanR4) ∞
      (fun parameter : EquatorialTwoSphere × Real =>
        (EuclideanSpace.equiv (Fin 4) Real).symm
          (fun index : Fin 4 =>
            Fin.cases (motive := fun _ => Real) (Real.sin parameter.2)
              (fun tail : Fin 3 => Real.cos parameter.2 *
                (EuclideanSpace.equiv (Fin 3) Real
                  (equatorialTwoSphereHomeomorph parameter.1).1) tail)
              index)) :=
    (EuclideanSpace.equiv (Fin 4) Real).symm.toContinuousLinearMap.contDiff.contMDiff.comp
      hRaw
  have hStandard : ContMDiff ((𝓡 2).prod 𝓘(Real, Real))
      (𝓡 3) ∞
      (fun parameter : EquatorialTwoSphere × Real =>
        unitThreeSphereHomeomorph
          (equatorialLatitudeUncurried parameter)) := by
    apply ContMDiff.codRestrict_sphere hAmbient
  have hInv := chartedSpacePullback_invFun_contMDiff (𝓡 3) ∞
    unitThreeSphereHomeomorph
  exact (hInv.comp hStandard).congr fun parameter => by simp

/-- In particular, the formerly residual joint `C¹` statement is proved. -/
theorem equatorialLatitudeJointContMDiffOne :
    EquatorialLatitudeJointContMDiffOne :=
  equatorialLatitude_joint_contMDiff.of_le (by simp)

/-- Joint `C¹` of the elementary sphere map supplies joint `C¹` of the full
mapping-torus collar. -/
theorem canonicalLatitudeCollarContMDiffOne_of_equatorial
    (regularity : EquatorialLatitudeJointContMDiffOne) :
    CanonicalLatitudeCollarContMDiffOne period hPeriod := by
  have hEquator : ContMDiff canonicalLatitudeParameterModelWithCorners
      (𝓡 2) 1
      (fun parameter : CanonicalLatitudeParameter =>
        equatorialTwoSphereHomeomorph.symm parameter.1.1) :=
    ((chartedSpacePullback_invFun_contMDiff (𝓡 2) ∞
      equatorialTwoSphereHomeomorph).of_le (by simp)).comp
      (contMDiff_fst.comp contMDiff_fst)
  have hLatitudeInput : ContMDiff canonicalLatitudeParameterModelWithCorners
      ((𝓡 2).prod 𝓘(Real, Real)) 1
      (fun parameter : CanonicalLatitudeParameter =>
        (equatorialTwoSphereHomeomorph.symm parameter.1.1,
          parameter.2)) :=
    hEquator.prodMk contMDiff_snd
  have hLatitude : ContMDiff canonicalLatitudeParameterModelWithCorners
      (𝓡 3) 1
      (fun parameter : CanonicalLatitudeParameter =>
        equatorialLatitudeUncurried
          (equatorialTwoSphereHomeomorph.symm parameter.1.1,
            parameter.2)) :=
    regularity.comp hLatitudeInput
  have hProduct : ContMDiff canonicalLatitudeParameterModelWithCorners
      coverModelWithCorners 1
      (fun parameter : CanonicalLatitudeParameter =>
        (equatorialLatitudeUncurried
            (equatorialTwoSphereHomeomorph.symm parameter.1.1,
              parameter.2),
          parameter.1.2)) :=
    hLatitude.prodMk (contMDiff_snd.comp contMDiff_fst)
  have hCover : ContMDiff canonicalLatitudeParameterModelWithCorners
      coverModelWithCorners 1
      (fun parameter : CanonicalLatitudeParameter =>
        (coverHomeomorphProd (sphereData period hPeriod)).symm
          (equatorialLatitudeUncurried
              (equatorialTwoSphereHomeomorph.symm parameter.1.1,
                parameter.2),
            parameter.1.2)) :=
    ((chartedSpacePullback_invFun_contMDiff coverModelWithCorners ∞
      (coverHomeomorphProd (sphereData period hPeriod))).of_le (by simp)).comp
      hProduct
  have hProjection :=
    ((reflectedSphere_projection_isLocalDiffeomorph period hPeriod).contMDiff
      |>.of_le (by simp)).comp hCover
  change ContMDiff canonicalLatitudeParameterModelWithCorners
    coverModelWithCorners 1
    (fun parameter : CanonicalLatitudeParameter =>
      mappingTorusMk (sphereData period hPeriod)
        ⟨equatorialLatitude
            (equatorialTwoSphereHomeomorph.symm parameter.1.1)
            parameter.2,
          parameter.1.2⟩)
  exact hProjection

/-- Unit tangent section on the real normal factor. -/
def canonicalLatitudeRealUnitTangentLift (normal : Real) :
    TangentBundle 𝓘(Real, Real) Real :=
  ⟨normal, 1⟩

theorem canonicalLatitudeRealUnitTangentLift_contMDiff :
    ContMDiff 𝓘(Real, Real) 𝓘(Real, Real).tangent ∞
      canonicalLatitudeRealUnitTangentLift := by
  unfold canonicalLatitudeRealUnitTangentLift
  rw [contMDiff_vectorSpace_iff_contDiff]
  exact contDiff_const

/-- Smooth vertical unit section of the full collar parameter bundle. -/
def canonicalLatitudeVerticalTangentLift
    (parameter : CanonicalLatitudeParameter) :
    TangentBundle canonicalLatitudeParameterModelWithCorners
      CanonicalLatitudeParameter :=
  (equivTangentBundleProd canonicalLatitudeBaseModelWithCorners
      CanonicalLatitudeBase 𝓘(Real, Real) Real).symm
    (⟨parameter.1, 0⟩,
      canonicalLatitudeRealUnitTangentLift parameter.2)

theorem canonicalLatitudeVerticalTangentLift_contMDiff :
    ContMDiff canonicalLatitudeParameterModelWithCorners
      canonicalLatitudeParameterModelWithCorners.tangent ∞
      canonicalLatitudeVerticalTangentLift := by
  apply (contMDiff_equivTangentBundleProd_symm
    (I := canonicalLatitudeBaseModelWithCorners)
    (I' := 𝓘(Real, Real))
    (M := CanonicalLatitudeBase) (M' := Real)).comp
  exact ((Bundle.contMDiff_zeroSection Real
      (TangentSpace canonicalLatitudeBaseModelWithCorners :
        CanonicalLatitudeBase → Type _)).of_le le_top |>.comp contMDiff_fst).prodMk
    (canonicalLatitudeRealUnitTangentLift_contMDiff.comp contMDiff_snd)

/-- The bundled canonical normal lift is exactly the collar tangent map on the
vertical unit section. -/
theorem canonicalLatitudeNormalLift_eq_tangentMap_vertical
    (regularity : CanonicalLatitudeCollarContMDiffOne period hPeriod)
    (parameter : CanonicalLatitudeParameter) :
    canonicalLatitudeNormalLift period hPeriod parameter =
      tangentMap canonicalLatitudeParameterModelWithCorners
        coverModelWithCorners (canonicalLatitudeCollarMap period hPeriod)
        (canonicalLatitudeVerticalTangentLift parameter) := by
  let slice : Real → CanonicalLatitudeParameter :=
    fun normal => (parameter.1, normal)
  have hCollarAt : MDifferentiableAt
      canonicalLatitudeParameterModelWithCorners coverModelWithCorners
      (canonicalLatitudeCollarMap period hPeriod) parameter :=
    regularity.mdifferentiableAt (by simp)
  have hSliceAt : MDifferentiableAt 𝓘(Real, Real)
      canonicalLatitudeParameterModelWithCorners slice parameter.2 :=
    mdifferentiableAt_const.prodMk mdifferentiableAt_id
  have hComp := tangentMap_comp_at
    (I := 𝓘(Real, Real))
    (I' := canonicalLatitudeParameterModelWithCorners)
    (I'' := coverModelWithCorners)
    (f := slice)
    (g := canonicalLatitudeCollarMap period hPeriod)
    (⟨parameter.2, 1⟩ : TangentBundle 𝓘(Real, Real) Real)
    hCollarAt hSliceAt
  rw [tangentMap_prod_right] at hComp
  change
    tangentMap 𝓘(Real, Real) coverModelWithCorners
        (fun normal => quotientNormalLatitude period hPeriod
          (canonicalLatitudeAnchor period hPeriod parameter.1) normal)
        (⟨parameter.2, 1⟩ : TangentBundle 𝓘(Real, Real) Real) =
      tangentMap canonicalLatitudeParameterModelWithCorners
        coverModelWithCorners (canonicalLatitudeCollarMap period hPeriod)
        (canonicalLatitudeVerticalTangentLift parameter) at hComp
  calc
    canonicalLatitudeNormalLift period hPeriod parameter =
        tangentMap 𝓘(Real, Real) coverModelWithCorners
          (fun normal => quotientNormalLatitude period hPeriod
            (canonicalLatitudeAnchor period hPeriod parameter.1) normal)
          (⟨parameter.2, 1⟩ : TangentBundle 𝓘(Real, Real) Real) := by
      rfl
    _ = tangentMap canonicalLatitudeParameterModelWithCorners
        coverModelWithCorners (canonicalLatitudeCollarMap period hPeriod)
        (canonicalLatitudeVerticalTangentLift parameter) := hComp

/-- Joint `C¹` of the collar discharges the original normal-lift continuity
predicate. -/
theorem canonicalLatitudeNormalLiftContinuous_of_collarContMDiffOne
    (regularity : CanonicalLatitudeCollarContMDiffOne period hPeriod) :
    CanonicalLatitudeNormalLiftContinuous period hPeriod := by
  have hTangentMap : Continuous
      (tangentMap canonicalLatitudeParameterModelWithCorners
        coverModelWithCorners (canonicalLatitudeCollarMap period hPeriod)) :=
    regularity.continuous_tangentMap (by simp)
  exact (hTangentMap.comp
      canonicalLatitudeVerticalTangentLift_contMDiff.continuous).congr
    (fun parameter =>
      (canonicalLatitudeNormalLift_eq_tangentMap_vertical
        period hPeriod regularity parameter).symm)

/-- The elementary joint `C¹` latitude formula is sufficient for the
original bundled normal-lift continuity obligation. -/
theorem canonicalLatitudeNormalLiftContinuous_of_equatorial
    (regularity : EquatorialLatitudeJointContMDiffOne) :
    CanonicalLatitudeNormalLiftContinuous period hPeriod :=
  canonicalLatitudeNormalLiftContinuous_of_collarContMDiffOne period hPeriod
    (canonicalLatitudeCollarContMDiffOne_of_equatorial
      period hPeriod regularity)

/-- The explicit analytic latitude formula proves joint `C¹` of the full
mapping-torus collar without any residual assumption. -/
theorem canonicalLatitudeCollar_contMDiffOne :
    CanonicalLatitudeCollarContMDiffOne period hPeriod :=
  canonicalLatitudeCollarContMDiffOne_of_equatorial period hPeriod
    equatorialLatitudeJointContMDiffOne

/-- The canonical bundled normal lift is continuous unconditionally. -/
theorem canonicalLatitudeNormalLift_continuous :
    CanonicalLatitudeNormalLiftContinuous period hPeriod :=
  canonicalLatitudeNormalLiftContinuous_of_collarContMDiffOne period hPeriod
    (canonicalLatitudeCollar_contMDiffOne period hPeriod)

/-- The compact finite-frame reconstruction package is now unconditional. -/
def canonicalNormalFrameReconstructionBound :
    CanonicalNormalFrameReconstructionBound period hPeriod :=
  canonicalNormalFrameReconstructionBoundOfNormalLiftContinuous period hPeriod
    (canonicalLatitudeNormalLift_continuous period hPeriod)

end

end P0EFTJanusMappingTorusCanonicalNormalLiftContinuityReduction4D
end JanusFormal
