import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeAmbientOrthogonality4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeScalarStressEnergyCurrent4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkCanonicalCutoffCollarMFDeriv4D

/-!
# Canonical collar derivative and the metric normal covector

This gate transports the product latitude component through the genuine
mapping-torus collar derivative and identifies it with the metric normal
covector.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLatitudeNormalCovectorCollarDerivative4D

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusIntrinsicCoverLorentzTensor4D
open P0EFTJanusMappingTorusIntrinsicLorentzMetricDescent4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalNormalLiftContinuityReduction4D
open P0EFTJanusMappingTorusCanonicalLatitudeScalarNormalCurrent4D
open P0EFTJanusMappingTorusCanonicalLatitudeScalarStressEnergyCurrent4D
open P0EFTJanusMappingTorusCanonicalLatitudeAmbientOrthogonality4D
open P0EFTJanusMappingTorusCanonicalLatitudeCutoffNormalField4D
open P0EFTJanusMappingTorusCutBulkCanonicalCutoffCollarMFDeriv4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveCover := MappingTorusCover (sphereData period hPeriod)
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

private local instance effectiveCoverChartedSpace :
    ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod

private local instance effectiveCoverIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveCover period hPeriod) :=
  reflectedSphereCover_isManifold period hPeriod

private local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

private local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance canonicalLatitudeSphereFinrank :
    Fact (Module.finrank Real EuclideanR3 = 2 + 1) := ⟨by simp⟩

local instance canonicalLatitudeTargetSphereFinrank :
    Fact (Module.finrank Real EuclideanR4 = 3 + 1) := ⟨by simp⟩

local instance canonicalLatitudeSphereChartedSpace :
    ChartedSpace (EuclideanSpace Real (Fin 2))
      (Metric.sphere (0 : EuclideanR3) 1) := inferInstance

local instance canonicalLatitudeBaseChartedSpace :
    ChartedSpace CanonicalLatitudeBaseModel CanonicalLatitudeBase :=
  inferInstance

local instance canonicalLatitudeParameterChartedSpace :
    ChartedSpace CanonicalLatitudeParameterModel CanonicalLatitudeParameter :=
  inferInstance

/-- Cover representative of a fixed-normal equatorial latitude slice. -/
def equatorialLatitudeCoverSlice
    (normal : Real) (base : EquatorialTwoSphere × Real) :
    EffectiveCover period hPeriod :=
  (coverHomeomorphProd (sphereData period hPeriod)).symm
    (equatorialLatitude base.1 normal, base.2)

theorem equatorialLatitudeCoverSlice_eq_normalLatitudeCover
    (normal : Real) (base : EquatorialTwoSphere × Real) :
    equatorialLatitudeCoverSlice period hPeriod normal base =
      normalLatitudeCover period hPeriod
        ((coverHomeomorphProd (fixedEquatorData period hPeriod)).symm base)
        normal := by
  rfl

theorem equatorialLatitude_fixed_contMDiff (normal : Real) :
    ContMDiff (𝓡 2) (𝓡 3) ∞
      (fun point : EquatorialTwoSphere => equatorialLatitude point normal) := by
  have hInput : ContMDiff (𝓡 2) ((𝓡 2).prod 𝓘(Real, Real)) ∞
      (fun point : EquatorialTwoSphere => (point, normal)) :=
    contMDiff_id.prodMk contMDiff_const
  have hComp := equatorialLatitude_joint_contMDiff.comp hInput
  exact hComp.congr (fun _ => rfl)

theorem equatorialLatitudeCoverSlice_contMDiff (normal : Real) :
    ContMDiff ((𝓡 2).prod 𝓘(Real, Real)) coverModelWithCorners ∞
      (equatorialLatitudeCoverSlice period hPeriod normal) := by
  have hLatitude : ContMDiff ((𝓡 2).prod 𝓘(Real, Real)) (𝓡 3) ∞
      (fun base : EquatorialTwoSphere × Real =>
        equatorialLatitude base.1 normal) :=
    (equatorialLatitude_fixed_contMDiff normal).comp contMDiff_fst
  exact (chartedSpacePullback_invFun_contMDiff coverModelWithCorners ∞
    (coverHomeomorphProd (sphereData period hPeriod))).comp
      (hLatitude.prodMk contMDiff_snd)

theorem coverProductDerivative_equatorialLatitudeCoverSlice
    (normal : Real) (base : EquatorialTwoSphere × Real)
    (tangent : TangentSpace ((𝓡 2).prod 𝓘(Real, Real)) base) :
    coverProductDerivative period hPeriod
        (equatorialLatitudeCoverSlice period hPeriod normal base)
        (mfderiv ((𝓡 2).prod 𝓘(Real, Real)) coverModelWithCorners
          (equatorialLatitudeCoverSlice period hPeriod normal) base tangent) =
      (mfderiv (𝓡 2) (𝓡 3)
          (fun point : EquatorialTwoSphere => equatorialLatitude point normal)
          base.1 tangent.1,
        tangent.2) := by
  have hCover : MDifferentiableAt coverModelWithCorners coverModelWithCorners
      (coverHomeomorphProd (sphereData period hPeriod))
      (equatorialLatitudeCoverSlice period hPeriod normal base) :=
    (chartedSpacePullback_toFun_contMDiff coverModelWithCorners ∞
      (coverHomeomorphProd (sphereData period hPeriod))).mdifferentiableAt
        (by simp)
  have hSlice : MDifferentiableAt ((𝓡 2).prod 𝓘(Real, Real))
      coverModelWithCorners (equatorialLatitudeCoverSlice period hPeriod normal)
      base :=
    (equatorialLatitudeCoverSlice_contMDiff period hPeriod normal)
      |>.mdifferentiableAt (by simp)
  have hChain := mfderiv_comp_apply base hCover hSlice tangent
  have hMap :
      (coverHomeomorphProd (sphereData period hPeriod)) ∘
          equatorialLatitudeCoverSlice period hPeriod normal =
        Prod.map
          (fun point : EquatorialTwoSphere => equatorialLatitude point normal)
          (id : Real → Real) := by
    rfl
  rw [hMap] at hChain
  have hLatitude : MDifferentiableAt (𝓡 2) (𝓡 3)
      (fun point : EquatorialTwoSphere => equatorialLatitude point normal)
      base.1 :=
    (equatorialLatitude_fixed_contMDiff normal).mdifferentiableAt (by simp)
  rw [mfderiv_prodMap hLatitude mdifferentiableAt_id, mfderiv_id] at hChain
  exact hChain.symm

/-- The genuine latitude normal is orthogonal to every fixed-latitude base
tangent on the mapping-torus cover. -/
theorem intrinsicCoverLorentzTensor_normalLatitude_slice_orthogonal
    (normal : Real) (hCos : Real.cos normal ≠ 0)
    (base : EquatorialTwoSphere × Real)
    (tangent : TangentSpace ((𝓡 2).prod 𝓘(Real, Real)) base) :
    intrinsicCoverLorentzTensor period hPeriod
        (equatorialLatitudeCoverSlice period hPeriod normal base)
        (mfderiv 𝓘(Real, Real) coverModelWithCorners
          (normalLatitudeCover period hPeriod
            ((coverHomeomorphProd (fixedEquatorData period hPeriod)).symm base))
          normal 1)
        (mfderiv ((𝓡 2).prod 𝓘(Real, Real)) coverModelWithCorners
          (equatorialLatitudeCoverSlice period hPeriod normal) base tangent) = 0 := by
  let anchor :=
    (coverHomeomorphProd (fixedEquatorData period hPeriod)).symm base
  let sliceTangent :=
    mfderiv ((𝓡 2).prod 𝓘(Real, Real)) coverModelWithCorners
      (equatorialLatitudeCoverSlice period hPeriod normal) base tangent
  have hBaseAmbient := coverAmbientDerivative_apply_product period hPeriod
    (equatorialLatitudeCoverSlice period hPeriod normal base) sliceTangent
  rw [coverProductDerivative_equatorialLatitudeCoverSlice] at hBaseAmbient
  have hNormalAmbient := coverAmbientDerivative_normalLatitude
    period hPeriod anchor normal
  change coverAmbientDerivative period hPeriod
      (equatorialLatitudeCoverSlice period hPeriod normal base)
      (mfderiv 𝓘(Real, Real) coverModelWithCorners
        (normalLatitudeCover period hPeriod anchor) normal 1) =
    (latitudeAmbientVelocity base.1 normal, 0) at hNormalAmbient
  rw [intrinsicCoverLorentzTensor_apply, hNormalAmbient, hBaseAmbient]
  simp only [zero_mul, sub_zero]
  have hFiber :
      (equatorialLatitudeCoverSlice period hPeriod normal base).fiber =
        equatorialLatitude base.1 normal := by
    rfl
  rw [hFiber]
  exact latitudeAmbientVelocity_inner_fixedLatitudeDerivative_zero
    base.1 normal hCos tangent.1

/-- Canonical metric-sphere coordinates rewritten in the equatorial cover
coordinates used by the explicit latitude slice. -/
def canonicalLatitudeEquatorialBaseMap
    (base : CanonicalLatitudeBase) : EquatorialTwoSphere × Real :=
  (equatorialTwoSphereHomeomorph.symm base.1, base.2)

theorem canonicalLatitudeEquatorialBaseMap_contMDiff :
    ContMDiff canonicalLatitudeBaseModelWithCorners
      ((𝓡 2).prod 𝓘(Real, Real)) ∞ canonicalLatitudeEquatorialBaseMap := by
  have hEquator : ContMDiff canonicalLatitudeBaseModelWithCorners (𝓡 2) ∞
      (fun base : CanonicalLatitudeBase =>
        equatorialTwoSphereHomeomorph.symm base.1) :=
    (chartedSpacePullback_invFun_contMDiff (𝓡 2) ∞
      equatorialTwoSphereHomeomorph).comp contMDiff_fst
  exact hEquator.prodMk contMDiff_snd

/-- The derivative of the quotient collar along the base is the quotient
projection derivative of the explicit cover slice derivative. -/
theorem mfderiv_canonicalLatitudeCollarBaseSlice_eq_projection
    (normal : Real) (base : CanonicalLatitudeBase)
    (tangent : TangentSpace canonicalLatitudeBaseModelWithCorners base) :
    mfderiv canonicalLatitudeBaseModelWithCorners coverModelWithCorners
        (fun source : CanonicalLatitudeBase =>
          canonicalLatitudeCollarMap period hPeriod (source, normal))
        base tangent =
      mfderiv coverModelWithCorners coverModelWithCorners
        (mappingTorusMk (sphereData period hPeriod))
        (equatorialLatitudeCoverSlice period hPeriod normal
          (canonicalLatitudeEquatorialBaseMap base))
        (mfderiv ((𝓡 2).prod 𝓘(Real, Real)) coverModelWithCorners
          (equatorialLatitudeCoverSlice period hPeriod normal)
          (canonicalLatitudeEquatorialBaseMap base)
          (mfderiv canonicalLatitudeBaseModelWithCorners
            ((𝓡 2).prod 𝓘(Real, Real)) canonicalLatitudeEquatorialBaseMap
            base tangent)) := by
  let baseMap := canonicalLatitudeEquatorialBaseMap
  let coverSlice := equatorialLatitudeCoverSlice period hPeriod normal
  let projection := mappingTorusMk (sphereData period hPeriod)
  have hBase : MDifferentiableAt canonicalLatitudeBaseModelWithCorners
      ((𝓡 2).prod 𝓘(Real, Real)) baseMap base :=
    canonicalLatitudeEquatorialBaseMap_contMDiff.mdifferentiableAt (by simp)
  have hSlice : MDifferentiableAt ((𝓡 2).prod 𝓘(Real, Real))
      coverModelWithCorners coverSlice (baseMap base) :=
    (equatorialLatitudeCoverSlice_contMDiff period hPeriod normal)
      |>.mdifferentiableAt (by simp)
  have hProjection : MDifferentiableAt coverModelWithCorners
      coverModelWithCorners projection (coverSlice (baseMap base)) :=
    (reflectedSphere_projection_isLocalDiffeomorph period hPeriod).contMDiff
      |>.mdifferentiableAt (by simp)
  have hInner := mfderiv_comp_apply base hSlice hBase tangent
  have hComposite : MDifferentiableAt canonicalLatitudeBaseModelWithCorners
      coverModelWithCorners (coverSlice ∘ baseMap) base :=
    hSlice.comp base hBase
  have hOuter := mfderiv_comp_apply base hProjection hComposite tangent
  have hMap : projection ∘ coverSlice ∘ baseMap =
      fun source : CanonicalLatitudeBase =>
        canonicalLatitudeCollarMap period hPeriod (source, normal) := by
    rfl
  rw [hMap] at hOuter
  rw [hInner] at hOuter
  exact hOuter

/-- The quotient metric normal is orthogonal to the full fixed-latitude base
derivative of the canonical collar. -/
theorem intrinsicMetric_normal_canonicalLatitudeCollarBase_orthogonal
    (normal : Real) (hCos : Real.cos normal ≠ 0)
    (base : CanonicalLatitudeBase)
    (tangent : TangentSpace canonicalLatitudeBaseModelWithCorners base) :
    (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor
        (canonicalLatitudeCollarMap period hPeriod (base, normal))
        (canonicalLatitudeNormalVector period hPeriod base normal)
        (mfderiv canonicalLatitudeBaseModelWithCorners coverModelWithCorners
          (fun source : CanonicalLatitudeBase =>
            canonicalLatitudeCollarMap period hPeriod (source, normal))
          base tangent) = 0 := by
  let equatorialBase := canonicalLatitudeEquatorialBaseMap base
  let equatorialTangent :=
    mfderiv canonicalLatitudeBaseModelWithCorners
      ((𝓡 2).prod 𝓘(Real, Real)) canonicalLatitudeEquatorialBaseMap
      base tangent
  let point := equatorialLatitudeCoverSlice period hPeriod normal equatorialBase
  let normalTangent := mfderiv 𝓘(Real, Real) coverModelWithCorners
    (normalLatitudeCover period hPeriod
      (canonicalLatitudeAnchor period hPeriod base)) normal 1
  let baseTangent := mfderiv ((𝓡 2).prod 𝓘(Real, Real))
    coverModelWithCorners (equatorialLatitudeCoverSlice period hPeriod normal)
    equatorialBase equatorialTangent
  change (intrinsicTensorQuotientDescent period hPeriod).tensor
      (mappingTorusMk (sphereData period hPeriod) point)
      (canonicalLatitudeNormalVector period hPeriod base normal)
      (mfderiv canonicalLatitudeBaseModelWithCorners coverModelWithCorners
        (fun source : CanonicalLatitudeBase =>
          canonicalLatitudeCollarMap period hPeriod (source, normal))
        base tangent) = 0
  rw [canonicalLatitudeNormalVector_eq_projectionDerivative,
    mfderiv_canonicalLatitudeCollarBaseSlice_eq_projection]
  exact ((intrinsicTensorQuotientDescent period hPeriod).pullback
    point normalTangent baseTangent).trans
      (intrinsicCoverLorentzTensor_normalLatitude_slice_orthogonal
        period hPeriod normal hCos equatorialBase equatorialTangent)

/-- Product decomposition of the full collar derivative into its fixed-normal
base derivative and its canonical normal component. -/
theorem mfderiv_canonicalLatitudeCollarMap_decomposition
    (base : CanonicalLatitudeBase) (normal : Real)
    (tangent : TangentSpace canonicalLatitudeParameterModelWithCorners
      (base, normal)) :
    mfderiv canonicalLatitudeParameterModelWithCorners coverModelWithCorners
        (canonicalLatitudeCollarMap period hPeriod) (base, normal) tangent =
      mfderiv canonicalLatitudeBaseModelWithCorners coverModelWithCorners
          (fun source : CanonicalLatitudeBase =>
            canonicalLatitudeCollarMap period hPeriod (source, normal))
          base tangent.1 +
        tangent.2 •
          (show TangentSpace coverModelWithCorners
              (canonicalLatitudeCollarMap period hPeriod (base, normal)) from
            canonicalLatitudeNormalVector period hPeriod base normal) := by
  have hCollar : MDifferentiableAt canonicalLatitudeParameterModelWithCorners
      coverModelWithCorners (canonicalLatitudeCollarMap period hPeriod)
      (base, normal) :=
    (canonicalLatitudeCollar_contMDiff period hPeriod).mdifferentiableAt
      (by simp)
  rw [mfderiv_prod_eq_add_apply hCollar]
  congr 1
  let verticalDerivative :=
    mfderiv 𝓘(Real, Real) coverModelWithCorners
      (fun coordinate : Real =>
        canonicalLatitudeCollarMap period hPeriod (base, coordinate)) normal
  calc
    verticalDerivative tangent.2 =
        verticalDerivative (tangent.2 • (1 : Real)) := by simp
    _ = tangent.2 • verticalDerivative 1 :=
      verticalDerivative.map_smul tangent.2 1
    _ = tangent.2 •
        (show TangentSpace coverModelWithCorners
            (canonicalLatitudeCollarMap period hPeriod (base, normal)) from
          canonicalLatitudeNormalVector period hPeriod base normal) := by
      rfl

theorem canonicalLatitudeNormalCovector_apply_collarBaseDerivative
    (normal : Real) (hCos : Real.cos normal ≠ 0)
    (base : CanonicalLatitudeBase)
    (tangent : TangentSpace canonicalLatitudeBaseModelWithCorners base) :
    canonicalLatitudeNormalCovector period hPeriod base normal
        (mfderiv canonicalLatitudeBaseModelWithCorners coverModelWithCorners
          (fun source : CanonicalLatitudeBase =>
            canonicalLatitudeCollarMap period hPeriod (source, normal))
          base tangent) = 0 := by
  let baseDerivative :=
    mfderiv canonicalLatitudeBaseModelWithCorners coverModelWithCorners
      (fun source : CanonicalLatitudeBase =>
        canonicalLatitudeCollarMap period hPeriod (source, normal)) base tangent
  unfold canonicalLatitudeNormalCovector
  have hFlat := congrArg
    (fun linearMap =>
      linearMap (canonicalLatitudeNormalVector period hPeriod base normal))
    ((intrinsicSmoothGeneralLorentzMetric period hPeriod).musical_eq_tensor
      (canonicalLatitudeCollarMap period hPeriod (base, normal)))
  exact (DFunLike.congr_fun hFlat baseDerivative).trans
    (intrinsicMetric_normal_canonicalLatitudeCollarBase_orthogonal
      period hPeriod normal hCos base tangent)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Pulling the metric normal covector through the full canonical collar
derivative gives exactly the product latitude component. -/
theorem canonicalLatitudeNormalCovector_comp_mfderiv_collar_apply
    (base : CanonicalLatitudeBase) (normal : Real)
    (hCos : Real.cos normal ≠ 0)
    (tangent : TangentSpace canonicalLatitudeParameterModelWithCorners
      (base, normal)) :
    canonicalLatitudeNormalCovector period hPeriod base normal
        (mfderiv canonicalLatitudeParameterModelWithCorners
          coverModelWithCorners (canonicalLatitudeCollarMap period hPeriod)
          (base, normal) tangent) = tangent.2 := by
  let baseTangent := tangent.1
  let normalComponent := tangent.2
  let baseDerivative :=
    mfderiv canonicalLatitudeBaseModelWithCorners coverModelWithCorners
      (fun source : CanonicalLatitudeBase =>
        canonicalLatitudeCollarMap period hPeriod (source, normal))
      base baseTangent
  let normalVector : TangentSpace coverModelWithCorners
      (canonicalLatitudeCollarMap period hPeriod (base, normal)) :=
    canonicalLatitudeNormalVector period hPeriod base normal
  let normalCovector := canonicalLatitudeNormalCovector
    period hPeriod base normal
  rw [mfderiv_canonicalLatitudeCollarMap_decomposition]
  change normalCovector (baseDerivative + normalComponent • normalVector) =
    normalComponent
  calc
    normalCovector (baseDerivative + normalComponent • normalVector) =
        normalCovector baseDerivative +
          normalCovector (normalComponent • normalVector) :=
      normalCovector.map_add _ _
    _ = normalCovector baseDerivative +
        normalComponent • normalCovector normalVector := by
      rw [normalCovector.map_smul]
    _ = 0 + normalComponent • 1 := by
      rw [canonicalLatitudeNormalCovector_apply_collarBaseDerivative
          period hPeriod normal hCos base baseTangent,
        canonicalLatitudeNormalCovector_apply_normal]
    _ = normalComponent := by simp

/-- The genuine global cutoff differential pulled to the collar is exactly
`cutoff'` times the metric normal covector evaluated on the pushed tangent. -/
theorem mfderiv_cutBulkCanonicalCutoffCollarPullback_eq_normalCovector
    (base : CanonicalLatitudeBase) (normal : Real)
    (hNormal : normal ∈ Set.Ioo (0 : Real) 1)
    (tangent : TangentSpace canonicalLatitudeParameterModelWithCorners
      (base, normal)) :
    mfderiv canonicalLatitudeParameterModelWithCorners
        (modelWithCornersSelf Real Real)
        (cutBulkCanonicalCutoffCollarPullback period hPeriod) (base, normal)
        tangent =
      deriv canonicalLatitudeCollarCutoff normal *
        canonicalLatitudeNormalCovector period hPeriod base normal
          (mfderiv canonicalLatitudeParameterModelWithCorners
            coverModelWithCorners (canonicalLatitudeCollarMap period hPeriod)
            (base, normal) tangent) := by
  have hNormalWide : normal ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [hNormal.1, hNormal.2, Real.pi_gt_three]
  have hCos : Real.cos normal ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo hNormalWide)
  rw [mfderiv_cutBulkCanonicalCutoffCollarPullback_apply
      period hPeriod base normal hNormal tangent,
    canonicalLatitudeNormalCovector_comp_mfderiv_collar_apply
      period hPeriod base normal hCos tangent]

end

end P0EFTJanusMappingTorusCanonicalLatitudeNormalCovectorCollarDerivative4D
end JanusFormal
