import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutBulkPositiveUnitTubularProductDiffeomorph4D

/-!
# Identity mapping tori commute smoothly with a passive product factor
-/

namespace JanusFormal
namespace P0EFTJanusIdentityMappingTorusProductDiffeomorph4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusIdentityMappingTorusSmoothFunctor4D
open P0EFTJanusMappingTorusEquivariantSmoothDescent4D

variable {E H X EW HW W : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [NormedAddCommGroup EW] [NormedSpace Real EW]
  [TopologicalSpace H] [TopologicalSpace X] [T2Space X]
  [LocallyCompactSpace X] [ChartedSpace H X]
  [TopologicalSpace HW] [TopologicalSpace W] [T2Space W]
  [LocallyCompactSpace W] [ChartedSpace HW W]
  (I : ModelWithCorners Real E H) [IsManifold I ∞ X]
  (K : ModelWithCorners Real EW HW) [IsManifold K ∞ W]
  (period : Real) (hPeriod : period ≠ 0)

abbrev identityMappingTorusProductData :=
  identityMappingTorusData (X := X × W) (I.prod K) period hPeriod

def identityMappingTorusProductForward
    (point : MappingTorus (identityMappingTorusProductData
      (X := X) (W := W) I K period hPeriod)) :
    MappingTorus (identityMappingTorusData (X := X) I period hPeriod) × W :=
  (identityMappingTorusMap (I.prod K) period hPeriod I Prod.fst point,
    mappingTorusInvariantMap (identityMappingTorusProductData
      (X := X) (W := W) I K period hPeriod)
      (fun coverPoint => coverPoint.fiber.2)
      (fun winding coverPoint => by
        change (((Homeomorph.refl (X × W)) ^ winding) coverPoint.fiber).2 =
          coverPoint.fiber.2
        rw [show ((Homeomorph.refl (X × W)) ^ winding) coverPoint.fiber =
            ((Homeomorph.refl (X × W)) ^ winding).toEquiv coverPoint.fiber from rfl,
          homeomorph_toEquiv_zpow,
          show (Homeomorph.refl (X × W)).toEquiv = 1 from rfl, one_zpow]
        rfl) point)

def identityMappingTorusProductInverseCover
    (point : MappingTorusCover
        (identityMappingTorusData (X := X) I period hPeriod) × W) :
    MappingTorusCover (identityMappingTorusProductData
      (X := X) (W := W) I K period hPeriod) :=
  ⟨(point.1.fiber, point.2), point.1.time⟩

def identityMappingTorusProductInverseCoverQuotient
    (point : MappingTorusCover
        (identityMappingTorusData (X := X) I period hPeriod) × W) :
    MappingTorus (identityMappingTorusProductData
      (X := X) (W := W) I K period hPeriod) :=
  mappingTorusMk _ (identityMappingTorusProductInverseCover
    (X := X) (W := W) I K period hPeriod point)

omit [T2Space X] [LocallyCompactSpace X] [ChartedSpace H X]
    [T2Space W] [LocallyCompactSpace W] [ChartedSpace HW W]
    [IsManifold I ∞ X] [IsManifold K ∞ W] in
theorem identityMappingTorusProductInverseCoverQuotient_invariant
    (winding : Int)
    (point : MappingTorusCover
        (identityMappingTorusData (X := X) I period hPeriod) × W) :
    identityMappingTorusProductInverseCoverQuotient
      (X := X) (W := W) I K period hPeriod
        (winding +ᵥ point.1, point.2) =
      identityMappingTorusProductInverseCoverQuotient
        (X := X) (W := W) I K period hPeriod point := by
  unfold identityMappingTorusProductInverseCoverQuotient
  rw [mappingTorusMk_eq_iff_exists_vadd]
  refine ⟨winding, ?_⟩
  apply MappingTorusCover.ext
  · change (((Homeomorph.refl (X × W)) ^ winding)
      (point.1.fiber, point.2)) =
      (((Homeomorph.refl X) ^ winding) point.1.fiber, point.2)
    rw [show ((Homeomorph.refl (X × W)) ^ winding)
        (point.1.fiber, point.2) =
      ((Homeomorph.refl (X × W)) ^ winding).toEquiv
        (point.1.fiber, point.2) from rfl,
      show ((Homeomorph.refl X) ^ winding) point.1.fiber =
        ((Homeomorph.refl X) ^ winding).toEquiv point.1.fiber from rfl,
      homeomorph_toEquiv_zpow, homeomorph_toEquiv_zpow,
      show (Homeomorph.refl (X × W)).toEquiv = 1 from rfl,
      show (Homeomorph.refl X).toEquiv = 1 from rfl, one_zpow]
    simp
  · rfl

def identityMappingTorusProductInverse :
    MappingTorus (identityMappingTorusData (X := X) I period hPeriod) × W →
      MappingTorus (identityMappingTorusProductData
        (X := X) (W := W) I K period hPeriod) :=
  mappingTorusInvariantMapProd
    (identityMappingTorusData (X := X) I period hPeriod)
    (identityMappingTorusProductInverseCoverQuotient
      (X := X) (W := W) I K period hPeriod)
    (identityMappingTorusProductInverseCoverQuotient_invariant
      (X := X) (W := W) I K period hPeriod)

omit [T2Space X] [LocallyCompactSpace X] [ChartedSpace H X]
    [T2Space W] [LocallyCompactSpace W] [ChartedSpace HW W]
    [IsManifold I ∞ X] [IsManifold K ∞ W] in
theorem identityMappingTorusProductForward_leftInverse :
    Function.LeftInverse (identityMappingTorusProductInverse
      (X := X) (W := W) I K period hPeriod)
      (identityMappingTorusProductForward
        (X := X) (W := W) I K period hPeriod) := by
  intro quotientPoint
  refine Quotient.inductionOn quotientPoint ?_
  intro representative
  rfl

omit [T2Space X] [LocallyCompactSpace X] [ChartedSpace H X]
    [T2Space W] [LocallyCompactSpace W] [ChartedSpace HW W]
    [IsManifold I ∞ X] [IsManifold K ∞ W] in
theorem identityMappingTorusProductForward_rightInverse :
    Function.RightInverse (identityMappingTorusProductInverse
      (X := X) (W := W) I K period hPeriod)
      (identityMappingTorusProductForward
        (X := X) (W := W) I K period hPeriod) := by
  rintro ⟨quotientPoint, parameter⟩
  refine Quotient.inductionOn quotientPoint ?_
  intro representative
  rfl

theorem identityMappingTorusProductForward_contMDiff :
    letI := identityMappingTorusQuotientChartedSpace
      (X := X × W) (I.prod K) period hPeriod
    letI := identityMappingTorusQuotientChartedSpace
      (X := X) I period hPeriod
    ContMDiff (identityCoverModelWithCorners (I.prod K))
      ((identityCoverModelWithCorners I).prod K) ∞
      (identityMappingTorusProductForward
        (X := X) (W := W) I K period hPeriod) := by
  letI := identityMappingTorusCoverChartedSpace
    (X := X × W) (I.prod K) period hPeriod
  letI := identityMappingTorusQuotientChartedSpace
    (X := X × W) (I.prod K) period hPeriod
  letI := identityMappingTorusQuotientChartedSpace
    (X := X) I period hPeriod
  have hFst : ContMDiff (I.prod K) I ∞ (Prod.fst : X × W → X) :=
    contMDiff_fst
  have hBoundary := identityMappingTorusMap_contMDiff (I.prod K)
    period hPeriod I (Prod.fst : X × W → X) hFst
  have hTo := chartedSpacePullback_toFun_contMDiff
    (identityCoverModelWithCorners (I.prod K)) ∞
    (coverHomeomorphProd
      (identityMappingTorusProductData (X := X) (W := W) I K period hPeriod))
  have hNormalCover : ContMDiff
      (identityCoverModelWithCorners (I.prod K)) K ∞
      (fun point : MappingTorusCover
        (identityMappingTorusProductData (X := X) (W := W) I K period hPeriod) =>
          point.fiber.2) :=
    (contMDiff_snd.comp (contMDiff_fst.comp hTo)).congr fun _ => rfl
  have hNormal := mappingTorusInvariantMap_contMDiff
    (sourceData := identityMappingTorusProductData
      (X := X) (W := W) I K period hPeriod)
    (sourceModel := identityCoverModelWithCorners (I.prod K))
    (n := ∞) (targetModel' := K)
    (invariantMap := fun coverPoint => coverPoint.fiber.2)
    (hInvariant := fun winding coverPoint => by
      change (((Homeomorph.refl (X × W)) ^ winding) coverPoint.fiber).2 =
        coverPoint.fiber.2
      rw [show ((Homeomorph.refl (X × W)) ^ winding) coverPoint.fiber =
          ((Homeomorph.refl (X × W)) ^ winding).toEquiv coverPoint.fiber from rfl,
        homeomorph_toEquiv_zpow,
        show (Homeomorph.refl (X × W)).toEquiv = 1 from rfl, one_zpow]
      rfl)
    (hSourceProjection := identityMappingTorus_projection_isLocalDiffeomorph
      (X := X × W) (I.prod K) period hPeriod)
    (hInvariantMap := hNormalCover)
  exact hBoundary.prodMk hNormal

omit [T2Space X] [LocallyCompactSpace X]
    [T2Space W] [LocallyCompactSpace W] in
theorem identityMappingTorusProductInverseCover_contMDiff :
    letI := identityMappingTorusCoverChartedSpace (X := X) I period hPeriod
    letI := identityMappingTorusCoverChartedSpace
      (X := X × W) (I.prod K) period hPeriod
    ContMDiff ((identityCoverModelWithCorners I).prod K)
      (identityCoverModelWithCorners (I.prod K)) ∞
      (identityMappingTorusProductInverseCover
        (X := X) (W := W) I K period hPeriod) := by
  letI := identityMappingTorusCoverChartedSpace (X := X) I period hPeriod
  letI := identityMappingTorusCoverChartedSpace
    (X := X × W) (I.prod K) period hPeriod
  have hTo := chartedSpacePullback_toFun_contMDiff
    (identityCoverModelWithCorners I) ∞
    (coverHomeomorphProd (identityMappingTorusData (X := X) I period hPeriod))
  have hToProd := hTo.prodMap (contMDiff_id : ContMDiff K K ∞ (id : W → W))
  have hFiber : ContMDiff ((I.prod 𝓘(Real, Real)).prod K) (I.prod K) ∞
      (fun point : (X × Real) × W => (point.1.1, point.2)) :=
    (contMDiff_fst.comp contMDiff_fst).prodMk contMDiff_snd
  have hTime : ContMDiff ((I.prod 𝓘(Real, Real)).prod K) 𝓘(Real, Real) ∞
      (fun point : (X × Real) × W => point.1.2) :=
    contMDiff_snd.comp contMDiff_fst
  have hReorder := hFiber.prodMk hTime
  have hInv := chartedSpacePullback_invFun_contMDiff
    (identityCoverModelWithCorners (I.prod K)) ∞
    (coverHomeomorphProd
      (identityMappingTorusProductData (X := X) (W := W) I K period hPeriod))
  exact (hInv.comp (hReorder.comp hToProd)).congr fun _ => rfl

theorem identityMappingTorusProductInverse_contMDiff :
    letI := identityMappingTorusQuotientChartedSpace
      (X := X) I period hPeriod
    letI := identityMappingTorusQuotientChartedSpace
      (X := X × W) (I.prod K) period hPeriod
    ContMDiff ((identityCoverModelWithCorners I).prod K)
      (identityCoverModelWithCorners (I.prod K)) ∞
      (identityMappingTorusProductInverse
        (X := X) (W := W) I K period hPeriod) := by
  letI := identityMappingTorusCoverChartedSpace (X := X) I period hPeriod
  letI := identityMappingTorusQuotientChartedSpace (X := X) I period hPeriod
  letI := identityMappingTorusCoverChartedSpace
    (X := X × W) (I.prod K) period hPeriod
  letI := identityMappingTorusQuotientChartedSpace
    (X := X × W) (I.prod K) period hPeriod
  have hCover := identityMappingTorusProductInverseCover_contMDiff
    (X := X) (W := W) I K period hPeriod
  have hQuotient : ContMDiff ((identityCoverModelWithCorners I).prod K)
      (identityCoverModelWithCorners (I.prod K)) ∞
      (identityMappingTorusProductInverseCoverQuotient
        (X := X) (W := W) I K period hPeriod) :=
    (identityMappingTorus_projection_isLocalDiffeomorph
      (X := X × W) (I.prod K) period hPeriod).contMDiff.comp hCover
  exact mappingTorusInvariantMapProd_contMDiff
    (sourceData := identityMappingTorusData (X := X) I period hPeriod)
    (sourceModel := identityCoverModelWithCorners I) (n := ∞)
    (parameterModel := K)
    (targetModel' := identityCoverModelWithCorners (I.prod K))
    (invariantMap := identityMappingTorusProductInverseCoverQuotient
      (X := X) (W := W) I K period hPeriod)
    (hInvariant := identityMappingTorusProductInverseCoverQuotient_invariant
      I K period hPeriod)
    (hSourceProjection := identityMappingTorus_projection_isLocalDiffeomorph
      (X := X) I period hPeriod)
    (hInvariantMap := hQuotient)

def identityMappingTorusProductDiffeomorph :
    letI := identityMappingTorusQuotientChartedSpace
      (X := X × W) (I.prod K) period hPeriod
    letI := identityMappingTorusQuotientChartedSpace
      (X := X) I period hPeriod
    MappingTorus (identityMappingTorusProductData
      (X := X) (W := W) I K period hPeriod) ≃ₘ^∞⟮
        identityCoverModelWithCorners (I.prod K),
        (identityCoverModelWithCorners I).prod K⟯
      (MappingTorus (identityMappingTorusData (X := X) I period hPeriod) × W) := by
  letI := identityMappingTorusQuotientChartedSpace
    (X := X × W) (I.prod K) period hPeriod
  letI := identityMappingTorusQuotientChartedSpace
    (X := X) I period hPeriod
  exact
    { toFun := identityMappingTorusProductForward
        (X := X) (W := W) I K period hPeriod
      invFun := identityMappingTorusProductInverse
        (X := X) (W := W) I K period hPeriod
      left_inv := identityMappingTorusProductForward_leftInverse
        (X := X) (W := W) I K period hPeriod
      right_inv := identityMappingTorusProductForward_rightInverse
        (X := X) (W := W) I K period hPeriod
      contMDiff_toFun := identityMappingTorusProductForward_contMDiff
        (X := X) (W := W) I K period hPeriod
      contMDiff_invFun := identityMappingTorusProductInverse_contMDiff
        (X := X) (W := W) I K period hPeriod }

end
end P0EFTJanusIdentityMappingTorusProductDiffeomorph4D
end JanusFormal
