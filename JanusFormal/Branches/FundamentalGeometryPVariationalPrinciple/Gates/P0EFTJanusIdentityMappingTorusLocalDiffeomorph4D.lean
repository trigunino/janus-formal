import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIdentityMappingTorusSmoothFunctor4D
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Local diffeomorphisms of identity mapping tori

A local diffeomorphism of fibres induces a local diffeomorphism of the
corresponding identity mapping tori.
-/

namespace JanusFormal
namespace P0EFTJanusIdentityMappingTorusLocalDiffeomorph4D

set_option autoImplicit false
noncomputable section

open Set
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusIdentityMappingTorusSmoothFunctor4D

private def partialDiffeomorphProd
    {E H M E' H' M' F G N F' G' N' : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E] [TopologicalSpace H]
    [TopologicalSpace M] [ChartedSpace H M]
    [NormedAddCommGroup E'] [NormedSpace Real E'] [TopologicalSpace H']
    [TopologicalSpace M'] [ChartedSpace H' M']
    [NormedAddCommGroup F] [NormedSpace Real F] [TopologicalSpace G]
    [TopologicalSpace N] [ChartedSpace G N]
    [NormedAddCommGroup F'] [NormedSpace Real F'] [TopologicalSpace G']
    [TopologicalSpace N'] [ChartedSpace G' N']
    {I : ModelWithCorners Real E H} {I' : ModelWithCorners Real E' H'}
    {J : ModelWithCorners Real F G} {J' : ModelWithCorners Real F' G'}
    {n : ℕ∞ω}
    (Φ : PartialDiffeomorph I I' M M' n)
    (Ψ : PartialDiffeomorph J J' N N' n) :
    PartialDiffeomorph (I.prod J) (I'.prod J') (M × N) (M' × N') n where
  __ := Φ.toOpenPartialHomeomorph.prod Ψ.toOpenPartialHomeomorph
  contMDiffOn_toFun := Φ.contMDiffOn.prodMap Ψ.contMDiffOn
  contMDiffOn_invFun := Φ.symm.contMDiffOn.prodMap Ψ.symm.contMDiffOn

private theorem isLocalDiffeomorph_prodMap
    {E H M E' H' M' F G N F' G' N' : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E] [TopologicalSpace H]
    [TopologicalSpace M] [ChartedSpace H M]
    [NormedAddCommGroup E'] [NormedSpace Real E'] [TopologicalSpace H']
    [TopologicalSpace M'] [ChartedSpace H' M']
    [NormedAddCommGroup F] [NormedSpace Real F] [TopologicalSpace G]
    [TopologicalSpace N] [ChartedSpace G N]
    [NormedAddCommGroup F'] [NormedSpace Real F'] [TopologicalSpace G']
    [TopologicalSpace N'] [ChartedSpace G' N']
    {I : ModelWithCorners Real E H} {I' : ModelWithCorners Real E' H'}
    {J : ModelWithCorners Real F G} {J' : ModelWithCorners Real F' G'}
    {n : ℕ∞ω} {f : M → M'} {g : N → N'}
    (hf : IsLocalDiffeomorph I I' n f)
    (hg : IsLocalDiffeomorph J J' n g) :
    IsLocalDiffeomorph (I.prod J) (I'.prod J') n (Prod.map f g) := by
  intro point
  obtain ⟨Φ, hPoint, hΦ⟩ := hf point.1
  obtain ⟨Ψ, hPoint', hΨ⟩ := hg point.2
  refine ⟨partialDiffeomorphProd Φ Ψ, ⟨hPoint, hPoint'⟩, ?_⟩
  rintro ⟨first, second⟩ ⟨hFirst, hSecond⟩
  exact Prod.ext (hΦ hFirst) (hΨ hSecond)

private def coverProductDiffeomorph
    {E H X : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [TopologicalSpace H] [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [ChartedSpace H X]
    (I : ModelWithCorners Real E H) [IsManifold I ∞ X]
    (period : Real) (hPeriod : period ≠ 0) :
    letI := identityMappingTorusCoverChartedSpace (X := X) I period hPeriod
    MappingTorusCover (identityMappingTorusData (X := X) I period hPeriod) ≃ₘ^∞⟮
      identityCoverModelWithCorners I, I.prod 𝓘(Real, Real)⟯ X × Real := by
  letI := identityMappingTorusCoverChartedSpace (X := X) I period hPeriod
  exact
    { toEquiv := (coverHomeomorphProd
        (identityMappingTorusData (X := X) I period hPeriod)).toEquiv
      contMDiff_toFun := chartedSpacePullback_toFun_contMDiff
        (identityCoverModelWithCorners I) ∞
        (coverHomeomorphProd
          (identityMappingTorusData (X := X) I period hPeriod))
      contMDiff_invFun := chartedSpacePullback_invFun_contMDiff
        (identityCoverModelWithCorners I) ∞
        (coverHomeomorphProd
          (identityMappingTorusData (X := X) I period hPeriod)) }

theorem identityMappingTorusMap_isLocalDiffeomorph
    {E H X E' H' Y : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [TopologicalSpace H] [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [ChartedSpace H X]
    (I : ModelWithCorners Real E H) [IsManifold I ∞ X]
    (period : Real) (hPeriod : period ≠ 0)
    [NormedAddCommGroup E'] [NormedSpace Real E']
    [TopologicalSpace H'] [TopologicalSpace Y] [T2Space Y]
    [LocallyCompactSpace Y] [ChartedSpace H' Y]
    (J : ModelWithCorners Real E' H') [IsManifold J ∞ Y]
    (fiberMap : X → Y)
    (hFiberMap : IsLocalDiffeomorph I J ∞ fiberMap) :
    letI := identityMappingTorusQuotientChartedSpace (X := X) I period hPeriod
    letI := identityMappingTorusQuotientChartedSpace (X := Y) J period hPeriod
    IsLocalDiffeomorph (identityCoverModelWithCorners I)
      (identityCoverModelWithCorners J) ∞
      (identityMappingTorusMap I period hPeriod J fiberMap) := by
  letI := identityMappingTorusCoverChartedSpace (X := X) I period hPeriod
  letI := identityMappingTorusQuotientChartedSpace (X := X) I period hPeriod
  letI := identityMappingTorusCoverChartedSpace (X := Y) J period hPeriod
  letI := identityMappingTorusQuotientChartedSpace (X := Y) J period hPeriod
  have hCover : IsLocalDiffeomorph (identityCoverModelWithCorners I)
      (identityCoverModelWithCorners J) ∞
      (identityMappingTorusCoverMap I period hPeriod J fiberMap) := by
    have hProduct := isLocalDiffeomorph_prodMap hFiberMap
      ((Diffeomorph.refl 𝓘(Real, Real) Real ∞).isLocalDiffeomorph)
    intro point
    have hFirst := (coverProductDiffeomorph I period hPeriod)
      |>.isLocalDiffeomorph point
    have hMiddle := hProduct
      ((coverProductDiffeomorph I period hPeriod) point)
    have hLast := (coverProductDiffeomorph J period hPeriod).symm
      |>.isLocalDiffeomorph
        (Prod.map fiberMap (id : Real → Real)
          ((coverProductDiffeomorph I period hPeriod) point))
    have hFirstMiddle := IsLocalDiffeomorphAt.comp
      (I := identityCoverModelWithCorners I)
      (J := I.prod 𝓘(Real, Real)) (K := J.prod 𝓘(Real, Real))
      (M := MappingTorusCover
        (identityMappingTorusData (X := X) I period hPeriod))
      (N := X × Real) (P := Y × Real) (n := ∞) hFirst hMiddle
    have hComposite := IsLocalDiffeomorphAt.comp
      (I := identityCoverModelWithCorners I)
      (J := J.prod 𝓘(Real, Real))
      (K := identityCoverModelWithCorners J)
      (M := MappingTorusCover
        (identityMappingTorusData (X := X) I period hPeriod))
      (N := Y × Real)
      (P := MappingTorusCover
        (identityMappingTorusData (X := Y) J period hPeriod))
      (n := ∞) hFirstMiddle hLast
    convert hComposite using 1
    funext cover
    rfl
  intro quotientPoint
  obtain ⟨coverPoint, rfl⟩ := mappingTorusMk_surjective
    (identityMappingTorusData (X := X) I period hPeriod) quotientPoint
  let sourceProjection := mappingTorusMk
    (identityMappingTorusData (X := X) I period hPeriod)
  let targetProjection := mappingTorusMk
    (identityMappingTorusData (X := Y) J period hPeriod)
  have hSource := identityMappingTorus_projection_isLocalDiffeomorph
    (X := X) I period hPeriod coverPoint
  obtain ⟨coverLocal, hCoverLocalSource, hCoverLocalEq⟩ := hCover coverPoint
  have hTargetAt := identityMappingTorus_projection_isLocalDiffeomorph
    (X := Y) J period hPeriod
    (identityMappingTorusCoverMap I period hPeriod J fiberMap coverPoint)
  obtain ⟨targetLocal, hTargetLocalSource, hTargetLocalEq⟩ := hTargetAt
  let Φ := hSource.localInverse.trans
    (coverLocal.trans targetLocal)
  refine ⟨Φ, ?_, ?_⟩
  · change mappingTorusMk
        (identityMappingTorusData (X := X) I period hPeriod) coverPoint ∈
      hSource.localInverse.source ∩
        hSource.localInverse ⁻¹' (coverLocal.trans targetLocal).source
    refine ⟨hSource.localInverse_mem_source, ?_⟩
    change hSource.localInverse (mappingTorusMk
      (identityMappingTorusData (X := X) I period hPeriod) coverPoint) ∈
        (coverLocal.trans targetLocal).source
    rw [hSource.localInverse_left_inv hSource.localInverse_mem_target]
    refine ⟨hCoverLocalSource, ?_⟩
    change coverLocal coverPoint ∈ targetLocal.source
    rw [← hCoverLocalEq hCoverLocalSource]
    exact hTargetLocalSource
  · intro point hPoint
    have hInverse : sourceProjection (hSource.localInverse point) = point := by
      exact hSource.localInverse_right_inv hPoint.1
    calc
      identityMappingTorusMap I period hPeriod J fiberMap point =
          identityMappingTorusMap I period hPeriod J fiberMap
            (sourceProjection (hSource.localInverse point)) := congrArg _ hInverse.symm
      _ = targetProjection
          (identityMappingTorusCoverMap I period hPeriod J fiberMap
            (hSource.localInverse point)) := rfl
      _ = Φ point := by
        change targetProjection
            (identityMappingTorusCoverMap I period hPeriod J fiberMap
              (hSource.localInverse point)) =
          targetLocal (coverLocal (hSource.localInverse point))
        have hCoverEq := hCoverLocalEq hPoint.2.1
        change identityMappingTorusCoverMap I period hPeriod J fiberMap
            (hSource.localInverse point) =
          coverLocal (hSource.localInverse point) at hCoverEq
        have hTargetEq := hTargetLocalEq hPoint.2.2
        change targetProjection (coverLocal (hSource.localInverse point)) =
          targetLocal (coverLocal (hSource.localInverse point)) at hTargetEq
        rw [hCoverEq, hTargetEq]

end
end P0EFTJanusIdentityMappingTorusLocalDiffeomorph4D
end JanusFormal
