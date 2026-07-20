import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusEquivariantSmoothDescent4D

/-!
# Smooth functoriality of identity mapping tori

A smooth manifold `X` and a nonzero real period define a smooth mapping torus
with identity monodromy.  A smooth diffeomorphism of fibers induces a smooth
diffeomorphism of these mapping tori.
-/

namespace JanusFormal
namespace P0EFTJanusIdentityMappingTorusSmoothFunctor4D

set_option autoImplicit false
noncomputable section

open Set Topology
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusEquivariantSmoothDescent4D

abbrev IdentityCoverCoordinates (E : Type*) := E × Real
abbrev IdentityCoverModel (H : Type*) := ModelProd H Real

abbrev identityCoverModelWithCorners
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [TopologicalSpace H] (I : ModelWithCorners Real E H) :
    ModelWithCorners Real (IdentityCoverCoordinates E)
      (IdentityCoverModel H) :=
  I.prod 𝓘(Real, Real)

variable {E H X : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [TopologicalSpace H] [TopologicalSpace X] [T2Space X]
  [LocallyCompactSpace X] [ChartedSpace H X]
  (I : ModelWithCorners Real E H) [IsManifold I ∞ X]
  (period : Real) (hPeriod : period ≠ 0)

/-- Identity-monodromy data with the chosen nonzero period. -/
def identityMappingTorusData
    (_I : ModelWithCorners Real E H) (period' : Real)
    (hPeriod' : period' ≠ 0) : MappingTorusData X where
  monodromy := Homeomorph.refl X
  period := period'
  period_ne_zero := hPeriod'

@[implicit_reducible] def identityMappingTorusCoverChartedSpace :
    ChartedSpace (IdentityCoverModel H)
      (MappingTorusCover (identityMappingTorusData (X := X) I period hPeriod)) :=
  chartedSpacePullback
    (coverHomeomorphProd (identityMappingTorusData (X := X) I period hPeriod))

omit [T2Space X] [LocallyCompactSpace X] in
theorem identityMappingTorusCover_isManifold :
    @IsManifold Real _ (IdentityCoverCoordinates E) _ _
      (IdentityCoverModel H) _ (identityCoverModelWithCorners I) ∞
      (MappingTorusCover (identityMappingTorusData (X := X) I period hPeriod)) _
      (identityMappingTorusCoverChartedSpace (X := X) I period hPeriod) :=
  isManifold_chartedSpacePullback (identityCoverModelWithCorners I) ∞
    (coverHomeomorphProd (identityMappingTorusData (X := X) I period hPeriod))

def identityMappingTorusProductDeck
    (_I : ModelWithCorners Real E H) (period' : Real) (winding : Int) :
    X × Real → X × Real :=
  fun point => (point.1, point.2 + (winding : Real) * period')

omit [T2Space X] [LocallyCompactSpace X] [IsManifold I ∞ X] in
theorem identityMappingTorusProductDeck_contMDiff (winding : Int) :
    ContMDiff (identityCoverModelWithCorners I)
      (identityCoverModelWithCorners I) ∞
      (identityMappingTorusProductDeck (X := X) I period winding) := by
  have hTime : ContMDiff 𝓘(Real, Real) 𝓘(Real, Real) ∞
      (fun time : Real => time + (winding : Real) * period) :=
    (contDiff_id.add contDiff_const).contMDiff.congr fun _ => rfl
  exact (contMDiff_id : ContMDiff I I ∞ (id : X → X)).prodMap hTime

omit [T2Space X] [LocallyCompactSpace X] in
theorem identityMappingTorusCover_deck_contMDiff (winding : Int) :
    letI : ChartedSpace (IdentityCoverModel H)
        (MappingTorusCover (identityMappingTorusData (X := X) I period hPeriod)) :=
      identityMappingTorusCoverChartedSpace (X := X) I period hPeriod
    ContMDiff (identityCoverModelWithCorners I)
      (identityCoverModelWithCorners I) ∞
      (winding +ᵥ · : MappingTorusCover
        (identityMappingTorusData (X := X) I period hPeriod) →
          MappingTorusCover (identityMappingTorusData (X := X) I period hPeriod)) := by
  letI : ChartedSpace (IdentityCoverModel H)
      (MappingTorusCover (identityMappingTorusData (X := X) I period hPeriod)) :=
    identityMappingTorusCoverChartedSpace (X := X) I period hPeriod
  letI : IsManifold (identityCoverModelWithCorners I) ∞
      (MappingTorusCover (identityMappingTorusData (X := X) I period hPeriod)) :=
    identityMappingTorusCover_isManifold (X := X) I period hPeriod
  have hTo := chartedSpacePullback_toFun_contMDiff
    (identityCoverModelWithCorners I) ∞
    (coverHomeomorphProd (identityMappingTorusData (X := X) I period hPeriod))
  have hInv := chartedSpacePullback_invFun_contMDiff
    (identityCoverModelWithCorners I) ∞
    (coverHomeomorphProd (identityMappingTorusData (X := X) I period hPeriod))
  have hComposite := hInv.comp
    ((identityMappingTorusProductDeck_contMDiff I period winding).comp hTo)
  exact hComposite.congr fun point => by
    apply MappingTorusCover.ext
    · change (((Homeomorph.refl X) ^ winding) point.fiber) = point.fiber
      rw [show (((Homeomorph.refl X) ^ winding) point.fiber) =
          ((Homeomorph.refl X) ^ winding).toEquiv point.fiber from rfl,
        homeomorph_toEquiv_zpow]
      rw [show (Homeomorph.refl X).toEquiv = 1 from rfl, one_zpow]
      rfl
    · rfl

@[implicit_reducible] def identityMappingTorusQuotientChartedSpace :
    ChartedSpace (IdentityCoverModel H)
      (MappingTorus (identityMappingTorusData (X := X) I period hPeriod)) := by
  letI : ChartedSpace (IdentityCoverModel H)
      (MappingTorusCover (identityMappingTorusData (X := X) I period hPeriod)) :=
    identityMappingTorusCoverChartedSpace (X := X) I period hPeriod
  exact mappingTorusSmoothChartedSpace
    (identityMappingTorusData (X := X) I period hPeriod)

theorem identityMappingTorus_isManifold :
    @IsManifold Real _ (IdentityCoverCoordinates E) _ _
      (IdentityCoverModel H) _ (identityCoverModelWithCorners I) ∞
      (MappingTorus (identityMappingTorusData (X := X) I period hPeriod)) _
      (identityMappingTorusQuotientChartedSpace (X := X) I period hPeriod) := by
  letI : ChartedSpace (IdentityCoverModel H)
      (MappingTorusCover (identityMappingTorusData (X := X) I period hPeriod)) :=
    identityMappingTorusCoverChartedSpace (X := X) I period hPeriod
  letI : IsManifold (identityCoverModelWithCorners I) ∞
      (MappingTorusCover (identityMappingTorusData (X := X) I period hPeriod)) :=
    identityMappingTorusCover_isManifold (X := X) I period hPeriod
  exact mappingTorus_isManifold_of_smooth_deck
    (identityCoverModelWithCorners I) ∞
    (identityMappingTorusData (X := X) I period hPeriod)
    (identityMappingTorusCover_deck_contMDiff I period hPeriod)

theorem identityMappingTorus_projection_isLocalDiffeomorph :
    letI : ChartedSpace (IdentityCoverModel H)
        (MappingTorusCover (identityMappingTorusData (X := X) I period hPeriod)) :=
      identityMappingTorusCoverChartedSpace (X := X) I period hPeriod
    letI : IsManifold (identityCoverModelWithCorners I) ∞
        (MappingTorusCover (identityMappingTorusData (X := X) I period hPeriod)) :=
      identityMappingTorusCover_isManifold (X := X) I period hPeriod
    letI : ChartedSpace (IdentityCoverModel H)
        (MappingTorus (identityMappingTorusData (X := X) I period hPeriod)) :=
      identityMappingTorusQuotientChartedSpace (X := X) I period hPeriod
    letI : IsManifold (identityCoverModelWithCorners I) ∞
        (MappingTorus (identityMappingTorusData (X := X) I period hPeriod)) :=
      identityMappingTorus_isManifold (X := X) I period hPeriod
    IsLocalDiffeomorph (identityCoverModelWithCorners I)
      (identityCoverModelWithCorners I) ∞
      (mappingTorusMk (identityMappingTorusData (X := X) I period hPeriod)) := by
  letI : ChartedSpace (IdentityCoverModel H)
      (MappingTorusCover (identityMappingTorusData (X := X) I period hPeriod)) :=
    identityMappingTorusCoverChartedSpace (X := X) I period hPeriod
  letI : IsManifold (identityCoverModelWithCorners I) ∞
      (MappingTorusCover (identityMappingTorusData (X := X) I period hPeriod)) :=
    identityMappingTorusCover_isManifold (X := X) I period hPeriod
  letI : ChartedSpace (IdentityCoverModel H)
      (MappingTorus (identityMappingTorusData (X := X) I period hPeriod)) :=
    identityMappingTorusQuotientChartedSpace (X := X) I period hPeriod
  letI : IsManifold (identityCoverModelWithCorners I) ∞
      (MappingTorus (identityMappingTorusData (X := X) I period hPeriod)) :=
    identityMappingTorus_isManifold (X := X) I period hPeriod
  exact mappingTorus_projection_isLocalDiffeomorph
    (identityCoverModelWithCorners I) ∞
    (identityMappingTorusData (X := X) I period hPeriod)
    (identityMappingTorusCover_deck_contMDiff I period hPeriod)

section Functoriality

variable {E' H' Y : Type*} [NormedAddCommGroup E'] [NormedSpace Real E']
  [TopologicalSpace H'] [TopologicalSpace Y] [T2Space Y]
  [LocallyCompactSpace Y] [ChartedSpace H' Y]
  (J : ModelWithCorners Real E' H') [IsManifold J ∞ Y]

def identityMappingTorusCoverMap
    (fiberMap : X → Y)
    (point : MappingTorusCover (identityMappingTorusData (X := X) I period hPeriod)) :
    MappingTorusCover (identityMappingTorusData (X := Y) J period hPeriod) :=
  ⟨fiberMap point.fiber, point.time⟩

omit [T2Space X] [LocallyCompactSpace X] [ChartedSpace H X]
    [IsManifold I ∞ X] [T2Space Y] [LocallyCompactSpace Y]
    [ChartedSpace H' Y] [IsManifold J ∞ Y] in
theorem identityMappingTorusCoverMap_equivariant
    (fiberMap : X → Y) (winding : Int)
    (point : MappingTorusCover (identityMappingTorusData (X := X) I period hPeriod)) :
    identityMappingTorusCoverMap I period hPeriod J fiberMap
        (winding +ᵥ point) =
      winding +ᵥ identityMappingTorusCoverMap I period hPeriod J fiberMap point := by
  apply MappingTorusCover.ext
  · change fiberMap (((Homeomorph.refl X) ^ winding) point.fiber) =
      ((Homeomorph.refl Y) ^ winding) (fiberMap point.fiber)
    rw [show (((Homeomorph.refl X) ^ winding) point.fiber) =
        ((Homeomorph.refl X) ^ winding).toEquiv point.fiber from rfl,
      show (((Homeomorph.refl Y) ^ winding) (fiberMap point.fiber)) =
        ((Homeomorph.refl Y) ^ winding).toEquiv
          (fiberMap point.fiber) from rfl,
      homeomorph_toEquiv_zpow, homeomorph_toEquiv_zpow,
      show (Homeomorph.refl X).toEquiv = 1 from rfl,
      show (Homeomorph.refl Y).toEquiv = 1 from rfl, one_zpow]
    simp
  · rfl

omit [T2Space X] [LocallyCompactSpace X] [ChartedSpace H X]
    [IsManifold I ∞ X] [T2Space Y] [LocallyCompactSpace Y]
    [ChartedSpace H' Y] [IsManifold J ∞ Y] in
theorem identityMappingTorusCoverMap_isOpenEmbedding
    (fiberMap : X → Y) (hFiberMap : IsOpenEmbedding fiberMap) :
    IsOpenEmbedding
      (identityMappingTorusCoverMap I period hPeriod J fiberMap) := by
  have hProduct : IsOpenEmbedding
      (Prod.map fiberMap (id : Real → Real)) :=
    hFiberMap.prodMap (Homeomorph.refl Real).isOpenEmbedding
  have hComposite :=
    (coverHomeomorphProd
      (identityMappingTorusData (X := Y) J period hPeriod)).symm.isOpenEmbedding.comp
      (hProduct.comp
        (coverHomeomorphProd
          (identityMappingTorusData (X := X) I period hPeriod)).isOpenEmbedding)
  convert hComposite using 1
  all_goals
    funext point
    rfl

omit [T2Space X] [LocallyCompactSpace X]
    [T2Space Y] [LocallyCompactSpace Y] in
theorem identityMappingTorusCoverMap_contMDiff
    (fiberMap : X → Y) (hFiberMap : ContMDiff I J ∞ fiberMap) :
    letI : ChartedSpace (IdentityCoverModel H)
        (MappingTorusCover (identityMappingTorusData (X := X) I period hPeriod)) :=
      identityMappingTorusCoverChartedSpace (X := X) I period hPeriod
    letI : ChartedSpace (IdentityCoverModel H')
        (MappingTorusCover (identityMappingTorusData (X := Y) J period hPeriod)) :=
      identityMappingTorusCoverChartedSpace (X := Y) J period hPeriod
    ContMDiff (identityCoverModelWithCorners I)
      (identityCoverModelWithCorners J) ∞
      (identityMappingTorusCoverMap I period hPeriod J fiberMap) := by
  letI : ChartedSpace (IdentityCoverModel H)
      (MappingTorusCover (identityMappingTorusData (X := X) I period hPeriod)) :=
    identityMappingTorusCoverChartedSpace (X := X) I period hPeriod
  letI : IsManifold (identityCoverModelWithCorners I) ∞
      (MappingTorusCover (identityMappingTorusData (X := X) I period hPeriod)) :=
    identityMappingTorusCover_isManifold (X := X) I period hPeriod
  letI : ChartedSpace (IdentityCoverModel H')
      (MappingTorusCover (identityMappingTorusData (X := Y) J period hPeriod)) :=
    identityMappingTorusCoverChartedSpace (X := Y) J period hPeriod
  letI : IsManifold (identityCoverModelWithCorners J) ∞
      (MappingTorusCover (identityMappingTorusData (X := Y) J period hPeriod)) :=
    identityMappingTorusCover_isManifold (X := Y) J period hPeriod
  have hTo := chartedSpacePullback_toFun_contMDiff
    (identityCoverModelWithCorners I) ∞
    (coverHomeomorphProd (identityMappingTorusData (X := X) I period hPeriod))
  have hInv := chartedSpacePullback_invFun_contMDiff
    (identityCoverModelWithCorners J) ∞
    (coverHomeomorphProd (identityMappingTorusData (X := Y) J period hPeriod))
  have hProduct : ContMDiff (identityCoverModelWithCorners I)
      (identityCoverModelWithCorners J) ∞
      (Prod.map fiberMap (id : Real → Real)) :=
    hFiberMap.prodMap contMDiff_id
  exact (hInv.comp (hProduct.comp hTo)).congr fun point => by
    apply MappingTorusCover.ext <;> rfl

def identityMappingTorusMap (fiberMap : X → Y) :
    MappingTorus (identityMappingTorusData (X := X) I period hPeriod) →
      MappingTorus (identityMappingTorusData (X := Y) J period hPeriod) :=
  mappingTorusEquivariantMap
    (identityMappingTorusData (X := X) I period hPeriod)
    (identityMappingTorusData (X := Y) J period hPeriod)
    (identityMappingTorusCoverMap I period hPeriod J fiberMap)
    (identityMappingTorusCoverMap_equivariant I period hPeriod J fiberMap)

omit [T2Space X] [LocallyCompactSpace X]
    [T2Space Y] [LocallyCompactSpace Y]
    [ChartedSpace H X] [IsManifold I ∞ X]
    [ChartedSpace H' Y] [IsManifold J ∞ Y] in
theorem identityMappingTorusMap_injective
    (fiberMap : X → Y) (hFiberMap : Function.Injective fiberMap) :
    Function.Injective (identityMappingTorusMap I period hPeriod J fiberMap) := by
  intro first second
  refine Quotient.inductionOn first ?_
  intro firstRepresentative
  refine Quotient.inductionOn second ?_
  intro secondRepresentative hEqual
  change mappingTorusMk
      (identityMappingTorusData (X := Y) J period hPeriod)
      (identityMappingTorusCoverMap I period hPeriod J fiberMap
        firstRepresentative) =
    mappingTorusMk (identityMappingTorusData (X := Y) J period hPeriod)
      (identityMappingTorusCoverMap I period hPeriod J fiberMap
        secondRepresentative) at hEqual
  rw [mappingTorusMk_eq_iff_exists_vadd] at hEqual ⊢
  rcases hEqual with ⟨winding, hWinding⟩
  refine ⟨winding, ?_⟩
  apply MappingTorusCover.ext
  · change ((Homeomorph.refl X) ^ winding) secondRepresentative.fiber =
      firstRepresentative.fiber
    have hTargetFiber := congrArg
      (fun point : MappingTorusCover
        (identityMappingTorusData (X := Y) J period hPeriod) => point.fiber)
      hWinding
    change ((Homeomorph.refl Y) ^ winding)
        (fiberMap secondRepresentative.fiber) =
      fiberMap firstRepresentative.fiber at hTargetFiber
    rw [show (((Homeomorph.refl X) ^ winding) secondRepresentative.fiber) =
        ((Homeomorph.refl X) ^ winding).toEquiv
          secondRepresentative.fiber from rfl,
      homeomorph_toEquiv_zpow,
      show (Homeomorph.refl X).toEquiv = 1 from rfl, one_zpow]
    rw [show (((Homeomorph.refl Y) ^ winding)
          (fiberMap secondRepresentative.fiber)) =
        ((Homeomorph.refl Y) ^ winding).toEquiv
          (fiberMap secondRepresentative.fiber) from rfl,
      homeomorph_toEquiv_zpow,
      show (Homeomorph.refl Y).toEquiv = 1 from rfl, one_zpow]
      at hTargetFiber
    simpa using hFiberMap hTargetFiber
  · exact congrArg
      (fun point : MappingTorusCover
        (identityMappingTorusData (X := Y) J period hPeriod) => point.time)
      hWinding

omit [T2Space X] [LocallyCompactSpace X]
    [T2Space Y] [LocallyCompactSpace Y]
    [ChartedSpace H X] [IsManifold I ∞ X]
    [ChartedSpace H' Y] [IsManifold J ∞ Y] in
theorem continuous_identityMappingTorusMap
    (fiberMap : X → Y) (hFiberMap : IsOpenEmbedding fiberMap) :
    Continuous (identityMappingTorusMap I period hPeriod J fiberMap) := by
  apply (continuous_quotient_mk'.comp ?_).quotient_lift
  exact (identityMappingTorusCoverMap_isOpenEmbedding
    I period hPeriod J fiberMap hFiberMap).continuous

omit [T2Space X] [LocallyCompactSpace X]
    [ChartedSpace H X] [IsManifold I ∞ X]
    [ChartedSpace H' Y] [IsManifold J ∞ Y] in
theorem identityMappingTorusMap_isOpenMap
    (fiberMap : X → Y) (hFiberMap : IsOpenEmbedding fiberMap) :
    IsOpenMap (identityMappingTorusMap I period hPeriod J fiberMap) := by
  intro source hSource
  let sourceProjection := mappingTorusMk
    (identityMappingTorusData (X := X) I period hPeriod)
  let targetProjection := mappingTorusMk
    (identityMappingTorusData (X := Y) J period hPeriod)
  have hSourcePreimage : IsOpen (sourceProjection ⁻¹' source) :=
    hSource.preimage continuous_quotient_mk'
  have hCoverImage : IsOpen
      (identityMappingTorusCoverMap I period hPeriod J fiberMap ''
        (sourceProjection ⁻¹' source)) :=
    (identityMappingTorusCoverMap_isOpenEmbedding
      I period hPeriod J fiberMap hFiberMap).isOpenMap _ hSourcePreimage
  have hTargetImage : IsOpen
      (targetProjection ''
        (identityMappingTorusCoverMap I period hPeriod J fiberMap ''
          (sourceProjection ⁻¹' source))) :=
    (mappingTorusMk_isCoveringMap
      (identityMappingTorusData (X := Y) J period hPeriod)).isLocalHomeomorph
        |>.isOpenMap _ hCoverImage
  have hImage : identityMappingTorusMap I period hPeriod J fiberMap '' source =
      targetProjection ''
        (identityMappingTorusCoverMap I period hPeriod J fiberMap ''
          (sourceProjection ⁻¹' source)) := by
    ext target
    constructor
    · rintro ⟨quotient, hQuotient, rfl⟩
      obtain ⟨representative, rfl⟩ := mappingTorusMk_surjective
        (identityMappingTorusData (X := X) I period hPeriod) quotient
      exact ⟨identityMappingTorusCoverMap I period hPeriod J fiberMap
        representative, ⟨representative, hQuotient, rfl⟩, rfl⟩
    · rintro ⟨-, ⟨representative, hRepresentative, rfl⟩, rfl⟩
      exact ⟨sourceProjection representative, hRepresentative, rfl⟩
  rw [hImage]
  exact hTargetImage

omit [T2Space X] [LocallyCompactSpace X]
    [ChartedSpace H X] [IsManifold I ∞ X]
    [ChartedSpace H' Y] [IsManifold J ∞ Y] in
theorem identityMappingTorusMap_isOpenEmbedding
    (fiberMap : X → Y) (hFiberMap : IsOpenEmbedding fiberMap) :
    IsOpenEmbedding (identityMappingTorusMap I period hPeriod J fiberMap) :=
  IsOpenEmbedding.of_continuous_injective_isOpenMap
    (continuous_identityMappingTorusMap I period hPeriod J fiberMap hFiberMap)
    (identityMappingTorusMap_injective I period hPeriod J fiberMap
      hFiberMap.injective)
    (identityMappingTorusMap_isOpenMap I period hPeriod J fiberMap hFiberMap)

theorem identityMappingTorusMap_contMDiff
    (fiberMap : X → Y) (hFiberMap : ContMDiff I J ∞ fiberMap) :
    letI : ChartedSpace (IdentityCoverModel H)
        (MappingTorusCover (identityMappingTorusData (X := X) I period hPeriod)) :=
      identityMappingTorusCoverChartedSpace (X := X) I period hPeriod
    letI : ChartedSpace (IdentityCoverModel H)
        (MappingTorus (identityMappingTorusData (X := X) I period hPeriod)) :=
      identityMappingTorusQuotientChartedSpace (X := X) I period hPeriod
    letI : ChartedSpace (IdentityCoverModel H')
        (MappingTorusCover (identityMappingTorusData (X := Y) J period hPeriod)) :=
      identityMappingTorusCoverChartedSpace (X := Y) J period hPeriod
    letI : ChartedSpace (IdentityCoverModel H')
        (MappingTorus (identityMappingTorusData (X := Y) J period hPeriod)) :=
      identityMappingTorusQuotientChartedSpace (X := Y) J period hPeriod
    ContMDiff (identityCoverModelWithCorners I)
      (identityCoverModelWithCorners J) ∞
      (identityMappingTorusMap I period hPeriod J fiberMap) := by
  letI : ChartedSpace (IdentityCoverModel H)
      (MappingTorusCover (identityMappingTorusData (X := X) I period hPeriod)) :=
    identityMappingTorusCoverChartedSpace (X := X) I period hPeriod
  letI : IsManifold (identityCoverModelWithCorners I) ∞
      (MappingTorusCover (identityMappingTorusData (X := X) I period hPeriod)) :=
    identityMappingTorusCover_isManifold (X := X) I period hPeriod
  letI : ChartedSpace (IdentityCoverModel H)
      (MappingTorus (identityMappingTorusData (X := X) I period hPeriod)) :=
    identityMappingTorusQuotientChartedSpace (X := X) I period hPeriod
  letI : IsManifold (identityCoverModelWithCorners I) ∞
      (MappingTorus (identityMappingTorusData (X := X) I period hPeriod)) :=
    identityMappingTorus_isManifold (X := X) I period hPeriod
  letI : ChartedSpace (IdentityCoverModel H')
      (MappingTorusCover (identityMappingTorusData (X := Y) J period hPeriod)) :=
    identityMappingTorusCoverChartedSpace (X := Y) J period hPeriod
  letI : IsManifold (identityCoverModelWithCorners J) ∞
      (MappingTorusCover (identityMappingTorusData (X := Y) J period hPeriod)) :=
    identityMappingTorusCover_isManifold (X := Y) J period hPeriod
  letI : ChartedSpace (IdentityCoverModel H')
      (MappingTorus (identityMappingTorusData (X := Y) J period hPeriod)) :=
    identityMappingTorusQuotientChartedSpace (X := Y) J period hPeriod
  letI : IsManifold (identityCoverModelWithCorners J) ∞
      (MappingTorus (identityMappingTorusData (X := Y) J period hPeriod)) :=
    identityMappingTorus_isManifold (X := Y) J period hPeriod
  exact mappingTorusEquivariantMap_contMDiff
    (identityMappingTorusData (X := X) I period hPeriod)
    (identityMappingTorusData (X := Y) J period hPeriod)
    (identityMappingTorusCoverMap I period hPeriod J fiberMap)
    (identityMappingTorusCoverMap_equivariant I period hPeriod J fiberMap)
    (identityCoverModelWithCorners I) (identityCoverModelWithCorners J) ∞
    (identityMappingTorus_projection_isLocalDiffeomorph (X := X) I period hPeriod)
    (identityMappingTorus_projection_isLocalDiffeomorph (X := Y) J period hPeriod)
    (identityMappingTorusCoverMap_contMDiff I period hPeriod J fiberMap
      hFiberMap)

def identityMappingTorusDiffeomorph
    (fiberEquiv : X ≃ₘ^∞⟮I, J⟯ Y) :
    letI : ChartedSpace (IdentityCoverModel H)
        (MappingTorus (identityMappingTorusData (X := X) I period hPeriod)) :=
      identityMappingTorusQuotientChartedSpace (X := X) I period hPeriod
    letI : ChartedSpace (IdentityCoverModel H')
        (MappingTorus (identityMappingTorusData (X := Y) J period hPeriod)) :=
      identityMappingTorusQuotientChartedSpace (X := Y) J period hPeriod
    MappingTorus (identityMappingTorusData (X := X) I period hPeriod) ≃ₘ^∞⟮
      identityCoverModelWithCorners I, identityCoverModelWithCorners J⟯
        MappingTorus (identityMappingTorusData (X := Y) J period hPeriod) := by
  letI : ChartedSpace (IdentityCoverModel H)
      (MappingTorus (identityMappingTorusData (X := X) I period hPeriod)) :=
    identityMappingTorusQuotientChartedSpace (X := X) I period hPeriod
  letI : ChartedSpace (IdentityCoverModel H')
      (MappingTorus (identityMappingTorusData (X := Y) J period hPeriod)) :=
    identityMappingTorusQuotientChartedSpace (X := Y) J period hPeriod
  exact
    { toFun := identityMappingTorusMap I period hPeriod J fiberEquiv
      invFun := identityMappingTorusMap J period hPeriod I fiberEquiv.symm
      left_inv := by
        intro point
        refine Quotient.inductionOn point ?_
        intro representative
        apply congrArg
          (mappingTorusMk (identityMappingTorusData (X := X) I period hPeriod))
        apply MappingTorusCover.ext
        · exact fiberEquiv.symm_apply_apply representative.fiber
        · rfl
      right_inv := by
        intro point
        refine Quotient.inductionOn point ?_
        intro representative
        apply congrArg
          (mappingTorusMk (identityMappingTorusData (X := Y) J period hPeriod))
        apply MappingTorusCover.ext
        · exact fiberEquiv.apply_symm_apply representative.fiber
        · rfl
      contMDiff_toFun := identityMappingTorusMap_contMDiff I period hPeriod J
        fiberEquiv fiberEquiv.contMDiff
      contMDiff_invFun := identityMappingTorusMap_contMDiff J period hPeriod I
        fiberEquiv.symm fiberEquiv.symm.contMDiff }

end Functoriality

end
end P0EFTJanusIdentityMappingTorusSmoothFunctor4D
end JanusFormal
