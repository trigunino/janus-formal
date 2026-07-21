import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusSmoothQuotientManifold

/-!
# Smooth descent of equivariant maps between mapping tori

A smooth cover map commuting with every integer deck transformation descends
to a smooth map between the corresponding smooth mapping-torus quotients.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusEquivariantSmoothDescent4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (sourceData : MappingTorusData X) (targetData : MappingTorusData Y)
  (coverMap : MappingTorusCover sourceData → MappingTorusCover targetData)
  (hEquivariant : ∀ (winding : Int) (point : MappingTorusCover sourceData),
    coverMap (winding +ᵥ point) = winding +ᵥ coverMap point)

/-- Quotient map induced by an integer-deck-equivariant cover map. -/
def mappingTorusEquivariantMap :
    MappingTorus sourceData → MappingTorus targetData :=
  Quotient.map coverMap (fun first second hOrbit => by
    change AddAction.orbitRel Int (MappingTorusCover sourceData)
      first second at hOrbit
    change AddAction.orbitRel Int (MappingTorusCover targetData)
      (coverMap first) (coverMap second)
    rw [AddAction.orbitRel_apply, AddAction.mem_orbit_iff] at hOrbit ⊢
    rcases hOrbit with ⟨winding, hWinding⟩
    refine ⟨winding, ?_⟩
    rw [← hEquivariant]
    exact congrArg coverMap hWinding)

@[simp] theorem mappingTorusEquivariantMap_mk
    (point : MappingTorusCover sourceData) :
    mappingTorusEquivariantMap sourceData targetData coverMap hEquivariant
        (mappingTorusMk sourceData point) =
      mappingTorusMk targetData (coverMap point) :=
  rfl

variable {Z : Type*} [TopologicalSpace Z]

/-- Quotient map induced by a cover map invariant under every integer deck. -/
def mappingTorusInvariantMap
    (invariantMap : MappingTorusCover sourceData → Z)
    (hInvariant : ∀ (winding : Int) (point : MappingTorusCover sourceData),
      invariantMap (winding +ᵥ point) = invariantMap point) :
    MappingTorus sourceData → Z :=
  Quotient.lift invariantMap (fun first second hOrbit => by
    change AddAction.orbitRel Int (MappingTorusCover sourceData)
      first second at hOrbit
    rw [AddAction.orbitRel_apply, AddAction.mem_orbit_iff] at hOrbit
    rcases hOrbit with ⟨winding, hWinding⟩
    rw [← hWinding, hInvariant])

omit [TopologicalSpace Z] in
@[simp] theorem mappingTorusInvariantMap_mk
    (invariantMap : MappingTorusCover sourceData → Z)
    (hInvariant : ∀ (winding : Int) (point : MappingTorusCover sourceData),
      invariantMap (winding +ᵥ point) = invariantMap point)
    (point : MappingTorusCover sourceData) :
    mappingTorusInvariantMap sourceData invariantMap hInvariant
        (mappingTorusMk sourceData point) = invariantMap point :=
  rfl

variable {W : Type*} [TopologicalSpace W]

/-- Parameterized quotient map induced by invariance in the mapping-torus
cover variable. -/
def mappingTorusInvariantMapProd
    (invariantMap : MappingTorusCover sourceData × W → Z)
    (hInvariant : ∀ (winding : Int) (point : MappingTorusCover sourceData × W),
      invariantMap (winding +ᵥ point.1, point.2) = invariantMap point) :
    MappingTorus sourceData × W → Z :=
  fun point => Quotient.lift
    (fun coverPoint => invariantMap (coverPoint, point.2))
    (fun first second hOrbit => by
      change AddAction.orbitRel Int (MappingTorusCover sourceData)
        first second at hOrbit
      rw [AddAction.orbitRel_apply, AddAction.mem_orbit_iff] at hOrbit
      rcases hOrbit with ⟨winding, hWinding⟩
      rw [← hWinding]
      exact hInvariant winding (second, point.2)) point.1

omit [TopologicalSpace Z] [TopologicalSpace W] in
@[simp] theorem mappingTorusInvariantMapProd_mk
    (invariantMap : MappingTorusCover sourceData × W → Z)
    (hInvariant : ∀ (winding : Int) (point : MappingTorusCover sourceData × W),
      invariantMap (winding +ᵥ point.1, point.2) = invariantMap point)
    (coverPoint : MappingTorusCover sourceData) (parameter : W) :
    mappingTorusInvariantMapProd sourceData invariantMap hInvariant
        (mappingTorusMk sourceData coverPoint, parameter) =
      invariantMap (coverPoint, parameter) :=
  rfl

variable {𝕜 E H E' H' : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [TopologicalSpace H] [TopologicalSpace H']
  (sourceModel : ModelWithCorners 𝕜 E H)
  (targetModel : ModelWithCorners 𝕜 E' H') (n : ℕ∞ω)
  [ChartedSpace H (MappingTorusCover sourceData)]
  [ChartedSpace H (MappingTorus sourceData)]
  [ChartedSpace H' (MappingTorusCover targetData)]
  [ChartedSpace H' (MappingTorus targetData)]

/-- Smooth equivariant cover maps descend smoothly through local inverses of
the source covering projection. -/
theorem mappingTorusEquivariantMap_contMDiff
    (hSourceProjection : IsLocalDiffeomorph sourceModel sourceModel n
      (mappingTorusMk sourceData))
    (hTargetProjection : IsLocalDiffeomorph targetModel targetModel n
      (mappingTorusMk targetData))
    (hCoverMap : ContMDiff sourceModel targetModel n coverMap) :
    ContMDiff sourceModel targetModel n
      (mappingTorusEquivariantMap sourceData targetData coverMap
        hEquivariant) := by
  intro quotientPoint
  obtain ⟨coverPoint, rfl⟩ :=
    mappingTorusMk_surjective sourceData quotientPoint
  have hAt := hSourceProjection coverPoint
  have hLocal : ContMDiffAt sourceModel targetModel n
      (mappingTorusMk targetData ∘ coverMap ∘ hAt.localInverse)
      (mappingTorusMk sourceData coverPoint) :=
    hTargetProjection.contMDiff.contMDiffAt.comp _
      (hCoverMap.contMDiffAt.comp _
        (hAt.localInverse_contMDiffAt.of_le le_rfl))
  apply hLocal.congr_of_eventuallyEq
  filter_upwards [hAt.localInverse_eventuallyEq_right] with point hPoint
  have hPoint' : mappingTorusMk sourceData (hAt.localInverse point) = point := by
    simpa [Function.comp_def] using hPoint
  calc
    mappingTorusEquivariantMap sourceData targetData coverMap hEquivariant point =
        mappingTorusEquivariantMap sourceData targetData coverMap hEquivariant
          (mappingTorusMk sourceData (hAt.localInverse point)) :=
      congrArg _ hPoint'.symm
    _ = mappingTorusMk targetData (coverMap (hAt.localInverse point)) := rfl

variable {E'' H'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  [TopologicalSpace H''] [ChartedSpace H'' Z]

/-- Smooth deck-invariant cover maps descend to an arbitrary smooth target. -/
theorem mappingTorusInvariantMap_contMDiff
    (targetModel' : ModelWithCorners 𝕜 E'' H'')
    (invariantMap : MappingTorusCover sourceData → Z)
    (hInvariant : ∀ (winding : Int) (point : MappingTorusCover sourceData),
      invariantMap (winding +ᵥ point) = invariantMap point)
    (hSourceProjection : IsLocalDiffeomorph sourceModel sourceModel n
      (mappingTorusMk sourceData))
    (hInvariantMap : ContMDiff sourceModel targetModel' n invariantMap) :
    ContMDiff sourceModel targetModel' n
      (mappingTorusInvariantMap sourceData invariantMap hInvariant) := by
  intro quotientPoint
  obtain ⟨coverPoint, rfl⟩ :=
    mappingTorusMk_surjective sourceData quotientPoint
  have hAt := hSourceProjection coverPoint
  have hLocal : ContMDiffAt sourceModel targetModel' n
      (invariantMap ∘ hAt.localInverse)
      (mappingTorusMk sourceData coverPoint) :=
    hInvariantMap.contMDiffAt.comp _
      (hAt.localInverse_contMDiffAt.of_le le_rfl)
  apply hLocal.congr_of_eventuallyEq
  filter_upwards [hAt.localInverse_eventuallyEq_right] with point hPoint
  have hPoint' : mappingTorusMk sourceData (hAt.localInverse point) = point := by
    simpa [Function.comp_def] using hPoint
  calc
    mappingTorusInvariantMap sourceData invariantMap hInvariant point =
        mappingTorusInvariantMap sourceData invariantMap hInvariant
          (mappingTorusMk sourceData (hAt.localInverse point)) :=
      congrArg _ hPoint'.symm
    _ = invariantMap (hAt.localInverse point) := rfl

variable {EW HW : Type*} [NormedAddCommGroup EW] [NormedSpace 𝕜 EW]
  [TopologicalSpace HW] [ChartedSpace HW W]

/-- Parameterized smooth invariant cover maps descend smoothly on the product
of the mapping-torus quotient with the parameter manifold. -/
theorem mappingTorusInvariantMapProd_contMDiff
    (parameterModel : ModelWithCorners 𝕜 EW HW)
    (targetModel' : ModelWithCorners 𝕜 E'' H'')
    (invariantMap : MappingTorusCover sourceData × W → Z)
    (hInvariant : ∀ (winding : Int) (point : MappingTorusCover sourceData × W),
      invariantMap (winding +ᵥ point.1, point.2) = invariantMap point)
    (hSourceProjection : IsLocalDiffeomorph sourceModel sourceModel n
      (mappingTorusMk sourceData))
    (hInvariantMap : ContMDiff (sourceModel.prod parameterModel)
      targetModel' n invariantMap) :
    ContMDiff (sourceModel.prod parameterModel) targetModel' n
      (mappingTorusInvariantMapProd sourceData invariantMap hInvariant) := by
  rintro ⟨quotientPoint, parameter⟩
  obtain ⟨coverPoint, rfl⟩ :=
    mappingTorusMk_surjective sourceData quotientPoint
  have hAt := hSourceProjection coverPoint
  have hFirst : ContMDiffAt (sourceModel.prod parameterModel) sourceModel n
      (fun point => hAt.localInverse point.1)
      (mappingTorusMk sourceData coverPoint, parameter) :=
    hAt.localInverse_contMDiffAt.of_le le_rfl |>.comp
      (mappingTorusMk sourceData coverPoint, parameter) contMDiffAt_fst
  have hLift : ContMDiffAt (sourceModel.prod parameterModel)
      (sourceModel.prod parameterModel) n
      (fun point => (hAt.localInverse point.1, point.2))
      (mappingTorusMk sourceData coverPoint, parameter) :=
    hFirst.prodMk contMDiffAt_snd
  have hLocal : ContMDiffAt (sourceModel.prod parameterModel) targetModel' n
      (invariantMap ∘ fun point => (hAt.localInverse point.1, point.2))
      (mappingTorusMk sourceData coverPoint, parameter) :=
    hInvariantMap.contMDiffAt.comp _ hLift
  apply hLocal.congr_of_eventuallyEq
  have hFstContinuous : Filter.Tendsto Prod.fst
      (nhds (mappingTorusMk sourceData coverPoint, parameter))
      (nhds (mappingTorusMk sourceData coverPoint)) := continuousAt_fst
  have hRight := hAt.localInverse_eventuallyEq_right.comp_tendsto hFstContinuous
  filter_upwards [hRight] with point hPoint
  calc
    mappingTorusInvariantMapProd sourceData invariantMap hInvariant point =
        mappingTorusInvariantMapProd sourceData invariantMap hInvariant
          (mappingTorusMk sourceData (hAt.localInverse point.1), point.2) := by
      apply congrArg _
      apply Prod.ext
      · simpa [Function.comp_def] using hPoint.symm
      · rfl
    _ = invariantMap (hAt.localInverse point.1, point.2) := rfl

end
end P0EFTJanusMappingTorusEquivariantSmoothDescent4D
end JanusFormal
