import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusSmoothAtlasFrontier

/-!
# Compactness of the effective mapping torus

A compact fiber and one compact time interval cover the full orbit quotient.
This supplies the compact global base needed for bounded smooth fields and
finite-measure functional completions. No metric volume form is selected.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCompactQuotient

set_option autoImplicit false

noncomputable section

open Set Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier

variable {X : Type*} [TopologicalSpace X]

/-- A compact fundamental strip for the translation direction. -/
abbrev FundamentalStrip (data : MappingTorusData X) :=
  Prod X (Set.Icc (0 : Real) |data.period|)

/-- Projection of the compact fundamental strip to the orbit quotient. -/
def fundamentalStripProjection (data : MappingTorusData X) :
    FundamentalStrip data -> MappingTorus data :=
  fun point => mappingTorusMk data
    (MappingTorusCover.mk point.1 point.2.1)

theorem fundamentalStripProjection_continuous
    (data : MappingTorusData X) [T2Space X] [LocallyCompactSpace X] :
    Continuous (fundamentalStripProjection data) := by
  have hCover : Continuous
      (fun point : FundamentalStrip data =>
        (MappingTorusCover.mk point.1 point.2.1 : MappingTorusCover data)) := by
    have hProd : Continuous
        (fun point : FundamentalStrip data => Prod.mk point.1 point.2.1) :=
      continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
    exact (coverHomeomorphProd data).symm.continuous.comp hProd
  exact (mappingTorusMk_isCoveringMap data).continuous.comp hCover

private theorem translated_time_mem_strip
    (data : MappingTorusData X) (point : MappingTorusCover data) :
    Exists fun winding : Int =>
      (Set.Icc (0 : Real) |data.period|)
        (mappingTorusVAdd data winding point).time := by
  have hAbs : 0 < |data.period| := abs_pos.mpr data.period_ne_zero
  obtain ⟨winding, hWinding, -⟩ :=
    existsUnique_add_zsmul_mem_Ico hAbs point.time 0
  by_cases hPositive : 0 < data.period
  case pos =>
    refine Exists.intro winding ?_
    have hIcc : (Set.Icc (0 : Real) |data.period|)
        (point.time + winding • |data.period|) :=
      And.intro hWinding.1 (by simpa using hWinding.2.le)
    simpa [mappingTorusVAdd, abs_of_pos hPositive] using hIcc
  case neg =>
    have hNegative : data.period < 0 :=
      lt_of_le_of_ne (le_of_not_gt hPositive) data.period_ne_zero
    refine Exists.intro (-winding) ?_
    have hIcc : (Set.Icc (0 : Real) |data.period|)
        (point.time + winding • |data.period|) :=
      And.intro hWinding.1 (by simpa using hWinding.2.le)
    simpa [mappingTorusVAdd, abs_of_neg hNegative] using hIcc

theorem fundamentalStripProjection_surjective
    (data : MappingTorusData X) :
    Function.Surjective (fundamentalStripProjection data) := by
  intro quotientPoint
  obtain ⟨point, rfl⟩ := mappingTorusMk_surjective data quotientPoint
  obtain ⟨winding, hTime⟩ := translated_time_mem_strip data point
  refine Exists.intro
    (Prod.mk (mappingTorusVAdd data winding point).fiber
      (Subtype.mk (mappingTorusVAdd data winding point).time hTime)) ?_
  apply (mappingTorusMk_eq_iff_exists_vadd data _ _).2
  exact Exists.intro winding rfl

/-- The effective mapping torus of a compact fiber is compact. -/
@[implicit_reducible]
def mappingTorusCompactSpace
    (data : MappingTorusData X) [T2Space X] [LocallyCompactSpace X]
    [CompactSpace X] : CompactSpace (MappingTorus data) :=
  (fundamentalStripProjection_surjective data).compactSpace
    (fundamentalStripProjection_continuous data)

instance unitThreeSphereCompactSpace : CompactSpace UnitThreeSphere :=
  unitThreeSphereHomeomorph.symm.compactSpace

instance equatorialTwoSphereCompactSpace : CompactSpace EquatorialTwoSphere :=
  equatorialTwoSphereHomeomorph.symm.compactSpace

variable (period : Real) (hPeriod : Not (period = 0))

/-- Compactness of the actual four-dimensional effective D8 quotient. -/
@[implicit_reducible]
def reflectedSphereQuotientCompactSpace :
    CompactSpace (MappingTorus (reflectedSphereData period hPeriod)) :=
  mappingTorusCompactSpace (reflectedSphereData period hPeriod)

/-- Compactness of the actual three-dimensional fixed-throat quotient. -/
@[implicit_reducible]
def fixedThroatQuotientCompactSpace :
    CompactSpace (MappingTorus (fixedEquatorData period hPeriod)) :=
  mappingTorusCompactSpace (fixedEquatorData period hPeriod)

end

end P0EFTJanusMappingTorusCompactQuotient
end JanusFormal
