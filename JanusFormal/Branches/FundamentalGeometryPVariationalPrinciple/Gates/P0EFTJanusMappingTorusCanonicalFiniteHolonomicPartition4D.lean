import Mathlib.Geometry.Manifold.PartitionOfUnity
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalFiniteHolonomicAtlasCover4D

/-!
# Smooth partition subordinate to the finite holonomic atlas

The finite atlas cover admits a smooth partition of unity whose closed
supports lie inside the corresponding genuine holonomic chart images.  This
provides the analytic localization datum needed before assembling local PDE
and Stokes identities.  No coordinate change-of-variables or flux
cancellation is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalFiniteHolonomicPartition4D

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusCanonicalFiniteHolonomicAtlasCover4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient :=
  MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

/-- Finite index type of the selected holonomic patches. -/
abbrev CanonicalFiniteHolonomicPatch :=
  { patch : SmoothHolonomicFrameChart4 period hPeriod //
    patch ∈ (canonicalFiniteHolonomicAtlas period hPeriod).patches }

/-- Open quotient image associated with one selected patch. -/
def canonicalFiniteHolonomicOpenPatch
    (patch : CanonicalFiniteHolonomicPatch period hPeriod) :
    Set (EffectiveQuotient period hPeriod) :=
  Set.range patch.1.coordinateMap

theorem canonicalFiniteHolonomicOpenPatch_isOpen
    (patch : CanonicalFiniteHolonomicPatch period hPeriod) :
    IsOpen (canonicalFiniteHolonomicOpenPatch period hPeriod patch) :=
  patch.1.coordinateMap_isLocalDiffeomorph.isOpen_range

theorem canonicalFiniteHolonomicOpenPatch_covers :
    (Set.univ : Set (EffectiveQuotient period hPeriod)) ⊆
      ⋃ patch : CanonicalFiniteHolonomicPatch period hPeriod,
        canonicalFiniteHolonomicOpenPatch period hPeriod patch := by
  intro point _hPoint
  rcases canonicalFiniteHolonomicAtlas_covers period hPeriod point with
    ⟨patch, hPatch, coordinate, hCoordinate⟩
  exact Set.mem_iUnion.mpr
    ⟨⟨patch, hPatch⟩, ⟨coordinate, hCoordinate⟩⟩

/-- Existence of a globally smooth partition subordinate to the selected
finite holonomic atlas. -/
theorem exists_canonicalFiniteHolonomicPartition :
    ∃ partition : SmoothPartitionOfUnity
        (CanonicalFiniteHolonomicPatch period hPeriod)
        coverModelWithCorners (EffectiveQuotient period hPeriod) Set.univ,
      partition.IsSubordinate
        (canonicalFiniteHolonomicOpenPatch period hPeriod) := by
  exact SmoothPartitionOfUnity.exists_isSubordinate coverModelWithCorners
    isClosed_univ (canonicalFiniteHolonomicOpenPatch period hPeriod)
    (canonicalFiniteHolonomicOpenPatch_isOpen period hPeriod)
    (canonicalFiniteHolonomicOpenPatch_covers period hPeriod)

/-- A fixed field-independent smooth partition subordinate to the finite
holonomic atlas. -/
def canonicalFiniteHolonomicPartition :
    SmoothPartitionOfUnity
      (CanonicalFiniteHolonomicPatch period hPeriod)
      coverModelWithCorners (EffectiveQuotient period hPeriod) Set.univ :=
  Classical.choose
    (exists_canonicalFiniteHolonomicPartition period hPeriod)

theorem canonicalFiniteHolonomicPartition_subordinate :
    (canonicalFiniteHolonomicPartition period hPeriod).IsSubordinate
      (canonicalFiniteHolonomicOpenPatch period hPeriod) :=
  Classical.choose_spec
    (exists_canonicalFiniteHolonomicPartition period hPeriod)

/-- The selected weights sum to one at every physical point. -/
theorem canonicalFiniteHolonomicPartition_sum_eq_one
    (point : EffectiveQuotient period hPeriod) :
    ∑ᶠ patch : CanonicalFiniteHolonomicPatch period hPeriod,
        canonicalFiniteHolonomicPartition period hPeriod patch point = 1 :=
  (canonicalFiniteHolonomicPartition period hPeriod).sum_eq_one
    (Set.mem_univ point)

/-- Every closed weight support stays inside its selected chart image. -/
theorem canonicalFiniteHolonomicPartition_tsupport_subset
    (patch : CanonicalFiniteHolonomicPatch period hPeriod) :
    tsupport (canonicalFiniteHolonomicPartition period hPeriod patch) ⊆
      canonicalFiniteHolonomicOpenPatch period hPeriod patch :=
  canonicalFiniteHolonomicPartition_subordinate period hPeriod patch

/-- Gate marker: the finite global atlas now carries an honest smooth
subordinate localization with pointwise total weight one. -/
theorem mapping_torus_canonical_finite_holonomic_partition_gate :
    (∀ point : EffectiveQuotient period hPeriod,
        ∑ᶠ patch : CanonicalFiniteHolonomicPatch period hPeriod,
            canonicalFiniteHolonomicPartition period hPeriod patch point = 1) ∧
      (∀ patch : CanonicalFiniteHolonomicPatch period hPeriod,
        tsupport (canonicalFiniteHolonomicPartition period hPeriod patch) ⊆
          canonicalFiniteHolonomicOpenPatch period hPeriod patch) :=
  ⟨canonicalFiniteHolonomicPartition_sum_eq_one period hPeriod,
    canonicalFiniteHolonomicPartition_tsupport_subset period hPeriod⟩

end
end P0EFTJanusMappingTorusCanonicalFiniteHolonomicPartition4D
end JanusFormal
