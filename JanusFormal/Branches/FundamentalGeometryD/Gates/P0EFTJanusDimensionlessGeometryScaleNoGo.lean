import Mathlib

namespace JanusFormal
namespace P0EFTJanusDimensionlessGeometryScaleNoGo

set_option autoImplicit false

/-- A geometric predicate selects exactly one positive overall length. -/
def SelectsUniquePositiveLength (P : ℝ → Prop) : Prop :=
  ∃! length : ℝ, 0 < length /\ P length

/--
Any nonempty positive solution family closed under a fixed nontrivial positive
rescaling cannot determine a unique absolute length.
-/
theorem rescaling_orbit_blocks_unique_length
    (P : ℝ → Prop)
    (scale : ℝ)
    (hScalePositive : 0 < scale)
    (hScaleNontrivial : scale ≠ 1)
    (hCovariant : ∀ length, P length → P (scale * length)) :
    Not (SelectsUniquePositiveLength P) := by
  intro hUnique
  rcases hUnique with ⟨length, hLength, hOnly⟩
  have hRescaled : 0 < scale * length /\ P (scale * length) :=
    ⟨mul_pos hScalePositive hLength.1,
      hCovariant length hLength.2⟩
  have hEqual : scale * length = length :=
    hOnly (scale * length) hRescaled
  have hFactor : (scale - 1) * length = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hFactor with hScale | hLengthZero
  · apply hScaleNontrivial
    linarith
  · exact (ne_of_gt hLength.1) hLengthZero

/-- Doubling covariance is the most direct specialization. -/
theorem doubling_covariance_blocks_unique_length
    (P : ℝ → Prop)
    (hDoubling : ∀ length, P length → P (2 * length)) :
    Not (SelectsUniquePositiveLength P) := by
  exact rescaling_orbit_blocks_unique_length
    P 2 (by norm_num) (by norm_num) hDoubling

/--
Topological classes, covering degree, Pin sign, Z4 residue and dimensionless
spectral ratios may select sectors and ratios but not the overall metric scale
unless a dimensionful law breaks this orbit.
-/
structure GeometryScaleBreakingStatus where
  topologyAndMonodromyFixed : Prop
  dimensionlessMetricModuliFixed : Prop
  pinAndZ4SectorFixed : Prop
  chargeIntegerFixed : Prop
  dimensionfulQuantumScaleDerived : Prop
  gravitationalBoundaryScaleDerived : Prop
  conformalScaleOrbitBroken : Prop
  absoluteLengthUnique : Prop


def absoluteGeometryScaleClosed
    (s : GeometryScaleBreakingStatus) : Prop :=
  s.topologyAndMonodromyFixed /\
  s.dimensionlessMetricModuliFixed /\
  s.pinAndZ4SectorFixed /\
  s.chargeIntegerFixed /\
  s.dimensionfulQuantumScaleDerived /\
  s.gravitationalBoundaryScaleDerived /\
  s.conformalScaleOrbitBroken /\
  s.absoluteLengthUnique

end P0EFTJanusDimensionlessGeometryScaleNoGo
end JanusFormal
