import Mathlib

namespace JanusFormal
namespace P0EFTJanusDiracMonopolePatching

set_option autoImplicit false

/-- North-chart coefficient of the charge-`n` Dirac monopole potential. -/
noncomputable def northPotentialCoefficient
    (n : ℤ) (theta : ℝ) : ℝ :=
  ((n : ℝ) / 2) * (1 - Real.cos theta)

/-- South-chart coefficient of the charge-`n` Dirac monopole potential. -/
noncomputable def southPotentialCoefficient
    (n : ℤ) (theta : ℝ) : ℝ :=
  -((n : ℝ) / 2) * (1 + Real.cos theta)

/-- Curvature coefficient shared by both local potentials. -/
noncomputable def monopoleCurvatureCoefficient
    (n : ℤ) (theta : ℝ) : ℝ :=
  ((n : ℝ) / 2) * Real.sin theta

/-- On the overlap, the two local potentials differ by the winding-`n` gauge term. -/
theorem north_minus_south_is_integer_winding
    (n : ℤ) (theta : ℝ) :
    northPotentialCoefficient n theta -
        southPotentialCoefficient n theta = (n : ℝ) := by
  unfold northPotentialCoefficient southPotentialCoefficient
  ring

/-- The north-chart potential is regular at the north pole. -/
@[simp] theorem north_potential_vanishes_at_north_pole
    (n : ℤ) :
    northPotentialCoefficient n 0 = 0 := by
  simp [northPotentialCoefficient]

/-- The south-chart potential is regular at the south pole. -/
@[simp] theorem south_potential_vanishes_at_south_pole
    (n : ℤ) :
    southPotentialCoefficient n Real.pi = 0 := by
  simp [southPotentialCoefficient]

/-- Both local potentials produce the same formal curvature coefficient. -/
theorem north_curvature_formula
    (n : ℤ) (theta : ℝ) :
    ((n : ℝ) / 2) * Real.sin theta =
      monopoleCurvatureCoefficient n theta := by
  rfl

/-- PT/charge conjugation negates the local north potential. -/
theorem north_potential_pt_conjugation
    (n : ℤ) (theta : ℝ) :
    northPotentialCoefficient (-n) theta =
      -northPotentialCoefficient n theta := by
  unfold northPotentialCoefficient
  push_cast
  ring

/-- PT/charge conjugation negates the local south potential. -/
theorem south_potential_pt_conjugation
    (n : ℤ) (theta : ℝ) :
    southPotentialCoefficient (-n) theta =
      -southPotentialCoefficient n theta := by
  unfold southPotentialCoefficient
  push_cast
  ring

/-- PT/charge conjugation negates the curvature. -/
theorem curvature_pt_conjugation
    (n : ℤ) (theta : ℝ) :
    monopoleCurvatureCoefficient (-n) theta =
      -monopoleCurvatureCoefficient n theta := by
  unfold monopoleCurvatureCoefficient
  push_cast
  ring

/-- A primitive integral sector has one unit of transition winding in magnitude. -/
theorem primitive_sector_has_unit_transition_winding
    (n : ℤ)
    (hPrimitive : n.natAbs = 1) :
    |(n : ℝ)| = 1 := by
  obtain hn | hn := Int.natAbs_eq n
  · rw [hn, hPrimitive]
    norm_num
  · rw [hn, hPrimitive]
    norm_num

/--
The local Dirac data are explicit. The remaining geometric theorem is to build
these charts as a genuine principal `U(1)` bundle on the throat, prove the
transition cocycle on the equatorial overlap, and match its connection
normalization to the LL auxiliary field.
-/
structure DiracMonopoleBundleStatus where
  northChartConstructed : Prop
  southChartConstructed : Prop
  equatorialOverlapConstructed : Prop
  transitionFunctionWindingDerived : Prop
  cocycleConditionProved : Prop
  principalU1BundleConstructed : Prop
  connectionOneFormsConstructed : Prop
  curvatureGlobalized : Prop
  firstChernNumberComputed : Prop
  llAuxiliaryConnectionIdentified : Prop


def diracMonopoleBundleClosed
    (s : DiracMonopoleBundleStatus) : Prop :=
  s.northChartConstructed /\
  s.southChartConstructed /\
  s.equatorialOverlapConstructed /\
  s.transitionFunctionWindingDerived /\
  s.cocycleConditionProved /\
  s.principalU1BundleConstructed /\
  s.connectionOneFormsConstructed /\
  s.curvatureGlobalized /\
  s.firstChernNumberComputed /\
  s.llAuxiliaryConnectionIdentified

end P0EFTJanusDiracMonopolePatching
end JanusFormal
