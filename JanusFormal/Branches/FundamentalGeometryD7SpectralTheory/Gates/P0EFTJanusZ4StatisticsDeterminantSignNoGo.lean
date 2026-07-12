import Mathlib
import JanusFormal.Branches.FundamentalGeometryD7SpectralTheory.Gates.P0EFTJanusZ4StatisticsSelection
import JanusFormal.Branches.FundamentalGeometryD.Gates.P0EFTJanusPeriodicQuarterCompetition

namespace JanusFormal
namespace P0EFTJanusZ4StatisticsDeterminantSignNoGo

set_option autoImplicit false

open P0EFTJanusZ4StatisticsSelection
open P0EFTJanusPeriodicQuarterCompetition

/--
Cleared derivative numerator for the statistics-correct one-loop action made of

* a periodic bosonic determinant of positive multiplicity `p`;
* a quarter-holonomy fermionic determinant of positive multiplicity `q`.

The bosonic periodic contribution is proportional to `+2*r/(1-r)`.  The raw
quarter determinant has derivative `-2*r^2/(1+r^2)`, but the fermionic minus
sign reverses it.  After multiplication by the positive denominator
`(1-r)*(1+r^2)`, the total numerator is

`2*r*(p*(1+r^2) + q*r*(1-r))`.
-/
def standardStatisticsClearedDerivative
    (periodicBosonWeight quarterFermionWeight radial : ℝ) : ℝ :=
  2 * radial *
    (periodicBosonWeight * (1 + radial ^ 2) +
      quarterFermionWeight * radial * (1 - radial))

/-- Both statistics-correct contributions have the same positive slope on `0<r<1`. -/
theorem standard_statistics_derivative_positive
    (periodicBosonWeight quarterFermionWeight radial : ℝ)
    (hPeriodicWeight : 0 < periodicBosonWeight)
    (hQuarterWeight : 0 < quarterFermionWeight)
    (hRadial : 0 < radial)
    (hUpper : radial < 1) :
    0 < standardStatisticsClearedDerivative
      periodicBosonWeight quarterFermionWeight radial := by
  have hOneMinus : 0 < 1 - radial := sub_pos.mpr hUpper
  have hOnePlusSquare : 0 < 1 + radial ^ 2 := by
    nlinarith [sq_nonneg radial]
  have hPeriodicTerm :
      0 < periodicBosonWeight * (1 + radial ^ 2) :=
    mul_pos hPeriodicWeight hOnePlusSquare
  have hQuarterTerm :
      0 < quarterFermionWeight * radial * (1 - radial) :=
    mul_pos (mul_pos hQuarterWeight hRadial) hOneMinus
  unfold standardStatisticsClearedDerivative
  exact mul_pos
    (mul_pos (by norm_num) hRadial)
    (add_pos hPeriodicTerm hQuarterTerm)

/-- Therefore no physical radial variable can be stationary in this two-sector model. -/
theorem standard_statistics_have_no_finite_stationary_point
    (periodicBosonWeight quarterFermionWeight radial : ℝ)
    (hPeriodicWeight : 0 < periodicBosonWeight)
    (hQuarterWeight : 0 < quarterFermionWeight)
    (hRadial : 0 < radial)
    (hUpper : radial < 1) :
    standardStatisticsClearedDerivative
      periodicBosonWeight quarterFermionWeight radial ≠ 0 :=
  ne_of_gt (standard_statistics_derivative_positive
    periodicBosonWeight quarterFermionWeight radial
    hPeriodicWeight hQuarterWeight hRadial hUpper)

/-- At the old arithmetic root `r=1/3`, the correct signed derivative is positive. -/
@[simp] theorem one_five_standard_statistics_at_one_third :
    standardStatisticsClearedDerivative 1 5 (1 / 3) = 40 / 27 := by
  norm_num [standardStatisticsClearedDerivative]

/-- The same-sign polynomial vanishes at `1/3`, but the physical signed action does not. -/
theorem one_five_same_sign_root_is_not_standard_statistics_vacuum :
    stationarityPolynomial 1 5 (1 / 3) = 0 /\
      0 < standardStatisticsClearedDerivative 1 5 (1 / 3) := by
  constructor
  · exact third_is_one_to_five_stationary
  · rw [one_five_standard_statistics_at_one_third]
    norm_num

/-- PT doubling preserves the positive slope rather than creating a vacuum. -/
theorem pt_doubled_standard_statistics_derivative_positive
    (radial : ℝ)
    (hRadial : 0 < radial)
    (hUpper : radial < 1) :
    0 < 2 * standardStatisticsClearedDerivative 1 5 radial := by
  have hOneFold := standard_statistics_derivative_positive
    1 5 radial (by norm_num) (by norm_num) hRadial hUpper
  nlinarith

/--
A direct Pin-`Z4` interpretation fixes the statistics: periodic/half-turn phases
are bosonic, while quarter/three-quarter phases are fermionic.  With standard
one-loop determinant signs, that assignment rules out the previously proposed
`1:5` and PT-doubled `2:10` minima.
-/
theorem central_pin_z4_statistics_rule_out_direct_one_five_vacuum
    (radial : ℝ)
    (hRadial : 0 < radial)
    (hUpper : radial < 1) :
    PinZ4Compatible FieldStatistics.boson periodicPhase /\
    PinZ4Compatible FieldStatistics.fermion quarterPhase /\
    standardStatisticsClearedDerivative 1 5 radial ≠ 0 := by
  exact ⟨periodic_phase_is_bosonic,
    quarter_phase_is_fermionic,
    standard_statistics_have_no_finite_stationary_point
      1 5 radial (by norm_num) (by norm_num) hRadial hUpper⟩

/--
The arithmetic `1:5` ratio can survive only after changing at least one physical
ingredient: an internal `Z4` not equal to the central Pin lift, a nonstandard
commuting-spinor/ghost sign, an additional positive-cosine holonomy sector,
interactions, or a microscopically fixed local/boundary term.
-/
structure StatisticsSignExitStatus where
  internalZ4DistinctFromPinLiftDerived : Prop
  nonstandardQuarterDeterminantSignDerived : Prop
  additionalPositiveCosineSectorDerived : Prop
  interactingPotentialDerived : Prop
  microscopicLocalOrBoundaryTermDerived : Prop
  fullStatisticsAndGhostAuditCompleted : Prop
  atLeastOneExitDerived : Prop


def statisticsSignNoGoExited
    (s : StatisticsSignExitStatus) : Prop :=
  (s.internalZ4DistinctFromPinLiftDerived \/
    s.nonstandardQuarterDeterminantSignDerived \/
    s.additionalPositiveCosineSectorDerived \/
    s.interactingPotentialDerived \/
    s.microscopicLocalOrBoundaryTermDerived) /\
  s.fullStatisticsAndGhostAuditCompleted /\
  s.atLeastOneExitDerived

end P0EFTJanusZ4StatisticsDeterminantSignNoGo
end JanusFormal
