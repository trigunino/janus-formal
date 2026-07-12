import Mathlib
import JanusFormal.Branches.FundamentalGeometryD.Gates.P0EFTJanusTwistedMappingGenerator

namespace JanusFormal
namespace P0EFTJanusSmoothMappingTorusOrbifoldAudit

set_option autoImplicit false

open P0EFTJanusTwistedMappingGenerator

variable {X : Type*}

/-- Reflection without translation. -/
def reflectionOnly
    (rho : X → X) (p : X × ℝ) : X × ℝ :=
  (rho p.1, p.2)

/-- Reflection-only isotropy is exactly fiber fixed-point data. -/
theorem reflection_only_fixed_iff
    (rho : X → X) (p : X × ℝ) :
    reflectionOnly rho p = p ↔ rho p.1 = p.1 := by
  constructor
  · intro hFixed
    exact congrArg Prod.fst hFixed
  · intro hFiber
    rcases p with ⟨x, u⟩
    simp [reflectionOnly, hFiber]

/-- The mapping-torus generator has no fixed point on the covering space when `T ≠ 0`. -/
theorem twisted_step_has_no_cover_fixed_point
    (rho : X → X)
    (period : ℝ)
    (hPeriod : period ≠ 0)
    (p : X × ℝ) :
    twistedStep rho period p ≠ p := by
  intro hFixed
  have hSecond := congrArg Prod.snd hFixed
  change p.2 + period = p.2 at hSecond
  apply hPeriod
  linarith

/-- Even a fiber point fixed by `rho` is translated rather than fixed upstairs. -/
theorem fixed_fiber_point_is_not_mapping_action_isotropy
    (rho : X → X)
    (period : ℝ)
    (hPeriod : period ≠ 0)
    (x : X)
    (u : ℝ)
    (hFiber : FixedBy rho x) :
    twistedStep rho period (x, u) = (x, u + period) /\
      twistedStep rho period (x, u) ≠ (x, u) := by
  constructor
  · exact twisted_step_on_fixed_point rho period x u hFiber
  · exact twisted_step_has_no_cover_fixed_point
      rho period hPeriod (x, u)

/-- Abstract integer translate used to audit all nonzero powers of a mapping-torus action. -/
def cyclicMappingTranslate
    (fiberIterate : ℤ → X → X)
    (period : ℝ)
    (winding : ℤ)
    (p : X × ℝ) : X × ℝ :=
  (fiberIterate winding p.1,
    p.2 + (winding : ℝ) * period)

/-- Nonzero integer winding cannot fix a covering-space point when `T ≠ 0`. -/
theorem nonzero_cyclic_translate_has_no_fixed_point
    (fiberIterate : ℤ → X → X)
    (period : ℝ)
    (hPeriod : period ≠ 0)
    (winding : ℤ)
    (hWinding : winding ≠ 0)
    (p : X × ℝ) :
    cyclicMappingTranslate fiberIterate period winding p ≠ p := by
  intro hFixed
  have hSecond := congrArg Prod.snd hFixed
  change p.2 + (winding : ℝ) * period = p.2 at hSecond
  have hProduct : (winding : ℝ) * period = 0 := by
    linarith
  rcases mul_eq_zero.mp hProduct with hCast | hPeriodZero
  · have : winding = 0 := by exact_mod_cast hCast
    exact hWinding this
  · exact hPeriod hPeriodZero

/--
The current twisted-Hopf candidate is therefore a smooth mapping-torus quotient
candidate, not a reflection orbifold with local isotropy.  The equatorial
`S2 x S1` is an embedded mapping-torus submanifold, not a singular fixed stratum
of the free cyclic action.
-/
structure SmoothVersusOrbifoldStatus where
  nonzeroPeriodDerived : Prop
  fullIntegerActionConstructed : Prop
  fullActionProvedFree : Prop
  quotientSmoothManifoldConstructed : Prop
  equatorialMappingTorusEmbedded : Prop
  localOrbifoldIsotropyAbsent : Prop
  physicalUseOfWordOrbifoldClarified : Prop
  singularAlternativeIfRequiredSpecified : Prop


def smoothMappingTorusAuditClosed
    (s : SmoothVersusOrbifoldStatus) : Prop :=
  s.nonzeroPeriodDerived /\
  s.fullIntegerActionConstructed /\
  s.fullActionProvedFree /\
  s.quotientSmoothManifoldConstructed /\
  s.equatorialMappingTorusEmbedded /\
  s.localOrbifoldIsotropyAbsent /\
  s.physicalUseOfWordOrbifoldClarified /\
  s.singularAlternativeIfRequiredSpecified

end P0EFTJanusSmoothMappingTorusOrbifoldAudit
end JanusFormal
