import Mathlib
import JanusFormal.Branches.FundamentalGeometryD.Gates.P0EFTJanusTwistedMappingGenerator
import JanusFormal.Branches.FundamentalGeometryD.Gates.P0EFTJanusSmoothMappingTorusOrbifoldAudit

namespace JanusFormal
namespace P0EFTJanusFreeTunnelSingularOrbifoldDichotomy

set_option autoImplicit false

open P0EFTJanusTwistedMappingGenerator
open P0EFTJanusSmoothMappingTorusOrbifoldAudit

variable {X : Type*}

/-- A fixed point of the twisted generator forces the translation period to vanish. -/
theorem twisted_generator_fixed_point_forces_zero_period
    (rho : X → X)
    (period : ℝ)
    (p : X × ℝ)
    (hFixed : twistedStep rho period p = p) :
    period = 0 := by
  have hSecond := congrArg Prod.snd hFixed
  change p.2 + period = p.2 at hSecond
  linarith

/-- At zero period the twisted generator reduces to reflection only. -/
theorem zero_period_twisted_step_is_reflection
    (rho : X → X)
    (p : X × ℝ) :
    twistedStep rho 0 p = reflectionOnly rho p := by
  rcases p with ⟨x, u⟩
  simp [twistedStep, reflectionOnly]

/-- Nonzero tunnel period and local fixed-point isotropy are incompatible. -/
theorem no_simultaneous_nonzero_tunnel_and_generator_fixed_point
    (rho : X → X)
    (period : ℝ)
    (hPeriod : period ≠ 0) :
    Not (∃ p : X × ℝ,
      twistedStep rho period p = p) := by
  rintro ⟨p, hFixed⟩
  exact hPeriod
    (twisted_generator_fixed_point_forces_zero_period
      rho period p hFixed)

/-- Reflection fixed data may exist only in the zero-translation model. -/
structure SingularReflectionDatum where
  point : X × ℝ
  fiberFixed : Prop

/-- A compact mapping-torus circle requires nonzero period. -/
structure TunnelCircleDatum where
  period : ℝ
  periodNonzero : period ≠ 0

/-- The simple one-generator model cannot simultaneously realize both structures as fixed-point data. -/
theorem simple_generator_model_dichotomy
    (rho : X → X)
    (tunnel : TunnelCircleDatum) :
    ∀ p : X × ℝ,
      twistedStep rho tunnel.period p ≠ p := by
  intro p
  exact twisted_step_has_no_cover_fixed_point
    rho tunnel.period tunnel.periodNonzero p

/--
The current generator presents a sharp choice:

* `T != 0`: a free cyclic action, a smooth tunnel/mapping torus and no local
  orbifold fixed stratum;
* `T = 0`: reflection isotropy can occur, but the compact translation circle
  and finite tunnel period disappear.

A theory requiring both a finite tunnel and a genuinely singular Big-Bang
orbifold zone needs a richer groupoid, boundary/mirror construction or a
singular limiting geometry; it is not supplied by the single generator above.
-/
structure FreeVersusSingularPhysicalStatus where
  finiteTunnelPeriodDerived : Prop
  freeCyclicActionProved : Prop
  smoothQuotientConstructed : Prop
  singularBigBangStratumRequired : Prop
  richerOrbifoldGroupoidConstructed : Prop
  singularLimitOrBoundarySpecified : Prop
  tunnelAndSingularSectorCompatibilityProved : Prop


def freeVersusSingularPhysicalClosed
    (s : FreeVersusSingularPhysicalStatus) : Prop :=
  s.finiteTunnelPeriodDerived /\
  s.freeCyclicActionProved /\
  s.smoothQuotientConstructed /\
  s.singularBigBangStratumRequired /\
  s.richerOrbifoldGroupoidConstructed /\
  s.singularLimitOrBoundarySpecified /\
  s.tunnelAndSingularSectorCompatibilityProved

end P0EFTJanusFreeTunnelSingularOrbifoldDichotomy
end JanusFormal
