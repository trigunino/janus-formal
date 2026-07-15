import JanusFormal.Branches.JanusCompactObjects.Gates.P0EFTJanusCOGRBaseline

namespace JanusFormal
namespace P0EFTJanusCOFutureBimetricInterface

set_option autoImplicit false

/-- Data contract for a future two-sector static solver. It contains actual
radial fields rather than readiness booleans. -/
structure StaticSectorFields where
  lapse : ℝ → ℝ
  radialMetric : ℝ → ℝ
  density : ℝ → ℝ
  pressureRadial : ℝ → ℝ
  pressureTangential : ℝ → ℝ

structure BimetricStaticCandidate where
  plus : StaticSectorFields
  minus : StaticSectorFields
  conversionCurrent : ℝ → ℝ
  interfaceRadius : ℝ

structure BimetricStaticLaws (candidate : BimetricStaticCandidate) where
  plusEulerEinsteinEquation : Prop
  minusEulerEinsteinEquation : Prop
  totalBianchiConservation : Prop
  conversionBalanceLaw : Prop
  centerRegularity : Prop
  interfaceJunction : Prop
  asymptoticBoundaryCondition : Prop
  causalEquationOfState : Prop

def co02Ready (candidate : BimetricStaticCandidate)
    (laws : BimetricStaticLaws candidate) : Prop :=
  laws.plusEulerEinsteinEquation ∧
  laws.minusEulerEinsteinEquation ∧
  laws.totalBianchiConservation ∧
  laws.conversionBalanceLaw ∧
  laws.centerRegularity ∧
  laws.interfaceJunction ∧
  laws.asymptoticBoundaryCondition ∧
  laws.causalEquationOfState

end P0EFTJanusCOFutureBimetricInterface
end JanusFormal
