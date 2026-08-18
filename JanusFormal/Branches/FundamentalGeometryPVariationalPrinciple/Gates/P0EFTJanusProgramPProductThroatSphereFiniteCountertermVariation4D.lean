import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteHeatCountertermFinitePartVariation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatSphereCountertermFinitePartLimit4D

/-!
# Finite counterterm variation for the reduced product-throat sphere

The three fixed profiles `t⁻¹`, `1`, and `t` reproduce the reduced sphere
counterterm.  Their logarithmically weighted finite parts are `-1`, `0`, and
`1` respectively.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPProductThroatSphereFiniteCountertermVariation4D

set_option autoImplicit false
noncomputable section

open Filter
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusMonopoleHeatAsymptoticMatch
open P0EFTJanusProgramPFiniteHeatCountertermVariation4D
open P0EFTJanusProgramPFiniteHeatCountertermFinitePartVariation4D
open P0EFTJanusProgramPProductThroatSphereShortTimeFinitePart4D
open P0EFTJanusProgramPProductThroatSphereCountertermFinitePartLimit4D

/-- The three local time profiles in the reduced sphere counterterm. -/
inductive ReducedSphereCountertermProfile
  | inverse
  | constant
  | linear
  deriving DecidableEq, Fintype

open ReducedSphereCountertermProfile

def reducedSphereCountertermBasis :
    ReducedSphereCountertermProfile → Real → Real
  | inverse, time => 1 / time
  | constant, _ => 1
  | linear, time => time

def reducedSphereCountertermCoefficient
    (data : ProductThroatSpectralData) :
    ReducedSphereCountertermProfile → Real
  | inverse => 2
  | constant => -(1 / 3 : Real) - (monopoleAbsCharge data : Real)
  | linear => (5 * (monopoleAbsCharge data : Real) ^ 2 - 1) / 30

/-- The reduced sphere counterterm as a finite, parameter-constant family. -/
def reducedSphereCountertermVariation
    (data : ProductThroatSpectralData) :
    FiniteHeatCountertermVariationData ReducedSphereCountertermProfile where
  support := {inverse, constant, linear}
  basis := reducedSphereCountertermBasis
  coefficient := fun _ index ↦ reducedSphereCountertermCoefficient data index
  coefficientDerivative := fun _ _ ↦ 0
  coefficient_hasDerivAt := by
    intro parameter index _
    exact hasDerivAt_const parameter
      (reducedSphereCountertermCoefficient data index)

def reducedSphereCountertermBasisFinitePart :
    ReducedSphereCountertermProfile → Real
  | inverse => -1
  | constant => 0
  | linear => 1

/-- Finite-part packet for the three reduced sphere counterterm profiles. -/
def reducedSphereFiniteCountertermVariation
    (data : ProductThroatSpectralData) :
    FiniteHeatCountertermFinitePartVariationData
      ReducedSphereCountertermProfile where
  variation := reducedSphereCountertermVariation data
  basisFinitePart := reducedSphereCountertermBasisFinitePart

theorem reducedSphereCountertermVariation_counterterm_eq
    (data : ProductThroatSpectralData) (parameter time : Real) :
    counterterm (reducedSphereCountertermVariation data) parameter time =
      reducedSphereCounterterm data time := by
  unfold counterterm reducedSphereCountertermVariation
    reducedSphereCountertermCoefficient reducedSphereCountertermBasis
    reducedSphereCounterterm predictedSphereHeatExpansion
  simp
  ring

theorem reducedSphereFiniteCountertermVariation_finitePartContribution_eq
    (data : ProductThroatSpectralData) (parameter : Real) :
    finitePartContribution (reducedSphereFiniteCountertermVariation data)
        parameter =
      reducedSphereCountertermFinitePart data := by
  unfold finitePartContribution reducedSphereFiniteCountertermVariation
    reducedSphereCountertermVariation reducedSphereCountertermCoefficient
    reducedSphereCountertermBasisFinitePart reducedSphereCountertermFinitePart
  simp

theorem reducedSphereFiniteCountertermVariation_finitePartDerivative_eq_zero
    (data : ProductThroatSpectralData) (parameter : Real) :
    finitePartDerivative (reducedSphereFiniteCountertermVariation data)
      parameter = 0 := by
  unfold finitePartDerivative reducedSphereFiniteCountertermVariation
    reducedSphereCountertermVariation reducedSphereCountertermBasisFinitePart
  simp

/-- The cutoff-renormalized integral tends to the coefficientwise finite-part
contribution of the three-profile packet. -/
theorem reducedSphereCountertermRenormalizedCutoff_tendsto_finitePartContribution
    (data : ProductThroatSpectralData) (parameter : Real) :
    Tendsto (reducedSphereCountertermRenormalizedCutoff data)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (finitePartContribution
        (reducedSphereFiniteCountertermVariation data) parameter)) := by
  rw [reducedSphereFiniteCountertermVariation_finitePartContribution_eq]
  exact reducedSphereCountertermRenormalizedCutoff_tendsto data

/-- Public gate for the concrete finite counterterm representation. -/
theorem product_throat_sphere_finite_counterterm_variation_gate
    (data : ProductThroatSpectralData) (parameter time : Real) :
    counterterm (reducedSphereCountertermVariation data) parameter time =
        reducedSphereCounterterm data time ∧
      finitePartContribution (reducedSphereFiniteCountertermVariation data)
          parameter = reducedSphereCountertermFinitePart data ∧
      finitePartDerivative (reducedSphereFiniteCountertermVariation data)
          parameter = 0 :=
  ⟨reducedSphereCountertermVariation_counterterm_eq data parameter time,
    reducedSphereFiniteCountertermVariation_finitePartContribution_eq data parameter,
    reducedSphereFiniteCountertermVariation_finitePartDerivative_eq_zero data parameter⟩

end
end P0EFTJanusProgramPProductThroatSphereFiniteCountertermVariation4D
end JanusFormal
