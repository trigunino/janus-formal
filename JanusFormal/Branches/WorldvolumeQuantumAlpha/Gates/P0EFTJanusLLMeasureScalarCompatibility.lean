import Mathlib
import JanusFormal.Branches.WorldvolumeQuantumAlpha.Gates.P0EFTJanusWorldvolumeSignatureAndEOM
import JanusFormal.Branches.RP4TwistedFourFormAlpha.Gates.P0EFTJanusLLBraneAuxiliaryFluxClosure

namespace JanusFormal.P0EFTJanusLLMeasureScalarCompatibility

set_option autoImplicit false

open P0EFTJanusWorldvolumeSignatureAndEOM
open P0EFTJanusLLBraneAuxiliaryFluxClosure

/-- Conditional compatibility of the published minimal LL measure constraint
with the new homogeneous scale-invariant scalar equation. -/
structure LLScalarConstraintSector where
  ll : MinimalWrongSignMaxwellSector
  lambdaSix : ℝ
  phi : ℝ
  lambdaSixPositive : 0 < lambdaSix
  phiNonzero : phi ≠ 0
  scalarEquation :
    homogeneousScalarEuler lambdaSix ll.fieldInvariant phi = 0

/-- The LL equations remove the continuous auxiliary invariant and reduce the
scalar saddle to `4*lambda6*phi^8=1`. -/
theorem ll_constraint_reduces_scalar_saddle
    (s : LLScalarConstraintSector) :
    4 * s.lambdaSix * s.phi ^ 8 = 1 := by
  have hScalar :=
    (homogeneous_scalar_equation_iff s.lambdaSix s.ll.fieldInvariant
      s.phi s.phiNonzero).mp s.scalarEquation
  have hField := field_invariant_eq_one_half s.ll
  nlinarith

/-- The same constrained saddle has a strictly positive condensate magnitude. -/
theorem constrained_scalar_power_positive (s : LLScalarConstraintSector) :
    0 < s.phi ^ 8 := by
  have hLaw := ll_constraint_reduces_scalar_saddle s
  nlinarith [s.lambdaSixPositive]

structure LLConstraintClosureStatus where
  nonRiemannianMeasureVariationDerived : Prop
  auxiliaryMetricVariationDerived : Prop
  scalarVariationDerived : Prop
  gaugeVariationDerived : Prop
  firstClassConstraintAlgebraClosed : Prop
  reducedHamiltonianNonnegative : Prop
  noNegativeNormModeProved : Prop

def llConstraintClosure (s : LLConstraintClosureStatus) : Prop :=
  s.nonRiemannianMeasureVariationDerived ∧
  s.auxiliaryMetricVariationDerived ∧
  s.scalarVariationDerived ∧
  s.gaugeVariationDerived ∧
  s.firstClassConstraintAlgebraClosed ∧
  s.reducedHamiltonianNonnegative ∧
  s.noNegativeNormModeProved

end JanusFormal.P0EFTJanusLLMeasureScalarCompatibility
