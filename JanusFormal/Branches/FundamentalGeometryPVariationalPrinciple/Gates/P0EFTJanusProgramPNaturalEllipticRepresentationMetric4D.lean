import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNaturalEllipticOperatorRepresentation4D

/-!
# Concrete metrics on represented D11 section families

Once a D11 natural elliptic family is represented on a fixed real Hilbert
space, the Hilbert inner product pulls back to actual pairings on every source
and target section type.  These are data-bearing metric objects, not status
flags.

The represented state-space metric is constant in the real family parameter,
so its scalar coefficients are smooth without any extra hypothesis.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPNaturalEllipticRepresentationMetric4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPNaturalEllipticOperatorRepresentation4D
open P0EFTJanusNaturalEllipticFamilyExistence
open scoped InnerProductSpace

variable {State : Type*}
  [NormedAddCommGroup State] [NormedSpace Real State]
  [InnerProductSpace Real State]

/-- Data-bearing real pairings on the D11 source and target section types,
obtained by transporting the fixed represented Hilbert metric. -/
structure NaturalEllipticRepresentationMetricData
    {immersionCategory : P0EFTJanusSpinCImmersionCategory.SpinCImmersionCategory}
    {family : NaturalEllipticOperatorFamily immersionCategory}
    {representedOperator : Real → State → State}
    (representation : NaturalEllipticOperatorRepresentationData
      immersionCategory family representedOperator) where
  sourcePairing : ∀ parameter,
    family.sourceFunctor.Section (representation.objectAt parameter) →
      family.sourceFunctor.Section (representation.objectAt parameter) → Real
  targetPairing : ∀ parameter,
    family.targetFunctor.Section (representation.objectAt parameter) →
      family.targetFunctor.Section (representation.objectAt parameter) → Real
  sourcePairing_eq : ∀ parameter first second,
    sourcePairing parameter first second =
      real_inner
        (representation.sourceEquiv parameter first)
        (representation.sourceEquiv parameter second)
  targetPairing_eq : ∀ parameter first second,
    targetPairing parameter first second =
      real_inner
        (representation.targetEquiv parameter first)
        (representation.targetEquiv parameter second)

namespace NaturalEllipticOperatorRepresentationData

/-- Canonical represented metric packet. -/
def canonicalMetricData
    {immersionCategory : P0EFTJanusSpinCImmersionCategory.SpinCImmersionCategory}
    {family : NaturalEllipticOperatorFamily immersionCategory}
    {representedOperator : Real → State → State}
    (representation : NaturalEllipticOperatorRepresentationData
      immersionCategory family representedOperator) :
    NaturalEllipticRepresentationMetricData representation where
  sourcePairing := fun parameter first second =>
    real_inner
      (representation.sourceEquiv parameter first)
      (representation.sourceEquiv parameter second)
  targetPairing := fun parameter first second =>
    real_inner
      (representation.targetEquiv parameter first)
      (representation.targetEquiv parameter second)
  sourcePairing_eq := by intros; rfl
  targetPairing_eq := by intros; rfl

/-- The represented source pairing is symmetric. -/
theorem canonicalSourcePairing_symmetric
    {immersionCategory : P0EFTJanusSpinCImmersionCategory.SpinCImmersionCategory}
    {family : NaturalEllipticOperatorFamily immersionCategory}
    {representedOperator : Real → State → State}
    (representation : NaturalEllipticOperatorRepresentationData
      immersionCategory family representedOperator)
    (parameter : Real)
    (first second : family.sourceFunctor.Section
      (representation.objectAt parameter)) :
    representation.canonicalMetricData.sourcePairing parameter first second =
      representation.canonicalMetricData.sourcePairing parameter second first := by
  simp [canonicalMetricData, real_inner_comm]

/-- The represented target pairing is symmetric. -/
theorem canonicalTargetPairing_symmetric
    {immersionCategory : P0EFTJanusSpinCImmersionCategory.SpinCImmersionCategory}
    {family : NaturalEllipticOperatorFamily immersionCategory}
    {representedOperator : Real → State → State}
    (representation : NaturalEllipticOperatorRepresentationData
      immersionCategory family representedOperator)
    (parameter : Real)
    (first second : family.targetFunctor.Section
      (representation.objectAt parameter)) :
    representation.canonicalMetricData.targetPairing parameter first second =
      representation.canonicalMetricData.targetPairing parameter second first := by
  simp [canonicalMetricData, real_inner_comm]

/-- The common represented Hilbert pairing, viewed as a parameter family. -/
def representedStatePairing (_parameter : Real) (first second : State) : Real :=
  real_inner first second

/-- The represented metric coefficients are smooth in the family parameter. -/
theorem representedStatePairing_contDiff
    (first second : State) :
    ContDiff Real ∞ (fun parameter : Real =>
      representedStatePairing parameter first second) := by
  exact contDiff_const

/-- Public data-bearing represented-metric checkpoint. -/
theorem natural_elliptic_representation_metric_gate
    {immersionCategory : P0EFTJanusSpinCImmersionCategory.SpinCImmersionCategory}
    {family : NaturalEllipticOperatorFamily immersionCategory}
    {representedOperator : Real → State → State}
    (representation : NaturalEllipticOperatorRepresentationData
      immersionCategory family representedOperator) :
    Nonempty (NaturalEllipticRepresentationMetricData representation) ∧
    (∀ first second : State,
      ContDiff Real ∞ (fun parameter : Real =>
        representedStatePairing parameter first second)) :=
  ⟨⟨representation.canonicalMetricData⟩,
    representedStatePairing_contDiff⟩

end NaturalEllipticOperatorRepresentationData

end
end P0EFTJanusProgramPNaturalEllipticRepresentationMetric4D
end JanusFormal
