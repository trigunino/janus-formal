import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeDeterminantPhase4D

/-!
# Independence of the finite-part subtraction scheme

Two short-time counterterm schemes define the same determinant when their
renormalized short-time finite parts agree.  The long-time integral is already
identical because both schemes regularize the same intrinsic heat trace.

This file packages that equivalence and proves equality of logarithms and
determinants.  Establishing the finite-part agreement from a concrete heat
asymptotic expansion remains the local analytic calculation.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRelativeHeatFinitePartSchemeIndependence4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D
open P0EFTJanusProgramPRelativeDeterminantPhase4D

/-- Equality of the renormalized short-time contributions of two subtraction
schemes. -/
structure RelativeHeatFinitePartSchemeAgreement
    {heatTrace : P0EFTJanusCircleDiracHeatTraceCancellation.HeatTime → Real}
    (first second : RelativeHeatFinitePartData heatTrace) : Prop where
  shortTimeFinitePart_eq :
    first.countertermFinitePart + relativeHeatShortTimeFinitePart first =
      second.countertermFinitePart + relativeHeatShortTimeFinitePart second

/-- Scheme agreement is reflexive. -/
def RelativeHeatFinitePartSchemeAgreement.refl
    {heatTrace : P0EFTJanusCircleDiracHeatTraceCancellation.HeatTime → Real}
    (data : RelativeHeatFinitePartData heatTrace) :
    RelativeHeatFinitePartSchemeAgreement data data where
  shortTimeFinitePart_eq := rfl

/-- Scheme agreement is symmetric. -/
def RelativeHeatFinitePartSchemeAgreement.symm
    {heatTrace : P0EFTJanusCircleDiracHeatTraceCancellation.HeatTime → Real}
    {first second : RelativeHeatFinitePartData heatTrace}
    (agreement : RelativeHeatFinitePartSchemeAgreement first second) :
    RelativeHeatFinitePartSchemeAgreement second first where
  shortTimeFinitePart_eq := agreement.shortTimeFinitePart_eq.symm

/-- Scheme agreement is transitive. -/
def RelativeHeatFinitePartSchemeAgreement.trans
    {heatTrace : P0EFTJanusCircleDiracHeatTraceCancellation.HeatTime → Real}
    {first second third : RelativeHeatFinitePartData heatTrace}
    (firstSecond : RelativeHeatFinitePartSchemeAgreement first second)
    (secondThird : RelativeHeatFinitePartSchemeAgreement second third) :
    RelativeHeatFinitePartSchemeAgreement first third where
  shortTimeFinitePart_eq :=
    firstSecond.shortTimeFinitePart_eq.trans
      secondThird.shortTimeFinitePart_eq

/-- Equivalent subtraction schemes give the same renormalized logarithm. -/
theorem RelativeHeatFinitePartSchemeAgreement.logDeterminant_eq
    {heatTrace : P0EFTJanusCircleDiracHeatTraceCancellation.HeatTime → Real}
    {first second : RelativeHeatFinitePartData heatTrace}
    (agreement : RelativeHeatFinitePartSchemeAgreement first second) :
    relativeHeatFinitePartLogDeterminant first =
      relativeHeatFinitePartLogDeterminant second := by
  unfold relativeHeatFinitePartLogDeterminant
  rw [show first.countertermFinitePart +
        relativeHeatShortTimeFinitePart first +
          relativeHeatLongTimeIntegral first =
      second.countertermFinitePart +
        relativeHeatShortTimeFinitePart second +
          relativeHeatLongTimeIntegral second by
    rw [agreement.shortTimeFinitePart_eq]]

/-- Hence the positive determinants are equal. -/
theorem RelativeHeatFinitePartSchemeAgreement.determinant_eq
    {heatTrace : P0EFTJanusCircleDiracHeatTraceCancellation.HeatTime → Real}
    {first second : RelativeHeatFinitePartData heatTrace}
    (agreement : RelativeHeatFinitePartSchemeAgreement first second) :
    relativeHeatFinitePartDeterminant first =
      relativeHeatFinitePartDeterminant second := by
  unfold relativeHeatFinitePartDeterminant
  rw [agreement.logDeterminant_eq]

/-- The corresponding complex determinants also agree when the phase is kept
fixed. -/
theorem RelativeHeatFinitePartSchemeAgreement.complexDeterminant_eq
    {heatTrace : P0EFTJanusCircleDiracHeatTraceCancellation.HeatTime → Real}
    {first second : RelativeHeatFinitePartData heatTrace}
    (agreement : RelativeHeatFinitePartSchemeAgreement first second)
    (phase : RelativeDeterminantPhaseData) :
    relativeHeatComplexDeterminant first phase =
      relativeHeatComplexDeterminant second phase := by
  unfold relativeHeatComplexDeterminant
  rw [agreement.determinant_eq]

/-- Public subtraction-scheme checkpoint. -/
theorem relative_heat_finite_part_scheme_independence_gate
    {heatTrace : P0EFTJanusCircleDiracHeatTraceCancellation.HeatTime → Real}
    {first second : RelativeHeatFinitePartData heatTrace}
    (agreement : RelativeHeatFinitePartSchemeAgreement first second) :
    relativeHeatFinitePartLogDeterminant first =
        relativeHeatFinitePartLogDeterminant second ∧
      relativeHeatFinitePartDeterminant first =
        relativeHeatFinitePartDeterminant second :=
  ⟨agreement.logDeterminant_eq, agreement.determinant_eq⟩

end
end P0EFTJanusProgramPRelativeHeatFinitePartSchemeIndependence4D
end JanusFormal
