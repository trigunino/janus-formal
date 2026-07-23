import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetPDEClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCutoffClosedAnalyticClosure4D

/-!
# Full physical scalar analytic closure from the four PDE layers

The boundary triple is supplied by
`CanonicalPhysicalScalarCauchyJetPDEData`: Euler compatibility and divergence,
Gårding energy, higher normal regularity, and product-coordinate estimates for
the explicit Cauchy lift.

Adding smooth graph approximation of Hilbert adjoint pairs, coercivity of one
shifted form, and compact approximations of the physical `H¹ -> L²` inclusion
then yields actual self-adjointness and compact semibounded spectral theory.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarPDEAnalyticClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology Module End
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetPDEClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCutoffClosedAnalyticClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarRellichApproximation4D
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleAdjointGraphRegularity4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleShiftedForm4D

universe x y r

variable (period : Real) (hPeriod : period ≠ 0)
variable {massSquared : Real}
variable {Regularity : Type r}
  [NormedAddCommGroup Regularity] [NormedSpace Real Regularity]
  [CompleteSpace Regularity]

private abbrev BoundaryL2 := CanonicalPhysicalScalarFirstSheetL2 period

/-- Full analytic data after the physical boundary triple has been reduced to
the four concrete PDE layers. -/
structure CanonicalPhysicalScalarPDEAnalyticData
    (massSquared : Real)
    (ValueCore : Type x) (NormalCore : Type y)
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore] where
  boundary : CanonicalPhysicalScalarCauchyJetPDEData
    period hPeriod massSquared ValueCore NormalCore
    (Regularity := Regularity)
  condition : CanonicalScalarHilbertLagrangianBoundaryCondition
    (BoundaryL2 period)
  adjointApproximation : boundary.triple.AdjointPairSmoothApproximationData
    condition
  referenceParameter : Real
  shiftedFormCoercive : boundary.triple.LagrangianShiftedFormCoerciveData
    condition referenceParameter
  rellichApproximation : CanonicalPhysicalScalarRellichApproximationData
    period hPeriod

namespace CanonicalPhysicalScalarPDEAnalyticData

/-- Conversion to the existing cutoff-closed analytic engine. -/
def toCutoffClosedAnalyticData
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (analytic : CanonicalPhysicalScalarPDEAnalyticData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :
    CanonicalPhysicalScalarCutoffClosedAnalyticData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity) where
  boundary := analytic.boundary.boundaryData
  condition := analytic.condition
  adjointApproximation := analytic.adjointApproximation
  referenceParameter := analytic.referenceParameter
  shiftedFormCoercive := analytic.shiftedFormCoercive
  rellichApproximation := analytic.rellichApproximation

/-- Actual Hilbert self-adjointness of the selected physical realization. -/
theorem actualAdjointDomain_eq
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (analytic : CanonicalPhysicalScalarPDEAnalyticData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :
    analytic.boundary.triple.actualAdjointDomain analytic.condition =
      analytic.boundary.triple.realizationDomain analytic.condition :=
  (analytic.toCutoffClosedAnalyticData period hPeriod)
    |>.actualAdjointDomain_eq period hPeriod

/-- Compact physical reference resolvent. -/
noncomputable def compactResolvent
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (analytic : CanonicalPhysicalScalarPDEAnalyticData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :=
  (analytic.toCutoffClosedAnalyticData period hPeriod)
    |>.compactResolvent period hPeriod

/-- Direct physical Fredholm alternative. -/
theorem fredholmAlternative
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (analytic : CanonicalPhysicalScalarPDEAnalyticData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity))
    (spectralParameter : Real)
    (hParameter : spectralParameter ≠ analytic.referenceParameter) :
    analytic.boundary.triple.LagrangianHasEigenvalue
        analytic.condition spectralParameter ∨
      analytic.boundary.triple.LagrangianResolventPoint
        analytic.condition spectralParameter :=
  (analytic.toCutoffClosedAnalyticData period hPeriod)
    |>.fredholmAlternative period hPeriod spectralParameter hParameter

/-- Finite multiplicity of every nonreference physical eigenspace. -/
theorem finiteDimensional_operatorEigenspace
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (analytic : CanonicalPhysicalScalarPDEAnalyticData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity))
    (eigenvalue : Real)
    (hEigenvalue : eigenvalue ≠ analytic.referenceParameter) :
    FiniteDimensional Real
      (analytic.boundary.triple.lagrangianOperatorEigenspace
        analytic.condition eigenvalue) :=
  (analytic.toCutoffClosedAnalyticData period hPeriod)
    |>.toFullyReducedAnalyticData period hPeriod
    |>.toEllipticAnalyticData period hPeriod
    |>.toSequentialAnalyticData period hPeriod
    |>.toConstructiveAnalyticData period hPeriod
    |>.shiftedFormData period hPeriod
    |>.toDirectAnalyticData period hPeriod
    |>.toGeneric period hPeriod
    |>.finiteDimensional_operatorEigenspace
      analytic.boundary.triple analytic.condition eigenvalue hEigenvalue

/-- Lower spectral bound supplied by the coercive reference form. -/
theorem eigenvalue_ge_referenceParameter
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (analytic : CanonicalPhysicalScalarPDEAnalyticData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity))
    (eigenvalue : Real)
    (hEigenvalue : analytic.boundary.triple.LagrangianHasEigenvalue
      analytic.condition eigenvalue) :
    analytic.referenceParameter ≤ eigenvalue :=
  (analytic.toCutoffClosedAnalyticData period hPeriod)
    |>.eigenvalue_ge_referenceParameter period hPeriod eigenvalue hEigenvalue

/-- Four-layer PDE analytic certificate. -/
theorem certificate
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (analytic : CanonicalPhysicalScalarPDEAnalyticData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :
    Function.Surjective
        (P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D.canonicalScalarGreenCoreCompletedBoundaryTrace
          (analytic.boundary.geometric.greenCore period hPeriod).core
          ((analytic.boundary.completedInputs period hPeriod).traceBound
            period hPeriod
            (analytic.boundary.geometric.greenCore period hPeriod))) ∧
      analytic.boundary.triple.actualAdjointDomain analytic.condition =
        analytic.boundary.triple.realizationDomain analytic.condition ∧
      IsCompactOperator
        (P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D.canonicalPhysicalScalarH1ToBulkL2
          period hPeriod) ∧
      (∀ spectralParameter : Real,
        spectralParameter ≠ analytic.referenceParameter →
          analytic.boundary.triple.LagrangianHasEigenvalue
              analytic.condition spectralParameter ∨
            analytic.boundary.triple.LagrangianResolventPoint
              analytic.condition spectralParameter) ∧
      (∀ eigenvalue : Real,
        analytic.boundary.triple.LagrangianHasEigenvalue
            analytic.condition eigenvalue →
          analytic.referenceParameter ≤ eigenvalue) :=
  ⟨analytic.boundary.completedTraceSurjective period hPeriod,
    analytic.actualAdjointDomain_eq period hPeriod,
    analytic.rellichApproximation.rellich,
    analytic.fredholmAlternative period hPeriod,
    analytic.eigenvalue_ge_referenceParameter period hPeriod⟩

end CanonicalPhysicalScalarPDEAnalyticData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarPDEAnalyticClosure4D
end JanusFormal
