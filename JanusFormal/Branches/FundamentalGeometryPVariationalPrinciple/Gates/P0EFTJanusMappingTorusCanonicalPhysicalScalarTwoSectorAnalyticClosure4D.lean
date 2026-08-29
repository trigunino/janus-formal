import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarGreenIdentityBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarHilbertGreenSystemDirectSum4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarLagrangianAnalyticClosure4D

/-!
# Physical two-sector scalar analytic closure

Two physical scalar Green bridges on the same mapping torus combine into a
product Hilbert Green system.  Independent closed Lagrangian boundary
conditions combine componentwise.  Once the product trace estimate,
closability, density, adjoint characterization, compact resolvent and lower
form bound are supplied, the full scalar analytic closure applies to the Janus
doublet.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarTwoSectorAnalyticClosure4D

set_option autoImplicit false
noncomputable section

open scoped ENNReal
open MeasureTheory Set Topology Module End
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarHilbertGreenSystem4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarGreenIdentityBridge4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarClosedGraphRealization4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarHilbertBoundaryDirectSum4D
open P0EFTJanusMappingTorusScalarHilbertGreenSystemDirectSum4D
open P0EFTJanusMappingTorusScalarLagrangianResolvent4D
open P0EFTJanusMappingTorusScalarLagrangianEigenmodeTheory4D
open P0EFTJanusMappingTorusScalarLagrangianFredholmAlternative4D
open P0EFTJanusMappingTorusScalarLagrangianAnalyticClosure4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance canonicalLorentzVolumeFinite :
    IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

local instance canonicalThroatVolumeFinite :
    IsFiniteMeasure
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod

private abbrev PhysicalTrace := CanonicalPhysicalThroatL2 period hPeriod
private abbrev ProductTrace := WithLp 2
  (PhysicalTrace period hPeriod × PhysicalTrace period hPeriod)

/-- Two physical scalar Green bridges. -/
structure CanonicalPhysicalScalarTwoSectorGreenData where
  left : CanonicalPhysicalScalarGreenIdentityBridgeData period hPeriod
  right : CanonicalPhysicalScalarGreenIdentityBridgeData period hPeriod

namespace CanonicalPhysicalScalarTwoSectorGreenData

/-- Left physical Green system. -/
def leftSystem
    (green : CanonicalPhysicalScalarTwoSectorGreenData period hPeriod) :=
  green.left.toHilbertGreenSystem period hPeriod

/-- Right physical Green system. -/
def rightSystem
    (green : CanonicalPhysicalScalarTwoSectorGreenData period hPeriod) :=
  green.right.toHilbertGreenSystem period hPeriod

/-- Product physical Green system. -/
def system
    (green : CanonicalPhysicalScalarTwoSectorGreenData period hPeriod) :=
  CanonicalScalarHilbertGreenSystem.directSum
    green.leftSystem green.rightSystem

/-- Product Lagrangian boundary condition. -/
noncomputable def boundaryCondition
    (green : CanonicalPhysicalScalarTwoSectorGreenData period hPeriod)
    (leftCondition rightCondition :
      CanonicalScalarHilbertLagrangianBoundaryCondition
        (PhysicalTrace period hPeriod)) :
    CanonicalScalarHilbertLagrangianBoundaryCondition
      (ProductTrace period hPeriod) :=
  CanonicalScalarHilbertLagrangianBoundaryCondition.directSum
    leftCondition rightCondition

/-- Product Green identity certificate. -/
theorem green_certificate
    (green : CanonicalPhysicalScalarTwoSectorGreenData period hPeriod) :
    Function.Surjective green.system.boundaryTrace ∧
      (∀ first second,
        inner Real (green.system.operator first)
              (green.system.inclusion second) -
            inner Real (green.system.inclusion first)
              (green.system.operator second) =
          2 * P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D.canonicalScalarHilbertBoundarySymplecticForm
            (green.system.boundaryTrace first)
            (green.system.boundaryTrace second)) :=
  canonicalScalarHilbertGreenSystemDirectSum_certificate
    green.leftSystem green.rightSystem

end CanonicalPhysicalScalarTwoSectorGreenData

/-- Remaining analytic inputs for the physical scalar doublet. -/
structure CanonicalPhysicalScalarTwoSectorAnalyticClosureData
    (green : CanonicalPhysicalScalarTwoSectorGreenData period hPeriod) where
  leftCondition : CanonicalScalarHilbertLagrangianBoundaryCondition
    (PhysicalTrace period hPeriod)
  rightCondition : CanonicalScalarHilbertLagrangianBoundaryCondition
    (PhysicalTrace period hPeriod)
  graphBound : CanonicalScalarHilbertGreenSystemDirectSumGraphBound
    green.leftSystem green.rightSystem
  closable : CanonicalScalarGraphClosable green.system
  analytic : CanonicalScalarLagrangianAnalyticClosureData
    green.system closable
      (graphBound.toAbstract green.leftSystem green.rightSystem)
      (CanonicalPhysicalScalarTwoSectorGreenData.boundaryCondition
        period hPeriod green leftCondition rightCondition)

namespace CanonicalPhysicalScalarTwoSectorAnalyticClosureData

/-- Combined abstract graph bound. -/
def abstractGraphBound
    {green : CanonicalPhysicalScalarTwoSectorGreenData period hPeriod}
    (closure : CanonicalPhysicalScalarTwoSectorAnalyticClosureData
      period hPeriod green) :=
  closure.graphBound.toAbstract green.leftSystem green.rightSystem

/-- Combined boundary condition. -/
def condition
    {green : CanonicalPhysicalScalarTwoSectorGreenData period hPeriod}
    (closure : CanonicalPhysicalScalarTwoSectorAnalyticClosureData
      period hPeriod green) :=
  CanonicalPhysicalScalarTwoSectorGreenData.boundaryCondition
    period hPeriod green closure.leftCondition closure.rightCondition

/-- Actual product closed-operator domain. -/
def operatorDomain
    {green : CanonicalPhysicalScalarTwoSectorGreenData period hPeriod}
    (closure : CanonicalPhysicalScalarTwoSectorAnalyticClosureData
      period hPeriod green) :=
  canonicalScalarClosedLagrangianDomainSubmodule
    green.system closure.closable closure.abstractGraphBound closure.condition

/-- Product-domain adjoint equality. -/
theorem adjointDomain_eq
    {green : CanonicalPhysicalScalarTwoSectorGreenData period hPeriod}
    (closure : CanonicalPhysicalScalarTwoSectorAnalyticClosureData
      period hPeriod green) :
    closure.analytic.adjointCharacterization.adjointDomain =
      (closure.operatorDomain :
        Set (canonicalScalarClosedOperatorDomain green.system)) :=
  closure.analytic.adjointDomain_eq
    green.system closure.closable closure.abstractGraphBound closure.condition

/-- Fredholm alternative for the physical scalar doublet. -/
theorem fredholmAlternative
    {green : CanonicalPhysicalScalarTwoSectorGreenData period hPeriod}
    (closure : CanonicalPhysicalScalarTwoSectorAnalyticClosureData
      period hPeriod green)
    (spectralParameter : Real)
    (hParameter : spectralParameter ≠ closure.analytic.referenceParameter) :
    CanonicalScalarClosedLagrangianHasEigenvalue
        green.system closure.closable closure.abstractGraphBound
          closure.condition spectralParameter ∨
      CanonicalScalarClosedLagrangianResolventPoint
        green.system closure.closable closure.abstractGraphBound
          closure.condition spectralParameter :=
  closure.analytic.fredholmAlternative
    green.system closure.closable closure.abstractGraphBound closure.condition
      spectralParameter hParameter

/-- Finite multiplicity of every non-reference doublet eigenspace. -/
theorem finiteDimensional_eigenspace
    {green : CanonicalPhysicalScalarTwoSectorGreenData period hPeriod}
    (closure : CanonicalPhysicalScalarTwoSectorAnalyticClosureData
      period hPeriod green)
    (eigenvalue : Real)
    (hEigenvalue : eigenvalue ≠ closure.analytic.referenceParameter) :
    FiniteDimensional Real
      (canonicalScalarClosedLagrangianOperatorEigenspace
        green.system closure.closable closure.abstractGraphBound
          closure.condition eigenvalue) :=
  closure.analytic.finiteDimensional_eigenspace
    green.system closure.closable closure.abstractGraphBound closure.condition
      eigenvalue hEigenvalue

/-- Lower spectral bound for the doublet. -/
theorem eigenvalue_ge_lowerBound
    {green : CanonicalPhysicalScalarTwoSectorGreenData period hPeriod}
    (closure : CanonicalPhysicalScalarTwoSectorAnalyticClosureData
      period hPeriod green)
    (eigenvalue : Real)
    (hEigenvalue : CanonicalScalarClosedLagrangianHasEigenvalue
      green.system closure.closable closure.abstractGraphBound
        closure.condition eigenvalue) :
    closure.analytic.semibounded.lowerBound ≤ eigenvalue :=
  closure.analytic.eigenvalue_ge_lowerBound
    green.system closure.closable closure.abstractGraphBound closure.condition
      eigenvalue hEigenvalue

/-- Physical two-sector closure certificate. -/
theorem certificate
    {green : CanonicalPhysicalScalarTwoSectorGreenData period hPeriod}
    (closure : CanonicalPhysicalScalarTwoSectorAnalyticClosureData
      period hPeriod green) :
    closure.analytic.adjointCharacterization.adjointDomain =
        (closure.operatorDomain :
          Set (canonicalScalarClosedOperatorDomain green.system)) ∧
      (∀ spectralParameter : Real,
        spectralParameter ≠ closure.analytic.referenceParameter →
          CanonicalScalarClosedLagrangianHasEigenvalue
              green.system closure.closable closure.abstractGraphBound
                closure.condition spectralParameter ∨
            CanonicalScalarClosedLagrangianResolventPoint
              green.system closure.closable closure.abstractGraphBound
                closure.condition spectralParameter) ∧
      (∀ eigenvalue : Real,
        CanonicalScalarClosedLagrangianHasEigenvalue
            green.system closure.closable closure.abstractGraphBound
              closure.condition eigenvalue →
          closure.analytic.semibounded.lowerBound ≤ eigenvalue) :=
  ⟨closure.adjointDomain_eq,
    closure.fredholmAlternative,
    closure.eigenvalue_ge_lowerBound⟩

end CanonicalPhysicalScalarTwoSectorAnalyticClosureData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarTwoSectorAnalyticClosure4D
end JanusFormal
