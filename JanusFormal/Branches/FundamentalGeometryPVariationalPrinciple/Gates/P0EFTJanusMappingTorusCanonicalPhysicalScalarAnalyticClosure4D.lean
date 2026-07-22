import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarHilbertGreenSystem4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarLagrangianAnalyticClosure4D

/-!
# Physical Janus specialization of the scalar analytic closure

The generic Lagrangian boundary theory is specialized here to the canonical
physical bulk and throat L2 spaces of the effective D8 quotient.

The structure below is intentionally an exact frontier record.  It asks for the
smooth physical Euler/normal-trace Green data, the paired graph bound,
closability, a closed Lagrangian boundary condition, density, actual-adjoint
characterization, one compact resolvent and a lower quadratic-form bound.

From these named inputs all abstract closure, variational and spectral
consequences become concrete theorems about the physical Janus scalar Hilbert
spaces.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarAnalyticClosure4D

set_option autoImplicit false
noncomputable section

open scoped ENNReal
open MeasureTheory Set Topology Module End
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarHilbertGreenSystem4D
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarClosedGraphRealization4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarLagrangianResolvent4D
open P0EFTJanusMappingTorusScalarLagrangianCompactSpectrum4D
open P0EFTJanusMappingTorusScalarLagrangianEigenmodeTheory4D
open P0EFTJanusMappingTorusScalarLagrangianFredholmAlternative4D
open P0EFTJanusMappingTorusScalarLagrangianSemiboundedSpectrum4D
open P0EFTJanusMappingTorusScalarLagrangianVariationalEigenprinciple4D
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

private abbrev SmoothDomain := SmoothQuotientField period hPeriod Real
private abbrev BulkL2 := CanonicalPhysicalBulkL2 period hPeriod
private abbrev ThroatL2 := CanonicalPhysicalThroatL2 period hPeriod

/-- Canonical physical Dirichlet Lagrangian condition. -/
noncomputable def canonicalPhysicalScalarDirichletLagrangianCondition :
    CanonicalScalarHilbertLagrangianBoundaryCondition
      (ThroatL2 period hPeriod) :=
  CanonicalScalarHilbertLagrangianBoundaryCondition.dirichlet
    (Trace := ThroatL2 period hPeriod)

/-- Canonical physical Neumann Lagrangian condition. -/
noncomputable def canonicalPhysicalScalarNeumannLagrangianCondition :
    CanonicalScalarHilbertLagrangianBoundaryCondition
      (ThroatL2 period hPeriod) :=
  CanonicalScalarHilbertLagrangianBoundaryCondition.neumann
    (Trace := ThroatL2 period hPeriod)

/-- Canonical physical constant Robin Lagrangian condition. -/
noncomputable def canonicalPhysicalScalarRobinLagrangianCondition
    (coefficient : Real) :
    CanonicalScalarHilbertLagrangianBoundaryCondition
      (ThroatL2 period hPeriod) :=
  CanonicalScalarHilbertLagrangianBoundaryCondition.scalarRobin
    (Trace := ThroatL2 period hPeriod) coefficient

/-- Physical bounded operator-valued Robin Lagrangian condition. -/
noncomputable def canonicalPhysicalScalarOperatorRobinLagrangianCondition
    (robin : ThroatL2 period hPeriod →L[Real] ThroatL2 period hPeriod)
    (hRobin : robin.toLinearMap.IsSymmetric) :
    CanonicalScalarHilbertLagrangianBoundaryCondition
      (ThroatL2 period hPeriod) :=
  CanonicalScalarHilbertLagrangianBoundaryCondition.robinGraph robin hRobin

/-- Full physical analytic closure input. -/
structure CanonicalPhysicalScalarAnalyticClosureData where
  smoothGreen : CanonicalPhysicalSmoothScalarGreenData period hPeriod
  graphBound : CanonicalPhysicalPairedBoundaryGraphBound
    period hPeriod smoothGreen
  closable : CanonicalScalarGraphClosable
    (canonicalPhysicalScalarHilbertGreenSystem period hPeriod smoothGreen)
  condition : CanonicalScalarHilbertLagrangianBoundaryCondition
    (ThroatL2 period hPeriod)
  analytic : CanonicalScalarLagrangianAnalyticClosureData
    (canonicalPhysicalScalarHilbertGreenSystem period hPeriod smoothGreen)
    closable
    (graphBound.toAbstract period hPeriod smoothGreen)
    condition

namespace CanonicalPhysicalScalarAnalyticClosureData

/-- Underlying generic physical Hilbert Green system. -/
def system
    (closureData : CanonicalPhysicalScalarAnalyticClosureData period hPeriod) :=
  canonicalPhysicalScalarHilbertGreenSystem
    period hPeriod closureData.smoothGreen

/-- Underlying abstract graph-bound input. -/
def abstractGraphBound
    (closureData : CanonicalPhysicalScalarAnalyticClosureData period hPeriod) :=
  closureData.graphBound.toAbstract
    period hPeriod closureData.smoothGreen

/-- Actual closed physical scalar operator domain. -/
abbrev ClosedDomain
    (closureData : CanonicalPhysicalScalarAnalyticClosureData period hPeriod) :=
  canonicalScalarClosedOperatorDomain closureData.system

/-- Physical Lagrangian operator domain. -/
abbrev LagrangianDomain
    (closureData : CanonicalPhysicalScalarAnalyticClosureData period hPeriod) :=
  canonicalScalarClosedLagrangianDomainSubmodule
    closureData.system closureData.closable closureData.abstractGraphBound
      closureData.condition

/-- Concrete physical domain equality with the supplied actual Hilbert adjoint. -/
theorem adjointDomain_eq
    (closureData : CanonicalPhysicalScalarAnalyticClosureData period hPeriod) :
    closureData.analytic.adjointCharacterization.adjointDomain =
      (closureData.LagrangianDomain period hPeriod :
        Set closureData.ClosedDomain) :=
  closureData.analytic.adjointDomain_eq
    closureData.system closureData.closable closureData.abstractGraphBound
      closureData.condition

/-- Physical non-reference Fredholm alternative. -/
theorem fredholmAlternative
    (closureData : CanonicalPhysicalScalarAnalyticClosureData period hPeriod)
    (spectralParameter : Real)
    (hParameter : spectralParameter ≠
      closureData.analytic.referenceParameter) :
    CanonicalScalarClosedLagrangianHasEigenvalue
        closureData.system closureData.closable closureData.abstractGraphBound
          closureData.condition spectralParameter ∨
      CanonicalScalarClosedLagrangianResolventPoint
        closureData.system closureData.closable closureData.abstractGraphBound
          closureData.condition spectralParameter :=
  closureData.analytic.fredholmAlternative
    closureData.system closureData.closable closureData.abstractGraphBound
      closureData.condition spectralParameter hParameter

/-- Finite multiplicity of every physical eigenvalue away from the reference
resolvent parameter. -/
theorem finiteDimensional_eigenspace
    (closureData : CanonicalPhysicalScalarAnalyticClosureData period hPeriod)
    (eigenvalue : Real)
    (hEigenvalue : eigenvalue ≠ closureData.analytic.referenceParameter) :
    FiniteDimensional Real
      (canonicalScalarClosedLagrangianOperatorEigenspace
        closureData.system closureData.closable closureData.abstractGraphBound
          closureData.condition eigenvalue) :=
  closureData.analytic.finiteDimensional_eigenspace
    closureData.system closureData.closable closureData.abstractGraphBound
      closureData.condition eigenvalue hEigenvalue

/-- Physical spectral lower bound. -/
theorem eigenvalue_ge_lowerBound
    (closureData : CanonicalPhysicalScalarAnalyticClosureData period hPeriod)
    (eigenvalue : Real)
    (hEigenvalue : CanonicalScalarClosedLagrangianHasEigenvalue
      closureData.system closureData.closable closureData.abstractGraphBound
        closureData.condition eigenvalue) :
    closureData.analytic.semibounded.lowerBound ≤ eigenvalue :=
  closureData.analytic.eigenvalue_ge_lowerBound
    closureData.system closureData.closable closureData.abstractGraphBound
      closureData.condition eigenvalue hEigenvalue

/-- Physical weak/strong variational equivalence. -/
theorem stationary_iff_eigenfield
    (closureData : CanonicalPhysicalScalarAnalyticClosureData period hPeriod)
    (eigenvalue : Real)
    (field : closureData.LagrangianDomain period hPeriod) :
    CanonicalScalarClosedLagrangianStationaryAt
        closureData.system closureData.closable closureData.abstractGraphBound
          closureData.condition eigenvalue field ↔
      canonicalScalarClosedLagrangianDomainOperator
          closureData.system closureData.closable closureData.abstractGraphBound
            closureData.condition field =
        eigenvalue • canonicalScalarClosedLagrangianDomainInclusion
          closureData.system closureData.closable closureData.abstractGraphBound
            closureData.condition field :=
  closureData.analytic.stationary_iff_eigenfield
    closureData.system closureData.closable closureData.abstractGraphBound
      closureData.condition eigenvalue field

/-- Complete physical analytic closure certificate. -/
theorem certificate
    (closureData : CanonicalPhysicalScalarAnalyticClosureData period hPeriod) :
    closureData.analytic.adjointCharacterization.adjointDomain =
        (closureData.LagrangianDomain period hPeriod :
          Set closureData.ClosedDomain) ∧
      (∀ spectralParameter : Real,
        spectralParameter ≠ closureData.analytic.referenceParameter →
          CanonicalScalarClosedLagrangianHasEigenvalue
              closureData.system closureData.closable
                closureData.abstractGraphBound closureData.condition
                spectralParameter ∨
            CanonicalScalarClosedLagrangianResolventPoint
              closureData.system closureData.closable
                closureData.abstractGraphBound closureData.condition
                spectralParameter) ∧
      (∀ eigenvalue : Real,
        CanonicalScalarClosedLagrangianHasEigenvalue
            closureData.system closureData.closable
              closureData.abstractGraphBound closureData.condition eigenvalue →
          closureData.analytic.semibounded.lowerBound ≤ eigenvalue) ∧
      (⨆ eigenvalue : Real,
        Module.End.eigenspace
          (closureData.analytic.compactResolvent.bounded.ambientResolvent
            closureData.system closureData.closable
              closureData.abstractGraphBound closureData.condition
              closureData.analytic.referenceParameter).toLinearMap eigenvalue)ᗮ = ⊥ :=
  canonicalScalarLagrangianAnalyticClosure_certificate
    closureData.system closureData.closable closureData.abstractGraphBound
      closureData.condition closureData.analytic

end CanonicalPhysicalScalarAnalyticClosureData

/-- Physical specialization certificate exposing the concrete bulk and throat
Hilbert spaces. -/
theorem canonicalPhysicalScalarAnalyticClosure_certificate
    (closureData : CanonicalPhysicalScalarAnalyticClosureData period hPeriod) :
    Nonempty (CanonicalPhysicalBulkL2 period hPeriod) ∧
      Nonempty (CanonicalPhysicalThroatL2 period hPeriod) ∧
      DenseRange (smoothToCanonicalPhysicalScalarH1 period hPeriod) ∧
      closureData.analytic.adjointCharacterization.adjointDomain =
        (closureData.LagrangianDomain period hPeriod :
          Set closureData.ClosedDomain) :=
  ⟨⟨0⟩, ⟨0⟩,
    smoothToCanonicalPhysicalScalarH1_denseRange period hPeriod,
    closureData.adjointDomain_eq period hPeriod⟩

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarAnalyticClosure4D
end JanusFormal
