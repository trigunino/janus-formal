import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarHilbertGreenCoreLagrangianDensity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCompletedBoundaryTripleActualAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCompletedBoundaryTripleSemiboundedSpectrum4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCompletedBoundaryTripleEigenspace4D

/-!
# Direct analytic closure on a completed scalar boundary triple

The corrected boundary triple already is the maximal completed graph.  Its
minimal smooth core controls density, its Lagrangian submodules are closed and
symmetric, and maximal-adjoint regularity identifies the genuine Hilbert
adjoint.  One compact reference resolvent and one lower quadratic-form bound
then provide the full discrete semibounded spectral closure, including finite
multiplicity of every nonreference operator eigenspace.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarCompletedBoundaryTripleAnalyticClosure4D
end P0EFTJanusMappingTorusScalarCompletedBoundaryTripleAnalyticClosure4D

namespace P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D

set_option autoImplicit false
noncomputable section

open Set Topology Module End
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreMinimalClosable4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreMinimalClosable4D.CanonicalScalarHilbertGreenCore
open P0EFTJanusMappingTorusScalarHilbertGreenCoreLagrangianDensity4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreLagrangianDensity4D.CanonicalScalarCompletedBoundaryTripleData
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleActualAdjoint4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleResolvent4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleCompactSpectrum4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleFredholmAlternative4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleSemiboundedSpectrum4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleEigenspace4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

namespace CanonicalScalarCompletedBoundaryTripleData

variable {core : CanonicalScalarHilbertGreenCore
    (Domain := Domain) (Ambient := Ambient) (Trace := Trace)}
  {traceBound : HasCanonicalScalarHilbertGreenCoreBoundaryGraphBound core}

/-- Full direct analytic closure data for one completed Lagrangian condition. -/
structure LagrangianAnalyticClosureData
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace) where
  minimalDense :
    P0EFTJanusMappingTorusScalarHilbertGreenCoreMinimalClosable4D.CanonicalScalarHilbertGreenCore.MinimalCoreDense
      core
  adjointRegularity : triple.MaximalAdjointRegularity condition
  referenceParameter : Real
  compactResolvent : triple.LagrangianCompactResolventAt
    condition referenceParameter
  semibounded : triple.LagrangianSemiboundedData condition

namespace LagrangianAnalyticClosureData

/-- Density of the selected realization follows from the common minimal core. -/
theorem denseDomain
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (analytic : triple.LagrangianAnalyticClosureData condition) :
    DenseRange (triple.lagrangianInclusion condition) :=
  P0EFTJanusMappingTorusScalarHilbertGreenCoreLagrangianDensity4D.CanonicalScalarCompletedBoundaryTripleData.lagrangianInclusion_denseRange_of_minimalCore
    triple condition analytic.minimalDense

/-- Genuine Hilbert adjoint domain equals the realization domain. -/
theorem actualAdjointDomain_eq
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (analytic : triple.LagrangianAnalyticClosureData condition) :
    triple.actualAdjointDomain condition =
      triple.realizationDomain condition :=
  triple.actualAdjointDomain_eq_realizationDomain
    condition analytic.adjointRegularity

/-- Direct Fredholm alternative away from the reference parameter. -/
theorem fredholmAlternative
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (analytic : triple.LagrangianAnalyticClosureData condition)
    (spectralParameter : Real)
    (hParameter : spectralParameter ≠ analytic.referenceParameter) :
    triple.LagrangianHasEigenvalue condition spectralParameter ∨
      triple.LagrangianResolventPoint condition spectralParameter :=
  triple.lagrangian_fredholmAlternative condition
    analytic.referenceParameter spectralParameter
    (sub_ne_zero.mpr hParameter) analytic.compactResolvent

/-- Every nonreference direct operator eigenspace has finite multiplicity. -/
theorem finiteDimensional_operatorEigenspace
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (analytic : triple.LagrangianAnalyticClosureData condition)
    (eigenvalue : Real)
    (hEigenvalue : eigenvalue ≠ analytic.referenceParameter) :
    FiniteDimensional Real
      (triple.lagrangianOperatorEigenspace condition eigenvalue) :=
  analytic.compactResolvent.finiteDimensional_operatorEigenspace
    triple condition analytic.referenceParameter eigenvalue hEigenvalue

/-- Direct eigenfields of distinct eigenvalues are ambient-orthogonal. -/
theorem eigenfields_orthogonal
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (analytic : triple.LagrangianAnalyticClosureData condition)
    (firstEigenvalue secondEigenvalue : Real)
    (hDistinct : firstEigenvalue ≠ secondEigenvalue)
    (first : triple.lagrangianOperatorEigenspace condition firstEigenvalue)
    (second : triple.lagrangianOperatorEigenspace condition secondEigenvalue) :
    inner Real
        (triple.lagrangianInclusion condition first.1)
        (triple.lagrangianInclusion condition second.1) = 0 :=
  triple.lagrangianEigenfields_orthogonal condition
    firstEigenvalue secondEigenvalue hDistinct first second

/-- Every direct eigenvalue lies above the physical lower form bound. -/
theorem eigenvalue_ge_lowerBound
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (analytic : triple.LagrangianAnalyticClosureData condition)
    (eigenvalue : Real)
    (hEigenvalue : triple.LagrangianHasEigenvalue condition eigenvalue) :
    analytic.semibounded.lowerBound ≤ eigenvalue := by
  rcases hEigenvalue with ⟨field, hField, hEquation⟩
  exact analytic.semibounded.eigenvalue_ge_lowerBound
    triple condition eigenvalue field hField hEquation

/-- The lower open half-line is in the direct resolvent set away from the
reference parameter. -/
theorem lower_halfLine_resolvent
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (analytic : triple.LagrangianAnalyticClosureData condition) :
    Set.Iio analytic.semibounded.lowerBound \
        {analytic.referenceParameter} ⊆
      triple.lagrangianResolventSet condition :=
  analytic.semibounded.lower_halfLine_resolvent
    triple condition analytic.referenceParameter analytic.compactResolvent

/-- Spectral completeness of the direct compact ambient resolvent. -/
theorem spectral_complete
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (analytic : triple.LagrangianAnalyticClosureData condition) :
    (⨆ eigenvalue : Real,
      Module.End.eigenspace
        (analytic.compactResolvent.bounded.ambientResolvent
          triple condition analytic.referenceParameter).toLinearMap
        eigenvalue)ᗮ = ⊥ :=
  analytic.compactResolvent.spectral_complete
    triple condition analytic.referenceParameter

/-- Direct analytic-closure certificate. -/
theorem certificate
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (analytic : triple.LagrangianAnalyticClosureData condition) :
    DenseRange (triple.lagrangianInclusion condition) ∧
      triple.actualAdjointDomain condition =
        triple.realizationDomain condition ∧
      (∀ spectralParameter : Real,
        spectralParameter ≠ analytic.referenceParameter →
          triple.LagrangianHasEigenvalue condition spectralParameter ∨
            triple.LagrangianResolventPoint condition spectralParameter) ∧
      (∀ eigenvalue : Real,
        triple.LagrangianHasEigenvalue condition eigenvalue →
          analytic.semibounded.lowerBound ≤ eigenvalue) ∧
      (⨆ eigenvalue : Real,
        Module.End.eigenspace
          (analytic.compactResolvent.bounded.ambientResolvent
            triple condition analytic.referenceParameter).toLinearMap
          eigenvalue)ᗮ = ⊥ :=
  ⟨analytic.denseDomain triple condition,
    analytic.actualAdjointDomain_eq triple condition,
    analytic.fredholmAlternative triple condition,
    analytic.eigenvalue_ge_lowerBound triple condition,
    analytic.spectral_complete triple condition⟩

/-- Extended direct spectral certificate including finite multiplicity. -/
theorem spectral_certificate
    (triple : CanonicalScalarCompletedBoundaryTripleData core traceBound)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (analytic : triple.LagrangianAnalyticClosureData condition) :
    (∀ eigenvalue : Real,
      eigenvalue ≠ analytic.referenceParameter →
        FiniteDimensional Real
          (triple.lagrangianOperatorEigenspace condition eigenvalue)) ∧
      (∀ firstEigenvalue secondEigenvalue : Real,
        firstEigenvalue ≠ secondEigenvalue →
        ∀ first : triple.lagrangianOperatorEigenspace condition firstEigenvalue,
        ∀ second : triple.lagrangianOperatorEigenspace condition secondEigenvalue,
          inner Real
              (triple.lagrangianInclusion condition first.1)
              (triple.lagrangianInclusion condition second.1) = 0) :=
  ⟨analytic.finiteDimensional_operatorEigenspace triple condition,
    fun firstEigenvalue secondEigenvalue hDistinct first second =>
      analytic.eigenfields_orthogonal triple condition
        firstEigenvalue secondEigenvalue hDistinct first second⟩

end LagrangianAnalyticClosureData

end CanonicalScalarCompletedBoundaryTripleData

end
end P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D
end JanusFormal
