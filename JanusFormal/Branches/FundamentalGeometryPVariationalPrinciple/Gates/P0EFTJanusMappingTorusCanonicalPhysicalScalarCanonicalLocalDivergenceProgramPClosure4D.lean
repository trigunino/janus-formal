import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalLocalDivergenceResolventClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalResolventReducedVariational4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalResolventReducedGaussian4D

/-!
# Program P endpoint from the canonical local divergence bridge

This endpoint combines the smallest local Green/PDE package with the complete
adjoint-free physical scalar theory.  It exposes the classical source solution,
variational minimum, Gaussian response and compact spectral conclusions while
retaining the local half-collar formulation of Green's theorem.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalLocalDivergenceProgramPClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology MeasureTheory
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalLocalDivergenceResolventClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalResolventReducedAnalyticClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalResolventReducedVariational4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalResolventReducedGaussian4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D

universe r

variable (period : Real) (hPeriod : period ≠ 0)
variable {Regularity : Type r}
  [NormedAddCommGroup Regularity] [NormedSpace Real Regularity]
  [CompleteSpace Regularity]

private abbrev BulkL2 :=
  P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D.CanonicalPhysicalBulkL2
    period hPeriod

namespace CanonicalPhysicalScalarCanonicalLocalDivergenceResolventData

/-- Conversion to the generic variational/Gaussian endpoint. -/
def toFinalAnalyticData
    (data : CanonicalPhysicalScalarCanonicalLocalDivergenceResolventData
      period hPeriod massSquared (Regularity := Regularity)) :=
  data.toResolventReducedAnalyticData

/-- Classical source solution. -/
noncomputable def sourceSolution
    (data : CanonicalPhysicalScalarCanonicalLocalDivergenceResolventData
      period hPeriod massSquared (Regularity := Regularity)) :
    BulkL2 period hPeriod →L[Real]
      data.boundary.triple.lagrangianDomainSubmodule data.condition :=
  (data.toFinalAnalyticData period hPeriod).sourceSolution period hPeriod

/-- Strong shifted source equation. -/
theorem sourceSolution_equation
    (data : CanonicalPhysicalScalarCanonicalLocalDivergenceResolventData
      period hPeriod massSquared (Regularity := Regularity))
    (source : BulkL2 period hPeriod) :
    data.boundary.triple.lagrangianShiftedOperator
        data.condition data.referenceParameter
        (data.sourceSolution period hPeriod source) = source :=
  (data.toFinalAnalyticData period hPeriod)
    |>.sourceSolution_equation period hPeriod source

/-- Weak stationarity. -/
theorem sourceSolution_stationary
    (data : CanonicalPhysicalScalarCanonicalLocalDivergenceResolventData
      period hPeriod massSquared (Regularity := Regularity))
    (source : BulkL2 period hPeriod) :
    data.boundary.triple.lagrangianSourceStationary
      data.condition data.referenceParameter source
      (data.sourceSolution period hPeriod source) :=
  (data.toFinalAnalyticData period hPeriod)
    |>.sourceSolution_stationary period hPeriod source

/-- Unique global minimizer. -/
theorem sourceSolution_unique_minimizer
    (data : CanonicalPhysicalScalarCanonicalLocalDivergenceResolventData
      period hPeriod massSquared (Regularity := Regularity))
    (source : BulkL2 period hPeriod) :
    (∀ field : data.boundary.triple.lagrangianDomainSubmodule data.condition,
      data.boundary.triple.lagrangianSourceAction
          data.condition data.referenceParameter source
          (data.sourceSolution period hPeriod source) ≤
        data.boundary.triple.lagrangianSourceAction
          data.condition data.referenceParameter source field) ∧
      (∀ field : data.boundary.triple.lagrangianDomainSubmodule data.condition,
        data.boundary.triple.lagrangianSourceAction
            data.condition data.referenceParameter source field =
          data.boundary.triple.lagrangianSourceAction
            data.condition data.referenceParameter source
            (data.sourceSolution period hPeriod source) →
        field = data.sourceSolution period hPeriod source) :=
  (data.toFinalAnalyticData period hPeriod)
    |>.sourceSolution_unique_minimizer period hPeriod source

/-- Gaussian source pairing. -/
def gaussianPairing
    (data : CanonicalPhysicalScalarCanonicalLocalDivergenceResolventData
      period hPeriod massSquared (Regularity := Regularity))
    (first second : BulkL2 period hPeriod) : Real :=
  (data.toFinalAnalyticData period hPeriod)
    |>.gaussianPairing period hPeriod first second

/-- Gaussian generating functional. -/
def gaussianGeneratingFunctional
    (data : CanonicalPhysicalScalarCanonicalLocalDivergenceResolventData
      period hPeriod massSquared (Regularity := Regularity))
    (source : BulkL2 period hPeriod) : Real :=
  (data.toFinalAnalyticData period hPeriod)
    |>.gaussianGeneratingFunctional period hPeriod source

/-- On-shell Gaussian identity and positivity. -/
theorem gaussian_certificate
    (data : CanonicalPhysicalScalarCanonicalLocalDivergenceResolventData
      period hPeriod massSquared (Regularity := Regularity))
    (source : BulkL2 period hPeriod) :
    data.gaussianGeneratingFunctional period hPeriod source =
        -data.boundary.triple.lagrangianSourceAction
          data.condition data.referenceParameter source
          (data.sourceSolution period hPeriod source) ∧
      0 ≤ data.gaussianGeneratingFunctional period hPeriod source :=
  (data.toFinalAnalyticData period hPeriod)
    |>.gaussian_certificate period hPeriod source

/-- Complete local-divergence Program P certificate. -/
theorem finalProgramP_certificate
    (data : CanonicalPhysicalScalarCanonicalLocalDivergenceResolventData
      period hPeriod massSquared (Regularity := Regularity))
    (source : BulkL2 period hPeriod) :
    Function.Surjective
        (canonicalScalarGreenCoreCompletedBoundaryTrace
          data.boundary.geometric.greenCore.core
          (data.boundary.completedInputs.traceBound
            data.boundary.geometric.greenCore)) ∧
      data.boundary.triple.actualAdjointDomain data.condition =
        data.boundary.triple.realizationDomain data.condition ∧
      data.boundary.triple.lagrangianShiftedOperator
          data.condition data.referenceParameter
          (data.sourceSolution period hPeriod source) = source ∧
      data.boundary.triple.lagrangianSourceStationary
          data.condition data.referenceParameter source
          (data.sourceSolution period hPeriod source) ∧
      0 ≤ data.gaussianGeneratingFunctional period hPeriod source ∧
      (∀ spectralParameter : Real,
        spectralParameter ≠ data.referenceParameter →
          data.boundary.triple.LagrangianHasEigenvalue
              data.condition spectralParameter ∨
            data.boundary.triple.LagrangianResolventPoint
              data.condition spectralParameter) :=
  ⟨data.boundary.certificate.2.2.1,
    data.actualAdjointDomain_eq period hPeriod,
    data.sourceSolution_equation period hPeriod source,
    data.sourceSolution_stationary period hPeriod source,
    (data.gaussian_certificate period hPeriod source).2,
    data.fredholmAlternative period hPeriod⟩

end CanonicalPhysicalScalarCanonicalLocalDivergenceResolventData

/-- Marker theorem for the local-divergence Program P endpoint. -/
theorem canonicalPhysicalScalarCanonicalLocalDivergenceProgramPClosure_available : True :=
  trivial

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalLocalDivergenceProgramPClosure4D
end JanusFormal
