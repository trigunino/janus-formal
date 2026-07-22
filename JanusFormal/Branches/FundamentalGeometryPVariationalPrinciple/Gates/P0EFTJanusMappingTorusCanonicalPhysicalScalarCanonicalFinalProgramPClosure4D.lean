import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalFinalReducedAnalyticClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalFinalReducedVariational4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalFinalReducedGaussian4D

/-!
# Final canonical physical scalar Program P endpoint

This file exposes one stable endpoint for the completed physical scalar theory.
It combines the smallest current PDE and analytic data with the direct
variational and Gaussian consequences.

Once the fields of
`CanonicalPhysicalScalarCanonicalFinalReducedAnalyticData` are instantiated,
the endpoint gives in one place:

* the completed surjective boundary triple;
* actual Hilbert self-adjointness;
* a compact reference resolvent and the Fredholm alternative;
* finite eigenspace multiplicity and the lower spectral bound;
* the unique variational source solution;
* the symmetric nonnegative Gaussian generating functional.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalFinalProgramPClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology MeasureTheory
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalFinalReducedAnalyticClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalFinalReducedVariational4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalFinalReducedGaussian4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D

universe r

variable (period : Real) (hPeriod : period ≠ 0)
variable {Regularity : Type r}
  [NormedAddCommGroup Regularity] [NormedSpace Real Regularity]
  [CompleteSpace Regularity]

private abbrev BulkL2 :=
  P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D.CanonicalPhysicalBulkL2
    period hPeriod

/-- Stable abbreviation for the final scalar Program P input. -/
abbrev CanonicalPhysicalScalarProgramPFinalData
    (massSquared : Real) :=
  CanonicalPhysicalScalarCanonicalFinalReducedAnalyticData
    period hPeriod massSquared (Regularity := Regularity)

namespace CanonicalPhysicalScalarCanonicalFinalReducedAnalyticData

/-- Combined source, boundary and spectral certificate at the final endpoint. -/
theorem finalProgramP_certificate
    (analytic : CanonicalPhysicalScalarProgramPFinalData
      period hPeriod (Regularity := Regularity) massSquared)
    (source : BulkL2 period hPeriod) :
    Function.Surjective
        (canonicalScalarGreenCoreCompletedBoundaryTrace
          analytic.boundary.geometric.greenCore.core
          (analytic.boundary.completedInputs.traceBound
            analytic.boundary.geometric.greenCore)) ∧
      analytic.boundary.triple.actualAdjointDomain analytic.condition =
        analytic.boundary.triple.realizationDomain analytic.condition ∧
      analytic.boundary.triple.lagrangianShiftedOperator
          analytic.condition analytic.referenceParameter
          (analytic.sourceSolution period hPeriod source) = source ∧
      analytic.boundary.triple.lagrangianSourceStationary
          analytic.condition analytic.referenceParameter source
          (analytic.sourceSolution period hPeriod source) ∧
      analytic.gaussianGeneratingFunctional period hPeriod source =
        -analytic.boundary.triple.lagrangianSourceAction
          analytic.condition analytic.referenceParameter source
          (analytic.sourceSolution period hPeriod source) ∧
      0 ≤ analytic.gaussianGeneratingFunctional period hPeriod source ∧
      IsCompactOperator
        (P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D.canonicalPhysicalScalarH1ToBulkL2
          period hPeriod) ∧
      (∀ spectralParameter : Real,
        spectralParameter ≠ analytic.referenceParameter →
          analytic.boundary.triple.LagrangianHasEigenvalue
              analytic.condition spectralParameter ∨
            analytic.boundary.triple.LagrangianResolventPoint
              analytic.condition spectralParameter) :=
  ⟨analytic.boundary.certificate.2.2.2.2.1,
    analytic.actualAdjointDomain_eq period hPeriod,
    analytic.sourceSolution_equation period hPeriod source,
    analytic.sourceSolution_stationary period hPeriod source,
    analytic.gaussianGeneratingFunctional_eq_neg_onShell
      period hPeriod source,
    analytic.gaussianGeneratingFunctional_nonnegative
      period hPeriod source,
    analytic.finiteRankRellich.rellich,
    analytic.fredholmAlternative period hPeriod⟩

/-- The final source solution is the unique global minimizer and its Gaussian
response is nonnegative. -/
theorem finalProgramP_variationalGaussian_certificate
    (analytic : CanonicalPhysicalScalarProgramPFinalData
      period hPeriod (Regularity := Regularity) massSquared)
    (source : BulkL2 period hPeriod) :
    (∀ field : analytic.boundary.triple.lagrangianDomainSubmodule
        analytic.condition,
      analytic.boundary.triple.lagrangianSourceAction
          analytic.condition analytic.referenceParameter source
          (analytic.sourceSolution period hPeriod source) ≤
        analytic.boundary.triple.lagrangianSourceAction
          analytic.condition analytic.referenceParameter source field) ∧
      (∀ field : analytic.boundary.triple.lagrangianDomainSubmodule
          analytic.condition,
        analytic.boundary.triple.lagrangianSourceAction
            analytic.condition analytic.referenceParameter source field =
          analytic.boundary.triple.lagrangianSourceAction
            analytic.condition analytic.referenceParameter source
            (analytic.sourceSolution period hPeriod source) →
        field = analytic.sourceSolution period hPeriod source) ∧
      0 ≤ analytic.gaussianGeneratingFunctional period hPeriod source :=
  ⟨(analytic.sourceSolution_unique_minimizer period hPeriod source).1,
    (analytic.sourceSolution_unique_minimizer period hPeriod source).2,
    analytic.gaussianGeneratingFunctional_nonnegative period hPeriod source⟩

end CanonicalPhysicalScalarCanonicalFinalReducedAnalyticData

/-- Marker theorem for the final canonical physical scalar Program P endpoint. -/
theorem canonicalPhysicalScalarCanonicalFinalProgramPClosure_available : True :=
  trivial

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalFinalProgramPClosure4D
end JanusFormal
