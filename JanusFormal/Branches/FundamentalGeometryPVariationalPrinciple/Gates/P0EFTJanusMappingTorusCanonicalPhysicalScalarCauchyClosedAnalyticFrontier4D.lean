import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyClosedAnalyticClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusEquatorialTubularCoverInverseRegularity4D

/-!
# Current physical scalar analytic frontier after closing Cauchy cutoffs

The following facts are no longer frontier assumptions:

* spherical coarea;
* density of smooth bulk scalar fields;
* construction and deck invariance of shrinking zero-Cauchy cutoffs;
* convergence of those cutoffs in physical bulk `L²`;
* density of the minimal core and injectivity of the maximal graph inclusion;
* the algebraic tubular inverse and the tubular--polar open cover;
* construction of the smooth Cauchy extension from a regular tubular inverse;
* completed trace surjectivity from componentwise extension estimates;
* Lax--Milgram resolvent construction, semiboundedness and compact spectral
  consequences.

The preferred frontier is `CauchyClosedAnalyticFrontier`.  Its genuine remaining
fields are organized as:

1. wave-operator globalization and the Euler-skew/divergence integral theorem;
2. smooth dense periodic value and antiperiodic normal boundary cores;
3. smoothness of the normalized equatorial-tail inverse on the non-polar band;
4. separate bulk-`L²` and Euler-residual bounds for the explicit Cauchy jet;
5. a squared Gårding estimate;
6. higher regularity with bounded normal trace;
7. smooth approximation of Hilbert-adjoint graph pairs;
8. coercivity of one shifted form;
9. compact approximation of the physical `H¹ -> L²` inclusion.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyClosedAnalyticFrontier4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyClosedAnalyticClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyClosedBoundaryTriple4D
open P0EFTJanusMappingTorusEquatorialTubularCoverInverseRegularity4D

universe x y r

variable (period : Real) (hPeriod : period ≠ 0)

/-- Preferred present physical scalar frontier. -/
abbrev CauchyClosedAnalyticFrontier
    (massSquared : Real)
    (ValueCore : Type x) (NormalCore : Type y)
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (Regularity : Type r)
    [NormedAddCommGroup Regularity] [NormedSpace Real Regularity]
    [CompleteSpace Regularity] :=
  CanonicalPhysicalScalarCauchyClosedAnalyticData
    period hPeriod massSquared ValueCore NormalCore
    (Regularity := Regularity)

/-- The only geometric inverse regularity datum needed by the current frontier
is the smooth standard-`S²` normalized-tail component. -/
abbrev TubularEquatorialBaseFrontier :=
  CanonicalLatitudeTubularEquatorialBaseRegularityData period hPeriod

/-- Every current frontier produces actual Hilbert self-adjointness. -/
theorem actualAdjointDomain_eq
    {ValueCore : Type x} {NormalCore : Type y} {Regularity : Type r}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    [NormedAddCommGroup Regularity] [NormedSpace Real Regularity]
    [CompleteSpace Regularity]
    (frontier : CauchyClosedAnalyticFrontier
      period hPeriod massSquared ValueCore NormalCore Regularity) :
    frontier.boundary.triple.actualAdjointDomain frontier.condition =
      frontier.boundary.triple.realizationDomain frontier.condition :=
  frontier.actualAdjointDomain_eq period hPeriod

/-- Every current frontier produces the direct Fredholm alternative. -/
theorem fredholmAlternative
    {ValueCore : Type x} {NormalCore : Type y} {Regularity : Type r}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    [NormedAddCommGroup Regularity] [NormedSpace Real Regularity]
    [CompleteSpace Regularity]
    (frontier : CauchyClosedAnalyticFrontier
      period hPeriod massSquared ValueCore NormalCore Regularity)
    (spectralParameter : Real)
    (hParameter : spectralParameter ≠ frontier.referenceParameter) :
    frontier.boundary.triple.LagrangianHasEigenvalue
        frontier.condition spectralParameter ∨
      frontier.boundary.triple.LagrangianResolventPoint
        frontier.condition spectralParameter :=
  frontier.fredholmAlternative period hPeriod spectralParameter hParameter

/-- Current frontier certificate. -/
theorem certificate
    {ValueCore : Type x} {NormalCore : Type y} {Regularity : Type r}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    [NormedAddCommGroup Regularity] [NormedSpace Real Regularity]
    [CompleteSpace Regularity]
    (frontier : CauchyClosedAnalyticFrontier
      period hPeriod massSquared ValueCore NormalCore Regularity) :
    DenseRange
        (P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D.smoothCanonicalPhysicalScalarFirstSheetCauchyTrace
          period hPeriod) ∧
      Function.Surjective
        (P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D.canonicalScalarGreenCoreCompletedBoundaryTrace
          frontier.boundary.cauchy.greenCore.core
          frontier.boundary.toCutoffClosedBoundaryData.toFullyGeometricBoundaryData
            |>.cutoffEllipticBoundaryData.toEllipticBoundaryData
            |>.toBoundaryConstructionData.traceBound) ∧
      frontier.boundary.triple.actualAdjointDomain frontier.condition =
        frontier.boundary.triple.realizationDomain frontier.condition ∧
      IsCompactOperator
        (P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D.canonicalPhysicalScalarH1ToBulkL2
          period hPeriod) :=
  ⟨frontier.boundary.cauchy.boundaryTrace_denseRange,
    frontier.boundary.extensionEstimate.completedBoundaryTrace_surjective
      (frontier.boundary.toCutoffClosedBoundaryData.toFullyGeometricBoundaryData
        |>.cutoffEllipticBoundaryData.toEllipticBoundaryData
        |>.toBoundaryConstructionData.traceBound),
    frontier.actualAdjointDomain_eq period hPeriod,
    frontier.rellichApproximation.rellich⟩

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyClosedAnalyticFrontier4D
end JanusFormal
