import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarExplicitCauchyAnalyticClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalCauchyClosedGaussian4D

/-!
# Preferred explicit-Cauchy analytic frontier

This is the preferred current endpoint of the physical scalar Program P-B
formalization.  It exposes no abstract smooth extension, smooth-density,
minimal-core-density, completed-surjectivity, resolvent, semiboundedness or
compact-resolvent hypothesis.

Its remaining fields have direct mathematical meanings:

* atlas naturality and global continuity of the physical wave residual;
* the Euler-skew/divergence integral identity;
* periodic and antiperiodic continuous-to-smooth boundary approximation;
* smooth normalized-tail inverse coordinates on the non-polar sphere band;
* product-coarea bulk and Euler-residual estimates for the explicit Cauchy jet;
* Gårding and higher normal regularity;
* smooth approximation of adjoint graph pairs;
* one shifted-form coercivity theorem;
* one compact approximation scheme for `H¹ -> L²`.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarExplicitCauchyAnalyticFrontier4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusCanonicalPhysicalScalarExplicitCauchyAnalyticClosure4D

universe r

variable (period : Real) (hPeriod : period ≠ 0)

/-- Preferred current physical scalar frontier. -/
abbrev ExplicitCauchyAnalyticFrontier
    (massSquared : Real)
    (Regularity : Type r)
    [NormedAddCommGroup Regularity] [NormedSpace Real Regularity]
    [CompleteSpace Regularity] :=
  CanonicalPhysicalScalarExplicitCauchyAnalyticData
    period hPeriod massSquared (Regularity := Regularity)

/-- Every explicit-Cauchy frontier produces actual self-adjointness. -/
theorem actualAdjointDomain_eq
    {Regularity : Type r}
    [NormedAddCommGroup Regularity] [NormedSpace Real Regularity]
    [CompleteSpace Regularity]
    (frontier : ExplicitCauchyAnalyticFrontier
      period hPeriod massSquared Regularity) :
    frontier.boundary.triple.actualAdjointDomain frontier.condition =
      frontier.boundary.triple.realizationDomain frontier.condition :=
  frontier.actualAdjointDomain_eq period hPeriod

/-- Every explicit-Cauchy frontier produces the Fredholm alternative. -/
theorem fredholmAlternative
    {Regularity : Type r}
    [NormedAddCommGroup Regularity] [NormedSpace Real Regularity]
    [CompleteSpace Regularity]
    (frontier : ExplicitCauchyAnalyticFrontier
      period hPeriod massSquared Regularity)
    (spectralParameter : Real)
    (hParameter : spectralParameter ≠ frontier.referenceParameter) :
    frontier.boundary.triple.LagrangianHasEigenvalue
        frontier.condition spectralParameter ∨
      frontier.boundary.triple.LagrangianResolventPoint
        frontier.condition spectralParameter :=
  frontier.fredholmAlternative period hPeriod spectralParameter hParameter

/-- Preferred frontier certificate. -/
theorem certificate
    {Regularity : Type r}
    [NormedAddCommGroup Regularity] [NormedSpace Real Regularity]
    [CompleteSpace Regularity]
    (frontier : ExplicitCauchyAnalyticFrontier
      period hPeriod massSquared Regularity) :
    DenseRange
        (P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D.smoothCanonicalPhysicalScalarFirstSheetCauchyTrace
          period hPeriod) ∧
      frontier.boundary.triple.actualAdjointDomain frontier.condition =
        frontier.boundary.triple.realizationDomain frontier.condition ∧
      IsCompactOperator
        (P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D.canonicalPhysicalScalarH1ToBulkL2
          period hPeriod) ∧
      (∀ spectralParameter : Real,
        spectralParameter ≠ frontier.referenceParameter →
          frontier.boundary.triple.LagrangianHasEigenvalue
              frontier.condition spectralParameter ∨
            frontier.boundary.triple.LagrangianResolventPoint
              frontier.condition spectralParameter) :=
  ⟨frontier.boundary.green.toCanonicalCauchyJetGreenCoreData
      |>.boundaryTrace_denseRange,
    frontier.actualAdjointDomain_eq period hPeriod,
    frontier.rellichApproximation.rellich,
    frontier.fredholmAlternative period hPeriod⟩

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarExplicitCauchyAnalyticFrontier4D
end JanusFormal
