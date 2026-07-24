import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCutoffClosedAnalyticClosure4D

/-!
# Preferred analytic frontier after global cutoff closure

This is the current smallest physical scalar analytic frontier.  Smooth bulk
`L²` density and shrinking zero-Cauchy collar cutoffs have been removed from the
input record because they are now unconditional theorems.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCutoffClosedAnalyticFrontier4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCutoffClosedAnalyticClosure4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D

variable (period : Real) (hPeriod : period ≠ 0)
variable {massSquared : Real}

/-- Preferred current frontier. -/
abbrev CutoffClosedAnalyticFrontier
    (massSquared : Real)
    (ValueCore : Type*) (NormalCore : Type*)
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (Regularity : Type*)
    [NormedAddCommGroup Regularity] [NormedSpace Real Regularity]
    [CompleteSpace Regularity] :=
  CanonicalPhysicalScalarCutoffClosedAnalyticData
    period hPeriod massSquared ValueCore NormalCore
    (Regularity := Regularity)

/-- Every cutoff-closed frontier yields actual Hilbert self-adjointness. -/
theorem actualAdjointDomain_eq
    {ValueCore NormalCore Regularity : Type*}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    [NormedAddCommGroup Regularity] [NormedSpace Real Regularity]
    [CompleteSpace Regularity]
    (frontier : CutoffClosedAnalyticFrontier
      period hPeriod massSquared ValueCore NormalCore Regularity) :
    frontier.boundary.triple.actualAdjointDomain frontier.condition =
      frontier.boundary.triple.realizationDomain frontier.condition :=
  frontier.actualAdjointDomain_eq period hPeriod

/-- Every cutoff-closed frontier yields the direct Fredholm alternative. -/
theorem fredholmAlternative
    {ValueCore NormalCore Regularity : Type*}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    [NormedAddCommGroup Regularity] [NormedSpace Real Regularity]
    [CompleteSpace Regularity]
    (frontier : CutoffClosedAnalyticFrontier
      period hPeriod massSquared ValueCore NormalCore Regularity)
    (spectralParameter : Real)
    (hParameter : spectralParameter ≠ frontier.referenceParameter) :
    frontier.boundary.triple.LagrangianHasEigenvalue
        frontier.condition spectralParameter ∨
      frontier.boundary.triple.LagrangianResolventPoint
        frontier.condition spectralParameter :=
  frontier.fredholmAlternative period hPeriod spectralParameter hParameter

/-- Current-frontier certificate. -/
theorem certificate
    {ValueCore NormalCore Regularity : Type*}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    [NormedAddCommGroup Regularity] [NormedSpace Real Regularity]
    [CompleteSpace Regularity]
    (frontier : CutoffClosedAnalyticFrontier
      period hPeriod massSquared ValueCore NormalCore Regularity) :
    frontier.boundary.geometric.greenCore.MinimalCoreDense period hPeriod ∧
      Function.Injective
        (canonicalScalarGreenCoreGraphInclusion
          frontier.boundary.geometric.greenCore.core) ∧
      frontier.boundary.triple.actualAdjointDomain frontier.condition =
        frontier.boundary.triple.realizationDomain frontier.condition ∧
      IsCompactOperator
        (P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D.canonicalPhysicalScalarH1ToBulkL2
          period hPeriod) :=
  ⟨frontier.minimalCoreDense period hPeriod,
    frontier.graphInclusion_injective period hPeriod,
    frontier.actualAdjointDomain_eq period hPeriod,
    frontier.rellichApproximation.rellich⟩

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCutoffClosedAnalyticFrontier4D
end JanusFormal
