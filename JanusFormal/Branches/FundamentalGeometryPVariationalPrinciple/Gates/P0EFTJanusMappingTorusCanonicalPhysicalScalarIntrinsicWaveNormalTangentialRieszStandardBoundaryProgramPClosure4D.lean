import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszProgramPClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveRieszStandardBoundaryProgramPClosure4D

/-!
# Standard boundaries for the normal/tangential Riesz endpoint

This file specializes the preferred normal/tangential Green decomposition to the
standard separated physical boundary conditions

`a Γ₀ u + b Γ₁ u = 0`,

with Dirichlet, Neumann and constant real Robin as canonical cases.

The completed pair `(Γ₀,Γ₁)` is the Riesz trace reconstructed from the Green form
and the bounded explicit Cauchy extension.  No independent normal regularity
input is retained.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszStandardBoundaryProgramPClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology MeasureTheory
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszPDEClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszResolventClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszProgramPClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveRieszStandardBoundaryProgramPClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalStandardBoundaryResolventClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFiniteRankRellich4D
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTriplePositiveShiftedForm4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev BoundaryL2 := CanonicalPhysicalScalarFirstSheetL2 period

private abbrev BulkL2 :=
  P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D.CanonicalPhysicalBulkL2
    period hPeriod

/-- Final normal/tangential Riesz data for one separated physical boundary
condition. -/
structure CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszSeparatedData
    (massSquared a b : Real)
    (hNondegenerate : a ≠ 0 ∨ b ≠ 0) where
  boundary : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszPDEData
    period hPeriod massSquared
  referenceParameter : Real
  shiftedPositiveDecomposition :
    boundary.triple.LagrangianShiftedPositiveDecompositionData
      (canonicalPhysicalScalarSeparatedCondition
        period a b hNondegenerate)
      referenceParameter
  finiteRankRellich : CanonicalPhysicalScalarFiniteRankRellichData
    period hPeriod

namespace CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszSeparatedData

/-- Conversion to the generic normal/tangential resolvent endpoint. -/
def toNormalTangentialRieszResolventData
    {a b : Real} {hNondegenerate : a ≠ 0 ∨ b ≠ 0}
    (data : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszSeparatedData
      period hPeriod massSquared a b hNondegenerate) :
    CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszResolventData
      period hPeriod massSquared where
  boundary := data.boundary
  condition := canonicalPhysicalScalarSeparatedCondition
    period a b hNondegenerate
  referenceParameter := data.referenceParameter
  shiftedPositiveDecomposition := data.shiftedPositiveDecomposition
  finiteRankRellich := data.finiteRankRellich

/-- Conversion to the established separated Riesz endpoint. -/
def toIntrinsicWaveRieszSeparatedData
    {a b : Real} {hNondegenerate : a ≠ 0 ∨ b ≠ 0}
    (data : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszSeparatedData
      period hPeriod massSquared a b hNondegenerate) :
    CanonicalPhysicalScalarIntrinsicWaveRieszSeparatedData
      period hPeriod massSquared a b hNondegenerate where
  boundary := data.boundary.toIntrinsicWaveRieszReducedPDEData
  referenceParameter := data.referenceParameter
  shiftedPositiveDecomposition := data.shiftedPositiveDecomposition
  finiteRankRellich := data.finiteRankRellich

/-- Membership in the separated realization is exactly the completed Riesz
Cauchy constraint. -/
theorem mem_lagrangianDomainSubmodule_iff
    {a b : Real} {hNondegenerate : a ≠ 0 ∨ b ≠ 0}
    (data : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszSeparatedData
      period hPeriod massSquared a b hNondegenerate)
    (field : data.boundary.triple.MaximalDomain) :
    field ∈ data.boundary.triple.lagrangianDomainSubmodule
        (canonicalPhysicalScalarSeparatedCondition
          period a b hNondegenerate) ↔
      a • (data.boundary.completedBoundaryTrace field).1 +
        b • (data.boundary.completedBoundaryTrace field).2 = 0 := by
  change data.boundary.completedBoundaryTrace field ∈
      canonicalScalarHilbertSeparatedBoundarySubmodule
        (Trace := BoundaryL2 period) a b ↔ _
  exact mem_canonicalScalarHilbertSeparatedBoundarySubmodule
    (Trace := BoundaryL2 period) a b _

/-- Actual Hilbert self-adjointness. -/
theorem actualAdjointDomain_eq
    {a b : Real} {hNondegenerate : a ≠ 0 ∨ b ≠ 0}
    (data : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszSeparatedData
      period hPeriod massSquared a b hNondegenerate) :
    data.boundary.triple.actualAdjointDomain
        (canonicalPhysicalScalarSeparatedCondition
          period a b hNondegenerate) =
      data.boundary.triple.realizationDomain
        (canonicalPhysicalScalarSeparatedCondition
          period a b hNondegenerate) :=
  (data.toNormalTangentialRieszResolventData period hPeriod)
    |>.actualAdjointDomain_eq period hPeriod

/-- Compact reference resolvent. -/
noncomputable def compactResolvent
    {a b : Real} {hNondegenerate : a ≠ 0 ∨ b ≠ 0}
    (data : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszSeparatedData
      period hPeriod massSquared a b hNondegenerate) :=
  (data.toNormalTangentialRieszResolventData period hPeriod)
    |>.compactResolvent period hPeriod

/-- Classical source solution. -/
noncomputable def sourceSolution
    {a b : Real} {hNondegenerate : a ≠ 0 ∨ b ≠ 0}
    (data : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszSeparatedData
      period hPeriod massSquared a b hNondegenerate) :
    BulkL2 period hPeriod →L[Real]
      data.boundary.triple.lagrangianDomainSubmodule
        (canonicalPhysicalScalarSeparatedCondition
          period a b hNondegenerate) :=
  (data.toNormalTangentialRieszResolventData period hPeriod)
    |>.sourceSolution period hPeriod

/-- Strong shifted source equation. -/
theorem sourceSolution_equation
    {a b : Real} {hNondegenerate : a ≠ 0 ∨ b ≠ 0}
    (data : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszSeparatedData
      period hPeriod massSquared a b hNondegenerate)
    (source : BulkL2 period hPeriod) :
    data.boundary.triple.lagrangianShiftedOperator
        (canonicalPhysicalScalarSeparatedCondition
          period a b hNondegenerate)
        data.referenceParameter
        (data.sourceSolution period hPeriod source) = source :=
  (data.toNormalTangentialRieszResolventData period hPeriod)
    |>.sourceSolution_equation period hPeriod source

/-- Unique global minimizer. -/
theorem sourceSolution_unique_minimizer
    {a b : Real} {hNondegenerate : a ≠ 0 ∨ b ≠ 0}
    (data : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszSeparatedData
      period hPeriod massSquared a b hNondegenerate)
    (source : BulkL2 period hPeriod) :
    (∀ field : data.boundary.triple.lagrangianDomainSubmodule
        (canonicalPhysicalScalarSeparatedCondition
          period a b hNondegenerate),
      data.boundary.triple.lagrangianSourceAction
          (canonicalPhysicalScalarSeparatedCondition
            period a b hNondegenerate)
          data.referenceParameter source
          (data.sourceSolution period hPeriod source) ≤
        data.boundary.triple.lagrangianSourceAction
          (canonicalPhysicalScalarSeparatedCondition
            period a b hNondegenerate)
          data.referenceParameter source field) ∧
      (∀ field : data.boundary.triple.lagrangianDomainSubmodule
          (canonicalPhysicalScalarSeparatedCondition
            period a b hNondegenerate),
        data.boundary.triple.lagrangianSourceAction
            (canonicalPhysicalScalarSeparatedCondition
              period a b hNondegenerate)
            data.referenceParameter source field =
          data.boundary.triple.lagrangianSourceAction
            (canonicalPhysicalScalarSeparatedCondition
              period a b hNondegenerate)
            data.referenceParameter source
            (data.sourceSolution period hPeriod source) →
        field = data.sourceSolution period hPeriod source) :=
  (data.toNormalTangentialRieszResolventData period hPeriod)
    |>.sourceSolution_unique_minimizer period hPeriod source

/-- Gaussian generating functional. -/
def gaussianGeneratingFunctional
    {a b : Real} {hNondegenerate : a ≠ 0 ∨ b ≠ 0}
    (data : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszSeparatedData
      period hPeriod massSquared a b hNondegenerate)
    (source : BulkL2 period hPeriod) : Real :=
  (data.toNormalTangentialRieszResolventData period hPeriod)
    |>.gaussianGeneratingFunctional period hPeriod source

/-- On-shell Gaussian identity and positivity. -/
theorem gaussian_certificate
    {a b : Real} {hNondegenerate : a ≠ 0 ∨ b ≠ 0}
    (data : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszSeparatedData
      period hPeriod massSquared a b hNondegenerate)
    (source : BulkL2 period hPeriod) :
    data.gaussianGeneratingFunctional period hPeriod source =
        -data.boundary.triple.lagrangianSourceAction
          (canonicalPhysicalScalarSeparatedCondition
            period a b hNondegenerate)
          data.referenceParameter source
          (data.sourceSolution period hPeriod source) ∧
      0 ≤ data.gaussianGeneratingFunctional period hPeriod source :=
  (data.toNormalTangentialRieszResolventData period hPeriod)
    |>.gaussianGeneratingFunctional_eq_neg_onShell period hPeriod source
    |> fun hOnShell =>
      ⟨hOnShell,
        (data.toNormalTangentialRieszResolventData period hPeriod)
          |>.gaussianGeneratingFunctional_nonnegative period hPeriod source⟩

/-- Complete separated normal/tangential Riesz Program P certificate. -/
theorem finalProgramP_certificate
    {a b : Real} {hNondegenerate : a ≠ 0 ∨ b ≠ 0}
    (data : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszSeparatedData
      period hPeriod massSquared a b hNondegenerate)
    (source : BulkL2 period hPeriod) :
    (∀ field test,
      (∫ parameter,
        data.boundary.geometric.tangentialDensity field test parameter
        ∂P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProductCoarea4D.canonicalLatitudeCauchyJetProductMeasure
          period) = 0) ∧
      data.boundary.triple.actualAdjointDomain
          (canonicalPhysicalScalarSeparatedCondition
            period a b hNondegenerate) =
        data.boundary.triple.realizationDomain
          (canonicalPhysicalScalarSeparatedCondition
            period a b hNondegenerate) ∧
      data.boundary.triple.lagrangianShiftedOperator
          (canonicalPhysicalScalarSeparatedCondition
            period a b hNondegenerate)
          data.referenceParameter
          (data.sourceSolution period hPeriod source) = source ∧
      (∀ field : data.boundary.triple.lagrangianDomainSubmodule
          (canonicalPhysicalScalarSeparatedCondition
            period a b hNondegenerate),
        data.boundary.triple.lagrangianSourceAction
            (canonicalPhysicalScalarSeparatedCondition
              period a b hNondegenerate)
            data.referenceParameter source
            (data.sourceSolution period hPeriod source) ≤
          data.boundary.triple.lagrangianSourceAction
            (canonicalPhysicalScalarSeparatedCondition
              period a b hNondegenerate)
            data.referenceParameter source field) ∧
      0 ≤ data.gaussianGeneratingFunctional period hPeriod source :=
  ⟨data.boundary.geometric.toNormalTangentialSplitData
      |>.tangential_integral_eq_zero,
    data.actualAdjointDomain_eq period hPeriod,
    data.sourceSolution_equation period hPeriod source,
    (data.sourceSolution_unique_minimizer period hPeriod source).1,
    (data.gaussian_certificate period hPeriod source).2⟩

end CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszSeparatedData

/-- Dirichlet normal/tangential Riesz endpoint. -/
abbrev CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszDirichletData
    (massSquared : Real) :=
  CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszSeparatedData
    period hPeriod massSquared 1 0 (Or.inl one_ne_zero)

/-- Neumann normal/tangential Riesz endpoint. -/
abbrev CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszNeumannData
    (massSquared : Real) :=
  CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszSeparatedData
    period hPeriod massSquared 0 1 (Or.inr one_ne_zero)

/-- Constant Robin normal/tangential Riesz endpoint. -/
abbrev CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszRobinData
    (massSquared coefficient : Real) :=
  CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszSeparatedData
    period hPeriod massSquared (-coefficient) 1 (Or.inr one_ne_zero)

namespace CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszSeparatedData

/-- Dirichlet domain is exactly zero Riesz value trace. -/
theorem mem_dirichletDomain_iff
    (data : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszDirichletData
      period hPeriod massSquared)
    (field : data.boundary.triple.MaximalDomain) :
    field ∈ data.boundary.triple.lagrangianDomainSubmodule
        (canonicalPhysicalScalarDirichletCondition period) ↔
      (data.boundary.completedBoundaryTrace field).1 = 0 := by
  change data.boundary.completedBoundaryTrace field ∈
      canonicalScalarHilbertDirichletBoundarySubmodule
        (Trace := BoundaryL2 period) ↔ _
  exact mem_canonicalScalarHilbertDirichletBoundarySubmodule
    (Trace := BoundaryL2 period) _

/-- Neumann domain is exactly zero Riesz normal trace. -/
theorem mem_neumannDomain_iff
    (data : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszNeumannData
      period hPeriod massSquared)
    (field : data.boundary.triple.MaximalDomain) :
    field ∈ data.boundary.triple.lagrangianDomainSubmodule
        (canonicalPhysicalScalarNeumannCondition period) ↔
      (data.boundary.completedBoundaryTrace field).2 = 0 := by
  change data.boundary.completedBoundaryTrace field ∈
      canonicalScalarHilbertNeumannBoundarySubmodule
        (Trace := BoundaryL2 period) ↔ _
  exact mem_canonicalScalarHilbertNeumannBoundarySubmodule
    (Trace := BoundaryL2 period) _

/-- Robin domain is exactly `Γ₁ = κ Γ₀`. -/
theorem mem_robinDomain_iff
    (coefficient : Real)
    (data : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszRobinData
      period hPeriod massSquared coefficient)
    (field : data.boundary.triple.MaximalDomain) :
    field ∈ data.boundary.triple.lagrangianDomainSubmodule
        (canonicalPhysicalScalarRobinCondition period coefficient) ↔
      (data.boundary.completedBoundaryTrace field).2 =
        coefficient • (data.boundary.completedBoundaryTrace field).1 := by
  change data.boundary.completedBoundaryTrace field ∈
      canonicalScalarHilbertRobinBoundarySubmodule
        (Trace := BoundaryL2 period) coefficient ↔ _
  exact mem_canonicalScalarHilbertRobinBoundarySubmodule
    (Trace := BoundaryL2 period) coefficient _

end CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszSeparatedData

/-- Marker theorem for the standard normal/tangential Riesz boundary endpoints. -/
theorem canonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszStandardBoundaryProgramPClosure_available : True :=
  trivial

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszStandardBoundaryProgramPClosure4D
end JanusFormal
