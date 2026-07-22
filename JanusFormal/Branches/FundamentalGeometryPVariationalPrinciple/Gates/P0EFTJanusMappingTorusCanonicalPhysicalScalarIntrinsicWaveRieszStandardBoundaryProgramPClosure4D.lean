import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveRieszProgramPClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalStandardBoundaryResolventClosure4D

/-!
# Standard boundary realizations through the Riesz completed trace

The Riesz boundary construction supplies the completed Cauchy pair without an
independent normal trace theorem.  This file specializes it to the standard
separated physical conditions

`a Γ₀ u + b Γ₁ u = 0`,

including Dirichlet, Neumann and constant real Robin realizations.

For each family, one positive shifted-form decomposition and one finite-rank
Rellich scheme give the complete self-adjoint, compact spectral, variational and
Gaussian Program P output.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveRieszStandardBoundaryProgramPClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology MeasureTheory
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveRieszReducedPDEClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveRieszResolventClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveRieszProgramPClosure4D
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

/-- Final Riesz data for one separated physical boundary condition. -/
structure CanonicalPhysicalScalarIntrinsicWaveRieszSeparatedData
    (massSquared a b : Real)
    (hNondegenerate : a ≠ 0 ∨ b ≠ 0) where
  boundary : CanonicalPhysicalScalarIntrinsicWaveRieszReducedPDEData
    period hPeriod massSquared
  referenceParameter : Real
  shiftedPositiveDecomposition :
    boundary.triple.LagrangianShiftedPositiveDecompositionData
      (canonicalPhysicalScalarSeparatedCondition
        period a b hNondegenerate)
      referenceParameter
  finiteRankRellich : CanonicalPhysicalScalarFiniteRankRellichData
    period hPeriod

namespace CanonicalPhysicalScalarIntrinsicWaveRieszSeparatedData

/-- Conversion to the generic Riesz resolvent endpoint. -/
def toRieszResolventData
    {a b : Real} {hNondegenerate : a ≠ 0 ∨ b ≠ 0}
    (data : CanonicalPhysicalScalarIntrinsicWaveRieszSeparatedData
      period hPeriod massSquared a b hNondegenerate) :
    CanonicalPhysicalScalarIntrinsicWaveRieszResolventData
      period hPeriod massSquared where
  boundary := data.boundary
  condition := canonicalPhysicalScalarSeparatedCondition
    period a b hNondegenerate
  referenceParameter := data.referenceParameter
  shiftedPositiveDecomposition := data.shiftedPositiveDecomposition
  finiteRankRellich := data.finiteRankRellich

/-- Membership in the separated Riesz realization is exactly the completed
Cauchy constraint. -/
theorem mem_lagrangianDomainSubmodule_iff
    {a b : Real} {hNondegenerate : a ≠ 0 ∨ b ≠ 0}
    (data : CanonicalPhysicalScalarIntrinsicWaveRieszSeparatedData
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
    (data : CanonicalPhysicalScalarIntrinsicWaveRieszSeparatedData
      period hPeriod massSquared a b hNondegenerate) :
    data.boundary.triple.actualAdjointDomain
        (canonicalPhysicalScalarSeparatedCondition
          period a b hNondegenerate) =
      data.boundary.triple.realizationDomain
        (canonicalPhysicalScalarSeparatedCondition
          period a b hNondegenerate) :=
  (data.toRieszResolventData period hPeriod)
    |>.actualAdjointDomain_eq period hPeriod

/-- Compact reference resolvent. -/
noncomputable def compactResolvent
    {a b : Real} {hNondegenerate : a ≠ 0 ∨ b ≠ 0}
    (data : CanonicalPhysicalScalarIntrinsicWaveRieszSeparatedData
      period hPeriod massSquared a b hNondegenerate) :=
  (data.toRieszResolventData period hPeriod)
    |>.compactResolvent period hPeriod

/-- Classical source solution. -/
noncomputable def sourceSolution
    {a b : Real} {hNondegenerate : a ≠ 0 ∨ b ≠ 0}
    (data : CanonicalPhysicalScalarIntrinsicWaveRieszSeparatedData
      period hPeriod massSquared a b hNondegenerate) :
    BulkL2 period hPeriod →L[Real]
      data.boundary.triple.lagrangianDomainSubmodule
        (canonicalPhysicalScalarSeparatedCondition
          period a b hNondegenerate) :=
  (data.toRieszResolventData period hPeriod)
    |>.sourceSolution period hPeriod

/-- Strong shifted source equation. -/
theorem sourceSolution_equation
    {a b : Real} {hNondegenerate : a ≠ 0 ∨ b ≠ 0}
    (data : CanonicalPhysicalScalarIntrinsicWaveRieszSeparatedData
      period hPeriod massSquared a b hNondegenerate)
    (source : BulkL2 period hPeriod) :
    data.boundary.triple.lagrangianShiftedOperator
        (canonicalPhysicalScalarSeparatedCondition
          period a b hNondegenerate)
        data.referenceParameter
        (data.sourceSolution period hPeriod source) = source :=
  (data.toRieszResolventData period hPeriod)
    |>.sourceSolution_equation period hPeriod source

/-- Unique global minimizer. -/
theorem sourceSolution_unique_minimizer
    {a b : Real} {hNondegenerate : a ≠ 0 ∨ b ≠ 0}
    (data : CanonicalPhysicalScalarIntrinsicWaveRieszSeparatedData
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
  (data.toRieszResolventData period hPeriod)
    |>.sourceSolution_unique_minimizer period hPeriod source

/-- Gaussian generating functional. -/
def gaussianGeneratingFunctional
    {a b : Real} {hNondegenerate : a ≠ 0 ∨ b ≠ 0}
    (data : CanonicalPhysicalScalarIntrinsicWaveRieszSeparatedData
      period hPeriod massSquared a b hNondegenerate)
    (source : BulkL2 period hPeriod) : Real :=
  (data.toRieszResolventData period hPeriod)
    |>.gaussianGeneratingFunctional period hPeriod source

/-- On-shell Gaussian identity and positivity. -/
theorem gaussian_certificate
    {a b : Real} {hNondegenerate : a ≠ 0 ∨ b ≠ 0}
    (data : CanonicalPhysicalScalarIntrinsicWaveRieszSeparatedData
      period hPeriod massSquared a b hNondegenerate)
    (source : BulkL2 period hPeriod) :
    data.gaussianGeneratingFunctional period hPeriod source =
        -data.boundary.triple.lagrangianSourceAction
          (canonicalPhysicalScalarSeparatedCondition
            period a b hNondegenerate)
          data.referenceParameter source
          (data.sourceSolution period hPeriod source) ∧
      0 ≤ data.gaussianGeneratingFunctional period hPeriod source :=
  (data.toRieszResolventData period hPeriod)
    |>.gaussian_certificate period hPeriod source

/-- Complete separated Riesz Program P certificate. -/
theorem finalProgramP_certificate
    {a b : Real} {hNondegenerate : a ≠ 0 ∨ b ≠ 0}
    (data : CanonicalPhysicalScalarIntrinsicWaveRieszSeparatedData
      period hPeriod massSquared a b hNondegenerate)
    (source : BulkL2 period hPeriod) :
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
  ⟨data.actualAdjointDomain_eq period hPeriod,
    data.sourceSolution_equation period hPeriod source,
    (data.sourceSolution_unique_minimizer period hPeriod source).1,
    (data.gaussian_certificate period hPeriod source).2⟩

end CanonicalPhysicalScalarIntrinsicWaveRieszSeparatedData

/-- Dirichlet Riesz endpoint. -/
abbrev CanonicalPhysicalScalarIntrinsicWaveRieszDirichletData
    (massSquared : Real) :=
  CanonicalPhysicalScalarIntrinsicWaveRieszSeparatedData
    period hPeriod massSquared 1 0 (Or.inl one_ne_zero)

/-- Neumann Riesz endpoint. -/
abbrev CanonicalPhysicalScalarIntrinsicWaveRieszNeumannData
    (massSquared : Real) :=
  CanonicalPhysicalScalarIntrinsicWaveRieszSeparatedData
    period hPeriod massSquared 0 1 (Or.inr one_ne_zero)

/-- Constant Robin Riesz endpoint. -/
abbrev CanonicalPhysicalScalarIntrinsicWaveRieszRobinData
    (massSquared coefficient : Real) :=
  CanonicalPhysicalScalarIntrinsicWaveRieszSeparatedData
    period hPeriod massSquared (-coefficient) 1 (Or.inr one_ne_zero)

namespace CanonicalPhysicalScalarIntrinsicWaveRieszSeparatedData

/-- Dirichlet domain is exactly zero Riesz value trace. -/
theorem mem_dirichletDomain_iff
    (data : CanonicalPhysicalScalarIntrinsicWaveRieszDirichletData
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
    (data : CanonicalPhysicalScalarIntrinsicWaveRieszNeumannData
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

/-- Robin domain is exactly `Γ₁ = κ Γ₀` for the Riesz trace. -/
theorem mem_robinDomain_iff
    (coefficient : Real)
    (data : CanonicalPhysicalScalarIntrinsicWaveRieszRobinData
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

end CanonicalPhysicalScalarIntrinsicWaveRieszSeparatedData

/-- Marker theorem for the standard Riesz boundary endpoints. -/
theorem canonicalPhysicalScalarIntrinsicWaveRieszStandardBoundaryProgramPClosure_available : True :=
  trivial

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveRieszStandardBoundaryProgramPClosure4D
end JanusFormal
