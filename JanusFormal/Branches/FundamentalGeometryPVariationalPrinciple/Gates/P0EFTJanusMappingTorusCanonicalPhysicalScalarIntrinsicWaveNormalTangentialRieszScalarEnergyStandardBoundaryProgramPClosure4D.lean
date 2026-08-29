import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergyMinimalProgramPClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalStandardBoundaryResolventClosure4D

/-!
# Standard boundaries for the smallest physical scalar endpoint

Dirichlet, Neumann and constant Robin realizations are specialized directly from
the scalar-energy, normal/tangential Riesz package.

The shifted positive part may take values in any energy space and the Rellich
approximants factor through finite Euclidean coordinate spaces.  No normal trace
regularity, adjoint regularity, arbitrary zeroth-order operator or finite-range
proof is retained.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergyStandardBoundaryProgramPClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology MeasureTheory
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergyPDEClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergyMinimalAnalyticClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergyMinimalProgramPClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalStandardBoundaryResolventClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFiniteCoordinateRellich4D
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleExternalPositiveShiftedForm4D

universe e

variable (period : Real) (hPeriod : period ≠ 0)
variable {Energy : Type e}
  [NormedAddCommGroup Energy] [NormedSpace Real Energy]

private abbrev BoundaryL2 := CanonicalPhysicalScalarFirstSheetL2 period

private abbrev BulkL2 :=
  P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D.CanonicalPhysicalBulkL2
    period hPeriod

/-- Smallest final data for a separated physical boundary condition. -/
structure CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergySeparatedData
    (massSquared a b : Real)
    (hNondegenerate : a ≠ 0 ∨ b ≠ 0)
    (Energy : Type e)
    [NormedAddCommGroup Energy] [NormedSpace Real Energy] where
  boundary : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergyPDEData
    period hPeriod massSquared
  referenceParameter : Real
  shiftedPositiveDecomposition :
    boundary.triple.LagrangianShiftedExternalPositiveDecompositionData
      (canonicalPhysicalScalarSeparatedCondition
        period a b hNondegenerate)
      referenceParameter Energy
  finiteCoordinateRellich : CanonicalPhysicalScalarFiniteCoordinateRellichData
    period hPeriod

namespace CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergySeparatedData

/-- Conversion to the generic smallest analytic endpoint. -/
def toScalarEnergyMinimalAnalyticData
    {a b : Real} {hNondegenerate : a ≠ 0 ∨ b ≠ 0}
    (data : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergySeparatedData
      period hPeriod massSquared a b hNondegenerate Energy) :
    CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergyMinimalAnalyticData
      period hPeriod massSquared Energy where
  boundary := data.boundary
  condition := canonicalPhysicalScalarSeparatedCondition
    period a b hNondegenerate
  referenceParameter := data.referenceParameter
  shiftedPositiveDecomposition := data.shiftedPositiveDecomposition
  finiteCoordinateRellich := data.finiteCoordinateRellich

/-- Membership is exactly the separated Riesz Cauchy constraint. -/
theorem mem_lagrangianDomainSubmodule_iff
    {a b : Real} {hNondegenerate : a ≠ 0 ∨ b ≠ 0}
    (data : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergySeparatedData
      period hPeriod massSquared a b hNondegenerate Energy)
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
    (data : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergySeparatedData
      period hPeriod massSquared a b hNondegenerate Energy) :
    data.boundary.triple.actualAdjointDomain
        (canonicalPhysicalScalarSeparatedCondition
          period a b hNondegenerate) =
      data.boundary.triple.realizationDomain
        (canonicalPhysicalScalarSeparatedCondition
          period a b hNondegenerate) :=
  (data.toScalarEnergyMinimalAnalyticData period hPeriod)
    |>.actualAdjointDomain_eq period hPeriod

/-- Compact reference resolvent. -/
noncomputable def compactResolvent
    {a b : Real} {hNondegenerate : a ≠ 0 ∨ b ≠ 0}
    (data : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergySeparatedData
      period hPeriod massSquared a b hNondegenerate Energy) :=
  (data.toScalarEnergyMinimalAnalyticData period hPeriod)
    |>.compactResolvent period hPeriod

/-- Classical source solution. -/
noncomputable def sourceSolution
    {a b : Real} {hNondegenerate : a ≠ 0 ∨ b ≠ 0}
    (data : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergySeparatedData
      period hPeriod massSquared a b hNondegenerate Energy) :
    BulkL2 period hPeriod →L[Real]
      data.boundary.triple.lagrangianDomainSubmodule
        (canonicalPhysicalScalarSeparatedCondition
          period a b hNondegenerate) :=
  (data.toScalarEnergyMinimalAnalyticData period hPeriod)
    |>.sourceSolution period hPeriod

/-- Strong shifted source equation. -/
theorem sourceSolution_equation
    {a b : Real} {hNondegenerate : a ≠ 0 ∨ b ≠ 0}
    (data : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergySeparatedData
      period hPeriod massSquared a b hNondegenerate Energy)
    (source : BulkL2 period hPeriod) :
    data.boundary.triple.lagrangianShiftedOperator
        (canonicalPhysicalScalarSeparatedCondition
          period a b hNondegenerate)
        data.referenceParameter
        (data.sourceSolution period hPeriod source) = source :=
  (data.toScalarEnergyMinimalAnalyticData period hPeriod)
    |>.sourceSolution_equation period hPeriod source

/-- Unique global minimizer. -/
theorem sourceSolution_unique_minimizer
    {a b : Real} {hNondegenerate : a ≠ 0 ∨ b ≠ 0}
    (data : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergySeparatedData
      period hPeriod massSquared a b hNondegenerate Energy)
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
  (data.toScalarEnergyMinimalAnalyticData period hPeriod)
    |>.sourceSolution_unique_minimizer period hPeriod source

/-- Gaussian generating functional. -/
def gaussianGeneratingFunctional
    {a b : Real} {hNondegenerate : a ≠ 0 ∨ b ≠ 0}
    (data : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergySeparatedData
      period hPeriod massSquared a b hNondegenerate Energy)
    (source : BulkL2 period hPeriod) : Real :=
  (data.toScalarEnergyMinimalAnalyticData period hPeriod)
    |>.gaussianGeneratingFunctional period hPeriod source

/-- On-shell Gaussian identity and positivity. -/
theorem gaussian_certificate
    {a b : Real} {hNondegenerate : a ≠ 0 ∨ b ≠ 0}
    (data : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergySeparatedData
      period hPeriod massSquared a b hNondegenerate Energy)
    (source : BulkL2 period hPeriod) :
    data.gaussianGeneratingFunctional period hPeriod source =
        -data.boundary.triple.lagrangianSourceAction
          (canonicalPhysicalScalarSeparatedCondition
            period a b hNondegenerate)
          data.referenceParameter source
          (data.sourceSolution period hPeriod source) ∧
      0 ≤ data.gaussianGeneratingFunctional period hPeriod source :=
  (data.toScalarEnergyMinimalAnalyticData period hPeriod)
    |>.gaussian_certificate period hPeriod source

/-- Complete separated smallest-endpoint certificate. -/
theorem finalProgramP_certificate
    {a b : Real} {hNondegenerate : a ≠ 0 ∨ b ≠ 0}
    (data : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergySeparatedData
      period hPeriod massSquared a b hNondegenerate Energy)
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

end CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergySeparatedData

/-- Dirichlet endpoint. -/
abbrev CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergyDirichletData
    (massSquared : Real) (Energy : Type e)
    [NormedAddCommGroup Energy] [NormedSpace Real Energy] :=
  CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergySeparatedData
    period hPeriod massSquared 1 0 (Or.inl one_ne_zero) Energy

/-- Neumann endpoint. -/
abbrev CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergyNeumannData
    (massSquared : Real) (Energy : Type e)
    [NormedAddCommGroup Energy] [NormedSpace Real Energy] :=
  CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergySeparatedData
    period hPeriod massSquared 0 1 (Or.inr one_ne_zero) Energy

/-- Constant Robin endpoint. -/
abbrev CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergyRobinData
    (massSquared coefficient : Real) (Energy : Type e)
    [NormedAddCommGroup Energy] [NormedSpace Real Energy] :=
  CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergySeparatedData
    period hPeriod massSquared (-coefficient) 1 (Or.inr one_ne_zero) Energy

namespace CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergySeparatedData

/-- Dirichlet domain is zero completed value trace. -/
theorem mem_dirichletDomain_iff
    (data : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergyDirichletData
      period hPeriod massSquared Energy)
    (field : data.boundary.triple.MaximalDomain) :
    field ∈ data.boundary.triple.lagrangianDomainSubmodule
        (canonicalPhysicalScalarDirichletCondition period) ↔
      (data.boundary.completedBoundaryTrace field).1 = 0 := by
  change data.boundary.completedBoundaryTrace field ∈
      canonicalScalarHilbertDirichletBoundarySubmodule
        (Trace := BoundaryL2 period) ↔ _
  exact mem_canonicalScalarHilbertDirichletBoundarySubmodule
    (Trace := BoundaryL2 period) _

/-- Neumann domain is zero completed normal trace. -/
theorem mem_neumannDomain_iff
    (data : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergyNeumannData
      period hPeriod massSquared Energy)
    (field : data.boundary.triple.MaximalDomain) :
    field ∈ data.boundary.triple.lagrangianDomainSubmodule
        (canonicalPhysicalScalarNeumannCondition period) ↔
      (data.boundary.completedBoundaryTrace field).2 = 0 := by
  change data.boundary.completedBoundaryTrace field ∈
      canonicalScalarHilbertNeumannBoundarySubmodule
        (Trace := BoundaryL2 period) ↔ _
  exact mem_canonicalScalarHilbertNeumannBoundarySubmodule
    (Trace := BoundaryL2 period) _

/-- Robin domain is `Γ₁ = κ Γ₀`. -/
theorem mem_robinDomain_iff
    (coefficient : Real)
    (data : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergyRobinData
      period hPeriod massSquared coefficient Energy)
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

end CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergySeparatedData

/-- Marker for standard smallest-endpoint boundary families. -/
theorem canonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergyStandardBoundaryProgramPClosure_available : True :=
  trivial

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergyStandardBoundaryProgramPClosure4D
end JanusFormal
