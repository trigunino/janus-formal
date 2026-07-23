import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalFinalClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalStandardBoundaryResolventClosure4D

/-!
# Standard boundaries for corrected weighted normal transport

Separated, Dirichlet, Neumann and constant Robin realizations are exposed for
the constructive weighted transported-normal endpoint.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalStandardBoundaryFinalClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology MeasureTheory
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalFinalClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalStandardBoundaryResolventClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFiniteCoordinateRellich4D
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleExternalPositiveShiftedForm4D

universe e

variable (period : Real) (hPeriod : period ≠ 0)
variable {massSquared : Real}
variable {Energy : Type e}
  [NormedAddCommGroup Energy] [NormedSpace Real Energy]

private abbrev BoundaryL2 := CanonicalPhysicalScalarFirstSheetL2 period

/-- Preferred weighted endpoint for one separated boundary condition. -/
structure CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalGraphSeparatedFinalData
    (massSquared a b : Real)
    (hNondegenerate : a ≠ 0 ∨ b ≠ 0) where
  geometric :
    P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveWeightedTransportedGlobalGreen4D.CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedGlobalGreenData
      period hPeriod massSquared
  eulerCoefficientOperators :
    geometric.toCanonicalNormalGreenData.toNormalTangentialGreenData.toIntrinsicWaveLocalGreenData.toCanonicalLocalDivergenceData.toCanonicalWaveCauchyJetData.toCanonicalCauchyJetCompatibilityData.toCompatibilityData.toCauchyJetGeometricData.CauchyJetEulerSixCanonicalL2OperatorData
      period hPeriod
  graphEllipticEstimate :
    (geometric.greenCore period hPeriod).GraphEllipticEstimate period hPeriod
  referenceParameter : Real
  shiftedFormCoercive :
    (P0EFTJanusMappingTorusCanonicalPhysicalScalarProgramPFinalObligations4D.assembleCanonicalPhysicalScalarGraphBoundaryData
      period hPeriod
      (geometric.toCanonicalNormalGreenData period hPeriod)
      eulerCoefficientOperators).triple
      |>.LagrangianShiftedFormCoerciveData
        (canonicalPhysicalScalarSeparatedCondition
          period a b hNondegenerate)
        referenceParameter
  finiteCoordinateRellich : CanonicalPhysicalScalarFiniteCoordinateRellichData
    period hPeriod

namespace CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalGraphSeparatedFinalData

/-- Conversion to the preferred generic weighted endpoint. -/
def toFinalData
    {a b : Real} {hNondegenerate : a ≠ 0 ∨ b ≠ 0}
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalGraphSeparatedFinalData
        period hPeriod massSquared a b hNondegenerate) :
    CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalGraphDirectCoerciveFinalData
      period hPeriod massSquared where
  geometric := data.geometric
  eulerCoefficientOperators := data.eulerCoefficientOperators
  graphEllipticEstimate := data.graphEllipticEstimate
  condition := canonicalPhysicalScalarSeparatedCondition
    period a b hNondegenerate
  referenceParameter := data.referenceParameter
  shiftedFormCoercive := data.shiftedFormCoercive
  finiteCoordinateRellich := data.finiteCoordinateRellich

/-- Membership is exactly the separated completed Riesz constraint. -/
theorem mem_lagrangianDomainSubmodule_iff
    {a b : Real} {hNondegenerate : a ≠ 0 ∨ b ≠ 0}
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalGraphSeparatedFinalData
        period hPeriod massSquared a b hNondegenerate)
    (field : data.toFinalData.triple.MaximalDomain) :
    field ∈ data.toFinalData.triple.lagrangianDomainSubmodule
        (canonicalPhysicalScalarSeparatedCondition
          period a b hNondegenerate) ↔
      a • (data.toFinalData.completedBoundaryTrace period hPeriod field).1 +
        b • (data.toFinalData.completedBoundaryTrace period hPeriod field).2 = 0 := by
  change data.toFinalData.completedBoundaryTrace period hPeriod field ∈
      canonicalScalarHilbertSeparatedBoundarySubmodule
        (Trace := BoundaryL2 period) a b ↔ _
  exact mem_canonicalScalarHilbertSeparatedBoundarySubmodule
    (Trace := BoundaryL2 period) a b _

end CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalGraphSeparatedFinalData

/-- Preferred Dirichlet weighted endpoint. -/
abbrev CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalGraphDirichletFinalData
    (massSquared : Real) :=
  CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalGraphSeparatedFinalData
    period hPeriod massSquared 1 0 (Or.inl one_ne_zero)

/-- Preferred Neumann weighted endpoint. -/
abbrev CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalGraphNeumannFinalData
    (massSquared : Real) :=
  CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalGraphSeparatedFinalData
    period hPeriod massSquared 0 1 (Or.inr one_ne_zero)

/-- Preferred constant Robin weighted endpoint. -/
abbrev CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalGraphRobinFinalData
    (massSquared coefficient : Real) :=
  CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalGraphSeparatedFinalData
    period hPeriod massSquared (-coefficient) 1 (Or.inr one_ne_zero)

namespace CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalGraphSeparatedFinalData

/-- Dirichlet domain. -/
theorem mem_dirichletDomain_iff
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalGraphDirichletFinalData
        period hPeriod massSquared)
    (field : data.toFinalData.triple.MaximalDomain) :
    field ∈ data.toFinalData.triple.lagrangianDomainSubmodule
        (canonicalPhysicalScalarDirichletCondition period) ↔
      (data.toFinalData.completedBoundaryTrace period hPeriod field).1 = 0 := by
  change data.toFinalData.completedBoundaryTrace period hPeriod field ∈
      canonicalScalarHilbertDirichletBoundarySubmodule
        (Trace := BoundaryL2 period) ↔ _
  exact mem_canonicalScalarHilbertDirichletBoundarySubmodule
    (Trace := BoundaryL2 period) _

/-- Neumann domain. -/
theorem mem_neumannDomain_iff
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalGraphNeumannFinalData
        period hPeriod massSquared)
    (field : data.toFinalData.triple.MaximalDomain) :
    field ∈ data.toFinalData.triple.lagrangianDomainSubmodule
        (canonicalPhysicalScalarNeumannCondition period) ↔
      (data.toFinalData.completedBoundaryTrace period hPeriod field).2 = 0 := by
  change data.toFinalData.completedBoundaryTrace period hPeriod field ∈
      canonicalScalarHilbertNeumannBoundarySubmodule
        (Trace := BoundaryL2 period) ↔ _
  exact mem_canonicalScalarHilbertNeumannBoundarySubmodule
    (Trace := BoundaryL2 period) _

/-- Constant Robin domain. -/
theorem mem_robinDomain_iff
    (coefficient : Real)
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalGraphRobinFinalData
        period hPeriod massSquared coefficient)
    (field : data.toFinalData.triple.MaximalDomain) :
    field ∈ data.toFinalData.triple.lagrangianDomainSubmodule
        (canonicalPhysicalScalarRobinCondition period coefficient) ↔
      (data.toFinalData.completedBoundaryTrace period hPeriod field).2 =
        coefficient •
          (data.toFinalData.completedBoundaryTrace period hPeriod field).1 := by
  change data.toFinalData.completedBoundaryTrace period hPeriod field ∈
      canonicalScalarHilbertRobinBoundarySubmodule
        (Trace := BoundaryL2 period) coefficient ↔ _
  exact mem_canonicalScalarHilbertRobinBoundarySubmodule
    (Trace := BoundaryL2 period) coefficient _

end CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalGraphSeparatedFinalData

/-- Corrected weighted final data for one separated boundary condition. -/
structure CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalSeparatedFinalData
    (massSquared a b : Real)
    (hNondegenerate : a ≠ 0 ∨ b ≠ 0)
    (Energy : Type e)
    [NormedAddCommGroup Energy] [NormedSpace Real Energy] where
  geometric :
    P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveWeightedTransportedGlobalGreen4D.CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedGlobalGreenData
      period hPeriod massSquared
  energyIdentity :
    (geometric.greenCore period hPeriod).MassCorrectedEnergyIdentityData
      period hPeriod
  eulerCoefficientOperators :
    geometric.toCanonicalNormalGreenData.toNormalTangentialGreenData.toIntrinsicWaveLocalGreenData.toCanonicalLocalDivergenceData.toCanonicalWaveCauchyJetData.toCanonicalCauchyJetCompatibilityData.toCompatibilityData.toCauchyJetGeometricData.CauchyJetEulerSixCanonicalL2OperatorData
      period hPeriod
  referenceParameter : Real
  shiftedPositiveDecomposition :
    (P0EFTJanusMappingTorusCanonicalPhysicalScalarProgramPFinalObligations4D.assembleCanonicalPhysicalScalarBoundaryData
      period hPeriod
      (geometric.toCanonicalNormalGreenData period hPeriod)
      (energyIdentity.toScalarRemainderEnergyIdentityData
        period hPeriod (geometric.greenCore period hPeriod))
      eulerCoefficientOperators).triple
      |>.LagrangianShiftedExternalPositiveDecompositionData
        (canonicalPhysicalScalarSeparatedCondition
          period a b hNondegenerate)
        referenceParameter Energy
  finiteCoordinateRellich : CanonicalPhysicalScalarFiniteCoordinateRellichData
    period hPeriod

namespace CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalSeparatedFinalData

/-- Conversion to the generic corrected weighted endpoint. -/
def toFinalData
    {a b : Real} {hNondegenerate : a ≠ 0 ∨ b ≠ 0}
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalSeparatedFinalData
        period hPeriod massSquared a b hNondegenerate Energy) :
    CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalFinalData
      period hPeriod massSquared Energy where
  geometric := data.geometric
  energyIdentity := data.energyIdentity
  eulerCoefficientOperators := data.eulerCoefficientOperators
  condition := canonicalPhysicalScalarSeparatedCondition
    period a b hNondegenerate
  referenceParameter := data.referenceParameter
  shiftedPositiveDecomposition := data.shiftedPositiveDecomposition
  finiteCoordinateRellich := data.finiteCoordinateRellich

/-- Membership is exactly the separated completed Riesz constraint. -/
theorem mem_lagrangianDomainSubmodule_iff
    {a b : Real} {hNondegenerate : a ≠ 0 ∨ b ≠ 0}
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalSeparatedFinalData
        period hPeriod massSquared a b hNondegenerate Energy)
    (field : data.toFinalData.triple.MaximalDomain) :
    field ∈ data.toFinalData.triple.lagrangianDomainSubmodule
        (canonicalPhysicalScalarSeparatedCondition
          period a b hNondegenerate) ↔
      a • (data.toFinalData.completedBoundaryTrace period hPeriod field).1 +
        b • (data.toFinalData.completedBoundaryTrace period hPeriod field).2 = 0 := by
  change data.toFinalData.completedBoundaryTrace period hPeriod field ∈
      canonicalScalarHilbertSeparatedBoundarySubmodule
        (Trace := BoundaryL2 period) a b ↔ _
  exact mem_canonicalScalarHilbertSeparatedBoundarySubmodule
    (Trace := BoundaryL2 period) a b _

end CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalSeparatedFinalData

/-- Dirichlet corrected weighted endpoint. -/
abbrev CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalDirichletFinalData
    (massSquared : Real) (Energy : Type e)
    [NormedAddCommGroup Energy] [NormedSpace Real Energy] :=
  CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalSeparatedFinalData
    period hPeriod massSquared 1 0 (Or.inl one_ne_zero) Energy

/-- Neumann corrected weighted endpoint. -/
abbrev CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalNeumannFinalData
    (massSquared : Real) (Energy : Type e)
    [NormedAddCommGroup Energy] [NormedSpace Real Energy] :=
  CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalSeparatedFinalData
    period hPeriod massSquared 0 1 (Or.inr one_ne_zero) Energy

/-- Constant Robin corrected weighted endpoint. -/
abbrev CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalRobinFinalData
    (massSquared coefficient : Real) (Energy : Type e)
    [NormedAddCommGroup Energy] [NormedSpace Real Energy] :=
  CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalSeparatedFinalData
    period hPeriod massSquared (-coefficient) 1 (Or.inr one_ne_zero) Energy

namespace CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalSeparatedFinalData

/-- Dirichlet domain. -/
theorem mem_dirichletDomain_iff
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalDirichletFinalData
        period hPeriod massSquared Energy)
    (field : data.toFinalData.triple.MaximalDomain) :
    field ∈ data.toFinalData.triple.lagrangianDomainSubmodule
        (canonicalPhysicalScalarDirichletCondition period) ↔
      (data.toFinalData.completedBoundaryTrace period hPeriod field).1 = 0 := by
  change data.toFinalData.completedBoundaryTrace period hPeriod field ∈
      canonicalScalarHilbertDirichletBoundarySubmodule
        (Trace := BoundaryL2 period) ↔ _
  exact mem_canonicalScalarHilbertDirichletBoundarySubmodule
    (Trace := BoundaryL2 period) _

/-- Neumann domain. -/
theorem mem_neumannDomain_iff
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalNeumannFinalData
        period hPeriod massSquared Energy)
    (field : data.toFinalData.triple.MaximalDomain) :
    field ∈ data.toFinalData.triple.lagrangianDomainSubmodule
        (canonicalPhysicalScalarNeumannCondition period) ↔
      (data.toFinalData.completedBoundaryTrace period hPeriod field).2 = 0 := by
  change data.toFinalData.completedBoundaryTrace period hPeriod field ∈
      canonicalScalarHilbertNeumannBoundarySubmodule
        (Trace := BoundaryL2 period) ↔ _
  exact mem_canonicalScalarHilbertNeumannBoundarySubmodule
    (Trace := BoundaryL2 period) _

/-- Constant Robin domain. -/
theorem mem_robinDomain_iff
    (coefficient : Real)
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalRobinFinalData
        period hPeriod massSquared coefficient Energy)
    (field : data.toFinalData.triple.MaximalDomain) :
    field ∈ data.toFinalData.triple.lagrangianDomainSubmodule
        (canonicalPhysicalScalarRobinCondition period coefficient) ↔
      (data.toFinalData.completedBoundaryTrace period hPeriod field).2 =
        coefficient •
          (data.toFinalData.completedBoundaryTrace period hPeriod field).1 := by
  change data.toFinalData.completedBoundaryTrace period hPeriod field ∈
      canonicalScalarHilbertRobinBoundarySubmodule
        (Trace := BoundaryL2 period) coefficient ↔ _
  exact mem_canonicalScalarHilbertRobinBoundarySubmodule
    (Trace := BoundaryL2 period) coefficient _

end CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalSeparatedFinalData

/-- Marker for the corrected weighted standard-boundary endpoints. -/
theorem canonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalStandardBoundaryFinalClosure_available :
    True :=
  trivial

/-- Marker for the preferred graph/direct-coercive standard boundaries. -/
theorem canonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalGraphStandardBoundaryFinalClosure_available :
    True :=
  trivial

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalStandardBoundaryFinalClosure4D
end JanusFormal
