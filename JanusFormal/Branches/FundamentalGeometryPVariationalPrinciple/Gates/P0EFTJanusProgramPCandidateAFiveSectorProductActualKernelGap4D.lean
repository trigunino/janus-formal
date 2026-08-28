import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCandidateAFiveSectorProductOffDiagonalGarding4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteSectorPhysicalSmallnessGarding4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPQuadraticGardingActualKernelGap4D

/-!
# Actual-kernel gap from one five-factor complement decomposition

This file sends the literal orthogonal five-factor decomposition all the way to
H12.  The decomposition is imposed on the actual orthogonal kernel complement,
not on the full Hilbert space, so nonzero Noether zero modes remain compatible
with strict coercivity.

Input:

* finite-dimensionality of the actual kernel;
* one five-factor orthogonal coordinate decomposition of `(ker H)ᗮ`;
* five diagonal principal estimates;
* one off-diagonal principal norm comparison;
* one bounded physical quadratic perturbation smaller than the principal
  margin;
* the standard energy upper bound by `‖x‖ ‖H_red x‖`.

Output: the genuine `SelfAdjointKernelComplementGapData` packet used by H12.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPCandidateAFiveSectorProductActualKernelGap4D

set_option autoImplicit false
set_option maxHeartbeats 5200000
set_option synthInstance.maxHeartbeats 2600000

noncomputable section

open scoped InnerProductSpace
open P0EFTJanusProgramPCandidateAFiveSectorProductOffDiagonalGarding4D
open P0EFTJanusProgramPFiniteSectorPhysicalSmallnessGarding4D
open P0EFTJanusProgramPQuadraticGardingOperatorLowerBound4D
open P0EFTJanusProgramPQuadraticGardingActualKernelGap4D
open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D
open P0EFTJanusProgramPCandidateAZeroModeSector4D
open P0EFTJanusProgramPGlobalCandidateANamedZeroModeSectors4D

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- Five-factor Gårding data directly on the actual kernel complement. -/
structure CandidateAFiveSectorProductActualKernelGapData
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (Metric Abelian Matter Longitudinal Boundary : Type*)
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary] where
  kernel_finite : FiniteDimensional Real operator.ker
  principal : CandidateAFiveSectorProductOffDiagonalGardingData
    (E := SelfAdjointKernelComplement operator)
    (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
    (Longitudinal := Longitudinal) (Boundary := Boundary)
  physicalEnergy : SelfAdjointKernelComplement operator → Real
  physicalConstant : Real
  physicalConstant_nonneg : 0 ≤ physicalConstant
  physical_bound : ∀ vector,
    |physicalEnergy vector| ≤ physicalConstant * ‖vector‖ ^ 2
  physical_small : physicalConstant < principal.margin
  totalEnergy : SelfAdjointKernelComplement operator → Real
  total_eq : ∀ vector,
    totalEnergy vector = principal.principalForm vector vector + physicalEnergy vector
  energy_upper : ∀ vector,
    totalEnergy vector ≤ ‖vector‖ *
      ‖selfAdjointKernelComplementOperator operator hSelfAdjoint vector‖

namespace CandidateAFiveSectorProductActualKernelGapData

/-- Finite-sector physical-smallness packet on the true kernel complement. -/
def toPhysicalSmallness
    {operator : E →L[Real] E}
    {hSelfAdjoint : IsSelfAdjoint operator}
    {Metric Abelian Matter Longitudinal Boundary : Type*}
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    (data : CandidateAFiveSectorProductActualKernelGapData operator hSelfAdjoint
      Metric Abelian Matter Longitudinal Boundary) :
    FiniteSectorPhysicalSmallnessGardingData
      (Sector := CandidateAZeroModeSector)
      (E := SelfAdjointKernelComplement operator) where
  principal := data.principal.toFiniteSectorGarding
  physicalEnergy := data.physicalEnergy
  physicalConstant := data.physicalConstant
  physicalConstant_nonneg := data.physicalConstant_nonneg
  physical_bound := data.physical_bound
  physical_small := data.physical_small
  totalEnergy := data.totalEnergy
  total_eq := data.total_eq

/-- Operator lower-bound packet on the true complement. -/
def toQuadraticOperatorData
    {operator : E →L[Real] E}
    {hSelfAdjoint : IsSelfAdjoint operator}
    {Metric Abelian Matter Longitudinal Boundary : Type*}
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    (data : CandidateAFiveSectorProductActualKernelGapData operator hSelfAdjoint
      Metric Abelian Matter Longitudinal Boundary) :
    QuadraticGardingOperatorData
      (selfAdjointKernelComplementOperator operator hSelfAdjoint) where
  margin := data.toPhysicalSmallness.margin
  margin_pos := data.toPhysicalSmallness.margin_pos
  energy := data.totalEnergy
  energy_lower := data.toPhysicalSmallness.margin_norm_sq_le_totalEnergy
  energy_upper := data.energy_upper

/-- Genuine H12 actual-kernel gap. -/
def toGapData
    {operator : E →L[Real] E}
    {hSelfAdjoint : IsSelfAdjoint operator}
    {Metric Abelian Matter Longitudinal Boundary : Type*}
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    (data : CandidateAFiveSectorProductActualKernelGapData operator hSelfAdjoint
      Metric Abelian Matter Longitudinal Boundary) :
    SelfAdjointKernelComplementGapData operator hSelfAdjoint :=
  ({ kernel_finite := data.kernel_finite
     complementGarding := data.toQuadraticOperatorData } :
    QuadraticGardingActualKernelGapData operator hSelfAdjoint).toGapData

/-- Public five-factor actual-kernel gap checkpoint. -/
def candidateA_five_sector_product_actual_kernel_gap_gate
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    {Metric Abelian Matter Longitudinal Boundary : Type*}
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    (data : CandidateAFiveSectorProductActualKernelGapData operator hSelfAdjoint
      Metric Abelian Matter Longitudinal Boundary) :
    SelfAdjointKernelComplementGapData operator hSelfAdjoint :=
  data.toGapData

end CandidateAFiveSectorProductActualKernelGapData

end
end P0EFTJanusProgramPCandidateAFiveSectorProductActualKernelGap4D
end JanusFormal
