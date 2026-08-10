import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCandidateAFiveSectorProductResolutionAdapter4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteCommutingProjectionKernelComplement4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteSectorPhysicalSmallnessGarding4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPQuadraticGardingActualKernelGap4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCandidateAFiveSectorPairwiseGarding4D

/-!
# Actual-kernel gap from one full-space five-sector decomposition commuting with H

The sector geometry should be chosen once on the physical Hilbert space.  This
file combines the previous reductions:

* one orthogonal five-factor decomposition generates the five full-space
  Candidate-A projectors;
* commutation with the actual Hessian makes those projectors preserve both
  `ker H` and `(ker H)ᗮ`;
* the restricted projectors automatically resolve the identity and satisfy
  Pythagoras on the zero-mode complement;
* five diagonal lower bounds plus one complete off-diagonal norm estimate give
  the principal margin there;
* one small physical quadratic perturbation gives the total margin and hence
  the genuine H12 gap.

No second coordinate decomposition on `(ker H)ᗮ` is supplied.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPCandidateAFiveSectorCommutingActualKernelGap4D

set_option autoImplicit false
set_option maxHeartbeats 6200000
set_option synthInstance.maxHeartbeats 3100000
noncomputable section

open scoped BigOperators InnerProductSpace
open P0EFTJanusProgramPFiveSectorOrthogonalProductResolution4D
open P0EFTJanusProgramPCandidateAFiveSectorProductResolutionAdapter4D
open P0EFTJanusProgramPFiniteCommutingProjectionKernelComplement4D
open P0EFTJanusProgramPCandidateAFiveSectorPairwiseGarding4D
open P0EFTJanusProgramPFiniteSectorQuadraticGarding4D
open P0EFTJanusProgramPFiniteSectorPhysicalSmallnessGarding4D
open P0EFTJanusProgramPQuadraticGardingOperatorLowerBound4D
open P0EFTJanusProgramPQuadraticGardingActualKernelGap4D
open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D
open P0EFTJanusProgramPGlobalCandidateANamedZeroModeSectors4D

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [CompleteSpace E]

/-- One full-space sector decomposition, commuting with `H`, plus the irreducible
coercive estimates on the automatically generated kernel-complement sectors. -/
structure CandidateAFiveSectorCommutingActualKernelGapData
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (Metric Abelian Matter Longitudinal Boundary : Type*)
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary] where
  kernel_finite : FiniteDimensional Real operator.ker
  coordinates : FiveSectorOrthogonalProductDecomposition
    (E := E) (MetricDiffeomorphism := Metric) (AbelianGauge := Abelian)
    (PrimitiveSpinCMatter := Matter) (LongitudinalLL := Longitudinal)
    (BoundaryFiniteBV := Boundary)
  commute : ∀ sector vector,
    operator
        ((candidateAFiveSectorSelfAdjointResolutionOfProduct coordinates).projection
          sector vector) =
      (candidateAFiveSectorSelfAdjointResolutionOfProduct coordinates).projection
        sector (operator vector)
  principalForm : SelfAdjointKernelComplement operator →L[Real]
    SelfAdjointKernelComplement operator →L[Real] Real
  principal_symmetric : ∀ first second,
    principalForm first second = principalForm second first
  diagonalConstants : CandidateAFiveSectorDiagonalConstants
  diagonal_lower : ∀ sector vector,
    diagonalConstants.sectorConstant sector *
        ‖((({ resolution :=
              candidateAFiveSectorSelfAdjointResolutionOfProduct coordinates
            commute := commute } :
            FiniteCommutingProjectionResolutionData
              (Sector := CandidateAZeroModeSector) operator)
          ).toKernelComplementResolution).projection sector vector‖ ^ 2 ≤
      principalForm
        (((({ resolution :=
              candidateAFiveSectorSelfAdjointResolutionOfProduct coordinates
            commute := commute } :
            FiniteCommutingProjectionResolutionData
              (Sector := CandidateAZeroModeSector) operator)
          ).toKernelComplementResolution).projection sector vector)
        ((({ resolution :=
              candidateAFiveSectorSelfAdjointResolutionOfProduct coordinates
            commute := commute } :
            FiniteCommutingProjectionResolutionData
              (Sector := CandidateAZeroModeSector) operator)
          ).toKernelComplementResolution).projection sector vector)
  offDiagonal_small :
    ‖principalForm -
      ∑ sector : CandidateAZeroModeSector,
        principalForm.bilinearComp
          ((({ resolution :=
              candidateAFiveSectorSelfAdjointResolutionOfProduct coordinates
            commute := commute } :
            FiniteCommutingProjectionResolutionData
              (Sector := CandidateAZeroModeSector) operator)
          ).toKernelComplementResolution).projection sector)
          ((({ resolution :=
              candidateAFiveSectorSelfAdjointResolutionOfProduct coordinates
            commute := commute } :
            FiniteCommutingProjectionResolutionData
              (Sector := CandidateAZeroModeSector) operator)
          ).toKernelComplementResolution).projection sector)‖ <
      diagonalConstants.sectorFloor
  physicalEnergy : SelfAdjointKernelComplement operator → Real
  physicalConstant : Real
  physicalConstant_nonneg : 0 ≤ physicalConstant
  physical_bound : ∀ vector,
    |physicalEnergy vector| ≤ physicalConstant * ‖vector‖ ^ 2
  physical_small : physicalConstant <
    diagonalConstants.sectorFloor -
      ‖principalForm -
        ∑ sector : CandidateAZeroModeSector,
          principalForm.bilinearComp
            ((({ resolution :=
                candidateAFiveSectorSelfAdjointResolutionOfProduct coordinates
              commute := commute } :
              FiniteCommutingProjectionResolutionData
                (Sector := CandidateAZeroModeSector) operator)
            ).toKernelComplementResolution).projection sector)
            ((({ resolution :=
                candidateAFiveSectorSelfAdjointResolutionOfProduct coordinates
              commute := commute } :
              FiniteCommutingProjectionResolutionData
                (Sector := CandidateAZeroModeSector) operator)
            ).toKernelComplementResolution).projection sector)‖
  totalEnergy : SelfAdjointKernelComplement operator → Real
  total_eq : ∀ vector,
    totalEnergy vector = principalForm vector vector + physicalEnergy vector
  energy_upper : ∀ vector,
    totalEnergy vector ≤ ‖vector‖ *
      ‖selfAdjointKernelComplementOperator operator hSelfAdjoint vector‖

namespace CandidateAFiveSectorCommutingActualKernelGapData

/-- Full-space Candidate-A projection resolution generated by the coordinates. -/
def fullResolution
    {operator : E →L[Real] E}
    {hSelfAdjoint : IsSelfAdjoint operator}
    {Metric Abelian Matter Longitudinal Boundary : Type*}
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    (data : CandidateAFiveSectorCommutingActualKernelGapData operator hSelfAdjoint
      Metric Abelian Matter Longitudinal Boundary) :=
  candidateAFiveSectorSelfAdjointResolutionOfProduct data.coordinates

/-- The same full-space resolution together with commutation. -/
def commutingResolution
    {operator : E →L[Real] E}
    {hSelfAdjoint : IsSelfAdjoint operator}
    {Metric Abelian Matter Longitudinal Boundary : Type*}
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    (data : CandidateAFiveSectorCommutingActualKernelGapData operator hSelfAdjoint
      Metric Abelian Matter Longitudinal Boundary) :
    FiniteCommutingProjectionResolutionData
      (Sector := CandidateAZeroModeSector) operator where
  resolution := data.fullResolution
  commute := data.commute

/-- Automatically restricted resolution on `(ker H)ᗮ`. -/
def reducedResolution
    {operator : E →L[Real] E}
    {hSelfAdjoint : IsSelfAdjoint operator}
    {Metric Abelian Matter Longitudinal Boundary : Type*}
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    (data : CandidateAFiveSectorCommutingActualKernelGapData operator hSelfAdjoint
      Metric Abelian Matter Longitudinal Boundary) :=
  data.commutingResolution.toKernelComplementResolution

/-- Canonical diagonal restriction on the actual complement. -/
def diagonalForm
    {operator : E →L[Real] E}
    {hSelfAdjoint : IsSelfAdjoint operator}
    {Metric Abelian Matter Longitudinal Boundary : Type*}
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    (data : CandidateAFiveSectorCommutingActualKernelGapData operator hSelfAdjoint
      Metric Abelian Matter Longitudinal Boundary) :=
  ∑ sector : CandidateAZeroModeSector,
    data.principalForm.bilinearComp
      (data.reducedResolution.projection sector)
      (data.reducedResolution.projection sector)

/-- Single off-diagonal remainder. -/
def offDiagonalForm
    {operator : E →L[Real] E}
    {hSelfAdjoint : IsSelfAdjoint operator}
    {Metric Abelian Matter Longitudinal Boundary : Type*}
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    (data : CandidateAFiveSectorCommutingActualKernelGapData operator hSelfAdjoint
      Metric Abelian Matter Longitudinal Boundary) :=
  data.principalForm - data.diagonalForm

/-- Principal Gårding generated from the restricted full-space projectors. -/
def principalGarding
    {operator : E →L[Real] E}
    {hSelfAdjoint : IsSelfAdjoint operator}
    {Metric Abelian Matter Longitudinal Boundary : Type*}
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    (data : CandidateAFiveSectorCommutingActualKernelGapData operator hSelfAdjoint
      Metric Abelian Matter Longitudinal Boundary) :
    FiniteSectorQuadraticGardingData
      (Sector := CandidateAZeroModeSector)
      (E := SelfAdjointKernelComplement operator) where
  sectorWeight := fun sector vector => ‖data.reducedResolution.projection sector vector‖ ^ 2
  sectorWeight_nonneg := fun _ _ => sq_nonneg _
  sectorWeight_sum := data.reducedResolution.norm_sq_decomposition
  sectorConstant := data.diagonalConstants.sectorConstant
  sectorConstant_pos := data.diagonalConstants.sectorConstant_pos
  sectorFloor := data.diagonalConstants.sectorFloor
  sectorFloor_pos := data.diagonalConstants.sectorFloor_pos
  sectorFloor_le := data.diagonalConstants.sectorFloor_le
  diagonalEnergy := fun vector => data.diagonalForm vector vector
  diagonal_lower := by
    intro vector
    unfold diagonalForm
    simp only [ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.bilinearComp_apply]
    apply Finset.sum_le_sum
    intro sector _
    exact data.diagonal_lower sector vector
  couplingEnergy := fun vector => data.offDiagonalForm vector vector
  couplingConstant := ‖data.offDiagonalForm‖
  couplingConstant_nonneg := norm_nonneg _
  coupling_bound := by
    intro vector
    calc
      |data.offDiagonalForm vector vector| =
          ‖data.offDiagonalForm vector vector‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖data.offDiagonalForm vector‖ * ‖vector‖ :=
        (data.offDiagonalForm vector).le_opNorm vector
      _ ≤ (‖data.offDiagonalForm‖ * ‖vector‖) * ‖vector‖ :=
        mul_le_mul_of_nonneg_right
          (data.offDiagonalForm.le_opNorm vector) (norm_nonneg vector)
      _ = ‖data.offDiagonalForm‖ * ‖vector‖ ^ 2 := by ring
  coupling_small := by
    simpa [offDiagonalForm, diagonalForm, reducedResolution,
      commutingResolution, fullResolution] using data.offDiagonal_small
  principalEnergy := fun vector => data.principalForm vector vector
  principal_eq := by
    intro vector
    unfold offDiagonalForm
    simp only [ContinuousLinearMap.sub_apply]
    ring

/-- Add the physical H11 perturbation. -/
def totalGarding
    {operator : E →L[Real] E}
    {hSelfAdjoint : IsSelfAdjoint operator}
    {Metric Abelian Matter Longitudinal Boundary : Type*}
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    (data : CandidateAFiveSectorCommutingActualKernelGapData operator hSelfAdjoint
      Metric Abelian Matter Longitudinal Boundary) :
    FiniteSectorPhysicalSmallnessGardingData
      (Sector := CandidateAZeroModeSector)
      (E := SelfAdjointKernelComplement operator) where
  principal := data.principalGarding
  physicalEnergy := data.physicalEnergy
  physicalConstant := data.physicalConstant
  physicalConstant_nonneg := data.physicalConstant_nonneg
  physical_bound := data.physical_bound
  physical_small := by
    simpa [FiniteSectorQuadraticGardingData.margin, principalGarding,
      offDiagonalForm, diagonalForm, reducedResolution, commutingResolution,
      fullResolution] using data.physical_small
  totalEnergy := data.totalEnergy
  total_eq := data.total_eq

/-- Operator lower bound and actual H12 gap. -/
def toGapData
    {operator : E →L[Real] E}
    {hSelfAdjoint : IsSelfAdjoint operator}
    {Metric Abelian Matter Longitudinal Boundary : Type*}
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    (data : CandidateAFiveSectorCommutingActualKernelGapData operator hSelfAdjoint
      Metric Abelian Matter Longitudinal Boundary) :
    SelfAdjointKernelComplementGapData operator hSelfAdjoint :=
  let quadratic : QuadraticGardingOperatorData
      (selfAdjointKernelComplementOperator operator hSelfAdjoint) :=
    { margin := data.totalGarding.margin
      margin_pos := data.totalGarding.margin_pos
      energy := data.totalEnergy
      energy_lower := data.totalGarding.margin_norm_sq_le_totalEnergy
      energy_upper := data.energy_upper }
  ({ kernel_finite := data.kernel_finite
     complementGarding := quadratic } :
    QuadraticGardingActualKernelGapData operator hSelfAdjoint).toGapData

/-- Public checkpoint: one commuting five-sector decomposition on the full
Hilbert space suffices for the H12 complement calculation. -/
theorem candidateA_five_sector_commuting_actual_kernel_gap_gate
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    {Metric Abelian Matter Longitudinal Boundary : Type*}
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    (data : CandidateAFiveSectorCommutingActualKernelGapData operator hSelfAdjoint
      Metric Abelian Matter Longitudinal Boundary) :
    SelfAdjointKernelComplementGapData operator hSelfAdjoint :=
  data.toGapData

end CandidateAFiveSectorCommutingActualKernelGapData

end
end P0EFTJanusProgramPCandidateAFiveSectorCommutingActualKernelGap4D
end JanusFormal
