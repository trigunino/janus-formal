import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FourSectorOffDiagonalOperatorNorm4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiagonalFourSectorRieszCommutation4D

/-! The diagonal Candidate-A Riesz operator contributes no four-sector
off-diagonal term; the augmented remainder is entirely physical. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12FullPhysicalOffDiagonalOperatorNorm4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

open scoped BigOperators InnerProductSpace
open P0EFTJanusProgramPFiniteSelfAdjointProjectionResolution4D
open P0EFTJanusProgramPT12DiagonalExtendedFourSectorSelfAdjointResolution4D
open P0EFTJanusProgramPT12FourSectorOffDiagonalOperatorNorm4D

variable {Sector E : Type*} [Fintype Sector] [DecidableEq Sector]
  [NormedAddCommGroup E] [InnerProductSpace Real E]

/-- A commuting operator has no off-diagonal blocks. -/
theorem diagonalCompression_eq_of_commutes
    (resolution : FiniteSelfAdjointProjectionResolutionData
      (Sector := Sector) (E := E)) (D : E →L[Real] E)
    (hComm : ∀ s x,
      D (resolution.projection s x) = resolution.projection s (D x)) :
    diagonalCompression resolution D = D := by
  ext x
  simp only [diagonalCompression, sum_apply, ContinuousLinearMap.comp_apply]
  calc
    (∑ s : Sector, resolution.projection s
        (D (resolution.projection s x))) =
      ∑ s : Sector, resolution.projection s
        (resolution.projection s (D x)) := by
          apply Finset.sum_congr rfl
          intro s _
          rw [hComm s x]
    _ = ∑ s : Sector, resolution.projection s (D x) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [resolution.projection_idempotent s (D x)]
    _ = D x := resolution.sum_projection (D x)

/-- Compression is additive. -/
theorem diagonalCompression_add
    (resolution : FiniteSelfAdjointProjectionResolutionData
      (Sector := Sector) (E := E)) (D F : E →L[Real] E) :
    diagonalCompression resolution (D + F) =
      diagonalCompression resolution D + diagonalCompression resolution F := by
  ext x
  simp only [diagonalCompression, sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply, map_add, Finset.sum_add_distrib]

/-- Removing diagonal blocks from a commuting reference plus a perturbation
is exactly the off-diagonal part of the perturbation. -/
theorem offDiagonal_add_commuting
    (resolution : FiniteSelfAdjointProjectionResolutionData
      (Sector := Sector) (E := E)) (D F : E →L[Real] E)
    (hComm : ∀ s x,
      D (resolution.projection s x) = resolution.projection s (D x)) :
    (D + F) - diagonalCompression resolution (D + F) =
      F - diagonalCompression resolution F := by
  rw [diagonalCompression_add,
    diagonalCompression_eq_of_commutes resolution D hComm]
  abel

section Physical

open Set Topology MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateAFaithfulFredholmSum4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D
open P0EFTJanusProgramPGlobalCandidateACanonicalStablePerturbation4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBoundedExtension4D
open P0EFTJanusProgramPT12ActualPhysicalRieszCoreBound4D
open P0EFTJanusProgramPT12DiagonalFourSectorRieszCommutation4D

attribute [local instance]
  actualKernelNormedAddCommGroup
  actualKernelInnerProductSpace
  actualKernelNormedSpace
  actualKernelModule
  actualKernelCompleteSpace
  diagonalL2DiffeomorphismNormedAddCommGroup
  diagonalL2DiffeomorphismInnerProductSpace
  diagonalL2AbelianInnerProductSpace
  diagonalL2MatterInnerProductSpace
  diagonalL2LLInnerProductSpace
  diagonalL2ExtendedBulkNormedAddCommGroup
  diagonalL2ExtendedBulkInnerProductSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- The diagonal Riesz operator on the same four-factor graph as the
physical Riesz operator. -/
def diagonalRieszOnFourGraph
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis →L[Real]
    GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis := by
  exact globalCandidateACanonicalStableReferenceOperator period hPeriod
    configuration data analysis

/-- All four canonical projectors commute with the diagonal Riesz operator. -/
theorem diagonalRiesz_commutes_fourSector
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (s : FourSectorSlot)
    (x : GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis) :
    diagonalRieszOnFourGraph period hPeriod configuration data analysis
        (sectorProjector s x) =
      sectorProjector s
        (diagonalRieszOnFourGraph period hPeriod configuration data analysis x) := by
  have h := diagonalExtendedBulkL2RieszOperator_four_projectors_commute
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis x
  cases s with
  | diffeomorphism => simpa [diagonalRieszOnFourGraph, sectorProjector,
      globalCandidateACanonicalStableReferenceOperator] using h.1
  | abelian => simpa [diagonalRieszOnFourGraph, sectorProjector,
      globalCandidateACanonicalStableReferenceOperator] using h.2.1
  | matter => simpa [diagonalRieszOnFourGraph, sectorProjector,
      globalCandidateACanonicalStableReferenceOperator] using h.2.2.1
  | ll => simpa [diagonalRieszOnFourGraph, sectorProjector,
      globalCandidateACanonicalStableReferenceOperator] using h.2.2.2

/-- The full augmented four-sector off-diagonal norm is bounded by H11. -/
theorem fullPhysicalOffDiagonal_opNorm_le_two_coreConstant
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod configuration data analysis chart)
    (bound : GlobalCandidateASevenPhysicalCoreBound4D period hPeriod
      configuration data analysis chart sameAction) :
    let resolution := fourSectorSelfAdjointResolution
      (D := GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
        period hPeriod (globalCandidateAMetricBySector period hPeriod data))
      (A := GlobalPairedAbelianOffShellGraphHilbert period hPeriod
        (globalCandidateAMetricBySector period hPeriod data))
      (M := ProgramPPrimitiveSpinCMatterL2GraphDomain period hPeriod
        couplings.matterMassSquared)
      (L := GlobalFullLLGraphHilbert period hPeriod data analysis)
    let D := diagonalRieszOnFourGraph period hPeriod configuration data analysis
    let F := physicalRieszOnFourGraph period hPeriod configuration data analysis
      chart sameAction bound
    ‖(D + F) - diagonalCompression resolution (D + F)‖ ≤
      2 * bound.constant := by
  dsimp only
  have hComm (s : FourSectorSlot)
      (x : GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)
        couplings.matterMassSquared data analysis) :
      diagonalRieszOnFourGraph period hPeriod configuration data analysis
        ((fourSectorSelfAdjointResolution
          (D := GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
            period hPeriod (globalCandidateAMetricBySector period hPeriod data))
          (A := GlobalPairedAbelianOffShellGraphHilbert period hPeriod
            (globalCandidateAMetricBySector period hPeriod data))
          (M := ProgramPPrimitiveSpinCMatterL2GraphDomain period hPeriod
            couplings.matterMassSquared)
          (L := GlobalFullLLGraphHilbert period hPeriod data analysis)).projection s x) =
      (fourSectorSelfAdjointResolution
        (D := GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
          period hPeriod (globalCandidateAMetricBySector period hPeriod data))
        (A := GlobalPairedAbelianOffShellGraphHilbert period hPeriod
          (globalCandidateAMetricBySector period hPeriod data))
        (M := ProgramPPrimitiveSpinCMatterL2GraphDomain period hPeriod
          couplings.matterMassSquared)
        (L := GlobalFullLLGraphHilbert period hPeriod data analysis)).projection s
        (diagonalRieszOnFourGraph period hPeriod configuration data analysis x) := by
    exact diagonalRiesz_commutes_fourSector period hPeriod configuration data
      analysis s x
  rw [offDiagonal_add_commuting _ _ _ hComm]
  exact physicalOffDiagonal_opNorm_le_two_coreConstant period hPeriod
    configuration data analysis chart sameAction bound

end Physical

end
end P0EFTJanusProgramPT12FullPhysicalOffDiagonalOperatorNorm4D
end JanusFormal
