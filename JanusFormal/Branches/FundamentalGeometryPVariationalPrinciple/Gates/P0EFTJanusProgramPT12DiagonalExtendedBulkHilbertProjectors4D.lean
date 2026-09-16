import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAExtendedBulkCoreCoordinates4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2CorePairing4D

/-!
# Canonical completed bulk/matter/LL projectors for the diagonal Candidate-A graph

The genuine graph Hilbert space already has four completed factors: diffeomorphism,
Abelian, SpinC matter and LL.  The first two form the existing bulk core block.
This resolves the three completed coordinate blocks; only bulk smooth-core
agreement is proved below. A separate boundary factor and a physical
five-sector refinement of bulk are not asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12DiagonalExtendedBulkHilbertProjectors4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

open scoped InnerProductSpace

variable {D A M L : Type*}
variable [NormedAddCommGroup D] [InnerProductSpace Real D]
variable [NormedAddCommGroup A] [InnerProductSpace Real A]
variable [NormedAddCommGroup M] [InnerProductSpace Real M]
variable [NormedAddCommGroup L] [InnerProductSpace Real L]

private abbrev Tail2 := WithLp 2 (M × L)
private abbrev Tail1 := WithLp 2 (A × Tail2 (M := M) (L := L))
private abbrev Graph := WithLp 2 (D × Tail1 (A := A) (M := M) (L := L))
private abbrev Raw := D × (A × (M × L))

/-- The four genuine graph factors, with the equivalent ordinary product norm. -/
def graphCoordinates : Graph (D := D) (A := A) (M := M) (L := L) ≃L[Real]
    Raw (D := D) (A := A) (M := M) (L := L) :=
  (WithLp.prodContinuousLinearEquiv 2 Real D (Tail1 (A := A) (M := M) (L := L))).trans
    ((ContinuousLinearEquiv.refl Real D).prodCongr
      ((WithLp.prodContinuousLinearEquiv 2 Real A (Tail2 (M := M) (L := L))).trans
        ((ContinuousLinearEquiv.refl Real A).prodCongr
          (WithLp.prodContinuousLinearEquiv 2 Real M L))))

@[simp] theorem graphCoordinates_apply (x : Graph (D := D) (A := A) (M := M) (L := L)) :
    graphCoordinates x = (x.fst, (x.snd.fst, (x.snd.snd.fst, x.snd.snd.snd))) := rfl

private def rawBulk : Raw (D := D) (A := A) (M := M) (L := L) →L[Real]
    Raw (D := D) (A := A) (M := M) (L := L) :=
  (ContinuousLinearMap.fst Real D (A × (M × L))).prod
    (((ContinuousLinearMap.fst Real A (M × L)).comp
      (ContinuousLinearMap.snd Real D (A × (M × L)))).prod 0)

private def rawMatter : Raw (D := D) (A := A) (M := M) (L := L) →L[Real]
    Raw (D := D) (A := A) (M := M) (L := L) :=
  (0 : Raw (D := D) (A := A) (M := M) (L := L) →L[Real] D).prod
    ((0 : Raw (D := D) (A := A) (M := M) (L := L) →L[Real] A).prod
      (((ContinuousLinearMap.fst Real M L).comp
        ((ContinuousLinearMap.snd Real A (M × L)).comp
          (ContinuousLinearMap.snd Real D (A × (M × L))))).prod 0))

private def rawLL : Raw (D := D) (A := A) (M := M) (L := L) →L[Real]
    Raw (D := D) (A := A) (M := M) (L := L) :=
  (0 : Raw (D := D) (A := A) (M := M) (L := L) →L[Real] D).prod
    ((0 : Raw (D := D) (A := A) (M := M) (L := L) →L[Real] A).prod
      ((0 : Raw (D := D) (A := A) (M := M) (L := L) →L[Real] M).prod
        ((ContinuousLinearMap.snd Real M L).comp
          ((ContinuousLinearMap.snd Real A (M × L)).comp
            (ContinuousLinearMap.snd Real D (A × (M × L)))))))

/-- Completed projection onto the existing diffeomorphism–Abelian bulk block. -/
def bulkProjector : Graph (D := D) (A := A) (M := M) (L := L) →L[Real]
    Graph (D := D) (A := A) (M := M) (L := L) :=
  graphCoordinates.symm.toContinuousLinearMap.comp
    (rawBulk.comp graphCoordinates.toContinuousLinearMap)

/-- Completed projection onto the primitive SpinC matter block. -/
def matterProjector : Graph (D := D) (A := A) (M := M) (L := L) →L[Real]
    Graph (D := D) (A := A) (M := M) (L := L) :=
  graphCoordinates.symm.toContinuousLinearMap.comp
    (rawMatter.comp graphCoordinates.toContinuousLinearMap)

/-- Completed projection onto the longitudinal/LL graph block. -/
def llProjector : Graph (D := D) (A := A) (M := M) (L := L) →L[Real]
    Graph (D := D) (A := A) (M := M) (L := L) :=
  graphCoordinates.symm.toContinuousLinearMap.comp
    (rawLL.comp graphCoordinates.toContinuousLinearMap)

theorem projectors_reconstruct (x : Graph (D := D) (A := A) (M := M) (L := L)) :
    bulkProjector x + matterProjector x + llProjector x = x := by
  have hraw (y : Raw (D := D) (A := A) (M := M) (L := L)) :
      rawBulk y + rawMatter y + rawLL y = y := by
    rcases y with ⟨d, a, m, l⟩
    simp [rawBulk, rawMatter, rawLL]
  apply graphCoordinates.injective
  simp only [map_add]
  simp only [bulkProjector, matterProjector, llProjector,
    ContinuousLinearMap.comp_apply]
  exact hraw (graphCoordinates x)

section Physical

open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateAExtendedBulkCoreCoordinates4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Graph4D

attribute [local instance]
  diagonalL2DiffeomorphismNormedAddCommGroup
  diagonalL2DiffeomorphismInnerProductSpace
  diagonalL2AbelianInnerProductSpace
  diagonalL2MatterInnerProductSpace
  diagonalL2LLInnerProductSpace
  diagonalL2ExtendedBulkNormedAddCommGroup
  diagonalL2ExtendedBulkInnerProductSpace

variable (period : Real) (hPeriod : period ≠ 0)

/-- The canonical completed bulk projector on the actual Candidate-A graph Hilbert. -/
def physicalBulkProjector
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod metric
        massSquared data analysis →L[Real]
      GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod metric
        massSquared data analysis :=
  bulkProjector

/-- The three continuous completed projectors resolve the actual graph Hilbert. -/
theorem physical_projectors_reconstruct
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (x : GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod metric
      massSquared data analysis) :
    physicalBulkProjector period hPeriod metric massSquared data analysis x +
        matterProjector x + llProjector x = x :=
  projectors_reconstruct x

/-- On the genuine dense smooth core, the completed bulk projector is exactly
the previously defined bulk core projector. -/
theorem physicalBulkProjector_smoothCore
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (core : P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Graph4D.GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod data analysis) :
    physicalBulkProjector period hPeriod metric massSquared data analysis
        (P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Graph4D.diagonalExtendedBulkL2SmoothEmbedding
          period hPeriod metric massSquared data analysis core) =
      P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Graph4D.diagonalExtendedBulkL2SmoothEmbedding
        period hPeriod metric massSquared data analysis
        (globalCandidateAExtendedBulkCoreBulkProjector period hPeriod
          configuration data analysis core) := by
  rw [P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2CorePairing4D.diagonalExtendedBulkL2SmoothEmbedding_apply]
  conv_rhs => rw [P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2CorePairing4D.diagonalExtendedBulkL2SmoothEmbedding_apply]
  apply graphCoordinates.injective
  simp [physicalBulkProjector, bulkProjector, rawBulk, graphCoordinates_apply,
    globalCandidateAExtendedBulkCoreBulkProjector]
  rfl

end Physical

end
end P0EFTJanusProgramPT12DiagonalExtendedBulkHilbertProjectors4D
end JanusFormal
