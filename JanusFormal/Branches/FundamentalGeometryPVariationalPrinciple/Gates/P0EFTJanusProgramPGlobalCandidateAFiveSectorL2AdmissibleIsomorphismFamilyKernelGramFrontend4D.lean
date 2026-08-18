import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAFiveSectorCompletionCoordinates4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiveSectorL2OrthogonalProductCoordinatesBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiveSectorL2AdmissibleIsomorphismFamilyKernelGramGlobalBridge4D

/-!
# Candidate-A D11 family Gram frontend

An explicitly supplied orthogonal resolution of the Candidate-A completion,
identified with its five-sector coordinates, provides the genuine L² coordinates
and projector comparison required by the global D11 kernel-Gram bridge.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAFiveSectorL2AdmissibleIsomorphismFamilyKernelGramFrontend4D

set_option autoImplicit false
noncomputable section

open Set
open scoped InnerProductSpace
open P0EFTJanusSpinCImmersionCategory
open P0EFTJanusNaturalEllipticFamilyExistence
open P0EFTJanusProgramPNaturalEllipticOperatorRepresentation4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateAFiveSectorCompletionCoordinates4D
open P0EFTJanusProgramPFiveSectorHilbertCoordinates4D
open P0EFTJanusProgramPFiveSectorOrthogonalProductResolution4D
open P0EFTJanusProgramPFiveSectorL2HilbertCoordinates4D
open P0EFTJanusProgramPFiveSectorNaturalRepresentationRefinement4D
open P0EFTJanusProgramPFiveSectorNaturalRepresentationPullback4D
open P0EFTJanusProgramPFiveSectorL2NaturalRepresentationPullbackBridge4D
open P0EFTJanusProgramPFiveSectorL2OrthogonalProductCoordinatesBridge4D
open P0EFTJanusProgramPLinearNaturalRepresentationAdmissibleIsomorphismFamily4D
open P0EFTJanusProgramPFiveSectorL2AdmissibleFrameKernelGramBridge4D
open P0EFTJanusProgramPFiveSectorL2AdmissibleFrameKernelGramGlobalBridge4D
open P0EFTJanusProgramPFiveSectorL2AdmissibleFrameKernelGramGlobalBridge4D.FiveSectorL2AdmissibleFrameKernelGramData
open P0EFTJanusProgramPFiveSectorL2AdmissibleIsomorphismFamilyKernelGramGlobalBridge4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev CandidateAHilbert
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :=
  GlobalCandidateAFiveSectorCompletionHilbert4D period hPeriod configuration
    data analysis

local instance (priority := 30000) candidateAHilbertNormedAddCommGroup
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedAddCommGroup
      (CandidateAHilbert period hPeriod configuration data analysis) :=
  diagonalL2ExtendedBulkNormedAddCommGroup period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis

local instance (priority := 30000) candidateAHilbertInnerProductSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    InnerProductSpace Real
      (CandidateAHilbert period hPeriod configuration data analysis) :=
  diagonalL2ExtendedBulkInnerProductSpace period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis

local instance (priority := 30000) candidateAHilbertNormedSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedSpace Real
      (CandidateAHilbert period hPeriod configuration data analysis) :=
  diagonalL2ExtendedBulkNormedSpace period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis

local instance (priority := 30000) candidateAHilbertModule
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    Module Real
      (CandidateAHilbert period hPeriod configuration data analysis) :=
  diagonalL2ExtendedBulkModule period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis

/-- Candidate-A completion data packaged for the global D11 Gram bridge. -/
def globalCandidateAFiveSectorIsomorphismFamilyKernelGramData
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    {Metric Abelian Matter Longitudinal Boundary Index : Type*}
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    [Fintype Index] [DecidableEq Index]
    {immersionCategory : SpinCImmersionCategory}
    {family : NaturalEllipticOperatorFamily immersionCategory}
    {operator : Real →
      CandidateAHilbert period hPeriod configuration data analysis →L[Real]
        CandidateAHilbert period hPeriod configuration data analysis}
    (sectorData : GlobalCandidateAFiveSectorCompletionCoordinates4D period
      hPeriod configuration data analysis Metric Abelian Matter Longitudinal
        Boundary)
    (resolution : FiveSectorOrthogonalProductDecomposition
      (E := CandidateAHilbert period hPeriod configuration data analysis)
      (MetricDiffeomorphism := Metric) (AbelianGauge := Abelian)
      (PrimitiveSpinCMatter := Matter) (LongitudinalLL := Longitudinal)
      (BoundaryFiniteBV := Boundary))
    (decomposition_eq : resolution.decomposition =
      sectorData.coordinates.decomposition.toContinuousLinearEquiv)
    (representation : NaturalEllipticOperatorRepresentationData
      immersionCategory family (fun parameter state => operator parameter state))
    (refinement : FiveSectorNaturalRepresentationRefinementData
      representation sectorData.coordinates)
    (pullback : FiveSectorNaturalRepresentationPullbackData
      representation sectorData.coordinates refinement)
    (isomorphisms : LinearNaturalRepresentationAdmissibleIsomorphismFamilyData
      representation sectorData.coordinates refinement pullback)
    (baseKernelBasis : Module.Basis Index Real (operator 0).ker) :
    FiveSectorL2AdmissibleFrameKernelGramData
      (Index := Index) representation sectorData.coordinates refinement pullback :=
  admissibleIsomorphismFamilyKernelGramData representation
    sectorData.coordinates refinement pullback
      (fiveSectorL2HilbertCoordinatesOfOrthogonalProduct resolution)
      (fun sector => fiveSectorLegacyProjector_eq_l2OfOrthogonalProduct
        sectorData.coordinates resolution decomposition_eq sector)
      isomorphisms baseKernelBasis

/-- Candidate-A terminal checkpoint: every transported Gram map is injective
and its regular set is the whole parameter line. -/
theorem global_candidateA_five_sector_isomorphism_family_kernel_gram_gate
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    {Metric Abelian Matter Longitudinal Boundary Index : Type*}
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    [Fintype Index] [DecidableEq Index]
    {immersionCategory : SpinCImmersionCategory}
    {family : NaturalEllipticOperatorFamily immersionCategory}
    {operator : Real →
      CandidateAHilbert period hPeriod configuration data analysis →L[Real]
        CandidateAHilbert period hPeriod configuration data analysis}
    (sectorData : GlobalCandidateAFiveSectorCompletionCoordinates4D period
      hPeriod configuration data analysis Metric Abelian Matter Longitudinal
        Boundary)
    (resolution : FiveSectorOrthogonalProductDecomposition
      (E := CandidateAHilbert period hPeriod configuration data analysis)
      (MetricDiffeomorphism := Metric) (AbelianGauge := Abelian)
      (PrimitiveSpinCMatter := Matter) (LongitudinalLL := Longitudinal)
      (BoundaryFiniteBV := Boundary))
    (decomposition_eq : resolution.decomposition =
      sectorData.coordinates.decomposition.toContinuousLinearEquiv)
    (representation : NaturalEllipticOperatorRepresentationData
      immersionCategory family (fun parameter state => operator parameter state))
    (refinement : FiveSectorNaturalRepresentationRefinementData
      representation sectorData.coordinates)
    (pullback : FiveSectorNaturalRepresentationPullbackData
      representation sectorData.coordinates refinement)
    (isomorphisms : LinearNaturalRepresentationAdmissibleIsomorphismFamilyData
      representation sectorData.coordinates refinement pullback)
    (baseKernelBasis : Module.Basis Index Real (operator 0).ker) :
    let gramData := globalCandidateAFiveSectorIsomorphismFamilyKernelGramData
      period hPeriod configuration data analysis sectorData resolution
        decomposition_eq representation refinement pullback isomorphisms
          baseKernelBasis
    (∀ parameter,
      Function.Injective
        (transportedKernelGramMap representation sectorData.coordinates
          refinement pullback gramData parameter)) ∧
    transportedKernelGramRegularSet representation sectorData.coordinates
      refinement pullback gramData = Set.univ := by
  simpa only [globalCandidateAFiveSectorIsomorphismFamilyKernelGramData] using
    five_sector_l2_admissible_isomorphism_family_global_gram_gate
      representation sectorData.coordinates refinement pullback
        (fiveSectorL2HilbertCoordinatesOfOrthogonalProduct resolution)
        (fun sector => fiveSectorLegacyProjector_eq_l2OfOrthogonalProduct
          sectorData.coordinates resolution decomposition_eq sector)
        isomorphisms baseKernelBasis

end
end P0EFTJanusProgramPGlobalCandidateAFiveSectorL2AdmissibleIsomorphismFamilyKernelGramFrontend4D
end JanusFormal
