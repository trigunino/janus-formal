import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAFiveSectorL2AdmissibleIsomorphismFamilyKernelGramFrontend4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiveSectorL2AdmissibleFrameDifferentiableKernelBasisFamilyGlobalBridge4D

/-!
# Candidate-A D11 true-kernel family frontend

The concrete Candidate-A D11 Gram data determines a complete basis of every
true kernel, the standard finite kernel-family packet and, under vectorwise C1
control of the represented frame, its differentiable refinement.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAFiveSectorL2AdmissibleIsomorphismFamilyTrueKernelFrontend4D

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
open P0EFTJanusProgramPFiveSectorNaturalRepresentationRefinement4D
open P0EFTJanusProgramPFiveSectorNaturalRepresentationPullback4D
open P0EFTJanusProgramPLinearNaturalRepresentationAdmissibleIsomorphismFamily4D
open P0EFTJanusProgramPFiniteKernelBasisFamily4D
open P0EFTJanusProgramPDifferentiableFiniteKernelBasisFamily4D
open P0EFTJanusProgramPFiveSectorL2AdmissibleFrameKernelGramGlobalBridge4D
open P0EFTJanusProgramPFiveSectorL2AdmissibleFrameKernelGramGlobalBridge4D.FiveSectorL2AdmissibleFrameKernelGramData
open P0EFTJanusProgramPFiveSectorL2AdmissibleFrameTrueKernelBasisGlobalBridge4D
open P0EFTJanusProgramPFiveSectorL2AdmissibleFrameTrueKernelBasisGlobalBridge4D.FiveSectorL2AdmissibleFrameKernelGramData
open P0EFTJanusProgramPFiveSectorL2AdmissibleFrameDifferentiableKernelBasisFamilyGlobalBridge4D
open P0EFTJanusProgramPFiveSectorL2AdmissibleFrameDifferentiableKernelBasisFamilyGlobalBridge4D.FiveSectorL2AdmissibleFrameKernelGramData
open P0EFTJanusProgramPGlobalCandidateAFiveSectorL2AdmissibleIsomorphismFamilyKernelGramFrontend4D

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

variable
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    {Metric Abelian Matter Longitudinal Boundary : Type*}
    {Index : Type}
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
    (baseKernelBasis : Module.Basis Index Real (operator 0).ker)

/-- Complete Candidate-A true-kernel basis at one parameter. -/
def globalCandidateAFiveSectorTrueKernelBasis (parameter : Real) :
    Module.Basis Index Real (operator parameter).ker :=
  let gramData := globalCandidateAFiveSectorIsomorphismFamilyKernelGramData
    period hPeriod configuration data analysis sectorData resolution
      decomposition_eq representation refinement pullback isomorphisms
        baseKernelBasis
  transportedTrueKernelBasis representation sectorData.coordinates refinement
    pullback gramData parameter

/-- Standard fixed-label family of all Candidate-A true kernels. -/
def globalCandidateAFiveSectorFiniteKernelBasisFamilyData :
    FiniteKernelBasisFamilyData operator Index :=
  let gramData := globalCandidateAFiveSectorIsomorphismFamilyKernelGramData
    period hPeriod configuration data analysis sectorData resolution
      decomposition_eq representation refinement pullback isomorphisms
        baseKernelBasis
  toFiniteKernelBasisFamilyData representation sectorData.coordinates refinement
    pullback gramData

/-- Candidate-A true-kernel completeness, constant finite rank and global Gram
regularity, all induced by the same D11 transported basis. -/
theorem global_candidateA_five_sector_true_kernel_family_gate :
    let gramData := globalCandidateAFiveSectorIsomorphismFamilyKernelGramData
      period hPeriod configuration data analysis sectorData resolution
        decomposition_eq representation refinement pullback isomorphisms
          baseKernelBasis
    let kernels := globalCandidateAFiveSectorFiniteKernelBasisFamilyData
      period hPeriod configuration data analysis sectorData resolution
        decomposition_eq representation refinement pullback isomorphisms
          baseKernelBasis
    (∀ parameter,
      kernels.basis parameter =
        transportedTrueKernelBasis representation sectorData.coordinates
          refinement pullback gramData parameter) ∧
    (∀ parameter,
      Submodule.span Real
          (Set.range
            (gramData.transportedKernelVector representation
              sectorData.coordinates refinement pullback parameter)) = ⊤) ∧
    transportedKernelGramRegularSet representation sectorData.coordinates
        refinement pullback gramData = Set.univ ∧
    (∀ parameter,
      Module.finrank Real (operator parameter).ker = Fintype.card Index) := by
  dsimp only
  let gramData := globalCandidateAFiveSectorIsomorphismFamilyKernelGramData
    period hPeriod configuration data analysis sectorData resolution
      decomposition_eq representation refinement pullback isomorphisms
        baseKernelBasis
  have hTrue := five_sector_l2_admissible_frame_true_kernel_global_gate
    representation sectorData.coordinates refinement pullback gramData
  have hFinite := five_sector_l2_admissible_frame_finite_kernel_basis_family_gate
    representation sectorData.coordinates refinement pullback gramData
  refine ⟨?_, hTrue.1, hTrue.2, hFinite.2.2.2⟩
  intro parameter
  rfl

/-- Exact vectorwise C1 premise needed to upgrade the Candidate-A D11 basis. -/
def GlobalCandidateAFiveSectorOperatorFrameVectorDifferentiable : Prop :=
  let gramData := globalCandidateAFiveSectorIsomorphismFamilyKernelGramData
    period hPeriod configuration data analysis sectorData resolution
      decomposition_eq representation refinement pullback isomorphisms
        baseKernelBasis
  ∀ index,
    Differentiable Real
      (fun parameter : Real =>
        (gramData.operatorFrame representation sectorData.coordinates refinement
          pullback).frame parameter (gramData.baseKernelBasis index).1)

/-- The exact C1 field already carried by the concrete preferred D11 family
plugs into the Gram-frame predicate without any additional regularity premise. -/
theorem globalCandidateAFiveSectorOperatorFrameVectorDifferentiable_of_transport
    (transported_vector_differentiable : ∀ index,
      Differentiable Real
        (fun parameter : Real =>
          isomorphisms.transport representation sectorData.coordinates
            refinement pullback 0 parameter (baseKernelBasis index).1)) :
    GlobalCandidateAFiveSectorOperatorFrameVectorDifferentiable period hPeriod
      configuration data analysis sectorData resolution decomposition_eq
        representation refinement pullback isomorphisms baseKernelBasis := by
  intro index
  exact transported_vector_differentiable index

/-- Differentiable fixed-label packet for the complete Candidate-A kernels. -/
def globalCandidateAFiveSectorDifferentiableKernelBasisFamilyData
    (operatorFrame_vector_differentiable :
      GlobalCandidateAFiveSectorOperatorFrameVectorDifferentiable period hPeriod
        configuration data analysis sectorData resolution decomposition_eq
          representation refinement pullback isomorphisms baseKernelBasis) :
    DifferentiableFiniteKernelBasisFamilyData operator Index :=
  let gramData := globalCandidateAFiveSectorIsomorphismFamilyKernelGramData
    period hPeriod configuration data analysis sectorData resolution
      decomposition_eq representation refinement pullback isomorphisms
        baseKernelBasis
  toDifferentiableFiniteKernelBasisFamilyData representation
    sectorData.coordinates refinement pullback gramData (by
      simpa only [GlobalCandidateAFiveSectorOperatorFrameVectorDifferentiable]
        using operatorFrame_vector_differentiable)

/-- Terminal Candidate-A C1 true-kernel checkpoint. -/
theorem global_candidateA_five_sector_differentiable_true_kernel_family_gate
    (operatorFrame_vector_differentiable :
      GlobalCandidateAFiveSectorOperatorFrameVectorDifferentiable period hPeriod
        configuration data analysis sectorData resolution decomposition_eq
          representation refinement pullback isomorphisms baseKernelBasis) :
    let gramData := globalCandidateAFiveSectorIsomorphismFamilyKernelGramData
      period hPeriod configuration data analysis sectorData resolution
        decomposition_eq representation refinement pullback isomorphisms
          baseKernelBasis
    let kernels := globalCandidateAFiveSectorDifferentiableKernelBasisFamilyData
      period hPeriod configuration data analysis sectorData resolution
        decomposition_eq representation refinement pullback isomorphisms
          baseKernelBasis operatorFrame_vector_differentiable
    (∀ index,
      Differentiable Real
        (fun parameter : Real => kernels.kernels.vector parameter index)) ∧
    (∀ parameter,
      Submodule.span Real
          (Set.range
            (gramData.transportedKernelVector representation
              sectorData.coordinates refinement pullback parameter)) = ⊤) ∧
    transportedKernelGramRegularSet representation sectorData.coordinates
      refinement pullback gramData = Set.univ := by
  let gramData := globalCandidateAFiveSectorIsomorphismFamilyKernelGramData
    period hPeriod configuration data analysis sectorData resolution
      decomposition_eq representation refinement pullback isomorphisms
        baseKernelBasis
  have hVector : ∀ index,
      Differentiable Real
        (fun parameter : Real =>
          (gramData.operatorFrame representation sectorData.coordinates
            refinement pullback).frame parameter
              (gramData.baseKernelBasis index).1) := by
    simpa only [GlobalCandidateAFiveSectorOperatorFrameVectorDifferentiable]
      using operatorFrame_vector_differentiable
  simpa only [globalCandidateAFiveSectorDifferentiableKernelBasisFamilyData]
    using
      (five_sector_l2_admissible_frame_differentiable_true_kernel_global_gate
        representation sectorData.coordinates refinement pullback gramData
          hVector)

end
end P0EFTJanusProgramPGlobalCandidateAFiveSectorL2AdmissibleIsomorphismFamilyTrueKernelFrontend4D
end JanusFormal
