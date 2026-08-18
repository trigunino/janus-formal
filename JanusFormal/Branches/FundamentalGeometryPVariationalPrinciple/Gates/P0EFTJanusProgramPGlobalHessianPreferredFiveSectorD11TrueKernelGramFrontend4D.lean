import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAFiveSectorL2AdmissibleIsomorphismFamilyTrueKernelFrontend4D

/-!
# Preferred Candidate-A D11 true-kernel frontend

This frontend deliberately stops before the named-kernel-family closure.  Its
input contains only the represented operator family, the physical five-sector
geometry, one basis of the true kernel at parameter zero and the admissible D11
isomorphisms transporting that basis.  The global kernel family is an output.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11TrueKernelGramFrontend4D

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
open P0EFTJanusProgramPGlobalCandidateAFiveSectorL2AdmissibleIsomorphismFamilyKernelGramFrontend4D
open P0EFTJanusProgramPGlobalCandidateAFiveSectorL2AdmissibleIsomorphismFamilyTrueKernelFrontend4D

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

/-- Minimal pre-named-kernel D11 input.  In particular it contains no basis or
transport for kernels away from the base parameter. -/
structure GlobalHessianPreferredFiveSectorD11BasepointInput4D
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (Metric Abelian Matter Longitudinal Boundary : Type*)
    (Index : Type)
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    [Fintype Index] [DecidableEq Index]
    (operator : Real →
    CandidateAHilbert period hPeriod configuration data analysis →L[Real]
      CandidateAHilbert period hPeriod configuration data analysis)
    (sectorData : GlobalCandidateAFiveSectorCompletionCoordinates4D period hPeriod
      configuration data analysis Metric Abelian Matter Longitudinal Boundary)
    (resolution : FiveSectorOrthogonalProductDecomposition
    (E := CandidateAHilbert period hPeriod configuration data analysis)
    (MetricDiffeomorphism := Metric) (AbelianGauge := Abelian)
    (PrimitiveSpinCMatter := Matter) (LongitudinalLL := Longitudinal)
    (BoundaryFiniteBV := Boundary))
    (decomposition_eq : resolution.decomposition =
      sectorData.coordinates.decomposition.toContinuousLinearEquiv)
    {immersionCategory : SpinCImmersionCategory}
    {ellipticFamily : NaturalEllipticOperatorFamily immersionCategory}
    (representation : NaturalEllipticOperatorRepresentationData immersionCategory
      ellipticFamily (fun parameter state => operator parameter state))
    (refinement : FiveSectorNaturalRepresentationRefinementData representation
      sectorData.coordinates)
    (pullback : FiveSectorNaturalRepresentationPullbackData representation
      sectorData.coordinates refinement)
    (isomorphisms : LinearNaturalRepresentationAdmissibleIsomorphismFamilyData
      representation sectorData.coordinates refinement pullback) where
  baseKernelBasis : Module.Basis Index Real (operator 0).ker
  transported_vector_differentiable : ∀ index,
    Differentiable Real
      (fun parameter : Real =>
        isomorphisms.transport representation sectorData.coordinates refinement
          pullback 0 parameter (baseKernelBasis index).1)

variable
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {Metric Abelian Matter Longitudinal Boundary : Type*}
    {Index : Type}
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    [Fintype Index] [DecidableEq Index]
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
    {immersionCategory : SpinCImmersionCategory}
    {ellipticFamily : NaturalEllipticOperatorFamily immersionCategory}
    (representation : NaturalEllipticOperatorRepresentationData
      immersionCategory ellipticFamily
        (fun parameter state => operator parameter state))
    (refinement : FiveSectorNaturalRepresentationRefinementData representation
      sectorData.coordinates)
    (pullback : FiveSectorNaturalRepresentationPullbackData representation
      sectorData.coordinates refinement)
    (isomorphisms : LinearNaturalRepresentationAdmissibleIsomorphismFamilyData
      representation sectorData.coordinates refinement pullback)
    (input : GlobalHessianPreferredFiveSectorD11BasepointInput4D period hPeriod
      configuration data analysis Metric Abelian Matter Longitudinal Boundary
        Index operator sectorData resolution decomposition_eq representation
          refinement pullback isomorphisms)

/-- Complete true-kernel basis transported from the sole basepoint basis. -/
def globalHessianPreferredFiveSectorD11TrueKernelBasis (parameter : Real) :
    Module.Basis Index Real (operator parameter).ker :=
  globalCandidateAFiveSectorTrueKernelBasis period hPeriod configuration data
    analysis sectorData resolution decomposition_eq representation refinement
      pullback isomorphisms input.baseKernelBasis parameter

/-- The resulting fixed-label finite family of all true kernels. -/
def globalHessianPreferredFiveSectorD11FiniteKernelBasisFamilyData :
    FiniteKernelBasisFamilyData operator Index :=
  globalCandidateAFiveSectorFiniteKernelBasisFamilyData period hPeriod
    configuration data analysis sectorData resolution decomposition_eq
      representation refinement pullback isomorphisms input.baseKernelBasis

/-- The C1 D11 transport field supplies exactly the Gram-frame regularity. -/
theorem globalHessianPreferredFiveSectorD11OperatorFrameVectorDifferentiable :
    GlobalCandidateAFiveSectorOperatorFrameVectorDifferentiable period hPeriod
      configuration data analysis sectorData resolution decomposition_eq
        representation refinement pullback isomorphisms input.baseKernelBasis :=
  globalCandidateAFiveSectorOperatorFrameVectorDifferentiable_of_transport
    period hPeriod configuration data analysis sectorData resolution
      decomposition_eq representation refinement pullback isomorphisms
        input.baseKernelBasis input.transported_vector_differentiable

/-- C1 fixed-label packet, constructed rather than assumed globally. -/
def globalHessianPreferredFiveSectorD11DifferentiableKernelBasisFamilyData :
    DifferentiableFiniteKernelBasisFamilyData operator Index :=
  globalCandidateAFiveSectorDifferentiableKernelBasisFamilyData period hPeriod
    configuration data analysis sectorData resolution decomposition_eq
      representation refinement pullback isomorphisms input.baseKernelBasis
          (globalHessianPreferredFiveSectorD11OperatorFrameVectorDifferentiable
            period hPeriod sectorData resolution decomposition_eq representation
              refinement pullback isomorphisms input)

/-- Terminal pre-named-kernel checkpoint: C1 basis, full true kernels, global
Gram regularity and constant kernel rank are all outputs. -/
theorem global_hessian_preferred_five_sector_D11_true_kernel_gram_gate :
    let gramData := globalCandidateAFiveSectorIsomorphismFamilyKernelGramData
      period hPeriod configuration data analysis sectorData resolution
        decomposition_eq representation refinement pullback isomorphisms
          input.baseKernelBasis
    let kernels :=
      globalHessianPreferredFiveSectorD11DifferentiableKernelBasisFamilyData
        period hPeriod sectorData resolution decomposition_eq representation
          refinement pullback isomorphisms input
    (∀ index,
      Differentiable Real
        (fun parameter : Real => kernels.kernels.vector parameter index)) ∧
    (∀ parameter,
      Submodule.span Real
          (Set.range
            (gramData.transportedKernelVector representation
              sectorData.coordinates refinement pullback parameter)) = ⊤) ∧
    transportedKernelGramRegularSet representation
        sectorData.coordinates refinement pullback gramData =
      Set.univ ∧
    (∀ parameter,
      Module.finrank Real (operator parameter).ker =
        Fintype.card Index) := by
  have hC1 :=
    global_candidateA_five_sector_differentiable_true_kernel_family_gate
      period hPeriod configuration data analysis sectorData resolution
        decomposition_eq representation refinement pullback isomorphisms
          input.baseKernelBasis
            (globalHessianPreferredFiveSectorD11OperatorFrameVectorDifferentiable
              period hPeriod sectorData resolution decomposition_eq representation
                refinement pullback isomorphisms input)
  have hTrue := global_candidateA_five_sector_true_kernel_family_gate
    period hPeriod configuration data analysis sectorData resolution
      decomposition_eq representation refinement pullback isomorphisms
        input.baseKernelBasis
  exact ⟨hC1.1, hC1.2.1, hC1.2.2, hTrue.2.2.2⟩

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11TrueKernelGramFrontend4D
end JanusFormal
