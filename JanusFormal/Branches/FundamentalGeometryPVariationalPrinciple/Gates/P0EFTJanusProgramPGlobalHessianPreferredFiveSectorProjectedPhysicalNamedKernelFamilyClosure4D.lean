import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelGlobalContinuation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D

/-!
# Replace the arbitrary named family by the projected physical kernel family

The family-index closure initially carries one arbitrary fixed-label basis of
every actual kernel.  The projected Candidate-A construction now provides a
canonical sector-pure replacement wherever the projected Gram determinant does
not cross zero.

Under the exact global continuation statement

`projectedKernelRegularSet = univ`,

this file rebuilds the existing named-kernel family closure with

* exactly the same family-index/spectral-cut data;
* exactly the same actual operator family;
* the canonical projected physical basis at every parameter;
* the same action-generated H12 basis at parameter zero;
* differentiable ambient basis vectors inherited from the projected family.

Thus the no-Gram-crossing criterion feeds the already implemented determinant
and families-index architecture through its genuine `FiniteKernelBasisFamilyData`
interface.  No parallel or replacement operator family is introduced.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedPhysicalNamedKernelFamilyClosure4D

set_option autoImplicit false
set_option maxHeartbeats 54000000
set_option synthInstance.maxHeartbeats 27000000
noncomputable section

open Set Filter Topology MeasureTheory
open scoped BigOperators Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
open P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D
open P0EFTJanusProgramPFiniteKernelBasisFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedResolvedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelBasisFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelRegularChart4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelGlobalContinuation4D
open P0EFTJanusProgramPDenseCoreChartBilinearBound4D

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
    BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl

variable
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {einsteinScale : Real}
    {hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric}
    {family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale}
    {chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis
          (globalCandidateAActualKernelChart period hPeriod configuration data
            analysis einsteinScale hTransverse family)
          (globalCandidateAActualKernelSameAction period hPeriod configuration
            data analysis einsteinScale hTransverse family))}
    {Metric Abelian Matter Longitudinal Boundary : Type*}
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    {ZeroMode : Type*} [Fintype ZeroMode] [DecidableEq ZeroMode]
    {fold : Fold} {Index : Type*}

/-- The canonical all-parameter projected physical basis obtained from the
no-Gram-crossing statement. -/
def projectedPhysicalBasisFamily
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (hRegular : projectedKernelRegularSet period hPeriod input = Set.univ) :
    GlobalHessianPreferredFiveSectorProjectedKernelBasisFamily4D
      period hPeriod input natural :=
  globalProjectedKernelBasisFamilyOfRegularSetEqUniv period hPeriod input natural
    hRegular

/-- Existing family-index closure rebuilt with the projected physical kernel
basis and no change to the operator/spectral family. -/
def projectedPhysicalNamedKernelFamilyClosure
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (hRegular : projectedKernelRegularSet period hPeriod input = Set.univ) :
    GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index := by
  let physical := projectedPhysicalBasisFamily period hPeriod input natural hRegular
  exact
    { familyIndex := input.familyIndex
      kernels := physical.physicalKernels period hPeriod input natural
      basis_zero_agreement := by
        intro mode
        change
          (physical.physicalKernels period hPeriod input natural).vector 0 mode =
            (input.familyIndex.baseFamily.quillen.intrinsicFamily.basepoint.
              intrinsic.closure.basis mode).1
        rw [physical.physicalKernels_vector_zero period hPeriod input natural]
        exact input.basis_zero_agreement mode }

/-- The rebuilt closure retains the original family-index datum definitionally. -/
@[simp]
theorem projectedPhysicalNamedKernelFamilyClosure_familyIndex
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (hRegular : projectedKernelRegularSet period hPeriod input = Set.univ) :
    (projectedPhysicalNamedKernelFamilyClosure period hPeriod input natural
      hRegular).familyIndex = input.familyIndex :=
  rfl

/-- Every ambient named vector of the rebuilt closure is exactly the canonical
sector projection of the original named vector. -/
@[simp]
theorem projectedPhysicalNamedKernelFamilyClosure_vector
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (hRegular : projectedKernelRegularSet period hPeriod input = Set.univ)
    (parameter : Real) (mode : ZeroMode) :
    (projectedPhysicalNamedKernelFamilyClosure period hPeriod input natural
      hRegular).kernels.vector parameter mode =
      projectedNamedKernelVector period hPeriod input parameter mode := by
  let physical := projectedPhysicalBasisFamily period hPeriod input natural hRegular
  change
    (physical.physicalKernels period hPeriod input natural).vector parameter mode =
      projectedNamedKernelVector period hPeriod input parameter mode
  exact physical.physicalKernels_vector period hPeriod input natural parameter mode

/-- In particular, the replacement basis remains in the true actual kernel. -/
theorem projectedPhysicalNamedKernelFamilyClosure_vector_mem_kernel
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (hRegular : projectedKernelRegularSet period hPeriod input = Set.univ)
    (parameter : Real) (mode : ZeroMode) :
    input.familyIndex.baseFamily.actualOperator parameter
        ((projectedPhysicalNamedKernelFamilyClosure period hPeriod input natural
          hRegular).kernels.vector parameter mode) = 0 := by
  rw [projectedPhysicalNamedKernelFamilyClosure_vector period hPeriod input natural
    hRegular]
  exact projectedNamedKernelVector_mem_kernel period hPeriod input natural parameter
    mode

/-- Every replacement basis vector is genuinely sector-pure at every parameter. -/
theorem projectedPhysicalNamedKernelFamilyClosure_vector_mem_sectorKernel
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (hRegular : projectedKernelRegularSet period hPeriod input = Set.univ)
    (parameter : Real) (mode : ZeroMode) :
    (projectedPhysicalNamedKernelFamilyClosure period hPeriod input natural
      hRegular).kernels.vector parameter mode ∈
      sectorKernel period hPeriod input parameter
        (namedModeFiveSector period hPeriod input mode) := by
  rw [projectedPhysicalNamedKernelFamilyClosure_vector period hPeriod input natural
    hRegular]
  exact projectedNamedKernelVector_mem_sectorKernel period hPeriod input natural
    parameter mode

/-- C1 regularity of the original named family automatically upgrades the
rebuilt physical named family. -/
def projectedPhysicalNamedKernelFamilyRegularity
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (regularity : GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod input)
    (hRegular : projectedKernelRegularSet period hPeriod input = Set.univ) :
    GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod
        (projectedPhysicalNamedKernelFamilyClosure period hPeriod input natural
          hRegular) where
  vector_differentiable := by
    intro mode
    let physical := projectedPhysicalBasisFamily period hPeriod input natural hRegular
    change Differentiable Real
      (fun parameter : Real =>
        (physical.physicalKernels period hPeriod input natural).vector parameter
          mode)
    exact physical.physicalKernels_vector_differentiable period hPeriod input natural
      regularity mode

/-- The rebuilt C1 family still agrees with the exact action-generator basis at
H12. -/
theorem projectedPhysicalNamedKernelFamilyClosure_vector_zero_eq_actionGenerator
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (hRegular : projectedKernelRegularSet period hPeriod input = Set.univ)
    (mode : ZeroMode) :
    (projectedPhysicalNamedKernelFamilyClosure period hPeriod input natural
      hRegular).kernels.vector 0 mode =
      input.familyIndex.baseFamily.quillen.intrinsicFamily.basepoint.intrinsic.
        closure.frontier.generators.translations.vector mode := by
  rw [projectedPhysicalNamedKernelFamilyClosure_vector period hPeriod input natural
    hRegular]
  rw [projectedNamedKernelVector_zero period hPeriod input]
  exact input.vector_zero_eq_actionGenerator period hPeriod mode

/-- Public physical replacement-family checkpoint. -/
theorem projected_physical_named_kernel_family_closure_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (regularity : GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod input)
    (hRegular : projectedKernelRegularSet period hPeriod input = Set.univ) :
    let physicalInput :=
      projectedPhysicalNamedKernelFamilyClosure period hPeriod input natural hRegular
    physicalInput.familyIndex = input.familyIndex ∧
    (∀ parameter mode,
      physicalInput.kernels.vector parameter mode ∈
        sectorKernel period hPeriod input parameter
          (namedModeFiveSector period hPeriod input mode)) ∧
    GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod physicalInput ∧
    (∀ mode,
      physicalInput.kernels.vector 0 mode =
        input.familyIndex.baseFamily.quillen.intrinsicFamily.basepoint.intrinsic.
          closure.frontier.generators.translations.vector mode) := by
  dsimp
  exact
    ⟨projectedPhysicalNamedKernelFamilyClosure_familyIndex period hPeriod input
        natural hRegular,
      projectedPhysicalNamedKernelFamilyClosure_vector_mem_sectorKernel period
        hPeriod input natural hRegular,
      projectedPhysicalNamedKernelFamilyRegularity period hPeriod input natural
        regularity hRegular,
      projectedPhysicalNamedKernelFamilyClosure_vector_zero_eq_actionGenerator
        period hPeriod input natural hRegular⟩

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedPhysicalNamedKernelFamilyClosure4D
end JanusFormal
