import Mathlib.LinearAlgebra.Matrix.Block
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelGramBlocks4D

/-!
# Factorization of the projected Candidate-A kernel Gram determinant

The projected physical Gram matrix has no entries between distinct physical
sectors.  A fixed auxiliary order on the five sector labels therefore makes the
matrix block triangular.  The finite block-triangular determinant theorem then
gives the exact identity

`det G(a) = product_s det G_s(a)`.

The auxiliary order is used only to invoke the determinant theorem; the final
factorization is the unordered finite product over the five physical sectors.
Consequently, the full Gram-regular chart is exactly the intersection of the
five sector Gram-regular charts.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelGramFactorization4D

set_option autoImplicit false
set_option maxHeartbeats 62000000
set_option synthInstance.maxHeartbeats 31000000
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
open P0EFTJanusProgramPFiniteFamilyGramLocalPersistence4D
open P0EFTJanusProgramPFiveSectorHilbertCoordinates4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedResolvedKernelFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelRegularChart4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelGramBlocks4D
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

/-- A proof-only enumeration of the five physical sectors. -/
private def fivePhysicalSectorRank : FivePhysicalSector → Fin 5
  | .metricDiffeomorphism => 0
  | .abelianGauge => 1
  | .primitiveSpinCMatter => 2
  | .longitudinalLL => 3
  | .boundaryFiniteBV => 4

private theorem fivePhysicalSectorRank_injective :
    Function.Injective fivePhysicalSectorRank := by
  intro first second hEqual
  cases first <;> cases second <;>
    simp [fivePhysicalSectorRank] at hEqual ⊢

local instance fivePhysicalSectorLinearOrder : LinearOrder FivePhysicalSector :=
  LinearOrder.lift' fivePhysicalSectorRank fivePhysicalSectorRank_injective

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

/-- The full projected Gram matrix is block triangular with respect to the
physical sector label.  In fact it is block diagonal, since every off-sector
entry vanishes. -/
theorem projectedKernelGramMatrix_blockTriangular
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (parameter : Real) :
    Matrix.BlockTriangular
      (finiteFamilyGramMatrix
        (fun mode =>
          projectedNamedKernelVector period hPeriod input parameter mode))
      (namedModeFiveSector period hPeriod input) := by
  intro row column hLower
  exact projectedKernelGramMatrix_offSector_zero period hPeriod input parameter
    row column (ne_of_gt hLower)

/-- The square block selected by one physical label is definitionally the
sector Gram matrix introduced in the preceding layer. -/
theorem projectedKernelGramMatrix_toSquareBlock
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (parameter : Real) (sector : FivePhysicalSector) :
    (finiteFamilyGramMatrix
        (fun mode =>
          projectedNamedKernelVector period hPeriod input parameter mode)).
      toSquareBlock (namedModeFiveSector period hPeriod input) sector =
        projectedKernelSectorGramMatrix period hPeriod input parameter sector := by
  rfl

/-- Exact determinant factorization into the five physical Gram blocks. -/
theorem projectedKernelGramDeterminant_eq_sectorProduct
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (parameter : Real) :
    (finiteFamilyGramMatrix
      (fun mode =>
        projectedNamedKernelVector period hPeriod input parameter mode)).det =
      ∏ sector : FivePhysicalSector,
        projectedKernelSectorGramDeterminant period hPeriod input parameter
          sector := by
  have hTriangular :=
    projectedKernelGramMatrix_blockTriangular period hPeriod input parameter
  calc
    (finiteFamilyGramMatrix
      (fun mode =>
        projectedNamedKernelVector period hPeriod input parameter mode)).det =
        ∏ sector : FivePhysicalSector,
          ((finiteFamilyGramMatrix
              (fun mode =>
                projectedNamedKernelVector period hPeriod input parameter mode)).
            toSquareBlock (namedModeFiveSector period hPeriod input) sector).det :=
      hTriangular.det_fintype
    _ = ∏ sector : FivePhysicalSector,
        projectedKernelSectorGramDeterminant period hPeriod input parameter
          sector := by
      apply Finset.prod_congr rfl
      intro sector _
      rw [projectedKernelGramMatrix_toSquareBlock period hPeriod input parameter
        sector]
      rfl

/-- Absolute determinant factorization.  This is the form used to propagate
quantitative sector margins to a full Gram margin. -/
theorem abs_projectedKernelGramDeterminant_eq_sectorProduct
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (parameter : Real) :
    |(finiteFamilyGramMatrix
      (fun mode =>
        projectedNamedKernelVector period hPeriod input parameter mode)).det| =
      ∏ sector : FivePhysicalSector,
        |projectedKernelSectorGramDeterminant period hPeriod input parameter
          sector| := by
  rw [projectedKernelGramDeterminant_eq_sectorProduct period hPeriod input
    parameter]
  simpa using
    (Finset.abs_prod (Finset.univ : Finset FivePhysicalSector)
      (fun sector =>
        projectedKernelSectorGramDeterminant period hPeriod input parameter
          sector))

/-- Full Gram regularity at one parameter is equivalent to simultaneous
regularity of all five physical blocks. -/
theorem mem_projectedKernelRegularSet_iff_forall_sector
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (parameter : Real) :
    parameter ∈ projectedKernelRegularSet period hPeriod input ↔
      ∀ sector : FivePhysicalSector,
        parameter ∈
          projectedKernelSectorRegularSet period hPeriod input sector := by
  change
    (finiteFamilyGramMatrix
      (fun mode =>
        projectedNamedKernelVector period hPeriod input parameter mode)).det ≠ 0 ↔
      ∀ sector : FivePhysicalSector,
        projectedKernelSectorGramDeterminant period hPeriod input parameter
          sector ≠ 0
  rw [projectedKernelGramDeterminant_eq_sectorProduct period hPeriod input
    parameter]
  simp

/-- The maximal full Gram chart is exactly the intersection of the five
sectorwise regular charts. -/
theorem projectedKernelRegularSet_eq_iInter_sectorRegularSet
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index) :
    projectedKernelRegularSet period hPeriod input =
      ⋂ sector : FivePhysicalSector,
        projectedKernelSectorRegularSet period hPeriod input sector := by
  ext parameter
  simp only [Set.mem_iInter]
  exact mem_projectedKernelRegularSet_iff_forall_sector period hPeriod input
    parameter

/-- Every physical Gram block is already nondegenerate at the H12 basepoint. -/
theorem zero_mem_projectedKernelSectorRegularSet
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (sector : FivePhysicalSector) :
    (0 : Real) ∈
      projectedKernelSectorRegularSet period hPeriod input sector :=
  (mem_projectedKernelRegularSet_iff_forall_sector period hPeriod input 0).mp
    (zero_mem_projectedKernelRegularSet period hPeriod input natural) sector

/-- Public five-sector determinant-factorization checkpoint. -/
theorem projected_kernel_gram_factorization_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (regularity : GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
      period hPeriod input) :
    (∀ parameter,
      (finiteFamilyGramMatrix
        (fun mode =>
          projectedNamedKernelVector period hPeriod input parameter mode)).det =
        ∏ sector : FivePhysicalSector,
          projectedKernelSectorGramDeterminant period hPeriod input parameter
            sector) ∧
    projectedKernelRegularSet period hPeriod input =
      ⋂ sector : FivePhysicalSector,
        projectedKernelSectorRegularSet period hPeriod input sector ∧
    (∀ sector,
      IsOpen (projectedKernelSectorRegularSet period hPeriod input sector)) ∧
    (∀ sector,
      (0 : Real) ∈
        projectedKernelSectorRegularSet period hPeriod input sector) :=
  ⟨projectedKernelGramDeterminant_eq_sectorProduct period hPeriod input,
    projectedKernelRegularSet_eq_iInter_sectorRegularSet period hPeriod input,
    isOpen_projectedKernelSectorRegularSet period hPeriod input regularity,
    zero_mem_projectedKernelSectorRegularSet period hPeriod input natural⟩

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorProjectedKernelGramFactorization4D
end JanusFormal