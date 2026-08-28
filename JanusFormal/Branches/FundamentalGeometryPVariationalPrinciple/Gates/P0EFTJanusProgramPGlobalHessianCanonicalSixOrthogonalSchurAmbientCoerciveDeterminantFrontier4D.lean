import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAActualOrthogonalSchurAmbientCoercivity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianCanonicalSixOrthogonalSchurCoerciveDeterminantFrontier4D

/-!
# Full Candidate-A Green operator from ambient coercivity and a determinant

On the zero-mode-free stratum the only infinite-dimensional estimate is
coercivity of the displayed augmented Hessian on the orthogonal complement of
finitely many concrete reference modes.  This constructs `D⁻¹`.  A nonzero
determinant of the finite Schur matrix then constructs the inverse of the full
Hessian.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianCanonicalSixOrthogonalSchurAmbientCoerciveDeterminantFrontier4D

set_option autoImplicit false
set_option maxHeartbeats 16800000
set_option synthInstance.maxHeartbeats 8400000

noncomputable section

open Set Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
open P0EFTJanusProgramPGlobalCandidateAH10BoundaryProjectionFromChartBound4D
open P0EFTJanusProgramPGlobalCandidateAActualOrthogonalSchurAmbientCoercivity4D
open P0EFTJanusProgramPGlobalHessianCanonicalSixOrthogonalSchurCoerciveDeterminantFrontier4D
open P0EFTJanusProgramPGlobalHessianActualKernelFrontier4D
open P0EFTJanusProgramPGlobalHessianDiracGreenBoundedClosure4D
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
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- Ambient Candidate-A coercivity and nonvanishing of the induced finite Schur
determinant. -/
structure GlobalCandidateAActualOrthogonalSchurAmbientCoerciveDeterminantData4D
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
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction)
    (Mode : Type*) [Fintype Mode] [DecidableEq Mode] where
  ambient : GlobalCandidateAActualOrthogonalSchurNamedAmbientCoercivityData4D
    period hPeriod configuration data analysis chart sameAction physical Mode
  determinant_ne_zero :
    globalCandidateAHessianNamedOrthogonalSchurDeterminant
      ((ambient.toComplementCoercivityData period hPeriod).toNamedVectorsData
        period hPeriod) ≠ 0

/-- Convert the physical ambient estimate to the preceding compressed-block
coercive determinant packet. -/
def GlobalCandidateAActualOrthogonalSchurAmbientCoerciveDeterminantData4D.toCoerciveDeterminantData
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure}
    {sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod configuration data analysis chart}
    {physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction}
    {Mode : Type*} [Fintype Mode] [DecidableEq Mode]
    (determinantData :
      GlobalCandidateAActualOrthogonalSchurAmbientCoerciveDeterminantData4D
        period hPeriod configuration data analysis chart sameAction physical
          Mode) :
    GlobalCandidateAActualOrthogonalSchurCoerciveDeterminantData4D period
      hPeriod configuration data analysis chart sameAction physical Mode where
  coercive := determinantData.ambient.toComplementCoercivityData period hPeriod
  determinant_ne_zero := determinantData.determinant_ne_zero

/-- Preferred zero-mode-free terminal from the ambient Hessian estimate. -/
def global_candidateA_hessian_canonicalSix_orthogonalSchurAmbientCoerciveDeterminant_frontier_gate
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale)
    (chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis
          (globalCandidateAActualKernelChart period hPeriod configuration data
            analysis einsteinScale hTransverse family)
          (globalCandidateAActualKernelSameAction period hPeriod configuration
            data analysis einsteinScale hTransverse family)))
    (Mode : Type*) [Fintype Mode] [DecidableEq Mode]
    (determinantData :
      GlobalCandidateAActualOrthogonalSchurAmbientCoerciveDeterminantData4D
        period hPeriod configuration data analysis
        (globalCandidateAActualKernelChart period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateACanonicalSixOrthogonalSchurPhysicalExtension period
          hPeriod configuration data analysis einsteinScale hTransverse family
            chartBound)
        Mode) :=
  let coerciveDeterminant :=
    determinantData.toCoerciveDeterminantData period hPeriod
  let terminal :=
    global_candidateA_hessian_canonicalSix_orthogonalSchurCoerciveDeterminant_frontier_gate
      period hPeriod configuration data analysis einsteinScale hTransverse
        family chartBound Mode coerciveDeterminant
  (terminal,
    determinantData.ambient.ambientCoercivity.constant,
    determinantData.ambient.ambientCoercivity.constant_pos,
    determinantData.ambient.ambientCoercivity.coercive,
    determinantData.determinant_ne_zero)

end
end P0EFTJanusProgramPGlobalHessianCanonicalSixOrthogonalSchurAmbientCoerciveDeterminantFrontier4D
end JanusFormal
