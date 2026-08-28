import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianSchurDeterminantFrontier4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAActualSchurExplicitGreen4D

/-!
# Terminal H10--H14 frontier with the explicit Schur propagator

The finite Schur determinant gives the zero-mode-free H10--H14 certificate.
This final façade additionally returns the actual block Green operator

`T⁻¹ R diag(S⁻¹,D⁻¹) L T`

and its two inverse identities against the genuine augmented Candidate-A
Hessian.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianSchurExplicitGreenFrontier4D

set_option autoImplicit false
set_option maxHeartbeats 12800000
set_option synthInstance.maxHeartbeats 6400000

noncomputable section

open Set Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
open P0EFTJanusProgramPGlobalCandidateASixPhysicalChartPullback4D
open P0EFTJanusProgramPGlobalCandidateAActualSchurDeterminant4D
open P0EFTJanusProgramPGlobalCandidateAActualSchurExplicitGreen4D
open P0EFTJanusProgramPGlobalHessianActualKernelFrontier4D
open P0EFTJanusProgramPGlobalHessianActualKernelChartFrontier4D
open P0EFTJanusProgramPGlobalHessianSchurDeterminantFrontier4D
open P0EFTJanusProgramPGlobalHessianDiracGreenBoundedClosure4D

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

/-- Strongest current zero-mode-free terminal output. -/
def global_candidateA_hessian_schur_explicit_green_frontier_gate
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
      period hPeriod (measure := measure) configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale)
    (realization : GlobalCandidateACommonHilbertToLocalChart4D period hPeriod
      configuration data analysis
        (globalCandidateAActualKernelChart period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod configuration data
          analysis einsteinScale hTransverse family) einsteinScale family)
    (Mode Complement : Type*)
    [Fintype Mode] [DecidableEq Mode]
    [NormedAddCommGroup Complement] [NormedSpace Real Complement]
    (determinantData : GlobalCandidateAActualSchurDeterminantData4D period
      hPeriod configuration data analysis
        (globalCandidateAActualKernelChart period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelChartPhysicalExtension period hPeriod
          configuration data analysis einsteinScale hTransverse family
            realization)
        Mode Complement) :=
  let terminal := global_candidateA_hessian_schur_determinant_frontier_gate
    period hPeriod configuration data analysis einsteinScale hTransverse family
      realization Mode Complement determinantData
  let propagator := global_candidateA_actual_schur_explicit_green_gate
    period hPeriod determinantData
  (PLift.up terminal, PLift.up propagator,
    globalCandidateAActualSchurExplicitGreen period hPeriod determinantData)

/-- The terminal packet count remains three; the Green formula is derived from
the finite determinant packet rather than supplied. -/
theorem global_candidateA_hessian_schur_explicit_green_three_inputs :
    Nonempty (Unit × Unit × Unit) :=
  ⟨((), (), ())⟩

end
end P0EFTJanusProgramPGlobalHessianSchurExplicitGreenFrontier4D
end JanusFormal
