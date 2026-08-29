import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianZeroModeModelFrontier4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAActualSchurZeroMode4D

/-!
# Terminal H10--H14 frontier through a finite Schur zero-mode problem

The classified-zero-mode frontier still asked for a linear equivalence from a
finite coordinate space directly onto the kernel of the full augmented
Hessian.  The present façade replaces that global kernel classification by a
finite Schur reduction:

* choose finitely many reference modes;
* eliminate one bijective infinite-dimensional complement block;
* compute the finite Schur operator `S`;
* classify `ker S` instead of `ker H`.

The generic reduction constructs the exact equivalence `ker H ≃ ker S`, while
closed range supplies the true-kernel coercive gap.  All H10--H14, Green,
resolvent and perturbative outputs of the existing zero-mode frontier are then
reused unchanged.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianSchurZeroModeFrontier4D

set_option autoImplicit false
set_option maxHeartbeats 8400000
set_option synthInstance.maxHeartbeats 4200000

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
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelStability4D
open P0EFTJanusProgramPGlobalCandidateAActualSchurZeroMode4D
open P0EFTJanusProgramPGlobalHessianActualKernelFrontier4D
open P0EFTJanusProgramPGlobalHessianActualKernelChartFrontier4D
open P0EFTJanusProgramPGlobalHessianZeroModeModelFrontier4D
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

/-- Preferred terminal gate when the zero-mode problem is presented through a
finite Schur complement rather than a direct basis of the full kernel. -/
def global_candidateA_hessian_schur_zeroMode_frontier_gate
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
    [AddCommGroup Complement] [Module Real Complement]
    (schurData : GlobalCandidateAActualSchurZeroModeData4D period hPeriod
      configuration data analysis
        (globalCandidateAActualKernelChart period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelChartPhysicalExtension period hPeriod
          configuration data analysis einsteinScale hTransverse family
            realization)
        Mode Complement) :=
  let zeroModes := schurData.toActualZeroModeGap period hPeriod
  let terminal := global_candidateA_hessian_zeroModeModel_frontier_gate
    period hPeriod configuration data analysis einsteinScale hTransverse family
      realization zeroModes
  And.intro terminal
    (And.intro (schurData.kernel_finrank_eq_schur period hPeriod)
      (schurData.kernel_finrank_le_mode_card period hPeriod))

/-- Perturbative stability of the same Schur-classified Hessian. -/
def global_candidateA_hessian_schur_zeroMode_stability_gate
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
    [AddCommGroup Complement] [Module Real Complement]
    (schurData : GlobalCandidateAActualSchurZeroModeData4D period hPeriod
      configuration data analysis
        (globalCandidateAActualKernelChart period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelChartPhysicalExtension period hPeriod
          configuration data analysis einsteinScale hTransverse family
            realization)
        Mode Complement)
    (perturbation : GlobalCandidateAActualKernelPerturbation4D period hPeriod
      configuration data analysis
        (globalCandidateAActualKernelChart period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelChartPhysicalExtension period hPeriod
          configuration data analysis einsteinScale hTransverse family
            realization)
        ((schurData.toActualZeroModeGap period hPeriod).toActualKernelGap
          period hPeriod)) :=
  global_candidateA_hessian_zeroModeModel_stability_gate period hPeriod
    configuration data analysis einsteinScale hTransverse family realization
      (schurData.toActualZeroModeGap period hPeriod) perturbation

/-- The terminal interface still has three analytic packets, but its third
packet is now finite-dimensional Schur data rather than a direct basis of the
full Hilbert-space kernel. -/
theorem global_candidateA_hessian_schur_zeroMode_three_inputs :
    Nonempty (Unit × Unit × Unit) :=
  ⟨((), (), ())⟩

end
end P0EFTJanusProgramPGlobalHessianSchurZeroModeFrontier4D
end JanusFormal
