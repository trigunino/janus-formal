import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartMatrixDomain4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D

/-!
# Openness of the exact paired minimal-physical admissible domain

The full paired condition is expressed as an open condition on the continuous
paired-relative core: two fixed-base Lorentz conditions, an invertible plus
root, and the transported relative matrix in the fixed plus-base matrix
domain.  Exact C² transport identifies this open pullback with the original
nested admissibility predicate.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomainOpen4D

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 1200000

noncomputable section

open Set
open scoped Manifold ContDiff Topology BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartRegularMetric4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartGeometry4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootLift4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootInverseCore4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalRelativeMetricCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedRelativeMatrixCore4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedRelativeMatrixC2Exact4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartMatrixDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance c2ScalarNormedAddCommGroup :
    NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule
    period hPeriod).normedAddCommGroup

local instance c2ScalarNormedSpace :
    NormedSpace Real (C2Scalar period hPeriod) :=
  inferInstance

local instance c2ScalarCompleteSpace :
    CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

private local instance minimalModelAddCommGroup
    (configuration : GlobalFieldConfiguration period hPeriod) :
    AddCommGroup (GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration) :=
  Submodule.addCommGroup
    (GlobalMinimalPhysicalFieldTangent period hPeriod configuration)

private local instance minimalModelModule
    (configuration : GlobalFieldConfiguration period hPeriod) :
    Module Real (GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration) :=
  Submodule.module
    (GlobalMinimalPhysicalFieldTangent period hPeriod configuration)

/-- Open root-and-relative-matrix condition on the paired relative core. -/
def regularGeneralMetricC2PairedRelativeLorentzMatrixDomain
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :
    Set (RegularGeneralMetricC2PairedRelativeCore
      period hPeriod plusBase minusBase) :=
  regularGeneralMetricC2PairedRelativeMatrixDomain
      period hPeriod plusBase minusBase ∩
    (regularGeneralMetricC2PairedRelativeMatrix
      period hPeriod plusBase minusBase) ⁻¹'
      regularGeneralMetricC2LorentzChartMatrixDomain
        period hPeriod plusBase

theorem regularGeneralMetricC2PairedRelativeLorentzMatrixDomain_isOpen
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :
    IsOpen (regularGeneralMetricC2PairedRelativeLorentzMatrixDomain
      period hPeriod plusBase minusBase) := by
  exact (regularGeneralMetricC2PairedRelativeMatrix_contDiffOn
      period hPeriod plusBase minusBase).continuousOn.isOpen_inter_preimage
    (regularGeneralMetricC2PairedRelativeMatrixDomain_isOpen
      period hPeriod plusBase minusBase)
    (regularGeneralMetricC2LorentzChartMatrixDomain_isOpen
      period hPeriod plusBase)

/-- Full open paired condition on the relative core, including both independent
fixed-base Lorentz conditions. -/
def regularGeneralMetricC2PairedLorentzMatrixDomain
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :
    Set (RegularGeneralMetricC2PairedRelativeCore
      period hPeriod plusBase minusBase) :=
  (fun core => core.1) ⁻¹'
      (regularGeneralMetricC2LorentzChartDomain period hPeriod plusBase ×ˢ
        regularGeneralMetricC2LorentzChartDomain period hPeriod minusBase) ∩
    regularGeneralMetricC2PairedRelativeLorentzMatrixDomain
      period hPeriod plusBase minusBase

theorem regularGeneralMetricC2PairedLorentzMatrixDomain_isOpen
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :
    IsOpen (regularGeneralMetricC2PairedLorentzMatrixDomain
      period hPeriod plusBase minusBase) := by
  exact (((regularGeneralMetricC2LorentzChartDomain_isOpen
      period hPeriod plusBase).prod
    (regularGeneralMetricC2LorentzChartDomain_isOpen
      period hPeriod minusBase)).preimage continuous_fst).inter
    (regularGeneralMetricC2PairedRelativeLorentzMatrixDomain_isOpen
      period hPeriod plusBase minusBase)

/-- The nested relative condition is exactly membership of the transported
relative matrix in the fixed plus-base ambient domain. -/
theorem regularGeneralMetricC2Paired_relative_mem_iff_matrixDomain
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration)
    (hPlus : regularGeneralMetricSmoothC2Variation period hPeriod plusBase
        (direction.1.completeVariation.fullMetricPerturbation .plus) ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod plusBase) :
    regularGeneralMetricSmoothC2Variation period hPeriod
        (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
          plusBase
          (direction.1.completeVariation.fullMetricPerturbation .plus)
          hPlus)
        (regularGeneralMetricC2PairedRelativeTensor period hPeriod
          plusBase minusBase
          (direction.1.completeVariation.fullMetricPerturbation .plus)
          (direction.1.completeVariation.fullMetricPerturbation .minus)) ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod
        (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
          plusBase
          (direction.1.completeVariation.fullMetricPerturbation .plus)
          hPlus) ↔
      regularGeneralMetricC2PairedRelativeMatrix period hPeriod
          plusBase minusBase
          (globalMinimalPhysicalPairedRelativeMetricCoreLinearMap period hPeriod
            configuration plusBase minusBase direction) ∈
        regularGeneralMetricC2LorentzChartMatrixDomain
          period hPeriod plusBase := by
  rw [regularGeneralMetricC2LorentzChartDomain_mem_iff_matrixDomain]
  change
    regularGeneralMetricC2VariationMatrix period hPeriod
        (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
          plusBase
          (direction.1.completeVariation.fullMetricPerturbation .plus)
          hPlus)
        (regularGeneralMetricC2PairedRelativeTensor period hPeriod
          plusBase minusBase
          (direction.1.completeVariation.fullMetricPerturbation .plus)
          (direction.1.completeVariation.fullMetricPerturbation .minus)) ∈
      regularGeneralMetricC2LorentzChartMatrixDomain period hPeriod
        (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod
          plusBase
          (direction.1.completeVariation.fullMetricPerturbation .plus)
          hPlus) ↔ _
  rw [← regularGeneralMetricC2PairedRelativeMatrix_projected_exact
      period hPeriod configuration plusBase minusBase direction hPlus,
    regularGeneralMetricC2LorentzChartMatrixDomain_transport_eq
      period hPeriod plusBase
        (direction.1.completeVariation.fullMetricPerturbation .plus) hPlus]

/-- The original honest three-field admissibility predicate is precisely the
full open paired core condition. -/
theorem globalMetricPerturbationPairLorentzChartAdmissible_iff_mem_matrixDomain
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration) :
    GlobalMetricPerturbationPairLorentzChartAdmissible period hPeriod
        plusBase minusBase
          direction.1.completeVariation.fullMetricPerturbation ↔
      globalMinimalPhysicalPairedRelativeMetricCoreLinearMap period hPeriod
          configuration plusBase minusBase direction ∈
        regularGeneralMetricC2PairedLorentzMatrixDomain
          period hPeriod plusBase minusBase := by
  constructor
  · intro hAdmissible
    refine ⟨⟨hAdmissible.plus_mem, hAdmissible.minus_mem⟩, ?_⟩
    refine ⟨?_, ?_⟩
    · change
        (globalMinimalPhysicalPairedRelativeMetricCoreLinearMap period hPeriod
          configuration plusBase minusBase direction).2.1 ∈
          c2IdentityRootInvertiblePerturbationDomain period hPeriod
      rw [globalMinimalPhysicalPairedRelativeMetricCoreLinearMap_plus]
      exact regularGeneralMetricC2VariationMatrix_mem_invertibleRootDomain
        period hPeriod plusBase
          (direction.1.completeVariation.fullMetricPerturbation .plus)
          hAdmissible.plus_mem
    · exact (regularGeneralMetricC2Paired_relative_mem_iff_matrixDomain
        period hPeriod configuration plusBase minusBase direction
          hAdmissible.plus_mem).1 hAdmissible.relative_mem
  · rintro ⟨hSeparate, hRelative⟩
    let hPlus := hSeparate.1
    let hMinus := hSeparate.2
    refine {
      plus_mem := hPlus
      minus_mem := hMinus
      relative_mem := ?_ }
    exact (regularGeneralMetricC2Paired_relative_mem_iff_matrixDomain
      period hPeriod configuration plusBase minusBase direction hPlus).2
        hRelative.2

/-- Open pullback of the full paired matrix domain to the minimal tangent. -/
def regularGeneralMetricC2PairedMinimalPhysicalOpenAdmissibleDomain
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :
    Set (GlobalMinimalPhysicalFieldTangent period hPeriod configuration) :=
  (globalMinimalPhysicalPairedRelativeMetricCoreLinearMap period hPeriod
      configuration plusBase minusBase) ⁻¹'
    regularGeneralMetricC2PairedLorentzMatrixDomain
      period hPeriod plusBase minusBase

/-- The open pullback is extensionally the pre-existing exact admissibility
locus used by the local action family. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalOpenAdmissibleDomain_eq
    (configuration : GlobalFieldConfiguration period hPeriod)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :
    regularGeneralMetricC2PairedMinimalPhysicalOpenAdmissibleDomain
        period hPeriod configuration plusBase minusBase =
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain
        period hPeriod configuration plusBase minusBase := by
  ext direction
  exact (globalMetricPerturbationPairLorentzChartAdmissible_iff_mem_matrixDomain
    period hPeriod configuration plusBase minusBase direction).symm

/-- Openness of the exact domain in the paired-relative graph topology. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain_isOpen
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :
    letI := globalMinimalPhysicalPairedRelativeMetricCoreNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
    letI := globalMinimalPhysicalPairedRelativeMetricCoreNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
    IsOpen (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain
      period hPeriod configuration.physical plusBase minusBase) := by
  letI := globalMinimalPhysicalPairedRelativeMetricCoreNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
  letI := globalMinimalPhysicalPairedRelativeMetricCoreNormedSpace period
    hPeriod configuration data analysis realization plusBase minusBase
  rw [← regularGeneralMetricC2PairedMinimalPhysicalOpenAdmissibleDomain_eq
    period hPeriod configuration.physical plusBase minusBase]
  change IsOpen
    ((globalMinimalPhysicalPairedRelativeMetricCoreCLM period hPeriod
        configuration data analysis realization plusBase minusBase) ⁻¹'
      regularGeneralMetricC2PairedLorentzMatrixDomain
        period hPeriod plusBase minusBase)
  exact (regularGeneralMetricC2PairedLorentzMatrixDomain_isOpen
    period hPeriod plusBase minusBase).preimage
      (globalMinimalPhysicalPairedRelativeMetricCoreCLM period hPeriod
        configuration data analysis realization plusBase minusBase).continuous

/-- Gate marker: the exact paired T03 chart locus is now an open neighborhood
of zero whenever the two base metrics are compatible. -/
theorem regular_general_metric_c2_paired_minimal_physical_admissible_domain_open_gate
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase) :
    letI := globalMinimalPhysicalPairedRelativeMetricCoreNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
    letI := globalMinimalPhysicalPairedRelativeMetricCoreNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
    IsOpen (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain
        period hPeriod configuration.physical plusBase minusBase) ∧
      (0 : GlobalMinimalPhysicalFieldTangent period hPeriod
        configuration.physical) ∈
        regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain
          period hPeriod configuration.physical plusBase minusBase := by
  letI := globalMinimalPhysicalPairedRelativeMetricCoreNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
  letI := globalMinimalPhysicalPairedRelativeMetricCoreNormedSpace period
    hPeriod configuration data analysis realization plusBase minusBase
  exact ⟨regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain_isOpen
      period hPeriod configuration data analysis realization plusBase minusBase,
    zero_mem_regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain
      period hPeriod configuration.physical plusBase minusBase hBase⟩

end

end P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomainOpen4D
end JanusFormal
