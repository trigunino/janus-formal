import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalMetricTangentIntrinsicEmbedding4D

/-!
# Dense normal-boundary core in the gauge-fixed physical tangent

The completed normal-boundary core has no synthesis map back to smooth
fields.  This file records the strongest canonical raccord already available:
its genuine smooth dense core embeds faithfully both in the completion and in
the corrected gauge-fixed physical tangent.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateANormalBoundaryGaugeFixedTangentDenseRaccord4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusCompleteVariationModuleCore4D
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusProgramPSpinorialCompleteVariation4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D

variable (period : Real) (hPeriod : period ≠ 0)

abbrev CandidateANormalBoundarySmoothCore :=
  SmoothSymmetricCovariantTwoTensor period hPeriod ×
    SmoothNormalDisplacement period hPeriod

local instance boundaryCoreNormedAddCommGroup
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    period hPeriod metric

local instance boundaryCoreNormedSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedSpace period hPeriod metric

/-- Put one smooth boundary metric/normal pair diagonally in the two Program-P
sectors, with every unrelated complete-variation slot fixed to zero. -/
def candidateANormalBoundarySmoothCompleteLinearMap :
    CandidateANormalBoundarySmoothCore period hPeriod →ₗ[Real]
      ProgramPCompleteVariation4D period hPeriod where
  toFun variation :=
    { (0 : ProgramPCompleteVariation4D period hPeriod) with
      normalDisplacement := fun _ ↦ variation.2
      fullMetricPerturbation := fun _ ↦ variation.1 }
  map_add' first second := by
    have hZero :
        (0 : ProgramPCompleteVariation4D period hPeriod) = 0 + 0 :=
      (zero_add 0).symm
    apply ProgramPCompleteVariation4D.ext
    · change
        (0 : ProgramPCompleteVariation4D period hPeriod).independent =
          (0 + 0 : ProgramPCompleteVariation4D period hPeriod).independent
      exact congrArg ProgramPCompleteVariation4D.independent hZero
    · rfl
    · change
        (0 : ProgramPCompleteVariation4D period hPeriod).diffeomorphismGhost =
          (0 + 0 : ProgramPCompleteVariation4D period hPeriod
            ).diffeomorphismGhost
      exact congrArg ProgramPCompleteVariation4D.diffeomorphismGhost hZero
    · rfl
  map_smul' scalar variation := by
    have hZero :
        (0 : ProgramPCompleteVariation4D period hPeriod) = scalar • 0 :=
      (smul_zero scalar).symm
    apply ProgramPCompleteVariation4D.ext
    · change
        (0 : ProgramPCompleteVariation4D period hPeriod).independent =
          (scalar • (0 : ProgramPCompleteVariation4D period hPeriod)
            ).independent
      exact congrArg ProgramPCompleteVariation4D.independent hZero
    · rfl
    · change
        (0 : ProgramPCompleteVariation4D period hPeriod).diffeomorphismGhost =
          (scalar • (0 : ProgramPCompleteVariation4D period hPeriod)
            ).diffeomorphismGhost
      exact congrArg ProgramPCompleteVariation4D.diffeomorphismGhost hZero
    · rfl

def candidateANormalBoundarySmoothMatterFreeLinearMap :
    CandidateANormalBoundarySmoothCore period hPeriod →ₗ[Real]
      MatterFreeCompleteVariation period hPeriod where
  toFun variation :=
    ⟨candidateANormalBoundarySmoothCompleteLinearMap
      period hPeriod variation, rfl⟩
  map_add' first second := Subtype.ext
    ((candidateANormalBoundarySmoothCompleteLinearMap
      period hPeriod).map_add first second)
  map_smul' scalar variation := Subtype.ext
    ((candidateANormalBoundarySmoothCompleteLinearMap
      period hPeriod).map_smul scalar variation)

def candidateANormalBoundarySmoothGeneralMetricLinearMap :
    CandidateANormalBoundarySmoothCore period hPeriod →ₗ[Real]
      GeneralMetricMatterFreeVariation period hPeriod where
  toFun variation :=
    ⟨candidateANormalBoundarySmoothMatterFreeLinearMap
      period hPeriod variation, rfl⟩
  map_add' first second := Subtype.ext
    ((candidateANormalBoundarySmoothMatterFreeLinearMap
      period hPeriod).map_add first second)
  map_smul' scalar variation := Subtype.ext
    ((candidateANormalBoundarySmoothMatterFreeLinearMap
      period hPeriod).map_smul scalar variation)

def candidateANormalBoundarySmoothPhysicalTangentLinearMap
    (configuration : GlobalFieldConfiguration period hPeriod) :
    CandidateANormalBoundarySmoothCore period hPeriod →ₗ[Real]
      GlobalPhysicalFieldTangent period hPeriod configuration :=
  (LinearMap.inl Real
      (GeneralMetricMatterFreeVariation period hPeriod)
      (Sector →
        D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter)).comp
    (candidateANormalBoundarySmoothGeneralMetricLinearMap period hPeriod)

def candidateANormalBoundarySmoothMinimalTangentLinearMap
    (configuration : GlobalFieldConfiguration period hPeriod) :
    CandidateANormalBoundarySmoothCore period hPeriod →ₗ[Real]
      GlobalMinimalPhysicalFieldTangent period hPeriod configuration where
  toFun variation :=
    ⟨candidateANormalBoundarySmoothPhysicalTangentLinearMap
      period hPeriod configuration variation, rfl⟩
  map_add' first second := Subtype.ext
    ((candidateANormalBoundarySmoothPhysicalTangentLinearMap
      period hPeriod configuration).map_add first second)
  map_smul' scalar variation := Subtype.ext
    ((candidateANormalBoundarySmoothPhysicalTangentLinearMap
      period hPeriod configuration).map_smul scalar variation)

/-- The real smooth normal-boundary direction in the corrected typed tangent. -/
def candidateANormalBoundarySmoothGaugeFixedTangentLinearMap
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) :
    CandidateANormalBoundarySmoothCore period hPeriod →ₗ[Real]
      GlobalGaugeFixedPhysicalFieldTangent period hPeriod configuration :=
  (globalGaugeFixedPhysicalTangentPhysicalInclusionLinearMap
      period hPeriod configuration).comp
    (candidateANormalBoundarySmoothMinimalTangentLinearMap
      period hPeriod configuration.physical)

@[simp] theorem candidateANormalBoundarySmoothGaugeFixedTangent_metric
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (variation : CandidateANormalBoundarySmoothCore period hPeriod)
    (sector : Sector) :
    (GlobalPhysicalFieldTangent.completeVariation period hPeriod
      (candidateANormalBoundarySmoothGaugeFixedTangentLinearMap
        period hPeriod configuration variation).1.1).fullMetricPerturbation
          sector = variation.1 :=
  rfl

@[simp] theorem candidateANormalBoundarySmoothGaugeFixedTangent_normal
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (variation : CandidateANormalBoundarySmoothCore period hPeriod)
    (sector : Sector) :
    (GlobalPhysicalFieldTangent.completeVariation period hPeriod
      (candidateANormalBoundarySmoothGaugeFixedTangentLinearMap
        period hPeriod configuration variation).1.1).normalDisplacement
          sector = variation.2 :=
  rfl

theorem candidateANormalBoundarySmoothGaugeFixedTangentLinearMap_injective
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) :
    Function.Injective
      (candidateANormalBoundarySmoothGaugeFixedTangentLinearMap
        period hPeriod configuration) := by
  intro first second hEqual
  apply Prod.ext
  · have hMetric := congrArg
      (fun variation : GlobalGaugeFixedPhysicalFieldTangent
          period hPeriod configuration ↦
        (GlobalPhysicalFieldTangent.completeVariation period hPeriod
          variation.1.1).fullMetricPerturbation Sector.plus) hEqual
    simpa using hMetric
  · have hNormal := congrArg
      (fun variation : GlobalGaugeFixedPhysicalFieldTangent
          period hPeriod configuration ↦
        (GlobalPhysicalFieldTangent.completeVariation period hPeriod
          variation.1.1).normalDisplacement Sector.plus) hEqual
    simpa using hNormal

/-- The common smooth core with both faithful realizations retained. -/
def candidateANormalBoundaryGaugeFixedTangentDenseRaccordLinearMap
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) :
    CandidateANormalBoundarySmoothCore period hPeriod →ₗ[Real]
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric ×
        GlobalGaugeFixedPhysicalFieldTangent period hPeriod configuration) where
  toFun variation :=
    (smoothToCandidateANormalBoundaryFunctionalCore
        period hPeriod metric variation,
      candidateANormalBoundarySmoothGaugeFixedTangentLinearMap
        period hPeriod configuration variation)
  map_add' first second := by
    apply Prod.ext
    · exact (smoothToCandidateANormalBoundaryFunctionalCore
        period hPeriod metric).map_add first second
    · exact (candidateANormalBoundarySmoothGaugeFixedTangentLinearMap
        period hPeriod configuration).map_add first second
  map_smul' scalar variation := by
    apply Prod.ext
    · exact (smoothToCandidateANormalBoundaryFunctionalCore
        period hPeriod metric).map_smul scalar variation
    · exact (candidateANormalBoundarySmoothGaugeFixedTangentLinearMap
        period hPeriod configuration).map_smul scalar variation

/-- Public dense-raccord checkpoint.  Density is asserted only in the actual
normal-boundary completion; no nonexistent synthesis map is introduced. -/
theorem global_candidateA_normal_boundary_gauge_fixed_tangent_dense_raccord_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) :
    Function.Injective
        (candidateANormalBoundaryGaugeFixedTangentDenseRaccordLinearMap
          period hPeriod metric configuration) ∧
      DenseRange
        (smoothToCandidateANormalBoundaryFunctionalCore
          period hPeriod metric) ∧
      Function.Injective
        (candidateANormalBoundarySmoothGaugeFixedTangentLinearMap
          period hPeriod configuration) := by
  refine ⟨?_, smoothToCandidateANormalBoundaryFunctionalCore_denseRange
    period hPeriod metric,
    candidateANormalBoundarySmoothGaugeFixedTangentLinearMap_injective
      period hPeriod configuration⟩
  intro first second hEqual
  apply smoothToCandidateANormalBoundaryFunctionalCore_injective
    period hPeriod metric
  exact congrArg Prod.fst hEqual

end
end P0EFTJanusProgramPGlobalCandidateANormalBoundaryGaugeFixedTangentDenseRaccord4D
end JanusFormal
