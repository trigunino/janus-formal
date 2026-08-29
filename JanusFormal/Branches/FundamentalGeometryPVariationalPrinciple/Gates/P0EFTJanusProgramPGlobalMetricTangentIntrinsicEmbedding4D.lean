import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCompleteVariationGlobalMetricD9Projection4D

/-!
# Intrinsic metric directions inside the corrected global tangent

The already constructed complete-variation bridge inserts one genuine smooth
symmetric metric perturbation in each sector.  This gate restricts that bridge
through the existing matter-free and duplicate-nonminimal kernels, then into
the typed gauge-fixed tangent with zero nonminimal variation.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalMetricTangentIntrinsicEmbedding4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusCompleteVariationGlobalMetricD9Projection4D
open P0EFTJanusIndependentCompleteVariationEmbedding4D
open P0EFTJanusCompleteVariationModuleCore4D
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPSpinorialCompleteVariation4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- The two independent smooth metric perturbations. -/
abbrev GlobalMetricPerturbationPair :=
  Sector → SmoothSymmetricCovariantTwoTensor period hPeriod

/-- The complete-variation metric slot, specialized to zero in every other
field direction.  This is the linear specialization of
`completeVariationWithGlobalMetric`. -/
def globalMetricPerturbationCompleteLinearMap :
  GlobalMetricPerturbationPair period hPeriod →ₗ[Real]
      ProgramPCompleteVariation4D period hPeriod where
  toFun metric :=
    { (0 : ProgramPCompleteVariation4D period hPeriod) with
      fullMetricPerturbation := metric }
  map_add' first second := by
    have hZero :
        (0 : ProgramPCompleteVariation4D period hPeriod) =
          0 + 0 :=
      (zero_add 0).symm
    apply ProgramPCompleteVariation4D.ext
    · change
        (0 : ProgramPCompleteVariation4D period hPeriod).independent =
          (0 + 0 : ProgramPCompleteVariation4D period hPeriod).independent
      exact congrArg ProgramPCompleteVariation4D.independent hZero
    · change
        (0 : ProgramPCompleteVariation4D period hPeriod).normalDisplacement =
          (0 + 0 : ProgramPCompleteVariation4D period hPeriod
            ).normalDisplacement
      exact congrArg ProgramPCompleteVariation4D.normalDisplacement hZero
    · change
        (0 : ProgramPCompleteVariation4D period hPeriod).diffeomorphismGhost =
          (0 + 0 : ProgramPCompleteVariation4D period hPeriod
            ).diffeomorphismGhost
      exact congrArg ProgramPCompleteVariation4D.diffeomorphismGhost hZero
    · rfl
  map_smul' scalar metric := by
    have hZero :
        (0 : ProgramPCompleteVariation4D period hPeriod) =
          scalar • 0 :=
      (smul_zero scalar).symm
    apply ProgramPCompleteVariation4D.ext
    · change
        (0 : ProgramPCompleteVariation4D period hPeriod).independent =
          (scalar • (0 : ProgramPCompleteVariation4D period hPeriod)
            ).independent
      exact congrArg ProgramPCompleteVariation4D.independent hZero
    · change
        (0 : ProgramPCompleteVariation4D period hPeriod).normalDisplacement =
          (scalar • (0 : ProgramPCompleteVariation4D period hPeriod)
            ).normalDisplacement
      exact congrArg ProgramPCompleteVariation4D.normalDisplacement hZero
    · change
        (0 : ProgramPCompleteVariation4D period hPeriod).diffeomorphismGhost =
          (scalar • (0 : ProgramPCompleteVariation4D period hPeriod)
            ).diffeomorphismGhost
      exact congrArg ProgramPCompleteVariation4D.diffeomorphismGhost hZero
    · rfl

@[simp]
theorem globalMetricPerturbationCompleteLinearMap_metric
    (metric : GlobalMetricPerturbationPair period hPeriod) :
    (globalMetricPerturbationCompleteLinearMap
      period hPeriod metric).fullMetricPerturbation =
      metric :=
  rfl

/-- The linear metric-slot insertion is exactly the previously constructed
global-metric complete variation at zero independent direction. -/
theorem globalMetricPerturbationCompleteLinearMap_eq_existing
    (metric : GlobalMetricPerturbationPair period hPeriod) :
    globalMetricPerturbationCompleteLinearMap period hPeriod metric =
      completeVariationWithGlobalMetric period hPeriod 0 metric := by
  have hZero :
      independentCompleteVariation period hPeriod
          (0 : IndependentFieldVariation period hPeriod) =
        (0 : ProgramPCompleteVariation4D period hPeriod) :=
    (independentCompleteVariationLinearMap period hPeriod).map_zero
  apply ProgramPCompleteVariation4D.ext
  · change
      (0 : ProgramPCompleteVariation4D period hPeriod).independent =
        (independentCompleteVariation period hPeriod
          (0 : IndependentFieldVariation period hPeriod)).independent
    exact congrArg ProgramPCompleteVariation4D.independent hZero.symm
  · change
      (0 : ProgramPCompleteVariation4D period hPeriod).normalDisplacement =
        (independentCompleteVariation period hPeriod
          (0 : IndependentFieldVariation period hPeriod)).normalDisplacement
    exact congrArg ProgramPCompleteVariation4D.normalDisplacement hZero.symm
  · change
      (0 : ProgramPCompleteVariation4D period hPeriod).diffeomorphismGhost =
        (independentCompleteVariation period hPeriod
          (0 : IndependentFieldVariation period hPeriod)).diffeomorphismGhost
    exact congrArg ProgramPCompleteVariation4D.diffeomorphismGhost hZero.symm
  · rfl

/-- Pure metric perturbations contain no legacy matter. -/
def globalMetricPerturbationMatterFreeLinearMap :
    GlobalMetricPerturbationPair period hPeriod →ₗ[Real]
      MatterFreeCompleteVariation period hPeriod where
  toFun metric :=
    ⟨globalMetricPerturbationCompleteLinearMap period hPeriod metric, rfl⟩
  map_add' first second := by
    apply Subtype.ext
    exact
      (globalMetricPerturbationCompleteLinearMap
        period hPeriod).map_add first second
  map_smul' scalar metric := by
    apply Subtype.ext
    exact
      (globalMetricPerturbationCompleteLinearMap
        period hPeriod).map_smul scalar metric

/-- Pure metric perturbations also contain no obsolete diagonal metric
variation. -/
def globalMetricPerturbationGeneralMetricLinearMap :
    GlobalMetricPerturbationPair period hPeriod →ₗ[Real]
      GeneralMetricMatterFreeVariation period hPeriod where
  toFun metric :=
    ⟨globalMetricPerturbationMatterFreeLinearMap
      period hPeriod metric, rfl⟩
  map_add' first second := by
    apply Subtype.ext
    exact
      (globalMetricPerturbationMatterFreeLinearMap
        period hPeriod).map_add first second
  map_smul' scalar metric := by
    apply Subtype.ext
    exact
      (globalMetricPerturbationMatterFreeLinearMap
        period hPeriod).map_smul scalar metric

/-- Pure metric direction in the D10-free physical tangent. -/
def globalMetricPerturbationPhysicalTangentLinearMap
    (configuration : GlobalFieldConfiguration period hPeriod) :
    GlobalMetricPerturbationPair period hPeriod →ₗ[Real]
      GlobalPhysicalFieldTangent period hPeriod configuration :=
  (LinearMap.inl Real
      (GeneralMetricMatterFreeVariation period hPeriod)
      (Sector →
        D9PrimitiveSpinCSmoothSection
          period hPeriod .positiveQuarter)).comp
    (globalMetricPerturbationGeneralMetricLinearMap period hPeriod)

@[simp]
theorem globalMetricPerturbationPhysicalTangentLinearMap_metric
    (configuration : GlobalFieldConfiguration period hPeriod)
    (metric : GlobalMetricPerturbationPair period hPeriod) :
    (GlobalPhysicalFieldTangent.completeVariation period hPeriod
      (globalMetricPerturbationPhysicalTangentLinearMap
        period hPeriod configuration metric)).fullMetricPerturbation =
      metric :=
  rfl

theorem globalMetricPerturbationPhysicalTangentLinearMap_injective
    (configuration : GlobalFieldConfiguration period hPeriod) :
    Function.Injective
      (globalMetricPerturbationPhysicalTangentLinearMap
        period hPeriod configuration) := by
  intro first second hEqual
  have hMetric := congrArg
    (fun variation :
        GlobalPhysicalFieldTangent period hPeriod configuration =>
      (GlobalPhysicalFieldTangent.completeVariation
        period hPeriod variation).fullMetricPerturbation)
    hEqual
  simpa using hMetric

/-- Pure metric directions lie in the corrected minimal tangent because the
legacy ghost and auxiliary coordinates stay zero. -/
def globalMetricPerturbationMinimalPhysicalTangentLinearMap
    (configuration : GlobalFieldConfiguration period hPeriod) :
    GlobalMetricPerturbationPair period hPeriod →ₗ[Real]
      GlobalMinimalPhysicalFieldTangent
        period hPeriod configuration where
  toFun metric :=
    ⟨globalMetricPerturbationPhysicalTangentLinearMap
      period hPeriod configuration metric, rfl⟩
  map_add' first second := by
    apply Subtype.ext
    exact
      (globalMetricPerturbationPhysicalTangentLinearMap
        period hPeriod configuration).map_add first second
  map_smul' scalar metric := by
    apply Subtype.ext
    exact
      (globalMetricPerturbationPhysicalTangentLinearMap
        period hPeriod configuration).map_smul scalar metric

@[simp]
theorem globalMetricPerturbationMinimalPhysicalTangentLinearMap_metric
    (configuration : GlobalFieldConfiguration period hPeriod)
    (metric : GlobalMetricPerturbationPair period hPeriod) :
    (GlobalPhysicalFieldTangent.completeVariation period hPeriod
      (globalMetricPerturbationMinimalPhysicalTangentLinearMap
        period hPeriod configuration metric).1).fullMetricPerturbation =
      metric :=
  rfl

theorem globalMetricPerturbationMinimalPhysicalTangentLinearMap_injective
    (configuration : GlobalFieldConfiguration period hPeriod) :
    Function.Injective
      (globalMetricPerturbationMinimalPhysicalTangentLinearMap
        period hPeriod configuration) := by
  intro first second hEqual
  apply globalMetricPerturbationPhysicalTangentLinearMap_injective
    period hPeriod configuration
  exact congrArg Subtype.val hEqual

/-- The same direction in the typed gauge-fixed tangent, with all nine
nonminimal variations fixed to zero. -/
def globalMetricPerturbationGaugeFixedTangentLinearMap
    (configuration :
      GlobalGaugeFixedFieldConfiguration period hPeriod) :
    GlobalMetricPerturbationPair period hPeriod →ₗ[Real]
      GlobalGaugeFixedPhysicalFieldTangent
        period hPeriod configuration :=
  (globalGaugeFixedPhysicalTangentPhysicalInclusionLinearMap
      period hPeriod configuration).comp
    (globalMetricPerturbationMinimalPhysicalTangentLinearMap
      period hPeriod configuration.physical)

@[simp]
theorem globalMetricPerturbationGaugeFixedTangentLinearMap_metric
    (configuration :
      GlobalGaugeFixedFieldConfiguration period hPeriod)
    (metric : GlobalMetricPerturbationPair period hPeriod) :
    (GlobalPhysicalFieldTangent.completeVariation period hPeriod
      (globalMetricPerturbationGaugeFixedTangentLinearMap
        period hPeriod configuration metric).1.1).fullMetricPerturbation =
      metric :=
  rfl

@[simp]
theorem globalMetricPerturbationGaugeFixedTangentLinearMap_nonminimal
    (configuration :
      GlobalGaugeFixedFieldConfiguration period hPeriod)
    (metric : GlobalMetricPerturbationPair period hPeriod) :
    (globalMetricPerturbationGaugeFixedTangentLinearMap
      period hPeriod configuration metric).2 =
      0 :=
  rfl

theorem globalMetricPerturbationGaugeFixedTangentLinearMap_injective
    (configuration :
      GlobalGaugeFixedFieldConfiguration period hPeriod) :
    Function.Injective
      (globalMetricPerturbationGaugeFixedTangentLinearMap
        period hPeriod configuration) := by
  intro first second hEqual
  apply globalMetricPerturbationMinimalPhysicalTangentLinearMap_injective
    period hPeriod configuration.physical
  exact congrArg Prod.fst hEqual

end
end P0EFTJanusProgramPGlobalMetricTangentIntrinsicEmbedding4D
end JanusFormal
