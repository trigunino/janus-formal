import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameRegularPairedRelativeSmoothCoreBridge4D

/-! # Linear graph of the finite-frame/regular paired-relative smooth bridge -/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameRegularPairedRelativeSmoothGraph4D

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1200000
noncomputable section
open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootLift4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalRelativeMetricCoreProjection4D
open P0EFTJanusFiniteFrameRegularPairedRelativeSmoothCoreBridge4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance
local instance : CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

variable (frame : SmoothD8Frame period hPeriod)
  (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
local notation "FinitePair" =>
  GeneralMetricRelativeC2Core period hPeriod frame plusBase.metric ×
    GeneralMetricRelativeC2Core period hPeriod frame plusBase.metric
local notation "RegularRelative" =>
  RegularGeneralMetricC2PairedRelativeCore period hPeriod plusBase minusBase

private theorem regularSmooth_add
    (base : RegularGeneralLorentzMetric period hPeriod)
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    regularGeneralMetricSmoothC2Variation period hPeriod base (first + second) =
      regularGeneralMetricSmoothC2Variation period hPeriod base first +
        regularGeneralMetricSmoothC2Variation period hPeriod base second := by
  unfold regularGeneralMetricSmoothC2Variation
  exact LinearMap.map_add _ _ _

private theorem regularSmooth_smul
    (base : RegularGeneralLorentzMetric period hPeriod) (scalar : Real)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    regularGeneralMetricSmoothC2Variation period hPeriod base (scalar • tensor) =
      scalar • regularGeneralMetricSmoothC2Variation period hPeriod base tensor := by
  unfold regularGeneralMetricSmoothC2Variation
  exact LinearMap.map_smul _ _ _

private theorem regularMatrix_add
    (base : RegularGeneralLorentzMetric period hPeriod)
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    regularGeneralMetricC2VariationMatrix period hPeriod base (first + second) =
      regularGeneralMetricC2VariationMatrix period hPeriod base first +
        regularGeneralMetricC2VariationMatrix period hPeriod base second := by
  unfold regularGeneralMetricC2VariationMatrix
  rw [regularSmooth_add]
  rfl

private theorem regularMatrix_smul
    (base : RegularGeneralLorentzMetric period hPeriod) (scalar : Real)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    regularGeneralMetricC2VariationMatrix period hPeriod base (scalar • tensor) =
      scalar • regularGeneralMetricC2VariationMatrix period hPeriod base tensor := by
  unfold regularGeneralMetricC2VariationMatrix
  rw [regularSmooth_smul]
  rfl

/-- Compatibility is closed under addition. -/
theorem finiteFrameRegularPairedRelativeSmoothCompatible_add
    {finiteFirst finiteSecond : FinitePair} {regularFirst regularSecond : RegularRelative}
    (hFirst : finiteFrameRegularPairedRelativeSmoothCompatible period hPeriod frame plusBase
      minusBase finiteFirst regularFirst)
    (hSecond : finiteFrameRegularPairedRelativeSmoothCompatible period hPeriod frame plusBase
      minusBase finiteSecond regularSecond) :
    finiteFrameRegularPairedRelativeSmoothCompatible period hPeriod frame plusBase minusBase
      (finiteFirst + finiteSecond) (regularFirst + regularSecond) := by
  rcases hFirst with ⟨plusFirst, minusFirst, hFinitePlusFirst, hFiniteMinusFirst,
    hRegularPlusFirst, hRegularMinusFirst, hMatrixFirst, hCrossFirst⟩
  rcases hSecond with ⟨plusSecond, minusSecond, hFinitePlusSecond, hFiniteMinusSecond,
    hRegularPlusSecond, hRegularMinusSecond, hMatrixSecond, hCrossSecond⟩
  refine ⟨plusFirst + plusSecond, minusFirst + minusSecond, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change finiteFirst.1 + finiteSecond.1 = _
    rw [hFinitePlusFirst, hFinitePlusSecond, LinearMap.map_add]
  · change finiteFirst.2 + finiteSecond.2 = _
    rw [hFiniteMinusFirst, hFiniteMinusSecond, LinearMap.map_add]
  · change regularFirst.1.1 + regularSecond.1.1 = _
    rw [hRegularPlusFirst, hRegularPlusSecond, regularSmooth_add]
  · change regularFirst.1.2 + regularSecond.1.2 = _
    rw [hRegularMinusFirst, hRegularMinusSecond, regularSmooth_add]
  · change regularFirst.2.1 + regularSecond.2.1 = _
    rw [hMatrixFirst, hMatrixSecond, regularMatrix_add]
  · change regularFirst.2.2 + regularSecond.2.2 = _
    rw [hCrossFirst, hCrossSecond, regularMatrix_add, regularMatrix_add]
    abel

/-- Compatibility is closed under real scalar multiplication. -/
theorem finiteFrameRegularPairedRelativeSmoothCompatible_smul
    (scalar : Real) {finite : FinitePair} {regular : RegularRelative}
    (hCompatible : finiteFrameRegularPairedRelativeSmoothCompatible period hPeriod frame plusBase
      minusBase finite regular) :
    finiteFrameRegularPairedRelativeSmoothCompatible period hPeriod frame plusBase minusBase
      (scalar • finite) (scalar • regular) := by
  rcases hCompatible with ⟨plusVariation, minusVariation, hFinitePlus, hFiniteMinus,
    hRegularPlus, hRegularMinus, hMatrix, hCross⟩
  refine ⟨scalar • plusVariation, scalar • minusVariation, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change scalar • finite.1 = _
    rw [hFinitePlus, LinearMap.map_smul]
  · change scalar • finite.2 = _
    rw [hFiniteMinus, LinearMap.map_smul]
  · change scalar • regular.1.1 = _
    rw [hRegularPlus, regularSmooth_smul]
  · change scalar • regular.1.2 = _
    rw [hRegularMinus, regularSmooth_smul]
  · change scalar • regular.2.1 = _
    rw [hMatrix, regularMatrix_smul]
  · change scalar • regular.2.2 = _
    rw [hCross, regularMatrix_smul, regularMatrix_smul, smul_sub]

/-- Linear graph of compatible smooth representatives. -/
def finiteFrameRegularPairedRelativeSmoothGraph :
    Submodule Real (FinitePair × RegularRelative) where
  carrier pair := finiteFrameRegularPairedRelativeSmoothCompatible period hPeriod frame plusBase
    minusBase pair.1 pair.2
  zero_mem' := zero_finiteFrameRegularPairedRelativeSmoothCompatible period hPeriod frame plusBase
    minusBase
  add_mem' hFirst hSecond :=
    finiteFrameRegularPairedRelativeSmoothCompatible_add period hPeriod frame plusBase minusBase
      hFirst hSecond
  smul_mem' scalar _ hCompatible :=
    finiteFrameRegularPairedRelativeSmoothCompatible_smul period hPeriod frame plusBase minusBase
      scalar hCompatible

/-- The finite-frame projection of the smooth graph is injective. -/
theorem finiteFrameRegularPairedRelativeSmoothGraph_finite_injective :
    Function.Injective (fun pair : finiteFrameRegularPairedRelativeSmoothGraph period hPeriod frame
      plusBase minusBase => pair.1.1) := by
  intro first second hFinite
  change first.1.1 = second.1.1 at hFinite
  apply Subtype.ext
  apply Prod.ext
  · exact hFinite
  · exact finiteFrameRegularPairedRelativeSmoothCompatible_right_unique period hPeriod frame
      plusBase minusBase first.1.1 first.1.2 second.1.2 first.2 (hFinite.symm ▸ second.2)

/-- The regular paired-relative projection of the smooth graph is injective. -/
theorem finiteFrameRegularPairedRelativeSmoothGraph_regular_injective :
    Function.Injective (fun pair : finiteFrameRegularPairedRelativeSmoothGraph period hPeriod frame
      plusBase minusBase => pair.1.2) := by
  intro first second hRegular
  change first.1.2 = second.1.2 at hRegular
  apply Subtype.ext
  apply Prod.ext
  · exact finiteFrameRegularPairedRelativeSmoothCompatible_left_unique period hPeriod frame
      plusBase minusBase first.1.1 second.1.1 first.1.2 first.2 (hRegular.symm ▸ second.2)
  · exact hRegular

end
end P0EFTJanusFiniteFrameRegularPairedRelativeSmoothGraph4D
end JanusFormal
