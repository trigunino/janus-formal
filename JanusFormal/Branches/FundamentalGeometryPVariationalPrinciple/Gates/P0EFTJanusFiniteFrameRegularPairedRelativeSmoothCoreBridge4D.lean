import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2PhysicalEulerThreeBlockSplit4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalRelativeMetricCoreProjection4D

/-! # Smooth-core bridge between finite-frame and regular paired-relative charts -/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameRegularPairedRelativeSmoothCoreBridge4D

set_option autoImplicit false
set_option maxHeartbeats 3000000
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

/-- Two finite-frame coefficients and one regular paired-relative core encode
the same smooth tensor pair. -/
def finiteFrameRegularPairedRelativeSmoothCompatible
    (finite : FinitePair) (regular : RegularRelative) : Prop :=
  ∃ plusVariation minusVariation : SmoothSymmetricCovariantTwoTensor period hPeriod,
    finite.1 = smoothToGeneralMetricRelativeC2Core period hPeriod frame plusBase.metric
      plusVariation ∧
    finite.2 = smoothToGeneralMetricRelativeC2Core period hPeriod frame plusBase.metric
      minusVariation ∧
    regular.1.1 = regularGeneralMetricSmoothC2Variation period hPeriod plusBase plusVariation ∧
    regular.1.2 = regularGeneralMetricSmoothC2Variation period hPeriod minusBase minusVariation ∧
    regular.2.1 = regularGeneralMetricC2VariationMatrix period hPeriod plusBase plusVariation ∧
    regular.2.2 =
      regularGeneralMetricC2VariationMatrix period hPeriod plusBase minusVariation -
        regularGeneralMetricC2VariationMatrix period hPeriod plusBase plusVariation

/-- Every smooth tensor pair has compatible representatives in both charts. -/
theorem finiteFrameRegularPairedRelativeSmoothCompatible_lifts
    (plusVariation minusVariation : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    finiteFrameRegularPairedRelativeSmoothCompatible period hPeriod frame plusBase minusBase
      (smoothToGeneralMetricRelativeC2Core period hPeriod frame plusBase.metric plusVariation,
        smoothToGeneralMetricRelativeC2Core period hPeriod frame plusBase.metric minusVariation)
      ((regularGeneralMetricSmoothC2Variation period hPeriod plusBase plusVariation,
          regularGeneralMetricSmoothC2Variation period hPeriod minusBase minusVariation),
        (regularGeneralMetricC2VariationMatrix period hPeriod plusBase plusVariation,
          regularGeneralMetricC2VariationMatrix period hPeriod plusBase minusVariation -
            regularGeneralMetricC2VariationMatrix period hPeriod plusBase plusVariation)) := by
  exact ⟨plusVariation, minusVariation, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A smooth finite-frame representative determines at most one regular relative representative. -/
theorem finiteFrameRegularPairedRelativeSmoothCompatible_right_unique
    (finite : FinitePair) (first second : RegularRelative)
    (hFirst : finiteFrameRegularPairedRelativeSmoothCompatible period hPeriod frame plusBase
      minusBase finite first)
    (hSecond : finiteFrameRegularPairedRelativeSmoothCompatible period hPeriod frame plusBase
      minusBase finite second) : first = second := by
  rcases hFirst with ⟨plusFirst, minusFirst, hFinitePlusFirst, hFiniteMinusFirst,
    hFirstPlus, hFirstMinus, hFirstMatrix, hFirstCross⟩
  rcases hSecond with ⟨plusSecond, minusSecond, hFinitePlusSecond, hFiniteMinusSecond,
    hSecondPlus, hSecondMinus, hSecondMatrix, hSecondCross⟩
  have hPlus : plusFirst = plusSecond :=
    (smoothToGeneralMetricRelativeC2Core_injective period hPeriod frame plusBase.metric)
      (hFinitePlusFirst.symm.trans hFinitePlusSecond)
  have hMinus : minusFirst = minusSecond :=
    (smoothToGeneralMetricRelativeC2Core_injective period hPeriod frame plusBase.metric)
      (hFiniteMinusFirst.symm.trans hFiniteMinusSecond)
  subst plusSecond
  subst minusSecond
  apply Prod.ext
  · apply Prod.ext
    · exact hFirstPlus.trans hSecondPlus.symm
    · exact hFirstMinus.trans hSecondMinus.symm
  · apply Prod.ext
    · exact hFirstMatrix.trans hSecondMatrix.symm
    · exact hFirstCross.trans hSecondCross.symm

/-- A smooth regular relative representative determines at most one finite-frame representative. -/
theorem finiteFrameRegularPairedRelativeSmoothCompatible_left_unique
    (first second : FinitePair) (regular : RegularRelative)
    (hFirst : finiteFrameRegularPairedRelativeSmoothCompatible period hPeriod frame plusBase
      minusBase first regular)
    (hSecond : finiteFrameRegularPairedRelativeSmoothCompatible period hPeriod frame plusBase
      minusBase second regular) : first = second := by
  rcases hFirst with ⟨plusFirst, minusFirst, hFinitePlusFirst, hFiniteMinusFirst,
    hRegularPlusFirst, hRegularMinusFirst, _, _⟩
  rcases hSecond with ⟨plusSecond, minusSecond, hFinitePlusSecond, hFiniteMinusSecond,
    hRegularPlusSecond, hRegularMinusSecond, _, _⟩
  have hPlus : plusFirst = plusSecond :=
    (smoothToGeneralMetricRelativeC2Core_injective period hPeriod
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod plusBase) plusBase.metric)
        (hRegularPlusFirst.symm.trans hRegularPlusSecond)
  have hMinus : minusFirst = minusSecond :=
    (smoothToGeneralMetricRelativeC2Core_injective period hPeriod
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod minusBase) minusBase.metric)
        (hRegularMinusFirst.symm.trans hRegularMinusSecond)
  subst plusSecond
  subst minusSecond
  apply Prod.ext
  · exact hFinitePlusFirst.trans hFinitePlusSecond.symm
  · exact hFiniteMinusFirst.trans hFiniteMinusSecond.symm

/-- The origins of both paired-relative charts are compatible. -/
theorem zero_finiteFrameRegularPairedRelativeSmoothCompatible :
    finiteFrameRegularPairedRelativeSmoothCompatible period hPeriod frame plusBase minusBase 0 0 := by
  have hPlusCore : regularGeneralMetricSmoothC2Variation period hPeriod plusBase 0 = 0 := by
    unfold regularGeneralMetricSmoothC2Variation
    exact map_zero _
  have hMinusCore : regularGeneralMetricSmoothC2Variation period hPeriod minusBase 0 = 0 := by
    unfold regularGeneralMetricSmoothC2Variation
    exact map_zero _
  have hPlusMatrix : regularGeneralMetricC2VariationMatrix period hPeriod plusBase 0 = 0 := by
    unfold regularGeneralMetricC2VariationMatrix
    rw [hPlusCore]
    rfl
  refine ⟨0, 0, ?_, ?_, hPlusCore.symm, hMinusCore.symm, hPlusMatrix.symm, ?_⟩
  · exact (map_zero (smoothToGeneralMetricRelativeC2Core period hPeriod frame plusBase.metric)).symm
  · exact (map_zero (smoothToGeneralMetricRelativeC2Core period hPeriod frame plusBase.metric)).symm
  · rw [hPlusMatrix]
    simp

end
end P0EFTJanusFiniteFrameRegularPairedRelativeSmoothCoreBridge4D
end JanusFormal
