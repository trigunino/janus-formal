import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D

/-! # Positive canonical-volume ratio on the completed metric chart

Taking the absolute value of the selected nonzero root removes any dependence
on its sign. Locally this operation multiplies by a fixed continuous sign, so
the resulting canonical-volume feature is C² on the full existing metric domain.
-/

namespace JanusFormal
namespace P0EFTJanusVariableMetricCanonicalVolumeRatio4D

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 600000

noncomputable section
open Set Filter
open scoped Topology Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2LocalRoot4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDensity4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D

section ContinuousAbsoluteValue
variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

def continuousScalarAbs (field : C(X, Real)) : C(X, Real) :=
  ⟨fun point => |field point|, field.continuous.abs⟩

/-- Away from zero, pointwise absolute value is locally a fixed multiplication operator. -/
theorem continuousScalarAbs_contDiffAt (order : WithTop ℕ∞) (field : C(X, Real))
    (hNonzero : ∀ point, field point ≠ 0) :
    ContDiffAt Real order continuousScalarAbs field := by
  let sign : C(X, Real) :=
    ⟨fun point => field point / |field point|,
      field.continuous.div field.continuous.abs (fun point => abs_ne_zero.mpr (hNonzero point))⟩
  have hPositiveOpen : IsOpen {value : C(X, Real) | ∀ point, 0 < value point} := by
    simpa only [range_subset_iff, mem_Ioi] using
      (ContinuousMap.isOpen_setOf_range_subset (X := X) (isOpen_Ioi : IsOpen (Ioi (0 : Real))))
  have hNeighborhood : {value : C(X, Real) | ∀ point, 0 < value point * field point} ∈
      𝓝 field :=
    (hPositiveOpen.preimage (continuous_id.mul continuous_const)).mem_nhds
      (fun point => mul_self_pos.mpr (hNonzero point))
  have hEqual : continuousScalarAbs =ᶠ[𝓝 field] (fun value => sign * value) := by
    filter_upwards [hNeighborhood] with value hValue
    apply ContinuousMap.ext
    intro point
    rcases mul_pos_iff.mp (hValue point) with ⟨hValuePos, hFieldPos⟩ | ⟨hValueNeg, hFieldNeg⟩
    · simp [continuousScalarAbs, sign, abs_of_pos hValuePos, abs_of_pos hFieldPos,
        ne_of_gt hFieldPos]
    · simp [continuousScalarAbs, sign, abs_of_neg hValueNeg, abs_of_neg hFieldNeg,
        ne_of_lt hFieldNeg]
  exact (contDiff_const.mul contDiff_id).contDiffAt.congr_of_eventuallyEq hEqual

end ContinuousAbsoluteValue

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C0Scalar := C(EffectiveQuotient period hPeriod, Real)
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

private theorem regularRoot_continuous_ne_zero (root : C2Scalar period hPeriod)
    (hRegular : root ∈ c2ScalarSylvesterRegularSet period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod root point ≠ 0 := by
  rcases hRegular with ⟨equiv, hEquiv⟩
  have hOne : c2ScalarSylvesterFamily period hPeriod root
      (equiv.symm (c2ScalarOne period hPeriod)) = c2ScalarOne period hPeriod := by
    rw [← hEquiv]
    exact equiv.apply_symm_apply _
  have hValue := congrArg (fun value : C2Scalar period hPeriod =>
    canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod value point) hOne
  change canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod root point *
        canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
          (equiv.symm (c2ScalarOne period hPeriod)) point +
      canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
          (equiv.symm (c2ScalarOne period hPeriod)) point *
        canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod root point = 1 at hValue
  intro hZero
  rw [hZero] at hValue
  norm_num at hValue

theorem regularMetricVolumeRoot_continuous_ne_zero
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (variation : RegularGeneralMetricC2Core period hPeriod reference)
    (hVariation : variation ∈ regularGeneralMetricC2Domain period hPeriod reference)
    (point : EffectiveQuotient period hPeriod) :
    canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
      (generalMetricRelativeC2VolumeRatio period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference)
        reference.metric variation) point ≠ 0 := by
  have hSource := (c2ScalarLocalSquareChart period hPeriod).map_target hVariation.2
  rw [c2ScalarLocalSquareChart, OpenPartialHomeomorph.restrOpen_source] at hSource
  exact regularRoot_continuous_ne_zero period hPeriod _ hSource.2 point

/-- Canonical reference density times the positive relative metric-volume root. -/
def variableMetricCanonicalVolumeRatio
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (variation : RegularGeneralMetricC2Core period hPeriod reference) :
    C0Scalar period hPeriod :=
  smoothToCanonicalPhysicalContinuousScalar period hPeriod
      (globalSmoothMetricVolumeRatio period hPeriod reference.metric) *
    continuousScalarAbs (canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
      (generalMetricRelativeC2VolumeRatio period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference)
        reference.metric variation))

theorem variableMetricCanonicalVolumeRatio_contDiffOn_two
    (reference : RegularGeneralLorentzMetric period hPeriod) :
    ContDiffOn Real 2 (variableMetricCanonicalVolumeRatio period hPeriod reference)
      (regularGeneralMetricC2Domain period hPeriod reference) := by
  have hRoot := (canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod).contDiff.comp_contDiffOn
    (generalMetricRelativeC2VolumeRatio_contDiffOn_two period hPeriod
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference) reference.metric)
  intro variation hVariation
  apply ContDiffWithinAt.mul contDiffWithinAt_const
  exact (continuousScalarAbs_contDiffAt 2 _
    (regularMetricVolumeRoot_continuous_ne_zero period hPeriod reference variation hVariation)).comp_contDiffWithinAt
      variation (hRoot variation hVariation)

theorem variableMetricCanonicalVolumeRatio_pos
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (variation : RegularGeneralMetricC2Core period hPeriod reference)
    (hVariation : variation ∈ regularGeneralMetricC2Domain period hPeriod reference)
    (point : EffectiveQuotient period hPeriod) :
    0 < variableMetricCanonicalVolumeRatio period hPeriod reference variation point :=
  mul_pos (globalMetricVolumeRatio_pos period hPeriod reference.metric point)
    (abs_pos.mpr (regularMetricVolumeRoot_continuous_ne_zero period hPeriod reference
      variation hVariation point))

end
end P0EFTJanusVariableMetricCanonicalVolumeRatio4D
end JanusFormal
