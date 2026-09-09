import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLSmoothResidualEquivalence4D

/-! # Obstruction to dense smooth LL direct/PT packets

The completed LL packet used by the polynomial action is the unrestricted
product of a direct first-jet packet and a PT first-jet packet.  The smooth
coefficient map cannot be dense in that product: already in the scalar
measure coordinate, its PT component at `x` is its direct component at
`PT x`.  This is a closed relation, and an unrestricted packet can violate it.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLSmoothDensityObstruction4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 600000
noncomputable section

open Set
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusPTInvolution
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D

attribute [local instance 2000]
  NonUnitalNormedRing.toNormedAddCommGroup NormedAlgebra.toNormedSpace

attribute [local instance 100]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance : ChartedSpace ThroatCoverModel
    (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance : IsManifold throatCoverModelWithCorners ω
    (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance : CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

private abbrev SmoothLLInput :=
  GlobalMinimalPhysicalLLSmoothCoefficientPacket period hPeriod

private abbrev LLInput
    (frame : SmoothThroatGeneratingFrame period hPeriod) :=
  GlobalMinimalPhysicalLLC0FirstJetPacket period hPeriod frame

/-- Every smooth direct/PT packet satisfies the scalar-measure compatibility
relation.  It is already enough to obstruct density in the unrestricted
product packet. -/
theorem smoothLLCoefficientPTC0FirstJetLinearMap_measure_compatible
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : SmoothLLInput period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    (smoothLLCoefficientPTC0FirstJetLinearMap period hPeriod frame fields).2.2.1
        point =
      (smoothLLCoefficientPTC0FirstJetLinearMap period hPeriod frame fields).1.2.1
        (fixedThroatPT period hPeriod point) := by
  rfl

/-- The smooth direct/PT first-jet map is not dense in the unrestricted
cartesian packet.  Its scalar-measure coordinates lie in the proper closed
PT-compatibility relation. -/
theorem smoothLLCoefficientPTC0FirstJetLinearMap_not_denseRange
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    ¬ DenseRange
      (smoothLLCoefficientPTC0FirstJetLinearMap period hPeriod frame) := by
  intro hDense
  let ptMeasureAt : LLInput period hPeriod frame → Real :=
    fun packet => packet.2.2.1 point
  let directMeasureAt : LLInput period hPeriod frame → Real :=
    fun packet => packet.1.2.1 (fixedThroatPT period hPeriod point)
  have hPtContinuous : Continuous ptMeasureAt := by
    exact (ContinuousMap.evalCLM Real point).continuous.comp
      (continuous_fst.comp (continuous_snd.comp continuous_snd))
  have hDirectContinuous : Continuous directMeasureAt := by
    exact (ContinuousMap.evalCLM Real
        (fixedThroatPT period hPeriod point)).continuous.comp
      (continuous_fst.comp (continuous_snd.comp continuous_fst))
  have hEveryPacket : ptMeasureAt = directMeasureAt :=
    hDense.equalizer hPtContinuous hDirectContinuous (by
      funext fields
      exact smoothLLCoefficientPTC0FirstJetLinearMap_measure_compatible
        period hPeriod frame fields point)
  let oneMeasure : C(EffectiveThroat period hPeriod, Real) :=
    ContinuousMap.const (EffectiveThroat period hPeriod) 1
  let incompatiblePacket : LLInput period hPeriod frame :=
    (0, (0, (oneMeasure, 0)))
  have hContradiction := congrFun hEveryPacket incompatiblePacket
  simp [ptMeasureAt, directMeasureAt, incompatiblePacket, oneMeasure] at hContradiction

/-- Gate 803: the density assumption used to promote the three smooth LL
pairings to stationarity of the unrestricted completed packet is false for
the current packet topology. -/
theorem finite_frame_paired_c2_physical_maxwell_spinC_matter_LL_smooth_density_obstruction_gate
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    ¬ DenseRange
      (smoothLLCoefficientPTC0FirstJetLinearMap period hPeriod frame) :=
  smoothLLCoefficientPTC0FirstJetLinearMap_not_denseRange
    period hPeriod frame point

end
end P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLSmoothDensityObstruction4D
end JanusFormal
