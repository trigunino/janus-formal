import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RegularGhostL2Recovery4D

/-! The regular and normalized ghost L² completions are continuously linearly equivalent. -/
namespace JanusFormal.P0EFTJanusProgramPT12RegularGhostL2Equiv4D
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 600000
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff ENNReal
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusL2PTFunctionalSpace4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceStokes4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceWeakStokes4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceLeibniz4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance : BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

open scoped BigOperators
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D
open P0EFTJanusMappingTorusMetricCartanGlobalAction4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusRegularFrameSymmetricTensorDivergence4D
open P0EFTJanusRegularFrameMetricCartanCoefficients4D
open P0EFTJanusProgramPT12CanonicalFrameDerivativeAdjoint4D
open P0EFTJanusProgramPT12CanonicalFirstOrderColumn4D

variable (reference : RegularGeneralLorentzMetric period hPeriod)


open Set
open P0EFTJanusProgramPT12RegularFrameCartanAdjoint4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothApproximation4D

open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPT12RegularFrameCartanClosed4D

open P0EFTJanusProgramPT12SmoothMatrixL24D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusProgramPGlobalDiffeomorphismBRSTOffShellGraphC2Chart4D
variable (metric : SmoothGeneralLorentzMetric period hPeriod)

open P0EFTJanusProgramPT12RegularGhostL2Transport4D
open P0EFTJanusProgramPT12FPCanonicalFormalAdjoint4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphPairing4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D

open P0EFTJanusProgramPT12RegularGhostL2Recovery4D

theorem regularGhostL2Transport_range_isClosed :
    IsClosed ((regularGhostL2Transport period hPeriod reference metric).range :
      Set (GlobalDiffeomorphismVectorL2 period hPeriod)) := by
  have hRange : ((regularGhostL2Transport period hPeriod reference metric).range :
      Set (GlobalDiffeomorphismVectorL2 period hPeriod)) =
      {field | regularGhostL2Transport period hPeriod reference metric
        (regularGhostL2Recovery period hPeriod reference metric field) = field} := by
    ext field
    constructor
    · rintro ⟨coefficients, rfl⟩
      change regularGhostL2Transport period hPeriod reference metric
        (regularGhostL2Recovery period hPeriod reference metric
          (regularGhostL2Transport period hPeriod reference metric coefficients)) = _
      rw [regularGhostL2Recovery_transport]
      rfl
    · intro h
      exact ⟨regularGhostL2Recovery period hPeriod reference metric field, h⟩
  rw [hRange]
  exact isClosed_eq ((regularGhostL2Transport period hPeriod reference metric).continuous.comp
    (regularGhostL2Recovery period hPeriod reference metric).continuous) continuous_id

def regularGhostL2EquivRange : CartanGhostL2 period hPeriod ≃L[Real]
    (regularGhostL2Transport period hPeriod reference metric).range where
  toLinearMap := (regularGhostL2Transport period hPeriod reference metric).rangeRestrict
  invFun field := regularGhostL2Recovery period hPeriod reference metric field.val
  left_inv := regularGhostL2Recovery_transport period hPeriod reference metric
  right_inv field := by
    apply Subtype.ext
    obtain ⟨coefficients, h⟩ := field.property
    change regularGhostL2Transport period hPeriod reference metric
      (regularGhostL2Recovery period hPeriod reference metric field.val) = field.val
    exact (congrArg (regularGhostL2Transport period hPeriod reference metric)
      ((congrArg (regularGhostL2Recovery period hPeriod reference metric) h.symm).trans
        (regularGhostL2Recovery_transport period hPeriod reference metric coefficients))).trans h
  continuous_toFun := (regularGhostL2Transport period hPeriod reference metric).continuous.codRestrict _
  continuous_invFun := (regularGhostL2Recovery period hPeriod reference metric).continuous.comp continuous_subtype_val

theorem regularGhostL2Transport_range_eq_smoothClosure :
    (regularGhostL2Transport period hPeriod reference metric).range =
      (globalNormalizedVectorFrameL2LinearMap period hPeriod metric).range.topologicalClosure := by
  apply le_antisymm
  · rintro _ ⟨field, rfl⟩
    let target := (globalNormalizedVectorFrameL2LinearMap period hPeriod metric).range.topologicalClosure
    have hClosed : IsClosed {field : CartanGhostL2 period hPeriod |
        regularGhostL2Transport period hPeriod reference metric field ∈ target} :=
      (globalNormalizedVectorFrameL2LinearMap period hPeriod metric).range.isClosed_topologicalClosure.preimage
        (regularGhostL2Transport period hPeriod reference metric).continuous
    have hAll : (Set.univ : Set (CartanGhostL2 period hPeriod)) ⊆
        {field | regularGhostL2Transport period hPeriod reference metric field ∈ target} := by
      rw [← (regularFrameGhostL2_denseRange period hPeriod).closure_range]
      apply closure_minimal _ hClosed
      rintro _ ⟨coefficients, rfl⟩
      change regularGhostL2Transport period hPeriod reference metric
        (regularFrameGhostL2 period hPeriod coefficients) ∈ target
      rw [regularGhostL2Transport_smooth]
      exact Submodule.le_topologicalClosure _ ⟨_, rfl⟩
    exact hAll (Set.mem_univ field)
  · apply closure_minimal _ (regularGhostL2Transport_range_isClosed period hPeriod reference metric)
    rintro _ ⟨ghost, rfl⟩
    exact ⟨regularFrameGhostL2 period hPeriod
      (regularFrameCartanGhostCoefficient period hPeriod reference ghost),
      regularGhostL2Transport_actual period hPeriod reference metric ghost⟩

theorem regularGhostL2EquivRange_smooth (coefficients : Fin 4 → SmoothScalarField period hPeriod) :
    (regularGhostL2EquivRange period hPeriod reference metric
      (regularFrameGhostL2 period hPeriod coefficients)).val =
      globalNormalizedVectorFrameL2LinearMap period hPeriod metric
        (regularFrameGhostFromCoefficients period hPeriod reference coefficients) :=
  regularGhostL2Transport_smooth period hPeriod reference metric coefficients

end
end JanusFormal.P0EFTJanusProgramPT12RegularGhostL2Equiv4D
