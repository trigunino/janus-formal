import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D

/-! Zeroth-order L² completion of the two metric perturbations and the shared
diagonal BRST triplet. Redundant frame coordinates are completed only in their
actual smooth image; no density in the full coordinate ambient is assumed. -/
namespace JanusFormal.P0EFTJanusProgramPT12DiffeomorphismL2Core4D
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 600000
noncomputable section
open Set
open scoped InnerProductSpace Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphCore4D
open P0EFTJanusProgramPGlobalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

abbrev DiffeomorphismL2Ambient :=
  WithLp 2 ((PiLp 2 fun _ : Sector => GlobalGeneralMetricTensorFrameL2 period hPeriod) ×
    PiLp 2 fun _ : Fin 3 => GlobalDiffeomorphismVectorL2 period hPeriod)

def diffeomorphismMetricL2Coordinate (sector : Sector) :
    GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod →ₗ[Real]
      GlobalGeneralMetricTensorFrameL2 period hPeriod :=
  (globalGeneralMetricTensorFrameL2LinearMap period hPeriod).comp
    ((globalDiffeomorphismMetricPerturbationProjectionLinearMap period hPeriod).comp
      (globalCandidateADiagonalDiffeomorphismSectorStateLinearMap period hPeriod sector))

/-- Ghost, antighost, multiplier, with one common zeroth-order normalization. -/
def diffeomorphismTripletL2Coordinate
    (metric : SmoothGeneralLorentzMetric period hPeriod) (index : Fin 3) :
    GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod →ₗ[Real]
      GlobalDiffeomorphismVectorL2 period hPeriod :=
  (globalNormalizedVectorFrameL2LinearMap period hPeriod metric).comp
    ((![globalDiffeomorphismGhostFieldProjectionLinearMap period hPeriod,
        globalDiffeomorphismAntighostFieldProjectionLinearMap period hPeriod,
        globalDiffeomorphismBFieldProjectionLinearMap period hPeriod] index).comp
      (globalCandidateADiagonalDiffeomorphismSectorStateLinearMap period hPeriod .plus))

def diffeomorphismL2Coordinates (metric : SmoothGeneralLorentzMetric period hPeriod) :
    GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod →ₗ[Real]
      DiffeomorphismL2Ambient period hPeriod where
  toFun field := WithLp.toLp 2
    (WithLp.toLp 2 fun sector => diffeomorphismMetricL2Coordinate period hPeriod sector field,
     WithLp.toLp 2 fun index => diffeomorphismTripletL2Coordinate period hPeriod metric index field)
  map_add' first second := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · apply PiLp.ext; intro sector
      exact (diffeomorphismMetricL2Coordinate period hPeriod sector).map_add first second
    · apply PiLp.ext; intro index
      exact (diffeomorphismTripletL2Coordinate period hPeriod metric index).map_add first second
  map_smul' scalar field := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · apply PiLp.ext; intro sector
      exact (diffeomorphismMetricL2Coordinate period hPeriod sector).map_smul scalar field
    · apply PiLp.ext; intro index
      exact (diffeomorphismTripletL2Coordinate period hPeriod metric index).map_smul scalar field

theorem diffeomorphismL2Coordinates_injective
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    Function.Injective (diffeomorphismL2Coordinates period hPeriod metric) := by
  intro first second h
  apply GlobalCandidateADiagonalDiffeomorphismBRSTState.ext
  · funext sector
    apply globalGeneralMetricTensorFrameL2LinearMap_injective period hPeriod
    exact congrArg (fun value : DiffeomorphismL2Ambient period hPeriod =>
      WithLp.fst value sector) h
  · apply GlobalDiffeomorphismNonminimalFields.ext
    · apply GlobalDiffeomorphismGhostField.ext
      apply globalNormalizedVectorFrameL2LinearMap_injective period hPeriod metric
      exact congrArg (fun value : DiffeomorphismL2Ambient period hPeriod =>
        WithLp.snd value 0) h
    · apply GlobalDiffeomorphismAntighostField.ext
      apply globalNormalizedVectorFrameL2LinearMap_injective period hPeriod metric
      exact congrArg (fun value : DiffeomorphismL2Ambient period hPeriod =>
        WithLp.snd value 1) h
    · apply GlobalDiffeomorphismNakanishiLautrupField.ext
      apply globalNormalizedVectorFrameL2LinearMap_injective period hPeriod metric
      exact congrArg (fun value : DiffeomorphismL2Ambient period hPeriod =>
        WithLp.snd value 2) h

def diffeomorphismL2Space (metric : SmoothGeneralLorentzMetric period hPeriod) :
    Submodule Real (DiffeomorphismL2Ambient period hPeriod) :=
  (diffeomorphismL2Coordinates period hPeriod metric).range.topologicalClosure

abbrev DiffeomorphismL2 (metric : SmoothGeneralLorentzMetric period hPeriod) :=
  diffeomorphismL2Space period hPeriod metric

instance (metric : SmoothGeneralLorentzMetric period hPeriod) :
    CompleteSpace (DiffeomorphismL2 period hPeriod metric) :=
  Submodule.topologicalClosure.completeSpace _

def diffeomorphismL2Smooth (metric : SmoothGeneralLorentzMetric period hPeriod) :
    GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod →ₗ[Real]
      DiffeomorphismL2 period hPeriod metric :=
  (diffeomorphismL2Coordinates period hPeriod metric).codRestrict
    (diffeomorphismL2Space period hPeriod metric)
    (fun field => Submodule.le_topologicalClosure _ ⟨field, rfl⟩)

theorem diffeomorphismL2Smooth_injective
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    Function.Injective (diffeomorphismL2Smooth period hPeriod metric) := by
  intro first second h
  exact diffeomorphismL2Coordinates_injective period hPeriod metric (congrArg Subtype.val h)

theorem diffeomorphismL2Smooth_denseRange
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    DenseRange (diffeomorphismL2Smooth period hPeriod metric) := by
  rw [DenseRange, Subtype.dense_iff]
  have hRange : Subtype.val '' Set.range (diffeomorphismL2Smooth period hPeriod metric) =
      ((diffeomorphismL2Coordinates period hPeriod metric).range : Set _) := by
    ext value
    constructor
    · rintro ⟨_, ⟨field, rfl⟩, rfl⟩; exact ⟨field, rfl⟩
    · rintro ⟨field, rfl⟩
      exact ⟨diffeomorphismL2Smooth period hPeriod metric field, ⟨field, rfl⟩, rfl⟩
  change closure ((diffeomorphismL2Coordinates period hPeriod metric).range :
    Set (DiffeomorphismL2Ambient period hPeriod)) ⊆
    closure (Subtype.val '' Set.range (diffeomorphismL2Smooth period hPeriod metric))
  exact (congrArg closure hRange).symm.subset

end
end JanusFormal.P0EFTJanusProgramPT12DiffeomorphismL2Core4D
