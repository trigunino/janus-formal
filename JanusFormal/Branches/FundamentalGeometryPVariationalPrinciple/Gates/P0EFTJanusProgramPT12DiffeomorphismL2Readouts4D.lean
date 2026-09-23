import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RegularTensorL2Bridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismL2BRST4D

/-! Bounded original-coordinate readouts on the completed diagonal BRST field space. -/
namespace JanusFormal.P0EFTJanusProgramPT12DiffeomorphismL2Readouts4D
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

open P0EFTJanusProgramPT12SmoothMatrixL24D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open Set

open P0EFTJanusProgramPT12FrameTensorL2Transport4D

open P0EFTJanusProgramPT12FrameTensorL2Equiv4D
open P0EFTJanusProgramPT12RegularFrameCartanClosed4D
open P0EFTJanusProgramPT12PairedRegularFrameCartan4D
open P0EFTJanusProgramPT12PairedRegularFrameCartanCore4D
open P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphCore4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusD9D10ExactFieldContentBridge4D

open P0EFTJanusProgramPT12RegularTensorL2Bridge4D
open P0EFTJanusProgramPT12DiffeomorphismL2Core4D
open P0EFTJanusProgramPT12DiffeomorphismL2BRST4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalDiffeomorphismBRSTOffShellGraphC2Chart4D

variable (metric : SmoothGeneralLorentzMetric period hPeriod)

def diffeomorphismTensorReadout (sector : Sector) :
    DiffeomorphismL2 period hPeriod metric →L[Real] GlobalGeneralMetricTensorFrameL2 period hPeriod :=
  ((PiLp.proj 2 (fun _ : Sector => GlobalGeneralMetricTensorFrameL2 period hPeriod) sector).comp
    (WithLp.fstL 2 Real _ _)).comp (diffeomorphismL2Space period hPeriod metric).subtypeL

def diffeomorphismTripletReadout (index : Fin 3) :
    DiffeomorphismL2 period hPeriod metric →L[Real] GlobalDiffeomorphismVectorL2 period hPeriod :=
  ((PiLp.proj 2 (fun _ : Fin 3 => GlobalDiffeomorphismVectorL2 period hPeriod) index).comp
    (WithLp.sndL 2 Real _ _)).comp (diffeomorphismL2Space period hPeriod metric).subtypeL

theorem diffeomorphismTensorReadout_smooth (sector : Sector)
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    diffeomorphismTensorReadout period hPeriod metric sector (diffeomorphismL2Smooth period hPeriod metric field) =
      globalGeneralMetricTensorFrameL2LinearMap period hPeriod (field.metricPerturbation sector) := rfl

theorem diffeomorphismTripletReadout_smooth (index : Fin 3)
    (field : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod) :
    diffeomorphismTripletReadout period hPeriod metric index (diffeomorphismL2Smooth period hPeriod metric field) =
      globalNormalizedVectorFrameL2LinearMap period hPeriod metric
        (![field.nonminimal.ghost.field, field.nonminimal.antighost.field,
          field.nonminimal.nakanishiLautrup.field] index) := by
  fin_cases index <;> rfl

theorem diffeomorphismTensorReadout_mem (sector : Sector) (field : DiffeomorphismL2 period hPeriod metric) :
    diffeomorphismTensorReadout period hPeriod metric sector field ∈
      frameTensorL2Space period hPeriod (finiteSmoothTangentFrame period hPeriod) := by
  rw [finiteTensorL2Space_eq_actual]
  let read : DiffeomorphismL2Ambient period hPeriod →L[Real] GlobalGeneralMetricTensorFrameL2 period hPeriod :=
    (PiLp.proj 2 (fun _ : Sector => GlobalGeneralMetricTensorFrameL2 period hPeriod) sector).comp (WithLp.fstL 2 Real _ _)
  have h : Set.MapsTo read (diffeomorphismL2Coordinates period hPeriod metric).range
      (globalGeneralMetricTensorFrameL2LinearMap period hPeriod).range := by
    rintro _ ⟨smooth, rfl⟩
    exact ⟨smooth.metricPerturbation sector, rfl⟩
  exact h.closure read.continuous field.property

theorem diffeomorphismTensorReadout_recovery_zero
    (reference : RegularGeneralLorentzMetric period hPeriod) (sector : Sector)
    (field : DiffeomorphismL2 period hPeriod metric)
    (hZero : regularTensorL2Recovery period hPeriod reference
      (diffeomorphismTensorReadout period hPeriod metric sector field) = 0) :
    diffeomorphismTensorReadout period hPeriod metric sector field = 0 := by
  have hInverse := frameTensorL2Transport_inverse period hPeriod
    (finiteSmoothTangentFrame period hPeriod)
    (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference) reference.metric
    ⟨_, diffeomorphismTensorReadout_mem period hPeriod metric sector field⟩
  exact hInverse.symm.trans ((congrArg (regularTensorL2Transport period hPeriod reference) hZero).trans (map_zero _))

theorem diffeomorphismL2_eq_zero_of_readouts (field : DiffeomorphismL2 period hPeriod metric)
    (hTensor : ∀ sector, diffeomorphismTensorReadout period hPeriod metric sector field = 0)
    (hTriplet : ∀ index, diffeomorphismTripletReadout period hPeriod metric index field = 0) : field = 0 := by
  apply Subtype.ext
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · apply PiLp.ext; intro sector; exact hTensor sector
  · apply PiLp.ext; intro index; exact hTriplet index

end
end JanusFormal.P0EFTJanusProgramPT12DiffeomorphismL2Readouts4D
