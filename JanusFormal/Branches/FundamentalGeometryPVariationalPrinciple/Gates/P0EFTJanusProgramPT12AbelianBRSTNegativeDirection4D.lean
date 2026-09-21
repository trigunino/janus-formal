import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D

/-! Pure Nakanishi--Lautrup directions have strictly negative BRST Hessian. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12AbelianBRSTNegativeDirection4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 600000
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Set
open scoped ENNReal Manifold ContDiff InnerProductSpace Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusL2PTFunctionalSpace4D
open P0EFTJanusMappingTorusPhysicalGaugeSobolevComplex4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusGlobalGeneralMetricAbelianLorenzCodifferential4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusProgramPGlobalAbelianLorenzGraphRiesz4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

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

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance canonicalLorentzVolumeFinite :
    IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D

/-- Populate only the independent paired Nakanishi--Lautrup field. -/
def pureAbelianNakanishiLautrup
    (field : GlobalPairedGaugeLieSmooth period hPeriod) :
    GlobalPairedAbelianBRSTState period hPeriod where
  potential := 0
  nonminimal := fun sector =>
    { ghost := ⟨0⟩
      antighost := ⟨0⟩
      nakanishiLautrup := ⟨field sector⟩ }

/-- The sign is fixed by the existing off-shell action, for every metric. -/
theorem pureAbelianNakanishiLautrup_hessian_self
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (field : GlobalPairedGaugeLieSmooth period hPeriod) :
    let state := globalPairedAbelianOffShellSmoothEmbedding period hPeriod
      metric (pureAbelianNakanishiLautrup period hPeriod field)
    globalPairedAbelianOffShellHessian period hPeriod metric state state =
      -‖globalPairedGaugeLieL2LinearMap period hPeriod field‖ ^ 2 := by
  dsimp only
  rw [globalPairedAbelianOffShellHessian_apply]
  simp only [globalPairedAbelianOffShellLorenzProjection_smooth,
    globalPairedAbelianOffShellBProjection_smooth,
    globalPairedAbelianOffShellAntighostProjection_smooth,
    globalPairedAbelianOffShellFPProjection_smooth,
    pureAbelianNakanishiLautrup, map_zero, inner_zero_left, inner_zero_right,
    add_zero, zero_sub, real_inner_self_eq_norm_sq]
  change -‖globalPairedGaugeLieL2LinearMap period hPeriod field‖ ^ 2 +
      inner Real (globalPairedGaugeLieL2LinearMap period hPeriod 0)
        (globalPairedAbelianFPL2LinearMap period hPeriod metric 0) +
      inner Real (globalPairedAbelianFPL2LinearMap period hPeriod metric 0)
        (globalPairedGaugeLieL2LinearMap period hPeriod 0) = _
  rw [map_zero, map_zero, inner_zero_left, add_zero, add_zero]

/-- Injectivity of the canonical L² readout makes every nonzero pure B field
strictly negative, independently of the covariant metric. -/
theorem pureAbelianNakanishiLautrup_hessian_self_neg
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (field : GlobalPairedGaugeLieSmooth period hPeriod)
    (hField : field ≠ 0) :
    let state := globalPairedAbelianOffShellSmoothEmbedding period hPeriod
      metric (pureAbelianNakanishiLautrup period hPeriod field)
    globalPairedAbelianOffShellHessian period hPeriod metric state state < 0 := by
  dsimp only
  rw [pureAbelianNakanishiLautrup_hessian_self]
  have hValue : globalPairedGaugeLieL2LinearMap period hPeriod field ≠ 0 := by
    intro hZero
    apply hField
    apply globalPairedGaugeLieL2LinearMap_injective period hPeriod
    simpa only [map_zero] using hZero
  exact neg_neg_of_pos (sq_pos_of_pos ((norm_pos_iff).2 hValue))

/-- A concrete constant paired B field supplies a negative direction. -/
theorem exists_abelianBRST_negative_direction
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    ∃ core : GlobalPairedAbelianBRSTState period hPeriod,
      globalPairedAbelianOffShellHessian period hPeriod metric
        (globalPairedAbelianOffShellSmoothEmbedding period hPeriod metric core)
        (globalPairedAbelianOffShellSmoothEmbedding period hPeriod metric core) < 0 := by
  let field : GlobalPairedGaugeLieSmooth period hPeriod := fun _ =>
    ⟨fun _ => (EuclideanSpace.equiv (Fin 2) Real).symm (fun _ => 1),
      contMDiff_const⟩
  refine ⟨pureAbelianNakanishiLautrup period hPeriod field,
    pureAbelianNakanishiLautrup_hessian_self_neg period hPeriod metric field ?_⟩
  intro hZero
  let sphere : UnitThreeSphere :=
    ⟨![0, 1, 0, 0], by
      norm_num [P0EFTJanusReflectionFixedThroat.OnUnitThreeSphere,
        P0EFTJanusReflectionFixedThroat.radiusSquared, Fin.sum_univ_succ]⟩
  let point := mappingTorusMk (reflectedSphereData period hPeriod) ⟨sphere, 0⟩
  have hValue := congrArg (fun f : GlobalPairedGaugeLieSmooth period hPeriod =>
    (EuclideanSpace.equiv (Fin 2) Real) (f .plus point) 0) hZero
  change (1 : Real) = 0 at hValue
  exact one_ne_zero hValue

end
end P0EFTJanusProgramPT12AbelianBRSTNegativeDirection4D
end JanusFormal
