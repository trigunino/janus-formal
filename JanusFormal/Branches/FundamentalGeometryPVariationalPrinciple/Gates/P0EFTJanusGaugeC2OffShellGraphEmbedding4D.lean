import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaugeC2AbelianOffShellGraphBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRegularFrameC2LorenzFeature4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaugeC2SmoothCoefficientDensity4D

/-! # Completed C² gauge coefficients in the genuine Abelian off-shell graph

The bounded potential and Lorenz features extend the same smooth gauge
potential. Density puts their paired extension in the closed off-shell graph.
This is the pure-potential inclusion; its nonminimal fields are zero.
-/

namespace JanusFormal
namespace P0EFTJanusGaugeC2OffShellGraphEmbedding4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 600000

noncomputable section
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusGlobalGeneralMetricAbelianLorenzCodifferential4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPRegularFrameMetricInverse4D
open P0EFTJanusProgramPRegularFrameGaugePotentialReconstruction4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricGaugeCoreProjection4D
open P0EFTJanusProgramPGlobalAbelianLorenzGraphRiesz4D
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusGaugeC2AbelianOffShellGraphBridge4D
open P0EFTJanusRegularFrameC2LorenzFeature4D
open P0EFTJanusGaugeC2SmoothCoefficientDensity4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev GaugeC2Core := RegularGeneralMetricC2GaugeCoefficientCore period hPeriod
private abbrev PairedGaugeC2Core :=
  RegularGeneralMetricC2PairedGaugeCoefficientCore period hPeriod

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : NormedAddCommGroup (CanonicalPhysicalScalarC2JetCore period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (CanonicalPhysicalScalarC2JetCore period hPeriod) :=
  inferInstance

local instance : NormedSpace Real (GlobalPairedAbelianPotentialL2 period hPeriod) :=
  (inferInstance : InnerProductSpace Real (GlobalPairedAbelianPotentialL2 period hPeriod)).toNormedSpace
local instance : Module Real (GlobalPairedAbelianPotentialL2 period hPeriod) :=
  (inferInstance : InnerProductSpace Real (GlobalPairedAbelianPotentialL2 period hPeriod)).toNormedSpace.toModule

local instance : NormedSpace Real (GlobalPairedAbelianLorenzL2 period hPeriod) :=
  (inferInstance : InnerProductSpace Real (GlobalPairedAbelianLorenzL2 period hPeriod)).toNormedSpace
local instance : Module Real (GlobalPairedAbelianLorenzL2 period hPeriod) :=
  (inferInstance : InnerProductSpace Real (GlobalPairedAbelianLorenzL2 period hPeriod)).toNormedSpace.toModule

local instance : NormedSpace Real (GlobalPairedAbelianLorenzGraphAmbient period hPeriod) :=
  (inferInstance : InnerProductSpace Real (GlobalPairedAbelianLorenzGraphAmbient period hPeriod)).toNormedSpace
local instance : Module Real (GlobalPairedAbelianLorenzGraphAmbient period hPeriod) :=
  (inferInstance : InnerProductSpace Real (GlobalPairedAbelianLorenzGraphAmbient period hPeriod)).toNormedSpace.toModule

local instance : NormedSpace Real (GlobalPairedAbelianOffShellAmbient period hPeriod) :=
  (inferInstance : InnerProductSpace Real (GlobalPairedAbelianOffShellAmbient period hPeriod)).toNormedSpace
local instance : Module Real (GlobalPairedAbelianOffShellAmbient period hPeriod) :=
  (inferInstance : InnerProductSpace Real (GlobalPairedAbelianOffShellAmbient period hPeriod)).toNormedSpace.toModule

local instance (metric : Sector → RegularGeneralLorentzMetric period hPeriod) :
    NormedSpace Real (GlobalPairedAbelianOffShellGraphHilbert period hPeriod
      (fun sector => (metric sector).metric)) :=
  (inferInstance : InnerProductSpace Real (GlobalPairedAbelianOffShellGraphHilbert
    period hPeriod (fun sector => (metric sector).metric))).toNormedSpace
local instance (metric : Sector → RegularGeneralLorentzMetric period hPeriod) :
    Module Real (GlobalPairedAbelianOffShellGraphHilbert period hPeriod
      (fun sector => (metric sector).metric)) :=
  (inferInstance : InnerProductSpace Real (GlobalPairedAbelianOffShellGraphHilbert
    period hPeriod (fun sector => (metric sector).metric))).toNormedSpace.toModule

private def pairedGaugeC2Sector (sector : Sector) :
    PairedGaugeC2Core period hPeriod →L[Real] GaugeC2Core period hPeriod :=
  match sector with
  | .plus => ContinuousLinearMap.fst Real _ _
  | .minus => ContinuousLinearMap.snd Real _ _

/-- Bounded extension of the two genuine Lorenz features. -/
def pairedGaugeC2LorenzL2
    (metric : Sector → RegularGeneralLorentzMetric period hPeriod) :
    PairedGaugeC2Core period hPeriod →L[Real]
      GlobalPairedAbelianLorenzL2 period hPeriod :=
  (PiLp.continuousLinearEquiv 2 Real
    (fun _ : GlobalPairedAbelianLorenzCoordinateIndex =>
      CanonicalPhysicalBulkL2 period hPeriod)).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.pi fun index =>
          (regularFrameC2LorenzComponentL2 period hPeriod (metric index.1)
            index.2).comp (pairedGaugeC2Sector period hPeriod index.1))

theorem pairedGaugeC2LorenzL2_smooth
    (metric : Sector → RegularGeneralLorentzMetric period hPeriod)
    (plus minus : SmoothQuotientField period hPeriod GaugeFiber) :
    pairedGaugeC2LorenzL2 period hPeriod metric
        (smoothGaugeCoefficientC2CoreLinearMap period hPeriod plus,
          smoothGaugeCoefficientC2CoreLinearMap period hPeriod minus) =
      globalPairedAbelianLorenzL2LinearMap period hPeriod
        (fun sector => (metric sector).metric)
        (fun sector => regularFrameGaugePotentialFromCoefficients period hPeriod
          (metric sector) (match sector with | .plus => plus | .minus => minus)) := by
  apply PiLp.ext
  intro index
  rcases index with ⟨sector, component⟩
  cases sector <;>
    exact regularFrameC2LorenzComponentL2_smooth period hPeriod _ _ component

/-- Potential and Lorenz, with zero auxiliary and ghost slots. -/
def pairedGaugeC2OffShellAmbient
    (metric : Sector → RegularGeneralLorentzMetric period hPeriod) :
    PairedGaugeC2Core period hPeriod →L[Real]
      GlobalPairedAbelianOffShellAmbient period hPeriod :=
  (WithLp.prodContinuousLinearEquiv 2 Real
    (GlobalPairedAbelianLorenzGraphAmbient period hPeriod)
    (GlobalPairedAbelianOffShellTail1 period hPeriod)).symm.toContinuousLinearMap.comp
      (((WithLp.prodContinuousLinearEquiv 2 Real
        (GlobalPairedAbelianPotentialL2 period hPeriod)
        (GlobalPairedAbelianLorenzL2 period hPeriod)).symm.toContinuousLinearMap.comp
          ((pairedGaugeC2PotentialL2 period hPeriod metric).prod
            (pairedGaugeC2LorenzL2 period hPeriod metric))).prod 0)

def pairedGaugeCoefficientOffShellState
    (metric : Sector → RegularGeneralLorentzMetric period hPeriod)
    (plus minus : SmoothQuotientField period hPeriod GaugeFiber) :
    GlobalPairedAbelianBRSTState period hPeriod where
  potential := fun sector => regularFrameGaugePotentialFromCoefficients period hPeriod
    (metric sector) (match sector with | .plus => plus | .minus => minus)
  nonminimal := 0

theorem pairedGaugeC2OffShellAmbient_smooth
    (metric : Sector → RegularGeneralLorentzMetric period hPeriod)
    (plus minus : SmoothQuotientField period hPeriod GaugeFiber) :
    pairedGaugeC2OffShellAmbient period hPeriod metric
        (smoothGaugeCoefficientC2CoreLinearMap period hPeriod plus,
          smoothGaugeCoefficientC2CoreLinearMap period hPeriod minus) =
      globalPairedAbelianOffShellAmbientLinearMap period hPeriod
        (fun sector => (metric sector).metric)
        (pairedGaugeCoefficientOffShellState period hPeriod metric plus minus) := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · apply WithLp.ofLp_injective 2
    exact Prod.ext
      (pairedGaugeC2PotentialL2_smooth period hPeriod metric plus minus)
      (pairedGaugeC2LorenzL2_smooth period hPeriod metric plus minus)
  · change (0 : GlobalPairedAbelianOffShellTail1 period hPeriod) = _
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · change 0 = globalPairedGaugeLieL2LinearMap period hPeriod 0
      exact (map_zero _).symm
    · apply WithLp.ofLp_injective 2
      apply Prod.ext
      · change 0 = globalPairedGaugeLieL2LinearMap period hPeriod 0
        exact (map_zero _).symm
      · apply WithLp.ofLp_injective 2
        apply Prod.ext
        · change 0 = globalPairedGaugeLieL2LinearMap period hPeriod 0
          exact (map_zero _).symm
        · change 0 = globalPairedAbelianFPL2LinearMap period hPeriod
            (fun sector => (metric sector).metric) 0
          exact (map_zero _).symm

theorem pairedGaugeC2OffShellAmbient_mem_graph
    (metric : Sector → RegularGeneralLorentzMetric period hPeriod)
    (coefficients : PairedGaugeC2Core period hPeriod) :
    pairedGaugeC2OffShellAmbient period hPeriod metric coefficients ∈
      globalPairedAbelianOffShellGraphSubmodule period hPeriod
        (fun sector => (metric sector).metric) := by
  refine (smoothGaugeVariationPairC2CoreLinearMap_denseRange period hPeriod).induction_on
    coefficients ?_ ?_
  · exact (LinearMap.range (globalPairedAbelianOffShellAmbientLinearMap
      period hPeriod (fun sector => (metric sector).metric))).isClosed_topologicalClosure.preimage
        (pairedGaugeC2OffShellAmbient period hPeriod metric).continuous
  · intro smooth
    change pairedGaugeC2OffShellAmbient period hPeriod metric
      (smoothGaugeCoefficientC2CoreLinearMap period hPeriod smooth.1,
        smoothGaugeCoefficientC2CoreLinearMap period hPeriod smooth.2) ∈ _
    rw [pairedGaugeC2OffShellAmbient_smooth]
    exact (LinearMap.range (globalPairedAbelianOffShellAmbientLinearMap
      period hPeriod (fun sector => (metric sector).metric))).le_topologicalClosure
        (LinearMap.mem_range_self _ _)

/-- Bounded pure-potential inclusion in the genuine off-shell graph. -/
def pairedGaugeC2OffShellGraph
    (metric : Sector → RegularGeneralLorentzMetric period hPeriod) :
    PairedGaugeC2Core period hPeriod →L[Real]
      GlobalPairedAbelianOffShellGraphHilbert period hPeriod
        (fun sector => (metric sector).metric) :=
  (pairedGaugeC2OffShellAmbient period hPeriod metric).codRestrict
    (globalPairedAbelianOffShellGraphSubmodule period hPeriod
      (fun sector => (metric sector).metric))
    (pairedGaugeC2OffShellAmbient_mem_graph period hPeriod metric)

theorem pairedGaugeC2OffShellGraph_smooth
    (metric : Sector → RegularGeneralLorentzMetric period hPeriod)
    (plus minus : SmoothQuotientField period hPeriod GaugeFiber) :
    pairedGaugeC2OffShellGraph period hPeriod metric
        (smoothGaugeCoefficientC2CoreLinearMap period hPeriod plus,
          smoothGaugeCoefficientC2CoreLinearMap period hPeriod minus) =
      globalPairedAbelianOffShellSmoothEmbedding period hPeriod
        (fun sector => (metric sector).metric)
        (pairedGaugeCoefficientOffShellState period hPeriod metric plus minus) :=
  Subtype.ext (pairedGaugeC2OffShellAmbient_smooth period hPeriod metric plus minus)

theorem pairedGaugeC2OffShellGraph_lorenz
    (metric : Sector → RegularGeneralLorentzMetric period hPeriod)
    (coefficients : PairedGaugeC2Core period hPeriod) :
    globalPairedAbelianOffShellLorenzProjection period hPeriod
        (fun sector => (metric sector).metric)
        (pairedGaugeC2OffShellGraph period hPeriod metric coefficients) =
      pairedGaugeC2LorenzL2 period hPeriod metric coefficients := rfl

theorem pairedGaugeC2OffShellGraph_potential
    (metric : Sector → RegularGeneralLorentzMetric period hPeriod)
    (coefficients : PairedGaugeC2Core period hPeriod) :
    (WithLp.ofLp (globalPairedAbelianOffShellPotentialAmbientProjection period hPeriod
        (fun sector => (metric sector).metric)
        (pairedGaugeC2OffShellGraph period hPeriod metric coefficients))).1 =
      pairedGaugeC2PotentialL2 period hPeriod metric coefficients := rfl

theorem pairedGaugeC2OffShellGraph_tail
    (metric : Sector → RegularGeneralLorentzMetric period hPeriod)
    (coefficients : PairedGaugeC2Core period hPeriod) :
    globalPairedAbelianOffShellTail1Projection period hPeriod
        (fun sector => (metric sector).metric)
        (pairedGaugeC2OffShellGraph period hPeriod metric coefficients) = 0 := rfl

end
end P0EFTJanusGaugeC2OffShellGraphEmbedding4D
end JanusFormal
