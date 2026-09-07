import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaugeC2OffShellGraphEmbedding4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPairedMobileGaugeSamePotentialL2Input4D

/-! # The mobile physical potential in a fixed Abelian off-shell graph

The total mobile potential is transported before entering the fixed graph.
This nonlinear C² map has the exact smooth off-shell state as its value.
Its Lorenz feature uses the fixed base metric; equality with mobile-metric
BRST gauge fixing requires a separate metric-change correction.
-/

namespace JanusFormal
namespace P0EFTJanusPairedMobileGaugeOffShellGraphInput4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 600000

noncomputable section
open Set
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPRegularFrameMetricInverse4D
open P0EFTJanusProgramPRegularFrameGaugePotentialReconstruction4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricGaugeCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedGaugeCoefficientMaxwellAction4D
open P0EFTJanusProgramPRegularGeneralMetricC2GaugeCoefficientFrameTransport4D
open P0EFTJanusProgramPGlobalAbelianLorenzGraphRiesz4D
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusGaugeC2OffShellGraphEmbedding4D
open P0EFTJanusPairedMobileGaugeSamePotentialL2Input4D

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

variable (configuration : GlobalFieldConfiguration period hPeriod)
  (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)

private abbrev baseMetrics : Sector → SmoothGeneralLorentzMetric period hPeriod :=
  fun sector => (match sector with | .plus => plusBase | .minus => minusBase).metric
private abbrev OffShellGraph :=
  GlobalPairedAbelianOffShellGraphHilbert period hPeriod
    (baseMetrics period hPeriod plusBase minusBase)

local instance : NormedSpace Real (OffShellGraph period hPeriod plusBase minusBase) :=
  (inferInstance : InnerProductSpace Real
    (OffShellGraph period hPeriod plusBase minusBase)).toNormedSpace
local instance : Module Real (OffShellGraph period hPeriod plusBase minusBase) :=
  (inferInstance : InnerProductSpace Real
    (OffShellGraph period hPeriod plusBase minusBase)).toNormedSpace.toModule

/-- Nonlinear C² input to a fixed graph, with the actual total physical potential. -/
def pairedMobileGaugeOffShellInput
    (core : RegularGeneralMetricC2PairedMetricGaugeCore period hPeriod plusBase minusBase) :
    OffShellGraph period hPeriod plusBase minusBase :=
  pairedGaugeC2OffShellGraph period hPeriod
    (fun | .plus => plusBase | .minus => minusBase)
    (pairedMobileGaugeC2Input period hPeriod configuration plusBase minusBase core)

theorem pairedMobileGaugeOffShellInput_contDiffOn_two :
    ContDiffOn Real 2
      (pairedMobileGaugeOffShellInput period hPeriod configuration plusBase minusBase)
      (regularGeneralMetricC2PairedMetricGaugeMaxwellDomain period hPeriod
        plusBase minusBase) := by
  have hGraph : ContDiff Real 2
      (pairedGaugeC2OffShellGraph period hPeriod
        (fun | .plus => plusBase | .minus => minusBase)) :=
    (pairedGaugeC2OffShellGraph period hPeriod
      (fun | .plus => plusBase | .minus => minusBase)).contDiff
  exact hGraph.contDiffOn.comp
    (pairedMobileGaugeC2Input_contDiffOn_two period hPeriod
      configuration plusBase minusBase) (fun _ _ => Set.mem_univ _)

def pairedMobileGaugeOffShellStateAt
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod configuration)
    (hDirection : direction ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration plusBase minusBase) :
    GlobalPairedAbelianBRSTState period hPeriod where
  potential := pairedMobileGaugePotentialAt period hPeriod configuration plusBase minusBase
    direction hDirection
  nonminimal := 0

theorem pairedMobileGaugeOffShellInput_projected
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod configuration)
    (hDirection : direction ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration plusBase minusBase) :
    pairedMobileGaugeOffShellInput period hPeriod configuration plusBase minusBase
        (globalMinimalPhysicalPairedMetricGaugeCoreLinearMap period hPeriod
          configuration plusBase minusBase direction) =
      globalPairedAbelianOffShellSmoothEmbedding period hPeriod
        (baseMetrics period hPeriod plusBase minusBase)
        (pairedMobileGaugeOffShellStateAt period hPeriod configuration plusBase minusBase
          direction hDirection) := by
  unfold pairedMobileGaugeOffShellInput
  rw [pairedMobileGaugeC2Input_projected period hPeriod configuration
      plusBase minusBase direction hDirection,
    pairedGaugeC2OffShellGraph_smooth]
  apply congrArg (globalPairedAbelianOffShellSmoothEmbedding period hPeriod
    (baseMetrics period hPeriod plusBase minusBase))
  apply GlobalPairedAbelianBRSTState.ext
  · funext sector
    cases sector <;>
      exact regularFrameGaugePotentialFromCoefficients_frameCoefficients period hPeriod _ _
  · rfl

/-- The graph Lorenz is the true fixed-base Lorenz of the mobile potential. -/
theorem pairedMobileGaugeOffShellInput_lorenz_projected
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod configuration)
    (hDirection : direction ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration plusBase minusBase) :
    globalPairedAbelianOffShellLorenzProjection period hPeriod
        (baseMetrics period hPeriod plusBase minusBase)
        (pairedMobileGaugeOffShellInput period hPeriod configuration plusBase minusBase
          (globalMinimalPhysicalPairedMetricGaugeCoreLinearMap period hPeriod
            configuration plusBase minusBase direction)) =
      globalPairedAbelianLorenzL2LinearMap period hPeriod
        (baseMetrics period hPeriod plusBase minusBase)
        (pairedMobileGaugePotentialAt period hPeriod configuration plusBase minusBase
          direction hDirection) := by
  rw [pairedMobileGaugeOffShellInput_projected period hPeriod configuration
    plusBase minusBase direction hDirection]
  rfl

/-- Exact graph value for the action datum, with independent nonminimal slots zero. -/
theorem pairedMobileGaugeOffShellInput_eq_datumAt
    (couplings : GlobalCandidateAActionCouplings)
    {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod configuration)
    (hDirection : direction ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration plusBase minusBase) :
    pairedMobileGaugeOffShellInput period hPeriod configuration plusBase minusBase
        (globalMinimalPhysicalPairedMetricGaugeCoreLinearMap period hPeriod
          configuration plusBase minusBase direction) =
      globalPairedAbelianOffShellSmoothEmbedding period hPeriod
        (baseMetrics period hPeriod plusBase minusBase)
        { potential := globalCandidateAPotentialBySector period hPeriod
            ((regularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily
              period hPeriod configuration couplings data plusBase minusBase).datumAt
                direction hDirection).2
          nonminimal := 0 } := by
  rw [pairedMobileGaugeOffShellInput_projected period hPeriod configuration
    plusBase minusBase direction hDirection]
  apply congrArg (globalPairedAbelianOffShellSmoothEmbedding period hPeriod
    (baseMetrics period hPeriod plusBase minusBase))
  apply GlobalPairedAbelianBRSTState.ext
  · funext sector
    cases sector <;> rfl
  · rfl

end
end P0EFTJanusPairedMobileGaugeOffShellGraphInput4D
end JanusFormal
