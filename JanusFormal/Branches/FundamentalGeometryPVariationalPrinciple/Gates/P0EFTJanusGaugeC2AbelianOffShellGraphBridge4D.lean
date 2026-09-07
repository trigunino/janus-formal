import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameGaugeCurvatureC0FromC2Coefficients4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D

/-! # Bounded potential-coordinate step toward the Abelian off-shell graph

Completed C² frame coefficients reconstruct the actual intrinsic potential
in physical L². The off-shell graph additionally requires a bounded extension
of its genuine Lorenz feature; that extension is not asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusGaugeC2AbelianOffShellGraphBridge4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 600000

noncomputable section
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothL2Density4D
open P0EFTJanusMappingTorusPhysicalGaugeSobolevComplex4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPRegularFrameMetricInverse4D
open P0EFTJanusProgramPRegularFrameGaugePotentialReconstruction4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricGaugeCoreProjection4D
open P0EFTJanusProgramPRegularFrameGaugeCurvatureC0FromC2Coefficients4D
open P0EFTJanusProgramPGlobalAbelianLorenzGraphRiesz4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C0Scalar := C(EffectiveQuotient period hPeriod, Real)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod
private abbrev GaugeC2Core := RegularGeneralMetricC2GaugeCoefficientCore period hPeriod
private abbrev PairedGaugeC2Core :=
  RegularGeneralMetricC2PairedGaugeCoefficientCore period hPeriod
private abbrev GeneratorIndex := Fin (finiteSmoothTangentFrame period hPeriod).count

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance
local instance : NormedSpace Real (GlobalPairedAbelianPotentialL2 period hPeriod) :=
  (inferInstance : InnerProductSpace Real
    (GlobalPairedAbelianPotentialL2 period hPeriod)).toNormedSpace
local instance : Module Real (GlobalPairedAbelianPotentialL2 period hPeriod) :=
  (inferInstance : InnerProductSpace Real
    (GlobalPairedAbelianPotentialL2 period hPeriod)).toNormedSpace.toModule

private def generatorTangentField (index : GeneratorIndex period hPeriod) :
    SmoothTangentField period hPeriod where
  toFun := fun point => (finiteSmoothTangentFrame period hPeriod).vectorAt point index
  contMDiff_toFun := (finiteSmoothTangentFrame period hPeriod).contMDiff_vector index

private def frameGeneratorMetricPairing
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (column : Fin 4) (index : GeneratorIndex period hPeriod) :
    SmoothQuotientField period hPeriod Real where
  toFun := fun point => metric.metric.tensor.tensor point
    (metric.frame column point)
    ((finiteSmoothTangentFrame period hPeriod).vectorAt point index)
  contMDiff_toFun := by
    have hApplied := metric.metric.tensor.tensor.contMDiff.clm_bundle_apply
      (metric.frame column).contMDiff |>.clm_bundle_apply
        (generatorTangentField period hPeriod index).contMDiff
    intro point
    have hAppliedAt := hApplied point
    rw [Bundle.contMDiffAt_section] at hAppliedAt
    simpa [generatorTangentField] using hAppliedAt

/-- The fixed smooth weight converting frame coefficients to one intrinsic
potential coordinate. -/
def gaugeC2PotentialCoordinateWeight
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4) (index : GeneratorIndex period hPeriod) :
    SmoothQuotientField period hPeriod Real where
  toFun := fun point =>
    regularFrameMetricInverseMatrix period hPeriod metric row column point *
      frameGeneratorMetricPairing period hPeriod metric column index point
  contMDiff_toFun :=
    (regularFrameMetricInverseMatrix period hPeriod metric row column).contMDiff_toFun.mul
      (frameGeneratorMetricPairing period hPeriod metric column index).contMDiff_toFun

/-- Bounded reconstruction of one continuous intrinsic potential coordinate. -/
def gaugeC2PotentialCoordinateContinuous
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (component : Fin 2) (index : GeneratorIndex period hPeriod) :
    GaugeC2Core period hPeriod →L[Real] C0Scalar period hPeriod :=
  ∑ row : Fin 4, ∑ column : Fin 4,
    (ContinuousLinearMap.mul Real (C0Scalar period hPeriod)
      (smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (gaugeC2PotentialCoordinateWeight period hPeriod metric row column index))).comp
      ((canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod).comp
        (gaugeCoefficientC2CoreComponentCLM period hPeriod row component))

theorem gaugeC2PotentialCoordinateContinuous_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (coefficients : SmoothQuotientField period hPeriod GaugeFiber)
    (component : Fin 2) (index : GeneratorIndex period hPeriod) :
    gaugeC2PotentialCoordinateContinuous period hPeriod metric component index
        (smoothGaugeCoefficientC2CoreLinearMap period hPeriod coefficients) =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (gaugePotentialCoordinateField period hPeriod
          (regularFrameGaugePotentialFromCoefficients period hPeriod metric coefficients)
          component index) := by
  apply ContinuousMap.ext
  intro point
  simp only [gaugeC2PotentialCoordinateContinuous, sum_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply',
    gaugeCoefficientC2CoreComponentCLM, ContinuousLinearMap.proj_apply,
    smoothGaugeCoefficientC2CoreLinearMap_apply,
    canonicalPhysicalScalarC2JetCoreToContinuous_smooth,
    ContinuousMap.sum_apply, ContinuousMap.mul_apply]
  change (∑ row : Fin 4, ∑ column : Fin 4,
      (regularFrameMetricInverseMatrix period hPeriod metric row column point *
        metric.metric.tensor.tensor point (metric.frame column point)
          ((finiteSmoothTangentFrame period hPeriod).vectorAt point index)) *
        coefficients point (row, component)) =
    (∑ row : Fin 4, ∑ column : Fin 4,
      (coefficients point (row, component) *
        regularFrameMetricInverseMatrix period hPeriod metric row column point) •
        metric.metric.tensor.tensor point (metric.frame column point))
      ((finiteSmoothTangentFrame period hPeriod).vectorAt point index)
  simp only [sum_apply, smul_apply,
    smul_eq_mul]
  apply Finset.sum_congr rfl
  intro row _
  apply Finset.sum_congr rfl
  intro column _
  ring

/-- Physical L² reconstruction is bounded because the fixed weights are
continuous on the compact quotient. -/
def gaugeC2PotentialCoordinateL2
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (component : Fin 2) (index : GeneratorIndex period hPeriod) :
    GaugeC2Core period hPeriod →L[Real] CanonicalPhysicalBulkL2 period hPeriod :=
  (continuousToCanonicalPhysicalBulkL2 period hPeriod).comp
    (gaugeC2PotentialCoordinateContinuous period hPeriod metric component index)

theorem gaugeC2PotentialCoordinateL2_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (coefficients : SmoothQuotientField period hPeriod GaugeFiber)
    (component : Fin 2) (index : GeneratorIndex period hPeriod) :
    gaugeC2PotentialCoordinateL2 period hPeriod metric component index
        (smoothGaugeCoefficientC2CoreLinearMap period hPeriod coefficients) =
      gaugePotentialL2Coordinates period hPeriod
        (regularFrameGaugePotentialFromCoefficients period hPeriod metric coefficients)
        component index := by
  change continuousToCanonicalPhysicalBulkL2 period hPeriod
    (gaugeC2PotentialCoordinateContinuous period hPeriod metric component index
      (smoothGaugeCoefficientC2CoreLinearMap period hPeriod coefficients)) = _
  rw [gaugeC2PotentialCoordinateContinuous_smooth,
    continuousToCanonicalPhysicalBulkL2_agrees_on_smooth]
  rfl

private def pairedGaugeC2Sector (sector : Sector) :
    PairedGaugeC2Core period hPeriod →L[Real] GaugeC2Core period hPeriod :=
  match sector with
  | .plus => ContinuousLinearMap.fst Real _ _
  | .minus => ContinuousLinearMap.snd Real _ _

/-- The potential projection required by the off-shell graph, in two arbitrary
fixed regular frames (in particular the two stored gravity frames). -/
def pairedGaugeC2PotentialL2
    (metric : Sector → RegularGeneralLorentzMetric period hPeriod) :
    PairedGaugeC2Core period hPeriod →L[Real]
      GlobalPairedAbelianPotentialL2 period hPeriod :=
  (PiLp.continuousLinearEquiv 2 Real
    (fun _ : GlobalPairedAbelianPotentialCoordinateIndex period hPeriod =>
      CanonicalPhysicalBulkL2 period hPeriod)).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.pi fun index =>
          (gaugeC2PotentialCoordinateL2 period hPeriod (metric index.1)
            index.2.1 index.2.2).comp (pairedGaugeC2Sector period hPeriod index.1))

theorem pairedGaugeC2PotentialL2_smooth
    (metric : Sector → RegularGeneralLorentzMetric period hPeriod)
    (plus minus : SmoothQuotientField period hPeriod GaugeFiber) :
    pairedGaugeC2PotentialL2 period hPeriod metric
        (smoothGaugeCoefficientC2CoreLinearMap period hPeriod plus,
          smoothGaugeCoefficientC2CoreLinearMap period hPeriod minus) =
      globalPairedAbelianPotentialL2LinearMap period hPeriod
        (fun sector => regularFrameGaugePotentialFromCoefficients period hPeriod
          (metric sector) (match sector with | .plus => plus | .minus => minus)) := by
  apply PiLp.ext
  intro index
  rcases index with ⟨sector, component, index⟩
  cases sector <;>
    exact gaugeC2PotentialCoordinateL2_smooth period hPeriod _ _ component index

end
end P0EFTJanusGaugeC2AbelianOffShellGraphBridge4D
end JanusFormal
