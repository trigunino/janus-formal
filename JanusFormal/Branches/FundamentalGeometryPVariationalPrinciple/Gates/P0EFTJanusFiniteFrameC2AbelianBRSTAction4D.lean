import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2AbelianOperators4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameCovectorC2Projection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameDiffeomorphismBRSTSmoothFeatures4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D

/-! # Abelian BRST on the genuine finite-frame C² metric model

The two Lie-algebra components of the potential and all three nonminimal
fields remain independent. Lorenz and FP use the same variable metric.
The potential is projected to the covector represented by its redundant coefficients.
The original Abelian action uses the fixed canonical measure.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameC2AbelianBRSTAction4D

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusGlobalGeneralMetricAbelianLorenzCodifferential4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusFiniteFrameC2AbelianOperators4D
open P0EFTJanusFiniteFrameCovectorC2Projection4D
open P0EFTJanusFiniteFrameDiffeomorphismBRSTSmoothFeatures4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod
private abbrev C0Scalar := C(EffectiveQuotient period hPeriod, Real)
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
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance

abbrev FiniteFrameAbelianNonminimalC2Core :=
  FiniteFrameAbelianGhostC2Core period hPeriod ×
    (FiniteFrameAbelianGhostC2Core period hPeriod × FiniteFrameAbelianGhostC2Core period hPeriod)

/-- Metric, potential, and total B/antighost/ghost, in this order. -/
abbrev FiniteFrameC2AbelianBRSTCore (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod) :=
  GeneralMetricRelativeC2Core period hPeriod frame baseMetric ×
    (FiniteFrameAbelianGaugeC2Core period hPeriod frame × FiniteFrameAbelianNonminimalC2Core period hPeriod)

def finiteFrameAbelianScalarC2Readout (component : Fin 2) :
    FiniteFrameAbelianGhostC2Core period hPeriod →L[Real] C0Scalar period hPeriod :=
  (canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod).comp (ContinuousLinearMap.proj component)

theorem finiteFrameAbelianScalarC2Readout_smooth
    (field : SmoothQuotientField period hPeriod GaugeLieAlgebra) (component : Fin 2) :
    finiteFrameAbelianScalarC2Readout period hPeriod component
      (finiteFrameSmoothAbelianGhostC2Coefficients period hPeriod field) =
    smoothToCanonicalPhysicalContinuousScalar period hPeriod (ghostComponent period hPeriod field component) :=
  canonicalPhysicalScalarC2JetCoreToContinuous_smooth period hPeriod _

variable (frame : SmoothD8Frame period hPeriod) (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
local notation "Input" => FiniteFrameC2AbelianBRSTCore period hPeriod frame baseMetric

theorem finiteFrameSmoothAbelianGaugeC2Coefficients_projected
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    finiteFrameGaugeC2Projection period hPeriod frame baseMetric
      (finiteFrameSmoothAbelianGaugeC2Coefficients period hPeriod frame potential) =
    finiteFrameSmoothAbelianGaugeC2Coefficients period hPeriod frame potential :=
  finiteFrameGaugeC2Projection_fixes_potential period hPeriod frame baseMetric potential

def finiteFrameC2AbelianBRSTDomain : Set Input :=
  generalMetricRelativeC2OpenDomain period hPeriod frame baseMetric ×ˢ Set.univ

theorem finiteFrameC2AbelianBRSTDomain_isOpen :
    IsOpen (finiteFrameC2AbelianBRSTDomain period hPeriod frame baseMetric) :=
  (generalMetricRelativeC2OpenDomain_isOpen period hPeriod frame baseMetric).prod isOpen_univ

def finiteFrameC2AbelianBRSTDensity (input : Input) : C0Scalar period hPeriod :=
  ∑ component : Fin 2,
    (finiteFrameAbelianScalarC2Readout period hPeriod component input.2.2.1 *
        finiteFrameC2AbelianLorenzComponentExpression period hPeriod frame baseMetric input.1
          (finiteFrameGaugeC2Projection period hPeriod frame baseMetric input.2.1) component -
      (1 / 2 : Real) • (finiteFrameAbelianScalarC2Readout period hPeriod component input.2.2.1 *
        finiteFrameAbelianScalarC2Readout period hPeriod component input.2.2.1) +
      finiteFrameAbelianScalarC2Readout period hPeriod component input.2.2.2.1 *
        finiteFrameC2AbelianFPComponentExpression period hPeriod frame baseMetric input.1 input.2.2.2.2 component)

theorem finiteFrameC2AbelianBRSTDensity_contDiffOn :
    ContDiffOn Real ∞ (finiteFrameC2AbelianBRSTDensity period hPeriod frame baseMetric)
      (finiteFrameC2AbelianBRSTDomain period hPeriod frame baseMetric) := by
  have hB (component : Fin 2) : ContDiff Real ∞
      (fun input : Input => finiteFrameAbelianScalarC2Readout period hPeriod component input.2.2.1) :=
    (finiteFrameAbelianScalarC2Readout period hPeriod component).contDiff.comp contDiff_snd.snd.fst
  have hAntighost (component : Fin 2) : ContDiff Real ∞
      (fun input : Input => finiteFrameAbelianScalarC2Readout period hPeriod component input.2.2.2.1) :=
    (finiteFrameAbelianScalarC2Readout period hPeriod component).contDiff.comp contDiff_snd.snd.snd.fst
  have hPotentialProjection : ContDiffOn Real ∞
      (fun input : Input => (input.1, finiteFrameGaugeC2Projection period hPeriod frame baseMetric input.2.1))
      (finiteFrameC2AbelianBRSTDomain period hPeriod frame baseMetric) :=
    (contDiff_fst.prodMk ((finiteFrameGaugeC2Projection period hPeriod frame baseMetric).contDiff.comp
      contDiff_snd.fst)).contDiffOn
  have hGhostProjection : ContDiffOn Real ∞
      (fun input : Input => (input.1, input.2.2.2.2))
      (finiteFrameC2AbelianBRSTDomain period hPeriod frame baseMetric) :=
    (contDiff_fst.prodMk contDiff_snd.snd.snd.snd).contDiffOn
  have hLorenz (component : Fin 2) :=
    (finiteFrameC2AbelianLorenzComponentExpression_contDiffOn period hPeriod frame baseMetric component).comp
      hPotentialProjection (fun _ h => ⟨h.1, Set.mem_univ _⟩)
  have hFP (component : Fin 2) :=
    (finiteFrameC2AbelianFPComponentExpression_contDiffOn period hPeriod frame baseMetric component).comp
      hGhostProjection (fun _ h => ⟨h.1, Set.mem_univ _⟩)
  have hComponent (component : Fin 2) :=
    (((hB component).contDiffOn.mul (hLorenz component)).sub
      (((hB component).contDiffOn.mul (hB component).contDiffOn).const_smul (1 / 2 : Real))).add
        ((hAntighost component).contDiffOn.mul (hFP component))
  have hResult := ContDiffOn.sum (s := Finset.univ) (fun component _ => hComponent component)
  exact hResult

def finiteFrameC2AbelianBRSTAction (input : Input) : Real :=
  finiteFrameBRSTCanonicalIntegralCLM period hPeriod
    (finiteFrameC2AbelianBRSTDensity period hPeriod frame baseMetric input)

/-- Coefficients with the same reconstructed covector have exactly the same action. -/
theorem finiteFrameC2AbelianBRSTAction_eq_of_projected_potential
    (variation : GeneralMetricRelativeC2Core period hPeriod frame baseMetric)
    (first second : FiniteFrameAbelianGaugeC2Core period hPeriod frame)
    (fields : FiniteFrameAbelianNonminimalC2Core period hPeriod)
    (hPotential : finiteFrameGaugeC2Projection period hPeriod frame baseMetric first =
      finiteFrameGaugeC2Projection period hPeriod frame baseMetric second) :
    finiteFrameC2AbelianBRSTAction period hPeriod frame baseMetric (variation, (first, fields)) =
    finiteFrameC2AbelianBRSTAction period hPeriod frame baseMetric (variation, (second, fields)) := by
  unfold finiteFrameC2AbelianBRSTAction finiteFrameC2AbelianBRSTDensity
  rw [hPotential]

theorem finiteFrameC2AbelianBRSTAction_contDiffOn :
    ContDiffOn Real ∞ (finiteFrameC2AbelianBRSTAction period hPeriod frame baseMetric)
      (finiteFrameC2AbelianBRSTDomain period hPeriod frame baseMetric) :=
  (finiteFrameBRSTCanonicalIntegralCLM period hPeriod).contDiff.comp_contDiffOn
    (finiteFrameC2AbelianBRSTDensity_contDiffOn period hPeriod frame baseMetric)

theorem finiteFrameC2AbelianBRSTAction_hasFDerivAt (input : Input)
    (hInput : input ∈ finiteFrameC2AbelianBRSTDomain period hPeriod frame baseMetric) :
    HasFDerivAt (finiteFrameC2AbelianBRSTAction period hPeriod frame baseMetric)
      (fderiv Real (finiteFrameC2AbelianBRSTAction period hPeriod frame baseMetric) input) input :=
  ((finiteFrameC2AbelianBRSTAction_contDiffOn period hPeriod frame baseMetric input hInput).contDiffAt
    ((finiteFrameC2AbelianBRSTDomain_isOpen period hPeriod frame baseMetric).mem_nhds hInput)).differentiableAt
      (by simp) |>.hasFDerivAt

def finiteFrameSmoothAbelianBRSTCore (variation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (fields : GlobalAbelianNonminimalFields period hPeriod) : Input :=
  (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation,
    (finiteFrameSmoothAbelianGaugeC2Coefficients period hPeriod frame potential,
      (finiteFrameSmoothAbelianGhostC2Coefficients period hPeriod fields.nakanishiLautrup.field,
        (finiteFrameSmoothAbelianGhostC2Coefficients period hPeriod fields.antighost.field,
          finiteFrameSmoothAbelianGhostC2Coefficients period hPeriod fields.ghost.field))))

theorem finiteFrameC2AbelianBRSTDensity_smooth
    (variation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (hMetric : metric.tensor = baseMetric.tensor + variation)
    (hVariation : smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation ∈
      generalMetricRelativeC2OpenDomain period hPeriod frame baseMetric)
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (fields : GlobalAbelianNonminimalFields period hPeriod) (point : EffectiveQuotient period hPeriod) :
    finiteFrameC2AbelianBRSTDensity period hPeriod frame baseMetric
      (finiteFrameSmoothAbelianBRSTCore period hPeriod frame baseMetric variation potential fields) point =
    globalGaugeLiePairingAt period hPeriod fields.nakanishiLautrup.field
        (globalGeneralMetricAbelianLorenzCodifferential period hPeriod metric potential) point -
      (1 / 2 : Real) * globalGaugeLiePairingAt period hPeriod fields.nakanishiLautrup.field
        fields.nakanishiLautrup.field point +
      globalGaugeLiePairingAt period hPeriod fields.antighost.field
        (globalGeneralMetricAbelianFaddeevPopov period hPeriod metric fields.ghost.field) point := by
  have hReadout (field : SmoothQuotientField period hPeriod GaugeLieAlgebra) (component : Fin 2) :
      smoothToCanonicalPhysicalContinuousScalar period hPeriod (ghostComponent period hPeriod field component) point =
        field point component := rfl
  simp only [finiteFrameC2AbelianBRSTDensity, finiteFrameSmoothAbelianBRSTCore,
    finiteFrameSmoothAbelianGaugeC2Coefficients_projected,
    finiteFrameAbelianScalarC2Readout_smooth,
    finiteFrameC2AbelianLorenzComponentExpression_smooth period hPeriod frame baseMetric variation metric hMetric hVariation,
    finiteFrameC2AbelianFPComponentExpression_smooth period hPeriod frame baseMetric variation metric hMetric hVariation,
    ContinuousMap.sum_apply, ContinuousMap.sub_apply, ContinuousMap.add_apply, ContinuousMap.mul_apply,
    ContinuousMap.smul_apply, smul_eq_mul, hReadout, globalGaugeLiePairingAt,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]

abbrev FiniteFramePairedC2AbelianBRSTCore
    (plusFrame minusFrame : SmoothD8Frame period hPeriod)
    (plusBase minusBase : SmoothGeneralLorentzMetric period hPeriod) :=
  FiniteFrameC2AbelianBRSTCore period hPeriod plusFrame plusBase ×
    FiniteFrameC2AbelianBRSTCore period hPeriod minusFrame minusBase

variable (plusFrame minusFrame : SmoothD8Frame period hPeriod)
  (plusBase minusBase : SmoothGeneralLorentzMetric period hPeriod)
local notation "PairInput" => FiniteFramePairedC2AbelianBRSTCore period hPeriod plusFrame minusFrame plusBase minusBase

def finiteFramePairedC2AbelianBRSTDomain : Set PairInput :=
  finiteFrameC2AbelianBRSTDomain period hPeriod plusFrame plusBase ×ˢ
    finiteFrameC2AbelianBRSTDomain period hPeriod minusFrame minusBase

theorem finiteFramePairedC2AbelianBRSTDomain_isOpen :
    IsOpen (finiteFramePairedC2AbelianBRSTDomain period hPeriod plusFrame minusFrame plusBase minusBase) :=
  (finiteFrameC2AbelianBRSTDomain_isOpen period hPeriod plusFrame plusBase).prod
    (finiteFrameC2AbelianBRSTDomain_isOpen period hPeriod minusFrame minusBase)

def finiteFramePairedC2AbelianBRSTAction (input : PairInput) : Real :=
  finiteFrameC2AbelianBRSTAction period hPeriod plusFrame plusBase input.1 +
    finiteFrameC2AbelianBRSTAction period hPeriod minusFrame minusBase input.2

theorem finiteFramePairedC2AbelianBRSTAction_contDiffOn :
    ContDiffOn Real ∞ (finiteFramePairedC2AbelianBRSTAction period hPeriod plusFrame minusFrame plusBase minusBase)
      (finiteFramePairedC2AbelianBRSTDomain period hPeriod plusFrame minusFrame plusBase minusBase) :=
  ((finiteFrameC2AbelianBRSTAction_contDiffOn period hPeriod plusFrame plusBase).comp
    contDiff_fst.contDiffOn (fun _ h => h.1)).add
      ((finiteFrameC2AbelianBRSTAction_contDiffOn period hPeriod minusFrame minusBase).comp
        contDiff_snd.contDiffOn (fun _ h => h.2))

theorem finiteFramePairedC2AbelianBRSTAction_smooth
    (plusVariation minusVariation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (hPlusMetric : (metric .plus).tensor = plusBase.tensor + plusVariation)
    (hMinusMetric : (metric .minus).tensor = minusBase.tensor + minusVariation)
    (hPlusVariation : smoothToGeneralMetricRelativeC2Core period hPeriod plusFrame plusBase plusVariation ∈
      generalMetricRelativeC2OpenDomain period hPeriod plusFrame plusBase)
    (hMinusVariation : smoothToGeneralMetricRelativeC2Core period hPeriod minusFrame minusBase minusVariation ∈
      generalMetricRelativeC2OpenDomain period hPeriod minusFrame minusBase)
    (state : GlobalPairedAbelianBRSTState period hPeriod) :
    finiteFramePairedC2AbelianBRSTAction period hPeriod plusFrame minusFrame plusBase minusBase
      (finiteFrameSmoothAbelianBRSTCore period hPeriod plusFrame plusBase plusVariation
          (state.potential .plus) (state.nonminimal .plus),
        finiteFrameSmoothAbelianBRSTCore period hPeriod minusFrame minusBase minusVariation
          (state.potential .minus) (state.nonminimal .minus)) =
    globalPairedAbelianGaugeFermionBRSTAction period hPeriod metric state
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  unfold finiteFramePairedC2AbelianBRSTAction finiteFrameC2AbelianBRSTAction
  rw [← map_add, finiteFrameBRSTCanonicalIntegralCLM_apply]
  unfold globalPairedAbelianGaugeFermionBRSTAction
  apply integral_congr_ae
  filter_upwards [] with point
  rw [ContinuousMap.add_apply,
    finiteFrameC2AbelianBRSTDensity_smooth period hPeriod plusFrame plusBase plusVariation (metric .plus)
      hPlusMetric hPlusVariation,
    finiteFrameC2AbelianBRSTDensity_smooth period hPeriod minusFrame minusBase minusVariation (metric .minus)
      hMinusMetric hMinusVariation]
  have hSectors : (Finset.univ : Finset Sector) = {.plus, .minus} := by decide
  simp only [globalPairedAbelianGaugeFermionBRSTDensity, hSectors, Finset.sum_insert,
    Finset.sum_singleton, Finset.mem_singleton, reduceCtorEq, not_false_eq_true]

end
end P0EFTJanusFiniteFrameC2AbelianBRSTAction4D
end JanusFormal
