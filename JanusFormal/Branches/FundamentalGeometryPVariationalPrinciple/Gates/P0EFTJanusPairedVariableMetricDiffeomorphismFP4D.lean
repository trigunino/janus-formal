import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusVariableMetricC2DiffeomorphismFPSmoothAgreement4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRegularFrameDiffeomorphismGhostTransition4D

/-! # Paired mobile Faddeev--Popov features of one geometric ghost

One source-frame ghost is transported into the two fixed sector frames.
The metric variations remain independent. Smooth agreement retains the same
intrinsic ghost in both actual Faddeev--Popov operators.
-/

namespace JanusFormal
namespace P0EFTJanusPairedVariableMetricDiffeomorphismFP4D

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
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothL2Density4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalGeneralMetricDiffeomorphismFaddeevPopov4D
open P0EFTJanusRegularFrameMetricCartanCoefficients4D
open P0EFTJanusRegularFrameDiffeomorphismGhostTransition4D
open P0EFTJanusVariableMetricC2CartanFirstJet4D
open P0EFTJanusVariableMetricC2DiffeomorphismFPFeatures4D
open P0EFTJanusVariableMetricC2DiffeomorphismFPSmoothAgreement4D

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

/-- Canonical coefficients of a given ghost commute with the bounded frame transition. -/
theorem smoothDiffeomorphismGhostC2Coefficients_transition
    (source target : RegularGeneralLorentzMetric period hPeriod)
    (ghost : GlobalDiffeomorphismGhostField period hPeriod) :
    regularFrameDiffeomorphismGhostTransition period hPeriod source target
        (smoothDiffeomorphismGhostC2Coefficients period hPeriod source ghost) =
      smoothDiffeomorphismGhostC2Coefficients period hPeriod target ghost := by
  unfold smoothDiffeomorphismGhostC2Coefficients
  rw [regularFrameDiffeomorphismGhostTransition_smooth]
  simp only [smoothRegularFrameGhostTransition, regularFrameGhostFromCoefficients_reconstructs]

abbrev PairedVariableMetricDiffeomorphismFPCore
    (plusReference minusReference : RegularGeneralLorentzMetric period hPeriod) :=
  (RegularGeneralMetricC2Core period hPeriod plusReference ×
    RegularGeneralMetricC2Core period hPeriod minusReference) ×
      DiffeomorphismGhostC2Coefficients period hPeriod

variable (source plusReference minusReference : RegularGeneralLorentzMetric period hPeriod)

def pairedVariableMetricDiffeomorphismFPDomain :
    Set (PairedVariableMetricDiffeomorphismFPCore period hPeriod plusReference minusReference) :=
  (regularGeneralMetricC2Domain period hPeriod plusReference ×ˢ
    regularGeneralMetricC2Domain period hPeriod minusReference) ×ˢ univ

theorem pairedVariableMetricDiffeomorphismFPDomain_isOpen :
    IsOpen (pairedVariableMetricDiffeomorphismFPDomain period hPeriod
      plusReference minusReference) :=
  ((regularGeneralMetricC2Domain_isOpen period hPeriod plusReference).prod
    (regularGeneralMetricC2Domain_isOpen period hPeriod minusReference)).prod isOpen_univ

def pairedVariableMetricDiffeomorphismFPPlusInput
    (input : PairedVariableMetricDiffeomorphismFPCore period hPeriod plusReference minusReference) :
    RegularGeneralMetricC2Core period hPeriod plusReference ×
      DiffeomorphismGhostC2Coefficients period hPeriod :=
  (input.1.1, regularFrameDiffeomorphismGhostTransition period hPeriod source plusReference input.2)

def pairedVariableMetricDiffeomorphismFPMinusInput
    (input : PairedVariableMetricDiffeomorphismFPCore period hPeriod plusReference minusReference) :
    RegularGeneralMetricC2Core period hPeriod minusReference ×
      DiffeomorphismGhostC2Coefficients period hPeriod :=
  (input.1.2, regularFrameDiffeomorphismGhostTransition period hPeriod source minusReference input.2)

theorem pairedVariableMetricDiffeomorphismFPPlusInput_contDiff :
    ContDiff Real ∞
      (pairedVariableMetricDiffeomorphismFPPlusInput period hPeriod
        source plusReference minusReference) := by
  have hMetric : ContDiff Real ∞
      (fun input : PairedVariableMetricDiffeomorphismFPCore period hPeriod
        plusReference minusReference => input.1.1) := contDiff_fst.fst
  have hGhost : ContDiff Real ∞
      (fun input : PairedVariableMetricDiffeomorphismFPCore period hPeriod
        plusReference minusReference =>
        regularFrameDiffeomorphismGhostTransition period hPeriod source plusReference input.2) :=
    (regularFrameDiffeomorphismGhostTransition_contDiff period hPeriod source plusReference).comp
      contDiff_snd
  have h := hMetric.prodMk hGhost
  exact h

theorem pairedVariableMetricDiffeomorphismFPMinusInput_contDiff :
    ContDiff Real ∞
      (pairedVariableMetricDiffeomorphismFPMinusInput period hPeriod
        source plusReference minusReference) := by
  have hMetric : ContDiff Real ∞
      (fun input : PairedVariableMetricDiffeomorphismFPCore period hPeriod
        plusReference minusReference => input.1.2) := contDiff_fst.snd
  have hGhost : ContDiff Real ∞
      (fun input : PairedVariableMetricDiffeomorphismFPCore period hPeriod
        plusReference minusReference =>
        regularFrameDiffeomorphismGhostTransition period hPeriod source minusReference input.2) :=
    (regularFrameDiffeomorphismGhostTransition_contDiff period hPeriod source minusReference).comp
      contDiff_snd
  have h := hMetric.prodMk hGhost
  exact h

theorem pairedVariableMetricDiffeomorphismFPPlusInput_mapsTo :
    MapsTo (pairedVariableMetricDiffeomorphismFPPlusInput period hPeriod
        source plusReference minusReference)
      (pairedVariableMetricDiffeomorphismFPDomain period hPeriod plusReference minusReference)
      (variableMetricC2DiffeomorphismFPDomain period hPeriod plusReference) :=
  fun _ hInput => ⟨hInput.1.1, mem_univ _⟩

theorem pairedVariableMetricDiffeomorphismFPMinusInput_mapsTo :
    MapsTo (pairedVariableMetricDiffeomorphismFPMinusInput period hPeriod
        source plusReference minusReference)
      (pairedVariableMetricDiffeomorphismFPDomain period hPeriod plusReference minusReference)
      (variableMetricC2DiffeomorphismFPDomain period hPeriod minusReference) :=
  fun _ hInput => ⟨hInput.1.2, mem_univ _⟩

def pairedVariableMetricDiffeomorphismFPL2
    (input : PairedVariableMetricDiffeomorphismFPCore period hPeriod plusReference minusReference) :
    (Fin 4 → CanonicalPhysicalBulkL2 period hPeriod) ×
      (Fin 4 → CanonicalPhysicalBulkL2 period hPeriod) :=
  (let plus := pairedVariableMetricDiffeomorphismFPPlusInput
      period hPeriod source plusReference minusReference input
   variableMetricC2DiffeomorphismFPL2 period hPeriod plusReference plus.1 plus.2,
   let minus := pairedVariableMetricDiffeomorphismFPMinusInput
      period hPeriod source plusReference minusReference input
   variableMetricC2DiffeomorphismFPL2 period hPeriod minusReference minus.1 minus.2)

theorem pairedVariableMetricDiffeomorphismFPL2_contDiffOn :
    ContDiffOn Real ∞
      (pairedVariableMetricDiffeomorphismFPL2 period hPeriod source plusReference minusReference)
      (pairedVariableMetricDiffeomorphismFPDomain period hPeriod plusReference minusReference) := by
  have hPlusInput : ContDiffOn Real ∞
      (pairedVariableMetricDiffeomorphismFPPlusInput period hPeriod source plusReference minusReference)
      (pairedVariableMetricDiffeomorphismFPDomain period hPeriod plusReference minusReference) :=
    (pairedVariableMetricDiffeomorphismFPPlusInput_contDiff period hPeriod
      source plusReference minusReference).contDiffOn
  have hMinusInput : ContDiffOn Real ∞
      (pairedVariableMetricDiffeomorphismFPMinusInput period hPeriod source plusReference minusReference)
      (pairedVariableMetricDiffeomorphismFPDomain period hPeriod plusReference minusReference) :=
    (pairedVariableMetricDiffeomorphismFPMinusInput_contDiff period hPeriod
      source plusReference minusReference).contDiffOn
  have hPlus := (variableMetricC2DiffeomorphismFPL2_contDiffOn period hPeriod plusReference).comp
    hPlusInput (pairedVariableMetricDiffeomorphismFPPlusInput_mapsTo
      period hPeriod source plusReference minusReference)
  have hMinus := (variableMetricC2DiffeomorphismFPL2_contDiffOn period hPeriod minusReference).comp
    hMinusInput (pairedVariableMetricDiffeomorphismFPMinusInput_mapsTo
      period hPeriod source plusReference minusReference)
  have h := hPlus.prodMk hMinus
  simp only [Function.comp_def] at h
  exact h

/-- Both completed features are the actual FP operators applied to the same smooth ghost. -/
theorem pairedVariableMetricDiffeomorphismFPL2_smooth
    (plusTensor minusTensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (plusMetric minusMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hPlusMetric : plusMetric.tensor = plusReference.metric.tensor + plusTensor)
    (hMinusMetric : minusMetric.tensor = minusReference.metric.tensor + minusTensor)
    (hPlusVariation : regularGeneralMetricSmoothC2Variation period hPeriod plusReference plusTensor ∈
      regularGeneralMetricC2Domain period hPeriod plusReference)
    (hMinusVariation : regularGeneralMetricSmoothC2Variation period hPeriod minusReference minusTensor ∈
      regularGeneralMetricC2Domain period hPeriod minusReference)
    (ghost : GlobalDiffeomorphismGhostField period hPeriod) :
    pairedVariableMetricDiffeomorphismFPL2 period hPeriod source plusReference minusReference
        ((regularGeneralMetricSmoothC2Variation period hPeriod plusReference plusTensor,
          regularGeneralMetricSmoothC2Variation period hPeriod minusReference minusTensor),
          smoothDiffeomorphismGhostC2Coefficients period hPeriod source ghost) =
      ((fun component => smoothToCanonicalPhysicalBulkL2 period hPeriod
          (globalCovectorVectorPairingField period hPeriod
            (globalGeneralMetricDiffeomorphismFaddeevPopovLinearMap period hPeriod plusMetric ghost)
            (plusReference.frame component))),
        (fun component => smoothToCanonicalPhysicalBulkL2 period hPeriod
          (globalCovectorVectorPairingField period hPeriod
            (globalGeneralMetricDiffeomorphismFaddeevPopovLinearMap period hPeriod minusMetric ghost)
            (minusReference.frame component)))) := by
  simp only [pairedVariableMetricDiffeomorphismFPL2,
    pairedVariableMetricDiffeomorphismFPPlusInput, pairedVariableMetricDiffeomorphismFPMinusInput,
    smoothDiffeomorphismGhostC2Coefficients_transition]
  apply Prod.ext
  · funext component
    exact variableMetricC2DiffeomorphismFPComponentL2_smooth period hPeriod plusReference
      plusTensor plusMetric hPlusMetric hPlusVariation ghost component
  · funext component
    exact variableMetricC2DiffeomorphismFPComponentL2_smooth period hPeriod minusReference
      minusTensor minusMetric hMinusMetric hMinusVariation ghost component

end
end P0EFTJanusPairedVariableMetricDiffeomorphismFP4D
end JanusFormal
