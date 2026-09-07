import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusVariableMetricDiffeomorphismBRSTAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRegularFrameDiffeomorphismGhostTransition4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusDiffeomorphismBRSTMetricChangeDefect4D

/-! # Mobile diagonal diffeomorphism BRST action with shared metric variables

The gauge tensor is the metric perturbation already present in the physical
chart. One independent total B/antighost/ghost triple is transported into
both reference frames. The two summands retain their actual Einstein weights.
-/

namespace JanusFormal
namespace P0EFTJanusPairedMobileDiffeomorphismBRSTAction4D

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
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPCandidateADiagonalDiffeomorphismKineticAdjointBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusVariableMetricC2DeDonderFeatures4D
open P0EFTJanusVariableMetricC2CartanFirstJet4D
open P0EFTJanusRegularFrameDiffeomorphismGhostTransition4D
open P0EFTJanusVariableMetricDiffeomorphismBRSTAction4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod
private abbrev VectorC2 := DiffeomorphismGhostC2Coefficients period hPeriod
private abbrev MetricCore (reference : RegularGeneralLorentzMetric period hPeriod) :=
  RegularGeneralMetricC2Core period hPeriod reference
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance

/-- Independent total fields, in B, antighost, ghost order, in a common source frame. -/
abbrev DiffeomorphismNonminimalC2Core :=
  VectorC2 period hPeriod × (VectorC2 period hPeriod × VectorC2 period hPeriod)

def diffeomorphismVectorC2ToContinuous :
    VectorC2 period hPeriod →L[Real] DiffeomorphismVectorC0Coefficients period hPeriod :=
  ContinuousLinearMap.pi fun index =>
    (canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod).comp
      (ContinuousLinearMap.proj index)

/-- Recover H from the existing metric variation, with no independent metric slot. -/
def metricC2PerturbationCoefficients
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (variation : MetricCore period hPeriod reference) : TensorC2Coefficients period hPeriod :=
  regularGeneralMetricC2MetricMatrix period hPeriod reference variation -
    regularGeneralMetricC2MetricMatrix period hPeriod reference 0

theorem metricC2PerturbationCoefficients_contDiff
    (reference : RegularGeneralLorentzMetric period hPeriod) :
    ContDiff Real ∞ (metricC2PerturbationCoefficients period hPeriod reference) := by
  have h := (regularGeneralMetricC2MetricMatrix_contDiff period hPeriod reference).sub
    (contDiff_const (c := regularGeneralMetricC2MetricMatrix period hPeriod reference 0))
  exact h

def sharedMetricDiffeomorphismBRSTInput
    (source reference : RegularGeneralLorentzMetric period hPeriod)
    (input : MetricCore period hPeriod reference × DiffeomorphismNonminimalC2Core period hPeriod) :
    VariableMetricDiffeomorphismBRSTCore period hPeriod reference :=
  (input.1, (metricC2PerturbationCoefficients period hPeriod reference input.1,
    (diffeomorphismVectorC2ToContinuous period hPeriod
        (regularFrameDiffeomorphismGhostTransition period hPeriod source reference input.2.1),
     (diffeomorphismVectorC2ToContinuous period hPeriod
        (regularFrameDiffeomorphismGhostTransition period hPeriod source reference input.2.2.1),
      regularFrameDiffeomorphismGhostTransition period hPeriod source reference input.2.2.2))))

theorem sharedMetricDiffeomorphismBRSTInput_contDiff
    (source reference : RegularGeneralLorentzMetric period hPeriod) :
    ContDiff Real ∞ (sharedMetricDiffeomorphismBRSTInput period hPeriod source reference) := by
  let T := regularFrameDiffeomorphismGhostTransition period hPeriod source reference
  let V := diffeomorphismVectorC2ToContinuous period hPeriod
  have hH := (metricC2PerturbationCoefficients_contDiff period hPeriod reference).comp
    (contDiff_fst (E := MetricCore period hPeriod reference)
      (F := DiffeomorphismNonminimalC2Core period hPeriod))
  have hB : ContDiff Real ∞
      (fun input : MetricCore period hPeriod reference × DiffeomorphismNonminimalC2Core period hPeriod =>
        V (T input.2.1)) := V.contDiff.comp (T.contDiff.comp contDiff_snd.fst)
  have hAntighost : ContDiff Real ∞
      (fun input : MetricCore period hPeriod reference × DiffeomorphismNonminimalC2Core period hPeriod =>
        V (T input.2.2.1)) := V.contDiff.comp (T.contDiff.comp contDiff_snd.snd.fst)
  have hGhost : ContDiff Real ∞
      (fun input : MetricCore period hPeriod reference × DiffeomorphismNonminimalC2Core period hPeriod =>
        T input.2.2.2) := T.contDiff.comp contDiff_snd.snd.snd
  have h := contDiff_fst.prodMk (hH.prodMk (hB.prodMk (hAntighost.prodMk hGhost)))
  simp only [Function.comp_def] at h
  exact h

abbrev PairedMobileDiffeomorphismBRSTCore
    (plusReference minusReference : RegularGeneralLorentzMetric period hPeriod) :=
  (MetricCore period hPeriod plusReference × MetricCore period hPeriod minusReference) ×
    DiffeomorphismNonminimalC2Core period hPeriod

variable (source plusReference minusReference : RegularGeneralLorentzMetric period hPeriod)

def pairedMobileDiffeomorphismBRSTDomain :
    Set (PairedMobileDiffeomorphismBRSTCore period hPeriod plusReference minusReference) :=
  (regularGeneralMetricC2Domain period hPeriod plusReference ×ˢ
    regularGeneralMetricC2Domain period hPeriod minusReference) ×ˢ univ

theorem pairedMobileDiffeomorphismBRSTDomain_isOpen :
    IsOpen (pairedMobileDiffeomorphismBRSTDomain period hPeriod plusReference minusReference) :=
  ((regularGeneralMetricC2Domain_isOpen period hPeriod plusReference).prod
    (regularGeneralMetricC2Domain_isOpen period hPeriod minusReference)).prod isOpen_univ

def pairedMobileDiffeomorphismBRSTPlusInput
    (input : PairedMobileDiffeomorphismBRSTCore period hPeriod plusReference minusReference) :=
  sharedMetricDiffeomorphismBRSTInput period hPeriod source plusReference (input.1.1, input.2)

def pairedMobileDiffeomorphismBRSTMinusInput
    (input : PairedMobileDiffeomorphismBRSTCore period hPeriod plusReference minusReference) :=
  sharedMetricDiffeomorphismBRSTInput period hPeriod source minusReference (input.1.2, input.2)

theorem pairedMobileDiffeomorphismBRSTPlusInput_contDiff :
    ContDiff Real ∞
      (pairedMobileDiffeomorphismBRSTPlusInput period hPeriod source plusReference minusReference) := by
  have hProjection : ContDiff Real ∞
      (fun input : PairedMobileDiffeomorphismBRSTCore period hPeriod plusReference minusReference =>
        (input.1.1, input.2)) := contDiff_fst.fst.prodMk contDiff_snd
  have h := (sharedMetricDiffeomorphismBRSTInput_contDiff period hPeriod source plusReference).comp
    hProjection
  simp only [Function.comp_def] at h
  exact h

theorem pairedMobileDiffeomorphismBRSTMinusInput_contDiff :
    ContDiff Real ∞
      (pairedMobileDiffeomorphismBRSTMinusInput period hPeriod source plusReference minusReference) := by
  have hProjection : ContDiff Real ∞
      (fun input : PairedMobileDiffeomorphismBRSTCore period hPeriod plusReference minusReference =>
        (input.1.2, input.2)) := contDiff_fst.snd.prodMk contDiff_snd
  have h := (sharedMetricDiffeomorphismBRSTInput_contDiff period hPeriod source minusReference).comp
    hProjection
  simp only [Function.comp_def] at h
  exact h

def pairedMobileDiffeomorphismBRSTAction (couplings : GlobalCandidateAActionCouplings)
    (input : PairedMobileDiffeomorphismBRSTCore period hPeriod plusReference minusReference) : Real :=
  candidateAPlusEinsteinKineticWeight couplings *
      variableMetricDiffeomorphismBRSTAction period hPeriod plusReference
        (pairedMobileDiffeomorphismBRSTPlusInput period hPeriod source plusReference minusReference input) +
    candidateAMinusEinsteinKineticWeight couplings *
      variableMetricDiffeomorphismBRSTAction period hPeriod minusReference
        (pairedMobileDiffeomorphismBRSTMinusInput period hPeriod source plusReference minusReference input)

theorem pairedMobileDiffeomorphismBRSTAction_contDiffOn_two
    (couplings : GlobalCandidateAActionCouplings) :
    ContDiffOn Real 2
      (pairedMobileDiffeomorphismBRSTAction period hPeriod source plusReference minusReference couplings)
      (pairedMobileDiffeomorphismBRSTDomain period hPeriod plusReference minusReference) := by
  have hPlusInput : ContDiffOn Real 2
      (pairedMobileDiffeomorphismBRSTPlusInput period hPeriod source plusReference minusReference)
      (pairedMobileDiffeomorphismBRSTDomain period hPeriod plusReference minusReference) :=
    ((pairedMobileDiffeomorphismBRSTPlusInput_contDiff period hPeriod source plusReference
      minusReference).of_le (by exact WithTop.coe_le_coe.mpr le_top)).contDiffOn
  have hMinusInput : ContDiffOn Real 2
      (pairedMobileDiffeomorphismBRSTMinusInput period hPeriod source plusReference minusReference)
      (pairedMobileDiffeomorphismBRSTDomain period hPeriod plusReference minusReference) :=
    ((pairedMobileDiffeomorphismBRSTMinusInput_contDiff period hPeriod source plusReference
      minusReference).of_le (by exact WithTop.coe_le_coe.mpr le_top)).contDiffOn
  have hPlus := (variableMetricDiffeomorphismBRSTAction_contDiffOn_two
    period hPeriod plusReference).comp hPlusInput (fun _ h => ⟨h.1.1, mem_univ _⟩)
  have hMinus := (variableMetricDiffeomorphismBRSTAction_contDiffOn_two
    period hPeriod minusReference).comp hMinusInput (fun _ h => ⟨h.1.2, mem_univ _⟩)
  have h := ((contDiffOn_const (c := candidateAPlusEinsteinKineticWeight couplings)).mul hPlus).add
    ((contDiffOn_const (c := candidateAMinusEinsteinKineticWeight couplings)).mul hMinus)
  simp only [Function.comp_def] at h
  exact h

theorem pairedMobileDiffeomorphismBRSTAction_hasFDerivAt
    (couplings : GlobalCandidateAActionCouplings)
    (input : PairedMobileDiffeomorphismBRSTCore period hPeriod plusReference minusReference)
    (hInput : input ∈ pairedMobileDiffeomorphismBRSTDomain period hPeriod plusReference minusReference) :
    HasFDerivAt
      (pairedMobileDiffeomorphismBRSTAction period hPeriod source plusReference minusReference couplings)
      (fderiv Real (pairedMobileDiffeomorphismBRSTAction period hPeriod source plusReference
        minusReference couplings) input) input :=
  (((pairedMobileDiffeomorphismBRSTAction_contDiffOn_two period hPeriod source plusReference
    minusReference couplings input hInput).contDiffAt
      ((pairedMobileDiffeomorphismBRSTDomain_isOpen period hPeriod plusReference minusReference).mem_nhds
        hInput)).differentiableAt (by norm_num)).hasFDerivAt

end
end P0EFTJanusPairedMobileDiffeomorphismBRSTAction4D
end JanusFormal
