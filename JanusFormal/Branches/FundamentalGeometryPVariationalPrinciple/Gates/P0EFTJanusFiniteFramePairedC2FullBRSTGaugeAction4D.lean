import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedDiffeomorphismBRSTAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2AbelianBRSTAction4D

/-! # The paired full BRST gauge contribution with shared metric variables

One metric pair supplies both the Abelian and diagonal diffeomorphism blocks.
Each sector has its own potential and Abelian nonminimal fields; one complete
diffeomorphism nonminimal packet supplies both sectors. No independent gauge
tensor H is introduced. This is the gauge contribution, not a C² claim for the
physical action, a complete covariant datum, or a global atlas.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteFramePairedC2FullBRSTGaugeAction4D

set_option autoImplicit false

noncomputable section
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDensity4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusFiniteFrameDiffeomorphismC2Core4D
open P0EFTJanusFiniteFramePairedDiffeomorphismBRSTAction4D
open P0EFTJanusFiniteFrameC2AbelianOperators4D
open P0EFTJanusFiniteFrameC2AbelianBRSTAction4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance : BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl
local instance : MeasureTheory.IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance

/-- Independent sector potentials and total Abelian B/antighost/ghost packets. -/
abbrev FiniteFramePairedC2AbelianGaugeFields
    (plusFrame minusFrame : SmoothD8Frame period hPeriod) :=
  (FiniteFrameAbelianGaugeC2Core period hPeriod plusFrame × FiniteFrameAbelianNonminimalC2Core period hPeriod) ×
    (FiniteFrameAbelianGaugeC2Core period hPeriod minusFrame × FiniteFrameAbelianNonminimalC2Core period hPeriod)

/-- A single metric pair, two Abelian field sectors and one diagonal diffeomorphism packet. -/
abbrev FiniteFramePairedC2FullBRSTGaugeCore
    (source plusFrame minusFrame : SmoothD8Frame period hPeriod)
    (plusReference minusReference : SmoothGeneralLorentzMetric period hPeriod) :=
  (GeneralMetricRelativeC2Core period hPeriod plusFrame plusReference ×
    GeneralMetricRelativeC2Core period hPeriod minusFrame minusReference) ×
      (FiniteFramePairedC2AbelianGaugeFields period hPeriod plusFrame minusFrame ×
        FiniteFrameDiffeomorphismNonminimalC2Core period hPeriod source)

variable (source plusFrame minusFrame : SmoothD8Frame period hPeriod)
  (plusReference minusReference : SmoothGeneralLorentzMetric period hPeriod)
local notation "Input" => FiniteFramePairedC2FullBRSTGaugeCore period hPeriod
  source plusFrame minusFrame plusReference minusReference

def finiteFramePairedC2FullBRSTGaugeAbelianProjection :
    Input →L[Real] FiniteFramePairedC2AbelianBRSTCore period hPeriod
      plusFrame minusFrame plusReference minusReference :=
  let metrics := ContinuousLinearMap.fst Real
    (GeneralMetricRelativeC2Core period hPeriod plusFrame plusReference ×
      GeneralMetricRelativeC2Core period hPeriod minusFrame minusReference)
    (FiniteFramePairedC2AbelianGaugeFields period hPeriod plusFrame minusFrame ×
      FiniteFrameDiffeomorphismNonminimalC2Core period hPeriod source)
  let fields : Input →L[Real] FiniteFramePairedC2AbelianGaugeFields period hPeriod plusFrame minusFrame :=
    (ContinuousLinearMap.fst Real _ _).comp (ContinuousLinearMap.snd Real _ _)
  let plusMetric := (ContinuousLinearMap.fst Real _ _).comp metrics
  let minusMetric := (ContinuousLinearMap.snd Real _ _).comp metrics
  let plusFields := (ContinuousLinearMap.fst Real _ _).comp fields
  let minusFields := (ContinuousLinearMap.snd Real _ _).comp fields
  (plusMetric.prod plusFields).prod (minusMetric.prod minusFields)

def finiteFramePairedC2FullBRSTGaugeDiffeomorphismProjection :
    Input →L[Real] FiniteFramePairedDiffeomorphismBRSTCore period hPeriod
      source plusFrame minusFrame plusReference minusReference :=
  (ContinuousLinearMap.fst Real _ _).prod
    ((ContinuousLinearMap.snd Real _ _).comp (ContinuousLinearMap.snd Real _ _))

@[simp] theorem finiteFramePairedC2FullBRSTGaugeAbelianProjection_apply (input : Input) :
    finiteFramePairedC2FullBRSTGaugeAbelianProjection period hPeriod source plusFrame minusFrame
        plusReference minusReference input =
      ((input.1.1, input.2.1.1), (input.1.2, input.2.1.2)) := rfl

@[simp] theorem finiteFramePairedC2FullBRSTGaugeDiffeomorphismProjection_apply (input : Input) :
    finiteFramePairedC2FullBRSTGaugeDiffeomorphismProjection period hPeriod source plusFrame minusFrame
        plusReference minusReference input = (input.1, input.2.2) := rfl

def finiteFramePairedC2FullBRSTGaugeDomain : Set Input :=
  Set.prod
    (Set.prod (generalMetricRelativeC2VolumeDomain period hPeriod plusFrame plusReference)
      (generalMetricRelativeC2VolumeDomain period hPeriod minusFrame minusReference)) Set.univ

theorem finiteFramePairedC2FullBRSTGaugeDomain_isOpen :
    IsOpen (finiteFramePairedC2FullBRSTGaugeDomain period hPeriod source plusFrame minusFrame
      plusReference minusReference) :=
  ((generalMetricRelativeC2VolumeDomain_isOpen period hPeriod plusFrame plusReference).prod
    (generalMetricRelativeC2VolumeDomain_isOpen period hPeriod minusFrame minusReference)).prod isOpen_univ

def finiteFramePairedC2FullBRSTGaugeAction (couplings : GlobalCandidateAActionCouplings)
    (input : Input) : Real :=
  finiteFramePairedC2AbelianBRSTAction period hPeriod plusFrame minusFrame plusReference minusReference
      (finiteFramePairedC2FullBRSTGaugeAbelianProjection period hPeriod source plusFrame minusFrame
        plusReference minusReference input) +
    finiteFramePairedDiffeomorphismBRSTAction period hPeriod source plusFrame minusFrame
      plusReference minusReference couplings
      (finiteFramePairedC2FullBRSTGaugeDiffeomorphismProjection period hPeriod source plusFrame minusFrame
        plusReference minusReference input)

theorem finiteFramePairedC2FullBRSTGaugeAction_contDiffOn_two
    (couplings : GlobalCandidateAActionCouplings) :
    ContDiffOn Real 2 (finiteFramePairedC2FullBRSTGaugeAction period hPeriod source plusFrame minusFrame
      plusReference minusReference couplings)
      (finiteFramePairedC2FullBRSTGaugeDomain period hPeriod source plusFrame minusFrame
        plusReference minusReference) := by
  have hAbelianProjection : ContDiffOn Real ∞
      (finiteFramePairedC2FullBRSTGaugeAbelianProjection period hPeriod source plusFrame minusFrame
        plusReference minusReference)
      (finiteFramePairedC2FullBRSTGaugeDomain period hPeriod source plusFrame minusFrame
        plusReference minusReference) :=
    (finiteFramePairedC2FullBRSTGaugeAbelianProjection period hPeriod source plusFrame minusFrame
      plusReference minusReference).contDiff.contDiffOn
  have hAbelian := (finiteFramePairedC2AbelianBRSTAction_contDiffOn period hPeriod
    plusFrame minusFrame plusReference minusReference).comp hAbelianProjection
      (fun _ h => ⟨⟨h.1.1.1, Set.mem_univ _⟩, ⟨h.1.2.1, Set.mem_univ _⟩⟩)
  have hDiffeomorphismProjection : ContDiffOn Real 2
      (finiteFramePairedC2FullBRSTGaugeDiffeomorphismProjection period hPeriod source plusFrame minusFrame
        plusReference minusReference)
      (finiteFramePairedC2FullBRSTGaugeDomain period hPeriod source plusFrame minusFrame
        plusReference minusReference) :=
    ((finiteFramePairedC2FullBRSTGaugeDiffeomorphismProjection period hPeriod source plusFrame minusFrame
      plusReference minusReference).contDiff.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffOn
  have hDiffeomorphism := (finiteFramePairedDiffeomorphismBRSTAction_contDiffOn_two period hPeriod
    source plusFrame minusFrame plusReference minusReference couplings).comp hDiffeomorphismProjection
      (fun _ h => ⟨h.1, Set.mem_univ _⟩)
  have h := (hAbelian.of_le (WithTop.coe_le_coe.mpr le_top)).add hDiffeomorphism
  simp only [Function.comp_def] at h
  exact h

/-- The actual Fréchet derivative of the two realized gauge contributions. -/
def finiteFramePairedC2FullBRSTGaugeEuler (couplings : GlobalCandidateAActionCouplings)
    (input : Input) : Input →L[Real] Real :=
  fderiv Real (finiteFramePairedC2FullBRSTGaugeAction period hPeriod source plusFrame minusFrame
    plusReference minusReference couplings) input

theorem finiteFramePairedC2FullBRSTGaugeAction_hasFDerivAt
    (couplings : GlobalCandidateAActionCouplings) (input : Input)
    (hInput : input ∈ finiteFramePairedC2FullBRSTGaugeDomain period hPeriod source plusFrame minusFrame
      plusReference minusReference) :
    HasFDerivAt
      (finiteFramePairedC2FullBRSTGaugeAction period hPeriod source plusFrame minusFrame
        plusReference minusReference couplings)
      (finiteFramePairedC2FullBRSTGaugeEuler period hPeriod source plusFrame minusFrame
        plusReference minusReference couplings input) input :=
  (((finiteFramePairedC2FullBRSTGaugeAction_contDiffOn_two period hPeriod source plusFrame minusFrame
    plusReference minusReference couplings input hInput).contDiffAt
      ((finiteFramePairedC2FullBRSTGaugeDomain_isOpen period hPeriod source plusFrame minusFrame
        plusReference minusReference).mem_nhds hInput)).differentiableAt (by norm_num)).hasFDerivAt

def finiteFrameSmoothPairedC2FullBRSTGaugeCore
    (sourceReference : SmoothGeneralLorentzMetric period hPeriod)
    (plusTensor minusTensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (abelian : GlobalPairedAbelianBRSTState period hPeriod)
    (diffeomorphism : GlobalDiffeomorphismNonminimalFields period hPeriod) : Input :=
  ((smoothToGeneralMetricRelativeC2Core period hPeriod plusFrame plusReference plusTensor,
    smoothToGeneralMetricRelativeC2Core period hPeriod minusFrame minusReference minusTensor),
    (((finiteFrameSmoothAbelianBRSTCore period hPeriod plusFrame plusReference plusTensor
        (abelian.potential .plus) (abelian.nonminimal .plus)).2,
      (finiteFrameSmoothAbelianBRSTCore period hPeriod minusFrame minusReference minusTensor
        (abelian.potential .minus) (abelian.nonminimal .minus)).2),
      finiteFrameSmoothDiffeomorphismNonminimalC2Core period hPeriod source sourceReference diffeomorphism))

theorem finiteFrameSmoothPairedC2FullBRSTGaugeCore_mem
    (sourceReference : SmoothGeneralLorentzMetric period hPeriod)
    (plusTensor minusTensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (abelian : GlobalPairedAbelianBRSTState period hPeriod)
    (diffeomorphism : GlobalDiffeomorphismNonminimalFields period hPeriod)
    (hPlusVolume : smoothToGeneralMetricRelativeC2Core period hPeriod plusFrame plusReference plusTensor ∈
      generalMetricRelativeC2VolumeDomain period hPeriod plusFrame plusReference)
    (hMinusVolume : smoothToGeneralMetricRelativeC2Core period hPeriod minusFrame minusReference minusTensor ∈
      generalMetricRelativeC2VolumeDomain period hPeriod minusFrame minusReference) :
    finiteFrameSmoothPairedC2FullBRSTGaugeCore period hPeriod source plusFrame minusFrame
        plusReference minusReference sourceReference plusTensor minusTensor abelian diffeomorphism ∈
      finiteFramePairedC2FullBRSTGaugeDomain period hPeriod source plusFrame minusFrame
        plusReference minusReference :=
  ⟨⟨hPlusVolume, hMinusVolume⟩, Set.mem_univ _⟩

theorem finiteFramePairedC2FullBRSTGaugeAbelianProjection_smooth
    (sourceReference : SmoothGeneralLorentzMetric period hPeriod)
    (plusTensor minusTensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (abelian : GlobalPairedAbelianBRSTState period hPeriod)
    (diffeomorphism : GlobalDiffeomorphismNonminimalFields period hPeriod) :
    finiteFramePairedC2FullBRSTGaugeAbelianProjection period hPeriod source plusFrame minusFrame
        plusReference minusReference
        (finiteFrameSmoothPairedC2FullBRSTGaugeCore period hPeriod source plusFrame minusFrame
          plusReference minusReference sourceReference plusTensor minusTensor abelian diffeomorphism) =
      (finiteFrameSmoothAbelianBRSTCore period hPeriod plusFrame plusReference plusTensor
        (abelian.potential .plus) (abelian.nonminimal .plus),
       finiteFrameSmoothAbelianBRSTCore period hPeriod minusFrame minusReference minusTensor
        (abelian.potential .minus) (abelian.nonminimal .minus)) := rfl

theorem finiteFramePairedC2FullBRSTGaugeDiffeomorphismProjection_smooth
    (sourceReference : SmoothGeneralLorentzMetric period hPeriod)
    (plusTensor minusTensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (abelian : GlobalPairedAbelianBRSTState period hPeriod)
    (diffeomorphism : GlobalDiffeomorphismNonminimalFields period hPeriod) :
    finiteFramePairedC2FullBRSTGaugeDiffeomorphismProjection period hPeriod source plusFrame minusFrame
        plusReference minusReference
        (finiteFrameSmoothPairedC2FullBRSTGaugeCore period hPeriod source plusFrame minusFrame
          plusReference minusReference sourceReference plusTensor minusTensor abelian diffeomorphism) =
      finiteFrameSmoothPairedDiffeomorphismBRSTCore period hPeriod source plusFrame minusFrame
        plusReference minusReference sourceReference plusTensor minusTensor diffeomorphism := rfl

/-- SAME-ACTION for the full gauge contribution with the same metrics, potentials and fields. -/
theorem finiteFramePairedC2FullBRSTGaugeAction_smooth
    (sourceReference : SmoothGeneralLorentzMetric period hPeriod)
    (couplings : GlobalCandidateAActionCouplings)
    (plusTensor minusTensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (hPlusMetric : (metric .plus).tensor = plusReference.tensor + plusTensor)
    (hMinusMetric : (metric .minus).tensor = minusReference.tensor + minusTensor)
    (hPlusVolume : smoothToGeneralMetricRelativeC2Core period hPeriod plusFrame plusReference plusTensor ∈
      generalMetricRelativeC2VolumeDomain period hPeriod plusFrame plusReference)
    (hMinusVolume : smoothToGeneralMetricRelativeC2Core period hPeriod minusFrame minusReference minusTensor ∈
      generalMetricRelativeC2VolumeDomain period hPeriod minusFrame minusReference)
    (abelian : GlobalPairedAbelianBRSTState period hPeriod)
    (diffeomorphism : GlobalDiffeomorphismNonminimalFields period hPeriod) :
    finiteFramePairedC2FullBRSTGaugeAction period hPeriod source plusFrame minusFrame
        plusReference minusReference couplings
        (finiteFrameSmoothPairedC2FullBRSTGaugeCore period hPeriod source plusFrame minusFrame
          plusReference minusReference sourceReference plusTensor minusTensor abelian diffeomorphism) =
      globalPairedAbelianGaugeFermionBRSTAction period hPeriod metric abelian
          (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) +
        globalCandidateADiagonalDiffeomorphismGaugeFermionBRSTVariation period hPeriod couplings metric
          { metricPerturbation := fun | .plus => plusTensor | .minus => minusTensor
            nonminimal := diffeomorphism } := by
  unfold finiteFramePairedC2FullBRSTGaugeAction
  rw [finiteFramePairedC2FullBRSTGaugeAbelianProjection_smooth,
    finiteFramePairedC2FullBRSTGaugeDiffeomorphismProjection_smooth,
    finiteFramePairedC2AbelianBRSTAction_smooth period hPeriod plusFrame minusFrame plusReference minusReference
      plusTensor minusTensor metric hPlusMetric hMinusMetric hPlusVolume.1 hMinusVolume.1 abelian,
    finiteFramePairedDiffeomorphismBRSTAction_smooth_eq_BRST period hPeriod source plusFrame minusFrame
      plusReference minusReference sourceReference couplings plusTensor minusTensor metric
      hPlusMetric hMinusMetric hPlusVolume hMinusVolume diffeomorphism]
  rfl

end
end P0EFTJanusFiniteFramePairedC2FullBRSTGaugeAction4D
end JanusFormal
