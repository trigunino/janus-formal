import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusAnomalySelection
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusExplicitReciprocalCrossDensities
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPTFlatBimetricVariationalBridge

/-!
Scheme-freedom audit for explicit Program-P Candidate A parameters.

The integer below is only the parity-odd anomaly proxy already used by the
Program-P anomaly gate.  PT pairing cancels that proxy algebraically.  No
determinant line, regulator, local/global anomaly, or physical Janus anomaly is
computed here.  The audit instead proves that this cancellation leaves both an
overall action normalization and a flat-vanishing reduced parity-even
finite-counterterm proxy undetermined.
-/

namespace JanusFormal
namespace P0EFTJanusCandidateSchemeFreedomAudit

set_option autoImplicit false

noncomputable section

open P0EFTJanusAnomalySelection
open P0EFTJanusExplicitReciprocalCrossDensities
open P0EFTJanusReciprocalBimetricPotential
open P0EFTJanusPTSymmetricFlatBimetricBranch
open P0EFTJanusPTFlatBimetricVariationalBridge

/-- Explicit Candidate A parameters together with two scheme choices.  The
`singleFoldAnomalyProxy` is input data, not a computed Janus anomaly. -/
@[ext] structure CandidateASchemeParameters where
  beta1 : ℝ
  beta2 : ℝ
  interactionScale : ℝ
  overallActionNormalization : ℝ
  finiteEvenCounterterm : ℝ
  singleFoldAnomalyProxy : ℤ

/-- Candidate A uses the committed PT-symmetric flat coefficient family. -/
def candidateACoefficients
    (parameters : CandidateASchemeParameters) : PotentialCoefficients :=
  ptFlatCoefficients parameters.beta1 parameters.beta2

/-- The explicit common Candidate A interaction restricted to a proportional
square-root spectrum is the previously derived PT-flat energy. -/
theorem candidateA_commonInteraction_eq_scaled_ptFlatEnergy
    (parameters : CandidateASchemeParameters) (c : ℝ) :
    commonInteractionPotential parameters.interactionScale
        (candidateACoefficients parameters) (proportionalSpectrum c) =
      parameters.interactionScale *
        proportionalInteractionEnergy parameters.beta1 parameters.beta2 c := by
  rw [commonInteractionPotential, spectralPotential_on_proportionalSpectrum]
  unfold candidateACoefficients proportionalInteractionEnergy
  ring

/-- A reduced parity-even finite-counterterm proxy chosen to vanish to fourth
order at the flat proportional point.  Covariant admissibility is not inferred. -/
def candidateAEvenCounterterm
    (parameters : CandidateASchemeParameters) (c : ℝ) : ℝ :=
  parameters.finiteEvenCounterterm * (c - 1) ^ 4

/-- Reduced even action used only to audit normalization and scheme freedom. -/
def candidateAReducedEvenAction
    (parameters : CandidateASchemeParameters) (c : ℝ) : ℝ :=
  parameters.overallActionNormalization *
      (parameters.interactionScale *
        proportionalInteractionEnergy parameters.beta1 parameters.beta2 c) +
    candidateAEvenCounterterm parameters c

theorem candidateAReducedEvenAction_eq_explicit_commonInteraction
    (parameters : CandidateASchemeParameters) (c : ℝ) :
    candidateAReducedEvenAction parameters c =
      parameters.overallActionNormalization *
          commonInteractionPotential parameters.interactionScale
            (candidateACoefficients parameters) (proportionalSpectrum c) +
        candidateAEvenCounterterm parameters c := by
  rw [candidateA_commonInteraction_eq_scaled_ptFlatEnergy]
  rfl

/-- Audited first variation: the interaction force is the actual derivative
proved in the imported PT-flat bridge, while the second term is the elementary
derivative of the displayed fourth-order polynomial. -/
def candidateAReducedEvenFirstVariation
    (parameters : CandidateASchemeParameters) (c : ℝ) : ℝ :=
  parameters.overallActionNormalization *
      (parameters.interactionScale *
        proportionalInteractionForce parameters.beta1 parameters.beta2 c) +
    4 * parameters.finiteEvenCounterterm * (c - 1) ^ 3

/-- Flat compatibility means zero reduced action and zero audited first
variation at the symmetric proportional point. -/
def CandidateAFlatCompatible
    (parameters : CandidateASchemeParameters) : Prop :=
  candidateAReducedEvenAction parameters 1 = 0 ∧
    candidateAReducedEvenFirstVariation parameters 1 = 0

/-- Every normalization and every finite-even coefficient preserve this
explicit flat point. -/
theorem candidateA_flat_compatible
    (parameters : CandidateASchemeParameters) :
    CandidateAFlatCompatible parameters := by
  constructor
  · simp [candidateAReducedEvenAction, candidateAEvenCounterterm,
      interaction_energy_at_symmetric_point]
  · simp [candidateAReducedEvenFirstVariation,
      proportionalInteractionForce]

/-- Candidate A data mapped to the existing parity-odd/even audit record. -/
def candidateAFoldAnomalyDecoration
    (parameters : CandidateASchemeParameters) : AnomalyDecoratedAction :=
  { anomalyCoefficient := parameters.singleFoldAnomalyProxy
    parityEvenCoupling :=
      parameters.overallActionNormalization * parameters.interactionScale
    finiteEvenCounterterm := parameters.finiteEvenCounterterm }

/-- PT-paired anomaly/even data for Candidate A. -/
def candidateAPTPairDecoration
    (parameters : CandidateASchemeParameters) : AnomalyDecoratedAction :=
  ptPair (candidateAFoldAnomalyDecoration parameters)

/-- Algebraic PT pairing cancels the supplied parity-odd proxy for every
explicit Candidate A parameter record. -/
theorem candidateA_pt_paired_anomaly_proxy_cancels
    (parameters : CandidateASchemeParameters) :
    AnomalyFree (candidateAPTPairDecoration parameters) := by
  exact pt_pair_anomaly_cancels (candidateAFoldAnomalyDecoration parameters)

/-- The PT-paired even coupling retains the overall normalization. -/
theorem candidateA_pt_pair_even_coupling
    (parameters : CandidateASchemeParameters) :
    (candidateAPTPairDecoration parameters).parityEvenCoupling =
      2 * (parameters.overallActionNormalization *
        parameters.interactionScale) := by
  exact pt_pair_even_coupling_doubles
    (candidateAFoldAnomalyDecoration parameters)

/-- The allowed finite parity-even coefficient also survives PT pairing. -/
theorem candidateA_pt_pair_finite_even_counterterm
    (parameters : CandidateASchemeParameters) :
    (candidateAPTPairDecoration parameters).finiteEvenCounterterm =
      2 * parameters.finiteEvenCounterterm := by
  exact pt_pair_even_counterterm_doubles
    (candidateAFoldAnomalyDecoration parameters)

def baselineCandidateA : CandidateASchemeParameters where
  beta1 := 1
  beta2 := 0
  interactionScale := 1
  overallActionNormalization := 1
  finiteEvenCounterterm := 0
  singleFoldAnomalyProxy := 1

/-- Same explicit Candidate A core and normalization, with only the allowed
finite parity-even coefficient changed. -/
def finiteShiftCandidateA : CandidateASchemeParameters where
  beta1 := 1
  beta2 := 0
  interactionScale := 1
  overallActionNormalization := 1
  finiteEvenCounterterm := 1
  singleFoldAnomalyProxy := 1

/-- Same explicit Candidate A core and finite term, with only the overall
normalization changed. -/
def normalizationShiftCandidateA : CandidateASchemeParameters where
  beta1 := 1
  beta2 := 0
  interactionScale := 1
  overallActionNormalization := 2
  finiteEvenCounterterm := 0
  singleFoldAnomalyProxy := 1

/-- The baseline and finite-shift records are both flat/anomaly compatible and
differ only in the finite-even scheme coefficient. -/
theorem finite_even_scheme_freedom_witness :
    CandidateAFlatCompatible baselineCandidateA ∧
      CandidateAFlatCompatible finiteShiftCandidateA ∧
      AnomalyFree (candidateAPTPairDecoration baselineCandidateA) ∧
      AnomalyFree (candidateAPTPairDecoration finiteShiftCandidateA) ∧
      baselineCandidateA.beta1 = finiteShiftCandidateA.beta1 ∧
      baselineCandidateA.beta2 = finiteShiftCandidateA.beta2 ∧
      baselineCandidateA.interactionScale =
        finiteShiftCandidateA.interactionScale ∧
      baselineCandidateA.overallActionNormalization =
        finiteShiftCandidateA.overallActionNormalization ∧
      baselineCandidateA.singleFoldAnomalyProxy =
        finiteShiftCandidateA.singleFoldAnomalyProxy ∧
      baselineCandidateA.finiteEvenCounterterm ≠
        finiteShiftCandidateA.finiteEvenCounterterm := by
  refine ⟨candidateA_flat_compatible _, candidateA_flat_compatible _,
    candidateA_pt_paired_anomaly_proxy_cancels _,
    candidateA_pt_paired_anomaly_proxy_cancels _, ?_⟩
  norm_num [baselineCandidateA, finiteShiftCandidateA]

/-- The baseline and normalization-shift records are both flat/anomaly
compatible and differ only in overall normalization. -/
theorem overall_normalization_freedom_witness :
    CandidateAFlatCompatible baselineCandidateA ∧
      CandidateAFlatCompatible normalizationShiftCandidateA ∧
      AnomalyFree (candidateAPTPairDecoration baselineCandidateA) ∧
      AnomalyFree (candidateAPTPairDecoration normalizationShiftCandidateA) ∧
      baselineCandidateA.beta1 = normalizationShiftCandidateA.beta1 ∧
      baselineCandidateA.beta2 = normalizationShiftCandidateA.beta2 ∧
      baselineCandidateA.interactionScale =
        normalizationShiftCandidateA.interactionScale ∧
      baselineCandidateA.finiteEvenCounterterm =
        normalizationShiftCandidateA.finiteEvenCounterterm ∧
      baselineCandidateA.singleFoldAnomalyProxy =
        normalizationShiftCandidateA.singleFoldAnomalyProxy ∧
      baselineCandidateA.overallActionNormalization ≠
        normalizationShiftCandidateA.overallActionNormalization := by
  refine ⟨candidateA_flat_compatible _, candidateA_flat_compatible _,
    candidateA_pt_paired_anomaly_proxy_cancels _,
    candidateA_pt_paired_anomaly_proxy_cancels _, ?_⟩
  norm_num [baselineCandidateA, normalizationShiftCandidateA]

def CandidateAAnomalyFlatAdmissible
    (parameters : CandidateASchemeParameters) : Prop :=
  CandidateAFlatCompatible parameters ∧
    AnomalyFree (candidateAPTPairDecoration parameters)

/-- No-go: even after imposing the explicit flat point and PT cancellation of
the supplied anomaly proxy, Candidate A parameters are not uniquely selected.
Thus anomaly cancellation alone fixes neither the finite-even scheme nor the
overall action normalization. -/
theorem anomaly_cancellation_alone_cannot_fix_candidateA_scheme :
    ¬ ∀ first second : CandidateASchemeParameters,
      CandidateAAnomalyFlatAdmissible first →
      CandidateAAnomalyFlatAdmissible second →
      first = second := by
  intro hUnique
  have hEqual := hUnique baselineCandidateA finiteShiftCandidateA
    ⟨candidateA_flat_compatible _,
      candidateA_pt_paired_anomaly_proxy_cancels _⟩
    ⟨candidateA_flat_compatible _,
      candidateA_pt_paired_anomaly_proxy_cancels _⟩
  have hFinite := congrArg CandidateASchemeParameters.finiteEvenCounterterm hEqual
  norm_num [baselineCandidateA, finiteShiftCandidateA] at hFinite

/- This audit is conditional on the supplied integer proxy and PT sign rule;
it is not evidence that the physical Janus determinant line is anomaly-free. -/

end

end P0EFTJanusCandidateSchemeFreedomAudit
end JanusFormal
