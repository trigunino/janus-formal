import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPairedMobileDiffeomorphismBRSTAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusVariableMetricDiffeomorphismBRSTSmoothAgreement4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPairedVariableMetricDiffeomorphismFP4D

/-! # Paired mobile diffeomorphism BRST agrees with the same smooth action

The gauge tensor is exactly the physical metric variation. One arbitrary
nonminimal triple supplies both sectors through their fixed frame transitions.
-/

namespace JanusFormal
namespace P0EFTJanusPairedMobileDiffeomorphismBRSTSmoothAgreement4D

set_option autoImplicit false
set_option maxHeartbeats 1600000
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
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open P0EFTJanusProgramPGeneralMetricC2VariationCore4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusRegularFrameMetricCartanCoefficients4D
open P0EFTJanusRegularFrameDiffeomorphismGhostTransition4D
open P0EFTJanusVariableMetricC2TensorTraceSmoothAgreement4D
open P0EFTJanusVariableMetricC2DiffeomorphismFPSmoothAgreement4D
open P0EFTJanusPairedVariableMetricDiffeomorphismFP4D
open P0EFTJanusVariableMetricDiffeomorphismBRSTAction4D
open P0EFTJanusVariableMetricDiffeomorphismBRSTSmoothAgreement4D
open P0EFTJanusPairedMobileDiffeomorphismBRSTAction4D

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

private theorem metricC2Matrix_smooth_eq_tensor
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    regularGeneralMetricC2MetricMatrix period hPeriod reference
        (regularGeneralMetricSmoothC2Variation period hPeriod reference tensor) =
      smoothTensorC2Coefficients period hPeriod reference (reference.metric.tensor + tensor) := by
  change regularGeneralMetricC2MetricMatrix period hPeriod reference
    (smoothToGeneralMetricRelativeC2Core period hPeriod
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference) reference.metric tensor) = _
  rw [candidateANormalBoundaryRegularGeneralMetricC2MetricMatrix_smooth]
  funext first second
  change smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
      (candidateANormalBoundarySmoothRegularGeneralMetricActualMatrix
        period hPeriod reference tensor first second) = _
  apply congrArg (smoothToCanonicalPhysicalScalarC2JetCore period hPeriod)
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  exact (candidateANormalBoundaryRegularGeneralMetricC0MetricCoefficient_smooth_eq_actualMatrix
    period hPeriod reference tensor first second point).symm.trans
      (candidateANormalBoundaryRegularGeneralMetricC0MetricCoefficient_smooth
        period hPeriod reference tensor first second point)

/-- Subtracting the chart centre recovers exactly the same smooth physical perturbation. -/
theorem metricC2PerturbationCoefficients_smooth
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    metricC2PerturbationCoefficients period hPeriod reference
        (regularGeneralMetricSmoothC2Variation period hPeriod reference tensor) =
      smoothTensorC2Coefficients period hPeriod reference tensor := by
  have hZero : regularGeneralMetricSmoothC2Variation period hPeriod reference
      (0 : SmoothSymmetricCovariantTwoTensor period hPeriod) = 0 :=
    (smoothToGeneralMetricRelativeC2Core period hPeriod
      (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference) reference.metric).map_zero
  unfold metricC2PerturbationCoefficients
  rw [metricC2Matrix_smooth_eq_tensor, ← hZero, metricC2Matrix_smooth_eq_tensor]
  simp only [smoothTensorC2Coefficients, add_zero, map_add]
  abel

theorem diffeomorphismVectorC2ToContinuous_smooth
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (ghost : GlobalDiffeomorphismGhostField period hPeriod) :
    diffeomorphismVectorC2ToContinuous period hPeriod
        (smoothDiffeomorphismGhostC2Coefficients period hPeriod reference ghost) =
      smoothDiffeomorphismVectorC0Coefficients period hPeriod reference ghost.field := by
  funext index
  exact canonicalPhysicalScalarC2JetCoreToContinuous_smooth period hPeriod
    (regularFrameCartanGhostCoefficient period hPeriod reference ghost.field index)

/-- One full geometric nonminimal triple in the chosen common source frame. -/
def smoothDiffeomorphismNonminimalC2Core
    (source : RegularGeneralLorentzMetric period hPeriod)
    (fields : GlobalDiffeomorphismNonminimalFields period hPeriod) :
    DiffeomorphismNonminimalC2Core period hPeriod :=
  (smoothDiffeomorphismGhostC2Coefficients period hPeriod source ⟨fields.nakanishiLautrup.field⟩,
    (smoothDiffeomorphismGhostC2Coefficients period hPeriod source ⟨fields.antighost.field⟩,
      smoothDiffeomorphismGhostC2Coefficients period hPeriod source fields.ghost))

/-- The tensor slot and all transported fields coincide with the single-sector smooth lift. -/
theorem sharedMetricDiffeomorphismBRSTInput_smooth
    (source reference : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (fields : GlobalDiffeomorphismNonminimalFields period hPeriod) :
    sharedMetricDiffeomorphismBRSTInput period hPeriod source reference
        (regularGeneralMetricSmoothC2Variation period hPeriod reference tensor,
          smoothDiffeomorphismNonminimalC2Core period hPeriod source fields) =
      smoothVariableMetricDiffeomorphismBRSTCore period hPeriod reference tensor
        { metricPerturbation := tensor, nonminimal := fields } := by
  simp only [sharedMetricDiffeomorphismBRSTInput, smoothDiffeomorphismNonminimalC2Core,
    metricC2PerturbationCoefficients_smooth, smoothDiffeomorphismGhostC2Coefficients_transition,
    diffeomorphismVectorC2ToContinuous_smooth, smoothVariableMetricDiffeomorphismBRSTCore]

def smoothPairedMobileDiffeomorphismBRSTCore
    (source plusReference minusReference : RegularGeneralLorentzMetric period hPeriod)
    (plusTensor minusTensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (fields : GlobalDiffeomorphismNonminimalFields period hPeriod) :
    PairedMobileDiffeomorphismBRSTCore period hPeriod plusReference minusReference :=
  ((regularGeneralMetricSmoothC2Variation period hPeriod plusReference plusTensor,
    regularGeneralMetricSmoothC2Variation period hPeriod minusReference minusTensor),
    smoothDiffeomorphismNonminimalC2Core period hPeriod source fields)

theorem smoothPairedMobileDiffeomorphismBRSTCore_mem_domain
    (source plusReference minusReference : RegularGeneralLorentzMetric period hPeriod)
    (plusTensor minusTensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (fields : GlobalDiffeomorphismNonminimalFields period hPeriod)
    (hPlusVariation : regularGeneralMetricSmoothC2Variation period hPeriod plusReference plusTensor ∈
      regularGeneralMetricC2Domain period hPeriod plusReference)
    (hMinusVariation : regularGeneralMetricSmoothC2Variation period hPeriod minusReference minusTensor ∈
      regularGeneralMetricC2Domain period hPeriod minusReference) :
    smoothPairedMobileDiffeomorphismBRSTCore period hPeriod source plusReference minusReference
        plusTensor minusTensor fields ∈
      pairedMobileDiffeomorphismBRSTDomain period hPeriod plusReference minusReference :=
  ⟨⟨hPlusVariation, hMinusVariation⟩, mem_univ _⟩

/-- SAME-ACTION with one metric perturbation per sector and one shared nonminimal triple. -/
theorem pairedMobileDiffeomorphismBRSTAction_smooth_eq_BRST
    (source plusReference minusReference : RegularGeneralLorentzMetric period hPeriod)
    (couplings : GlobalCandidateAActionCouplings)
    (plusTensor minusTensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (hPlusMetric : (metric .plus).tensor = plusReference.metric.tensor + plusTensor)
    (hMinusMetric : (metric .minus).tensor = minusReference.metric.tensor + minusTensor)
    (hPlusVariation : regularGeneralMetricSmoothC2Variation period hPeriod plusReference plusTensor ∈
      regularGeneralMetricC2Domain period hPeriod plusReference)
    (hMinusVariation : regularGeneralMetricSmoothC2Variation period hPeriod minusReference minusTensor ∈
      regularGeneralMetricC2Domain period hPeriod minusReference)
    (fields : GlobalDiffeomorphismNonminimalFields period hPeriod) :
    pairedMobileDiffeomorphismBRSTAction period hPeriod source plusReference minusReference couplings
        (smoothPairedMobileDiffeomorphismBRSTCore period hPeriod source plusReference minusReference
          plusTensor minusTensor fields) =
      globalCandidateADiagonalDiffeomorphismGaugeFermionBRSTVariation period hPeriod couplings metric
        { metricPerturbation := fun | .plus => plusTensor | .minus => minusTensor
          nonminimal := fields } := by
  simp only [pairedMobileDiffeomorphismBRSTAction,
    pairedMobileDiffeomorphismBRSTPlusInput, pairedMobileDiffeomorphismBRSTMinusInput,
    smoothPairedMobileDiffeomorphismBRSTCore, sharedMetricDiffeomorphismBRSTInput_smooth]
  rw [variableMetricDiffeomorphismBRSTAction_smooth_eq_BRST period hPeriod plusReference
      plusTensor (metric .plus) hPlusMetric hPlusVariation,
    variableMetricDiffeomorphismBRSTAction_smooth_eq_BRST period hPeriod minusReference
      minusTensor (metric .minus) hMinusMetric hMinusVariation]
  all_goals rfl

end
end P0EFTJanusPairedMobileDiffeomorphismBRSTSmoothAgreement4D
end JanusFormal
