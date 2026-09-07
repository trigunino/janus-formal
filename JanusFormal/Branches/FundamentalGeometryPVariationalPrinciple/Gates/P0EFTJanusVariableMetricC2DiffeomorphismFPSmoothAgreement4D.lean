import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusVariableMetricC2DiffeomorphismFPFeatures4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusVariableMetricC2CartanSmoothJet4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusVariableMetricC2DeDonderSmoothAgreement4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalGeneralMetricDiffeomorphismFaddeevPopov4D

/-! # Exact smooth agreement of the mobile diffeomorphism FP feature -/

namespace JanusFormal
namespace P0EFTJanusVariableMetricC2DiffeomorphismFPSmoothAgreement4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 600000
noncomputable section
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothL2Density4D
open P0EFTJanusMappingTorusMetricCartanGlobalAction4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalGeneralMetricDiffeomorphismFaddeevPopov4D
open P0EFTJanusRegularFrameMetricCartanCoefficients4D
open P0EFTJanusVariableMetricC2TensorTraceSmoothAgreement4D
open P0EFTJanusVariableMetricC2DeDonderSmoothAgreement4D
open P0EFTJanusVariableMetricDeDonderFirstJet4D
open P0EFTJanusVariableMetricC2CartanFirstJet4D
open P0EFTJanusVariableMetricC2CartanSmoothJet4D
open P0EFTJanusVariableMetricC2DiffeomorphismFPFeatures4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

/-- The coefficients of the given geometric ghost, rather than an independent replacement. -/
def smoothDiffeomorphismGhostC2Coefficients
    (reference : RegularGeneralLorentzMetric period hPeriod)
    (ghost : GlobalDiffeomorphismGhostField period hPeriod) :
    DiffeomorphismGhostC2Coefficients period hPeriod :=
  fun index => smoothToCanonicalPhysicalScalarC2JetCore period hPeriod
    (regularFrameCartanGhostCoefficient period hPeriod reference ghost.field index)

variable (reference : RegularGeneralLorentzMetric period hPeriod)
  (variationTensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
  (metric : SmoothGeneralLorentzMetric period hPeriod)
  (hMetric : metric.tensor = reference.metric.tensor + variationTensor)
  (hVariation : regularGeneralMetricSmoothC2Variation period hPeriod reference variationTensor ∈
    regularGeneralMetricC2Domain period hPeriod reference)
  (ghost : GlobalDiffeomorphismGhostField period hPeriod)
include hMetric hVariation

/-- The completed feature equals the existing intrinsic Faddeev--Popov operator. -/
theorem variableMetricC2DiffeomorphismFPComponentExpression_smooth
    (component : Fin 4) :
    variableMetricC2DiffeomorphismFPComponentExpression period hPeriod reference
        (regularGeneralMetricSmoothC2Variation period hPeriod reference variationTensor)
        (smoothDiffeomorphismGhostC2Coefficients period hPeriod reference ghost) component =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (globalCovectorVectorPairingField period hPeriod
          (globalGeneralMetricDiffeomorphismFaddeevPopovLinearMap period hPeriod metric ghost)
          (reference.frame component)) := by
  unfold variableMetricC2DiffeomorphismFPComponentExpression
    smoothDiffeomorphismGhostC2Coefficients
  rw [variableMetricC2CartanFirstJet_smooth period hPeriod reference variationTensor metric
    hMetric, ← variableMetricC2DeDonderComponentExpression_eq_firstJet]
  rw [regularFrameGhostFromCoefficients_reconstructs]
  have h := variableMetricC2DeDonderComponentExpression_smooth period hPeriod reference
    variationTensor metric hMetric hVariation
    (smoothMetricCartanAction period hPeriod ghost.field metric.tensor) component
  exact h

theorem variableMetricC2DiffeomorphismFPComponentExpression_smooth_apply
    (point : EffectiveQuotient period hPeriod) (component : Fin 4) :
    variableMetricC2DiffeomorphismFPComponentExpression period hPeriod reference
        (regularGeneralMetricSmoothC2Variation period hPeriod reference variationTensor)
        (smoothDiffeomorphismGhostC2Coefficients period hPeriod reference ghost) component point =
      globalGeneralMetricDiffeomorphismFaddeevPopovLinearMap period hPeriod metric ghost point
        (reference.frame component point) :=
  congrArg (fun field : C(EffectiveQuotient period hPeriod, Real) => field point)
    (variableMetricC2DiffeomorphismFPComponentExpression_smooth period hPeriod reference
      variationTensor metric hMetric hVariation ghost component)

theorem variableMetricC2DiffeomorphismFPComponentL2_smooth
    (component : Fin 4) :
    variableMetricC2DiffeomorphismFPComponentL2 period hPeriod reference
        (regularGeneralMetricSmoothC2Variation period hPeriod reference variationTensor)
        (smoothDiffeomorphismGhostC2Coefficients period hPeriod reference ghost) component =
      smoothToCanonicalPhysicalBulkL2 period hPeriod
        (globalCovectorVectorPairingField period hPeriod
          (globalGeneralMetricDiffeomorphismFaddeevPopovLinearMap period hPeriod metric ghost)
          (reference.frame component)) := by
  unfold variableMetricC2DiffeomorphismFPComponentL2
  rw [variableMetricC2DiffeomorphismFPComponentExpression_smooth period hPeriod reference
    variationTensor metric hMetric hVariation ghost component,
    continuousToCanonicalPhysicalBulkL2_agrees_on_smooth]

end
end P0EFTJanusVariableMetricC2DiffeomorphismFPSmoothAgreement4D
end JanusFormal
