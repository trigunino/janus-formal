import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RegularFrameSecondJetAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RegularTensorCovectorL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RegularTensorL2Bridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRegularFrameCanonicalFormalAdjoint4D

/-! Explicit actual L2 covectors for all smooth metric coefficient jets through order two. -/
namespace JanusFormal.P0EFTJanusProgramPT12TensorSecondJetL24D
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 600000
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff ENNReal
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusL2PTFunctionalSpace4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceStokes4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceWeakStokes4D
open P0EFTJanusMappingTorusCanonicalTenFlowDivergenceLeibniz4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
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

open scoped BigOperators
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D
open P0EFTJanusMappingTorusMetricCartanGlobalAction4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusRegularFrameSymmetricTensorDivergence4D
open P0EFTJanusRegularFrameMetricCartanCoefficients4D
open P0EFTJanusProgramPT12CanonicalFrameDerivativeAdjoint4D
open P0EFTJanusProgramPT12CanonicalFirstOrderColumn4D

open P0EFTJanusProgramPT12SmoothMatrixL24D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open Set

open P0EFTJanusProgramPT12FrameTensorL2Transport4D

open P0EFTJanusProgramPT12FrameTensorL2Equiv4D
open P0EFTJanusProgramPT12RegularFrameCartanClosed4D
open P0EFTJanusProgramPT12PairedRegularFrameCartan4D
open P0EFTJanusProgramPT12PairedRegularFrameCartanCore4D
open P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphCore4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusD9D10ExactFieldContentBridge4D

variable (reference : RegularGeneralLorentzMetric period hPeriod)

open scoped InnerProductSpace
open P0EFTJanusRegularFrameCanonicalFormalAdjoint4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusProgramPT12RegularTensorL2Bridge4D

open P0EFTJanusProgramPT12RegularTensorCovectorL24D
open P0EFTJanusProgramPT12RegularFrameSecondJetAdjoint4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D

theorem regularTensorCovectorActualL2_coefficient_pairing
    (coefficients : Fin 4 → Fin 4 → SmoothScalarField period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    inner Real (regularTensorCovectorActualL2 period hPeriod reference coefficients)
      (globalGeneralMetricTensorFrameL2LinearMap period hPeriod tensor) =
    ∑ row : Fin 4, ∑ column : Fin 4, canonicalSmoothScalarIntegral period hPeriod
      (smoothScalarFieldMul period hPeriod (coefficients row column)
        (generalMetricFrameCoefficient period hPeriod
          (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference) tensor row column)) := by
  rw [regularTensorCovectorActualL2_pairing]
  calc
    _ = canonicalSmoothScalarIntegral period hPeriod
        (∑ row : Fin 4, ∑ column : Fin 4, smoothScalarFieldMul period hPeriod (coefficients row column)
          (generalMetricFrameCoefficient period hPeriod
            (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference) tensor row column)) := by
      apply integral_congr_ae
      filter_upwards [] with point
      rw [regularFrameCovariantCoefficientTensor_pairing]
      simp only [smoothScalarFieldFinsetSum_apply, smoothScalarFieldMul_apply]
      rfl
    _ = _ := by simp only [map_sum]

variable (value : Fin 4 → Fin 4 → SmoothScalarField period hPeriod)
  (first : Fin 4 → Fin 4 → Fin 4 → SmoothScalarField period hPeriod)
  (second : Fin 4 → Fin 4 → Fin 4 → Fin 4 → SmoothScalarField period hPeriod)

/-- A finite metric jet expression with arbitrary smooth coefficient fields. -/
def tensorSecondJetFunctional (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) : Real :=
  ∑ row : Fin 4, ∑ column : Fin 4, canonicalSmoothScalarIntegral period hPeriod
    (regularFrameSecondJetDensity period hPeriod reference (value row column)
      (fun direction => first direction row column) (fun outer inner => second outer inner row column)
      (generalMetricFrameCoefficient period hPeriod
        (regularGeneralLorentzMetricSmoothD8Frame period hPeriod reference) tensor row column))

/-- All derivatives of the variable tensor have been moved to smooth coefficients. -/
def tensorSecondJetL2 : GlobalGeneralMetricTensorFrameL2 period hPeriod :=
  regularTensorCovectorActualL2 period hPeriod reference fun row column =>
    regularFrameSecondJetAdjoint period hPeriod reference (value row column)
      (fun direction => first direction row column) (fun outer inner => second outer inner row column)

theorem tensorSecondJetL2_pairing (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    inner Real (tensorSecondJetL2 period hPeriod reference value first second)
      (globalGeneralMetricTensorFrameL2LinearMap period hPeriod tensor) =
    tensorSecondJetFunctional period hPeriod reference value first second tensor := by
  rw [tensorSecondJetL2, regularTensorCovectorActualL2_coefficient_pairing]
  simp only [tensorSecondJetFunctional, regularFrameSecondJetAdjoint_integral]

def tensorSecondJetCovector : GlobalGeneralMetricTensorFrameL2 period hPeriod →L[Real] Real :=
  innerSL Real (tensorSecondJetL2 period hPeriod reference value first second)

theorem tensorSecondJetCovector_smooth (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    tensorSecondJetCovector period hPeriod reference value first second
      (globalGeneralMetricTensorFrameL2LinearMap period hPeriod tensor) =
    tensorSecondJetFunctional period hPeriod reference value first second tensor :=
  tensorSecondJetL2_pairing period hPeriod reference value first second tensor

theorem tensorSecondJetFunctional_bound (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    ‖tensorSecondJetFunctional period hPeriod reference value first second tensor‖ ≤
    ‖tensorSecondJetL2 period hPeriod reference value first second‖ *
      ‖globalGeneralMetricTensorFrameL2LinearMap period hPeriod tensor‖ := by
  rw [← tensorSecondJetL2_pairing]
  exact norm_inner_le_norm _ _

end
end JanusFormal.P0EFTJanusProgramPT12TensorSecondJetL24D
