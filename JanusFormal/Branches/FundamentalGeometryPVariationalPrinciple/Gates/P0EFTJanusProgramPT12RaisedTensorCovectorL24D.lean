import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRegularFrameFixedVolumeRicciResidual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RegularTensorCovectorL24D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFixedVolumeMaxwellStressResidual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRegularFrameMetricTensorTrace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RegularTensorL2Bridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRegularFrameCanonicalFormalAdjoint4D

/-! Actual L2 representatives for arbitrary smooth coframe coefficient tensors. -/
namespace JanusFormal.P0EFTJanusProgramPT12RaisedTensorCovectorL24D
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

open P0EFTJanusMappingTorusGeneralLorentzMetricBVUltralocalMaster4D
open P0EFTJanusMappingTorusGeneralMetricSmoothTrace4D
open P0EFTJanusProgramPRegularFrameMetricInverse4D
open P0EFTJanusProgramPRegularGeneralMetricGlobalSmoothMaxwellStressTensor4D
open P0EFTJanusProgramPRegularGeneralMetricInvariantMaxwellStressVariation4D
open P0EFTJanusFixedVolumeMaxwellStressResidual4D
open P0EFTJanusRegularFrameMetricTensorTrace4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D
open P0EFTJanusMappingTorusConformalFrameFreeMaxwellHessian4D

open P0EFTJanusRegularFrameFixedVolumeRicciResidual4D
open P0EFTJanusProgramPT12RegularTensorCovectorL24D

variable (coefficients : Fin 4 → Fin 4 → SmoothScalarField period hPeriod)

/-- Two inverse metric factors raise the arbitrary covariant coefficients. -/
def raisedTensorCoefficient (first second : Fin 4) : SmoothScalarField period hPeriod :=
  ∑ i : Fin 4, ∑ j : Fin 4, smoothScalarFieldMul period hPeriod
    (coefficients i j)
    (smoothScalarFieldMul period hPeriod
      (regularFrameMetricInverseMatrix period hPeriod reference i first)
      (regularFrameMetricInverseMatrix period hPeriod reference j second))

theorem raisedTensorCoefficient_apply (first second : Fin 4)
    (point : EffectiveQuotient period hPeriod) :
    raisedTensorCoefficient period hPeriod reference coefficients first second point =
      ∑ i : Fin 4, ∑ j : Fin 4,
        coefficients i j point *
          (regularFrameMetricInverseMatrix period hPeriod reference i first point *
            regularFrameMetricInverseMatrix period hPeriod reference j second point) := by
  let evaluation : SmoothScalarField period hPeriod →+ Real :=
    { toFun := fun field => field point, map_zero' := rfl, map_add' := by intros; rfl }
  change evaluation (∑ i : Fin 4, ∑ j : Fin 4, smoothScalarFieldMul period hPeriod
    (coefficients i j)
    (smoothScalarFieldMul period hPeriod
      (regularFrameMetricInverseMatrix period hPeriod reference i first)
      (regularFrameMetricInverseMatrix period hPeriod reference j second))) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_sum]
  rfl

private theorem tensor_dualFrame_expansion
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) (i j : Fin 4) :
    tensor.tensor point (regularFrameDualVectorAt period hPeriod reference point i)
      (regularFrameDualVectorAt period hPeriod reference point j) =
      ∑ first : Fin 4, ∑ second : Fin 4,
        (regularFrameMetricInverseMatrix period hPeriod reference i first point *
          regularFrameMetricInverseMatrix period hPeriod reference j second point) *
        tensor.tensor point (reference.frame first point) (reference.frame second point) := by
  rw [regularFrameDualVectorAt_eq_sum, map_sum, sum_apply]
  apply Finset.sum_congr rfl
  intro first _
  rw [map_smul]
  simp only [smul_apply, smul_eq_mul]
  rw [regularFrameDualVectorAt_eq_sum, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro second _
  rw [map_smul]
  simp only [smul_eq_mul]
  exact (mul_assoc _ _ _).symm

theorem coefficientTensor_pairing_eq_raisedCoefficients
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalMetricTensorPairingAt period hPeriod reference.metric
      (regularFrameSmoothCoefficientTensor period hPeriod reference coefficients) tensor point =
      ∑ first : Fin 4, ∑ second : Fin 4,
        raisedTensorCoefficient period hPeriod reference coefficients first second point *
          tensor.tensor point (reference.frame first point) (reference.frame second point) := by
  rw [regularFrameSmoothCoefficientTensor_pairing]
  simp_rw [tensor_dualFrame_expansion, raisedTensorCoefficient_apply,
    Finset.mul_sum, Finset.sum_mul]
  simpa only [Fintype.sum_prod_type, mul_assoc] using
    (Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun (p : Fin 4 × Fin 4) (q : Fin 4 × Fin 4) =>
        coefficients p.1 p.2 point *
          (regularFrameMetricInverseMatrix period hPeriod reference p.1 q.1 point *
            regularFrameMetricInverseMatrix period hPeriod reference p.2 q.2 point) *
          tensor.tensor point (reference.frame q.1 point) (reference.frame q.2 point)))

/-- Representation in the original physical tensor L2 coordinates. -/
def raisedTensorCovectorActualL2 : GlobalGeneralMetricTensorFrameL2 period hPeriod :=
  regularTensorCovectorActualL2 period hPeriod reference
    (raisedTensorCoefficient period hPeriod reference coefficients)

theorem raisedTensorCovectorActualL2_pairing
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    inner Real (raisedTensorCovectorActualL2 period hPeriod reference coefficients)
      (globalGeneralMetricTensorFrameL2LinearMap period hPeriod tensor) =
    ∫ point, generalMetricTensorPairingAt period hPeriod reference.metric
      (regularFrameSmoothCoefficientTensor period hPeriod reference coefficients) tensor point
      ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  rw [raisedTensorCovectorActualL2, regularTensorCovectorActualL2_pairing]
  apply integral_congr_ae
  filter_upwards [] with point
  rw [regularFrameCovariantCoefficientTensor_pairing,
    coefficientTensor_pairing_eq_raisedCoefficients]

theorem raisedTensorCovectorActualL2_bound
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    ‖∫ point, generalMetricTensorPairingAt period hPeriod reference.metric
      (regularFrameSmoothCoefficientTensor period hPeriod reference coefficients) tensor point
      ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod‖ ≤
    ‖raisedTensorCovectorActualL2 period hPeriod reference coefficients‖ *
      ‖globalGeneralMetricTensorFrameL2LinearMap period hPeriod tensor‖ := by
  rw [← raisedTensorCovectorActualL2_pairing]
  exact norm_inner_le_norm _ _

end
end JanusFormal.P0EFTJanusProgramPT12RaisedTensorCovectorL24D
