import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFixedVolumeMaxwellStressResidual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRegularFrameMetricTensorTrace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12RegularTensorL2Bridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRegularFrameCanonicalFormalAdjoint4D

/-! Exact regular-frame coefficients for the Maxwell stress and volume correction. -/
namespace JanusFormal.P0EFTJanusProgramPT12MaxwellStressCoefficients4D
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

variable (potential : SmoothAbelianGaugePotential period hPeriod)

/-- Two inverse metric factors raise the covariant Maxwell stress coefficients. -/
def maxwellStressRaisedCoefficient (first second : Fin 4) : SmoothScalarField period hPeriod :=
  ∑ i : Fin 4, ∑ j : Fin 4, smoothScalarFieldMul period hPeriod
    (regularFrameMaxwellStressCoefficient period hPeriod reference potential i j)
    (smoothScalarFieldMul period hPeriod
      (regularFrameMetricInverseMatrix period hPeriod reference i first)
      (regularFrameMetricInverseMatrix period hPeriod reference j second))

theorem maxwellStressRaisedCoefficient_apply (first second : Fin 4)
    (point : EffectiveQuotient period hPeriod) :
    maxwellStressRaisedCoefficient period hPeriod reference potential first second point =
      ∑ i : Fin 4, ∑ j : Fin 4,
        regularFrameMaxwellStressCoefficient period hPeriod reference potential i j point *
          (regularFrameMetricInverseMatrix period hPeriod reference i first point *
            regularFrameMetricInverseMatrix period hPeriod reference j second point) := by
  let evaluation : SmoothScalarField period hPeriod →+ Real :=
    { toFun := fun field => field point, map_zero' := rfl, map_add' := by intros; rfl }
  change evaluation (∑ i : Fin 4, ∑ j : Fin 4, smoothScalarFieldMul period hPeriod
    (regularFrameMaxwellStressCoefficient period hPeriod reference potential i j)
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

theorem maxwellStress_pairing_eq_raisedCoefficients
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalMetricTensorPairingAt period hPeriod reference.metric
      (regularGeneralMetricMaxwellStressTensor period hPeriod reference potential) tensor point =
      ∑ first : Fin 4, ∑ second : Fin 4,
        maxwellStressRaisedCoefficient period hPeriod reference potential first second point *
          tensor.tensor point (reference.frame first point) (reference.frame second point) := by
  rw [regularGeneralMetricMaxwellStressTensor_pairing_eq_dualFrameSum]
  simp_rw [tensor_dualFrame_expansion, maxwellStressRaisedCoefficient_apply,
    Finset.mul_sum, Finset.sum_mul]
  simpa only [Fintype.sum_prod_type, mul_assoc] using
    (Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun (p : Fin 4 × Fin 4) (q : Fin 4 × Fin 4) =>
        regularFrameMaxwellStressCoefficient period hPeriod reference potential p.1 p.2 point *
          (regularFrameMetricInverseMatrix period hPeriod reference p.1 q.1 point *
            regularFrameMetricInverseMatrix period hPeriod reference p.2 q.2 point) *
          tensor.tensor point (reference.frame q.1 point) (reference.frame q.2 point)))

theorem metric_pairing_eq_inverseCoefficients
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalMetricTensorPairingAt period hPeriod reference.metric reference.metric.tensor tensor point =
      ∑ first : Fin 4, ∑ second : Fin 4,
        regularFrameMetricInverseMatrix period hPeriod reference first second point *
          tensor.tensor point (reference.frame first point) (reference.frame second point) := by
  rw [generalMetricTensorPairingAt_symmetric, ← generalMetricTensorTraceAt_eq_pairing_metric,
    generalMetricTensorTraceAt_eq_regularFrameContraction period hPeriod reference]
  rfl

/-- Includes the positive fixed-volume correction with its exact coefficient. -/
def fixedVolumeMaxwellCoefficient (first second : Fin 4) : SmoothScalarField period hPeriod :=
  (1 / 2 : Real) • smoothScalarFieldMul period hPeriod reference.volume
    (maxwellStressRaisedCoefficient period hPeriod reference potential first second) +
  (1 / 8 : Real) • smoothScalarFieldMul period hPeriod
    (smoothScalarFieldMul period hPeriod reference.volume
      (globalSmoothMaxwellPairing period hPeriod reference.metric potential potential))
    (regularFrameMetricInverseMatrix period hPeriod reference first second)

theorem fixedVolumeMaxwellCoefficient_pairing
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalMetricTensorPairingAt period hPeriod reference.metric
      (regularFrameCovariantCoefficientTensor period hPeriod reference
        (fixedVolumeMaxwellCoefficient period hPeriod reference potential)) tensor point =
    generalMetricTensorPairingAt period hPeriod reference.metric
      (regularFrameFixedVolumeMaxwellStressResidual period hPeriod reference potential) tensor point := by
  rw [regularFrameCovariantCoefficientTensor_pairing,
    regularFrameFixedVolumeMaxwellStressResidual_pairing,
    maxwellStress_pairing_eq_raisedCoefficients, metric_pairing_eq_inverseCoefficients]
  simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  change ((1 / 2 : Real) * (reference.volume point * _) + (1 / 8 : Real) *
    (reference.volume point * globalMaxwellPairing period hPeriod reference.metric potential potential point * _)) * _ = _
  ring

end
end JanusFormal.P0EFTJanusProgramPT12MaxwellStressCoefficients4D
