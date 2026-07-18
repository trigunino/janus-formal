import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralLorentzMetricBVPTCovariance4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicLorentzMetricPTFixed4D

/-!
# Pointwise ultralocal BV master Hamiltonian for general Lorentz metrics

This gate constructs the bulk pointwise Hamiltonian
`1/2 ⟨h⁺, h⁺⟩` from the two genuine background Lorentz metrics.  Its exact
affine variation, generated contractible BRST doublet, pointwise CME and
PT/exchange covariance are explicit.  No spacetime integration or
derivative-dependent master equation is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGeneralLorentzMetricBVUltralocalMaster4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusPTInvolution
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricPTScalarAction4D
open P0EFTJanusMappingTorusD8NonabelianGhostFinitePositiveMetricBVMaster4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVPTCovariance4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusIntrinsicLorentzMetricPTFixed4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveTangentFiniteDimensional
    (point : EffectiveQuotient period hPeriod) :
    FiniteDimensional Real
      (GeneralMetricTangentFiber period hPeriod point) := by
  change FiniteDimensional Real CoverCoordinates
  infer_instance

/-! ## Affine tensor operations -/

def smoothGeneralMetricTensorPairAdd
    (first second : SmoothGeneralMetricTensorPair period hPeriod) :
    SmoothGeneralMetricTensorPair period hPeriod :=
  (smoothSymmetricTensorAdd period hPeriod first.1 second.1,
    smoothSymmetricTensorAdd period hPeriod first.2 second.2)

def smoothGeneralMetricTensorPairSMul
    (scalar : Real)
    (tensor : SmoothGeneralMetricTensorPair period hPeriod) :
    SmoothGeneralMetricTensorPair period hPeriod :=
  (smoothSymmetricTensorSMul period hPeriod scalar tensor.1,
    smoothSymmetricTensorSMul period hPeriod scalar tensor.2)

def smoothGeneralMetricTensorPairAffineLine
    (base variation : SmoothGeneralMetricTensorPair period hPeriod)
    (parameter : Real) : SmoothGeneralMetricTensorPair period hPeriod :=
  smoothGeneralMetricTensorPairAdd period hPeriod base
    (smoothGeneralMetricTensorPairSMul period hPeriod parameter variation)

/-- The genuine affine line in both entries of the linear BV phase space. -/
def smoothGeneralMetricBVAffineLine
    (base variation : SmoothGeneralMetricBVField period hPeriod)
    (parameter : Real) : SmoothGeneralMetricBVField period hPeriod :=
  (smoothGeneralMetricTensorPairAffineLine period hPeriod
      base.1 variation.1 parameter,
    smoothGeneralMetricTensorPairAffineLine period hPeriod
      base.2 variation.2 parameter)

/-! ## Bilinearity of the background-raised pairing -/

theorem raisedGeneralMetricTensorAt_add
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    raisedGeneralMetricTensorAt period hPeriod metric
        (smoothSymmetricTensorAdd period hPeriod first second) point =
      raisedGeneralMetricTensorAt period hPeriod metric first point +
        raisedGeneralMetricTensorAt period hPeriod metric second point := by
  apply ContinuousLinearMap.ext
  intro vector
  simp [raisedGeneralMetricTensorAt, smoothSymmetricTensorAdd]

theorem raisedGeneralMetricTensorAt_smul
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (scalar : Real)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    raisedGeneralMetricTensorAt period hPeriod metric
        (smoothSymmetricTensorSMul period hPeriod scalar tensor) point =
      scalar • raisedGeneralMetricTensorAt period hPeriod metric tensor point := by
  apply ContinuousLinearMap.ext
  intro vector
  simp [raisedGeneralMetricTensorAt, smoothSymmetricTensorSMul]

theorem generalMetricTensorPairingAt_add_left
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second third : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalMetricTensorPairingAt period hPeriod metric
        (smoothSymmetricTensorAdd period hPeriod first second) third point =
      generalMetricTensorPairingAt period hPeriod metric first third point +
        generalMetricTensorPairingAt period hPeriod metric second third point := by
  unfold generalMetricTensorPairingAt
  rw [raisedGeneralMetricTensorAt_add]
  simp [add_mul]

theorem generalMetricTensorPairingAt_add_right
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second third : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalMetricTensorPairingAt period hPeriod metric first
        (smoothSymmetricTensorAdd period hPeriod second third) point =
      generalMetricTensorPairingAt period hPeriod metric first second point +
        generalMetricTensorPairingAt period hPeriod metric first third point := by
  rw [generalMetricTensorPairingAt_symmetric period hPeriod metric first,
    generalMetricTensorPairingAt_add_left,
    generalMetricTensorPairingAt_symmetric period hPeriod metric second,
    generalMetricTensorPairingAt_symmetric period hPeriod metric third]

theorem generalMetricTensorPairingAt_smul_left
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (scalar : Real)
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalMetricTensorPairingAt period hPeriod metric
        (smoothSymmetricTensorSMul period hPeriod scalar first) second point =
      scalar * generalMetricTensorPairingAt period hPeriod metric first second point := by
  unfold generalMetricTensorPairingAt
  rw [raisedGeneralMetricTensorAt_smul]
  simp

theorem generalMetricTensorPairingAt_smul_right
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (scalar : Real)
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalMetricTensorPairingAt period hPeriod metric first
        (smoothSymmetricTensorSMul period hPeriod scalar second) point =
      scalar * generalMetricTensorPairingAt period hPeriod metric first second point := by
  rw [generalMetricTensorPairingAt_symmetric period hPeriod metric first,
    generalMetricTensorPairingAt_smul_left,
    generalMetricTensorPairingAt_symmetric period hPeriod metric second]

theorem generalMetricTensorPairPairingAt_add_left
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (first second third : SmoothGeneralMetricTensorPair period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalMetricTensorPairPairingAt period hPeriod metrics
        (smoothGeneralMetricTensorPairAdd period hPeriod first second) third point =
      generalMetricTensorPairPairingAt period hPeriod metrics first third point +
        generalMetricTensorPairPairingAt period hPeriod metrics second third point := by
  unfold generalMetricTensorPairPairingAt smoothGeneralMetricTensorPairAdd
  rw [generalMetricTensorPairingAt_add_left,
    generalMetricTensorPairingAt_add_left]
  ring

theorem generalMetricTensorPairPairingAt_add_right
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (first second third : SmoothGeneralMetricTensorPair period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalMetricTensorPairPairingAt period hPeriod metrics first
        (smoothGeneralMetricTensorPairAdd period hPeriod second third) point =
      generalMetricTensorPairPairingAt period hPeriod metrics first second point +
        generalMetricTensorPairPairingAt period hPeriod metrics first third point := by
  rw [generalMetricTensorPairPairingAt_symmetric period hPeriod metrics first,
    generalMetricTensorPairPairingAt_add_left,
    generalMetricTensorPairPairingAt_symmetric period hPeriod metrics second,
    generalMetricTensorPairPairingAt_symmetric period hPeriod metrics third]

theorem generalMetricTensorPairPairingAt_smul_left
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (scalar : Real)
    (first second : SmoothGeneralMetricTensorPair period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalMetricTensorPairPairingAt period hPeriod metrics
        (smoothGeneralMetricTensorPairSMul period hPeriod scalar first) second point =
      scalar * generalMetricTensorPairPairingAt period hPeriod metrics first second point := by
  unfold generalMetricTensorPairPairingAt smoothGeneralMetricTensorPairSMul
  rw [generalMetricTensorPairingAt_smul_left,
    generalMetricTensorPairingAt_smul_left]
  ring

theorem generalMetricTensorPairPairingAt_smul_right
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (scalar : Real)
    (first second : SmoothGeneralMetricTensorPair period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalMetricTensorPairPairingAt period hPeriod metrics first
        (smoothGeneralMetricTensorPairSMul period hPeriod scalar second) point =
      scalar * generalMetricTensorPairPairingAt period hPeriod metrics first second point := by
  rw [generalMetricTensorPairPairingAt_symmetric period hPeriod metrics first,
    generalMetricTensorPairPairingAt_smul_left,
    generalMetricTensorPairPairingAt_symmetric period hPeriod metrics second]

@[simp]
theorem generalMetricTensorPairPairingAt_zero_left
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (second : SmoothGeneralMetricTensorPair period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalMetricTensorPairPairingAt period hPeriod metrics
        (smoothGeneralMetricTensorPairZero period hPeriod) second point = 0 := by
  simp [generalMetricTensorPairPairingAt,
    smoothGeneralMetricTensorPairZero,
    generalMetricTensorPairingAt, raisedGeneralMetricTensorAt,
    zeroSymmetricTensor]

/-! ## Ultralocal master Hamiltonian -/

/-- Bulk pointwise Hamiltonian `1/2 ⟨h⁺,h⁺⟩`, with each sector paired by
its actual background Lorentz metric. -/
def generalLorentzMetricBVUltralocalMasterActionAt
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (phase : SmoothGeneralMetricBVField period hPeriod)
    (point : EffectiveQuotient period hPeriod) : Real :=
  (1 / 2 : Real) *
    generalMetricTensorPairPairingAt period hPeriod metrics
      phase.2 phase.2 point

def generalLorentzMetricBVUltralocalMasterObservable
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod) :
    GeneralMetricBVPointObservable period hPeriod where
  parity := .even
  value := generalLorentzMetricBVUltralocalMasterActionAt period hPeriod metrics
  fieldGradient := fun _ =>
    smoothGeneralMetricTensorPairZero period hPeriod
  antifieldGradient := fun phase => phase.2

theorem generalLorentzMetricBVUltralocalMasterActionAt_affine_expansion
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (phase variation : SmoothGeneralMetricBVField period hPeriod)
    (point : EffectiveQuotient period hPeriod) (parameter : Real) :
    generalLorentzMetricBVUltralocalMasterActionAt period hPeriod metrics
        (smoothGeneralMetricBVAffineLine period hPeriod phase variation parameter)
        point =
      generalLorentzMetricBVUltralocalMasterActionAt
          period hPeriod metrics phase point +
        parameter * generalMetricTensorPairPairingAt period hPeriod metrics
          phase.2 variation.2 point +
        parameter ^ 2 / 2 *
          generalMetricTensorPairPairingAt period hPeriod metrics
            variation.2 variation.2 point := by
  unfold generalLorentzMetricBVUltralocalMasterActionAt
    smoothGeneralMetricBVAffineLine
    smoothGeneralMetricTensorPairAffineLine
  rw [generalMetricTensorPairPairingAt_add_left,
    generalMetricTensorPairPairingAt_add_right,
    generalMetricTensorPairPairingAt_add_right,
    generalMetricTensorPairPairingAt_smul_right,
    generalMetricTensorPairPairingAt_smul_left,
    generalMetricTensorPairPairingAt_smul_left,
    generalMetricTensorPairPairingAt_smul_right,
    generalMetricTensorPairPairingAt_symmetric period hPeriod metrics
      variation.2 phase.2]
  ring

/-- The declared antifield gradient is the actual directional derivative
along every affine line in the full linear BV phase space. -/
theorem generalLorentzMetricBVUltralocalMasterActionAt_hasDerivAt
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (phase variation : SmoothGeneralMetricBVField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    HasDerivAt
      (fun parameter : Real =>
        generalLorentzMetricBVUltralocalMasterActionAt period hPeriod metrics
          (smoothGeneralMetricBVAffineLine
            period hPeriod phase variation parameter) point)
      (generalMetricTensorPairPairingAt period hPeriod metrics
        ((generalLorentzMetricBVUltralocalMasterObservable
          period hPeriod metrics).antifieldGradient phase)
        variation.2 point)
      0 := by
  let firstVariation :=
    generalMetricTensorPairPairingAt period hPeriod metrics
      phase.2 variation.2 point
  let quadraticRemainder :=
    generalMetricTensorPairPairingAt period hPeriod metrics
      variation.2 variation.2 point
  have hLinear : HasDerivAt
      (fun parameter : Real => parameter * firstVariation) firstVariation 0 := by
    simpa using
      (hasDerivAt_id (x := (0 : Real))).mul_const firstVariation
  have hQuadratic : HasDerivAt
      (fun parameter : Real => parameter ^ 2 / 2 * quadraticRemainder) 0 0 := by
    simpa [id] using
      (((hasDerivAt_id (x := (0 : Real))).pow 2).div_const 2).mul_const
        quadraticRemainder
  have hPolynomial : HasDerivAt
      (fun parameter : Real =>
        generalLorentzMetricBVUltralocalMasterActionAt
            period hPeriod metrics phase point +
          parameter * firstVariation +
          parameter ^ 2 / 2 * quadraticRemainder)
      firstVariation 0 := by
    have hRaw :=
      (hLinear.const_add
        (generalLorentzMetricBVUltralocalMasterActionAt
          period hPeriod metrics phase point)).add hQuadratic
    refine (hRaw.congr_deriv (by simp)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall ?_)
    intro parameter
    rfl
  refine hPolynomial.congr_of_eventuallyEq
    (Filter.Eventually.of_forall ?_)
  intro parameter
  simpa [firstVariation, quadraticRemainder,
    generalLorentzMetricBVUltralocalMasterObservable] using
    (generalLorentzMetricBVUltralocalMasterActionAt_affine_expansion
      period hPeriod metrics phase variation point parameter)

/-- The Hamiltonian vector is the bulk contractible doublet `(h⁺,0)`. -/
theorem generalLorentzMetricBVUltralocalMaster_generates_BRST
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (phase : SmoothGeneralMetricBVField period hPeriod) :
    ((generalLorentzMetricBVUltralocalMasterObservable
        period hPeriod metrics).antifieldGradient phase,
      (generalLorentzMetricBVUltralocalMasterObservable
        period hPeriod metrics).fieldGradient phase) =
      smoothGeneralMetricBVBRST period hPeriod phase :=
  rfl

/-- Pointwise classical master equation of the ultralocal doublet. -/
theorem generalLorentzMetricBVUltralocalMaster_classical_master_equation
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (phase : SmoothGeneralMetricBVField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalMetricBVOddAntibracketAt period hPeriod metrics
        (generalLorentzMetricBVUltralocalMasterObservable period hPeriod metrics)
        (generalLorentzMetricBVUltralocalMasterObservable period hPeriod metrics)
        phase point = 0 := by
  simp [generalMetricBVOddAntibracketAt,
    generalLorentzMetricBVUltralocalMasterObservable,
    finiteBVOddKoszulSign]

/-! ## PT/exchange covariance -/

theorem generalLorentzMetricBVUltralocalMasterActionAt_ptExchange
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (phase : SmoothGeneralMetricBVField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalLorentzMetricBVUltralocalMasterActionAt period hPeriod
        (smoothGeneralLorentzMetricPTExchange period hPeriod metrics)
        (smoothGeneralMetricBVPTExchange period hPeriod phase) point =
      generalLorentzMetricBVUltralocalMasterActionAt period hPeriod metrics phase
        (reflectedSpherePT period hPeriod point) := by
  simp only [generalLorentzMetricBVUltralocalMasterActionAt,
    smoothGeneralMetricBVPTExchange]
  rw [generalMetricTensorPairPairingAt_ptExchange period hPeriod]

theorem generalLorentzMetricBVUltralocalMaster_BRST_ptExchange
    (phase : SmoothGeneralMetricBVField period hPeriod) :
    smoothGeneralMetricBVPTExchange period hPeriod
        (smoothGeneralMetricBVBRST period hPeriod phase) =
      smoothGeneralMetricBVBRST period hPeriod
        (smoothGeneralMetricBVPTExchange period hPeriod phase) :=
  smoothGeneralMetricBVPTExchange_commutes_BRST period hPeriod phase

/-- Covariance of the pointwise CME, obtained from the canonical BV
PT/exchange covariance theorem. -/
theorem generalLorentzMetricBVUltralocalMaster_classical_master_equation_ptExchange
    (metrics : SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod)
    (phase : SmoothGeneralMetricBVField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalMetricBVOddAntibracketAt period hPeriod
        (smoothGeneralLorentzMetricPTExchange period hPeriod metrics)
        (generalMetricBVPointObservablePTExchange period hPeriod
          (generalLorentzMetricBVUltralocalMasterObservable
            period hPeriod metrics))
        (generalMetricBVPointObservablePTExchange period hPeriod
          (generalLorentzMetricBVUltralocalMasterObservable
            period hPeriod metrics))
        (smoothGeneralMetricBVPTExchange period hPeriod phase) point = 0 := by
  rw [generalMetricBVOddAntibracketAt_ptExchange]
  exact generalLorentzMetricBVUltralocalMaster_classical_master_equation
    period hPeriod metrics phase (reflectedSpherePT period hPeriod point)

/-! ## Explicit nonzero intrinsic witness -/

@[simp]
theorem raisedGeneralMetricTensorAt_metric_tensor
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    raisedGeneralMetricTensorAt period hPeriod metric metric.tensor point =
      ContinuousLinearMap.id Real
        (GeneralMetricTangentFiber period hPeriod point) := by
  apply ContinuousLinearMap.ext
  intro vector
  change (metric.musical point).symm
      (metric.tensor.tensor point vector) = vector
  rw [← DFunLike.congr_fun (metric.musical_eq_tensor point) vector]
  exact (metric.musical point).symm_apply_apply vector

theorem generalMetricTensorPairingAt_metric_self
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalMetricTensorPairingAt period hPeriod metric
        metric.tensor metric.tensor point = 4 := by
  have hDimension :
      Module.finrank Real
        (GeneralMetricTangentFiber period hPeriod point) = 4 := by
    change Module.finrank Real CoverCoordinates = 4
    simp [CoverCoordinates]
  unfold generalMetricTensorPairingAt
  rw [raisedGeneralMetricTensorAt_metric_tensor]
  have hIdentityProduct :
      (ContinuousLinearMap.id Real
          (GeneralMetricTangentFiber period hPeriod point)).toLinearMap *
          (ContinuousLinearMap.id Real
            (GeneralMetricTangentFiber period hPeriod point)).toLinearMap =
        LinearMap.id := by
    ext vector
    rfl
  rw [hIdentityProduct, LinearMap.trace_id, hDimension]
  norm_num

def intrinsicGeneralLorentzMetricPair :
    SmoothGeneralLorentzMetric period hPeriod ×
      SmoothGeneralLorentzMetric period hPeriod :=
  (intrinsicSmoothGeneralLorentzMetric period hPeriod,
    intrinsicSmoothGeneralLorentzMetric period hPeriod)

def intrinsicGeneralMetricTensorPairWitness :
    SmoothGeneralMetricTensorPair period hPeriod :=
  ((intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor,
    (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor)

def intrinsicGeneralMetricBVPhaseWitness :
    SmoothGeneralMetricBVField period hPeriod :=
  (smoothGeneralMetricTensorPairZero period hPeriod,
    intrinsicGeneralMetricTensorPairWitness period hPeriod)

theorem intrinsicGeneralMetricBVUltralocalMasterActionAt_witness_eq_four
    (point : EffectiveQuotient period hPeriod) :
    generalLorentzMetricBVUltralocalMasterActionAt period hPeriod
        (intrinsicGeneralLorentzMetricPair period hPeriod)
        (intrinsicGeneralMetricBVPhaseWitness period hPeriod) point = 4 := by
  unfold generalLorentzMetricBVUltralocalMasterActionAt
    intrinsicGeneralLorentzMetricPair
    intrinsicGeneralMetricBVPhaseWitness
    intrinsicGeneralMetricTensorPairWitness
    generalMetricTensorPairPairingAt
  rw [generalMetricTensorPairingAt_metric_self]
  norm_num

theorem intrinsicGeneralMetricBVUltralocalMasterActionAt_witness_ne_zero
    (point : EffectiveQuotient period hPeriod) :
    generalLorentzMetricBVUltralocalMasterActionAt period hPeriod
        (intrinsicGeneralLorentzMetricPair period hPeriod)
        (intrinsicGeneralMetricBVPhaseWitness period hPeriod) point ≠ 0 := by
  rw [intrinsicGeneralMetricBVUltralocalMasterActionAt_witness_eq_four]
  norm_num

end

end P0EFTJanusMappingTorusGeneralLorentzMetricBVUltralocalMaster4D
end JanusFormal
