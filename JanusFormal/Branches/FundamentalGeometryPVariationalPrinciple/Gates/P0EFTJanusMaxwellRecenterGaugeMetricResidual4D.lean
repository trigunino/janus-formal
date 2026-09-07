import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusSmoothMaxwellRecenterGaugeVelocity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMetricInducedMaxwellResidual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartVariationTransport4D

/-! # Metric residual of the actual Maxwell recentering gauge velocity

Covariant test components are taken in the original regular frame.  Their
linear covector is represented using the reconstructed metric's dual frame
products.  The canonical current already includes its density normalization.
-/
namespace JanusFormal
namespace P0EFTJanusMaxwellRecenterGaugeMetricResidual4D
set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 600000
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVUltralocalMaster4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0LocalRootBranch4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPRegularFrameGaugePotentialReconstruction4D
open P0EFTJanusProgramPRegularFrameMetricInverse4D
open P0EFTJanusProgramPRegularFrameMaxwellSmoothGaugeTestSeparation4D
open P0EFTJanusProgramPRegularFrameCanonicalMaxwellVariationalResidual4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartRegularMetric4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartVariationTransport4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootLift4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootSmoothInverse4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellDensityPointwise4D
open P0EFTJanusProgramPRegularGeneralMetricC2MaxwellStressDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2GaugeCoefficientFrameTransport4D
open P0EFTJanusMetricInducedSmoothGaugeVelocity4D
open P0EFTJanusSmoothIdentityRootVelocity4D
open P0EFTJanusSmoothMaxwellRecenterGaugeVelocity4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev Matrix4 := Matrix (Fin 4) (Fin 4) Real
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance : BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance
local instance : NormedRing Matrix4 := Matrix.frobeniusNormedRing
local instance : NormedAlgebra Real Matrix4 := Matrix.frobeniusNormedAlgebra
@[reducible] local instance canonicalMatrixNormedAddCommGroup : NormedAddCommGroup Matrix4 :=
  NonUnitalNormedRing.toNormedAddCommGroup
local instance : AddCommGroup Matrix4 := canonicalMatrixNormedAddCommGroup.toAddCommGroup
local instance canonicalMatrixPseudoMetricSpace : PseudoMetricSpace Matrix4 :=
  canonicalMatrixNormedAddCommGroup.toPseudoMetricSpace
local instance canonicalMatrixUniformSpace : UniformSpace Matrix4 :=
  canonicalMatrixPseudoMetricSpace.toUniformSpace
local instance : TopologicalSpace Matrix4 := canonicalMatrixUniformSpace.toTopologicalSpace
@[reducible] local instance canonicalMatrixNormedSpace : NormedSpace Real Matrix4 :=
  NormedAlgebra.toNormedSpace Matrix4
local instance : Module Real Matrix4 := canonicalMatrixNormedSpace.toModule
local instance : CompleteSpace Matrix4 := FiniteDimensional.complete Real Matrix4

private def matrixEntryCLM (row column : Fin 4) : Matrix4 →L[Real] Real :=
  LinearMap.toContinuousLinearMap
    { toFun := fun matrix => matrix row column
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

private theorem matrixProduct_contMDiff
    {first second : EffectiveQuotient period hPeriod → Matrix4}
    (hFirst : ContMDiff coverModelWithCorners (modelWithCornersSelf Real Matrix4) ∞ first)
    (hSecond : ContMDiff coverModelWithCorners (modelWithCornersSelf Real Matrix4) ∞ second) :
    ContMDiff coverModelWithCorners (modelWithCornersSelf Real Matrix4) ∞
      (fun point => first point * second point) :=
  ((ContinuousLinearMap.mul Real Matrix4).contMDiff.comp hFirst).clm_apply hSecond

variable (metric : RegularGeneralLorentzMetric period hPeriod)
  (shift : SmoothSymmetricCovariantTwoTensor period hPeriod)

/-- The complete matrix velocity acting on covariant tests in the original frame. -/
def maxwellRecenterGaugeMatrixVelocity (point : EffectiveQuotient period hPeriod) :
    Matrix4 →L[Real] Matrix4 :=
  let product := ContinuousLinearMap.mul Real Matrix4
  let inverse := regularGeneralMetricC2IdentityRootInverseMatrixAt period hPeriod metric shift point
  let raise := product (regularFrameMetricInverseMatrixMap period hPeriod metric point)
  (product.flip inverse).comp
      ((regularGeneralMetricIdentityRootSylvesterInverse period hPeriod metric shift point).comp raise) -
    (1 / 2 : Real) • (product inverse).comp ((product.flip inverse).comp raise)

theorem maxwellRecenterGaugeMatrixVelocity_apply
    (point : EffectiveQuotient period hPeriod) (matrix : Matrix4) :
    maxwellRecenterGaugeMatrixVelocity period hPeriod metric shift point matrix =
      regularGeneralMetricIdentityRootSylvesterInverse period hPeriod metric shift point
          (regularFrameMetricInverseMatrixMap period hPeriod metric point * matrix) *
        regularGeneralMetricC2IdentityRootInverseMatrixAt period hPeriod metric shift point -
      (1 / 2 : Real) •
        (regularGeneralMetricC2IdentityRootInverseMatrixAt period hPeriod metric shift point *
          ((regularFrameMetricInverseMatrixMap period hPeriod metric point * matrix) *
            regularGeneralMetricC2IdentityRootInverseMatrixAt period hPeriod metric shift point)) := rfl

variable (hShift : regularGeneralMetricSmoothC2Variation period hPeriod metric shift ∈
  regularGeneralMetricC2LorentzChartDomain period hPeriod metric)

include hShift in
theorem maxwellRecenterGaugeMatrixVelocity_contMDiff (matrix : Matrix4) :
    ContMDiff coverModelWithCorners (modelWithCornersSelf Real Matrix4) ∞
      (fun point => maxwellRecenterGaugeMatrixVelocity period hPeriod metric shift point matrix) := by
  have hRaise := matrixProduct_contMDiff period hPeriod
    (regularFrameMetricInverseMatrixMap_contMDiff period hPeriod metric)
    (contMDiff_const (c := matrix))
  have hInverse := regularGeneralMetricC2IdentityRootInverseMatrixAt_contMDiff
    period hPeriod metric shift hShift
  have hSylvester := regularGeneralMetricIdentityRootSylvesterInverse_contMDiff
    period hPeriod metric shift
      (regularGeneralMetricC2LorentzChartDomain_matrix_mem_root period hPeriod metric hShift).1
  exact (matrixProduct_contMDiff period hPeriod (hSylvester.clm_apply hRaise) hInverse).sub
    (((1 / 2 : Real) • ContinuousLinearMap.id Real Matrix4).contMDiff.comp
      (matrixProduct_contMDiff period hPeriod hInverse
        (matrixProduct_contMDiff period hPeriod hRaise hInverse)))

variable (coefficients : SmoothQuotientField period hPeriod GaugeFiber)

private def recenteredPotential : SmoothAbelianGaugePotential period hPeriod :=
  regularFrameGaugePotentialFromCoefficients period hPeriod
    (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric shift hShift) coefficients

/-- The canonical gauge current contracts with the actual transpose velocity. -/
def maxwellRecenterGaugeMetricCovector (point : EffectiveQuotient period hPeriod) :
    Matrix4 →L[Real] Real :=
  ∑ index : Fin 4, ∑ component : Fin 2, ∑ row : Fin 4,
    (regularFrameCanonicalMaxwellVariationalResidualCoefficient period hPeriod
        (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric shift hShift)
        (recenteredPotential period hPeriod metric shift hShift coefficients) index component point *
      coefficients point (row, component)) •
    (matrixEntryCLM row index).comp (maxwellRecenterGaugeMatrixVelocity period hPeriod metric shift point)

theorem maxwellRecenterGaugeMetricCovector_apply
    (point : EffectiveQuotient period hPeriod) (matrix : Matrix4) :
    maxwellRecenterGaugeMetricCovector period hPeriod metric shift hShift coefficients point matrix =
      ∑ index : Fin 4, ∑ component : Fin 2, ∑ row : Fin 4,
        (regularFrameCanonicalMaxwellVariationalResidualCoefficient period hPeriod
          (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric shift hShift)
          (recenteredPotential period hPeriod metric shift hShift coefficients) index component point *
          coefficients point (row, component)) *
        maxwellRecenterGaugeMatrixVelocity period hPeriod metric shift point matrix row index := by
  simp only [maxwellRecenterGaugeMetricCovector, sum_apply, smul_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul]
  rfl

def maxwellRecenterGaugeMetricCoefficient (first second : Fin 4) :
    SmoothScalarField period hPeriod where
  toFun := fun point => maxwellRecenterGaugeMetricCovector period hPeriod
    metric shift hShift coefficients point (Matrix.single first second 1)
  contMDiff_toFun := by
    simp only [maxwellRecenterGaugeMetricCovector_apply]
    apply ContMDiff.sum
    intro index _
    apply ContMDiff.sum
    intro component _
    apply ContMDiff.sum
    intro row _
    exact ((regularFrameCanonicalMaxwellVariationalResidualCoefficient period hPeriod
      (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric shift hShift)
      (recenteredPotential period hPeriod metric shift hShift coefficients) index component
      ).contMDiff_toFun.mul
      (regularFrameGaugeCoefficient period hPeriod coefficients (row, component)).contMDiff_toFun).mul
      ((matrixEntryCLM row index).contMDiff.comp
        (maxwellRecenterGaugeMatrixVelocity_contMDiff period hPeriod metric shift hShift
          (Matrix.single first second 1)))

/-- The metric duals use the reconstructed metric and the original frame. -/
def maxwellRecenterGaugeMetricResidual : SmoothSymmetricCovariantTwoTensor period hPeriod :=
  let frame := regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric
  let newMetric := (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric shift hShift).metric
  ∑ first : Fin 4, ∑ second : Fin 4,
    smoothBulkScalarSMulTensor period hPeriod
      (maxwellRecenterGaugeMetricCoefficient period hPeriod metric shift hShift coefficients first second)
      (smoothBulkCovectorSymmetricProduct period hPeriod
        (generalMetricFrameCovector period hPeriod frame newMetric.tensor first)
        (generalMetricFrameCovector period hPeriod frame newMetric.tensor second))

private theorem matrixLinearCovector_eq_sum (covector : Matrix4 →ₗ[Real] Real) (matrix : Matrix4) :
    covector matrix = ∑ row : Fin 4, ∑ column : Fin 4,
      covector (Matrix.single row column 1) * matrix row column := by
  have hMatrix := Matrix.matrix_eq_sum_single matrix
  conv_lhs => rw [hMatrix]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro row _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro column _
  rw [show Matrix.single row column (matrix row column) =
    (matrix row column) • Matrix.single row column (1 : Real) by
      simp only [Matrix.smul_single, smul_eq_mul, mul_one]]
  rw [map_smul]
  exact mul_comm _ _

theorem maxwellRecenterGaugeMetricResidual_pairing_eq_covector
    (direction : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalMetricTensorPairingAt period hPeriod
        (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric shift hShift).metric
        (maxwellRecenterGaugeMetricResidual period hPeriod metric shift hShift coefficients) direction point =
      maxwellRecenterGaugeMetricCovector period hPeriod metric shift hShift coefficients point
        (regularFrameCovariantVariationMatrixAt period hPeriod metric direction point) := by
  let frame := regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric
  let newMetric := (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric shift hShift).metric
  rw [generalMetricTensorPairingAt_symmetric]
  let pairing : SmoothSymmetricCovariantTwoTensor period hPeriod →ₗ[Real] Real :=
    { toFun := fun tensor => generalMetricTensorPairingAt period hPeriod newMetric direction tensor point
      map_add' := fun first second => generalMetricTensorPairingAt_add_right period hPeriod
        newMetric direction first second point
      map_smul' := fun scalar tensor => generalMetricTensorPairingAt_smul_right period hPeriod
        newMetric scalar direction tensor point }
  change pairing (maxwellRecenterGaugeMetricResidual period hPeriod metric shift hShift coefficients) =
    (maxwellRecenterGaugeMetricCovector period hPeriod metric shift hShift coefficients point).toLinearMap
      (regularFrameCovariantVariationMatrixAt period hPeriod metric direction point)
  rw [matrixLinearCovector_eq_sum]
  unfold maxwellRecenterGaugeMetricResidual
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro first _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro second _
  let coefficient := maxwellRecenterGaugeMetricCoefficient period hPeriod
    metric shift hShift coefficients first second
  let rankOne := smoothBulkCovectorSymmetricProduct period hPeriod
    (generalMetricFrameCovector period hPeriod frame newMetric.tensor first)
    (generalMetricFrameCovector period hPeriod frame newMetric.tensor second)
  have hCongr : pairing (smoothBulkScalarSMulTensor period hPeriod coefficient rankOne) =
      pairing ((coefficient point) • rankOne) := by
    apply generalMetricTensorPairingAt_congr_right_at
    apply ContinuousLinearMap.ext
    intro left
    apply ContinuousLinearMap.ext
    intro right
    rfl
  rw [hCongr, map_smul]
  change coefficient point * pairing rankOne = coefficient point * _
  apply congrArg (coefficient point * ·)
  exact generalMetricSymmetricFrameProduct_pairing period hPeriod frame newMetric direction point first second

private theorem matrixTransposeTransport_comp (velocity inverse : Matrix4)
    (packet : Fin 4 → Real) (index : Fin 4) :
    (∑ middle : Fin 4, inverse middle index *
        ∑ row : Fin 4, velocity row middle * packet row) =
      ∑ row : Fin 4, (velocity * inverse) row index * packet row := by
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro row _
  apply Finset.sum_congr rfl
  intro middle _
  ring

private theorem smoothFrameTransport_value
    (root : SmoothQuotientField period hPeriod Matrix4)
    (packet : SmoothQuotientField period hPeriod GaugeFiber)
    (point : EffectiveQuotient period hPeriod) (index : Fin 4) (component : Fin 2) :
    smoothGaugeCoefficientFrameTransport period hPeriod root packet point (index, component) =
      ∑ row : Fin 4, root point row index * packet point (row, component) := by
  rw [smoothGaugeCoefficientFrameTransport_apply]
  simp only [smoothGaugeCoefficientFrameTransportEntry, smoothScalarFieldFinsetSum_apply,
    smoothScalarFieldMul_apply, smoothMatrixFieldCoefficients_apply]
  rfl

private theorem metricInducedCoefficients_reconstructed_value
    (base : RegularGeneralLorentzMetric period hPeriod)
    (direction : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (packet : SmoothQuotientField period hPeriod GaugeFiber)
    (point : EffectiveQuotient period hPeriod) (index : Fin 4) (component : Fin 2) :
    metricInducedGaugeCoefficients period hPeriod base direction
        (regularFrameGaugePotentialFromCoefficients period hPeriod base packet) point (index, component) =
      (1 / 2 : Real) * ∑ row : Fin 4,
        c2FiniteMatrixValueAt period hPeriod 4
          (regularGeneralMetricC2VariationMatrix period hPeriod base direction) point row index *
        packet point (row, component) := by
  change metricInducedGaugeCoefficientEntry period hPeriod base direction
    (regularFrameGaugePotentialFromCoefficients period hPeriod base packet) index component point = _
  simp only [metricInducedGaugeCoefficientEntry, gaugePotentialFrameCoefficients_reconstructed,
    smoothQuotientField_smul_apply, smul_eq_mul, smoothScalarFieldFinsetSum_apply,
    smoothScalarFieldMul_apply]
  rfl

include hShift in
theorem maxwellRecenterGaugeMatrixVelocity_smoothTest
    (direction : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    maxwellRecenterGaugeMatrixVelocity period hPeriod metric shift point
        (regularFrameCovariantVariationMatrixAt period hPeriod metric direction point) =
      regularGeneralMetricSmoothIdentityRootVelocity period hPeriod metric shift direction hShift point *
        regularGeneralMetricC2IdentityRootInverseMatrixAt period hPeriod metric shift point -
      (1 / 2 : Real) • c2FiniteMatrixValueAt period hPeriod 4
        (regularGeneralMetricC2VariationMatrix period hPeriod
          (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric shift hShift) direction) point := by
  have hRelative : c2FiniteMatrixValueAt period hPeriod 4
      (regularGeneralMetricC2VariationMatrix period hPeriod metric direction) point =
      regularFrameMetricInverseMatrixMap period hPeriod metric point *
        regularFrameCovariantVariationMatrixAt period hPeriod metric direction point :=
    regularGeneralMetricC2RelativeMatrixAt_smooth period hPeriod metric direction point
  rw [maxwellRecenterGaugeMatrixVelocity_apply,
    regularGeneralMetricSmoothIdentityRootVelocity_apply,
    regularGeneralMetricC2LorentzChartVariationMatrix_valueAt, hRelative]

/-- The packet is the genuine smooth velocity from Gate616, including both root terms. -/
theorem smoothMobileMaxwellRecenterGaugeCoefficients_eq_matrixVelocity
    (direction : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) (index : Fin 4) (component : Fin 2) :
    smoothMobileMaxwellRecenterGaugeCoefficients period hPeriod metric shift direction hShift
        coefficients point (index, component) =
      ∑ row : Fin 4, maxwellRecenterGaugeMatrixVelocity period hPeriod metric shift point
        (regularFrameCovariantVariationMatrixAt period hPeriod metric direction point) row index *
          coefficients point (row, component) := by
  let shifted := regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric shift hShift
  let inverse := regularGeneralMetricC2IdentityRootInverseMatrixField period hPeriod metric shift hShift
  let velocity := regularGeneralMetricSmoothIdentityRootVelocity period hPeriod metric shift direction hShift
  change smoothGaugeCoefficientFrameTransport period hPeriod inverse
      (smoothGaugeCoefficientFrameTransport period hPeriod velocity coefficients) point (index, component) -
    metricInducedGaugeCoefficients period hPeriod shifted direction
      (regularFrameGaugePotentialFromCoefficients period hPeriod shifted coefficients) point (index, component) = _
  rw [smoothFrameTransport_value, metricInducedCoefficients_reconstructed_value]
  simp_rw [smoothFrameTransport_value]
  rw [matrixTransposeTransport_comp]
  rw [maxwellRecenterGaugeMatrixVelocity_smoothTest period hPeriod metric shift hShift direction point]
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, sub_mul,
    Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]
  rfl

/-- Pointwise representation of the additional canonical gauge pairing by the metric tensor. -/
theorem maxwellRecenterGaugeMetricResidual_pairing
    (direction : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    generalMetricTensorPairingAt period hPeriod
        (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric shift hShift).metric
        (maxwellRecenterGaugeMetricResidual period hPeriod metric shift hShift coefficients) direction point =
      inner Real
        (regularFrameCanonicalMaxwellVariationalResidual period hPeriod
          (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric shift hShift)
          (regularFrameGaugePotentialFromCoefficients period hPeriod
            (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric shift hShift) coefficients) point)
        (gaugePotentialFrameCoefficients period hPeriod
          (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric shift hShift)
          (smoothMobileMaxwellRecenterGaugePotential period hPeriod metric shift direction hShift coefficients) point) := by
  rw [maxwellRecenterGaugeMetricResidual_pairing_eq_covector,
    maxwellRecenterGaugeMetricCovector_apply, smoothMobileMaxwellRecenterGaugePotential,
    gaugePotentialFrameCoefficients_reconstructed, PiLp.inner_apply, Fintype.sum_prod_type]
  simp only [Real.inner_apply, regularFrameCanonicalMaxwellVariationalResidual_apply]
  simp_rw [smoothMobileMaxwellRecenterGaugeCoefficients_eq_matrixVelocity, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index _
  apply Finset.sum_congr rfl
  intro component _
  apply Finset.sum_congr rfl
  intro row _
  dsimp only [recenteredPotential]
  ring

/-- The actual canonical gauge residual on the recentering potential is the
integral of its smooth metric residual. No current or volume term is discarded. -/
theorem canonicalMaxwellResidualPairing_recenterGaugePotential_eq_metricIntegral
    (direction : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    canonicalRegularFrameIntrinsicGaugeResidualPairing period hPeriod
        (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric shift hShift)
        (regularFrameCanonicalMaxwellVariationalResidual period hPeriod
          (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric shift hShift)
          (regularFrameGaugePotentialFromCoefficients period hPeriod
            (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric shift hShift) coefficients))
        (smoothMobileMaxwellRecenterGaugePotential period hPeriod metric shift direction hShift coefficients) =
      ∫ point, generalMetricTensorPairingAt period hPeriod
        (regularGeneralMetricC2LorentzChartRegularMetric period hPeriod metric shift hShift).metric
        (maxwellRecenterGaugeMetricResidual period hPeriod metric shift hShift coefficients) direction point
        ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  unfold canonicalRegularFrameIntrinsicGaugeResidualPairing
    regularFrameIntrinsicGaugeResidualPairing smoothGaugeResidualPairing
  apply congrArg (fun density : EffectiveQuotient period hPeriod → Real =>
    ∫ point, density point ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
  funext point
  exact (maxwellRecenterGaugeMetricResidual_pairing period hPeriod
    metric shift hShift coefficients direction point).symm

end
end P0EFTJanusMaxwellRecenterGaugeMetricResidual4D
end JanusFormal
