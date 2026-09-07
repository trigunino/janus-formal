import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPairedInteractionMetricCenterSylvester4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRegularFrameFixedVolumeRicciResidual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootSmoothLift4D

/-! # Two smooth tensor representatives of the centre interaction covector

The pointwise inverse Sylvester operator acts on the exact two metric
velocities. Its spectral covector supplies sixteen smooth coefficients for
each sector. Metric-dual rank-one tensors reconstruct their invariant
representatives, including the fixed plus-volume factor of the action.
-/
namespace JanusFormal
namespace P0EFTJanusPairedInteractionSmoothMetricResidual4D
set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 600000
noncomputable section
open Set
open scoped Manifold ContDiff BigOperators Matrix.Norms.Frobenius
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVUltralocalMaster4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixInverse4D
open P0EFTJanusPositiveRawSplitCharpolyContDiffLocalRootBranch4D
open P0EFTJanusMatrixInteractionFrechetNoether
open P0EFTJanusReciprocalBimetricPotential
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open P0EFTJanusProgramPRegularFrameMetricInverse4D
open P0EFTJanusProgramPRegularGeneralMetricGlobalMaxwellDivergence4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootLift4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootSmoothLift4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartInteraction4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedRelativeMatrixCore4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalRelativeMetricCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomainOpen4D
open P0EFTJanusPairedInteractionMetricCenterSylvester4D

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
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance
local instance : CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod
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

/-- The root hypothesis used here follows from the actual centre matrix domain. -/
theorem pairedInteractionCenter_rootAdmissible
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hZero : (0 : RegularGeneralMetricC2PairedRelativeCore
      period hPeriod plusBase minusBase) ∈
      regularGeneralMetricC2PairedLorentzMatrixDomain period hPeriod plusBase minusBase) :
    RegularGeneralMetricC2IdentityRootAdmissible period hPeriod plusBase
      (minusBase.metric.tensor - plusBase.metric.tensor) := by
  have hRoot := hZero.2.2.2.1
  simpa only [RegularGeneralMetricC2IdentityRootAdmissible,
    regularGeneralMetricC2PairedRelativeMatrix,
    regularGeneralMetricC2IdentityRootInverseC2Matrix_zero, add_zero,
    Prod.fst_zero, Prod.snd_zero,
    c2FiniteMatrixProduct_identity_left, c2FiniteMatrixProduct_identity_right] using hRoot

variable (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)

/-- The smooth base root, in the fixed plus frame. -/
def pairedInteractionCenterRoot : EffectiveQuotient period hPeriod → Matrix4 :=
  regularGeneralMetricC2IdentityRootMatrixAt period hPeriod plusBase
    (minusBase.metric.tensor - plusBase.metric.tensor)

def pairedInteractionCenterRelativeMatrix : EffectiveQuotient period hPeriod → Matrix4 :=
  fun point => regularGeneralMetricAffineRelativeMatrixField period hPeriod plusBase
    (minusBase.metric.tensor - plusBase.metric.tensor) point - 1

def pairedInteractionCenterSylvesterInverse :
    EffectiveQuotient period hPeriod → Matrix4 →L[Real] Matrix4 :=
  fun point => (canonicalSylvesterOperator
    (pairedInteractionCenterRoot period hPeriod plusBase minusBase point)).inverse

variable (hRoot : RegularGeneralMetricC2IdentityRootAdmissible period hPeriod plusBase
  (minusBase.metric.tensor - plusBase.metric.tensor))

include hRoot in
theorem pairedInteractionCenterSylvester_isInvertible (point : EffectiveQuotient period hPeriod) :
    (canonicalSylvesterOperator
      (pairedInteractionCenterRoot period hPeriod plusBase minusBase point)).IsInvertible := by
  let equiv := (LinearEquiv.ofBijective
    (canonicalSylvesterOperator
      (pairedInteractionCenterRoot period hPeriod plusBase minusBase point)).toLinearMap
    (regularGeneralMetricC2IdentityRootMatrixAt_sylvester_bijective period hPeriod
      plusBase (minusBase.metric.tensor - plusBase.metric.tensor) hRoot point)).toContinuousLinearEquiv
  refine ⟨equiv, ?_⟩
  ext matrix
  rfl

include hRoot in
theorem pairedInteractionCenterSylvesterInverse_contMDiff :
    ContMDiff coverModelWithCorners (modelWithCornersSelf Real (Matrix4 →L[Real] Matrix4)) ∞
      (pairedInteractionCenterSylvesterInverse period hPeriod plusBase minusBase) := by
  let family : Matrix4 →L[Real] (Matrix4 →L[Real] Matrix4) := canonicalSylvesterFamily
  have hSmooth := family.contMDiff.comp
    (regularGeneralMetricC2IdentityRootMatrixAt_contMDiff period hPeriod plusBase
      (minusBase.metric.tensor - plusBase.metric.tensor) hRoot)
  intro point
  exact ((pairedInteractionCenterSylvester_isInvertible period hPeriod
    plusBase minusBase hRoot point).contDiffAt_map_inverse (n := ∞)).comp_contMDiffAt
      (f := fun p : EffectiveQuotient period hPeriod =>
        family (pairedInteractionCenterRoot period hPeriod plusBase minusBase p))
      (x := point)
      hSmooth.contMDiffAt

include hRoot in
/-- The smooth inverse selects the unique solution of the actual Sylvester equation. -/
theorem pairedInteractionCenterSylvesterInverse_solve
    (point : EffectiveQuotient period hPeriod) (velocity rootVelocity : Matrix4)
    (hEquation : canonicalSylvesterOperator
      (pairedInteractionCenterRoot period hPeriod plusBase minusBase point) rootVelocity = velocity) :
    pairedInteractionCenterSylvesterInverse period hPeriod plusBase minusBase point velocity =
      rootVelocity := by
  exact (pairedInteractionCenterSylvester_isInvertible period hPeriod plusBase minusBase
    hRoot point).inverse_apply_eq.mpr hEquation.symm

/-- Exact sector velocity of the relative matrix from covariant matrix input.
Both inputs are expressed in the fixed plus frame. -/
def pairedInteractionMetricMatrixVelocity (sector : Sector)
    (point : EffectiveQuotient period hPeriod) : Matrix4 →L[Real] Matrix4 :=
  let product := ContinuousLinearMap.mul Real Matrix4
  let raise := product (regularFrameMetricInverseMatrixMap period hPeriod plusBase point)
  let relative := pairedInteractionCenterRelativeMatrix period hPeriod plusBase minusBase point
  match sector with
  | .plus => -raise - (1 / 2 : Real) •
      ((product relative).comp raise + (product.comp raise).flip relative)
  | .minus => raise

theorem pairedInteractionMetricMatrixVelocity_contMDiff (sector : Sector) (matrix : Matrix4) :
    ContMDiff coverModelWithCorners (modelWithCornersSelf Real Matrix4) ∞
      (fun point => pairedInteractionMetricMatrixVelocity period hPeriod
        plusBase minusBase sector point matrix) := by
  let product : Matrix4 →L[Real] Matrix4 →L[Real] Matrix4 := ContinuousLinearMap.mul Real Matrix4
  have hRaise := (product.contMDiff.comp
    (regularFrameMetricInverseMatrixMap_contMDiff period hPeriod plusBase)).clm_apply
      (contMDiff_const (c := matrix))
  have hRelative := (regularGeneralMetricAffineRelativeMatrixField period hPeriod plusBase
    (minusBase.metric.tensor - plusBase.metric.tensor)).contMDiff_toFun.sub
      (contMDiff_const (c := (1 : Matrix4)))
  have hHalf : ContMDiff coverModelWithCorners (modelWithCornersSelf Real Real) ∞
      (fun _ : EffectiveQuotient period hPeriod => (1 / 2 : Real)) := contMDiff_const
  cases sector with
  | plus =>
      exact hRaise.neg.sub (hHalf.smul
        (((product.contMDiff.comp hRelative).clm_apply hRaise).add
          ((product.contMDiff.comp hRaise).clm_apply hRelative)))
  | minus => exact hRaise

/-- The spectral differential is polynomial in the root and the velocity.
This statement uses the canonical matrix topology, independent of the
Frobenius topology used to prove the original differential formula. -/
theorem matrixSpectralPotentialDerivative_contMDiff
    (coefficients : PotentialCoefficients)
    (root velocity : EffectiveQuotient period hPeriod → Matrix4)
    (hSmoothRoot : ContMDiff coverModelWithCorners (modelWithCornersSelf Real Matrix4) ∞ root)
    (hVelocity : ContMDiff coverModelWithCorners (modelWithCornersSelf Real Matrix4) ∞ velocity) :
    ContMDiff coverModelWithCorners (modelWithCornersSelf Real Real) ∞
      (fun point => matrixSpectralPotentialDerivative coefficients (root point) (velocity point)) := by
  have hRootEntry (row column : Fin 4) :=
    (matrixEntryCLM row column).contMDiff.comp hSmoothRoot
  have hVelocityEntry (row column : Fin 4) :=
    (matrixEntryCLM row column).contMDiff.comp hVelocity
  simp only [matrixSpectralPotentialDerivative_apply, matrixElementary2Derivative_apply,
    matrixElementary3Derivative_apply, determinantDerivative_apply, Matrix.trace,
    Matrix.diag_apply, Matrix.mul_apply, Matrix.add_apply, div_eq_mul_inv]
  repeat first
    | exact hRootEntry _ _
    | exact hVelocityEntry _ _
    | exact contMDiff_const
    | apply ContMDiff.add
    | apply ContMDiff.sub
    | apply ContMDiff.neg
    | apply ContMDiff.mul
    | apply ContMDiff.pow

/-- The exact fixed-volume spectral covector on one covariant matrix input. -/
def pairedInteractionMetricCovector (interactionScale : Real)
    (coefficients : PotentialCoefficients) (sector : Sector)
    (point : EffectiveQuotient period hPeriod) : Matrix4 →ₗ[Real] Real :=
  (-interactionScale * plusBase.volume point) •
    ((matrixSpectralPotentialDerivative coefficients
        (pairedInteractionCenterRoot period hPeriod plusBase minusBase point)).toLinearMap.comp
      ((pairedInteractionCenterSylvesterInverse period hPeriod plusBase minusBase point).toLinearMap.comp
        (pairedInteractionMetricMatrixVelocity period hPeriod plusBase minusBase sector point).toLinearMap))

include hRoot in
/-- A root velocity satisfying the already-derived Sylvester equation gives
exactly this covector, including the fixed volume density. -/
theorem pairedInteractionMetricCovector_apply_of_sylvester
    (interactionScale : Real) (coefficients : PotentialCoefficients) (sector : Sector)
    (point : EffectiveQuotient period hPeriod) (matrix rootVelocity : Matrix4)
    (hEquation : canonicalSylvesterOperator
        (pairedInteractionCenterRoot period hPeriod plusBase minusBase point) rootVelocity =
      pairedInteractionMetricMatrixVelocity period hPeriod plusBase minusBase sector point matrix) :
    pairedInteractionMetricCovector period hPeriod plusBase minusBase interactionScale
        coefficients sector point matrix =
      (-interactionScale * plusBase.volume point) *
        matrixSpectralPotentialDerivative coefficients
          (pairedInteractionCenterRoot period hPeriod plusBase minusBase point) rootVelocity := by
  change (-interactionScale * plusBase.volume point) *
    matrixSpectralPotentialDerivative coefficients
      (pairedInteractionCenterRoot period hPeriod plusBase minusBase point)
      (pairedInteractionCenterSylvesterInverse period hPeriod plusBase minusBase point
        (pairedInteractionMetricMatrixVelocity period hPeriod plusBase minusBase sector point matrix)) = _
  rw [pairedInteractionCenterSylvesterInverse_solve period hPeriod plusBase minusBase
    hRoot point _ rootVelocity hEquation]

include hRoot in
theorem pairedInteractionMetricCovector_contMDiff
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (sector : Sector) (matrix : Matrix4) :
    ContMDiff coverModelWithCorners (modelWithCornersSelf Real Real) ∞
      (fun point => pairedInteractionMetricCovector period hPeriod plusBase minusBase
        interactionScale coefficients sector point matrix) := by
  have hRootSmooth := regularGeneralMetricC2IdentityRootMatrixAt_contMDiff period hPeriod
    plusBase (minusBase.metric.tensor - plusBase.metric.tensor) hRoot
  have hVelocity := (pairedInteractionCenterSylvesterInverse_contMDiff period hPeriod
    plusBase minusBase hRoot).clm_apply
      (pairedInteractionMetricMatrixVelocity_contMDiff period hPeriod
        plusBase minusBase sector matrix)
  exact (contMDiff_const.mul plusBase.volume.contMDiff_toFun).mul
    (matrixSpectralPotentialDerivative_contMDiff period hPeriod coefficients
      _ _ hRootSmooth hVelocity)

/-- Sixteen smooth covector coefficients in each sector. -/
def pairedInteractionMetricCoefficient (interactionScale : Real)
    (coefficients : PotentialCoefficients) (sector : Sector)
    (row column : Fin 4) : SmoothScalarField period hPeriod where
  toFun := fun point => pairedInteractionMetricCovector period hPeriod plusBase minusBase
    interactionScale coefficients sector point (Matrix.single row column 1)
  contMDiff_toFun := pairedInteractionMetricCovector_contMDiff period hPeriod
    plusBase minusBase hRoot interactionScale coefficients sector _

/-- Metric-dual products are used rather than coframe products, since the
coefficients act directly on covariant components in the fixed plus frame. -/
def pairedInteractionSmoothMetricResidual (interactionScale : Real)
    (coefficients : PotentialCoefficients) (sector : Sector) :
    SmoothSymmetricCovariantTwoTensor period hPeriod :=
  let frame := regularGeneralLorentzMetricSmoothD8Frame period hPeriod plusBase
  let metric := match sector with | .plus => plusBase.metric | .minus => minusBase.metric
  ∑ row : Fin 4, ∑ column : Fin 4,
    smoothBulkScalarSMulTensor period hPeriod
      (pairedInteractionMetricCoefficient period hPeriod plusBase minusBase hRoot
        interactionScale coefficients sector row column)
      (smoothBulkCovectorSymmetricProduct period hPeriod
        (generalMetricFrameCovector period hPeriod frame metric.tensor row)
        (generalMetricFrameCovector period hPeriod frame metric.tensor column))

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

/-- Each of the two constructed tensors represents its actual spectral
covector on every smooth symmetric metric test, pointwise. -/
theorem pairedInteractionSmoothMetricResidual_pairing
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (sector : Sector) (test : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    let metric := match sector with | .plus => plusBase.metric | .minus => minusBase.metric
    generalMetricTensorPairingAt period hPeriod metric
        (pairedInteractionSmoothMetricResidual period hPeriod plusBase minusBase hRoot
          interactionScale coefficients sector) test point =
      pairedInteractionMetricCovector period hPeriod plusBase minusBase
        interactionScale coefficients sector point
        (fun row column => test.tensor point
          (plusBase.frame row point) (plusBase.frame column point)) := by
  let frame := regularGeneralLorentzMetricSmoothD8Frame period hPeriod plusBase
  let metric := match sector with | .plus => plusBase.metric | .minus => minusBase.metric
  dsimp only
  rw [generalMetricTensorPairingAt_symmetric]
  let pairing : SmoothSymmetricCovariantTwoTensor period hPeriod →ₗ[Real] Real :=
    { toFun := fun tensor => generalMetricTensorPairingAt period hPeriod metric test tensor point
      map_add' := fun first second => generalMetricTensorPairingAt_add_right period hPeriod
        metric test first second point
      map_smul' := fun scalar tensor => generalMetricTensorPairingAt_smul_right period hPeriod
        metric scalar test tensor point }
  change pairing (pairedInteractionSmoothMetricResidual period hPeriod plusBase minusBase hRoot
    interactionScale coefficients sector) = _
  rw [matrixLinearCovector_eq_sum]
  unfold pairedInteractionSmoothMetricResidual
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro row _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro column _
  let coefficient := pairedInteractionMetricCoefficient period hPeriod plusBase minusBase hRoot
    interactionScale coefficients sector row column
  let rankOne := smoothBulkCovectorSymmetricProduct period hPeriod
    (generalMetricFrameCovector period hPeriod frame metric.tensor row)
    (generalMetricFrameCovector period hPeriod frame metric.tensor column)
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
  exact generalMetricSymmetricFrameProduct_pairing period hPeriod frame metric test point row column

/-- Explicit paired residual, with the two sector pairings kept separate. -/
def pairedInteractionSmoothMetricResidualPair (interactionScale : Real)
    (coefficients : PotentialCoefficients) :
    SmoothSymmetricCovariantTwoTensor period hPeriod ×
      SmoothSymmetricCovariantTwoTensor period hPeriod :=
  (pairedInteractionSmoothMetricResidual period hPeriod plusBase minusBase hRoot
      interactionScale coefficients .plus,
    pairedInteractionSmoothMetricResidual period hPeriod plusBase minusBase hRoot
      interactionScale coefficients .minus)

end
end P0EFTJanusPairedInteractionSmoothMetricResidual4D
end JanusFormal
