import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPairedInteractionRecenterValue4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPairedRelativeVelocityCommutator4D

/-! # Native interaction derivative at a reconstructed smooth centre

The actual C² Leibniz and Sylvester equations, together with the exact
transport of smooth metric tests, determine the recentering commutator.
Its spectral differential vanishes. The final action equality retains the
fixed plus-volume and arbitrary interaction coefficients.
-/

namespace JanusFormal
namespace P0EFTJanusPairedInteractionDerivativeRecenter4D
set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 600000
noncomputable section
open Set MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusReciprocalBimetricPotential
open P0EFTJanusMatrixInteractionFrechetNoether
open P0EFTJanusPositiveRawSplitCharpolyContDiffLocalRootBranch4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixInverse4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2IdentityRootBranch4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2IdentityRootDerivative4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootLift4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootSmoothLift4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootSmoothInverse4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootInverseCore4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartMatrixDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartRegularMetric4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartVariationTransport4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartGeometry4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalRelativeMetricCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomainOpen4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMetricTotalEulerReduction4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalInteractionC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedRelativeMatrixCore4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedRelativeMatrixDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedRelativeRootSpectralDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedInteractionActionDerivative4D
open P0EFTJanusPairedInteractionMetricCenterSylvester4D
open P0EFTJanusPairedInteractionRecenterValue4D
open P0EFTJanusPairedRelativeVelocityCommutator4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
attribute [local instance 1900]
  P0EFTJanusProgramPRegularGeneralMetricC2PairedInteractionActionDerivative4D.relativeCoreNormedAddCommGroup
  P0EFTJanusProgramPRegularGeneralMetricC2PairedInteractionActionDerivative4D.relativeCoreNormedSpace

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev Matrix4 := Matrix (Fin 4) (Fin 4) Real
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod
private abbrev C2Matrix := C2FiniteMatrix period hPeriod 4
private abbrev RelativeCore (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :=
  RegularGeneralMetricC2PairedRelativeCore period hPeriod plusBase minusBase
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
local instance : CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod
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

private def matrixValueLinearMap (point : EffectiveQuotient period hPeriod) :
    C2Matrix period hPeriod →ₗ[Real] Matrix4 where
  toFun := fun matrix => c2FiniteMatrixValueAt period hPeriod 4 matrix point
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem matrixValue_neg (matrix : C2Matrix period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    c2FiniteMatrixValueAt period hPeriod 4 (-matrix) point =
      -c2FiniteMatrixValueAt period hPeriod 4 matrix point :=
  (matrixValueLinearMap period hPeriod point).map_neg matrix

private theorem matrixValue_smul (scalar : Real) (matrix : C2Matrix period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    c2FiniteMatrixValueAt period hPeriod 4 (scalar • matrix) point =
      scalar • c2FiniteMatrixValueAt period hPeriod 4 matrix point :=
  (matrixValueLinearMap period hPeriod point).map_smul scalar matrix

private theorem matrixValue_sub (first second : C2Matrix period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    c2FiniteMatrixValueAt period hPeriod 4 (first - second) point =
      c2FiniteMatrixValueAt period hPeriod 4 first point -
        c2FiniteMatrixValueAt period hPeriod 4 second point :=
  (matrixValueLinearMap period hPeriod point).map_sub first second

private theorem matrixValue_sylvester (root velocity : C2Matrix period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    c2FiniteMatrixValueAt period hPeriod 4
        (c2FiniteMatrixSylvester period hPeriod 4 root velocity) point =
      c2FiniteMatrixValueAt period hPeriod 4 root point *
          c2FiniteMatrixValueAt period hPeriod 4 velocity point +
        c2FiniteMatrixValueAt period hPeriod 4 velocity point *
          c2FiniteMatrixValueAt period hPeriod 4 root point := by
  change c2FiniteMatrixValueAt period hPeriod 4
    (c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) 4 root velocity +
      c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) 4 velocity root) point = _
  rw [c2FiniteMatrixValueAt_add, c2FiniteMatrixValueAt_product,
    c2FiniteMatrixValueAt_product]

/-- Evaluation of the actual native Leibniz derivative at an arbitrary core. -/
theorem pairedInteractionRelativeMatrixDerivative_valueAt
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (core direction : RelativeCore period hPeriod plusBase minusBase)
    (hCore : core ∈ regularGeneralMetricC2PairedRelativeMatrixDomain
      period hPeriod plusBase minusBase)
    (point : EffectiveQuotient period hPeriod) :
    c2FiniteMatrixValueAt period hPeriod 4
        (regularGeneralMetricC2PairedRelativeMatrixDerivative period hPeriod
          plusBase minusBase core hCore direction) point =
      matrixPairedOriginalRelativeVelocity
        (c2FiniteMatrixValueAt period hPeriod 4
          (regularGeneralMetricC2IdentityRootInverseC2Matrix period hPeriod core.2.1) point)
        (c2FiniteMatrixValueAt period hPeriod 4
          (regularGeneralMetricC2IdentityRootInverseDerivative period hPeriod
            core.2.1 hCore direction.2.1) point)
        (c2FiniteMatrixValueAt period hPeriod 4
          (regularGeneralMetricC2PairedAffineRelativeMatrix period hPeriod plusBase minusBase core) point)
        (c2FiniteMatrixValueAt period hPeriod 4 direction.2.2 point) := by
  simp only [regularGeneralMetricC2PairedRelativeMatrixDerivative,
    regularGeneralMetricC2PairedRelativeRightProductDerivative,
    regularGeneralMetricC2PairedRelativeRightProduct,
    regularGeneralMetricC2PairedInverseRootOnCoreDerivative,
    regularGeneralMetricC2PairedInverseRootOnCore,
    regularGeneralMetricC2PairedAffineRelativeMatrixDerivative, zero_add,
    add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    regularGeneralMetricC2PairedRelativePlusProjection_apply,
    regularGeneralMetricC2PairedRelativeCrossProjection_apply,
    c2FiniteMatrixValueAt_add, c2FiniteMatrixValueAt_product,
    matrixPairedOriginalRelativeVelocity]

/-- The genuine root derivative satisfies Sylvester at every admissible core. -/
theorem pairedInteractionRelativeRootDerivative_sylvester
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (core direction : RelativeCore period hPeriod plusBase minusBase)
    (hCore : core ∈ regularGeneralMetricC2PairedLorentzMatrixDomain
      period hPeriod plusBase minusBase) :
    c2FiniteMatrixSylvester period hPeriod 4
        (regularGeneralMetricC2PairedRelativeRoot period hPeriod plusBase minusBase core)
        (regularGeneralMetricC2PairedRelativeRootDerivative period hPeriod
          plusBase minusBase core hCore direction) =
      regularGeneralMetricC2PairedRelativeMatrixDerivative period hPeriod
        plusBase minusBase core hCore.2.1 direction := by
  unfold regularGeneralMetricC2PairedRelativeRootDerivative
    regularGeneralMetricC2PairedRelativeRoot
  rw [ContinuousLinearMap.comp_apply, c2IdentityRootDerivative_sylvester]

section Recenter
variable (configuration : GlobalFieldConfiguration period hPeriod)
  (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
  (plusVariation minusVariation : SmoothSymmetricCovariantTwoTensor period hPeriod)
  (hAdmissible : RegularGeneralMetricC2PairedLorentzChartAdmissible period hPeriod
    plusBase minusBase plusVariation minusVariation)

local notation "newPlus" => regularGeneralMetricC2PairedPlusMetric period hPeriod
  plusBase minusBase plusVariation minusVariation hAdmissible
local notation "newMinus" => regularGeneralMetricC2PairedMinusMetric period hPeriod
  plusBase minusBase plusVariation minusVariation hAdmissible
local notation "oldPoint" => pairedInteractionSmoothCore period hPeriod
  plusBase minusBase plusVariation minusVariation

include configuration hAdmissible in
theorem pairedInteractionSmoothCore_mem_lorentzMatrixDomain :
    oldPoint ∈ regularGeneralMetricC2PairedLorentzMatrixDomain
      period hPeriod plusBase minusBase := by
  rw [pairedInteractionSmoothCore_eq_projected period hPeriod configuration]
  apply (globalMetricPerturbationPairLorentzChartAdmissible_iff_mem_matrixDomain
    period hPeriod configuration plusBase minusBase _).mp
  exact hAdmissible

private theorem recenteredRelativeTensor_eq :
    (newMinus).metric.tensor - (newPlus).metric.tensor =
      regularGeneralMetricC2PairedRelativeTensor period hPeriod plusBase minusBase
        plusVariation minusVariation := by
  change (regularGeneralMetricC2LorentzChartMetric period hPeriod minusBase
      minusVariation hAdmissible.minus_mem).tensor -
    (regularGeneralMetricC2LorentzChartMetric period hPeriod plusBase
      plusVariation hAdmissible.plus_mem).tensor = _
  rw [regularGeneralMetricC2LorentzChartMetric_tensor,
    regularGeneralMetricC2LorentzChartMetric_tensor]
  rfl

theorem pairedInteractionRecenter_zero_mem_lorentzMatrixDomain :
    (0 : RelativeCore period hPeriod newPlus newMinus) ∈
      regularGeneralMetricC2PairedLorentzMatrixDomain period hPeriod newPlus newMinus := by
  refine ⟨⟨zero_mem_regularGeneralMetricC2LorentzChartDomain period hPeriod newPlus,
    zero_mem_regularGeneralMetricC2LorentzChartDomain period hPeriod newMinus⟩,
    zero_mem_regularGeneralMetricC2PairedRelativeMatrixDomain period hPeriod newPlus newMinus, ?_⟩
  change regularGeneralMetricC2PairedRelativeMatrix period hPeriod newPlus newMinus 0 ∈
    regularGeneralMetricC2LorentzChartMatrixDomain period hPeriod newPlus
  rw [pairedInteractionRelativeMatrix_zero,
    recenteredRelativeTensor_eq period hPeriod plusBase minusBase
      plusVariation minusVariation hAdmissible]
  exact (regularGeneralMetricC2LorentzChartDomain_mem_iff_matrixDomain
    period hPeriod newPlus _).mp hAdmissible.relative_mem

local notation "hOld" => pairedInteractionSmoothCore_mem_lorentzMatrixDomain period hPeriod
  configuration plusBase minusBase plusVariation minusVariation hAdmissible
local notation "hNew" => pairedInteractionRecenter_zero_mem_lorentzMatrixDomain period hPeriod
  plusBase minusBase plusVariation minusVariation hAdmissible

attribute [local irreducible] regularGeneralMetricC2PairedRelativeRootDerivative
  c2IdentityRootDerivative regularGeneralMetricC2IdentityRootInverseDerivative

include configuration in
/-- Actual native pointwise spectral derivatives agree on the same two smooth
covariant tests, expressed in the original and reconstructed regular frames. -/
theorem pairedInteractionSpectralDerivative_recenter_valueAt
    (coefficients : PotentialCoefficients)
    (plusTest minusTest : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    matrixSpectralPotentialDerivative coefficients
        (c2FiniteMatrixValueAt period hPeriod 4
          (regularGeneralMetricC2PairedRelativeRoot period hPeriod plusBase minusBase oldPoint) point)
        (c2FiniteMatrixValueAt period hPeriod 4
          (regularGeneralMetricC2PairedRelativeRootDerivative period hPeriod
            plusBase minusBase oldPoint hOld
            (pairedInteractionSmoothCore period hPeriod plusBase minusBase plusTest minusTest)) point) =
      matrixSpectralPotentialDerivative coefficients
        (c2FiniteMatrixValueAt period hPeriod 4
          (regularGeneralMetricC2PairedRelativeRoot period hPeriod newPlus newMinus 0) point)
        (c2FiniteMatrixValueAt period hPeriod 4
          (regularGeneralMetricC2PairedRelativeRootDerivative period hPeriod newPlus newMinus 0 hNew
            (pairedInteractionSmoothCore period hPeriod newPlus newMinus plusTest minusTest)) point) := by
  let ev := fun matrix : C2Matrix period hPeriod => c2FiniteMatrixValueAt period hPeriod 4 matrix point
  let oldDirection := pairedInteractionSmoothCore period hPeriod plusBase minusBase plusTest minusTest
  let newDirection := pairedInteractionSmoothCore period hPeriod newPlus newMinus plusTest minusTest
  let S := ev (c2IdentityRootBranch period hPeriod oldPoint.2.1)
  let T := ev (regularGeneralMetricC2IdentityRootInverseC2Matrix period hPeriod oldPoint.2.1)
  let U := ev (c2IdentityRootDerivative period hPeriod oldPoint.2.1 hOld.2.1.1 oldDirection.2.1)
  let V := ev (regularGeneralMetricC2IdentityRootInverseDerivative period hPeriod
    oldPoint.2.1 hOld.2.1 oldDirection.2.1)
  let K := ev oldDirection.2.1
  let C := ev (regularGeneralMetricC2PairedAffineRelativeMatrix period hPeriod plusBase minusBase oldPoint)
  let dC := ev oldDirection.2.2
  let root := ev (regularGeneralMetricC2PairedRelativeRoot period hPeriod plusBase minusBase oldPoint)
  let oldVelocity := ev (regularGeneralMetricC2PairedRelativeRootDerivative period hPeriod
    plusBase minusBase oldPoint hOld oldDirection)
  let newVelocity := ev (regularGeneralMetricC2PairedRelativeRootDerivative period hPeriod
    newPlus newMinus 0 hNew newDirection)
  have hST : S * T = 1 := by
    have h := congrArg ev (regularGeneralMetricC2IdentityRoot_mul_inverseC2Matrix
      period hPeriod oldPoint.2.1 hOld.2.1)
    simpa only [ev, c2FiniteMatrixValueAt_product, c2FiniteMatrixValueAt_identity] using h
  have hTS : T * S = 1 := by
    have h := congrArg ev (regularGeneralMetricC2IdentityRootInverseC2Matrix_mul
      period hPeriod oldPoint.2.1 hOld.2.1)
    simpa only [ev, c2FiniteMatrixValueAt_product, c2FiniteMatrixValueAt_identity] using h
  have hMetricSylvester : S * U + U * S = K := by
    have h := congrArg ev (c2IdentityRootDerivative_sylvester period hPeriod
      oldPoint.2.1 hOld.2.1.1 oldDirection.2.1)
    simpa only [ev, matrixValue_sylvester] using h
  have hInverse : V = -(T * (U * T)) := by
    have h := congrArg ev (regularGeneralMetricC2IdentityRootInverseDerivative_apply
      period hPeriod oldPoint.2.1 hOld.2.1 oldDirection.2.1)
    simpa only [ev, matrixValue_neg, c2FiniteMatrixValueAt_product] using h
  have hRelative : ev (regularGeneralMetricC2PairedRelativeMatrix
      period hPeriod plusBase minusBase oldPoint) = T * (C * T) := by
    change ev (c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) 4
      (regularGeneralMetricC2IdentityRootInverseC2Matrix period hPeriod oldPoint.2.1)
      (c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) 4
        (regularGeneralMetricC2PairedAffineRelativeMatrix period hPeriod plusBase minusBase oldPoint)
        (regularGeneralMetricC2IdentityRootInverseC2Matrix period hPeriod oldPoint.2.1))) = _
    simp only [ev, c2FiniteMatrixValueAt_product]
    rfl
  have hSquare : root * root = 1 + T * (C * T) := by
    have h := congrArg ev (c2IdentityRootBranch_square period hPeriod hOld.2.2.2.1)
    change ev (c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) 4
      (regularGeneralMetricC2PairedRelativeRoot period hPeriod plusBase minusBase oldPoint)
      (regularGeneralMetricC2PairedRelativeRoot period hPeriod plusBase minusBase oldPoint)) =
      ev (c2FiniteMatrixIdentity period hPeriod 4 +
        regularGeneralMetricC2PairedRelativeMatrix period hPeriod plusBase minusBase oldPoint) at h
    rw [show ev (c2FiniteMatrixIdentity period hPeriod 4 +
        regularGeneralMetricC2PairedRelativeMatrix period hPeriod plusBase minusBase oldPoint) =
      1 + ev (regularGeneralMetricC2PairedRelativeMatrix period hPeriod plusBase minusBase oldPoint) by
        simp only [ev, c2FiniteMatrixValueAt_add, c2FiniteMatrixValueAt_identity], hRelative] at h
    exact (c2FiniteMatrixValueAt_product period hPeriod 4 _ _ point).symm.trans h
  have hRootValue : root = ev (regularGeneralMetricC2PairedRelativeRoot
      period hPeriod newPlus newMinus 0) :=
    congrArg ev (pairedInteractionRelativeRoot_recenter_value period hPeriod configuration
      plusBase minusBase plusVariation minusVariation hAdmissible)
  have hNewRelative : ev (regularGeneralMetricC2VariationMatrix period hPeriod newPlus
      ((newMinus).metric.tensor - (newPlus).metric.tensor)) = T * (C * T) := by
    calc
      _ = ev (regularGeneralMetricC2PairedRelativeMatrix period hPeriod newPlus newMinus 0) :=
        congrArg ev (pairedInteractionRelativeMatrix_zero period hPeriod newPlus newMinus).symm
      _ = ev (regularGeneralMetricC2PairedRelativeMatrix period hPeriod plusBase minusBase oldPoint) :=
        congrArg ev (pairedInteractionRelativeMatrix_recenter_value period hPeriod configuration
          plusBase minusBase plusVariation minusVariation hAdmissible).symm
      _ = _ := hRelative
  have hT : T = regularGeneralMetricC2IdentityRootInverseMatrixAt
      period hPeriod plusBase plusVariation point :=
    regularGeneralMetricC2IdentityRootInverseC2Matrix_valueAt period hPeriod
      plusBase plusVariation hAdmissible.plus_mem point
  have hTest (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
      ev (regularGeneralMetricC2VariationMatrix period hPeriod newPlus tensor) =
        T * (ev (regularGeneralMetricC2VariationMatrix period hPeriod plusBase tensor) * T) := by
    rw [hT]
    exact regularGeneralMetricC2LorentzChartVariationMatrix_valueAt period hPeriod
      plusBase plusVariation tensor hAdmissible.plus_mem point
  have hPlusDirection : ev newDirection.2.1 = T * (K * T) := hTest plusTest
  have hCrossDirection : ev newDirection.2.2 = T * (dC * T) := by
    change ev (regularGeneralMetricC2VariationMatrix period hPeriod newPlus minusTest -
      regularGeneralMetricC2VariationMatrix period hPeriod newPlus plusTest) =
      T * (ev (regularGeneralMetricC2VariationMatrix period hPeriod plusBase minusTest -
        regularGeneralMetricC2VariationMatrix period hPeriod plusBase plusTest) * T)
    simp only [ev, matrixValue_sub]
    change ev (regularGeneralMetricC2VariationMatrix period hPeriod newPlus minusTest) -
      ev (regularGeneralMetricC2VariationMatrix period hPeriod newPlus plusTest) =
      T * ((ev (regularGeneralMetricC2VariationMatrix period hPeriod plusBase minusTest) -
        ev (regularGeneralMetricC2VariationMatrix period hPeriod plusBase plusTest)) * T)
    rw [hTest minusTest, hTest plusTest]
    noncomm_ring
  have hOriginalSylvester : root * oldVelocity + oldVelocity * root =
      matrixPairedOriginalRelativeVelocity T V C dC := by
    have h := congrArg ev (pairedInteractionRelativeRootDerivative_sylvester period hPeriod
      plusBase minusBase oldPoint oldDirection hOld)
    simpa only [ev, matrixValue_sylvester, pairedInteractionRelativeMatrixDerivative_valueAt] using h
  have hCenteredSylvester : root * newVelocity + newVelocity * root =
      matrixPairedRelativeCenterVelocity (T * (C * T)) (T * (K * T)) (T * (dC * T)) := by
    have h := congrArg ev (regularGeneralMetricC2PairedRelativeRootDerivative_zero_sylvester
      period hPeriod newPlus newMinus hNew newDirection)
    have hCenter : ev (pairedInteractionMetricCenterVelocity period hPeriod newPlus newMinus
        newDirection.2.1 newDirection.2.2) =
        matrixPairedRelativeCenterVelocity (T * (C * T)) (T * (K * T)) (T * (dC * T)) := by
      simp only [ev, pairedInteractionMetricCenterVelocity, c2FiniteMatrixValueAt_add,
        c2FiniteMatrixValueAt_product, matrixValue_neg, matrixValue_smul]
      change matrixPairedRelativeCenterVelocity
        (ev (regularGeneralMetricC2VariationMatrix period hPeriod newPlus
          ((newMinus).metric.tensor - (newPlus).metric.tensor)))
        (ev newDirection.2.1) (ev newDirection.2.2) = _
      rw [hNewRelative, hPlusDirection, hCrossDirection]
    rw [hCenter] at h
    rw [hRootValue]
    simpa only [ev, matrixValue_sylvester] using h
  have hNewRootAdmissible : RegularGeneralMetricC2IdentityRootAdmissible period hPeriod newPlus
      ((newMinus).metric.tensor - (newPlus).metric.tensor) := by
    change regularGeneralMetricC2VariationMatrix period hPeriod newPlus
      ((newMinus).metric.tensor - (newPlus).metric.tensor) ∈ c2IdentityRootPerturbationDomain period hPeriod
    rw [← pairedInteractionRelativeMatrix_zero period hPeriod newPlus newMinus]
    exact hNew.2.2.2.1
  have hRootSmoothValue : root = regularGeneralMetricC2IdentityRootMatrixAt
      period hPeriod newPlus ((newMinus).metric.tensor - (newPlus).metric.tensor) point := by
    rw [hRootValue]
    change ev (c2IdentityRootBranch period hPeriod
      (regularGeneralMetricC2PairedRelativeMatrix period hPeriod newPlus newMinus 0)) = _
    rw [pairedInteractionRelativeMatrix_zero]
    rfl
  have hInjective : Function.Injective (fun velocity : Matrix4 => root * velocity + velocity * root) := by
    rw [hRootSmoothValue]
    exact (regularGeneralMetricC2IdentityRootMatrixAt_sylvester_bijective period hPeriod newPlus
      ((newMinus).metric.tensor - (newPlus).metric.tensor) hNewRootAdmissible point).1
  have hSpectral := matrixPairedSpectralDerivative_recenter coefficients
    S T U V K C dC root oldVelocity newVelocity hST hTS hMetricSylvester hInverse hSquare
    hInjective hOriginalSylvester hCenteredSylvester
  exact hSpectral.trans (congrArg (fun currentRoot =>
    matrixSpectralPotentialDerivative coefficients currentRoot newVelocity) hRootValue)

attribute [local irreducible] regularGeneralMetricC2PairedInteractionC2ActionDerivative

include configuration in
/-- Native directional action derivatives agree, including the unchanged
fixed plus-volume, for every finite measure and both genuine metric tests. -/
theorem pairedInteractionC2ActionDerivative_recenter
    (measure : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure measure]
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (plusTest minusTest : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    regularGeneralMetricC2PairedInteractionC2ActionDerivative period hPeriod plusBase minusBase
        measure interactionScale coefficients oldPoint hOld
        (pairedInteractionSmoothCore period hPeriod plusBase minusBase plusTest minusTest) =
      regularGeneralMetricC2PairedInteractionC2ActionDerivative period hPeriod newPlus newMinus
        measure interactionScale coefficients 0 hNew
        (pairedInteractionSmoothCore period hPeriod newPlus newMinus plusTest minusTest) := by
  rw [regularGeneralMetricC2PairedInteractionC2ActionDerivative_apply,
    regularGeneralMetricC2PairedInteractionC2ActionDerivative_apply]
  apply congrArg (fun integrand : EffectiveQuotient period hPeriod → Real => ∫ point, integrand point ∂measure)
  funext point
  rw [pairedInteractionRecenterPlus_volume period hPeriod plusBase minusBase
    plusVariation minusVariation hAdmissible]
  exact congrArg (fun spectral : Real => (-interactionScale) * plusBase.volume point * spectral)
    (pairedInteractionSpectralDerivative_recenter_valueAt period hPeriod configuration
      plusBase minusBase plusVariation minusVariation hAdmissible coefficients plusTest minusTest point)

end Recenter
end
end P0EFTJanusPairedInteractionDerivativeRecenter4D
end JanusFormal
