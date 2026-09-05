import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedRelativeMatrixDerivative4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2MatrixSpectralPotential4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatrixInteractionFrechetNoether

/-! # Pointwise-explicit derivative of the C² spectral potential -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2MatrixSpectralPotentialDerivative4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open Set Filter
open scoped Manifold ContDiff Matrix.Norms.Frobenius
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2MatrixSpectralPotential4D
open P0EFTJanusMatrixSquareRootInteractionDensity
open P0EFTJanusMatrixInteractionFrechetNoether
open P0EFTJanusReciprocalBimetricPotential

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

private abbrev C2Matrix :=
  C2FiniteMatrix period hPeriod 4

private abbrev Matrix4 :=
  P0EFTJanusMatrixSquareRootInteractionDensity.Matrix4

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

@[reducible] local instance c2ScalarNormedAddCommGroup :
    NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule
    period hPeriod).normedAddCommGroup

@[reducible] local instance c2ScalarNormedSpace :
    NormedSpace Real (C2Scalar period hPeriod) :=
  inferInstance

local instance c2ScalarCompleteSpace :
    CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

@[reducible] local instance canonicalMatrixNormedAddCommGroup :
    NormedAddCommGroup Matrix4 :=
  Matrix.frobeniusNormedAddCommGroup

@[reducible] local instance canonicalMatrixNormedSpace :
    NormedSpace Real Matrix4 :=
  Matrix.frobeniusNormedSpace

local instance canonicalMatrixCompleteSpace : CompleteSpace Matrix4 :=
  FiniteDimensional.complete Real Matrix4

/-- Continuous evaluation of a completed scalar C² jet at one point. -/
def c2ScalarValueAtCLM
    (point : EffectiveQuotient period hPeriod) :
    C2Scalar period hPeriod →L[Real] Real :=
  (ContinuousMap.evalCLM Real point).comp
    (canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod)

@[simp]
theorem c2ScalarValueAtCLM_apply
    (point : EffectiveQuotient period hPeriod)
    (field : C2Scalar period hPeriod) :
    c2ScalarValueAtCLM period hPeriod point field =
      canonicalPhysicalScalarC2JetCoreToContinuous
        period hPeriod field point :=
  rfl

/-- Continuous point evaluation of a completed C² matrix. -/
def c2FiniteMatrixValueAtCLM
    (point : EffectiveQuotient period hPeriod) :
    C2Matrix period hPeriod →L[Real] Matrix4 :=
  ContinuousLinearMap.pi fun row =>
    ContinuousLinearMap.pi fun column =>
      (c2ScalarValueAtCLM period hPeriod point).comp
        ((ContinuousLinearMap.proj column :
            (Fin 4 → C2Scalar period hPeriod) →L[Real]
              C2Scalar period hPeriod).comp
          (ContinuousLinearMap.proj row :
            C2Matrix period hPeriod →L[Real]
              (Fin 4 → C2Scalar period hPeriod)))

@[simp]
theorem c2FiniteMatrixValueAtCLM_apply
    (point : EffectiveQuotient period hPeriod)
    (matrix : C2Matrix period hPeriod) :
    c2FiniteMatrixValueAtCLM period hPeriod point matrix =
      c2FiniteMatrixValueAt period hPeriod 4 matrix point :=
  rfl

/-- The genuine Fréchet derivative in the completed scalar C² core. -/
def c2MatrixSpectralPotentialDerivative
    (coefficients : PotentialCoefficients)
    (root : C2Matrix period hPeriod) :
    C2Matrix period hPeriod →L[Real] C2Scalar period hPeriod :=
  fderiv Real
    (c2MatrixSpectralPotential period hPeriod coefficients) root

theorem c2MatrixSpectralPotential_hasFDerivAt
    (coefficients : PotentialCoefficients)
    (root : C2Matrix period hPeriod) :
    HasFDerivAt
      (c2MatrixSpectralPotential period hPeriod coefficients)
      (c2MatrixSpectralPotentialDerivative
        period hPeriod coefficients root) root := by
  exact ((c2MatrixSpectralPotential_contDiff period hPeriod coefficients)
    |>.differentiable (by simp)).differentiableAt.hasFDerivAt

/-- Every spacetime value of the C² derivative is the already explicit
finite-matrix spectral covector. -/
theorem c2MatrixSpectralPotentialDerivative_valueAt
    (coefficients : PotentialCoefficients)
    (root direction : C2Matrix period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
        (c2MatrixSpectralPotentialDerivative
          period hPeriod coefficients root direction) point =
      matrixSpectralPotentialDerivative coefficients
        (c2FiniteMatrixValueAt period hPeriod 4 root point)
        (c2FiniteMatrixValueAt period hPeriod 4 direction point) := by
  let scalarEval := c2ScalarValueAtCLM period hPeriod point
  let matrixEval := c2FiniteMatrixValueAtCLM period hPeriod point
  let derivative := c2MatrixSpectralPotentialDerivative
    period hPeriod coefficients root
  have hC2 := c2MatrixSpectralPotential_hasFDerivAt
    period hPeriod coefficients root
  have hLeft := HasFDerivAt.comp
    (f := c2MatrixSpectralPotential period hPeriod coefficients)
    (g := fun field => scalarEval field) root
    scalarEval.hasFDerivAt hC2
  have hFinite : HasFDerivAt
      (matrixSpectralPotential coefficients)
      (matrixSpectralPotentialDerivative coefficients (matrixEval root))
      (matrixEval root) := by
    exact matrixSpectralPotential_hasFDerivAt coefficients (matrixEval root)
  have hRight := HasFDerivAt.comp
    (f := fun current => matrixEval current)
    (g := matrixSpectralPotential coefficients) root
    hFinite matrixEval.hasFDerivAt
  have hLeftOnRight : HasFDerivAt
      (matrixSpectralPotential coefficients ∘ fun current => matrixEval current)
      (scalarEval.comp derivative) root := by
    apply hLeft.congr_of_eventuallyEq
    filter_upwards [] with current
    exact (c2MatrixSpectralPotential_valueAt
      period hPeriod coefficients current point).symm
  have hDerivative := hLeftOnRight.unique hRight
  have hApplied := congrArg
    (fun linear : C2Matrix period hPeriod →L[Real] Real =>
      linear direction) hDerivative
  change canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
      (c2MatrixSpectralPotentialDerivative
        period hPeriod coefficients root direction) point =
    matrixSpectralPotentialDerivative coefficients
      (c2FiniteMatrixValueAt period hPeriod 4 root point)
      (c2FiniteMatrixValueAt period hPeriod 4 direction point) at hApplied
  exact hApplied

/-- Gate marker: the smooth C² polynomial has a genuine derivative whose
pointwise value is the explicit finite-matrix covector. -/
theorem regular_general_metric_c2_matrix_spectral_potential_derivative_gate
    (coefficients : PotentialCoefficients)
    (root : C2Matrix period hPeriod) :
    HasFDerivAt
        (c2MatrixSpectralPotential period hPeriod coefficients)
        (c2MatrixSpectralPotentialDerivative
          period hPeriod coefficients root) root ∧
      ∀ (direction : C2Matrix period hPeriod)
        (point : EffectiveQuotient period hPeriod),
        canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
            (c2MatrixSpectralPotentialDerivative
              period hPeriod coefficients root direction) point =
          matrixSpectralPotentialDerivative coefficients
            (c2FiniteMatrixValueAt period hPeriod 4 root point)
            (c2FiniteMatrixValueAt period hPeriod 4 direction point) :=
  ⟨c2MatrixSpectralPotential_hasFDerivAt
      period hPeriod coefficients root,
    c2MatrixSpectralPotentialDerivative_valueAt
      period hPeriod coefficients root⟩

end
end P0EFTJanusProgramPRegularGeneralMetricC2MatrixSpectralPotentialDerivative4D
end JanusFormal
