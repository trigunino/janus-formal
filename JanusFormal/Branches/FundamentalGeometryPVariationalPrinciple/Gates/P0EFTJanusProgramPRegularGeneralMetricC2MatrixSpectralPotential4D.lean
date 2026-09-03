import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomainOpen4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixDeterminant4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatrixSquareRootInteractionDensity

/-!
# C² matrix spectral potential

The polynomial Candidate-A matrix potential is lifted from real matrices to
the completed scalar C² algebra.  Its value projection is the original
pointwise potential, and the lift is smooth on the whole matrix core.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2MatrixSpectralPotential4D

set_option autoImplicit false
set_option maxHeartbeats 2400000

noncomputable section

open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2LocalRoot4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixDeterminant4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusMatrixSquareRootInteractionDensity
open P0EFTJanusReciprocalBimetricPotential

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

private abbrev C2Matrix :=
  C2FiniteMatrix period hPeriod 4

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

local instance c2ScalarNormedAddCommGroup :
    NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule
    period hPeriod).normedAddCommGroup

local instance c2ScalarNormedSpace :
    NormedSpace Real (C2Scalar period hPeriod) :=
  inferInstance

local instance c2ScalarCompleteSpace :
    CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

local instance c2ScalarCommMonoid : CommMonoid (C2Scalar period hPeriod) where
  mul := fun first second =>
    canonicalPhysicalScalarC2JetCoreProduct period hPeriod first second
  one := c2ScalarOne period hPeriod
  mul_assoc := c2ScalarProduct_assoc period hPeriod
  one_mul := c2ScalarOne_mul period hPeriod
  mul_one := c2Scalar_mul_one period hPeriod
  mul_comm := c2ScalarProduct_comm period hPeriod

private def c2ScalarValueAtLinearMap
    (point : EffectiveQuotient period hPeriod) :
    C2Scalar period hPeriod →ₗ[Real] Real where
  toFun field :=
    canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod field point
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def c2ScalarValueAtMonoidHom
    (point : EffectiveQuotient period hPeriod) :
    C2Scalar period hPeriod →* Real where
  toFun field :=
    canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod field point
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem c2ScalarProduct_valueAt
    (first second : C2Scalar period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
        (canonicalPhysicalScalarC2JetCoreProduct period hPeriod first second)
        point =
      canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod first point *
        canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod second
          point :=
  rfl

@[simp]
theorem c2ScalarAdd_valueAt
    (first second : C2Scalar period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
        (first + second) point =
      canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod first point +
        canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod second
          point :=
  rfl

@[simp]
theorem c2ScalarSub_valueAt
    (first second : C2Scalar period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
        (first - second) point =
      canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod first point -
        canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod second
          point :=
  rfl

@[simp]
theorem c2ScalarSmul_valueAt
    (scalar : Real) (field : C2Scalar period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
        (scalar • field) point =
      scalar * canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
        field point :=
  rfl

/-- Trace in the completed C² scalar algebra. -/
def c2FiniteMatrixTrace (matrix : C2Matrix period hPeriod) :
    C2Scalar period hPeriod :=
  ∑ index : Fin 4, matrix index index

/-- Newton's first five elementary matrix invariants in the C² algebra. -/
def c2MatrixElementary0 (_root : C2Matrix period hPeriod) :
    C2Scalar period hPeriod :=
  c2ScalarOne period hPeriod

def c2MatrixElementary1 (root : C2Matrix period hPeriod) :
    C2Scalar period hPeriod :=
  c2FiniteMatrixTrace period hPeriod root

def c2MatrixElementary2 (root : C2Matrix period hPeriod) :
    C2Scalar period hPeriod :=
  let trace := c2FiniteMatrixTrace period hPeriod root
  let square := c2FiniteMatrixProduct
    (period := period) (hPeriod := hPeriod) 4 root root
  (1 / 2 : Real) •
    (canonicalPhysicalScalarC2JetCoreProduct period hPeriod trace trace -
      c2FiniteMatrixTrace period hPeriod square)

def c2MatrixElementary3 (root : C2Matrix period hPeriod) :
    C2Scalar period hPeriod :=
  let trace := c2FiniteMatrixTrace period hPeriod root
  let square := c2FiniteMatrixProduct
    (period := period) (hPeriod := hPeriod) 4 root root
  let cube := c2FiniteMatrixProduct
    (period := period) (hPeriod := hPeriod) 4 square root
  (1 / 6 : Real) •
    (canonicalPhysicalScalarC2JetCoreProduct period hPeriod
        (canonicalPhysicalScalarC2JetCoreProduct period hPeriod trace trace)
        trace -
      (3 : Real) • canonicalPhysicalScalarC2JetCoreProduct period hPeriod trace
        (c2FiniteMatrixTrace period hPeriod square) +
      (2 : Real) • c2FiniteMatrixTrace period hPeriod cube)

def c2MatrixElementary4 (root : C2Matrix period hPeriod) :
    C2Scalar period hPeriod :=
  c2FiniteMatrixDeterminant period hPeriod 4 root

/-- Candidate-A spectral potential valued in the completed scalar C² core. -/
def c2MatrixSpectralPotential
    (coefficients : PotentialCoefficients)
    (root : C2Matrix period hPeriod) : C2Scalar period hPeriod :=
  coefficients.beta0 • c2MatrixElementary0 period hPeriod root +
    coefficients.beta1 • c2MatrixElementary1 period hPeriod root +
    coefficients.beta2 • c2MatrixElementary2 period hPeriod root +
    coefficients.beta3 • c2MatrixElementary3 period hPeriod root +
    coefficients.beta4 • c2MatrixElementary4 period hPeriod root

@[simp]
theorem c2FiniteMatrixTrace_valueAt
    (matrix : C2Matrix period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
        (c2FiniteMatrixTrace period hPeriod matrix) point =
      Matrix.trace
        (c2FiniteMatrixValueAt period hPeriod 4 matrix point) := by
  change c2ScalarValueAtLinearMap period hPeriod point
      (∑ index : Fin 4, matrix index index) =
    ∑ index : Fin 4,
      c2ScalarValueAtLinearMap period hPeriod point (matrix index index)
  exact map_sum (c2ScalarValueAtLinearMap period hPeriod point) _ _

@[simp]
theorem c2FiniteMatrixDeterminant_valueAt
    (matrix : C2Matrix period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
        (c2FiniteMatrixDeterminant period hPeriod 4 matrix) point =
      Matrix.det
        (c2FiniteMatrixValueAt period hPeriod 4 matrix point) := by
  rw [Matrix.det_apply']
  unfold c2FiniteMatrixDeterminant
  change c2ScalarValueAtLinearMap period hPeriod point
      (∑ permutation : Equiv.Perm (Fin 4),
        _ • ∏ index : Fin 4, matrix (permutation index) index) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro permutation _
  rw [map_smul]
  change _ * c2ScalarValueAtMonoidHom period hPeriod point
      (∏ index : Fin 4, matrix (permutation index) index) =
    _ * ∏ index : Fin 4,
      c2ScalarValueAtMonoidHom period hPeriod point
        (matrix (permutation index) index)
  rw [map_prod]
  rfl

@[simp]
theorem c2MatrixElementary0_valueAt
    (root : C2Matrix period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
        (c2MatrixElementary0 period hPeriod root) point =
      matrixElementary0
        (c2FiniteMatrixValueAt period hPeriod 4 root point) :=
  rfl

@[simp]
theorem c2MatrixElementary1_valueAt
    (root : C2Matrix period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
        (c2MatrixElementary1 period hPeriod root) point =
      matrixElementary1
        (c2FiniteMatrixValueAt period hPeriod 4 root point) := by
  unfold c2MatrixElementary1 matrixElementary1
  exact c2FiniteMatrixTrace_valueAt period hPeriod root point

@[simp]
theorem c2MatrixElementary2_valueAt
    (root : C2Matrix period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
        (c2MatrixElementary2 period hPeriod root) point =
      matrixElementary2
        (c2FiniteMatrixValueAt period hPeriod 4 root point) := by
  unfold c2MatrixElementary2 matrixElementary2
  simp only [c2ScalarSmul_valueAt, c2ScalarSub_valueAt,
    c2ScalarProduct_valueAt]
  simp_rw [c2FiniteMatrixTrace_valueAt]
  simp only [c2FiniteMatrixValueAt_product]
  ring

@[simp]
theorem c2MatrixElementary3_valueAt
    (root : C2Matrix period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
        (c2MatrixElementary3 period hPeriod root) point =
      matrixElementary3
        (c2FiniteMatrixValueAt period hPeriod 4 root point) := by
  unfold c2MatrixElementary3 matrixElementary3
  simp only [c2ScalarSmul_valueAt, c2ScalarSub_valueAt,
    c2ScalarAdd_valueAt, c2ScalarProduct_valueAt]
  simp_rw [c2FiniteMatrixTrace_valueAt]
  simp only [c2FiniteMatrixValueAt_product]
  ring

@[simp]
theorem c2MatrixElementary4_valueAt
    (root : C2Matrix period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
        (c2MatrixElementary4 period hPeriod root) point =
      matrixElementary4
        (c2FiniteMatrixValueAt period hPeriod 4 root point) := by
  unfold c2MatrixElementary4 matrixElementary4
  exact c2FiniteMatrixDeterminant_valueAt period hPeriod root point

/-- The C² lift evaluates to the original real matrix potential at every
spacetime point. -/
@[simp]
theorem c2MatrixSpectralPotential_valueAt
    (coefficients : PotentialCoefficients)
    (root : C2Matrix period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
        (c2MatrixSpectralPotential period hPeriod coefficients root) point =
      matrixSpectralPotential coefficients
        (c2FiniteMatrixValueAt period hPeriod 4 root point) := by
  unfold c2MatrixSpectralPotential matrixSpectralPotential
  change coefficients.beta0 *
          canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
            (c2MatrixElementary0 period hPeriod root) point +
        coefficients.beta1 *
          canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
            (c2MatrixElementary1 period hPeriod root) point +
      coefficients.beta2 *
        canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
          (c2MatrixElementary2 period hPeriod root) point +
    coefficients.beta3 *
        canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
          (c2MatrixElementary3 period hPeriod root) point +
      coefficients.beta4 *
        canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
          (c2MatrixElementary4 period hPeriod root) point = _
  rw [c2MatrixElementary0_valueAt, c2MatrixElementary1_valueAt,
    c2MatrixElementary2_valueAt, c2MatrixElementary3_valueAt,
    c2MatrixElementary4_valueAt]

private theorem c2FiniteMatrixTrace_contDiff :
    ContDiff Real ∞ (c2FiniteMatrixTrace period hPeriod) := by
  unfold c2FiniteMatrixTrace
  apply ContDiff.sum
  intro index _
  exact contDiff_apply_apply Real (C2Scalar period hPeriod) index index

private theorem c2MatrixElementary0_contDiff :
    ContDiff Real ∞ (c2MatrixElementary0 period hPeriod) :=
  contDiff_const

private theorem c2MatrixElementary1_contDiff :
    ContDiff Real ∞ (c2MatrixElementary1 period hPeriod) := by
  exact c2FiniteMatrixTrace_contDiff period hPeriod

private theorem c2MatrixElementary2_contDiff :
    ContDiff Real ∞ (c2MatrixElementary2 period hPeriod) := by
  have hTrace := c2FiniteMatrixTrace_contDiff period hPeriod
  have hSquare := c2FiniteMatrixSquare_contDiff period hPeriod 4
  have hTraceSquare := hTrace.comp hSquare
  have hTraceTwo :=
    ((canonicalPhysicalScalarC2JetCoreProduct
      period hPeriod).contDiff.comp hTrace).clm_apply hTrace
  unfold c2MatrixElementary2
  simpa only [Function.comp_apply, c2FiniteMatrixSquare] using
    (hTraceTwo.sub hTraceSquare).const_smul (1 / 2 : Real)

private theorem c2MatrixElementary3_contDiff :
    ContDiff Real ∞ (c2MatrixElementary3 period hPeriod) := by
  have hTrace := c2FiniteMatrixTrace_contDiff period hPeriod
  have hSquare := c2FiniteMatrixSquare_contDiff period hPeriod 4
  have hCube : ContDiff Real ∞
      (fun root : C2Matrix period hPeriod =>
        c2FiniteMatrixProduct
          (period := period) (hPeriod := hPeriod) 4
          (c2FiniteMatrixProduct
            (period := period) (hPeriod := hPeriod) 4 root root) root) :=
    ((c2FiniteMatrixProduct
      (period := period) (hPeriod := hPeriod) 4).contDiff.comp
        hSquare).clm_apply contDiff_id
  have hTraceSquare := hTrace.comp hSquare
  have hTraceCube := hTrace.comp hCube
  have hTraceTwo :=
    ((canonicalPhysicalScalarC2JetCoreProduct
      period hPeriod).contDiff.comp hTrace).clm_apply hTrace
  have hTraceThree :=
    ((canonicalPhysicalScalarC2JetCoreProduct
      period hPeriod).contDiff.comp hTraceTwo).clm_apply hTrace
  have hTraceTraceSquare :=
    ((canonicalPhysicalScalarC2JetCoreProduct
      period hPeriod).contDiff.comp hTrace).clm_apply hTraceSquare
  unfold c2MatrixElementary3
  simpa only [Function.comp_apply, c2FiniteMatrixSquare] using
    (((hTraceThree.sub (hTraceTraceSquare.const_smul 3)).add
      (hTraceCube.const_smul 2)).const_smul (1 / 6 : Real))

private theorem c2MatrixElementary4_contDiff :
    ContDiff Real ∞ (c2MatrixElementary4 period hPeriod) := by
  exact c2FiniteMatrixDeterminant_contDiff period hPeriod 4

/-- The lifted spectral potential is a smooth polynomial on the full C²
matrix space. -/
theorem c2MatrixSpectralPotential_contDiff
    (coefficients : PotentialCoefficients) :
    ContDiff Real ∞
      (c2MatrixSpectralPotential period hPeriod coefficients) := by
  unfold c2MatrixSpectralPotential
  have h0 := (c2MatrixElementary0_contDiff period hPeriod).const_smul
    coefficients.beta0
  have h1 := (c2MatrixElementary1_contDiff period hPeriod).const_smul
    coefficients.beta1
  have h2 := (c2MatrixElementary2_contDiff period hPeriod).const_smul
    coefficients.beta2
  have h3 := (c2MatrixElementary3_contDiff period hPeriod).const_smul
    coefficients.beta3
  have h4 := (c2MatrixElementary4_contDiff period hPeriod).const_smul
    coefficients.beta4
  exact (((h0.add h1).add h2).add h3).add h4

/-- Gate marker: the exact matrix potential now has a global smooth lift to
the completed C² scalar algebra. -/
theorem regular_general_metric_c2_matrix_spectral_potential_gate
    (coefficients : PotentialCoefficients) :
    ContDiff Real 2
      (c2MatrixSpectralPotential period hPeriod coefficients) :=
  (c2MatrixSpectralPotential_contDiff period hPeriod coefficients).of_le
    (by exact WithTop.coe_le_coe.mpr le_top)

end

end P0EFTJanusProgramPRegularGeneralMetricC2MatrixSpectralPotential4D
end JanusFormal
