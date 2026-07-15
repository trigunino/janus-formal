import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Matrix.Normed
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatrixDiagonalGaugeNoether
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatrixSquareRootFrechetSylvester

/-!
Exact pointwise Frechet derivative of the matrix interaction.

The determinant contribution is differentiated directly from the finite
Leibniz polynomial.  The resulting covector is then inserted into the
finite-matrix Noether pairing.  Nothing here is a spacetime Bianchi identity.
-/

namespace JanusFormal
namespace P0EFTJanusMatrixInteractionFrechetNoether

set_option autoImplicit false

noncomputable section

open Matrix
open scoped Matrix.Norms.Frobenius RightActions
open P0EFTJanusReciprocalBimetricPotential
open P0EFTJanusMatrixSquareRootInteractionDensity
open P0EFTJanusMatrixSquareRootFrechetSylvester
open P0EFTJanusMatrixDiagonalGaugeNoether

abbrev Matrix4 :=
  P0EFTJanusMatrixSquareRootInteractionDensity.Matrix4

/-- `HasFDerivAt` with the same Frobenius/topological-vector-space
instances used by the matrix square-root and frame-orbit gates. -/
def FrobeniusHasFDerivAt
    (f : Matrix4 → ℝ) (derivative : Matrix4 →L[ℝ] ℝ)
    (root : Matrix4) : Prop :=
  @HasFDerivAt ℝ DenselyNormedField.toNontriviallyNormedField Matrix4
    Matrix.frobeniusNormedAddCommGroup.toAddCommGroup
    Matrix.frobeniusNormedSpace.toModule
    Matrix.frobeniusNormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    ℝ Real.normedAddCommGroup.toAddCommGroup
    (RCLike.toInnerProductSpaceReal : InnerProductSpace ℝ ℝ).toModule
    Real.normedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    f derivative root

/-- Matrix-valued version of the same fixed Frobenius derivative predicate. -/
def FrobeniusMatrixHasFDerivAt
    (f : Matrix4 → Matrix4) (derivative : Matrix4 →L[ℝ] Matrix4)
    (root : Matrix4) : Prop :=
  @HasFDerivAt ℝ DenselyNormedField.toNontriviallyNormedField Matrix4
    Matrix.frobeniusNormedAddCommGroup.toAddCommGroup
    Matrix.frobeniusNormedSpace.toModule
    Matrix.frobeniusNormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    Matrix4 Matrix.frobeniusNormedAddCommGroup.toAddCommGroup
    Matrix.frobeniusNormedSpace.toModule
    Matrix.frobeniusNormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    f derivative root

/-- Matrix trace as a continuous linear covector. -/
def traceCovector : Matrix4 →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin 4) ℝ ℝ)

@[simp]
theorem traceCovector_apply (variation : Matrix4) :
    traceCovector variation = Matrix.trace variation := by
  rfl

/-- Entry evaluation as a continuous linear covector. -/
def entryCovector (row column : Fin 4) : Matrix4 →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun variation : Matrix4 => variation row column
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

@[simp]
theorem entryCovector_apply (row column : Fin 4) (variation : Matrix4) :
    entryCovector row column variation = variation row column := by
  rfl

/-- Differential of one Leibniz monomial of the determinant. -/
def determinantMonomialDerivative
    (root : Matrix4) (σ : Equiv.Perm (Fin 4)) : Matrix4 →L[ℝ] ℝ :=
  (root (σ 1) 1 * root (σ 2) 2 * root (σ 3) 3) •
      entryCovector (σ 0) 0 +
    (root (σ 0) 0 * root (σ 2) 2 * root (σ 3) 3) •
      entryCovector (σ 1) 1 +
    (root (σ 0) 0 * root (σ 1) 1 * root (σ 3) 3) •
      entryCovector (σ 2) 2 +
    (root (σ 0) 0 * root (σ 1) 1 * root (σ 2) 2) •
      entryCovector (σ 3) 3

/-- Exact polynomial differential of the determinant, valid also at singular
matrices (so no inverse or adjugate hypothesis is hidden). -/
def determinantDerivative (root : Matrix4) : Matrix4 →L[ℝ] ℝ :=
  ∑ σ : Equiv.Perm (Fin 4),
    ((Equiv.Perm.sign σ : ℤ) : ℝ) •
      determinantMonomialDerivative root σ

@[simp]
theorem determinantMonomialDerivative_apply
    (root variation : Matrix4) (σ : Equiv.Perm (Fin 4)) :
    determinantMonomialDerivative root σ variation =
      root (σ 1) 1 * root (σ 2) 2 * root (σ 3) 3 * variation (σ 0) 0 +
        root (σ 0) 0 * root (σ 2) 2 * root (σ 3) 3 * variation (σ 1) 1 +
        root (σ 0) 0 * root (σ 1) 1 * root (σ 3) 3 * variation (σ 2) 2 +
        root (σ 0) 0 * root (σ 1) 1 * root (σ 2) 2 * variation (σ 3) 3 := by
  simp [determinantMonomialDerivative]

@[simp]
theorem determinantDerivative_apply (root variation : Matrix4) :
    determinantDerivative root variation =
      ∑ σ : Equiv.Perm (Fin 4),
        ((Equiv.Perm.sign σ : ℤ) : ℝ) *
          (root (σ 1) 1 * root (σ 2) 2 * root (σ 3) 3 * variation (σ 0) 0 +
            root (σ 0) 0 * root (σ 2) 2 * root (σ 3) 3 * variation (σ 1) 1 +
            root (σ 0) 0 * root (σ 1) 1 * root (σ 3) 3 * variation (σ 2) 2 +
            root (σ 0) 0 * root (σ 1) 1 * root (σ 2) 2 * variation (σ 3) 3) := by
  simp [determinantDerivative]

/-- The Leibniz polynomial has the stated global Frechet derivative. -/
theorem determinant_hasFDerivAt (root : Matrix4) :
    FrobeniusHasFDerivAt Matrix.det (determinantDerivative root) root := by
  unfold FrobeniusHasFDerivAt
  have hSum : HasFDerivAt
      (fun point : Matrix4 =>
        ∑ σ : Equiv.Perm (Fin 4),
          ((Equiv.Perm.sign σ : ℤ) : ℝ) *
            ∏ i : Fin 4, point (σ i) i)
      (determinantDerivative root) root := by
    refine (HasFDerivAt.fun_sum (u := Finset.univ)
      (A' := fun σ =>
        ((Equiv.Perm.sign σ : ℤ) : ℝ) •
          determinantMonomialDerivative root σ)
      fun (σ : Equiv.Perm (Fin 4)) _ => ?_).congr_fderiv ?_
    · have h0 := (entryCovector (σ 0) 0).hasFDerivAt (x := root)
      have h1 := (entryCovector (σ 1) 1).hasFDerivAt (x := root)
      have h2 := (entryCovector (σ 2) 2).hasFDerivAt (x := root)
      have h3 := (entryCovector (σ 3) 3).hasFDerivAt (x := root)
      have hRaw := ((h0.mul h1).mul h2).mul h3
      let rawDerivative :=
        (entryCovector (σ 0) 0 root * entryCovector (σ 1) 1 root *
            entryCovector (σ 2) 2 root) • entryCovector (σ 3) 3 +
          entryCovector (σ 3) 3 root •
            ((entryCovector (σ 0) 0 root * entryCovector (σ 1) 1 root) •
                entryCovector (σ 2) 2 +
              entryCovector (σ 2) 2 root •
                (entryCovector (σ 0) 0 root • entryCovector (σ 1) 1 +
                  entryCovector (σ 1) 1 root • entryCovector (σ 0) 0))
      have hFunction : Filter.EventuallyEq (nhds root)
          (fun point : Matrix4 => ∏ i : Fin 4, point (σ i) i)
            (fun point : Matrix4 =>
              entryCovector (σ 0) 0 point * entryCovector (σ 1) 1 point *
                entryCovector (σ 2) 2 point * entryCovector (σ 3) 3 point) :=
        Filter.Eventually.of_forall fun point => by
          simp [Fin.prod_univ_four]
      have hProduct := hRaw.congr_of_eventuallyEq hFunction
      have hDerivative : rawDerivative = determinantMonomialDerivative root σ := by
        ext variation
        simp [rawDerivative, determinantMonomialDerivative]
        ring
      exact (hProduct.congr_fderiv hDerivative).const_mul
        (((Equiv.Perm.sign σ : ℤ) : ℝ))
    · rfl
  rw [show Matrix.det = fun point : Matrix4 =>
      ∑ σ : Equiv.Perm (Fin 4),
        ((Equiv.Perm.sign σ : ℤ) : ℝ) *
          ∏ i : Fin 4, point (σ i) i by
    funext point
    exact Matrix.det_apply' point]
  exact hSum

/-- Differential of `X ↦ tr(X²)`. -/
def traceSquareDerivative (root : Matrix4) : Matrix4 →L[ℝ] ℝ :=
  traceCovector.comp (sylvesterOperator root)

@[simp]
theorem traceSquareDerivative_apply (root variation : Matrix4) :
    traceSquareDerivative root variation =
      Matrix.trace (root * variation + variation * root) := by
  rfl

theorem traceSquare_hasFDerivAt (root : Matrix4) :
    FrobeniusHasFDerivAt (fun point : Matrix4 => Matrix.trace (point * point))
      (traceSquareDerivative root) root := by
  unfold FrobeniusHasFDerivAt
  have hRaw := traceCovector.hasFDerivAt.comp root
    (squareMap_hasFDerivAt root)
  have hFunction : Filter.EventuallyEq (nhds root)
      (fun point : Matrix4 => Matrix.trace (point * point))
      (fun point => traceCovector (squareMap point)) :=
    Filter.Eventually.of_forall fun point => by rfl
  exact hRaw.congr_of_eventuallyEq hFunction

/-- Differential of the cubic matrix map `X ↦ X³`. -/
def cubeMatrixDerivative (root : Matrix4) : Matrix4 →L[ℝ] Matrix4 :=
  (root * root) • (ContinuousLinearMap.id ℝ Matrix4) +
    sylvesterOperator root <• root

@[simp]
theorem cubeMatrixDerivative_apply (root variation : Matrix4) :
    cubeMatrixDerivative root variation =
      (root * variation + variation * root) * root +
        (root * root) * variation := by
  simp [cubeMatrixDerivative]
  noncomm_ring

theorem cubeMap_hasFDerivAt (root : Matrix4) :
    FrobeniusMatrixHasFDerivAt (fun point : Matrix4 => point * point * point)
      (cubeMatrixDerivative root) root := by
  unfold FrobeniusMatrixHasFDerivAt
  have hRaw := (squareMap_hasFDerivAt root).mul'
    ((ContinuousLinearMap.id ℝ Matrix4).hasFDerivAt)
  refine hRaw.congr_fderiv ?_
  ext variation
  rfl

/-- Differential of `X ↦ tr(X³)`. -/
def traceCubeDerivative (root : Matrix4) : Matrix4 →L[ℝ] ℝ :=
  traceCovector.comp (cubeMatrixDerivative root)

@[simp]
theorem traceCubeDerivative_apply (root variation : Matrix4) :
    traceCubeDerivative root variation =
      Matrix.trace
        ((root * variation + variation * root) * root +
          (root * root) * variation) := by
  simp [traceCubeDerivative]

theorem traceCube_hasFDerivAt (root : Matrix4) :
    FrobeniusHasFDerivAt (fun point : Matrix4 =>
      Matrix.trace (point * point * point))
      (traceCubeDerivative root) root := by
  unfold FrobeniusHasFDerivAt
  have hRaw := traceCovector.hasFDerivAt.comp root
    (cubeMap_hasFDerivAt root)
  have hFunction : Filter.EventuallyEq (nhds root)
      (fun point : Matrix4 => Matrix.trace (point * point * point))
      (fun point => traceCovector (point * point * point)) :=
    Filter.Eventually.of_forall fun point => by rfl
  exact hRaw.congr_of_eventuallyEq hFunction

/-- Exact Newton-invariant differential of `e₂`. -/
def matrixElementary2Derivative (root : Matrix4) : Matrix4 →L[ℝ] ℝ :=
  (2 : ℝ)⁻¹ •
    (Matrix.trace root • traceCovector +
      Matrix.trace root • traceCovector - traceSquareDerivative root)

@[simp]
theorem matrixElementary2Derivative_apply (root variation : Matrix4) :
    matrixElementary2Derivative root variation =
      (2 * Matrix.trace root * Matrix.trace variation -
        Matrix.trace (root * variation + variation * root)) / 2 := by
  simp [matrixElementary2Derivative, div_eq_mul_inv]
  ring

theorem matrixElementary2_hasFDerivAt (root : Matrix4) :
    FrobeniusHasFDerivAt matrixElementary2
      (matrixElementary2Derivative root) root := by
  unfold FrobeniusHasFDerivAt
  have hTrace := traceCovector.hasFDerivAt (x := root)
  have hSquare := traceSquare_hasFDerivAt root
  have hRaw := ((hTrace.mul hTrace).sub hSquare).const_mul ((2 : ℝ)⁻¹)
  have hFunction : Filter.EventuallyEq (nhds root)
      matrixElementary2
      (fun point : Matrix4 => (2 : ℝ)⁻¹ *
        (Matrix.trace point * Matrix.trace point -
          Matrix.trace (point * point))) :=
    Filter.Eventually.of_forall fun point => by
      simp [matrixElementary2, div_eq_mul_inv]
      ring
  have hRewritten := hRaw.congr_of_eventuallyEq hFunction
  refine hRewritten.congr_fderiv ?_
  rfl

/-- Exact Newton-invariant differential of `e₃`. -/
def matrixElementary3Derivative (root : Matrix4) : Matrix4 →L[ℝ] ℝ :=
  (6 : ℝ)⁻¹ •
    (((3 : ℕ) • (Matrix.trace root) ^ (3 - 1)) • traceCovector -
      (3 : ℝ) •
        (Matrix.trace root • traceSquareDerivative root +
          Matrix.trace (root * root) • traceCovector) +
      (2 : ℝ) • traceCubeDerivative root)

@[simp]
theorem matrixElementary3Derivative_apply (root variation : Matrix4) :
    matrixElementary3Derivative root variation =
      (3 * (Matrix.trace root) ^ 2 * Matrix.trace variation -
        3 *
          (Matrix.trace (root * root) * Matrix.trace variation +
            Matrix.trace root *
              Matrix.trace (root * variation + variation * root)) +
        2 * Matrix.trace
          ((root * variation + variation * root) * root +
            (root * root) * variation)) / 6 := by
  simp [matrixElementary3Derivative, div_eq_mul_inv]
  ring

theorem matrixElementary3_hasFDerivAt (root : Matrix4) :
    FrobeniusHasFDerivAt matrixElementary3
      (matrixElementary3Derivative root) root := by
  unfold FrobeniusHasFDerivAt
  have hTrace := traceCovector.hasFDerivAt (x := root)
  have hSquare := traceSquare_hasFDerivAt root
  have hCube := traceCube_hasFDerivAt root
  have hRaw := ((hTrace.pow 3).sub
      ((hTrace.mul hSquare).const_mul (3 : ℝ))).add
        (hCube.const_mul (2 : ℝ)) |>.const_mul ((6 : ℝ)⁻¹)
  have hFunction : Filter.EventuallyEq (nhds root)
      matrixElementary3
      (fun point : Matrix4 => (6 : ℝ)⁻¹ *
        (((Matrix.trace point) ^ 3 -
          3 * (Matrix.trace point * Matrix.trace (point * point))) +
          2 * Matrix.trace (point * point * point))) :=
    Filter.Eventually.of_forall fun point => by
      simp [matrixElementary3, div_eq_mul_inv]
      ring
  have hRewritten := hRaw.congr_of_eventuallyEq hFunction
  refine hRewritten.congr_fderiv ?_
  rfl

/-- The full explicit covector of the matrix spectral potential. -/
def matrixSpectralPotentialDerivative
    (coefficients : PotentialCoefficients) (root : Matrix4) :
    Matrix4 →L[ℝ] ℝ :=
  coefficients.beta1 • traceCovector +
    coefficients.beta2 • matrixElementary2Derivative root +
    coefficients.beta3 • matrixElementary3Derivative root +
    coefficients.beta4 • determinantDerivative root

@[simp]
theorem matrixSpectralPotentialDerivative_apply
    (coefficients : PotentialCoefficients) (root variation : Matrix4) :
    matrixSpectralPotentialDerivative coefficients root variation =
      coefficients.beta1 * Matrix.trace variation +
        coefficients.beta2 * matrixElementary2Derivative root variation +
        coefficients.beta3 * matrixElementary3Derivative root variation +
        coefficients.beta4 * determinantDerivative root variation := by
  simp [matrixSpectralPotentialDerivative]

/-- The displayed covector is the actual Frechet derivative, not supplied
gradient data. -/
theorem matrixSpectralPotential_hasFDerivAt
    (coefficients : PotentialCoefficients) (root : Matrix4) :
    FrobeniusHasFDerivAt (matrixSpectralPotential coefficients)
      (matrixSpectralPotentialDerivative coefficients root) root := by
  unfold FrobeniusHasFDerivAt
  have h1 := (traceCovector.hasFDerivAt (x := root)).const_mul coefficients.beta1
  have h2 := (matrixElementary2_hasFDerivAt root).const_mul coefficients.beta2
  have h3 := (matrixElementary3_hasFDerivAt root).const_mul coefficients.beta3
  have h4 := (determinant_hasFDerivAt root).const_mul coefficients.beta4
  have hRaw := (((h1.add h2).add h3).add h4).const_add coefficients.beta0
  have hFunction : Filter.EventuallyEq (nhds root)
      (matrixSpectralPotential coefficients)
      (fun point : Matrix4 =>
        coefficients.beta0 +
          (coefficients.beta1 * matrixElementary1 point +
          coefficients.beta2 * matrixElementary2 point +
          coefficients.beta3 * matrixElementary3 point +
          coefficients.beta4 * matrixElementary4 point)) :=
    Filter.Eventually.of_forall fun point => by
      simp [matrixSpectralPotential, matrixElementary0]
      ring
  have hRewritten := hRaw.congr_of_eventuallyEq hFunction
  refine hRewritten.congr_fderiv ?_
  rfl

/-- Unconditional pointwise Noether pairing for the explicit interaction
covector.  This remains a finite-matrix frame statement only. -/
theorem explicit_matrixInteraction_noether_pairing
    (coefficients : PotentialCoefficients)
    (curve : OneParameterDiagonalFrame) (root : Matrix4) :
    matrixSpectralPotentialDerivative coefficients root
        (commutatorGenerator curve.generator root) = 0 :=
  matrixInteraction_noether_pairing coefficients curve root
    (matrixSpectralPotentialDerivative coefficients root)
    (matrixSpectralPotential_hasFDerivAt coefficients root)

end

end P0EFTJanusMatrixInteractionFrechetNoether
end JanusFormal
