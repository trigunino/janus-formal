import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteNullFaceMobileGeometricRealization4D

/-!
# Explicit warped null hyperplane geometry

This gate gives `FiniteNullFaceMobileGeometricDatum` an unconditional,
coordinate-level inhabitant.  In coordinates `(u,x,y,z)` the face is the
hyperplane `z = u`, with embedding `(u,x,y) ↦ (u,x,y,u)` and diagonal ambient
metric `diag(-1, exp u, exp u, 1)`.  Its generator is null, its screen metric
is `exp u` times the identity, and its homogeneous screen expansion is one.

This is an explicit ambient carrier.  It is not identified with the mapping
torus, the cut throat, or their physical Lorentz metric, so it supplies no
bulk-to-null incidence or integrated Stokes theorem by itself.
Its endpoint, joint, orientation, and normalization fields are conventional
constants; no joint carrier or input-faithful action realization is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06ExplicitWarpedNullHyperplaneGeometry4D

set_option autoImplicit false

noncomputable section

open scoped BigOperators ContDiff
open P0EFTJanusExplicitBoundaryDensityLedger
open P0EFTJanusNullJointReparametrizationCancellation
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalProductEuler4D
open P0EFTJanusFiniteNullFaceMobileGeometricRealization4D

abbrev ProgramPT06WarpedNullSource3 :=
  Real × FiniteNullFaceScreenCoordinate2

/-- Linear embedding of the null hyperplane `z = u`. -/
def programPT06WarpedNullHyperplaneEmbeddingLinear :
    ProgramPT06WarpedNullSource3 →ₗ[Real]
      FiniteNullFaceAmbientCoordinate4 where
  toFun source :=
    (EuclideanSpace.equiv (Fin 4) Real).symm
      ![source.1, source.2 0, source.2 1, source.1]
  map_add' first second := by
    apply (EuclideanSpace.equiv (Fin 4) Real).injective
    funext index
    fin_cases index <;> simp
  map_smul' scalar source := by
    apply (EuclideanSpace.equiv (Fin 4) Real).injective
    funext index
    fin_cases index <;> simp

def programPT06WarpedNullHyperplaneEmbedding :
    ProgramPT06WarpedNullSource3 →L[Real]
      FiniteNullFaceAmbientCoordinate4 :=
  LinearMap.toContinuousLinearMap
    programPT06WarpedNullHyperplaneEmbeddingLinear

/-- The defining function `z - u`. -/
def programPT06WarpedNullHyperplaneDefiningLinear :
    FiniteNullFaceAmbientCoordinate4 →ₗ[Real] Real where
  toFun point := point 3 - point 0
  map_add' first second := by
    simp; ring
  map_smul' scalar point := by
    simp; ring

def programPT06WarpedNullHyperplaneDefiningDifferential :
    FiniteNullFaceAmbientCoordinate4 →L[Real] Real :=
  LinearMap.toContinuousLinearMap
    programPT06WarpedNullHyperplaneDefiningLinear

/-- Generator differential `(du,0,0,du)`. -/
def programPT06WarpedNullHyperplaneGeneratorDifferential :
    Real →L[Real] FiniteNullFaceAmbientCoordinate4 :=
  programPT06WarpedNullHyperplaneEmbedding.comp
    (ContinuousLinearMap.inl Real Real FiniteNullFaceScreenCoordinate2)

/-- Screen differential `(0,dx,dy,0)`. -/
def programPT06WarpedNullHyperplaneScreenDifferential :
    FiniteNullFaceScreenCoordinate2 →L[Real]
      FiniteNullFaceAmbientCoordinate4 :=
  programPT06WarpedNullHyperplaneEmbedding.comp
    (ContinuousLinearMap.inr Real Real FiniteNullFaceScreenCoordinate2)

@[simp] theorem programPT06WarpedNullHyperplaneEmbedding_apply
    (source : ProgramPT06WarpedNullSource3) :
    programPT06WarpedNullHyperplaneEmbedding source =
      (EuclideanSpace.equiv (Fin 4) Real).symm
        ![source.1, source.2 0, source.2 1, source.1] := by
  rfl

@[simp] theorem programPT06WarpedNullHyperplaneDefiningDifferential_apply
    (point : FiniteNullFaceAmbientCoordinate4) :
    programPT06WarpedNullHyperplaneDefiningDifferential point =
      point 3 - point 0 := by
  rfl

@[simp] theorem programPT06WarpedNullHyperplaneDefiningFunction_on_embedding
    (source : ProgramPT06WarpedNullSource3) :
    programPT06WarpedNullHyperplaneDefiningDifferential
        (programPT06WarpedNullHyperplaneEmbedding source) = 0 := by
  simp

@[simp] theorem programPT06WarpedNullHyperplaneGeneratorDifferential_apply
    (variation : Real) :
    programPT06WarpedNullHyperplaneGeneratorDifferential variation =
      (EuclideanSpace.equiv (Fin 4) Real).symm
        ![variation, 0, 0, variation] := by
  apply (EuclideanSpace.equiv (Fin 4) Real).injective
  funext index
  fin_cases index <;>
    simp [programPT06WarpedNullHyperplaneGeneratorDifferential]

@[simp] theorem programPT06WarpedNullHyperplaneScreenDifferential_apply
    (variation : FiniteNullFaceScreenCoordinate2) :
    programPT06WarpedNullHyperplaneScreenDifferential variation =
      (EuclideanSpace.equiv (Fin 4) Real).symm
        ![0, variation 0, variation 1, 0] := by
  apply (EuclideanSpace.equiv (Fin 4) Real).injective
  funext index
  fin_cases index <;>
    simp [programPT06WarpedNullHyperplaneScreenDifferential]

/-- Diagonal Lorentz weights `(-1, exp u, exp u, 1)`. -/
def programPT06WarpedNullHyperplaneAmbientWeight
    (point : FiniteNullFaceAmbientCoordinate4) : Fin 4 → Real :=
  ![-1, Real.exp (point 0), Real.exp (point 0), 1]

def programPT06WarpedNullHyperplaneAmbientMetric
    (point : FiniteNullFaceAmbientCoordinate4) :
    FiniteNullFaceAmbientMatrix4 :=
  Matrix.diagonal (programPT06WarpedNullHyperplaneAmbientWeight point)

def programPT06WarpedNullHyperplaneAmbientInverseMetric
    (point : FiniteNullFaceAmbientCoordinate4) :
    FiniteNullFaceAmbientMatrix4 :=
  Matrix.diagonal
    (fun index =>
      (programPT06WarpedNullHyperplaneAmbientWeight point index)⁻¹)

/-- Coordinate raising of the defining covector by the inverse metric. -/
def programPT06WarpedNullHyperplaneRaisedDefiningCovector
    (point : FiniteNullFaceAmbientCoordinate4) :
    FiniteNullFaceAmbientCoordinate4 :=
  (EuclideanSpace.equiv (Fin 4) Real).symm
    (fun row => ∑ column : Fin 4,
      programPT06WarpedNullHyperplaneAmbientInverseMetric point row column *
        programPT06WarpedNullHyperplaneDefiningDifferential
          (EuclideanSpace.single column 1))

/-- Raising `d(z-u)` gives the stored null generator `(1,0,0,1)`. -/
theorem programPT06WarpedNullHyperplaneRaisedDefiningCovector_eq_generator
    (point : FiniteNullFaceAmbientCoordinate4) :
    programPT06WarpedNullHyperplaneRaisedDefiningCovector point =
      programPT06WarpedNullHyperplaneGeneratorDifferential 1 := by
  apply (EuclideanSpace.equiv (Fin 4) Real).injective
  funext index
  fin_cases index <;>
    simp [programPT06WarpedNullHyperplaneRaisedDefiningCovector,
      programPT06WarpedNullHyperplaneAmbientInverseMetric,
      programPT06WarpedNullHyperplaneAmbientWeight, Fin.sum_univ_four]

def programPT06WarpedNullHyperplaneScreenMetric
    (parameter : Real) : Matrix2 :=
  Matrix.diagonal (fun _ => Real.exp parameter)

def programPT06WarpedNullHyperplaneScreenInverse
    (parameter : Real) : Matrix2 :=
  Matrix.diagonal (fun _ => (Real.exp parameter)⁻¹)

theorem programPT06WarpedNullHyperplaneAmbientWeight_ne_zero
    (point : FiniteNullFaceAmbientCoordinate4) (index : Fin 4) :
    programPT06WarpedNullHyperplaneAmbientWeight point index ≠ 0 := by
  fin_cases index <;>
    simp [programPT06WarpedNullHyperplaneAmbientWeight, Real.exp_ne_zero]

theorem programPT06WarpedNullHyperplaneAmbientInverseWitness
    (point : FiniteNullFaceAmbientCoordinate4) :
    FiniteNullFaceAmbientMatrix4InverseWitness
      (programPT06WarpedNullHyperplaneAmbientMetric point)
      (programPT06WarpedNullHyperplaneAmbientInverseMetric point) := by
  constructor
  · rw [programPT06WarpedNullHyperplaneAmbientMetric,
      programPT06WarpedNullHyperplaneAmbientInverseMetric,
      Matrix.diagonal_mul_diagonal]
    ext row column
    by_cases h : row = column
    · subst column
      simp [programPT06WarpedNullHyperplaneAmbientWeight_ne_zero]
    · simp [h]
  · rw [programPT06WarpedNullHyperplaneAmbientMetric,
      programPT06WarpedNullHyperplaneAmbientInverseMetric,
      Matrix.diagonal_mul_diagonal]
    ext row column
    by_cases h : row = column
    · subst column
      simp [programPT06WarpedNullHyperplaneAmbientWeight_ne_zero]
    · simp [h]

theorem programPT06WarpedNullHyperplaneScreenInverseWitness
    (parameter : Real) :
    Matrix2InverseWitness
      (programPT06WarpedNullHyperplaneScreenMetric parameter)
      (programPT06WarpedNullHyperplaneScreenInverse parameter) := by
  constructor
  · rw [programPT06WarpedNullHyperplaneScreenMetric,
      programPT06WarpedNullHyperplaneScreenInverse,
      Matrix.diagonal_mul_diagonal]
    ext row column
    by_cases h : row = column
    · subst column
      simp [Real.exp_ne_zero]
    · simp [h]
  · rw [programPT06WarpedNullHyperplaneScreenMetric,
      programPT06WarpedNullHyperplaneScreenInverse,
      Matrix.diagonal_mul_diagonal]
    ext row column
    by_cases h : row = column
    · subst column
      simp [Real.exp_ne_zero]
    · simp [h]

theorem programPT06WarpedNullHyperplaneScreenMetric_det
    (parameter : Real) :
    Matrix.det (programPT06WarpedNullHyperplaneScreenMetric parameter) =
      (Real.exp parameter) ^ 2 := by
  rw [Matrix.det_fin_two]
  simp [programPT06WarpedNullHyperplaneScreenMetric]; ring

@[simp] theorem programPT06WarpedNullHyperplaneScreenArea
    (parameter : Real) :
    finiteNullFaceHomogeneousScreenArea
        programPT06WarpedNullHyperplaneScreenMetric parameter =
      Real.exp parameter := by
  rw [finiteNullFaceHomogeneousScreenArea,
    programPT06WarpedNullHyperplaneScreenMetric_det,
    abs_of_nonneg (sq_nonneg _), Real.sqrt_sq (Real.exp_pos _).le]

theorem programPT06WarpedNullHyperplaneEmbedding_injective :
    Function.Injective programPT06WarpedNullHyperplaneEmbedding := by
  intro first second hEqual
  apply Prod.ext
  · simpa using congrArg
      (fun point : FiniteNullFaceAmbientCoordinate4 =>
        EuclideanSpace.equiv (Fin 4) Real point 0) hEqual
  · ext index
    fin_cases index
    · simpa using congrArg
        (fun point : FiniteNullFaceAmbientCoordinate4 =>
          EuclideanSpace.equiv (Fin 4) Real point 1) hEqual
    · simpa using congrArg
        (fun point : FiniteNullFaceAmbientCoordinate4 =>
          EuclideanSpace.equiv (Fin 4) Real point 2) hEqual

theorem programPT06WarpedNullHyperplaneScreenDifferential_injective :
    Function.Injective
      programPT06WarpedNullHyperplaneScreenDifferential := by
  intro first second hEqual
  ext index
  fin_cases index
  · simpa using congrArg
      (fun point : FiniteNullFaceAmbientCoordinate4 =>
        EuclideanSpace.equiv (Fin 4) Real point 1) hEqual
  · simpa using congrArg
      (fun point : FiniteNullFaceAmbientCoordinate4 =>
        EuclideanSpace.equiv (Fin 4) Real point 2) hEqual

theorem programPT06WarpedNullHyperplaneAmbientMetric_entry_contDiff_two
    (row column : Fin 4) :
    ContDiff Real 2
      (fun point : FiniteNullFaceAmbientCoordinate4 =>
        programPT06WarpedNullHyperplaneAmbientMetric point row column) := by
  fin_cases row <;> fin_cases column <;>
    simp [programPT06WarpedNullHyperplaneAmbientMetric,
      programPT06WarpedNullHyperplaneAmbientWeight] <;> fun_prop

theorem programPT06WarpedNullHyperplaneScreenMetric_entry_contDiff_two
    (row column : Fin 2) :
    ContDiff Real 2
      (fun parameter : Real =>
        programPT06WarpedNullHyperplaneScreenMetric parameter row column) := by
  fin_cases row <;> fin_cases column <;>
    simp [programPT06WarpedNullHyperplaneScreenMetric] <;> fun_prop

/-- An unconditional finite family of identical warped null hyperplanes. -/
def programPT06ExplicitWarpedNullHyperplaneGeometry
    (NullFace : Type*) [Fintype NullFace] :
    FiniteNullFaceMobileGeometricDatum NullFace where
  domain := Set.univ
  domain_isOpen := isOpen_univ
  zero_mem_domain := Set.mem_univ _
  embedding := fun _ _ => programPT06WarpedNullHyperplaneEmbedding
  definingFunction := fun _ _ =>
    programPT06WarpedNullHyperplaneDefiningDifferential
  ambientMetric := fun _ _ =>
    programPT06WarpedNullHyperplaneAmbientMetric
  ambientInverseMetric := fun _ _ =>
    programPT06WarpedNullHyperplaneAmbientInverseMetric
  definingDifferential := fun _ _ _ =>
    programPT06WarpedNullHyperplaneDefiningDifferential
  screenDifferential := fun _ _ _ _ =>
    programPT06WarpedNullHyperplaneScreenDifferential
  generatorDifferential := fun _ _ _ _ =>
    programPT06WarpedNullHyperplaneGeneratorDifferential
  generatorCovariantAcceleration := fun _ _ _ _ => 0
  screenMetric := fun _ _ => programPT06WarpedNullHyperplaneScreenMetric
  screenInverse := fun _ _ => programPT06WarpedNullHyperplaneScreenInverse
  expansion := fun _ _ _ => 1
  inaffinity := fun _ _ _ => 0
  sigma := fun _ _ _ => 0
  sigmaDerivative := fun _ _ _ => 0
  interval := fun _ =>
    { initialParameter := 0
      finalParameter := 1 }
  einsteinScale := fun _ => 1
  faceOrientationSign := fun _ => 1
  faceOrientationSignAdmissible := by
    intro face
    exact Or.inl rfl
  renormalizationLengthScale := fun _ => 1
  renormalizationLengthScalePositive := by
    intro face
    norm_num
  initialJointOrientationSign := fun _ => 1
  initialJointOrientationSignAdmissible := by
    intro face
    exact Or.inl rfl
  finalJointOrientationSign := fun _ => 1
  finalJointOrientationSignAdmissible := by
    intro face
    exact Or.inl rfl
  initialJointAngle := fun _ _ => 0
  finalJointAngle := fun _ _ => 0
  embedding_contDiffOn_three := by
    intro face
    exact
      (programPT06WarpedNullHyperplaneEmbedding.contDiff.comp
        contDiff_snd).contDiffOn
  definingFunction_contDiffOn_three := by
    intro face
    exact
      (programPT06WarpedNullHyperplaneDefiningDifferential.contDiff.comp
        contDiff_snd).contDiffOn
  ambientMetric_contDiffOn_two := by
    intro face row column
    exact
      ((programPT06WarpedNullHyperplaneAmbientMetric_entry_contDiff_two
          row column).comp contDiff_snd).contDiffOn
  screenMetric_contDiffOn_two := by
    intro face row column
    exact
      ((programPT06WarpedNullHyperplaneScreenMetric_entry_contDiff_two
          row column).comp contDiff_snd).contDiffOn
  expansion_contDiffOn_two := by
    intro face
    fun_prop
  inaffinity_contDiffOn_two := by
    intro face
    fun_prop
  embedding_injective := by
    intro input hInput face
    exact programPT06WarpedNullHyperplaneEmbedding_injective
  embedding_zero_level := by
    intro input hInput face source
    simp
  definingFunction_hasFDerivAt := by
    intro input hInput face point
    exact
      programPT06WarpedNullHyperplaneDefiningDifferential.hasFDerivAt
  definingDifferential_ne_zero_on_face := by
    intro input hInput face source hZero
    have hApplied := congrArg
      (fun differential : FiniteNullFaceAmbientCoordinate4 →L[Real] Real =>
        differential (EuclideanSpace.single (0 : Fin 4) 1)) hZero
    simp at hApplied
  ambientMetricSymmetric := by
    intro input face point
    simp [programPT06WarpedNullHyperplaneAmbientMetric]
  ambientMetricInverseWitness := by
    intro input face point
    exact programPT06WarpedNullHyperplaneAmbientInverseWitness point
  definingDifferential_null_on_face := by
    intro input hInput face source
    simp [finiteNullFaceDefiningCovectorSquare,
      programPT06WarpedNullHyperplaneAmbientInverseMetric,
      programPT06WarpedNullHyperplaneAmbientWeight,
      Fin.sum_univ_four]
  screenEmbedding_hasFDerivAt := by
    intro input hInput face parameter screen
    exact
      programPT06WarpedNullHyperplaneEmbedding.hasFDerivAt.comp screen
        (hasFDerivAt_prodMk_right (𝕜 := Real) parameter screen)
  screenDifferential_injective := by
    intro input hInput face parameter screen
    exact programPT06WarpedNullHyperplaneScreenDifferential_injective
  generatorEmbedding_hasFDerivAt := by
    intro input hInput face parameter screen
    exact
      programPT06WarpedNullHyperplaneEmbedding.hasFDerivAt.comp parameter
        (hasFDerivAt_prodMk_left (𝕜 := Real) parameter screen)
  generatorTangent_ne_zero := by
    intro input hInput face parameter screen hZero
    have hApplied := congrArg
      (fun point : FiniteNullFaceAmbientCoordinate4 =>
        EuclideanSpace.equiv (Fin 4) Real point 0) hZero
    norm_num at hApplied
  generatorTangent_null := by
    intro input hInput face parameter screen
    simp [finiteNullFaceAmbientMetricPairing,
      programPT06WarpedNullHyperplaneAmbientMetric,
      programPT06WarpedNullHyperplaneAmbientWeight,
      Fin.sum_univ_four]
  generatorTangent_screen_orthogonal := by
    intro input hInput face parameter screen index
    fin_cases index <;>
      simp [finiteNullFaceAmbientMetricPairing,
        programPT06WarpedNullHyperplaneAmbientMetric,
        programPT06WarpedNullHyperplaneAmbientWeight,
        Fin.sum_univ_four]
  screenMetric_eq_induced := by
    intro input hInput face parameter screen first second
    fin_cases first <;> fin_cases second <;>
      simp [finiteNullFaceInducedScreenMetricComponent,
        finiteNullFaceAmbientMetricPairing,
        programPT06WarpedNullHyperplaneScreenMetric,
        programPT06WarpedNullHyperplaneAmbientMetric,
        programPT06WarpedNullHyperplaneAmbientWeight,
        Fin.sum_univ_four]
  screenMetricSymmetric := by
    intro input face parameter
    simp [programPT06WarpedNullHyperplaneScreenMetric]
  screenMetricDeterminantPositive := by
    intro input face parameter
    rw [programPT06WarpedNullHyperplaneScreenMetric_det]
    positivity
  screenInverseWitness := by
    intro input face parameter
    exact programPT06WarpedNullHyperplaneScreenInverseWitness parameter
  inaffinity_acceleration_law := by
    intro input hInput face parameter screen
    simp
  screenArea_hasDerivAt := by
    intro input face parameter
    change HasDerivAt
      (fun current =>
        finiteNullFaceHomogeneousScreenArea
          programPT06WarpedNullHyperplaneScreenMetric current)
      (finiteNullFaceHomogeneousScreenArea
          programPT06WarpedNullHyperplaneScreenMetric parameter * 1)
      parameter
    have hFunction :
        (fun current =>
          finiteNullFaceHomogeneousScreenArea
            programPT06WarpedNullHyperplaneScreenMetric current) =
          Real.exp := by
      funext current
      exact programPT06WarpedNullHyperplaneScreenArea current
    rw [hFunction, programPT06WarpedNullHyperplaneScreenArea, mul_one]
    exact Real.hasDerivAt_exp parameter
  sigma_hasDerivAt := by
    intro input face parameter
    simpa using hasDerivAt_const (x := parameter) (c := (0 : Real))
  expansion_ne_zero_on_domain := by
    intro input hInput face parameter hParameter
    norm_num

theorem programPT06ExplicitWarpedNullHyperplaneGeometry_nonempty
    (NullFace : Type*) [Fintype NullFace] :
    Nonempty (FiniteNullFaceMobileGeometricDatum NullFace) :=
  ⟨programPT06ExplicitWarpedNullHyperplaneGeometry NullFace⟩

end
end P0EFTJanusProgramPT06ExplicitWarpedNullHyperplaneGeometry4D
end JanusFormal
