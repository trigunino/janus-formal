import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGradedDiffeomorphismGhostTensor4D

/-!
# Scalar ghost action with the matrix coefficient witness

The intrinsic `C∞` tangent ghosts act on genuine `C∞` scalar fields by
manifold directional differentiation.  This action is bundled bilinearly and
therefore gives the genuine degree-zero Chevalley--Eilenberg differential.
Tensoring with the explicit matrix coefficient witness produces a
matrix-coefficient field variation and intertwines the square-zero coefficient
differentials.  `OddCoefficientMatrix` is not yet a formally graded algebra:
no Z2 decomposition or Koszul sign rule is claimed here.

The historical analytic scalar fields downgrade canonically to this `C∞`
module, and the new action agrees there with the previously constructed
analytic scalar Lie derivative.  The Lie-representation commutator identity,
the nonlinear BRST differential and antifield/BV closure remain separate.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGradedScalarGhostAction4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff TensorProduct
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusLinearizedDiffeomorphismBRST4D
open P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D
open P0EFTJanusGradedGhostCoefficientWitness4D
open P0EFTJanusMappingTorusGradedDiffeomorphismGhostTensor4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Genuine globally smooth real scalar fields on the effective quotient. -/
abbrev CInfinityScalarField :=
  C^∞⟮coverModelWithCorners, EffectiveQuotient period hPeriod; Real⟯

/-- Every existing analytic scalar field canonically supplies a `C∞` field. -/
def analyticScalarToCInfinity
    (scalar : SmoothQuotientField period hPeriod Real) :
    CInfinityScalarField period hPeriod :=
  ⟨scalar.toFun, scalar.contMDiff_toFun.of_le (by simp)⟩

/-- Directional differentiation is an intrinsic action of a genuine global
`C∞` tangent ghost on a genuine global `C∞` scalar field. -/
def cInfinityScalarLieDerivative
    (ghost : CInfinityDiffeomorphismGhost period hPeriod)
    (scalar : CInfinityScalarField period hPeriod) :
    CInfinityScalarField period hPeriod :=
  ⟨fun point =>
      mvfderiv coverModelWithCorners scalar point (ghost point),
    by
      have hEvaluation : ContMDiff coverModelWithCorners.tangent
          (modelWithCornersSelf Real Real) ∞
          (fun vector : TangentBundle coverModelWithCorners
              (EffectiveQuotient period hPeriod) =>
            mvfderiv coverModelWithCorners scalar vector.1 vector.2) := by
        have hDerivative :=
          (contMDiff_snd_tangentBundle_modelSpace Real
            (modelWithCornersSelf Real Real) (n := ∞)).comp
            (scalar.contMDiff.contMDiff_tangentMap (m := ∞) (by simp))
        convert hDerivative using 1
        funext vector
        rfl
      exact hEvaluation.comp ghost.contMDiff⟩

@[simp]
theorem cInfinityScalarLieDerivative_zeroGhost
    (scalar : CInfinityScalarField period hPeriod) :
    cInfinityScalarLieDerivative period hPeriod 0 scalar = 0 := by
  apply ContMDiffMap.ext
  intro point
  change mvfderiv coverModelWithCorners scalar point 0 = 0
  exact map_zero _

theorem cInfinityScalarLieDerivative_addGhost
    (first second : CInfinityDiffeomorphismGhost period hPeriod)
    (scalar : CInfinityScalarField period hPeriod) :
    cInfinityScalarLieDerivative period hPeriod (first + second) scalar =
      cInfinityScalarLieDerivative period hPeriod first scalar +
        cInfinityScalarLieDerivative period hPeriod second scalar := by
  apply ContMDiffMap.ext
  intro point
  change mvfderiv coverModelWithCorners scalar point
      (first point + second point) = _
  exact map_add _ _ _

theorem cInfinityScalarLieDerivative_smulGhost
    (coefficient : Real)
    (ghost : CInfinityDiffeomorphismGhost period hPeriod)
    (scalar : CInfinityScalarField period hPeriod) :
    cInfinityScalarLieDerivative period hPeriod (coefficient • ghost) scalar =
      coefficient •
        cInfinityScalarLieDerivative period hPeriod ghost scalar := by
  apply ContMDiffMap.ext
  intro point
  change mvfderiv coverModelWithCorners scalar point
      (coefficient • ghost point) =
    coefficient • mvfderiv coverModelWithCorners scalar point (ghost point)
  exact map_smul _ _ _

@[simp]
theorem cInfinityScalarLieDerivative_zeroScalar
    (ghost : CInfinityDiffeomorphismGhost period hPeriod) :
    cInfinityScalarLieDerivative period hPeriod ghost 0 = 0 := by
  apply ContMDiffMap.ext
  intro point
  change mvfderiv coverModelWithCorners
      (0 : EffectiveQuotient period hPeriod → Real) point (ghost point) = 0
  rw [mvfderiv_zero]
  rfl

theorem cInfinityScalarLieDerivative_addScalar
    (ghost : CInfinityDiffeomorphismGhost period hPeriod)
    (first second : CInfinityScalarField period hPeriod) :
    cInfinityScalarLieDerivative period hPeriod ghost (first + second) =
      cInfinityScalarLieDerivative period hPeriod ghost first +
        cInfinityScalarLieDerivative period hPeriod ghost second := by
  apply ContMDiffMap.ext
  intro point
  change mvfderiv coverModelWithCorners
      ((first : EffectiveQuotient period hPeriod → Real) +
        (second : EffectiveQuotient period hPeriod → Real))
      point (ghost point) = _
  rw [mvfderiv_add
    (first.contMDiff.mdifferentiableAt (by simp))
    (second.contMDiff.mdifferentiableAt (by simp))]
  rfl

theorem cInfinityScalarLieDerivative_smulScalar
    (ghost : CInfinityDiffeomorphismGhost period hPeriod)
    (coefficient : Real)
    (scalar : CInfinityScalarField period hPeriod) :
    cInfinityScalarLieDerivative period hPeriod ghost
        (coefficient • scalar) =
      coefficient •
        cInfinityScalarLieDerivative period hPeriod ghost scalar := by
  apply ContMDiffMap.ext
  intro point
  have hConst : MDifferentiableAt coverModelWithCorners
      (modelWithCornersSelf Real Real)
      (fun _ : EffectiveQuotient period hPeriod => coefficient) point :=
    (contMDiff_const : ContMDiff coverModelWithCorners
      (modelWithCornersSelf Real Real) ∞
      (fun _ : EffectiveQuotient period hPeriod => coefficient)).mdifferentiableAt
        (by simp)
  change mvfderiv coverModelWithCorners
      ((fun _ : EffectiveQuotient period hPeriod => coefficient) *
        (scalar : EffectiveQuotient period hPeriod → Real))
      point (ghost point) =
    coefficient * mvfderiv coverModelWithCorners scalar point (ghost point)
  rw [mvfderiv_mul hConst
    (scalar.contMDiff.mdifferentiableAt (by simp)),
    mvfderiv_const]
  change coefficient * _ + _ * 0 = coefficient * _
  rw [mul_zero, add_zero]
  rfl

/-- The scalar action, bundled as a linear map from ghosts to field
endomorphisms. -/
def cInfinityScalarGhostAction :
    CInfinityDiffeomorphismGhost period hPeriod →ₗ[Real]
      (CInfinityScalarField period hPeriod →ₗ[Real]
        CInfinityScalarField period hPeriod) where
  toFun ghost :=
    { toFun := cInfinityScalarLieDerivative period hPeriod ghost
      map_add' := cInfinityScalarLieDerivative_addScalar period hPeriod ghost
      map_smul' := cInfinityScalarLieDerivative_smulScalar period hPeriod ghost }
  map_add' first second := by
    apply LinearMap.ext
    intro scalar
    exact cInfinityScalarLieDerivative_addGhost period hPeriod first second scalar
  map_smul' coefficient ghost := by
    apply LinearMap.ext
    intro scalar
    exact cInfinityScalarLieDerivative_smulGhost period hPeriod coefficient ghost scalar

/-- Degree-zero Chevalley--Eilenberg differential: a scalar field is sent to
the one-cochain `ghost ↦ L_ghost scalar`. -/
def cInfinityScalarCEDifferentialZero :
    CInfinityScalarField period hPeriod →ₗ[Real]
      (CInfinityDiffeomorphismGhost period hPeriod →ₗ[Real]
        CInfinityScalarField period hPeriod) :=
  (cInfinityScalarGhostAction period hPeriod).flip

@[simp]
theorem cInfinityScalarCEDifferentialZero_apply
    (scalar : CInfinityScalarField period hPeriod)
    (ghost : CInfinityDiffeomorphismGhost period hPeriod) :
    cInfinityScalarCEDifferentialZero period hPeriod scalar ghost =
      cInfinityScalarLieDerivative period hPeriod ghost scalar :=
  rfl

/-- On analytic inputs the `C∞` action is exactly the downgrade of the
previous analytic scalar Lie derivative. -/
theorem cInfinityScalarLieDerivative_analytic
    (ghost : SmoothDiffeomorphismGhost period hPeriod)
    (scalar : SmoothQuotientField period hPeriod Real) :
    cInfinityScalarLieDerivative period hPeriod
        (smoothGhostToCInfinity period hPeriod ghost)
        (analyticScalarToCInfinity period hPeriod scalar) =
      analyticScalarToCInfinity period hPeriod
        (scalarLieDerivative period hPeriod ghost scalar) := by
  apply ContMDiffMap.ext
  intro point
  rfl

/-- The matrix coefficient witness tensored with actual `C∞` scalar fields.
The historical `Graded` name records its intended use, not a proved Z2-graded
module structure. -/
abbrev GradedCInfinityScalarField :=
  OddCoefficientMatrix ⊗[Real] CInfinityScalarField period hPeriod

/-- The same square-zero matrix-coefficient differential on scalar fields. -/
def gradedScalarFieldCoefficientDifferential :
    GradedCInfinityScalarField period hPeriod →ₗ[Real]
      GradedCInfinityScalarField period hPeriod :=
  TensorProduct.map oddCoefficientDifferential LinearMap.id

@[simp]
theorem gradedScalarFieldCoefficientDifferential_tmul
    (coefficient : OddCoefficientMatrix)
    (scalar : CInfinityScalarField period hPeriod) :
    gradedScalarFieldCoefficientDifferential period hPeriod
        (coefficient ⊗ₜ[Real] scalar) =
      oddCoefficientDifferential coefficient ⊗ₜ[Real] scalar := by
  simp [gradedScalarFieldCoefficientDifferential]

/-- The degree-zero CE action tensored with the matrix coefficient witness. -/
def gradedScalarCEDifferentialZero
    (scalar : CInfinityScalarField period hPeriod) :
    GradedDiffeomorphismGhostModule period hPeriod →ₗ[Real]
      GradedCInfinityScalarField period hPeriod :=
  TensorProduct.map LinearMap.id
    (cInfinityScalarCEDifferentialZero period hPeriod scalar)

@[simp]
theorem gradedScalarCEDifferentialZero_tmul
    (scalar : CInfinityScalarField period hPeriod)
    (coefficient : OddCoefficientMatrix)
    (ghost : CInfinityDiffeomorphismGhost period hPeriod) :
    gradedScalarCEDifferentialZero period hPeriod scalar
        (coefficient ⊗ₜ[Real] ghost) =
      coefficient ⊗ₜ[Real]
        cInfinityScalarLieDerivative period hPeriod ghost scalar := by
  simp [gradedScalarCEDifferentialZero]

/-- The explicit quadratic ghost-bracket term now acts on an actual scalar
field, with no reinterpretation of either its odd coefficient or its tangent
ghost factor. -/
theorem gradedScalarCEDifferentialZero_quadraticGhostBracketTerm
    (scalar : CInfinityScalarField period hPeriod)
    (first second : CInfinityDiffeomorphismGhost period hPeriod) :
    gradedScalarCEDifferentialZero period hPeriod scalar
        (gradedQuadraticGhostBracketTerm period hPeriod first second) =
      gradedQuadraticGhostBRSTCoefficient ⊗ₜ[Real]
        cInfinityScalarLieDerivative period hPeriod
          (smoothGhostLieBracket period hPeriod first second) scalar := by
  rw [gradedQuadraticGhostBracketTerm,
    gradedScalarCEDifferentialZero_tmul]

/-- The coefficient differential is nilpotent on every matrix-coefficient
scalar field. -/
theorem gradedScalarFieldCoefficientDifferential_sq
    (term : GradedCInfinityScalarField period hPeriod) :
    gradedScalarFieldCoefficientDifferential period hPeriod
        (gradedScalarFieldCoefficientDifferential period hPeriod term) = 0 := by
  refine TensorProduct.induction_on term ?_ ?_ ?_
  · simp
  · intro coefficient scalar
    simp [oddCoefficientDifferential_sq]
  · intro first second hFirst hSecond
    simp only [map_add]
    rw [hFirst, hSecond, add_zero]

/-- The CE field action intertwines the coefficient differential on ghosts
with the coefficient differential on matrix-coefficient scalar variations. -/
theorem gradedScalarCEDifferentialZero_intertwinesCoefficientDifferential
    (scalar : CInfinityScalarField period hPeriod)
    (term : GradedDiffeomorphismGhostModule period hPeriod) :
    gradedScalarFieldCoefficientDifferential period hPeriod
        (gradedScalarCEDifferentialZero period hPeriod scalar term) =
      gradedScalarCEDifferentialZero period hPeriod scalar
        (gradedGhostCoefficientDifferential period hPeriod term) := by
  refine TensorProduct.induction_on term ?_ ?_ ?_
  · simp
  · intro coefficient ghost
    simp
  · intro first second hFirst hSecond
    simp only [map_add]
    rw [hFirst, hSecond]

/-- The genuine matter scalars already selected from `IndependentFields`
therefore receive the same matrix-coefficient ghost action. -/
theorem gradedScalarCEDifferentialZero_independentMatter
    (fields : IndependentFieldsWithDiffeomorphismGhost period hPeriod)
    (sector : Fin 2) (component : Fin 4)
    (coefficient : OddCoefficientMatrix) :
    gradedScalarCEDifferentialZero period hPeriod
        (analyticScalarToCInfinity period hPeriod
          (independentMatterScalar period hPeriod fields.fields sector component))
        (coefficient ⊗ₜ[Real]
          smoothGhostToCInfinity period hPeriod fields.diffeomorphismGhost) =
      coefficient ⊗ₜ[Real]
        analyticScalarToCInfinity period hPeriod
          (scalarLieDerivative period hPeriod fields.diffeomorphismGhost
            (independentMatterScalar period hPeriod
              fields.fields sector component)) := by
  rw [gradedScalarCEDifferentialZero_tmul,
    cInfinityScalarLieDerivative_analytic]

theorem graded_scalar_ghost_action4D_closure :
    (∀ term : GradedCInfinityScalarField period hPeriod,
      gradedScalarFieldCoefficientDifferential period hPeriod
          (gradedScalarFieldCoefficientDifferential period hPeriod term) = 0) ∧
      ∀ (scalar : CInfinityScalarField period hPeriod)
        (term : GradedDiffeomorphismGhostModule period hPeriod),
        gradedScalarFieldCoefficientDifferential period hPeriod
            (gradedScalarCEDifferentialZero period hPeriod scalar term) =
          gradedScalarCEDifferentialZero period hPeriod scalar
            (gradedGhostCoefficientDifferential period hPeriod term) :=
  ⟨gradedScalarFieldCoefficientDifferential_sq period hPeriod,
    gradedScalarCEDifferentialZero_intertwinesCoefficientDifferential
      period hPeriod⟩

end

end P0EFTJanusMappingTorusGradedScalarGhostAction4D
end JanusFormal
