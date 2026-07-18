import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorField.Pullback
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusDiagonalDiffeomorphismAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusSmoothFieldLinearSpace4D

/-!
# Linearized diffeomorphism ghost and BRST differential on the D8 quotient

The diffeomorphism ghost is an actual smooth section of the tangent bundle of
the effective mapping torus.  Global diffeomorphisms act through Mathlib's
intrinsic vector-field pullback.  The ghost acts infinitesimally on a genuine
smooth scalar by its manifold directional derivative.

The BRST complex constructed here is the honest linearized (abelianized)
complex about a fixed scalar background: `s(deltaPhi,c) = (L_c phi,0)`.  Its
nilpotence is exact.  No claim is made about the nonlinear graded rule
`s c = -1/2 [c,c]`, the metric Lie derivative, antifields or BV closure.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusLinearizedDiffeomorphismBRST4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusDiagonalDiffeomorphismAction4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- A diffeomorphism ghost is a genuine `C∞` tangent-bundle section on the
actual smooth D8 quotient. -/
abbrev SmoothDiffeomorphismGhost :=
  ContMDiffSection coverModelWithCorners CoverCoordinates ω
    (fun point : EffectiveQuotient period hPeriod =>
      TangentSpace coverModelWithCorners point)

/-- Intrinsic pullback of a smooth vector ghost by a global D8
diffeomorphism. -/
def pullbackDiffeomorphismGhost
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (ghost : SmoothDiffeomorphismGhost period hPeriod) :
    SmoothDiffeomorphismGhost period hPeriod where
  toFun := VectorField.mpullback coverModelWithCorners coverModelWithCorners
    diffeomorphism ghost
  contMDiff_toFun := by
    apply ghost.contMDiff.mpullback_vectorField diffeomorphism.contMDiff
    · intro point
      rw [← diffeomorphism.mfderivToContinuousLinearEquiv_coe (by simp)]
      exact ContinuousLinearMap.isInvertible_equiv
    · simp

@[simp]
theorem pullbackDiffeomorphismGhost_apply
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (ghost : SmoothDiffeomorphismGhost period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    pullbackDiffeomorphismGhost period hPeriod diffeomorphism ghost point =
      VectorField.mpullback coverModelWithCorners coverModelWithCorners
        diffeomorphism ghost point :=
  rfl

@[simp]
theorem pullbackDiffeomorphismGhost_refl
    (ghost : SmoothDiffeomorphismGhost period hPeriod) :
    pullbackDiffeomorphismGhost period hPeriod
        (Diffeomorph.refl coverModelWithCorners
          (EffectiveQuotient period hPeriod) ω) ghost = ghost := by
  apply ContMDiffSection.ext
  intro point
  simpa [pullbackDiffeomorphismGhost] using
    congrFun (VectorField.mpullback_id
      (I := coverModelWithCorners) (V := fun x => ghost x)) point

@[simp]
theorem pullbackDiffeomorphismGhost_zero
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod) :
    pullbackDiffeomorphismGhost period hPeriod diffeomorphism 0 = 0 := by
  apply ContMDiffSection.ext
  intro point
  exact congrFun (VectorField.mpullback_zero
    (I := coverModelWithCorners) (I' := coverModelWithCorners)
    (f := diffeomorphism)) point

theorem pullbackDiffeomorphismGhost_add
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (first second : SmoothDiffeomorphismGhost period hPeriod) :
    pullbackDiffeomorphismGhost period hPeriod diffeomorphism
        (first + second) =
      pullbackDiffeomorphismGhost period hPeriod diffeomorphism first +
        pullbackDiffeomorphismGhost period hPeriod diffeomorphism second := by
  apply ContMDiffSection.ext
  intro point
  exact congrFun (VectorField.mpullback_add
    (I := coverModelWithCorners) (I' := coverModelWithCorners)
    (f := diffeomorphism) (V := fun x => first x)
    (V₁ := fun x => second x)) point

/-- Contravariant action law for intrinsic vector-field pullback. -/
theorem pullbackDiffeomorphismGhost_trans
    (first second : SpacetimeDiffeomorphism period hPeriod)
    (ghost : SmoothDiffeomorphismGhost period hPeriod) :
    pullbackDiffeomorphismGhost period hPeriod first
        (pullbackDiffeomorphismGhost period hPeriod second ghost) =
      pullbackDiffeomorphismGhost period hPeriod (first.trans second) ghost := by
  apply ContMDiffSection.ext
  intro point
  have hFirst : MDifferentiableWithinAt coverModelWithCorners
      coverModelWithCorners first Set.univ point :=
    first.contMDiff.mdifferentiableAt (by simp) |>.mdifferentiableWithinAt
  have hSecondInvertible :
      (mfderivWithin coverModelWithCorners coverModelWithCorners
        second Set.univ (first point)).IsInvertible := by
    rw [mfderivWithin_univ,
      ← second.mfderivToContinuousLinearEquiv_coe (by simp)]
    exact ContinuousLinearMap.isInvertible_equiv
  have hComposition := VectorField.mpullbackWithin_comp_of_left
    (I := coverModelWithCorners) (I' := coverModelWithCorners)
    (I'' := coverModelWithCorners) (f := first) (g := second)
    (V := fun x => ghost x) (s := Set.univ) (t := Set.univ)
    (x₀ := point) hFirst (Set.mapsTo_univ first Set.univ)
    (uniqueMDiffWithinAt_univ coverModelWithCorners)
    hSecondInvertible
  simpa [pullbackDiffeomorphismGhost, Function.comp_def] using
    hComposition.symm

/-- Pullback by the inverse diffeomorphism is the inverse ghost action. -/
theorem pullbackDiffeomorphismGhost_symm
    (diffeomorphism : SpacetimeDiffeomorphism period hPeriod)
    (ghost : SmoothDiffeomorphismGhost period hPeriod) :
    pullbackDiffeomorphismGhost period hPeriod diffeomorphism.symm
        (pullbackDiffeomorphismGhost period hPeriod diffeomorphism ghost) =
      ghost := by
  rw [pullbackDiffeomorphismGhost_trans,
    diffeomorphism.symm_trans_self,
    pullbackDiffeomorphismGhost_refl]

/-- The intrinsic scalar Lie derivative `L_c phi = d phi(c)` on the actual
quotient. -/
def scalarLieDerivative
    (ghost : SmoothDiffeomorphismGhost period hPeriod)
    (scalar : SmoothQuotientField period hPeriod Real) :
    SmoothQuotientField period hPeriod Real where
  toFun := fun point =>
    mvfderiv coverModelWithCorners scalar.toFun point (ghost point)
  contMDiff_toFun := by
    have hEvaluation : ContMDiff coverModelWithCorners.tangent
        (modelWithCornersSelf Real Real) ∞
        (fun vector : TangentBundle coverModelWithCorners
            (EffectiveQuotient period hPeriod) =>
          mvfderiv coverModelWithCorners scalar.toFun vector.1 vector.2) := by
      have hDerivative :=
        (contMDiff_snd_tangentBundle_modelSpace Real
          (modelWithCornersSelf Real Real) (n := ∞)).comp
          (scalar.contMDiff_toFun.contMDiff_tangentMap
            (m := ∞) (by simp))
      convert hDerivative using 1
      funext vector
      rfl
    exact hEvaluation.comp (ghost.contMDiff.of_le (by simp))

@[simp]
theorem scalarLieDerivative_apply
    (ghost : SmoothDiffeomorphismGhost period hPeriod)
    (scalar : SmoothQuotientField period hPeriod Real)
    (point : EffectiveQuotient period hPeriod) :
    scalarLieDerivative period hPeriod ghost scalar point =
      mvfderiv coverModelWithCorners scalar.toFun point (ghost point) :=
  rfl

@[simp]
theorem scalarLieDerivative_zeroGhost
    (scalar : SmoothQuotientField period hPeriod Real) :
    scalarLieDerivative period hPeriod 0 scalar = 0 := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  change mvfderiv coverModelWithCorners scalar.toFun point 0 = 0
  exact map_zero _

theorem scalarLieDerivative_addGhost
    (first second : SmoothDiffeomorphismGhost period hPeriod)
    (scalar : SmoothQuotientField period hPeriod Real) :
    scalarLieDerivative period hPeriod (first + second) scalar =
      scalarLieDerivative period hPeriod first scalar +
        scalarLieDerivative period hPeriod second scalar := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  change mvfderiv coverModelWithCorners scalar.toFun point
      (first point + second point) =
    mvfderiv coverModelWithCorners scalar.toFun point (first point) +
      mvfderiv coverModelWithCorners scalar.toFun point (second point)
  exact map_add _ _ _

/-- The linearized diffeomorphism BRST state about a fixed scalar background.
The existing independent variation and the new tangent ghost remain distinct
slots. -/
@[ext]
structure LinearizedDiffeomorphismBRSTState where
  scalarVariation : SmoothQuotientField period hPeriod Real
  ghost : SmoothDiffeomorphismGhost period hPeriod

def zeroLinearizedBRSTState :
    LinearizedDiffeomorphismBRSTState period hPeriod where
  scalarVariation := 0
  ghost := 0

/-- Linearized BRST differential `s(deltaPhi,c) = (L_c phi,0)`. -/
def linearizedBRSTDifferential
    (background : SmoothQuotientField period hPeriod Real)
    (state : LinearizedDiffeomorphismBRSTState period hPeriod) :
    LinearizedDiffeomorphismBRSTState period hPeriod where
  scalarVariation :=
    scalarLieDerivative period hPeriod state.ghost background
  ghost := 0

/-- Exact nilpotence in the stated linearized/abelianized sector. -/
theorem linearizedBRSTDifferential_square_zero
    (background : SmoothQuotientField period hPeriod Real)
    (state : LinearizedDiffeomorphismBRSTState period hPeriod) :
    linearizedBRSTDifferential period hPeriod background
        (linearizedBRSTDifferential period hPeriod background state) =
      zeroLinearizedBRSTState period hPeriod := by
  apply LinearizedDiffeomorphismBRSTState.ext
  · exact scalarLieDerivative_zeroGhost period hPeriod background
  · rfl

/-- `IndependentFields` is extended, rather than reinterpreting its existing
`U(1)^2` ghost coefficients as tangent vectors. -/
structure IndependentFieldsWithDiffeomorphismGhost where
  fields : IndependentFields period hPeriod
  diffeomorphismGhost : SmoothDiffeomorphismGhost period hPeriod

/-- Every independent package has the canonical zero-ghost extension. -/
def zeroDiffeomorphismGhostExtension
    (fields : IndependentFields period hPeriod) :
    IndependentFieldsWithDiffeomorphismGhost period hPeriod where
  fields := fields
  diffeomorphismGhost := 0

@[simp]
theorem zeroDiffeomorphismGhostExtension_fields
    (fields : IndependentFields period hPeriod) :
    (zeroDiffeomorphismGhostExtension period hPeriod fields).fields = fields :=
  rfl

/-- Select either matter sector without changing its analytic regularity. -/
def selectMatterField
    (fields : IndependentFields period hPeriod) (sector : Fin 2) :
    SmoothQuotientField period hPeriod MatterFiber :=
  if sector = 0 then fields.matter.1 else fields.matter.2

/-- A genuine smooth scalar background selected from either matter sector of
the existing independent package. -/
def independentMatterScalar
    (fields : IndependentFields period hPeriod)
    (sector : Fin 2) (component : Fin 4) :
    SmoothQuotientField period hPeriod Real where
  toFun := fun point =>
    EuclideanSpace.proj component
      (selectMatterField period hPeriod fields sector point)
  contMDiff_toFun :=
    (EuclideanSpace.proj component).contDiff.contMDiff.comp
      (selectMatterField period hPeriod fields sector).contMDiff_toFun

/-- The extended independent package canonically supplies a linearized BRST
state with zero scalar variation and its genuine tangent ghost. -/
def independentFieldsLinearizedBRSTState
    (fields : IndependentFieldsWithDiffeomorphismGhost period hPeriod) :
    LinearizedDiffeomorphismBRSTState period hPeriod where
  scalarVariation := 0
  ghost := fields.diffeomorphismGhost

theorem independentFieldsLinearizedBRSTDifferential
    (fields : IndependentFieldsWithDiffeomorphismGhost period hPeriod)
    (sector : Fin 2) (component : Fin 4) :
    (linearizedBRSTDifferential period hPeriod
      (independentMatterScalar period hPeriod fields.fields sector component)
      (independentFieldsLinearizedBRSTState period hPeriod fields)).scalarVariation =
    scalarLieDerivative period hPeriod fields.diffeomorphismGhost
      (independentMatterScalar period hPeriod fields.fields sector component) :=
  rfl

end

end P0EFTJanusMappingTorusLinearizedDiffeomorphismBRST4D
end JanusFormal
