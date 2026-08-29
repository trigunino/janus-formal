import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusD8NonabelianGhostThroatBRST4D

/-!
# The weak LL Jacobi operator and the throat rotation generator

The existing throat BRST construction supplies three genuine smooth rotation
ghosts.  Their natural linear action on the LL flux is the vector-valued Lie
derivative defined below.

The flux-only weak Jacobi operator does not form a nontrivial gauge complex
with this action in the positive LL-measure sector.  Its quadratic form is
strictly positive there, hence the operator is injective.  Consequently
`J ∘ R = 0` holds exactly when `R = 0`.  A nontrivial rotation complex must
therefore use the simultaneous Hessian in which the auxiliary metric, measure,
frame, and LL flux all transform.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusLLWeakJacobiGaugeComplex4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Topology
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusGlobalLLCovariance4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLHessian4D
open P0EFTJanusMappingTorusPTSymmetricLLWeakEulerJacobiOperator4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusMappingTorusD8NonabelianGhostLinearFullFieldBRST4D
open P0EFTJanusMappingTorusD8NonabelianGhostThroatBRST4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveThroat := MappingTorus (throatData period hPeriod)

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance effectiveThroatCompactSpace :
    CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance effectiveThroatMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance effectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

/-- Vector-valued Lie derivative of an LL test field along a genuine smooth
throat ghost.  This is the real, ghost-number-zero part of the scalar action
used by the existing throat BRST differential. -/
def llWeakLieDerivative
    (ghost : CInfinityThroatGhost period hPeriod)
    (field : LLWeakTestSpace period hPeriod) :
    LLWeakTestSpace period hPeriod where
  toFun point :=
    (EuclideanSpace.equiv (Fin 4) Real).symm
      (fun index =>
        throatScalarLieDerivative period hPeriod ghost
          (smoothThroatEuclideanCoordinate period hPeriod field index) point)
  contMDiff_toFun := by
    apply
      (EuclideanSpace.equiv (Fin 4) Real).symm.toContinuousLinearMap.contMDiff.comp
    rw [contMDiff_pi_space]
    intro index
    exact
      (throatScalarLieDerivative period hPeriod ghost
        (smoothThroatEuclideanCoordinate period hPeriod field index)).contMDiff

@[simp]
theorem llWeakLieDerivative_apply_coordinate
    (ghost : CInfinityThroatGhost period hPeriod)
    (field : LLWeakTestSpace period hPeriod)
    (point : EffectiveThroat period hPeriod) (index : Fin 4) :
    (EuclideanSpace.equiv (Fin 4) Real)
        (llWeakLieDerivative period hPeriod ghost field point) index =
      throatScalarLieDerivative period hPeriod ghost
        (smoothThroatEuclideanCoordinate period hPeriod field index) point :=
  rfl

theorem llWeakLieDerivative_add
    (ghost : CInfinityThroatGhost period hPeriod)
    (first second : LLWeakTestSpace period hPeriod) :
    llWeakLieDerivative period hPeriod ghost (first + second) =
      llWeakLieDerivative period hPeriod ghost first +
        llWeakLieDerivative period hPeriod ghost second := by
  apply SmoothThroatField.ext period hPeriod LLFieldFiber
  intro point
  apply (EuclideanSpace.equiv (Fin 4) Real).injective
  funext index
  have hCoordinate :
      smoothThroatEuclideanCoordinate period hPeriod
          (first + second) index =
        smoothThroatEuclideanCoordinate period hPeriod first index +
          smoothThroatEuclideanCoordinate period hPeriod second index := by
    apply ContMDiffMap.ext
    intro current
    rfl
  change throatScalarLieDerivative period hPeriod ghost
      (smoothThroatEuclideanCoordinate period hPeriod
        (first + second) index) point = _
  rw [hCoordinate,
    throatScalarLieDerivative_addScalar period hPeriod]
  rfl

theorem llWeakLieDerivative_smul
    (ghost : CInfinityThroatGhost period hPeriod)
    (scalar : Real) (field : LLWeakTestSpace period hPeriod) :
    llWeakLieDerivative period hPeriod ghost (scalar • field) =
      scalar • llWeakLieDerivative period hPeriod ghost field := by
  apply SmoothThroatField.ext period hPeriod LLFieldFiber
  intro point
  apply (EuclideanSpace.equiv (Fin 4) Real).injective
  funext index
  have hCoordinate :
      smoothThroatEuclideanCoordinate period hPeriod
          (scalar • field) index =
        scalar •
          smoothThroatEuclideanCoordinate period hPeriod field index := by
    apply ContMDiffMap.ext
    intro current
    rfl
  change throatScalarLieDerivative period hPeriod ghost
      (smoothThroatEuclideanCoordinate period hPeriod
        (scalar • field) index) point = _
  rw [hCoordinate,
    throatScalarLieDerivative_smulScalar period hPeriod]
  rfl

/-- Natural linear LL-flux generator associated with a genuine throat ghost. -/
def llWeakGaugeGenerator
    (ghost : CInfinityThroatGhost period hPeriod) :
    LLWeakTestSpace period hPeriod →ₗ[Real]
      LLWeakTestSpace period hPeriod where
  toFun := llWeakLieDerivative period hPeriod ghost
  map_add' := llWeakLieDerivative_add period hPeriod ghost
  map_smul' := llWeakLieDerivative_smul period hPeriod ghost

/-- The three natural LL-flux generators furnished by the true throat
rotation ghosts. -/
def llWeakRotationGaugeGenerator
    (axis : Fin 3) :
    LLWeakTestSpace period hPeriod →ₗ[Real]
      LLWeakTestSpace period hPeriod :=
  llWeakGaugeGenerator period hPeriod
    (throatSpatialRotationGhost period hPeriod axis)

@[simp]
theorem llWeakRotationGaugeGenerator_apply
    (axis : Fin 3) (field : LLWeakTestSpace period hPeriod) :
    llWeakRotationGaugeGenerator period hPeriod axis field =
      llWeakLieDerivative period hPeriod
        (throatSpatialRotationGhost period hPeriod axis) field :=
  rfl

/-- Strict positivity of the already constructed LL energy form makes the
flux-only weak Jacobi operator injective. -/
theorem weakLLJacobiOperator_injective_of_positive_llMeasure
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure mu] [Measure.IsOpenPosMeasure mu]
    (hMeasure : ∀ point, 0 < fields.llMeasure point) :
    Function.Injective
      (weakLLJacobiOperator period hPeriod frame fields mu) := by
  intro first second hImage
  by_contra hDifferent
  have hDirection : first - second ≠ 0 :=
    sub_ne_zero.mpr hDifferent
  have hPositive :
      0 < weakLLJacobiOperator period hPeriod frame fields mu
        (first - second) (first - second) := by
    rw [weakLLJacobiOperator_apply]
    exact
      globalPTSymmetricDifferentialLLFluxHessian_self_pos_of_measure
        period hPeriod frame fields (first - second) mu
        hMeasure hDirection
  have hZero :
      weakLLJacobiOperator period hPeriod frame fields mu
        (first - second) (first - second) = 0 := by
    have hOuter :
        weakLLJacobiOperator period hPeriod frame fields mu
            (first - second) = 0 := by
      rw [map_sub, hImage, sub_self]
    rw [hOuter]
    rfl
  exact hPositive.ne' hZero

/-- Exact no-go/reduction theorem: in the positive LL-measure sector, a
linear flux generator forms a weak Jacobi complex precisely when it vanishes. -/
theorem weakLLJacobiOperator_comp_eq_zero_iff
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure mu] [Measure.IsOpenPosMeasure mu]
    (hMeasure : ∀ point, 0 < fields.llMeasure point)
    (generator : LLWeakTestSpace period hPeriod →ₗ[Real]
      LLWeakTestSpace period hPeriod) :
    (weakLLJacobiOperator period hPeriod frame fields mu).comp generator = 0 ↔
      generator = 0 := by
  constructor
  · intro hComplex
    apply LinearMap.ext
    intro direction
    apply weakLLJacobiOperator_injective_of_positive_llMeasure
      period hPeriod frame fields mu hMeasure
    have hAt := congrArg
      (fun operator => operator direction) hComplex
    simpa using hAt
  · rintro rfl
    simp

@[simp]
theorem weakLLJacobiOperator_comp_llWeakRotationGaugeGenerator_apply
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu]
    (axis : Fin 3) (direction test : LLWeakTestSpace period hPeriod) :
    ((weakLLJacobiOperator period hPeriod frame fields mu).comp
        (llWeakRotationGaugeGenerator period hPeriod axis)) direction test =
      globalPTSymmetricDifferentialLLFluxHessian period hPeriod
        frame fields
        (llWeakLieDerivative period hPeriod
          (throatSpatialRotationGhost period hPeriod axis) direction)
        test mu :=
  rfl

/-- Specialization of the no-go to each of the three genuine throat rotation
generators. -/
theorem weakLLJacobiOperator_comp_llWeakRotationGaugeGenerator_eq_zero_iff
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure mu] [Measure.IsOpenPosMeasure mu]
    (hMeasure : ∀ point, 0 < fields.llMeasure point)
    (axis : Fin 3) :
    (weakLLJacobiOperator period hPeriod frame fields mu).comp
        (llWeakRotationGaugeGenerator period hPeriod axis) = 0 ↔
      llWeakRotationGaugeGenerator period hPeriod axis = 0 :=
  weakLLJacobiOperator_comp_eq_zero_iff
    period hPeriod frame fields mu hMeasure
      (llWeakRotationGaugeGenerator period hPeriod axis)

theorem weakLLJacobiOperator_comp_llWeakRotationGaugeGenerator_ne_zero
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure mu] [Measure.IsOpenPosMeasure mu]
    (hMeasure : ∀ point, 0 < fields.llMeasure point)
    (axis : Fin 3)
    (hNontrivial :
      llWeakRotationGaugeGenerator period hPeriod axis ≠ 0) :
    (weakLLJacobiOperator period hPeriod frame fields mu).comp
        (llWeakRotationGaugeGenerator period hPeriod axis) ≠ 0 := by
  intro hComplex
  exact hNontrivial
    ((weakLLJacobiOperator_comp_llWeakRotationGaugeGenerator_eq_zero_iff
      period hPeriod frame fields mu hMeasure axis).mp hComplex)

end

end P0EFTJanusMappingTorusLLWeakJacobiGaugeComplex4D
end JanusFormal
