import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLCanonicalThroatChartDifferential4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLCanonicalThroatLocalFrameH1Control4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusLocalScalarGradientDifferentialBridge4D
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Smooth finite-chart localization on the LL throat

One LL field is multiplied by a finite throat partition weight, projected to
one of its four scalar components, pulled back to the preferred Hilbert chart,
and extended smoothly by zero.  Its Euclidean differential is identified with
the unweighted local throat derivatives of the cut field.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12LLCanonicalThroatSmoothLocalization4D

set_option autoImplicit false
noncomputable section

open Set Filter
open scoped Manifold ContDiff ENNReal
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricLLWeakEulerJacobiOperator4D
open P0EFTJanusProgramPT12LLCanonicalFrameH1Control4D
open P0EFTJanusProgramPT12LLCanonicalThroatEuclideanRellichCore4D
open P0EFTJanusProgramPT12LLCanonicalThroatLocalFrameH1Control4D
open P0EFTJanusProgramPT12LLCanonicalThroatChartDifferential4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev Patch :=
  FiniteThroatGeneratorPatch period hPeriod

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- Pointwise projection to one scalar coordinate of the LL fiber. -/
def llFieldComponentProjection (component : Fin 4) :
    LLFieldFiber →L[Real] Real :=
  PiLp.proj (2 : ENNReal) (fun _ : Fin 4 => Real) component

@[simp]
theorem llFieldComponentProjection_apply
    (component : Fin 4) (value : LLFieldFiber) :
    llFieldComponentProjection component value = value component :=
  rfl

/-- The smooth LL field localized by one genuine partition weight. -/
def finiteThroatGeneratorPatchCutField
    (patch : Patch period hPeriod)
    (field : LLWeakTestSpace period hPeriod) :
    LLWeakTestSpace period hPeriod :=
  llSmoothCutoff period hPeriod
    (finiteThroatGeneratorCutoff period hPeriod patch) field

/-- One scalar component of the partition-localized LL field. -/
def finiteThroatGeneratorPatchCutComponent
    (patch : Patch period hPeriod)
    (component : Fin 4)
    (field : LLWeakTestSpace period hPeriod) :
    SmoothThroatField period hPeriod Real where
  toFun :=
    llFieldComponentProjection component ∘
      (finiteThroatGeneratorPatchCutField
        period hPeriod patch field).toFun
  contMDiff_toFun :=
    (llFieldComponentProjection component).contDiff.contMDiff.comp
      (finiteThroatGeneratorPatchCutField
        period hPeriod patch field).contMDiff_toFun

@[simp]
theorem finiteThroatGeneratorPatchCutComponent_apply
    (patch : Patch period hPeriod)
    (component : Fin 4)
    (field : LLWeakTestSpace period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    finiteThroatGeneratorPatchCutComponent
        period hPeriod patch component field point =
      finiteThroatGeneratorWeight period hPeriod patch point *
        field point component := by
  rfl

theorem finiteThroatGeneratorPatchCutField_tsupport_subset
    (patch : Patch period hPeriod)
    (field : LLWeakTestSpace period hPeriod) :
    tsupport
        (finiteThroatGeneratorPatchCutField
          period hPeriod patch field).toFun ⊆
      finiteThroatGeneratorClosedPatch period hPeriod patch := by
  simpa [finiteThroatGeneratorPatchCutField,
    finiteThroatGeneratorClosedPatch,
    finiteThroatGeneratorCutoff] using
      (llSmoothCutoff_tsupport_subset period hPeriod
        (finiteThroatGeneratorCutoff period hPeriod patch) field)

theorem finiteThroatGeneratorPatchCutComponent_tsupport_subset
    (patch : Patch period hPeriod)
    (component : Fin 4)
    (field : LLWeakTestSpace period hPeriod) :
    tsupport
        (finiteThroatGeneratorPatchCutComponent
          period hPeriod patch component field).toFun ⊆
      finiteThroatGeneratorClosedPatch period hPeriod patch := by
  apply (closure_mono ?_).trans
    (finiteThroatGeneratorPatchCutField_tsupport_subset
      period hPeriod patch field)
  intro point hPoint hZero
  apply hPoint
  simp [finiteThroatGeneratorPatchCutComponent, hZero]

/-- One cut LL component in the preferred Euclidean chart, extended by zero
off the chart target. -/
def finiteThroatGeneratorPatchLocalizedCoordinateFunction
    (patch : Patch period hPeriod)
    (component : Fin 4)
    (field : LLWeakTestSpace period hPeriod) :
    CanonicalThroatChartHilbertCoordinates → Real :=
  (finiteThroatGeneratorPatchHilbertChartTarget
    period hPeriod patch).indicator
      (fun coordinate =>
        finiteThroatGeneratorPatchCutComponent
          period hPeriod patch component field
          (finiteThroatGeneratorPatchHilbertInverse
            period hPeriod patch coordinate))

theorem finiteThroatGeneratorPatchLocalizedCoordinateFunction_eventuallyEq
    (patch : Patch period hPeriod)
    (component : Fin 4)
    (field : LLWeakTestSpace period hPeriod)
    {coordinate : CanonicalThroatChartHilbertCoordinates}
    (hCoordinate :
      coordinate ∈ finiteThroatGeneratorPatchHilbertChartTarget
        period hPeriod patch) :
    finiteThroatGeneratorPatchLocalizedCoordinateFunction
        period hPeriod patch component field =ᶠ[nhds coordinate]
      fun current =>
        finiteThroatGeneratorPatchCutComponent
          period hPeriod patch component field
          (finiteThroatGeneratorPatchHilbertInverse
            period hPeriod patch current) := by
  filter_upwards
    [(finiteThroatGeneratorPatchHilbertChartTarget_isOpen
      period hPeriod patch).mem_nhds hCoordinate] with current hCurrent
  simp [finiteThroatGeneratorPatchLocalizedCoordinateFunction,
    Set.indicator_of_mem hCurrent]

theorem finiteThroatGeneratorPatchLocalizedCoordinateFunction_support
    (patch : Patch period hPeriod)
    (component : Fin 4)
    (field : LLWeakTestSpace period hPeriod) :
    Function.support
        (finiteThroatGeneratorPatchLocalizedCoordinateFunction
          period hPeriod patch component field) ⊆
      finiteThroatGeneratorPatchHilbertSupport
        period hPeriod patch := by
  intro coordinate hCoordinate
  have hTarget :
      coordinate ∈ finiteThroatGeneratorPatchHilbertChartTarget
        period hPeriod patch := by
    by_contra hNotTarget
    exact hCoordinate (by
      simp [finiteThroatGeneratorPatchLocalizedCoordinateFunction,
        Set.indicator_of_notMem hNotTarget])
  have hCutComponent :
      finiteThroatGeneratorPatchCutComponent
          period hPeriod patch component field
          (finiteThroatGeneratorPatchHilbertInverse
            period hPeriod patch coordinate) ≠ 0 := by
    have hExpanded :
        coordinate ∈ finiteThroatGeneratorPatchHilbertChartTarget
              period hPeriod patch ∧
          finiteThroatGeneratorPatchCutComponent
              period hPeriod patch component field
              (finiteThroatGeneratorPatchHilbertInverse
                period hPeriod patch coordinate) ≠ 0 := by
      simpa [finiteThroatGeneratorPatchLocalizedCoordinateFunction] using
        hCoordinate
    exact hExpanded.2
  have hPatch :
      finiteThroatGeneratorPatchHilbertInverse
          period hPeriod patch coordinate ∈
        finiteThroatGeneratorClosedPatch period hPeriod patch :=
    finiteThroatGeneratorPatchCutComponent_tsupport_subset
      period hPeriod patch component field
      (subset_closure hCutComponent)
  rw [← finiteThroatGeneratorPatchHilbertCoordinate_range
    period hPeriod patch]
  refine ⟨⟨finiteThroatGeneratorPatchHilbertInverse
    period hPeriod patch coordinate, hPatch⟩, ?_⟩
  change
    canonicalThroatChartHilbertEquivCoverCoordinates.symm
        (extChartAt throatCoverModelWithCorners patch.1
          (finiteThroatGeneratorPatchHilbertInverse
            period hPeriod patch coordinate)) =
      coordinate
  rw [show extChartAt throatCoverModelWithCorners patch.1
      (finiteThroatGeneratorPatchHilbertInverse
        period hPeriod patch coordinate) =
        canonicalThroatChartHilbertEquivCoverCoordinates coordinate by
    exact (extChartAt throatCoverModelWithCorners patch.1).right_inv hTarget]
  exact canonicalThroatChartHilbertEquivCoverCoordinates.symm_apply_apply coordinate

theorem finiteThroatGeneratorPatchLocalizedCoordinateFunction_tsupport
    (patch : Patch period hPeriod)
    (component : Fin 4)
    (field : LLWeakTestSpace period hPeriod) :
    tsupport
        (finiteThroatGeneratorPatchLocalizedCoordinateFunction
          period hPeriod patch component field) ⊆
      finiteThroatGeneratorPatchHilbertSupport period hPeriod patch :=
  closure_minimal
    (finiteThroatGeneratorPatchLocalizedCoordinateFunction_support
      period hPeriod patch component field)
    (finiteThroatGeneratorPatchHilbertSupport_isCompact
      period hPeriod patch).isClosed

theorem finiteThroatGeneratorPatchLocalizedCoordinateFunction_coordinate
    (patch : Patch period hPeriod)
    (point : FiniteThroatGeneratorPatchDomain period hPeriod patch)
    (component : Fin 4)
    (field : LLWeakTestSpace period hPeriod) :
    finiteThroatGeneratorPatchLocalizedCoordinateFunction
        period hPeriod patch component field
        (finiteThroatGeneratorPatchHilbertCoordinate
          period hPeriod patch point) =
      finiteThroatGeneratorWeight period hPeriod patch point.1 *
        field point.1 component := by
  have hCoordinate :
      finiteThroatGeneratorPatchHilbertCoordinate
          period hPeriod patch point ∈
        finiteThroatGeneratorPatchHilbertChartTarget
          period hPeriod patch := by
    apply finiteThroatGeneratorPatchHilbertSupport_subset_chartTarget
      period hPeriod patch
    rw [← finiteThroatGeneratorPatchHilbertCoordinate_range
      period hPeriod patch]
    exact ⟨point, rfl⟩
  simp [finiteThroatGeneratorPatchLocalizedCoordinateFunction,
    Set.indicator_of_mem hCoordinate,
    finiteThroatGeneratorPatchHilbertInverse_coordinate
      period hPeriod patch point]

theorem finiteThroatGeneratorPatchLocalizedCoordinateFunction_contDiff
    (patch : Patch period hPeriod)
    (component : Fin 4)
    (field : LLWeakTestSpace period hPeriod) :
    ContDiff Real ∞
      (finiteThroatGeneratorPatchLocalizedCoordinateFunction
        period hPeriod patch component field) := by
  rw [← contMDiff_iff_contDiff]
  apply contMDiff_of_tsupport
  intro coordinate hCoordinate
  have hSupport :
      coordinate ∈ finiteThroatGeneratorPatchHilbertSupport
        period hPeriod patch :=
    finiteThroatGeneratorPatchLocalizedCoordinateFunction_tsupport
      period hPeriod patch component field hCoordinate
  have hTarget :
      coordinate ∈ finiteThroatGeneratorPatchHilbertChartTarget
        period hPeriod patch :=
    finiteThroatGeneratorPatchHilbertSupport_subset_chartTarget
      period hPeriod patch hSupport
  have hInverse :=
    finiteThroatGeneratorPatchHilbertInverse_contMDiffAt
      period hPeriod patch hTarget
  have hLocal :
      ContMDiffAt
        (modelWithCornersSelf Real CanonicalThroatChartHilbertCoordinates)
        𝓘(Real, Real) ∞
        (fun current =>
          finiteThroatGeneratorPatchCutComponent
            period hPeriod patch component field
            (finiteThroatGeneratorPatchHilbertInverse
              period hPeriod patch current)) coordinate :=
    (finiteThroatGeneratorPatchCutComponent
      period hPeriod patch component field).contMDiff_toFun.contMDiffAt.comp
        coordinate hInverse
  apply hLocal.congr_of_eventuallyEq
  filter_upwards
    [(finiteThroatGeneratorPatchHilbertChartTarget_isOpen
      period hPeriod patch).mem_nhds hTarget] with current hCurrent
  simp [finiteThroatGeneratorPatchLocalizedCoordinateFunction,
    Set.indicator_of_mem hCurrent]

/-- Constant smooth LL field used to isolate one localized partition weight. -/
def smoothLLConstantOne : LLWeakTestSpace period hPeriod where
  toFun := fun _ =>
    (PiLp.continuousLinearEquiv (2 : ENNReal) Real
      (fun _ : Fin 4 => Real)).symm (fun _ => 1)
  contMDiff_toFun := contMDiff_const

@[simp]
theorem smoothLLConstantOne_apply
    (point : EffectiveThroat period hPeriod)
    (component : Fin 4) :
    smoothLLConstantOne period hPeriod point component = 1 :=
  rfl

/-- The partition weight in the preferred Hilbert chart, extended smoothly
by zero. -/
def finiteThroatGeneratorPatchLocalizedWeight
    (patch : Patch period hPeriod) :
    CanonicalThroatChartHilbertCoordinates → Real :=
  finiteThroatGeneratorPatchLocalizedCoordinateFunction
    period hPeriod patch (0 : Fin 4)
      (smoothLLConstantOne period hPeriod)

theorem finiteThroatGeneratorPatchLocalizedWeight_contDiff
    (patch : Patch period hPeriod) :
    ContDiff Real ∞
      (finiteThroatGeneratorPatchLocalizedWeight
        period hPeriod patch) :=
  finiteThroatGeneratorPatchLocalizedCoordinateFunction_contDiff
    period hPeriod patch (0 : Fin 4)
      (smoothLLConstantOne period hPeriod)

theorem finiteThroatGeneratorPatchLocalizedWeight_coordinate
    (patch : Patch period hPeriod)
    (point : FiniteThroatGeneratorPatchDomain period hPeriod patch) :
    finiteThroatGeneratorPatchLocalizedWeight period hPeriod patch
        (finiteThroatGeneratorPatchHilbertCoordinate
          period hPeriod patch point) =
      finiteThroatGeneratorWeight period hPeriod patch point.1 := by
  simp [finiteThroatGeneratorPatchLocalizedWeight,
    finiteThroatGeneratorPatchLocalizedCoordinateFunction_coordinate]

set_option backward.isDefEq.respectTransparency false in
/-- The derivative of a scalar pullback in a fixed Hilbert-basis direction is
the intrinsic derivative along the corresponding local throat vector. -/
theorem finiteThroatGeneratorPatchScalarPullback_fderiv_basis
    (patch : Patch period hPeriod)
    (point : FiniteThroatGeneratorPatchDomain period hPeriod patch)
    (scalarField : SmoothThroatField period hPeriod Real)
    (basisIndex : FiniteThroatGeneratorBasisIndex) :
    fderiv Real
        (fun coordinate =>
          scalarField (finiteThroatGeneratorPatchHilbertInverse
            period hPeriod patch coordinate))
        (finiteThroatGeneratorPatchHilbertCoordinate
          period hPeriod patch point)
        (finiteThroatGeneratorHilbertBasis basisIndex) =
      mvfderiv throatCoverModelWithCorners scalarField.toFun point.1
        (finiteThroatGeneratorLocalVector
          period hPeriod patch basisIndex point.1) := by
  let coordinate :=
    finiteThroatGeneratorPatchHilbertCoordinate
      period hPeriod patch point
  have hCoordinate :
      coordinate ∈ finiteThroatGeneratorPatchHilbertChartTarget
        period hPeriod patch := by
    apply finiteThroatGeneratorPatchHilbertSupport_subset_chartTarget
      period hPeriod patch
    rw [← finiteThroatGeneratorPatchHilbertCoordinate_range
      period hPeriod patch]
    exact ⟨point, rfl⟩
  have hInverse :=
    (finiteThroatGeneratorPatchHilbertInverse_contMDiffAt
      period hPeriod patch hCoordinate).mdifferentiableAt (by simp)
  have hField :
      MDifferentiableAt throatCoverModelWithCorners 𝓘(Real, Real)
        scalarField.toFun
        (finiteThroatGeneratorPatchHilbertInverse
          period hPeriod patch coordinate) :=
    scalarField.contMDiff_toFun.mdifferentiableAt (by simp)
  have hChain :=
    mfderiv_comp_apply coordinate hField hInverse
      (finiteThroatGeneratorHilbertBasis basisIndex)
  dsimp only [coordinate] at hChain
  rw [finiteThroatGeneratorPatchHilbertInverse_coordinate
    period hPeriod patch point] at hChain
  have hInverseBasis :=
    finiteThroatGeneratorPatchHilbertInverse_mfderiv_basis
      period hPeriod patch point basisIndex
  calc
    fderiv Real
          (fun current =>
            scalarField (finiteThroatGeneratorPatchHilbertInverse
              period hPeriod patch current))
          (finiteThroatGeneratorPatchHilbertCoordinate
            period hPeriod patch point)
          (finiteThroatGeneratorHilbertBasis basisIndex) =
        mfderiv
          (modelWithCornersSelf Real
            CanonicalThroatChartHilbertCoordinates)
          𝓘(Real, Real)
          (scalarField.toFun ∘
            finiteThroatGeneratorPatchHilbertInverse
              period hPeriod patch)
          (finiteThroatGeneratorPatchHilbertCoordinate
            period hPeriod patch point)
          (finiteThroatGeneratorHilbertBasis basisIndex) := by
      rw [mfderiv_eq_fderiv]
      rfl
    _ =
        mfderiv throatCoverModelWithCorners 𝓘(Real, Real)
          scalarField.toFun point.1
          (mfderiv
            (modelWithCornersSelf Real
              CanonicalThroatChartHilbertCoordinates)
            throatCoverModelWithCorners
            (finiteThroatGeneratorPatchHilbertInverse
              period hPeriod patch)
            (finiteThroatGeneratorPatchHilbertCoordinate
              period hPeriod patch point)
            (finiteThroatGeneratorHilbertBasis basisIndex)) :=
      hChain
    _ =
        mfderiv throatCoverModelWithCorners 𝓘(Real, Real)
          scalarField.toFun point.1
          (finiteThroatGeneratorLocalVector
            period hPeriod patch basisIndex point.1) := by
      rw [hInverseBasis]
    _ =
        mvfderiv throatCoverModelWithCorners scalarField.toFun point.1
          (finiteThroatGeneratorLocalVector
            period hPeriod patch basisIndex point.1) :=
      rfl

/-- Basis derivative of one cut LL component in Hilbert coordinates. -/
theorem finiteThroatGeneratorPatchCutComponentPullback_fderiv_basis
    (patch : Patch period hPeriod)
    (point : FiniteThroatGeneratorPatchDomain period hPeriod patch)
    (component : Fin 4)
    (field : LLWeakTestSpace period hPeriod)
    (basisIndex : FiniteThroatGeneratorBasisIndex) :
    fderiv Real
        (fun coordinate =>
          finiteThroatGeneratorPatchCutComponent
            period hPeriod patch component field
            (finiteThroatGeneratorPatchHilbertInverse
              period hPeriod patch coordinate))
        (finiteThroatGeneratorPatchHilbertCoordinate
          period hPeriod patch point)
        (finiteThroatGeneratorHilbertBasis basisIndex) =
      finiteThroatGeneratorLocalDerivative
        period hPeriod Real
        (finiteThroatGeneratorPatchCutComponent
          period hPeriod patch component field)
        patch basisIndex point.1 := by
  simpa [finiteThroatGeneratorLocalDerivative] using
    (finiteThroatGeneratorPatchScalarPullback_fderiv_basis
      period hPeriod patch point
      (finiteThroatGeneratorPatchCutComponent
        period hPeriod patch component field) basisIndex)

/-- Scalar local differentiation commutes with projection to an LL fiber
component. -/
theorem finiteThroatGeneratorPatchCutComponent_localDerivative
    (patch : Patch period hPeriod)
    (component : Fin 4)
    (field : LLWeakTestSpace period hPeriod)
    (basisIndex : FiniteThroatGeneratorBasisIndex)
    (point : EffectiveThroat period hPeriod) :
    finiteThroatGeneratorLocalDerivative
        period hPeriod Real
        (finiteThroatGeneratorPatchCutComponent
          period hPeriod patch component field)
        patch basisIndex point =
      finiteThroatGeneratorLocalDerivative
        period hPeriod LLFieldFiber
        (finiteThroatGeneratorPatchCutField
          period hPeriod patch field)
        patch basisIndex point component := by
  let cutField :=
    finiteThroatGeneratorPatchCutField period hPeriod patch field
  let projection := llFieldComponentProjection component
  let tangent :=
    finiteThroatGeneratorLocalVector
      period hPeriod patch basisIndex point
  have hField :
      MDifferentiableAt throatCoverModelWithCorners
        𝓘(Real, LLFieldFiber) cutField.toFun point :=
    cutField.contMDiff_toFun.mdifferentiableAt (by simp)
  have hProjection :
      MDifferentiableAt 𝓘(Real, LLFieldFiber) 𝓘(Real, Real)
        projection (cutField point) :=
    projection.differentiableAt.mdifferentiableAt
  have hChain :=
    mfderiv_comp_apply point hProjection hField tangent
  rw [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv] at hChain
  unfold finiteThroatGeneratorLocalDerivative
  change
    mfderiv throatCoverModelWithCorners 𝓘(Real, Real)
        (projection ∘ cutField.toFun) point tangent =
      projection
        (mfderiv throatCoverModelWithCorners 𝓘(Real, LLFieldFiber)
          cutField.toFun point tangent)
  exact hChain

/-- Linear assembly of the three local chart derivatives into a covector on
the Hilbert coordinate model. -/
def finiteThroatGeneratorPatchLocalCoordinateDifferential
    (_patch : Patch period hPeriod) :
    (FiniteThroatGeneratorBasisIndex → Real) →ₗ[Real]
      (CanonicalThroatChartHilbertCoordinates →L[Real] Real) where
  toFun derivatives :=
    (finiteThroatGeneratorHilbertBasis.constr Real derivatives).toContinuousLinearMap
  map_add' first second := by
    apply ContinuousLinearMap.coe_injective
    apply finiteThroatGeneratorHilbertBasis.ext
    intro basisIndex
    change
      (finiteThroatGeneratorHilbertBasis.constr Real (first + second))
          (finiteThroatGeneratorHilbertBasis basisIndex) =
        (finiteThroatGeneratorHilbertBasis.constr Real first)
            (finiteThroatGeneratorHilbertBasis basisIndex) +
          (finiteThroatGeneratorHilbertBasis.constr Real second)
            (finiteThroatGeneratorHilbertBasis basisIndex)
    rw [finiteThroatGeneratorHilbertBasis.constr_basis,
      finiteThroatGeneratorHilbertBasis.constr_basis,
      finiteThroatGeneratorHilbertBasis.constr_basis]
    rfl
  map_smul' scalar derivatives := by
    apply ContinuousLinearMap.coe_injective
    apply finiteThroatGeneratorHilbertBasis.ext
    intro basisIndex
    change
      (finiteThroatGeneratorHilbertBasis.constr Real
          (scalar • derivatives))
          (finiteThroatGeneratorHilbertBasis basisIndex) =
        scalar *
          (finiteThroatGeneratorHilbertBasis.constr Real derivatives)
            (finiteThroatGeneratorHilbertBasis basisIndex)
    rw [finiteThroatGeneratorHilbertBasis.constr_basis,
      finiteThroatGeneratorHilbertBasis.constr_basis]
    rfl

theorem finiteThroatGeneratorPatchLocalCoordinateDifferential_basis
    (patch : Patch period hPeriod)
    (derivatives : FiniteThroatGeneratorBasisIndex → Real)
    (basisIndex : FiniteThroatGeneratorBasisIndex) :
    finiteThroatGeneratorPatchLocalCoordinateDifferential
        period hPeriod patch derivatives
        (finiteThroatGeneratorHilbertBasis basisIndex) =
      derivatives basisIndex := by
  exact finiteThroatGeneratorHilbertBasis.constr_basis Real _ basisIndex

/-- Fixed bounded conversion from the three local chart derivatives to the
Euclidean Hilbert-coordinate gradient. -/
def finiteThroatGeneratorPatchLocalCoordinateGradient
    (patch : Patch period hPeriod) :
    (FiniteThroatGeneratorBasisIndex → Real) →L[Real]
      CanonicalThroatChartHilbertCoordinates :=
  (InnerProductSpace.toDual Real
      CanonicalThroatChartHilbertCoordinates).symm.toContinuousLinearMap.comp
    (finiteThroatGeneratorPatchLocalCoordinateDifferential
      period hPeriod patch).toContinuousLinearMap

set_option backward.isDefEq.respectTransparency false in
/-- The full Frechet differential of a localized LL component is assembled
from its three unweighted local throat derivatives. -/
theorem finiteThroatGeneratorPatchLocalizedCoordinateFunction_fderiv
    (patch : Patch period hPeriod)
    (point : FiniteThroatGeneratorPatchDomain period hPeriod patch)
    (component : Fin 4)
    (field : LLWeakTestSpace period hPeriod) :
    fderiv Real
        (finiteThroatGeneratorPatchLocalizedCoordinateFunction
          period hPeriod patch component field)
        (finiteThroatGeneratorPatchHilbertCoordinate
          period hPeriod patch point) =
      finiteThroatGeneratorPatchLocalCoordinateDifferential
        period hPeriod patch
        (fun basisIndex =>
          finiteThroatGeneratorLocalDerivative
            period hPeriod Real
            (finiteThroatGeneratorPatchCutComponent
              period hPeriod patch component field)
            patch basisIndex point.1) := by
  apply ContinuousLinearMap.coe_injective
  apply finiteThroatGeneratorHilbertBasis.ext
  intro basisIndex
  change
    fderiv Real
        (finiteThroatGeneratorPatchLocalizedCoordinateFunction
          period hPeriod patch component field)
        (finiteThroatGeneratorPatchHilbertCoordinate
          period hPeriod patch point)
        (finiteThroatGeneratorHilbertBasis basisIndex) =
      finiteThroatGeneratorPatchLocalCoordinateDifferential
          period hPeriod patch
          (fun index =>
            finiteThroatGeneratorLocalDerivative
              period hPeriod Real
              (finiteThroatGeneratorPatchCutComponent
                period hPeriod patch component field)
              patch index point.1)
        (finiteThroatGeneratorHilbertBasis basisIndex)
  have hCoordinate :
      finiteThroatGeneratorPatchHilbertCoordinate
          period hPeriod patch point ∈
        finiteThroatGeneratorPatchHilbertChartTarget
          period hPeriod patch := by
    apply finiteThroatGeneratorPatchHilbertSupport_subset_chartTarget
      period hPeriod patch
    rw [← finiteThroatGeneratorPatchHilbertCoordinate_range
      period hPeriod patch]
    exact ⟨point, rfl⟩
  have hLocalized :=
    finiteThroatGeneratorPatchLocalizedCoordinateFunction_eventuallyEq
      period hPeriod patch component field hCoordinate
  rw [hLocalized.fderiv_eq]
  change
    fderiv Real
        (fun coordinate =>
          finiteThroatGeneratorPatchCutComponent
            period hPeriod patch component field
            (finiteThroatGeneratorPatchHilbertInverse
              period hPeriod patch coordinate))
        (finiteThroatGeneratorPatchHilbertCoordinate
          period hPeriod patch point)
        (finiteThroatGeneratorHilbertBasis basisIndex) =
      finiteThroatGeneratorPatchLocalCoordinateDifferential
          period hPeriod patch
          (fun index =>
            finiteThroatGeneratorLocalDerivative
              period hPeriod Real
              (finiteThroatGeneratorPatchCutComponent
                period hPeriod patch component field)
              patch index point.1)
        (finiteThroatGeneratorHilbertBasis basisIndex)
  rw [finiteThroatGeneratorPatchCutComponentPullback_fderiv_basis
      period hPeriod patch point component field basisIndex,
    finiteThroatGeneratorPatchLocalCoordinateDifferential_basis]

/-- Euclidean gradient of the localized LL component in terms of the three
unweighted local throat derivatives. -/
theorem finiteThroatGeneratorPatchLocalizedCoordinateFunction_grad
    (patch : Patch period hPeriod)
    (point : FiniteThroatGeneratorPatchDomain period hPeriod patch)
    (component : Fin 4)
    (field : LLWeakTestSpace period hPeriod) :
    RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.grad
        (E := CanonicalThroatChartHilbertCoordinates)
        (finiteThroatGeneratorPatchLocalizedCoordinateFunction
          period hPeriod patch component field)
        (finiteThroatGeneratorPatchHilbertCoordinate
          period hPeriod patch point) =
      finiteThroatGeneratorPatchLocalCoordinateGradient
        period hPeriod patch
        (fun basisIndex =>
          finiteThroatGeneratorLocalDerivative
            period hPeriod Real
            (finiteThroatGeneratorPatchCutComponent
              period hPeriod patch component field)
            patch basisIndex point.1) := by
  simp only [
    RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.grad]
  rw [finiteThroatGeneratorPatchLocalizedCoordinateFunction_fderiv
    period hPeriod patch point component field]
  simp [finiteThroatGeneratorPatchLocalCoordinateGradient]
  rfl

end
end P0EFTJanusProgramPT12LLCanonicalThroatSmoothLocalization4D
end JanusFormal
