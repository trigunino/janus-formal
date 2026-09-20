import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLCanonicalThroatEuclideanRellichCore4D

/-!
# Differential of the finite throat charts

This file identifies the fixed Hilbert basis with the model basis used by
the finite throat generators and computes the derivative of each inverse
preferred chart on the corresponding closed patch.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12LLCanonicalThroatChartDifferential4D

set_option autoImplicit false
noncomputable section

open Set
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusProgramPT12LLCanonicalThroatEuclideanRellichCore4D

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

/-- Fixed Hilbert basis corresponding to the model basis used by the finite
throat generators. -/
def finiteThroatGeneratorHilbertBasis :
    Module.Basis FiniteThroatGeneratorBasisIndex Real
      CanonicalThroatChartHilbertCoordinates :=
  finiteThroatGeneratorModelBasis.map
    canonicalThroatChartHilbertEquivCoverCoordinates.symm.toLinearEquiv

set_option backward.isDefEq.respectTransparency false in
/-- The selected derivatives of the global finite throat frame, assembled as
the coordinate differential on one fixed patch. -/
def finiteThroatGeneratorPatchJetCoordinateDifferential
    (patch : Patch period hPeriod) :
    (Fin (finiteSmoothThroatGeneratingFrame period hPeriod).count → Real) →ₗ[Real]
      (CanonicalThroatChartHilbertCoordinates →L[Real] Real) where
  toFun derivatives :=
    ((finiteThroatGeneratorHilbertBasis.constr Real fun basisIndex =>
      derivatives
        (finiteThroatGeneratorIndexEquivFin period hPeriod
          (patch, basisIndex))).toContinuousLinearMap)
  map_add' first second := by
    apply ContinuousLinearMap.coe_injective
    apply finiteThroatGeneratorHilbertBasis.ext
    intro basisIndex
    change
      (finiteThroatGeneratorHilbertBasis.constr Real fun index =>
        (first + second)
          (finiteThroatGeneratorIndexEquivFin period hPeriod
            (patch, index)))
          (finiteThroatGeneratorHilbertBasis basisIndex) =
        (finiteThroatGeneratorHilbertBasis.constr Real fun index =>
          first (finiteThroatGeneratorIndexEquivFin period hPeriod
            (patch, index)))
            (finiteThroatGeneratorHilbertBasis basisIndex) +
          (finiteThroatGeneratorHilbertBasis.constr Real fun index =>
            second (finiteThroatGeneratorIndexEquivFin period hPeriod
              (patch, index)))
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
      (finiteThroatGeneratorHilbertBasis.constr Real fun index =>
        (scalar • derivatives)
          (finiteThroatGeneratorIndexEquivFin period hPeriod
            (patch, index)))
          (finiteThroatGeneratorHilbertBasis basisIndex) =
        scalar *
          (finiteThroatGeneratorHilbertBasis.constr Real fun index =>
            derivatives
              (finiteThroatGeneratorIndexEquivFin period hPeriod
                (patch, index)))
            (finiteThroatGeneratorHilbertBasis basisIndex)
    rw [finiteThroatGeneratorHilbertBasis.constr_basis,
      finiteThroatGeneratorHilbertBasis.constr_basis]
    rfl

theorem finiteThroatGeneratorPatchJetCoordinateDifferential_basis
    (patch : Patch period hPeriod)
    (derivatives :
      Fin (finiteSmoothThroatGeneratingFrame period hPeriod).count → Real)
    (basisIndex : FiniteThroatGeneratorBasisIndex) :
    finiteThroatGeneratorPatchJetCoordinateDifferential
        period hPeriod patch derivatives
        (finiteThroatGeneratorHilbertBasis basisIndex) =
      derivatives
        (finiteThroatGeneratorIndexEquivFin period hPeriod
          (patch, basisIndex)) := by
  change
    (finiteThroatGeneratorHilbertBasis.constr Real fun index =>
      derivatives
        (finiteThroatGeneratorIndexEquivFin period hPeriod
          (patch, index)))
        (finiteThroatGeneratorHilbertBasis basisIndex) =
      derivatives
        (finiteThroatGeneratorIndexEquivFin period hPeriod
          (patch, basisIndex))
  exact finiteThroatGeneratorHilbertBasis.constr_basis Real _ basisIndex

/-- Open Hilbert-coordinate target of one preferred throat chart. -/
def finiteThroatGeneratorPatchHilbertChartTarget
    (patch : Patch period hPeriod) :
    Set CanonicalThroatChartHilbertCoordinates :=
  canonicalThroatChartHilbertEquivCoverCoordinates ⁻¹'
    (extChartAt throatCoverModelWithCorners patch.1).target

theorem finiteThroatGeneratorPatchHilbertChartTarget_isOpen
    (patch : Patch period hPeriod) :
    IsOpen (finiteThroatGeneratorPatchHilbertChartTarget
      period hPeriod patch) :=
  (isOpen_extChartAt_target patch.1).preimage
    canonicalThroatChartHilbertEquivCoverCoordinates.continuous

/-- Inverse preferred throat chart on the ambient Hilbert coordinate model. -/
def finiteThroatGeneratorPatchHilbertInverse
    (patch : Patch period hPeriod)
    (coordinate : CanonicalThroatChartHilbertCoordinates) :
    EffectiveThroat period hPeriod :=
  (extChartAt throatCoverModelWithCorners patch.1).symm
    (canonicalThroatChartHilbertEquivCoverCoordinates coordinate)

theorem finiteThroatGeneratorPatchHilbertInverse_coordinate
    (patch : Patch period hPeriod)
    (point : FiniteThroatGeneratorPatchDomain period hPeriod patch) :
    finiteThroatGeneratorPatchHilbertInverse period hPeriod patch
        (finiteThroatGeneratorPatchHilbertCoordinate
          period hPeriod patch point) =
      point.1 := by
  unfold finiteThroatGeneratorPatchHilbertInverse
  rw [show canonicalThroatChartHilbertEquivCoverCoordinates
      (finiteThroatGeneratorPatchHilbertCoordinate
        period hPeriod patch point) =
        extChartAt throatCoverModelWithCorners patch.1 point.1 by
    simp [finiteThroatGeneratorPatchHilbertCoordinate]]
  apply (extChartAt throatCoverModelWithCorners patch.1).left_inv
  rw [extChartAt_source,
    ← finiteThroatGeneratorOpenPatch_eq_chart_source
      period hPeriod patch]
  exact finiteThroatGeneratorClosedPatch_subset_openPatch
    period hPeriod patch point.2

theorem finiteThroatGeneratorPatchHilbertInverse_contMDiffAt
    (patch : Patch period hPeriod)
    {coordinate : CanonicalThroatChartHilbertCoordinates}
    (hCoordinate :
      coordinate ∈ finiteThroatGeneratorPatchHilbertChartTarget
        period hPeriod patch) :
    ContMDiffAt
      (modelWithCornersSelf Real CanonicalThroatChartHilbertCoordinates)
      throatCoverModelWithCorners ∞
      (finiteThroatGeneratorPatchHilbertInverse period hPeriod patch)
      coordinate := by
  have hEquiv :
      ContMDiffAt
        (modelWithCornersSelf Real CanonicalThroatChartHilbertCoordinates)
        (modelWithCornersSelf Real ThroatCoverCoordinates) ∞
        canonicalThroatChartHilbertEquivCoverCoordinates coordinate :=
    canonicalThroatChartHilbertEquivCoverCoordinates.contDiff.contDiffAt.contMDiffAt
  have hInverse :
      ContMDiffAt
        (modelWithCornersSelf Real ThroatCoverCoordinates)
        throatCoverModelWithCorners ∞
        (extChartAt throatCoverModelWithCorners patch.1).symm
        (canonicalThroatChartHilbertEquivCoverCoordinates coordinate) :=
    (contMDiffWithinAt_extChartAt_symm_target
      patch.1 hCoordinate).contMDiffAt
        ((isOpen_extChartAt_target patch.1).mem_nhds hCoordinate)
  exact hInverse.comp coordinate hEquiv

set_option backward.isDefEq.respectTransparency false in
/-- The inverse preferred chart sends each fixed Hilbert basis vector to the
corresponding unweighted local throat generator. -/
theorem finiteThroatGeneratorPatchHilbertInverse_mfderiv_basis
    (patch : Patch period hPeriod)
    (point : FiniteThroatGeneratorPatchDomain period hPeriod patch)
    (basisIndex : FiniteThroatGeneratorBasisIndex) :
    mfderiv
        (modelWithCornersSelf Real CanonicalThroatChartHilbertCoordinates)
        throatCoverModelWithCorners
        (finiteThroatGeneratorPatchHilbertInverse period hPeriod patch)
        (finiteThroatGeneratorPatchHilbertCoordinate
          period hPeriod patch point)
        (finiteThroatGeneratorHilbertBasis basisIndex) =
      finiteThroatGeneratorLocalVector
        period hPeriod patch basisIndex point.1 := by
  let coordinate :=
    finiteThroatGeneratorPatchHilbertCoordinate period hPeriod patch point
  let coverCoordinate :=
    extChartAt throatCoverModelWithCorners patch.1 point.1
  have hPointOpen :
      point.1 ∈ finiteThroatGeneratorOpenPatch
        period hPeriod patch :=
    finiteThroatGeneratorClosedPatch_subset_openPatch
      period hPeriod patch point.2
  have hTarget :
      coverCoordinate ∈
        (extChartAt throatCoverModelWithCorners patch.1).target := by
    apply (extChartAt throatCoverModelWithCorners patch.1).map_source
    rw [extChartAt_source,
      ← finiteThroatGeneratorOpenPatch_eq_chart_source
        period hPeriod patch]
    exact hPointOpen
  have hCoordinate :
      canonicalThroatChartHilbertEquivCoverCoordinates coordinate =
        coverCoordinate := by
    simp [coordinate, coverCoordinate,
      finiteThroatGeneratorPatchHilbertCoordinate]
  have hInverseCont :
      ContMDiffAt
        (modelWithCornersSelf Real ThroatCoverCoordinates)
        throatCoverModelWithCorners ∞
        (extChartAt throatCoverModelWithCorners patch.1).symm
        coverCoordinate :=
    (contMDiffWithinAt_extChartAt_symm_target
      patch.1 hTarget).contMDiffAt
        ((isOpen_extChartAt_target patch.1).mem_nhds hTarget)
  have hInverse :
      MDifferentiableAt
        (modelWithCornersSelf Real ThroatCoverCoordinates)
        throatCoverModelWithCorners
        (extChartAt throatCoverModelWithCorners patch.1).symm
        coverCoordinate :=
    hInverseCont.mdifferentiableAt (by simp)
  have hEquivCont :
      ContMDiffAt
        (modelWithCornersSelf Real CanonicalThroatChartHilbertCoordinates)
        (modelWithCornersSelf Real ThroatCoverCoordinates) ∞
        canonicalThroatChartHilbertEquivCoverCoordinates coordinate :=
    canonicalThroatChartHilbertEquivCoverCoordinates.contDiff.contDiffAt.contMDiffAt
  have hEquiv :
      MDifferentiableAt
        (modelWithCornersSelf Real CanonicalThroatChartHilbertCoordinates)
        (modelWithCornersSelf Real ThroatCoverCoordinates)
        canonicalThroatChartHilbertEquivCoverCoordinates coordinate :=
    hEquivCont.mdifferentiableAt (by simp)
  have hChain :=
    mfderiv_comp_apply coordinate
      (show MDifferentiableAt
          (modelWithCornersSelf Real ThroatCoverCoordinates)
          throatCoverModelWithCorners
          (extChartAt throatCoverModelWithCorners patch.1).symm
          (canonicalThroatChartHilbertEquivCoverCoordinates coordinate) by
        simpa [hCoordinate] using hInverse)
      hEquiv
      (finiteThroatGeneratorHilbertBasis basisIndex)
  have hEquivDerivative :
      mfderiv
          (modelWithCornersSelf Real CanonicalThroatChartHilbertCoordinates)
          (modelWithCornersSelf Real ThroatCoverCoordinates)
          canonicalThroatChartHilbertEquivCoverCoordinates coordinate
          (finiteThroatGeneratorHilbertBasis basisIndex) =
        finiteThroatGeneratorModelBasisVector basisIndex := by
    rw [mfderiv_eq_fderiv,
      canonicalThroatChartHilbertEquivCoverCoordinates.fderiv]
    change
      canonicalThroatChartHilbertEquivCoverCoordinates
          (canonicalThroatChartHilbertEquivCoverCoordinates.symm
            (finiteThroatGeneratorModelBasisVector basisIndex)) =
        finiteThroatGeneratorModelBasisVector basisIndex
    exact canonicalThroatChartHilbertEquivCoverCoordinates.apply_symm_apply _
  rw [hEquivDerivative] at hChain
  rw [hCoordinate] at hChain
  have hRange : coverCoordinate ∈ Set.range throatCoverModelWithCorners :=
    extChartAt_target_subset_range patch.1 hTarget
  have hWithin :
      mfderiv
          (modelWithCornersSelf Real ThroatCoverCoordinates)
          throatCoverModelWithCorners
          (extChartAt throatCoverModelWithCorners patch.1).symm
          coverCoordinate =
        mfderivWithin
          (modelWithCornersSelf Real ThroatCoverCoordinates)
          throatCoverModelWithCorners
          (extChartAt throatCoverModelWithCorners patch.1).symm
          (Set.range throatCoverModelWithCorners)
          coverCoordinate := by
    exact
      (mfderivWithin_eq_mfderiv
        (throatCoverModelWithCorners.uniqueMDiffOn coverCoordinate hRange)
        hInverse).symm
  rw [hWithin] at hChain
  rw [finiteThroatGeneratorLocalVector_eq_chartAt_inverseDerivative
    period hPeriod patch basisIndex point.1 hPointOpen]
  change
    mfderiv
        (modelWithCornersSelf Real CanonicalThroatChartHilbertCoordinates)
        throatCoverModelWithCorners
        ((extChartAt throatCoverModelWithCorners patch.1).symm ∘
          canonicalThroatChartHilbertEquivCoverCoordinates)
        coordinate
        (finiteThroatGeneratorHilbertBasis basisIndex) =
      mfderivWithin
        (modelWithCornersSelf Real ThroatCoverCoordinates)
        throatCoverModelWithCorners
        (extChartAt throatCoverModelWithCorners patch.1).symm
        (Set.range throatCoverModelWithCorners)
        coverCoordinate
        (finiteThroatGeneratorModelBasisVector basisIndex)
  exact hChain

theorem finiteThroatGeneratorPatchHilbertSupport_subset_chartTarget
    (patch : Patch period hPeriod) :
    finiteThroatGeneratorPatchHilbertSupport period hPeriod patch ⊆
      finiteThroatGeneratorPatchHilbertChartTarget
        period hPeriod patch := by
  rw [← finiteThroatGeneratorPatchHilbertCoordinate_range
    period hPeriod patch]
  rintro _ ⟨point, rfl⟩
  change
    canonicalThroatChartHilbertEquivCoverCoordinates
        (canonicalThroatChartHilbertEquivCoverCoordinates.symm
          (extChartAt throatCoverModelWithCorners patch.1 point.1)) ∈
    (extChartAt throatCoverModelWithCorners patch.1).target
  rw [canonicalThroatChartHilbertEquivCoverCoordinates.apply_symm_apply]
  apply (extChartAt throatCoverModelWithCorners patch.1).map_source
  rw [extChartAt_source,
    ← finiteThroatGeneratorOpenPatch_eq_chart_source
      period hPeriod patch]
  exact finiteThroatGeneratorClosedPatch_subset_openPatch
    period hPeriod patch point.2

end
end P0EFTJanusProgramPT12LLCanonicalThroatChartDifferential4D
end JanusFormal
