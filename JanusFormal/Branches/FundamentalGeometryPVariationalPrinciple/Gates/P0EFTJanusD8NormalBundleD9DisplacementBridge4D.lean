import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusSmoothNormalVectorBundle
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusD9D10ExactFieldContentBridge4D

/-!
# D8 normal-bundle displacement in the D9 field package

The normal component of the D9 local field is supplied here by an actual
smooth section of the sign-clutched D8 normal vector bundle.  Its real scalar
representative is necessarily local: it is the coordinate in a specified
valid bundle chart.  Changing the chart by one deck circuit negates that
coordinate.  The existing two `Z4` multipliers square exactly to this same
one-loop transition.

No global scalar trivialization of the nontrivial normal line is asserted.
The diffeomorphism ghost and matter/SpinC identification remain explicit.
-/

namespace JanusFormal
namespace P0EFTJanusD8NormalBundleD9DisplacementBridge4D

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusCompleteGaugeFixedEllipticSymbol
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusD9D10ExactFieldContentBridge4D

variable (period : Real) (hPeriod : Not (period = 0))

private abbrev ThroatCover :=
  MappingTorusCover (fixedEquatorData period hPeriod)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance normalCoreIsContMDiff :
    (fixedThroatNormalVectorBundleCore period hPeriod).IsContMDiff
      throatCoverModelWithCorners ω :=
  fixedThroatNormalVectorBundleCore_isContMDiff period hPeriod

/-- Genuine smooth displacements in the constructed D8 normal line. -/
abbrev SmoothNormalDisplacement :=
  ContMDiffSection throatCoverModelWithCorners Real ω
    (FixedThroatNormalFiber period hPeriod)

/-- The normal displacement space is nonempty without choosing a
trivialization: it contains the zero section. -/
def zeroNormalDisplacement : SmoothNormalDisplacement period hPeriod := 0

/-- Coordinate of a fiber element in a specified bundle chart.  The
membership proof prevents use of a partial trivialization outside its source. -/
def localNormalCoordinate
    (anchor : ThroatCover period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (_hPoint : point ∈ normalBundleBaseSet period hPeriod anchor)
    (normal : FixedThroatNormalFiber period hPeriod point) : Real :=
  ((fixedThroatNormalVectorBundleCore period hPeriod).localTriv anchor
    ⟨point, normal⟩).2

/-- Local scalar representative of a genuine smooth normal section. -/
def localNormalMode
    (displacement : SmoothNormalDisplacement period hPeriod)
    (anchor : ThroatCover period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (hPoint : point ∈ normalBundleBaseSet period hPeriod anchor) : Real :=
  localNormalCoordinate period hPeriod anchor point hPoint (displacement point)

/-- After the normal bundle is used, only the D9 diffeomorphism ghost and the
matter-to-Spinor equivalence remain as local completion data. -/
structure D9ResidualAfterNormalBundle (Spinor : Type*) where
  diffeomorphismGhost : TangentVector3
  matterSpinorIdentification : MatterFiber ≃ Spinor

/-- Convert the geometric normal section and the reduced residual data to the
older D9 completion package. -/
def d9CompletionFromNormalBundle
    {Spinor : Type*}
    (displacement : SmoothNormalDisplacement period hPeriod)
    (anchor : ThroatCover period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (hPoint : point ∈ normalBundleBaseSet period hPeriod anchor)
    (residual : D9ResidualAfterNormalBundle Spinor) :
    D9ResidualCompletion Spinor where
  normalMode := localNormalMode period hPeriod displacement anchor point hPoint
  diffeomorphismGhost := residual.diffeomorphismGhost
  matterSpinorIdentification := residual.matterSpinorIdentification

/-- Type-safe D9 local field whose normal mode comes from the actual D8 normal
bundle, while all already-established Program-P projections are reused. -/
def d9LocalFieldFromNormalBundle
    {Spinor : Type*}
    (fields : IndependentFields period hPeriod)
    (variation : IndependentFieldVariation period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (anchor : ThroatCover period hPeriod)
    (hPoint : point ∈ normalBundleBaseSet period hPeriod anchor)
    (residual : D9ResidualAfterNormalBundle Spinor) : CompleteLocalField Spinor :=
  d9LocalField period hPeriod fields variation sector column point
    (d9CompletionFromNormalBundle period hPeriod displacement anchor point hPoint residual)

@[simp] theorem d9LocalFieldFromNormalBundle_normalMode
    {Spinor : Type*}
    (fields : IndependentFields period hPeriod)
    (variation : IndependentFieldVariation period hPeriod)
    (sector : Sector) (column : Fin 2)
    (point : EffectiveThroat period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (anchor : ThroatCover period hPeriod)
    (hPoint : point ∈ normalBundleBaseSet period hPeriod anchor)
    (residual : D9ResidualAfterNormalBundle Spinor) :
    (d9LocalFieldFromNormalBundle period hPeriod fields variation sector column
      point displacement anchor hPoint residual).bosonic.normalMode =
        localNormalMode period hPeriod displacement anchor point hPoint := rfl

/-- Every point has a preferred local scalar coordinate, chosen by the bundle
core.  This is pointwise and is not claimed to vary smoothly with the point. -/
def preferredNormalMode
    (displacement : SmoothNormalDisplacement period hPeriod)
    (point : EffectiveThroat period hPeriod) : Real :=
  localNormalMode period hPeriod displacement
    (normalBundleIndexAt period hPeriod point) point
    (mem_normalBundleBaseSet_indexAt period hPeriod point)

/-- A one-loop-shifted cover anchor projects to the same throat point. -/
theorem oneLoopAnchor_projects
    (anchor : ThroatCover period hPeriod) :
    mappingTorusMk (fixedEquatorData period hPeriod) ((1 : Int) +ᵥ anchor) =
      mappingTorusMk (fixedEquatorData period hPeriod) anchor := by
  exact (mappingTorusMk_isAddQuotientCoveringMap
    (fixedEquatorData period hPeriod)).map_vadd 1

/-- The coordinate of the same genuine fiber element changes sign between
charts whose cover anchors differ by one deck circuit. -/
theorem localNormalCoordinate_oneLoop
    (anchor : ThroatCover period hPeriod)
    (normal : FixedThroatNormalFiber period hPeriod
      (mappingTorusMk (fixedEquatorData period hPeriod) anchor)) :
    let base := mappingTorusMk (fixedEquatorData period hPeriod) anchor
    let shifted := (1 : Int) +ᵥ anchor
    let hAnchor : base ∈ normalBundleBaseSet period hPeriod anchor := by
      exact (mappingTorusMk_isCoveringMap (fixedEquatorData period hPeriod)).isLocalHomeomorph
        |>.apply_self_mem_localInverseAt_source
    let hShifted : base ∈ normalBundleBaseSet period hPeriod shifted := by
      have hSelf :=
        (mappingTorusMk_isCoveringMap (fixedEquatorData period hPeriod)).isLocalHomeomorph
          |>.apply_self_mem_localInverseAt_source (x := shifted)
      rw [oneLoopAnchor_projects period hPeriod anchor] at hSelf
      exact hSelf
    localNormalCoordinate period hPeriod shifted base hShifted normal =
      -localNormalCoordinate period hPeriod anchor base hAnchor normal := by
  dsimp only
  let core := fixedThroatNormalVectorBundleCore period hPeriod
  let base := mappingTorusMk (fixedEquatorData period hPeriod) anchor
  let shifted := (1 : Int) +ᵥ anchor
  have hAnchor : base ∈ core.baseSet anchor :=
    (mappingTorusMk_isCoveringMap (fixedEquatorData period hPeriod)).isLocalHomeomorph
      |>.apply_self_mem_localInverseAt_source
  have hShifted : base ∈ core.baseSet shifted := by
    have hSelf :=
      (mappingTorusMk_isCoveringMap (fixedEquatorData period hPeriod)).isLocalHomeomorph
        |>.apply_self_mem_localInverseAt_source (x := shifted)
    rw [oneLoopAnchor_projects period hPeriod anchor] at hSelf
    exact hSelf
  change core.coordChange (core.indexAt base) shifted base normal =
    -core.coordChange (core.indexAt base) anchor base normal
  rw [← core.coordChange_comp (core.indexAt base) anchor shifted base
    ⟨⟨core.mem_baseSet_at base, hAnchor⟩, hShifted⟩ normal]
  exact one_loop_coordChange_eq_neg_id period hPeriod anchor
    (core.coordChange (core.indexAt base) anchor base normal)

/-- Either existing `Z4` lift squares to the actual one-loop transition of
the smooth D8 normal bundle, in any valid one-loop chart pair. -/
theorem z4_multiplier_squares_to_normal_oneLoop
    (choice : NormalRootChoice)
    (anchor : ThroatCover period hPeriod)
    (hAnchor : mappingTorusMk (fixedEquatorData period hPeriod) anchor ∈
      normalBundleBaseSet period hPeriod anchor)
    (hShifted : mappingTorusMk (fixedEquatorData period hPeriod) anchor ∈
      normalBundleBaseSet period hPeriod ((1 : Int) +ᵥ anchor))
    (normal : FixedThroatNormalFiber period hPeriod
      (mappingTorusMk (fixedEquatorData period hPeriod) anchor)) :
    normalRootMultiplier choice *
        (normalRootMultiplier choice *
          (localNormalCoordinate period hPeriod anchor
            (mappingTorusMk (fixedEquatorData period hPeriod) anchor)
            hAnchor normal : Complex)) =
      (localNormalCoordinate period hPeriod ((1 : Int) +ᵥ anchor)
        (mappingTorusMk (fixedEquatorData period hPeriod) anchor)
        hShifted normal : Complex) := by
  rw [← mul_assoc, normal_root_multiplier_square]
  have hSign := localNormalCoordinate_oneLoop period hPeriod anchor normal
  dsimp only at hSign
  rw [hSign]
  norm_num

/-- Exact remaining closure contract after the genuine normal displacement is
installed. -/
structure RemainingD9FieldContract (Spinor : Type*) where
  diffeomorphismGhostFromGlobalGaugeGroup :
    IndependentFieldVariation period hPeriod ->
      EffectiveThroat period hPeriod -> Sector -> TangentVector3
  matterSpinorIdentification : MatterFiber ≃ Spinor
  fullMetricDirectionsAdded : Prop
  d9FieldIsTangentOfSelectedAction : Prop
  normalSectionBoundaryDomainMatchesD9 : Prop

end

end P0EFTJanusD8NormalBundleD9DisplacementBridge4D
end JanusFormal
