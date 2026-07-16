import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalLLCovariance4D

/-!
# A differential LL energy and its weak equation on the actual throat

This gate adds a first-order Dirichlet term to the already selected global LL
action.  Directional derivatives are genuine manifold derivatives along an
unconditionally constructed finite smooth spanning family of the tangent
bundle of the compact three-dimensional throat.  The existing auxiliary LL
metric field enters through the strictly positive coefficient
`1 + ‖llAuxMetric‖²`; it is therefore no longer a spectator.

The first variations with respect to both the LL flux and auxiliary metric are
derived from exact quadratic expansions.  Flux stationarity is proved
equivalent to a weak first-order Euler equation for every smooth test field.

The finite spanning-family energy is a rigorous global first-order model, but
is not yet the intrinsic Lorentzian LL action: the auxiliary matrix enters as
a positive scalar weight rather than by tensorial inverse-metric contraction,
and no integration-by-parts theorem identifying a strong divergence operator
or boundary/joint flux is claimed here.
The partition-of-unity generators are not proved PT-equivariant, so PT
covariance of this differential enrichment also remains a separate step.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusDifferentialLLWeakEquation4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Topology
open Set Bundle Module MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusPTInvolution
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusGlobalLLWorldvolume4D
open P0EFTJanusMappingTorusGlobalLLCovariance4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveThroat := MappingTorus (throatData period hPeriod)

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance effectiveThroatCompactSpace :
    CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance effectiveThroatMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance effectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

/-- A finite smooth family spanning every tangent fiber of the actual throat.
It need not be a basis, so no parallelizability assertion is hidden here. -/
structure SmoothThroatGeneratingFrame where
  count : Nat
  vectorAt : ∀ point : EffectiveThroat period hPeriod,
    Fin count → TangentSpace throatCoverModelWithCorners point
  spansAt : ∀ point : EffectiveThroat period hPeriod,
    Submodule.span Real (Set.range (vectorAt point)) = ⊤
  contMDiff_vector : ∀ index : Fin count,
    ContMDiff throatCoverModelWithCorners
      throatCoverModelWithCorners.tangent ∞
      (fun point =>
        (⟨point, vectorAt point index⟩ :
          TangentBundle throatCoverModelWithCorners
            (EffectiveThroat period hPeriod)))

private abbrev ThroatTangentFiber
    (point : EffectiveThroat period hPeriod) :=
  TangentSpace throatCoverModelWithCorners point

private abbrev throatTangentTrivialization
    (anchor : EffectiveThroat period hPeriod) :=
  trivializationAt ThroatCoverCoordinates
    (ThroatTangentFiber period hPeriod) anchor

theorem exists_finite_throat_tangent_trivialization_cover :
    ∃ anchors : Finset (EffectiveThroat period hPeriod),
      (Set.univ : Set (EffectiveThroat period hPeriod)) ⊆
        ⋃ anchor ∈ anchors,
          (throatTangentTrivialization period hPeriod anchor).baseSet := by
  apply isCompact_univ.elim_finite_subcover
  · exact fun anchor =>
      (throatTangentTrivialization period hPeriod anchor).open_baseSet
  · intro point _
    exact mem_iUnion_of_mem point
      (FiberBundle.mem_baseSet_trivializationAt' point)

private def throatCoverAnchors :
    Finset (EffectiveThroat period hPeriod) :=
  (exists_finite_throat_tangent_trivialization_cover period hPeriod).choose

private theorem throatCoverAnchors_cover :
    (Set.univ : Set (EffectiveThroat period hPeriod)) ⊆
      ⋃ anchor ∈ throatCoverAnchors period hPeriod,
        (throatTangentTrivialization period hPeriod anchor).baseSet :=
  (exists_finite_throat_tangent_trivialization_cover period hPeriod).choose_spec

private abbrev ThroatAnchor :=
  {anchor // anchor ∈ throatCoverAnchors period hPeriod}

private def throatTangentCover (anchor : ThroatAnchor period hPeriod) :
    Set (EffectiveThroat period hPeriod) :=
  (throatTangentTrivialization period hPeriod anchor.1).baseSet

private theorem throatTangentCover_isOpen
    (anchor : ThroatAnchor period hPeriod) :
    IsOpen (throatTangentCover period hPeriod anchor) :=
  (throatTangentTrivialization period hPeriod anchor.1).open_baseSet

private theorem throatTangentCover_covers :
    (Set.univ : Set (EffectiveThroat period hPeriod)) ⊆
      ⋃ anchor : ThroatAnchor period hPeriod,
        throatTangentCover period hPeriod anchor := by
  intro point hPoint
  rcases mem_iUnion₂.mp
      (throatCoverAnchors_cover period hPeriod hPoint) with
    ⟨anchor, hAnchor, hPointAnchor⟩
  exact mem_iUnion_of_mem ⟨anchor, hAnchor⟩ hPointAnchor

theorem exists_finite_throat_tangent_partition :
    ∃ partition : SmoothPartitionOfUnity (ThroatAnchor period hPeriod)
        throatCoverModelWithCorners
        (EffectiveThroat period hPeriod) Set.univ,
      partition.IsSubordinate (throatTangentCover period hPeriod) := by
  exact SmoothPartitionOfUnity.exists_isSubordinate
    throatCoverModelWithCorners isClosed_univ
    (throatTangentCover period hPeriod)
    (throatTangentCover_isOpen period hPeriod)
    (throatTangentCover_covers period hPeriod)

private def throatTangentPartition :
    SmoothPartitionOfUnity (ThroatAnchor period hPeriod)
      throatCoverModelWithCorners
      (EffectiveThroat period hPeriod) Set.univ :=
  (exists_finite_throat_tangent_partition period hPeriod).choose

private theorem throatTangentPartition_subordinate :
    (throatTangentPartition period hPeriod).IsSubordinate
      (throatTangentCover period hPeriod) :=
  (exists_finite_throat_tangent_partition period hPeriod).choose_spec

private abbrev ThroatBasisIndex :=
  Fin (Module.finrank Real ThroatCoverCoordinates)

private def throatTangentModelBasis :
    Basis ThroatBasisIndex Real ThroatCoverCoordinates :=
  Module.finBasis Real ThroatCoverCoordinates

private abbrev ThroatGeneratorIndex :=
  ThroatAnchor period hPeriod × ThroatBasisIndex

private def throatGeneratorSection
    (index : ThroatGeneratorIndex period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    ThroatTangentFiber period hPeriod point :=
  throatTangentPartition period hPeriod index.1 point •
    (throatTangentTrivialization period hPeriod index.1.1).localFrame
      throatTangentModelBasis index.2 point

private theorem throatGeneratorSection_contMDiff
    (index : ThroatGeneratorIndex period hPeriod) :
    ContMDiff throatCoverModelWithCorners
      throatCoverModelWithCorners.tangent ∞
      (fun point =>
        (⟨point, throatGeneratorSection period hPeriod index point⟩ :
          TangentBundle throatCoverModelWithCorners
            (EffectiveThroat period hPeriod))) := by
  exact ContMDiffOn.smul_section_of_tsupport
    ((throatTangentPartition period hPeriod index.1).contMDiff.contMDiffOn)
    (throatTangentCover_isOpen period hPeriod index.1)
    (throatTangentPartition_subordinate period hPeriod index.1)
    ((throatTangentTrivialization period hPeriod index.1.1).contMDiffOn_localFrame_baseSet
        (n := ∞) throatTangentModelBasis index.2)

private theorem throatGeneratorSection_spans
    (point : EffectiveThroat period hPeriod) :
    Submodule.span Real
      (Set.range (fun index : ThroatGeneratorIndex period hPeriod =>
        throatGeneratorSection period hPeriod index point)) = ⊤ := by
  obtain ⟨anchor, hAnchor⟩ :=
    (throatTangentPartition period hPeriod).exists_pos_of_mem
      (Set.mem_univ point)
  have hAnchorNe :
      throatTangentPartition period hPeriod anchor point ≠ 0 :=
    ne_of_gt hAnchor
  have hPointSupport :
      point ∈ Function.support
        (throatTangentPartition period hPeriod anchor) :=
    hAnchorNe
  have hPointBase : point ∈ throatTangentCover period hPeriod anchor :=
    throatTangentPartition_subordinate period hPeriod anchor
      (subset_closure hPointSupport)
  apply top_unique
  calc
    ⊤ ≤ Submodule.span Real
        (Set.range (fun index : ThroatBasisIndex =>
          (throatTangentTrivialization period hPeriod anchor.1).localFrame
            throatTangentModelBasis index point)) :=
      ((throatTangentTrivialization period hPeriod anchor.1).isLocalFrameOn_localFrame_baseSet
          throatCoverModelWithCorners ∞
          throatTangentModelBasis).generating hPointBase
    _ ≤ Submodule.span Real
        (Set.range (fun index : ThroatGeneratorIndex period hPeriod =>
          throatGeneratorSection period hPeriod index point)) := by
      apply Submodule.span_le.mpr
      rintro vector ⟨basisIndex, rfl⟩
      have hGenerator :
          throatGeneratorSection period hPeriod
              (anchor, basisIndex) point ∈
            Submodule.span Real
              (Set.range (fun index : ThroatGeneratorIndex period hPeriod =>
                throatGeneratorSection period hPeriod index point)) :=
        Submodule.subset_span ⟨(anchor, basisIndex), rfl⟩
      have hScaled :=
        (Submodule.span Real
          (Set.range (fun index : ThroatGeneratorIndex period hPeriod =>
            throatGeneratorSection period hPeriod index point))).smul_mem
          (throatTangentPartition period hPeriod anchor point)⁻¹ hGenerator
      simpa [throatGeneratorSection, hAnchorNe] using hScaled

private def throatGeneratorIndexEquivFin :
    ThroatGeneratorIndex period hPeriod ≃
      Fin (Fintype.card (ThroatGeneratorIndex period hPeriod)) :=
  Fintype.equivFin (ThroatGeneratorIndex period hPeriod)

/-- Unconditional finite smooth tangent generators on the actual compact
three-dimensional throat. -/
def finiteSmoothThroatGeneratingFrame :
    SmoothThroatGeneratingFrame period hPeriod where
  count := Fintype.card (ThroatGeneratorIndex period hPeriod)
  vectorAt point index :=
    throatGeneratorSection period hPeriod
      ((throatGeneratorIndexEquivFin period hPeriod).symm index) point
  spansAt point := by
    have hRange :
        Set.range
            (fun index : Fin
                (Fintype.card (ThroatGeneratorIndex period hPeriod)) =>
              throatGeneratorSection period hPeriod
                ((throatGeneratorIndexEquivFin period hPeriod).symm index)
                point) =
          Set.range
            (fun index : ThroatGeneratorIndex period hPeriod =>
              throatGeneratorSection period hPeriod index point) := by
      ext vector
      constructor
      · rintro ⟨index, rfl⟩
        exact ⟨(throatGeneratorIndexEquivFin period hPeriod).symm index, rfl⟩
      · rintro ⟨index, rfl⟩
        exact ⟨throatGeneratorIndexEquivFin period hPeriod index, by simp⟩
    rw [hRange]
    exact throatGeneratorSection_spans period hPeriod point
  contMDiff_vector index :=
    throatGeneratorSection_contMDiff period hPeriod
      ((throatGeneratorIndexEquivFin period hPeriod).symm index)

universe u

variable (Fiber : Type u)
  [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]

/-- Genuine directional derivatives of a smooth throat field along every
member of the finite spanning family. -/
def throatFrameDerivative
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (field : SmoothThroatField period hPeriod Fiber)
    (point : EffectiveThroat period hPeriod) : Fin frame.count → Fiber :=
  fun index =>
    NormedSpace.fromTangentSpace (field point)
      ((tangentMap throatCoverModelWithCorners 𝓘(Real, Fiber) field.toFun
        (⟨point, frame.vectorAt point index⟩ :
          TangentBundle throatCoverModelWithCorners
            (EffectiveThroat period hPeriod))).2)

theorem throatFrameDerivative_eq_mvfderiv
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (field : SmoothThroatField period hPeriod Fiber)
    (point : EffectiveThroat period hPeriod) (index : Fin frame.count) :
    throatFrameDerivative period hPeriod Fiber frame field point index =
      mvfderiv throatCoverModelWithCorners field.toFun point
        (frame.vectorAt point index) :=
  rfl

theorem throatFrameDerivative_contMDiff
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (field : SmoothThroatField period hPeriod Fiber) :
    ContMDiff throatCoverModelWithCorners
      𝓘(Real, Fin frame.count → Fiber) ∞
      (throatFrameDerivative period hPeriod Fiber frame field) := by
  rw [contMDiff_pi_space]
  intro index
  have hDerivative :=
    (contMDiff_snd_tangentBundle_modelSpace Fiber 𝓘(Real, Fiber)).comp
      ((field.contMDiff_toFun.contMDiff_tangentMap (by simp)).comp
        (frame.contMDiff_vector index))
  convert hDerivative using 1
  rfl

theorem throatFrameDerivative_add
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (first second : SmoothThroatField period hPeriod Fiber) :
    throatFrameDerivative period hPeriod Fiber frame (first + second) =
      throatFrameDerivative period hPeriod Fiber frame first +
        throatFrameDerivative period hPeriod Fiber frame second := by
  funext point index
  simp only [Pi.add_apply]
  rw [throatFrameDerivative_eq_mvfderiv,
    throatFrameDerivative_eq_mvfderiv,
    throatFrameDerivative_eq_mvfderiv]
  change mvfderiv throatCoverModelWithCorners
      (first.toFun + second.toFun) point
        (frame.vectorAt point index) = _
  rw [mvfderiv_add
    ((first.contMDiff_toFun.mdifferentiable (by simp)) point)
    ((second.contMDiff_toFun.mdifferentiable (by simp)) point)]
  rfl

theorem throatFrameDerivative_smul
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (scalar : Real) (field : SmoothThroatField period hPeriod Fiber) :
    throatFrameDerivative period hPeriod Fiber frame (scalar • field) =
      scalar • throatFrameDerivative period hPeriod Fiber frame field := by
  funext point index
  simp only [Pi.smul_apply]
  rw [throatFrameDerivative_eq_mvfderiv,
    throatFrameDerivative_eq_mvfderiv]
  change mvfderiv throatCoverModelWithCorners
      (scalar • field.toFun) point (frame.vectorAt point index) = _
  unfold mvfderiv
  rw [const_smul_mfderiv
    ((field.contMDiff_toFun.mdifferentiable (by simp)) point) scalar]
  rfl

/-- Frame contraction of two genuine first derivatives. -/
def throatDerivativePairing
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (first second : SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) : Real :=
  ∑ index : Fin frame.count,
    inner Real
      (throatFrameDerivative period hPeriod LLFieldFiber frame first point index)
      (throatFrameDerivative period hPeriod LLFieldFiber frame second point index)

/-- Sum of squared directional derivatives along the finite spanning family. -/
def throatDerivativeEnergy
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (field : SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) : Real :=
  ∑ index : Fin frame.count,
    ‖throatFrameDerivative period hPeriod LLFieldFiber frame field point index‖ ^ 2

theorem throatDerivativePairing_continuous
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (first second : SmoothThroatField period hPeriod LLFieldFiber) :
    Continuous (throatDerivativePairing period hPeriod frame first second) := by
  apply continuous_finsetSum
  intro index _
  exact
    ((continuous_apply index).comp
      (throatFrameDerivative_contMDiff period hPeriod LLFieldFiber frame first).continuous).inner
    ((continuous_apply index).comp
      (throatFrameDerivative_contMDiff period hPeriod LLFieldFiber frame second).continuous)

theorem throatDerivativeEnergy_continuous
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (field : SmoothThroatField period hPeriod LLFieldFiber) :
    Continuous (throatDerivativeEnergy period hPeriod frame field) := by
  apply continuous_finsetSum
  intro index _
  exact (((continuous_apply index).comp
    (throatFrameDerivative_contMDiff period hPeriod LLFieldFiber frame field).continuous).norm.pow 2)

/-- Positive kinetic coefficient extracted nontrivially from the existing
auxiliary LL metric slot. -/
def llAuxiliaryKineticWeight
    (fields : IndependentFields period hPeriod)
    (point : EffectiveThroat period hPeriod) : Real :=
  1 + ‖fields.llAuxMetric point‖ ^ 2

theorem llAuxiliaryKineticWeight_pos
    (fields : IndependentFields period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    0 < llAuxiliaryKineticWeight period hPeriod fields point := by
  unfold llAuxiliaryKineticWeight
  nlinarith [sq_nonneg ‖fields.llAuxMetric point‖]

theorem llAuxiliaryKineticWeight_continuous
    (fields : IndependentFields period hPeriod) :
    Continuous (llAuxiliaryKineticWeight period hPeriod fields) := by
  exact continuous_const.add
    (fields.llAuxMetric.contMDiff_toFun.continuous.norm.pow 2)

/-- The selected algebraic LL density plus a genuine first-order kinetic
energy on the same global throat field. -/
def differentialLLDensity
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (point : EffectiveThroat period hPeriod) : Real :=
  (1 / 2 : Real) * llAuxiliaryKineticWeight period hPeriod fields point *
      throatDerivativeEnergy period hPeriod frame fields.llField point +
    llWorldvolumeDensity period hPeriod fields point

theorem differentialLLDensity_eq_kinetic_add_selected
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    differentialLLDensity period hPeriod frame fields point =
      (1 / 2 : Real) * llAuxiliaryKineticWeight period hPeriod fields point *
          throatDerivativeEnergy period hPeriod frame fields.llField point +
        llWorldvolumeDensity period hPeriod fields point :=
  rfl

theorem differentialLLDensity_continuous
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod) :
    Continuous (differentialLLDensity period hPeriod frame fields) := by
  exact
    ((continuous_const.mul
      (llAuxiliaryKineticWeight_continuous period hPeriod fields)).mul
      (throatDerivativeEnergy_continuous period hPeriod frame
        fields.llField)).add
      (llWorldvolumeDensity_continuous period hPeriod fields)

/-- The differential LL action on the actual compact throat. -/
def globalDifferentialLLAction
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) : Real :=
  ∫ point, differentialLLDensity period hPeriod frame fields point ∂mu

theorem differentialLLDensity_integrable
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    Integrable (differentialLLDensity period hPeriod frame fields) mu := by
  exact Continuous.integrable_of_hasCompactSupport
    (differentialLLDensity_continuous period hPeriod frame fields)
    (HasCompactSupport.of_compactSpace
      (differentialLLDensity period hPeriod frame fields))

/-- Affine variation of the LL flux alone; measure and auxiliary metric remain
the same independent global fields. -/
def differentialLLFluxCurve
    (fields : IndependentFields period hPeriod)
    (direction : SmoothThroatField period hPeriod LLFieldFiber)
    (epsilon : Real) : IndependentFields period hPeriod :=
  { fields with llField := fields.llField + epsilon • direction }

/-- Weak Euler pairing produced by the differential LL density. -/
def differentialLLFluxFirstVariationDensity
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) : Real :=
  llAuxiliaryKineticWeight period hPeriod fields point *
      throatDerivativePairing period hPeriod frame fields.llField
        direction point +
    2 * fields.llMeasure point *
      inner Real (fields.llField point) (direction point)

def differentialLLFluxSecondCoefficient
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) : Real :=
  (1 / 2 : Real) * llAuxiliaryKineticWeight period hPeriod fields point *
      throatDerivativeEnergy period hPeriod frame direction point +
    fields.llMeasure point * ‖direction point‖ ^ 2

/-- Exact quadratic density expansion along every smooth LL test field. -/
theorem differentialLLDensity_fluxCurve_quadratic
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : SmoothThroatField period hPeriod LLFieldFiber)
    (epsilon : Real) (point : EffectiveThroat period hPeriod) :
    differentialLLDensity period hPeriod frame
        (differentialLLFluxCurve period hPeriod fields direction epsilon) point =
      differentialLLDensity period hPeriod frame fields point +
        epsilon * differentialLLFluxFirstVariationDensity period hPeriod
          frame fields direction point +
        epsilon ^ 2 * differentialLLFluxSecondCoefficient period hPeriod
          frame fields direction point := by
  have hDerivative (index : Fin frame.count) :
      throatFrameDerivative period hPeriod LLFieldFiber frame
          (fields.llField + epsilon • direction) point index =
        throatFrameDerivative period hPeriod LLFieldFiber frame
            fields.llField point index +
          epsilon • throatFrameDerivative period hPeriod LLFieldFiber frame
            direction point index := by
    rw [congrFun (congrFun
      (throatFrameDerivative_add period hPeriod LLFieldFiber frame
        fields.llField (epsilon • direction)) point) index]
    simp only [Pi.add_apply]
    rw [congrFun (congrFun
      (throatFrameDerivative_smul period hPeriod LLFieldFiber frame
        epsilon direction) point) index]
    simp only [Pi.smul_apply]
  unfold differentialLLDensity differentialLLFluxCurve
    llAuxiliaryKineticWeight llWorldvolumeDensity llFlux
  unfold differentialLLFluxFirstVariationDensity
    differentialLLFluxSecondCoefficient llAuxiliaryKineticWeight
  unfold throatDerivativeEnergy throatDerivativePairing
  simp_rw [hDerivative, norm_add_sq_real, real_inner_smul_right,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hFieldCurve :
      (fields.llField + epsilon • direction) point =
        fields.llField point + epsilon • direction point :=
    rfl
  rw [hFieldCurve]
  rw [norm_add_sq_real]
  simp only [real_inner_smul_right, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

theorem differentialLLFluxFirstVariationDensity_continuous
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : SmoothThroatField period hPeriod LLFieldFiber) :
    Continuous (differentialLLFluxFirstVariationDensity period hPeriod
      frame fields direction) := by
  exact
    ((llAuxiliaryKineticWeight_continuous period hPeriod fields).mul
      (throatDerivativePairing_continuous period hPeriod frame
        fields.llField direction)).add
      ((continuous_const.mul fields.llMeasure.contMDiff_toFun.continuous).mul
        (fields.llField.contMDiff_toFun.continuous.inner
          direction.contMDiff_toFun.continuous))

theorem differentialLLFluxSecondCoefficient_continuous
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : SmoothThroatField period hPeriod LLFieldFiber) :
    Continuous (differentialLLFluxSecondCoefficient period hPeriod
      frame fields direction) := by
  exact
    ((continuous_const.mul
      (llAuxiliaryKineticWeight_continuous period hPeriod fields)).mul
      (throatDerivativeEnergy_continuous period hPeriod frame direction)).add
      (fields.llMeasure.contMDiff_toFun.continuous.mul
        (direction.contMDiff_toFun.continuous.norm.pow 2))

/-- Integrated weak Euler pairing. -/
def globalDifferentialLLFluxFirstVariation
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) : Real :=
  ∫ point, differentialLLFluxFirstVariationDensity period hPeriod
    frame fields direction point ∂mu

private def globalDifferentialLLFluxSecondCoefficient
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) : Real :=
  ∫ point, differentialLLFluxSecondCoefficient period hPeriod
    frame fields direction point ∂mu

private theorem continuous_real_integrable
    (function : EffectiveThroat period hPeriod → Real)
    (hContinuous : Continuous function)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    Integrable function mu :=
  hContinuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace function)

/-- Exact quadratic expansion of the global differential action. -/
theorem globalDifferentialLLAction_fluxCurve_quadratic
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu]
    (epsilon : Real) :
    globalDifferentialLLAction period hPeriod frame
        (differentialLLFluxCurve period hPeriod fields direction epsilon) mu =
      globalDifferentialLLAction period hPeriod frame fields mu +
        epsilon * globalDifferentialLLFluxFirstVariation period hPeriod
          frame fields direction mu +
        epsilon ^ 2 * globalDifferentialLLFluxSecondCoefficient period hPeriod
          frame fields direction mu := by
  have hBase := differentialLLDensity_integrable period hPeriod frame fields mu
  have hFirst := continuous_real_integrable period hPeriod
    (differentialLLFluxFirstVariationDensity period hPeriod
      frame fields direction)
    (differentialLLFluxFirstVariationDensity_continuous period hPeriod
      frame fields direction) mu
  have hSecond := continuous_real_integrable period hPeriod
    (differentialLLFluxSecondCoefficient period hPeriod
      frame fields direction)
    (differentialLLFluxSecondCoefficient_continuous period hPeriod
      frame fields direction) mu
  unfold globalDifferentialLLAction
    globalDifferentialLLFluxFirstVariation
    globalDifferentialLLFluxSecondCoefficient
  simp_rw [differentialLLDensity_fluxCurve_quadratic period hPeriod
    frame fields direction epsilon]
  calc
    (∫ point,
        differentialLLDensity period hPeriod frame fields point +
            epsilon * differentialLLFluxFirstVariationDensity period hPeriod
              frame fields direction point +
          epsilon ^ 2 * differentialLLFluxSecondCoefficient period hPeriod
            frame fields direction point ∂mu) =
        (∫ point,
          differentialLLDensity period hPeriod frame fields point +
            epsilon * differentialLLFluxFirstVariationDensity period hPeriod
              frame fields direction point ∂mu) +
          ∫ point, epsilon ^ 2 *
            differentialLLFluxSecondCoefficient period hPeriod
              frame fields direction point ∂mu := by
      simpa only [Pi.add_apply] using
        integral_add (hBase.add (hFirst.const_mul epsilon))
          (hSecond.const_mul (epsilon ^ 2))
    _ = ((∫ point, differentialLLDensity period hPeriod frame fields point ∂mu) +
          ∫ point, epsilon *
            differentialLLFluxFirstVariationDensity period hPeriod
              frame fields direction point ∂mu) +
          ∫ point, epsilon ^ 2 *
            differentialLLFluxSecondCoefficient period hPeriod
              frame fields direction point ∂mu := by
      exact congrArg (fun value => value +
          ∫ point, epsilon ^ 2 *
            differentialLLFluxSecondCoefficient period hPeriod
              frame fields direction point ∂mu)
        (by
          simpa only [Pi.add_apply] using
            integral_add hBase (hFirst.const_mul epsilon))
    _ = _ := by
      simp only [integral_const_mul]

private theorem quadratic_scalar_hasDerivAt
    (base linear quadratic : Real) :
    HasDerivAt
      (fun epsilon : Real => base + epsilon * linear + epsilon ^ 2 * quadratic)
      linear 0 := by
  have hAffine : HasDerivAt
      (fun epsilon : Real => base + epsilon * linear) linear 0 := by
    have h := (hasDerivAt_id (0 : Real)).mul_const linear |>.const_add base
    exact h.congr_deriv (one_mul linear)
  have hSquare : HasDerivAt (fun epsilon : Real => epsilon * epsilon) 0 0 := by
    have h := (hasDerivAt_id (0 : Real)).mul (hasDerivAt_id (0 : Real))
    exact h.congr_deriv (by norm_num)
  have hQuadratic : HasDerivAt
      (fun epsilon : Real => epsilon * epsilon * quadratic) 0 0 := by
    exact (hSquare.mul_const quadratic).congr_deriv (by ring)
  have hTotal := hAffine.add hQuadratic
  exact (hTotal.congr_deriv (by ring)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun epsilon => by
      simp only [Pi.add_apply]
      ring)

/-- Actual first derivative of the global differential LL action. -/
theorem globalDifferentialLLAction_fluxCurve_hasDerivAt
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    HasDerivAt
      (fun epsilon : Real => globalDifferentialLLAction period hPeriod frame
        (differentialLLFluxCurve period hPeriod fields direction epsilon) mu)
      (globalDifferentialLLFluxFirstVariation period hPeriod
        frame fields direction mu) 0 := by
  rw [show (fun epsilon : Real => globalDifferentialLLAction period hPeriod frame
      (differentialLLFluxCurve period hPeriod fields direction epsilon) mu) =
      (fun epsilon : Real =>
        globalDifferentialLLAction period hPeriod frame fields mu +
          epsilon * globalDifferentialLLFluxFirstVariation period hPeriod
            frame fields direction mu +
          epsilon ^ 2 * globalDifferentialLLFluxSecondCoefficient period hPeriod
            frame fields direction mu) from by
      funext epsilon
      exact globalDifferentialLLAction_fluxCurve_quadratic period hPeriod
        frame fields direction mu epsilon]
  exact quadratic_scalar_hasDerivAt
    (globalDifferentialLLAction period hPeriod frame fields mu)
    (globalDifferentialLLFluxFirstVariation period hPeriod
      frame fields direction mu)
    (globalDifferentialLLFluxSecondCoefficient period hPeriod
      frame fields direction mu)

/-- Variational stationarity of the actual differential action. -/
def DifferentialLLFluxStationary
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) : Prop :=
  ∀ direction : SmoothThroatField period hPeriod LLFieldFiber,
    HasDerivAt
      (fun epsilon : Real => globalDifferentialLLAction period hPeriod frame
        (differentialLLFluxCurve period hPeriod fields direction epsilon) mu)
      0 0

/-- Genuine weak first-order LL equation on the global throat: the derived
Euler pairing vanishes against every smooth LL test field. -/
def SatisfiesWeakDifferentialLLEquation
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) : Prop :=
  ∀ direction : SmoothThroatField period hPeriod LLFieldFiber,
    globalDifferentialLLFluxFirstVariation period hPeriod
      frame fields direction mu = 0

/-- The weak PDE is derived from, and exactly equivalent to, stationarity of
the enriched global action.  It is not assumed in the action data. -/
theorem differentialLLFluxStationary_iff_weakEquation
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    DifferentialLLFluxStationary period hPeriod frame fields mu ↔
      SatisfiesWeakDifferentialLLEquation period hPeriod frame fields mu := by
  constructor
  · intro hStationary direction
    have hDerived := globalDifferentialLLAction_fluxCurve_hasDerivAt
      period hPeriod frame fields direction mu
    have hZero := hStationary direction
    exact hDerived.unique hZero
  · intro hWeak direction
    simpa [hWeak direction] using
      (globalDifferentialLLAction_fluxCurve_hasDerivAt
        period hPeriod frame fields direction mu)

/-- Unconditional specialization to the explicitly constructed finite smooth
spanning family on the same compact throat. -/
theorem actualThroatDifferentialLLStationary_iff_weakEquation
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    DifferentialLLFluxStationary period hPeriod
        (finiteSmoothThroatGeneratingFrame period hPeriod) fields mu ↔
      SatisfiesWeakDifferentialLLEquation period hPeriod
        (finiteSmoothThroatGeneratingFrame period hPeriod) fields mu :=
  differentialLLFluxStationary_iff_weakEquation period hPeriod
    (finiteSmoothThroatGeneratingFrame period hPeriod) fields mu

/-- Affine variation of the auxiliary LL metric while the measure and flux are
held fixed. -/
def differentialLLAuxMetricCurve
    (fields : IndependentFields period hPeriod)
    (direction : SmoothThroatField period hPeriod LLMetricFiber)
    (epsilon : Real) : IndependentFields period hPeriod :=
  { fields with
    llAuxMetric := fields.llAuxMetric + epsilon • direction }

/-- The actual first variation with respect to the auxiliary metric slot. -/
def differentialLLAuxMetricFirstVariationDensity
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : SmoothThroatField period hPeriod LLMetricFiber)
    (point : EffectiveThroat period hPeriod) : Real :=
  inner Real (fields.llAuxMetric point) (direction point) *
    throatDerivativeEnergy period hPeriod frame fields.llField point

def differentialLLAuxMetricSecondCoefficient
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : SmoothThroatField period hPeriod LLMetricFiber)
    (point : EffectiveThroat period hPeriod) : Real :=
  (1 / 2 : Real) * ‖direction point‖ ^ 2 *
    throatDerivativeEnergy period hPeriod frame fields.llField point

/-- Exact auxiliary-metric expansion.  This proves that the new action has a
real, generally nonzero response in the slot that was absent before. -/
theorem differentialLLDensity_auxMetricCurve_quadratic
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : SmoothThroatField period hPeriod LLMetricFiber)
    (epsilon : Real) (point : EffectiveThroat period hPeriod) :
    differentialLLDensity period hPeriod frame
        (differentialLLAuxMetricCurve period hPeriod
          fields direction epsilon) point =
      differentialLLDensity period hPeriod frame fields point +
        epsilon * differentialLLAuxMetricFirstVariationDensity period hPeriod
          frame fields direction point +
        epsilon ^ 2 * differentialLLAuxMetricSecondCoefficient period hPeriod
          frame fields direction point := by
  have hAuxCurve :
      (fields.llAuxMetric + epsilon • direction) point =
        fields.llAuxMetric point + epsilon • direction point :=
    rfl
  unfold differentialLLDensity differentialLLAuxMetricCurve
    llAuxiliaryKineticWeight llWorldvolumeDensity llFlux
  unfold differentialLLAuxMetricFirstVariationDensity
    differentialLLAuxMetricSecondCoefficient
  rw [hAuxCurve, norm_add_sq_real]
  simp only [real_inner_smul_right, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs]
  ring

theorem differentialLLAuxMetricFirstVariationDensity_continuous
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : SmoothThroatField period hPeriod LLMetricFiber) :
    Continuous (differentialLLAuxMetricFirstVariationDensity period hPeriod
      frame fields direction) := by
  exact
    (fields.llAuxMetric.contMDiff_toFun.continuous.inner
      direction.contMDiff_toFun.continuous).mul
      (throatDerivativeEnergy_continuous period hPeriod frame fields.llField)

theorem differentialLLAuxMetricSecondCoefficient_continuous
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : SmoothThroatField period hPeriod LLMetricFiber) :
    Continuous (differentialLLAuxMetricSecondCoefficient period hPeriod
      frame fields direction) := by
  exact
    ((continuous_const.mul
      (direction.contMDiff_toFun.continuous.norm.pow 2)).mul
      (throatDerivativeEnergy_continuous period hPeriod frame fields.llField))

theorem differentialLLAuxMetric_selfVariation_pos
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (hAux : fields.llAuxMetric point ≠ 0)
    (hEnergy : 0 < throatDerivativeEnergy period hPeriod
      frame fields.llField point) :
    0 < differentialLLAuxMetricFirstVariationDensity period hPeriod
      frame fields fields.llAuxMetric point := by
  unfold differentialLLAuxMetricFirstVariationDensity
  rw [real_inner_self_eq_norm_sq]
  exact mul_pos (pow_pos (norm_pos_iff.mpr hAux) 2) hEnergy

def globalDifferentialLLAuxMetricFirstVariation
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : SmoothThroatField period hPeriod LLMetricFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) : Real :=
  ∫ point, differentialLLAuxMetricFirstVariationDensity period hPeriod
    frame fields direction point ∂mu

private def globalDifferentialLLAuxMetricSecondCoefficient
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : SmoothThroatField period hPeriod LLMetricFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) : Real :=
  ∫ point, differentialLLAuxMetricSecondCoefficient period hPeriod
    frame fields direction point ∂mu

theorem globalDifferentialLLAction_auxMetricCurve_quadratic
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : SmoothThroatField period hPeriod LLMetricFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu]
    (epsilon : Real) :
    globalDifferentialLLAction period hPeriod frame
        (differentialLLAuxMetricCurve period hPeriod
          fields direction epsilon) mu =
      globalDifferentialLLAction period hPeriod frame fields mu +
        epsilon * globalDifferentialLLAuxMetricFirstVariation period hPeriod
          frame fields direction mu +
        epsilon ^ 2 *
          globalDifferentialLLAuxMetricSecondCoefficient period hPeriod
            frame fields direction mu := by
  have hBase := differentialLLDensity_integrable period hPeriod frame fields mu
  have hFirst := continuous_real_integrable period hPeriod
    (differentialLLAuxMetricFirstVariationDensity period hPeriod
      frame fields direction)
    (differentialLLAuxMetricFirstVariationDensity_continuous period hPeriod
      frame fields direction) mu
  have hSecond := continuous_real_integrable period hPeriod
    (differentialLLAuxMetricSecondCoefficient period hPeriod
      frame fields direction)
    (differentialLLAuxMetricSecondCoefficient_continuous period hPeriod
      frame fields direction) mu
  unfold globalDifferentialLLAction
    globalDifferentialLLAuxMetricFirstVariation
    globalDifferentialLLAuxMetricSecondCoefficient
  simp_rw [differentialLLDensity_auxMetricCurve_quadratic period hPeriod
    frame fields direction epsilon]
  calc
    (∫ point,
        differentialLLDensity period hPeriod frame fields point +
            epsilon *
              differentialLLAuxMetricFirstVariationDensity period hPeriod
                frame fields direction point +
          epsilon ^ 2 *
            differentialLLAuxMetricSecondCoefficient period hPeriod
              frame fields direction point ∂mu) =
        (∫ point,
          differentialLLDensity period hPeriod frame fields point +
            epsilon *
              differentialLLAuxMetricFirstVariationDensity period hPeriod
                frame fields direction point ∂mu) +
          ∫ point, epsilon ^ 2 *
            differentialLLAuxMetricSecondCoefficient period hPeriod
              frame fields direction point ∂mu := by
      simpa only [Pi.add_apply] using
        integral_add (hBase.add (hFirst.const_mul epsilon))
          (hSecond.const_mul (epsilon ^ 2))
    _ = ((∫ point, differentialLLDensity period hPeriod frame fields point ∂mu) +
          ∫ point, epsilon *
            differentialLLAuxMetricFirstVariationDensity period hPeriod
              frame fields direction point ∂mu) +
          ∫ point, epsilon ^ 2 *
            differentialLLAuxMetricSecondCoefficient period hPeriod
              frame fields direction point ∂mu := by
      exact congrArg (fun value => value +
          ∫ point, epsilon ^ 2 *
            differentialLLAuxMetricSecondCoefficient period hPeriod
              frame fields direction point ∂mu)
        (by
          simpa only [Pi.add_apply] using
            integral_add hBase (hFirst.const_mul epsilon))
    _ = _ := by
      simp only [integral_const_mul]

/-- Actual integrated derivative with respect to the auxiliary metric. -/
theorem globalDifferentialLLAction_auxMetricCurve_hasDerivAt
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : SmoothThroatField period hPeriod LLMetricFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    HasDerivAt
      (fun epsilon : Real => globalDifferentialLLAction period hPeriod frame
        (differentialLLAuxMetricCurve period hPeriod
          fields direction epsilon) mu)
      (globalDifferentialLLAuxMetricFirstVariation period hPeriod
        frame fields direction mu) 0 := by
  rw [show (fun epsilon : Real => globalDifferentialLLAction period hPeriod frame
      (differentialLLAuxMetricCurve period hPeriod
        fields direction epsilon) mu) =
      (fun epsilon : Real =>
        globalDifferentialLLAction period hPeriod frame fields mu +
          epsilon * globalDifferentialLLAuxMetricFirstVariation period hPeriod
            frame fields direction mu +
          epsilon ^ 2 *
            globalDifferentialLLAuxMetricSecondCoefficient period hPeriod
              frame fields direction mu) from by
      funext epsilon
      exact globalDifferentialLLAction_auxMetricCurve_quadratic period hPeriod
        frame fields direction mu epsilon]
  exact quadratic_scalar_hasDerivAt
    (globalDifferentialLLAction period hPeriod frame fields mu)
    (globalDifferentialLLAuxMetricFirstVariation period hPeriod
      frame fields direction mu)
    (globalDifferentialLLAuxMetricSecondCoefficient period hPeriod
      frame fields direction mu)

end

end P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
end JanusFormal
