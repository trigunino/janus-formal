import JanusFormal.Branches.FundamentalGeometryD10QuillenAnomaly.Gates.P0EFTJanusCircleDeterminantLineFamily
import JanusFormal.Branches.FundamentalGeometryDiracSpectral.Gates.P0EFTJanusCircleHolonomyEta
import Mathlib.Topology.VectorBundle.Constructions

/-!
# Topological determinant bundle of the bounded circle family

The preceding circle gate constructs the actual algebraic Fredholm determinant
fibers and a nonzero Fourier frame in every fiber.  Here that frame is used to
put the transported complex topology on every fiber and to register the
dependent total space as a genuine Mathlib `FiberBundle` and `VectorBundle`
over the closed holonomy interval.

The endpoint fibers are still glued by the exact large-gauge equivalence, not
by identifying their underlying types.  The Fourier frame is nowhere zero;
it must not be confused with the regularized determinant section, whose
coordinate is `2 sin (pi a)` and which vanishes at the crossing endpoints.

This is a topological circle-family result.  It does not construct a Quillen
metric, connection, curvature, or Bismut--Freed holonomy.
-/

namespace JanusFormal
namespace P0EFTJanusCircleDeterminantTopologicalBundle

set_option autoImplicit false

noncomputable section

open Bundle
open Topology
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusCircleBoundedTransformSpectralFlow
open P0EFTJanusCircleDeterminantLineFamily
open P0EFTJanusCircleHolonomyEta

/-! ## Fourier coordinates on the actual determinant fibers -/

/-- Scalar multiplication of the nonzero Fourier frame. -/
noncomputable def circleDeterminantFrameMap
    (fold : Fold) (twist : CircleTwist) :
    ℂ →ₗ[ℂ] CircleBoundedDeterminantLine fold twist :=
  LinearMap.toSpanSingleton ℂ _ (circleDeterminantFourierFrame fold twist)

theorem circleDeterminantFrameMap_injective
    (fold : Fold) (twist : CircleTwist) :
    Function.Injective (circleDeterminantFrameMap fold twist) := by
  have hKer : LinearMap.ker (circleDeterminantFrameMap fold twist) = ⊥ := by
    change LinearMap.ker (LinearMap.toSpanSingleton ℂ _
      (circleDeterminantFourierFrame fold twist)) = ⊥
    exact LinearMap.ker_toSpanSingleton ℂ
      (circleDeterminantFourierFrame_ne_zero fold twist)
  intro first second hEqual
  apply sub_eq_zero.mp
  have hMem : first - second ∈
      LinearMap.ker (circleDeterminantFrameMap fold twist) := by
    rw [LinearMap.mem_ker, map_sub, hEqual, sub_self]
  have hBot : first - second ∈ (⊥ : Submodule ℂ ℂ) := hKer ▸ hMem
  simpa using hBot

theorem circleDeterminantFrameMap_surjective
    (fold : Fold) (twist : CircleTwist) :
    Function.Surjective (circleDeterminantFrameMap fold twist) := by
  intro value
  obtain ⟨scalar, hScalar⟩ :=
    (finrank_eq_one_iff_of_nonzero'
      (circleDeterminantFourierFrame fold twist)
      (circleDeterminantFourierFrame_ne_zero fold twist)).mp
        (circleBoundedDeterminantLine_finrank_one fold twist) value
  exact ⟨scalar, by
    simpa [circleDeterminantFrameMap] using hScalar⟩

/-- Fourier-frame linear coordinates on the actual determinant-line fiber. -/
noncomputable def circleDeterminantFrameEquiv
    (fold : Fold) (twist : CircleTwist) :
    ℂ ≃ₗ[ℂ] CircleBoundedDeterminantLine fold twist :=
  LinearEquiv.ofBijective (circleDeterminantFrameMap fold twist)
    ⟨circleDeterminantFrameMap_injective fold twist,
      circleDeterminantFrameMap_surjective fold twist⟩

@[simp] theorem circleDeterminantFrameEquiv_one
    (fold : Fold) (twist : CircleTwist) :
    circleDeterminantFrameEquiv fold twist 1 =
    circleDeterminantFourierFrame fold twist := by
  simp [circleDeterminantFrameEquiv, circleDeterminantFrameMap]

/-- The topology transported from `ℂ` by the Fourier-frame equivalence. -/
noncomputable instance circleBoundedDeterminantLineTopology
    (fold : Fold) (twist : CircleTwist) :
    TopologicalSpace (CircleBoundedDeterminantLine fold twist) :=
  TopologicalSpace.induced
    (circleDeterminantFrameEquiv fold twist).symm inferInstance

theorem circleDeterminantFrameEquiv_symm_isInducing
    (fold : Fold) (twist : CircleTwist) :
    IsInducing (circleDeterminantFrameEquiv fold twist).symm := by
  exact ⟨rfl⟩

/-- The fiber coordinate is a homeomorphism for the transported topology. -/
noncomputable def circleDeterminantFrameHomeomorph
    (fold : Fold) (twist : CircleTwist) :
    CircleBoundedDeterminantLine fold twist ≃ₜ ℂ :=
  (circleDeterminantFrameEquiv fold twist).symm.toEquiv.toHomeomorphOfIsInducing
    (circleDeterminantFrameEquiv_symm_isInducing fold twist)

/-! ## A genuine dependent vector bundle over the holonomy interval -/

abbrev CircleDeterminantFiber (fold : Fold) (twist : CircleTwist) :=
  CircleBoundedDeterminantLine fold twist

/-- Global pretrivialization supplied by the Fourier frame. -/
noncomputable def circleDeterminantPretrivialization (fold : Fold) :
    Pretrivialization ℂ (π ℂ (CircleDeterminantFiber fold)) where
  toFun point :=
    (point.proj, (circleDeterminantFrameEquiv fold point.proj).symm point.2)
  invFun coordinate :=
    ⟨coordinate.1, circleDeterminantFrameEquiv fold coordinate.1 coordinate.2⟩
  source := Set.univ
  target := Set.univ
  map_source' _ _ := Set.mem_univ _
  map_target' _ _ := Set.mem_univ _
  left_inv' point _ := by
    cases point
    simp
  right_inv' coordinate _ := by
    simp
  open_target := isOpen_univ
  baseSet := Set.univ
  open_baseSet := isOpen_univ
  source_eq := by simp
  target_eq := by simp
  proj_toFun _ _ := rfl

theorem circleDeterminantPretrivialization_isLinear (fold : Fold) :
    (circleDeterminantPretrivialization fold).IsLinear ℂ where
  linear twist _ := (circleDeterminantFrameEquiv fold twist).symm.isLinear

/-- Vector-prebundle data on the actual dependent determinant fibers. -/
noncomputable def circleDeterminantVectorPrebundle (fold : Fold) :
    VectorPrebundle ℂ ℂ (CircleDeterminantFiber fold) where
  pretrivializationAtlas := {circleDeterminantPretrivialization fold}
  pretrivialization_linear' := by
    intro e he
    rw [Set.mem_singleton_iff.mp he]
    exact circleDeterminantPretrivialization_isLinear fold
  pretrivializationAt := fun _ => circleDeterminantPretrivialization fold
  mem_base_pretrivializationAt := by simp [circleDeterminantPretrivialization]
  pretrivialization_mem_atlas := by simp
  exists_coordChange := by
    intro first hFirst second hSecond
    rw [Set.mem_singleton_iff.mp hFirst, Set.mem_singleton_iff.mp hSecond]
    refine ⟨fun _ => ContinuousLinearMap.id ℂ ℂ, continuousOn_const, ?_⟩
    intro twist _ scalar
    simp [circleDeterminantPretrivialization]
  totalSpaceMk_isInducing := by
    intro twist
    change IsInducing (fun value : CircleDeterminantFiber fold twist =>
      (twist, (circleDeterminantFrameEquiv fold twist).symm value))
    exact isInducing_const_prod.2
      (circleDeterminantFrameEquiv_symm_isInducing fold twist)

/-- Total-space topology induced by the Fourier-frame trivialization. -/
noncomputable instance circleDeterminantTotalSpaceTopology (fold : Fold) :
    TopologicalSpace (TotalSpace ℂ (CircleDeterminantFiber fold)) :=
  (circleDeterminantVectorPrebundle fold).totalSpaceTopology

/-- Registered Mathlib fiber-bundle structure on the actual dependent fibers. -/
noncomputable instance circleDeterminantFiberBundle (fold : Fold) :
    FiberBundle ℂ (CircleDeterminantFiber fold) :=
  (circleDeterminantVectorPrebundle fold).toFiberBundle

/-- Registered Mathlib complex vector-bundle structure. -/
noncomputable instance circleDeterminantVectorBundle (fold : Fold) :
    VectorBundle ℂ ℂ (CircleDeterminantFiber fold) :=
  (circleDeterminantVectorPrebundle fold).toVectorBundle

/-! ## The exact large-gauge transition is topological -/

/-- The exact endpoint transition written in the Fourier coordinates of the
two actual determinant fibers. -/
noncomputable def circleLargeGaugeFrameCoordinateTransition (fold : Fold) :
    ℂ ≃ₗ[ℂ] ℂ :=
  ((circleDeterminantFrameEquiv fold unitCircleTwist).trans
    (circleLargeGaugeDeterminantTransition fold)).trans
      (circleDeterminantFrameEquiv fold periodicTwist).symm

theorem circleLargeGaugeFrameCoordinateTransition_bijective (fold : Fold) :
    Function.Bijective (circleLargeGaugeFrameCoordinateTransition fold) :=
  (circleLargeGaugeFrameCoordinateTransition fold).bijective

theorem circleLargeGaugeTransition_in_frame_coordinates
    (fold : Fold) (scalar : ℂ) :
    circleLargeGaugeDeterminantTransition fold
        (circleDeterminantFrameEquiv fold unitCircleTwist scalar) =
      circleDeterminantFrameEquiv fold periodicTwist
        (circleLargeGaugeFrameCoordinateTransition fold scalar) := by
  simp [circleLargeGaugeFrameCoordinateTransition]

/-- The exact large-gauge transition is a homeomorphism for the transported
fiber topologies. -/
noncomputable def circleLargeGaugeDeterminantTransitionHomeomorph (fold : Fold) :
    CircleDeterminantFiber fold unitCircleTwist ≃ₜ
      CircleDeterminantFiber fold periodicTwist :=
  (circleDeterminantFrameHomeomorph fold unitCircleTwist).trans <|
    (circleLargeGaugeFrameCoordinateTransition fold).toContinuousLinearEquiv.toHomeomorph.trans
      (circleDeterminantFrameHomeomorph fold periodicTwist).symm

theorem circleLargeGaugeDeterminantTransitionHomeomorph_apply
    (fold : Fold)
    (value : CircleDeterminantFiber fold unitCircleTwist) :
    circleLargeGaugeDeterminantTransitionHomeomorph fold value =
      circleLargeGaugeDeterminantTransition fold value := by
  simp [circleLargeGaugeDeterminantTransitionHomeomorph,
    circleLargeGaugeFrameCoordinateTransition,
    circleDeterminantFrameHomeomorph]

/-! ## A vanishing determinant section distinct from the frame -/

/-- Zeta-regularized circle determinant coordinate in the Fourier frame. -/
def circleRegularizedDeterminantCoordinate (twist : CircleTwist) : ℂ :=
  (determinantAmplitude twist.value : ℂ)

/-- The regularized determinant section.  Unlike the Fourier frame, this
section vanishes when the bounded Dirac operator has a zero mode. -/
noncomputable def circleRegularizedDeterminantSection
    (fold : Fold) (twist : CircleTwist) : CircleDeterminantFiber fold twist :=
  circleDeterminantFrameEquiv fold twist
    (circleRegularizedDeterminantCoordinate twist)

@[simp] theorem circleRegularizedDeterminantSection_periodic
    (fold : Fold) :
    circleRegularizedDeterminantSection fold periodicTwist = 0 := by
  have hCoordinate : circleRegularizedDeterminantCoordinate periodicTwist = 0 := by
    simp [circleRegularizedDeterminantCoordinate, determinantAmplitude,
      periodicTwist]
  rw [circleRegularizedDeterminantSection, hCoordinate, map_zero]

@[simp] theorem circleRegularizedDeterminantSection_unit
    (fold : Fold) :
    circleRegularizedDeterminantSection fold unitCircleTwist = 0 := by
  have hCoordinate : circleRegularizedDeterminantCoordinate unitCircleTwist = 0 := by
    simp [circleRegularizedDeterminantCoordinate, determinantAmplitude,
      unitCircleTwist]
  rw [circleRegularizedDeterminantSection, hCoordinate, map_zero]

theorem circleRegularizedDeterminantSection_ne_zero_of_interior
    (fold : Fold) (twist : CircleTwist)
    (hPositive : 0 < twist.value) (hLess : twist.value < 1) :
    circleRegularizedDeterminantSection fold twist ≠ 0 := by
  have hCoordinate : circleRegularizedDeterminantCoordinate twist ≠ 0 := by
    change (determinantAmplitude twist.value : ℂ) ≠ 0
    rw [Complex.ofReal_ne_zero]
    unfold determinantAmplitude
    apply mul_ne_zero (by norm_num)
    exact (Real.sin_pos_of_pos_of_lt_pi
      (mul_pos Real.pi_pos hPositive)
      (by nlinarith [Real.pi_pos])).ne'
  intro hZero
  have hEqual :
      circleDeterminantFrameEquiv fold twist
          (circleRegularizedDeterminantCoordinate twist) =
        circleDeterminantFrameEquiv fold twist 0 := by
    simpa [circleRegularizedDeterminantSection] using hZero
  exact hCoordinate ((circleDeterminantFrameEquiv fold twist).injective hEqual)

theorem circleRegularizedDeterminantSection_not_frame
    (fold : Fold) :
    circleRegularizedDeterminantSection fold periodicTwist ≠
      circleDeterminantFourierFrame fold periodicTwist := by
  rw [circleRegularizedDeterminantSection_periodic]
  exact (circleDeterminantFourierFrame_ne_zero fold periodicTwist).symm

theorem circleTwist_value_continuous :
    Continuous CircleTwist.value :=
  continuous_induced_dom

theorem circleRegularizedDeterminantCoordinate_continuous :
    Continuous circleRegularizedDeterminantCoordinate := by
  unfold circleRegularizedDeterminantCoordinate determinantAmplitude
  fun_prop

/-- The promoted global Fourier-frame trivialization of the dependent bundle. -/
noncomputable def circleDeterminantGlobalTrivialization (fold : Fold) :
    Trivialization ℂ (π ℂ (CircleDeterminantFiber fold)) :=
  (circleDeterminantVectorPrebundle fold).trivializationOfMemPretrivializationAtlas
    (e := circleDeterminantPretrivialization fold) (by
      exact Set.mem_singleton _)

/-- The global trivialization as a homeomorphism of total spaces. -/
noncomputable def circleDeterminantTotalSpaceHomeomorph (fold : Fold) :
    TotalSpace ℂ (CircleDeterminantFiber fold) ≃ₜ CircleTwist × ℂ :=
  (circleDeterminantGlobalTrivialization fold).toOpenPartialHomeomorph
    |>.toHomeomorphOfSourceEqUnivTargetEqUniv rfl rfl

/-- The determinant section itself obeys the large-gauge endpoint clutching:
both endpoint values vanish at the spectral crossing. -/
theorem circleRegularizedDeterminantSection_endpoint_clutching (fold : Fold) :
    circleLargeGaugeDeterminantTransition fold
        (circleRegularizedDeterminantSection fold unitCircleTwist) =
      circleRegularizedDeterminantSection fold periodicTwist := by
  simp

/-! ## Descent across the holonomy quotient -/

/-- Holonomy parameter with representatives differing by one identified. -/
abbrev CircleHolonomyQuotient := AddCircle (1 : ℝ)

/-- Quotient class of a representative in the closed fundamental interval. -/
def circleHolonomyClass (twist : CircleTwist) : CircleHolonomyQuotient :=
  (twist.value : AddCircle (1 : ℝ))

theorem circleHolonomyClass_endpoints :
    circleHolonomyClass unitCircleTwist =
      circleHolonomyClass periodicTwist := by
  change ((1 : ℝ) : AddCircle (1 : ℝ)) =
    ((0 : ℝ) : AddCircle (1 : ℝ))
  rw [AddCircle.coe_period]
  rfl

/-- The descended topological complex line on the quotient holonomy circle.
For a complex line over a circle this representative is topologically trivial;
the nontrivial family information remains in the exact endpoint clutching map. -/
abbrev CircleDeterminantQuotientFiber : CircleHolonomyQuotient → Type :=
  Bundle.Trivial CircleHolonomyQuotient ℂ

/-- Explicit global trivialization of the descended complex line bundle. -/
noncomputable def circleDeterminantQuotientTrivialization :
    Trivialization ℂ (π ℂ CircleDeterminantQuotientFiber) :=
  Bundle.Trivial.trivialization CircleHolonomyQuotient ℂ

theorem circleDeterminantQuotientFiber_finrank_one
    (holonomy : CircleHolonomyQuotient) :
    Module.finrank ℂ (CircleDeterminantQuotientFiber holonomy) = 1 := by
  exact Module.finrank_self ℂ

/-- Periodic endpoint represented in the descended quotient bundle. -/
noncomputable def circlePeriodicEndpointDescent
    (fold : Fold) (value : CircleDeterminantFiber fold periodicTwist) :
    TotalSpace ℂ CircleDeterminantQuotientFiber :=
  ⟨circleHolonomyClass periodicTwist,
    (circleDeterminantFrameEquiv fold periodicTwist).symm value⟩

/-- Unit endpoint represented after applying the exact large-gauge clutching
map into the periodic endpoint fiber. -/
noncomputable def circleUnitEndpointDescent
    (fold : Fold) (value : CircleDeterminantFiber fold unitCircleTwist) :
    TotalSpace ℂ CircleDeterminantQuotientFiber :=
  ⟨circleHolonomyClass unitCircleTwist,
    (circleDeterminantFrameEquiv fold periodicTwist).symm
      (circleLargeGaugeDeterminantTransition fold value)⟩

/-- The endpoint descent maps agree exactly after the large-gauge transition. -/
theorem circleEndpointDescent_clutching
    (fold : Fold) (value : CircleDeterminantFiber fold unitCircleTwist) :
    circleUnitEndpointDescent fold value =
      circlePeriodicEndpointDescent fold
        (circleLargeGaugeDeterminantTransition fold value) := by
  ext
  · exact circleHolonomyClass_endpoints
  · rfl

end

end P0EFTJanusCircleDeterminantTopologicalBundle
end JanusFormal
