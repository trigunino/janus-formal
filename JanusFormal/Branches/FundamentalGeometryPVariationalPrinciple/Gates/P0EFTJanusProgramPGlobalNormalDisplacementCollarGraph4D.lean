import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusD8NormalBundleD9DisplacementBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeTubularCollarEmbedding4D

/-!
# Global normal-displacement collar graph

A genuine smooth normal section supplies an antiperiodic cover coordinate,
hence a deck-compatible family inside the already constructed latitude
tubular collar.  The family descends from the effective throat to the bulk
quotient, starts at the canonical throat inclusion, has the prescribed
pointwise scalar velocity in every normal trivialization and has zero scalar
acceleration at the base.

The companion joint-smoothness gate proves smooth dependence on the physical
throat point and parameter.  The derivative is not yet identified with the
existing global orthogonal normal lift, so no same-action normal Hessian is
claimed here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalNormalDisplacementCollarGraph4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusEquatorialTubularCoverInjectivity4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetDeckGluing4D
open P0EFTJanusMappingTorusCanonicalLatitudeTubularCollarEmbedding4D

attribute [local instance 10000] instChartedSpaceCoverModelEffectiveQuotient

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev throatData := fixedEquatorData period hPeriod
private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev ThroatCover := MappingTorusCover (throatData period hPeriod)
private abbrev EffectiveThroat := MappingTorus (throatData period hPeriod)
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

/-- Coordinate of a genuine normal section in the chart centred at the same
cover representative. -/
def normalCoordinateLift
    (displacement : SmoothNormalDisplacement period hPeriod)
    (anchor : ThroatCover period hPeriod) : Real :=
  let point := mappingTorusMk (throatData period hPeriod) anchor
  localNormalCoordinate period hPeriod anchor point
    ((mappingTorusMk_isCoveringMap (throatData period hPeriod)).isLocalHomeomorph
      |>.apply_self_mem_localInverseAt_source)
    (displacement point)

private theorem localNormalCoordinate_section_congr
    (displacement : SmoothNormalDisplacement period hPeriod)
    (chartAnchor : ThroatCover period hPeriod)
    {point point' : EffectiveThroat period hPeriod}
    (hPoint : point = point')
    (hChart : point ∈ normalBundleBaseSet period hPeriod chartAnchor)
    (hChart' : point' ∈ normalBundleBaseSet period hPeriod chartAnchor) :
    localNormalCoordinate period hPeriod chartAnchor point hChart
        (displacement point) =
      localNormalCoordinate period hPeriod chartAnchor point' hChart'
        (displacement point') := by
  subst point'
  rfl

/-- One deck turn reverses the coordinate of the genuine twisted section. -/
theorem normalCoordinateLift_oneLoop
    (displacement : SmoothNormalDisplacement period hPeriod)
    (anchor : ThroatCover period hPeriod) :
    normalCoordinateLift period hPeriod displacement ((1 : Int) +ᵥ anchor) =
      -normalCoordinateLift period hPeriod displacement anchor := by
  let base := mappingTorusMk (throatData period hPeriod) anchor
  let shifted := (1 : Int) +ᵥ anchor
  have hBase : base ∈ normalBundleBaseSet period hPeriod anchor :=
    (mappingTorusMk_isCoveringMap (throatData period hPeriod)).isLocalHomeomorph
      |>.apply_self_mem_localInverseAt_source
  have hShiftedSelf :
      mappingTorusMk (throatData period hPeriod) shifted ∈
        normalBundleBaseSet period hPeriod shifted :=
    (mappingTorusMk_isCoveringMap (throatData period hPeriod)).isLocalHomeomorph
      |>.apply_self_mem_localInverseAt_source
  have hProjection :
      mappingTorusMk (throatData period hPeriod) shifted = base := by
    simpa [base, shifted, throatData] using
      oneLoopAnchor_projects period hPeriod anchor
  have hShifted : base ∈ normalBundleBaseSet period hPeriod shifted :=
    hProjection ▸ hShiftedSelf
  calc
    normalCoordinateLift period hPeriod displacement shifted =
        localNormalCoordinate period hPeriod shifted base hShifted
          (displacement base) := by
      exact localNormalCoordinate_section_congr period hPeriod displacement shifted
        hProjection hShiftedSelf hShifted
    _ = -localNormalCoordinate period hPeriod anchor base hBase
          (displacement base) := by
      simpa [base, shifted, throatData] using
        localNormalCoordinate_oneLoop period hPeriod anchor (displacement base)
    _ = -normalCoordinateLift period hPeriod displacement anchor := by
      rfl

/-- `arctan` keeps every affine normal curve inside the genuine open tubular
band, without a boundedness hypothesis on the section. -/
def normalGraphCoordinate
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (anchor : ThroatCover period hPeriod) :
    CanonicalLatitudeTubularNormal :=
  ⟨Real.arctan
      (parameter * normalCoordinateLift period hPeriod displacement anchor),
    Real.neg_pi_div_two_lt_arctan _, Real.arctan_lt_pi_div_two _⟩

@[simp]
theorem normalGraphCoordinate_zero
    (displacement : SmoothNormalDisplacement period hPeriod)
    (anchor : ThroatCover period hPeriod) :
    (normalGraphCoordinate period hPeriod displacement 0 anchor).1 = 0 := by
  simp [normalGraphCoordinate]

/-- The collar coordinate has the prescribed normal velocity at the base. -/
theorem normalGraphCoordinate_hasDerivAt_zero
    (displacement : SmoothNormalDisplacement period hPeriod)
    (anchor : ThroatCover period hPeriod) :
    HasDerivAt
      (fun parameter : Real =>
        (normalGraphCoordinate period hPeriod displacement parameter anchor).1)
      (normalCoordinateLift period hPeriod displacement anchor) 0 := by
  let coordinate := normalCoordinateLift period hPeriod displacement anchor
  have hInner : HasDerivAt (fun parameter : Real => parameter * coordinate)
      coordinate 0 := by
    simpa using (hasDerivAt_id (0 : Real)).mul_const coordinate
  have hComp :=
    (Real.hasDerivAt_arctan ((fun parameter : Real =>
      parameter * coordinate) 0)).comp 0 hInner
  simpa [normalGraphCoordinate, coordinate, Function.comp_def] using hComp

/-- First derivative of the scalar collar coordinate at every parameter. -/
theorem normalGraphCoordinate_hasDerivAt
    (displacement : SmoothNormalDisplacement period hPeriod)
    (anchor : ThroatCover period hPeriod) (parameter : Real) :
    HasDerivAt
      (fun time : Real =>
        (normalGraphCoordinate period hPeriod displacement time anchor).1)
      ((1 / (1 +
          (parameter * normalCoordinateLift period hPeriod displacement anchor) ^ 2)) *
        normalCoordinateLift period hPeriod displacement anchor)
      parameter := by
  let coordinate := normalCoordinateLift period hPeriod displacement anchor
  have hInner : HasDerivAt (fun time : Real => time * coordinate)
      coordinate parameter := by
    simpa using (hasDerivAt_id parameter).mul_const coordinate
  have hComp :=
    (Real.hasDerivAt_arctan (parameter * coordinate)).comp parameter hInner
  simpa [normalGraphCoordinate, coordinate, Function.comp_def] using hComp

/-- The velocity of the explicit `arctan` graph has zero derivative at the
base parameter. -/
theorem normalGraphCoordinateVelocity_hasDerivAt_zero
    (displacement : SmoothNormalDisplacement period hPeriod)
    (anchor : ThroatCover period hPeriod) :
    HasDerivAt
      (fun parameter : Real =>
        (1 / (1 +
            (parameter * normalCoordinateLift period hPeriod displacement anchor) ^ 2)) *
          normalCoordinateLift period hPeriod displacement anchor)
      0 0 := by
  let coordinate := normalCoordinateLift period hPeriod displacement anchor
  have hLinear : HasDerivAt (fun parameter : Real => parameter * coordinate)
      coordinate 0 := by
    simpa using (hasDerivAt_id (0 : Real)).mul_const coordinate
  have hSquare : HasDerivAt (fun parameter : Real => (parameter * coordinate) ^ 2)
      0 0 := by
    have hRaw := hLinear.pow 2
    refine (hRaw.congr_deriv ?_).congr_of_eventuallyEq
      (Filter.Eventually.of_forall ?_)
    · norm_num
    · intro parameter
      rfl
  have hDenominator :
      HasDerivAt (fun parameter : Real => 1 + (parameter * coordinate) ^ 2)
        0 0 := by
    have hRaw :=
      (hasDerivAt_const (x := (0 : Real)) (c := (1 : Real))).add hSquare
    refine (hRaw.congr_deriv ?_).congr_of_eventuallyEq
      (Filter.Eventually.of_forall ?_)
    · norm_num
    · intro parameter
      rfl
  have hInverse :
      HasDerivAt (fun parameter : Real =>
        (1 + (parameter * coordinate) ^ 2)⁻¹) 0 0 := by
    have hRaw := hDenominator.inv (by norm_num)
    refine (hRaw.congr_deriv ?_).congr_of_eventuallyEq
      (Filter.Eventually.of_forall ?_)
    · norm_num
    · intro parameter
      rfl
  simpa [coordinate, one_div] using hInverse.mul_const coordinate

/-- In the explicit collar scalar, the graph acceleration vanishes at the
base.  This is stronger than needed at a critical point and uses no field
equation. -/
theorem normalGraphCoordinate_secondDeriv_zero
    (displacement : SmoothNormalDisplacement period hPeriod)
    (anchor : ThroatCover period hPeriod) :
    deriv
      (fun parameter : Real =>
        deriv (fun time : Real =>
          (normalGraphCoordinate period hPeriod displacement time anchor).1)
          parameter)
      0 = 0 := by
  have hVelocity :
      (fun parameter : Real =>
          deriv (fun time : Real =>
            (normalGraphCoordinate period hPeriod displacement time anchor).1)
            parameter) =
        (fun parameter : Real =>
          (1 / (1 +
              (parameter * normalCoordinateLift period hPeriod displacement anchor) ^ 2)) *
            normalCoordinateLift period hPeriod displacement anchor) := by
    funext parameter
    exact (normalGraphCoordinate_hasDerivAt period hPeriod displacement anchor
      parameter).deriv
  rw [hVelocity]
  exact (normalGraphCoordinateVelocity_hasDerivAt_zero period hPeriod
    displacement anchor).deriv

/-- The graph coordinate inherits the one-loop sign clutching of the normal
section. -/
theorem normalGraphCoordinate_oneLoop
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (anchor : ThroatCover period hPeriod) :
    normalGraphCoordinate period hPeriod displacement parameter
        ((1 : Int) +ᵥ anchor) =
      canonicalLatitudeTubularNormalNeg
        (normalGraphCoordinate period hPeriod displacement parameter anchor) := by
  apply Subtype.ext
  change Real.arctan
      (parameter * normalCoordinateLift period hPeriod displacement
        ((1 : Int) +ᵥ anchor)) =
    -Real.arctan
      (parameter * normalCoordinateLift period hPeriod displacement anchor)
  rw [normalCoordinateLift_oneLoop]
  simp [Real.arctan_neg]

/-- Cover-level graph inside the already constructed latitude collar. -/
def normalGraphCoverMap
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (anchor : ThroatCover period hPeriod) :
    MappingTorusCover (sphereData period hPeriod) :=
  normalLatitudeCover period hPeriod anchor
    (normalGraphCoordinate period hPeriod displacement parameter anchor).1

/-- The graph map intertwines one generator of the source and target deck
actions. -/
theorem normalGraphCoverMap_deck
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (anchor : ThroatCover period hPeriod) :
    normalGraphCoverMap period hPeriod displacement parameter
        ((1 : Int) +ᵥ anchor) =
      (1 : Int) +ᵥ
        normalGraphCoverMap period hPeriod displacement parameter anchor := by
  unfold normalGraphCoverMap
  rw [normalGraphCoordinate_oneLoop]
  simpa [canonicalLatitudeTubularNormalNeg] using
    normalLatitudeCover_deck_generator_twist period hPeriod anchor
      (-(normalGraphCoordinate period hPeriod displacement parameter anchor).1)

/-- Equivariance for the inverse generator follows from the forward one. -/
theorem normalGraphCoverMap_deck_inv
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (anchor : ThroatCover period hPeriod) :
    normalGraphCoverMap period hPeriod displacement parameter
        ((-1 : Int) +ᵥ anchor) =
      (-1 : Int) +ᵥ
        normalGraphCoverMap period hPeriod displacement parameter anchor := by
  have hForward := normalGraphCoverMap_deck period hPeriod displacement parameter
    ((-1 : Int) +ᵥ anchor)
  have hAct := congrArg
    (fun point : MappingTorusCover (sphereData period hPeriod) =>
      (-1 : Int) +ᵥ point) hForward
  simpa [add_vadd] using hAct.symm

/-- The graph map is equivariant under every integer deck winding. -/
theorem normalGraphCoverMap_vadd
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (winding : Int)
    (anchor : ThroatCover period hPeriod) :
    normalGraphCoverMap period hPeriod displacement parameter
        (winding +ᵥ anchor) =
      winding +ᵥ
        normalGraphCoverMap period hPeriod displacement parameter anchor := by
  induction winding using Int.induction_on generalizing anchor with
  | zero => simp
  | succ winding ih =>
      calc
        normalGraphCoverMap period hPeriod displacement parameter
            (((winding : Int) + 1) +ᵥ anchor) =
          normalGraphCoverMap period hPeriod displacement parameter
            ((winding : Int) +ᵥ ((1 : Int) +ᵥ anchor)) := by rw [add_vadd]
        _ = (winding : Int) +ᵥ normalGraphCoverMap period hPeriod displacement parameter
            ((1 : Int) +ᵥ anchor) := ih _
        _ = (winding : Int) +ᵥ ((1 : Int) +ᵥ
            normalGraphCoverMap period hPeriod displacement parameter anchor) := by
          rw [normalGraphCoverMap_deck]
        _ = ((winding : Int) + 1) +ᵥ
            normalGraphCoverMap period hPeriod displacement parameter anchor := by
          rw [add_vadd]
  | pred winding ih =>
      calc
        normalGraphCoverMap period hPeriod displacement parameter
            ((-(winding : Int) - 1) +ᵥ anchor) =
          normalGraphCoverMap period hPeriod displacement parameter
            ((-(winding : Int)) +ᵥ ((-1 : Int) +ᵥ anchor)) := by
              rw [sub_eq_add_neg, add_vadd]
        _ = (-(winding : Int)) +ᵥ
            normalGraphCoverMap period hPeriod displacement parameter
              ((-1 : Int) +ᵥ anchor) := ih _
        _ = (-(winding : Int)) +ᵥ ((-1 : Int) +ᵥ
            normalGraphCoverMap period hPeriod displacement parameter anchor) := by
          rw [normalGraphCoverMap_deck_inv]
        _ = (-(winding : Int) - 1) +ᵥ
            normalGraphCoverMap period hPeriod displacement parameter anchor := by
          rw [sub_eq_add_neg, add_vadd]

/-- The deck-equivariant graph descends from the effective throat into the
effective bulk quotient. -/
def normalGraph
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) :
    EffectiveThroat period hPeriod → EffectiveQuotient period hPeriod :=
  Quotient.map (normalGraphCoverMap period hPeriod displacement parameter)
    (fun first second hOrbit => by
      change AddAction.orbitRel Int (ThroatCover period hPeriod)
        first second at hOrbit
      change AddAction.orbitRel Int
        (MappingTorusCover (sphereData period hPeriod))
        (normalGraphCoverMap period hPeriod displacement parameter first)
        (normalGraphCoverMap period hPeriod displacement parameter second)
      rw [AddAction.orbitRel_apply, AddAction.mem_orbit_iff] at hOrbit ⊢
      rcases hOrbit with ⟨winding, hWinding⟩
      refine ⟨winding, ?_⟩
      rw [← normalGraphCoverMap_vadd]
      exact congrArg
        (normalGraphCoverMap period hPeriod displacement parameter) hWinding)

@[simp]
theorem normalGraph_mk
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (anchor : ThroatCover period hPeriod) :
    normalGraph period hPeriod displacement parameter
        (mappingTorusMk (throatData period hPeriod) anchor) =
      mappingTorusMk (sphereData period hPeriod)
        (normalGraphCoverMap period hPeriod displacement parameter anchor) :=
  rfl

/-- Each cover-level graph is injective because it lies in the established
open latitude tubular band. -/
theorem normalGraphCoverMap_injective
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) :
    Function.Injective
      (normalGraphCoverMap period hPeriod displacement parameter) := by
  intro first second hEqual
  have hFiber := congrArg MappingTorusCover.fiber hEqual
  have hTime := congrArg MappingTorusCover.time hEqual
  change equatorialLatitude first.fiber
      (normalGraphCoordinate period hPeriod displacement parameter first).1 =
    equatorialLatitude second.fiber
      (normalGraphCoordinate period hPeriod displacement parameter second).1
    at hFiber
  change first.time = second.time at hTime
  have hTubular :
      (first.fiber,
          normalGraphCoordinate period hPeriod displacement parameter first) =
        (second.fiber,
          normalGraphCoordinate period hPeriod displacement parameter second) :=
    equatorialTubularMap_injective hFiber
  apply MappingTorusCover.ext
  · exact congrArg Prod.fst hTubular
  · exact hTime

/-- Every descended member of the normal family is an injective physical
throat graph. -/
theorem normalGraph_injective
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) :
    Function.Injective
      (normalGraph period hPeriod displacement parameter) := by
  intro first second hEqual
  refine Quotient.inductionOn₂ first second ?_ hEqual
  intro firstAnchor secondAnchor hCoverQuotient
  apply (mappingTorusMk_eq_iff_exists_vadd
    (throatData period hPeriod) firstAnchor secondAnchor).2
  have hOrbit := (mappingTorusMk_eq_iff_exists_vadd
    (sphereData period hPeriod)
    (normalGraphCoverMap period hPeriod displacement parameter firstAnchor)
    (normalGraphCoverMap period hPeriod displacement parameter secondAnchor)).1
      hCoverQuotient
  rcases hOrbit with ⟨winding, hWinding⟩
  refine ⟨winding, ?_⟩
  apply normalGraphCoverMap_injective period hPeriod displacement parameter
  calc
    normalGraphCoverMap period hPeriod displacement parameter
        (winding +ᵥ secondAnchor) =
      winding +ᵥ normalGraphCoverMap period hPeriod displacement parameter
        secondAnchor :=
      normalGraphCoverMap_vadd period hPeriod displacement parameter
        winding secondAnchor
    _ = normalGraphCoverMap period hPeriod displacement parameter firstAnchor :=
      hWinding

/-- At zero parameter the descended graph is exactly the established throat
inclusion. -/
@[simp]
theorem normalGraph_zero
    (displacement : SmoothNormalDisplacement period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    normalGraph period hPeriod displacement 0 point =
      fixedThroatQuotientInclusion period hPeriod point := by
  refine Quotient.inductionOn point ?_
  intro anchor
  change mappingTorusMk (sphereData period hPeriod)
      (normalGraphCoverMap period hPeriod displacement 0 anchor) =
    mappingTorusMk (sphereData period hPeriod)
      (fixedThroatCoverInclusion period hPeriod anchor)
  congr 1
  unfold normalGraphCoverMap
  rw [normalGraphCoordinate_zero, normalLatitudeCover_zero]

/-- For every chosen cover representative, the descended normal graph is a
smooth curve of the deformation parameter. -/
theorem normalGraph_mk_curve_contMDiff
    (displacement : SmoothNormalDisplacement period hPeriod)
    (anchor : ThroatCover period hPeriod) :
    ContMDiff 𝓘(Real, Real) coverModelWithCorners ∞
      (fun parameter : Real =>
        normalGraph period hPeriod displacement parameter
          (mappingTorusMk (throatData period hPeriod) anchor)) := by
  have hCoordinate : ContDiff Real ∞
      (fun parameter : Real =>
        (normalGraphCoordinate period hPeriod displacement parameter anchor).1) := by
    exact (contDiff_id.mul contDiff_const).arctan
  simpa [normalGraph_mk, normalGraphCoverMap, quotientNormalLatitude,
      Function.comp_def] using
    (quotientNormalLatitude_contMDiff period hPeriod anchor).comp
      hCoordinate.contMDiff

/-- The descended graph is a smooth parameter curve at every physical throat
point, independently of its cover representative. -/
theorem normalGraph_curve_contMDiff
    (displacement : SmoothNormalDisplacement period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    ContMDiff 𝓘(Real, Real) coverModelWithCorners ∞
      (fun parameter : Real =>
        normalGraph period hPeriod displacement parameter point) := by
  refine Quotient.inductionOn point ?_
  intro anchor
  exact normalGraph_mk_curve_contMDiff period hPeriod displacement anchor

end
end P0EFTJanusProgramPGlobalNormalDisplacementCollarGraph4D
end JanusFormal
