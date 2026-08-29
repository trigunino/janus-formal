import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCFourierMonopoleProductDensity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveMonopolePullbackBundle4D
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusCompactQuotient

/-!
# Fourier--monopole density on the intrinsic D9 throat

The fixed D9 throat has identity monodromy.  Its intrinsic sphere and time
coordinates therefore embed it into `S² × AddCircle |period|`.  Pullback of
the Fourier--solid-harmonic product algebra separates throat points and is
uniformly dense.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCThroatFourierMonopoleDensity4D

set_option autoImplicit false
noncomputable section

open Set AddCircle
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPPrimitiveMonopoleClutchingConnection4D
open P0EFTJanusProgramPD9PrimitiveMonopolePullbackBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCFourierMonopoleProductDensity4D
open P0EFTJanusProgramPD9PrimitiveSpinCSpherePolynomialDensity4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatCover :=
  MappingTorusCover (ThroatData period hPeriod)
private abbrev ThroatBase :=
  MappingTorus (ThroatData period hPeriod)

local instance throatBaseChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance throatBaseIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (ThroatBase period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance throatBaseCompactSpace :
    CompactSpace (ThroatBase period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance throatBaseMeasurableSpace :
    MeasurableSpace (ThroatBase period hPeriod) :=
  borel (ThroatBase period hPeriod)

local instance throatBaseBorelSpace :
    BorelSpace (ThroatBase period hPeriod) where
  measurable_eq := rfl

/-- Natural time coordinate before orienting the circle positively. -/
def d9ThroatTimeCircle :
    ThroatBase period hPeriod → AddCircle period :=
  Quotient.lift
    (fun point : ThroatCover period hPeriod =>
      (point.time : AddCircle period))
    (fun first second hOrbit => by
      change
        AddAction.orbitRel ℤ (ThroatCover period hPeriod)
          first second at hOrbit
      rw [AddAction.orbitRel_apply, AddAction.mem_orbit_iff] at hOrbit
      rcases hOrbit with ⟨winding, hWinding⟩
      rw [← hWinding]
      change
        ((second.time + (winding : Real) * period : Real) :
            AddCircle period) =
          (second.time : AddCircle period)
      rw [AddCircle.coe_add, ← zsmul_eq_mul,
        AddCircle.coe_zsmul, AddCircle.coe_period,
        smul_zero, add_zero])

@[simp]
theorem d9ThroatTimeCircle_mk
    (point : ThroatCover period hPeriod) :
    d9ThroatTimeCircle period hPeriod
        (mappingTorusMk (ThroatData period hPeriod) point) =
      (point.time : AddCircle period) :=
  rfl

theorem d9ThroatTimeCircle_continuous :
    Continuous (d9ThroatTimeCircle period hPeriod) := by
  apply Continuous.quotient_lift
  exact (AddCircle.continuous_mk' period).comp
    (by
      simpa [Function.comp_def] using
        continuous_snd.comp
          (coverHomeomorphProd
            (ThroatData period hPeriod)).continuous)

/-- Positive-period time coordinate used by the Fourier basis. -/
def d9ThroatPositiveTimeCircle :
    ThroatBase period hPeriod → AddCircle |period| :=
  AddCircle.homeomorphAddCircle
    period |period| hPeriod (abs_ne_zero.mpr hPeriod) ∘
      d9ThroatTimeCircle period hPeriod

theorem d9ThroatPositiveTimeCircle_continuous :
    Continuous (d9ThroatPositiveTimeCircle period hPeriod) :=
  (AddCircle.homeomorphAddCircle
      period |period| hPeriod (abs_ne_zero.mpr hPeriod)).continuous.comp
    (d9ThroatTimeCircle_continuous period hPeriod)

/-- Intrinsic product coordinates of the identity mapping torus. -/
def d9ThroatFourierMonopoleCoordinates :
    ThroatBase period hPeriod →
      MonopoleSphere × AddCircle |period| :=
  fun base =>
    (d9ThroatMonopoleSphereProjection period hPeriod base,
      d9ThroatPositiveTimeCircle period hPeriod base)

theorem d9ThroatFourierMonopoleCoordinates_continuous :
    Continuous
      (d9ThroatFourierMonopoleCoordinates period hPeriod) :=
  (d9ThroatMonopoleSphereProjection_continuous period hPeriod).prodMk
    (d9ThroatPositiveTimeCircle_continuous period hPeriod)

theorem d9ThroatFourierMonopoleCoordinates_injective :
    Function.Injective
      (d9ThroatFourierMonopoleCoordinates period hPeriod) := by
  intro first
  refine Quotient.inductionOn first ?_
  intro first second
  refine Quotient.inductionOn second ?_
  intro second hCoordinates
  apply Quotient.sound
  change
    AddAction.orbitRel ℤ (ThroatCover period hPeriod) first second
  rw [AddAction.orbitRel_apply, AddAction.mem_orbit_iff]
  have hSphere :
      d9MonopoleSphereCoverProjection period hPeriod first =
        d9MonopoleSphereCoverProjection period hPeriod second :=
    congrArg Prod.fst hCoordinates
  have hFiber : first.fiber = second.fiber :=
    equatorialTwoSphereHomeomorph.injective hSphere
  have hPositiveCircle :
      d9ThroatPositiveTimeCircle period hPeriod
          (mappingTorusMk (ThroatData period hPeriod) first) =
        d9ThroatPositiveTimeCircle period hPeriod
          (mappingTorusMk (ThroatData period hPeriod) second) :=
    congrArg Prod.snd hCoordinates
  have hCircle :
      (first.time : AddCircle period) =
        (second.time : AddCircle period) := by
    exact
      (AddCircle.homeomorphAddCircle
        period |period| hPeriod
          (abs_ne_zero.mpr hPeriod)).injective hPositiveCircle
  have hCircleZero :
      ((first.time - second.time : Real) : AddCircle period) = 0 := by
    rw [AddCircle.coe_sub, hCircle, sub_self]
  obtain ⟨winding, hWinding⟩ :=
    (AddCircle.coe_eq_zero_iff period).mp hCircleZero
  refine ⟨winding, ?_⟩
  apply MappingTorusCover.ext
  · change
      ((Homeomorph.refl EquatorialTwoSphere) ^ winding)
          second.fiber =
        first.fiber
    rw [show
        ((Homeomorph.refl EquatorialTwoSphere) ^ winding)
            second.fiber =
          ((Homeomorph.refl EquatorialTwoSphere) ^ winding).toEquiv
            second.fiber from rfl,
      homeomorph_toEquiv_zpow,
      show (Homeomorph.refl EquatorialTwoSphere).toEquiv = 1 from rfl,
      one_zpow]
    exact hFiber.symm
  · change
      second.time + (winding : Real) * period = first.time
    rw [← zsmul_eq_mul, hWinding]
    ring

def d9ThroatFourierMonopoleCoordinatesContinuousMap :
    C(ThroatBase period hPeriod,
      MonopoleSphere × AddCircle |period|) :=
  ⟨d9ThroatFourierMonopoleCoordinates period hPeriod,
    d9ThroatFourierMonopoleCoordinates_continuous period hPeriod⟩

def d9ThroatFourierMonopoleStarSubalgebra :
    StarSubalgebra Complex
      C(ThroatBase period hPeriod, Complex) := by
  letI : Fact (0 < |period|) := ⟨abs_pos.mpr hPeriod⟩
  exact StarSubalgebra.map
    (ContinuousMap.compStarAlgHom' Complex Complex
      (d9ThroatFourierMonopoleCoordinatesContinuousMap
        period hPeriod))
    (starSubalgebraProduct
      primitiveSpinCSpherePolynomialStarSubalgebra
      (@fourierSubalgebra |period|))

theorem d9ThroatFourierMonopoleStarSubalgebra_separatesPoints :
    (d9ThroatFourierMonopoleStarSubalgebra
      period hPeriod).SeparatesPoints := by
  letI : Fact (0 < |period|) := ⟨abs_pos.mpr hPeriod⟩
  intro first second hPoints
  have hCoordinates :
      d9ThroatFourierMonopoleCoordinates period hPeriod first ≠
        d9ThroatFourierMonopoleCoordinates period hPeriod second :=
    (d9ThroatFourierMonopoleCoordinates_injective
      period hPeriod).ne hPoints
  obtain ⟨_, ⟨productFunction, hProductFunction, rfl⟩,
      hValues⟩ :=
    starSubalgebraProduct_separatesPoints
      primitiveSpinCSpherePolynomialStarSubalgebra
      (@fourierSubalgebra |period|)
      primitiveSpinCSpherePolynomialStarSubalgebra_separatesPoints
      fourierSubalgebra_separatesPoints hCoordinates
  refine
    ⟨_, ⟨productFunction.comp
        (d9ThroatFourierMonopoleCoordinatesContinuousMap
          period hPeriod), ?_, rfl⟩, hValues⟩
  exact ⟨productFunction, hProductFunction, rfl⟩

theorem
    d9ThroatFourierMonopoleStarSubalgebra_topologicalClosure_eq_top :
    (d9ThroatFourierMonopoleStarSubalgebra
      period hPeriod).topologicalClosure = ⊤ :=
  ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
    (d9ThroatFourierMonopoleStarSubalgebra period hPeriod)
    (d9ThroatFourierMonopoleStarSubalgebra_separatesPoints
      period hPeriod)

def d9ThroatFourierMonopoleMode
    (label : FourierMonopoleLabel) :
    C(ThroatBase period hPeriod, Complex) := by
  letI : Fact (0 < |period|) := ⟨abs_pos.mpr hPeriod⟩
  exact
    (fourierMonopoleProduct (T := |period|) label).comp
      (d9ThroatFourierMonopoleCoordinatesContinuousMap
        period hPeriod)

def d9ThroatFourierMonopoleSpan :
    Submodule Complex C(ThroatBase period hPeriod, Complex) :=
  Submodule.span Complex
    (Set.range (d9ThroatFourierMonopoleMode period hPeriod))

private theorem productPullback_mem_d9ThroatFourierMonopoleSpan
    (productFunction :
      C(MonopoleSphere × AddCircle |period|, Complex))
    (hProductFunction :
      productFunction ∈ fourierMonopoleProductSpan |period|) :
    productFunction.comp
        (d9ThroatFourierMonopoleCoordinatesContinuousMap
          period hPeriod) ∈
      d9ThroatFourierMonopoleSpan period hPeriod := by
  letI : Fact (0 < |period|) := ⟨abs_pos.mpr hPeriod⟩
  refine Submodule.span_induction
    (p := fun productFunction _ =>
      productFunction.comp
          (d9ThroatFourierMonopoleCoordinatesContinuousMap
            period hPeriod) ∈
        d9ThroatFourierMonopoleSpan period hPeriod)
    ?_ ?_ ?_ ?_ hProductFunction
  · rintro _ ⟨label, rfl⟩
    exact Submodule.subset_span
      ⟨label, by
        simp [d9ThroatFourierMonopoleMode]⟩
  · simp
  · intro first second _ _ hFirst hSecond
    simpa using
      (d9ThroatFourierMonopoleSpan period hPeriod).add_mem
        hFirst hSecond
  · intro scalar productFunction _ hFunction
    simpa using
      (d9ThroatFourierMonopoleSpan period hPeriod).smul_mem
        scalar hFunction

theorem d9ThroatFourierMonopoleSpan_eq_starSubalgebra :
    d9ThroatFourierMonopoleSpan period hPeriod =
      (d9ThroatFourierMonopoleStarSubalgebra
        period hPeriod).toSubalgebra.toSubmodule := by
  letI : Fact (0 < |period|) := ⟨abs_pos.mpr hPeriod⟩
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨label, rfl⟩
    refine ⟨fourierMonopoleProduct (T := |period|) label, ?_, ?_⟩
    · change
        fourierMonopoleProduct (T := |period|) label ∈
          (starSubalgebraProduct
            primitiveSpinCSpherePolynomialStarSubalgebra
            (@fourierSubalgebra |period|)).toSubalgebra.toSubmodule
      rw [← fourierMonopoleProductSpan_eq_productStarSubalgebra]
      exact Submodule.subset_span ⟨label, rfl⟩
    · rfl
  · intro throatFunction hThroatFunction
    rcases hThroatFunction with
      ⟨productFunction, hProductFunction, rfl⟩
    apply productPullback_mem_d9ThroatFourierMonopoleSpan
      period hPeriod productFunction
    rw [fourierMonopoleProductSpan_eq_productStarSubalgebra]
    exact hProductFunction

theorem d9ThroatFourierMonopoleSpan_closure_eq_top :
    (d9ThroatFourierMonopoleSpan
      period hPeriod).topologicalClosure = ⊤ := by
  rw [d9ThroatFourierMonopoleSpan_eq_starSubalgebra]
  exact congr_arg
    (Subalgebra.toSubmodule ∘ StarSubalgebra.toSubalgebra)
    (d9ThroatFourierMonopoleStarSubalgebra_topologicalClosure_eq_top
      period hPeriod)

variable
  (measure : MeasureTheory.Measure (ThroatBase period hPeriod))
  [MeasureTheory.IsFiniteMeasure measure]
  [measure.WeaklyRegular]

def d9ThroatFourierMonopoleToL2 :
    d9ThroatFourierMonopoleSpan period hPeriod →L[Complex]
      MeasureTheory.Lp Complex (2 : ENNReal) measure :=
  (ContinuousMap.toLp (2 : ENNReal) measure Complex).comp
    (d9ThroatFourierMonopoleSpan period hPeriod).subtypeL

theorem d9ThroatFourierMonopoleToL2_denseRange :
    DenseRange
      (d9ThroatFourierMonopoleToL2
        period hPeriod measure) := by
  have hLp :
      DenseRange
        (ContinuousMap.toLp
          (2 : ENNReal) measure Complex) :=
    ContinuousMap.toLp_denseRange Complex measure Complex
      (by norm_num : (2 : ENNReal) ≠ ⊤)
  have hSubtype :
      DenseRange
        (d9ThroatFourierMonopoleSpan
          period hPeriod).subtypeL := by
    change Dense
      (Set.range
        (d9ThroatFourierMonopoleSpan
          period hPeriod).subtypeL)
    rw [show
      Set.range
          (d9ThroatFourierMonopoleSpan
            period hPeriod).subtypeL =
        (d9ThroatFourierMonopoleSpan period hPeriod :
          Set C(ThroatBase period hPeriod, Complex)) by
      ext continuousFunction
      constructor
      · rintro ⟨packetFunction, rfl⟩
        exact packetFunction.property
      · intro hPacket
        exact ⟨⟨continuousFunction, hPacket⟩, rfl⟩]
    exact Submodule.dense_iff_topologicalClosure_eq_top.mpr
      (d9ThroatFourierMonopoleSpan_closure_eq_top
        period hPeriod)
  unfold d9ThroatFourierMonopoleToL2
  simpa only [ContinuousLinearMap.coe_comp] using
    hLp.comp hSubtype
      (ContinuousMap.toLp
        (2 : ENNReal) measure Complex).continuous

end
end P0EFTJanusProgramPD9PrimitiveSpinCThroatFourierMonopoleDensity4D
end JanusFormal
