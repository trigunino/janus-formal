import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCircleUnboundedDiracDomain
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusFiniteTemporalFourierGaugeGhostCohomology4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusL2PTFunctionalSpace4D

/-!
# Infinite temporal Fourier--Sobolev bridge on the effective mapping torus

For a positive period, the time coordinate of the reflected-sphere mapping
torus descends to `AddCircle period`.  The pushforward of the explicit
round-`S³`-times-one-period volume through this time map is computed exactly.
After probability normalization, pullback along the time map is therefore a
linear isometry from circle `L²` into `L²` on the actual D8 quotient.

Mathlib's complete Fourier Hilbert basis then gives an isometric realization
of every `ℓ²(ℤ, ℂ)` sequence as a genuine temporal quotient `L²` section,
with convergence of the infinite Fourier series and exact recovery of every
coefficient.  The realization agrees with the already constructed smooth
finite Fourier fields.

Finally, an encoded weighted `ℓ²` completion with weight
`1 + |2π i n / period|²` is mapped continuously and injectively to a pair of
quotient `L²` sections (field and temporal spectral derivative); both Fourier
series converge in quotient `L²` and their coefficients obey the physical
derivative multiplier exactly.

This is only the scalar, spatially constant temporal sector.  It does not
identify spatial modes, nontrivial bundle transition functions, the full
intrinsic Sobolev space, or any boundary trace.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusInfiniteTemporalFourierSobolevBridge4D

set_option autoImplicit false

noncomputable section

open scoped ENNReal Manifold ContDiff
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusL2PTFunctionalSpace4D
open P0EFTJanusCircleUnboundedDiracDomain
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusFiniteTemporalFourierGaugeGhostCohomology4D
open P0EFTJanusShiftedSobolevMappingTorusFiniteTemporalFourierBridge4D

variable (period : Real) [hPeriodPos : Fact (0 < period)]

private abbrev sphereData :=
  reflectedSphereData period hPeriodPos.out.ne'

private abbrev EffectiveCover :=
  MappingTorusCover (sphereData period)

private abbrev EffectiveQuotient :=
  MappingTorus (sphereData period)

private abbrev StandardSphere := Metric.sphere (0 : EuclideanR4) 1

local instance effectiveCoverChartedSpace :
    ChartedSpace CoverModel (EffectiveCover period) :=
  reflectedSphereCoverChartedSpace period hPeriodPos.out.ne'

local instance effectiveCoverIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveCover period) :=
  reflectedSphereCover_isManifold period hPeriodPos.out.ne'

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period) :=
  reflectedSphereQuotientChartedSpace period hPeriodPos.out.ne'

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period) :=
  reflectedSphereQuotient_isManifold period hPeriodPos.out.ne'

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period) :=
  reflectedSphereQuotientCompactSpace period hPeriodPos.out.ne'

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period) :=
  borel (EffectiveQuotient period)

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period) where
  measurable_eq := rfl

/-- The globally defined time coordinate of the actual mapping torus. -/
def mappingTorusTimeCircle : EffectiveQuotient period → AddCircle period :=
  Quotient.lift
    (fun point : EffectiveCover period => (point.time : AddCircle period))
    (fun first second hOrbit => by
      change AddAction.orbitRel ℤ (EffectiveCover period) first second at hOrbit
      rw [AddAction.orbitRel_apply, AddAction.mem_orbit_iff] at hOrbit
      rcases hOrbit with ⟨winding, hWinding⟩
      rw [← hWinding]
      change
        ((second.time + (winding : Real) * period : Real) : AddCircle period) =
          (second.time : AddCircle period)
      rw [AddCircle.coe_add, ← zsmul_eq_mul, AddCircle.coe_zsmul,
        AddCircle.coe_period, smul_zero, add_zero])

@[simp]
theorem mappingTorusTimeCircle_mk (point : EffectiveCover period) :
    mappingTorusTimeCircle period
        (mappingTorusMk (sphereData period) point) =
      (point.time : AddCircle period) :=
  rfl

theorem mappingTorusTimeCircle_continuous :
    Continuous (mappingTorusTimeCircle period) := by
  apply Continuous.quotient_lift
  exact (AddCircle.continuous_mk' period).comp
    (by
      simpa [Function.comp_def] using
        continuous_snd.comp (coverHomeomorphProd (sphereData period)).continuous)

/-- Positive-period presentation of the canonical fundamental product
measure used by the global Lorentz-volume gate. -/
def positiveFundamentalProductMeasure : Measure (StandardSphere × Real) :=
  ((volume : Measure EuclideanR4).toSphere).prod
    (volume.restrict (Set.Ioc 0 period))

/-- Positive-period fundamental-domain map to the actual quotient. -/
def positiveFundamentalDomainMap
    (point : StandardSphere × Real) : EffectiveQuotient period :=
  mappingTorusMk (sphereData period)
    ((coverHomeomorphProd (sphereData period)).symm
      (unitThreeSphereHomeomorph.symm point.1, point.2))

theorem positiveFundamentalDomainMap_continuous :
    Continuous (positiveFundamentalDomainMap period) := by
  have hProduct : Continuous
      (fun point : StandardSphere × Real =>
        (unitThreeSphereHomeomorph.symm point.1, point.2)) :=
    (unitThreeSphereHomeomorph.symm.continuous.comp continuous_fst).prodMk
      continuous_snd
  exact (mappingTorusMk_isCoveringMap
      (sphereData period)).isLocalHomeomorph.continuous.comp
    ((coverHomeomorphProd
      (sphereData period)).symm.continuous.comp hProduct)

/-- The explicit positive-period quotient volume. -/
def positiveCanonicalLorentzVolumeMeasure :
    Measure (EffectiveQuotient period) :=
  (positiveFundamentalProductMeasure period).map
    (positiveFundamentalDomainMap period)

/-- This presentation is exactly the canonical intrinsic Program-P volume,
not a separately chosen temporal measure. -/
theorem positiveCanonicalLorentzVolumeMeasure_eq_intrinsic :
    positiveCanonicalLorentzVolumeMeasure period =
      intrinsicCanonicalLorentzVolumeMeasure period hPeriodPos.out.ne' := by
  change
    Measure.map (positiveFundamentalDomainMap period)
        (((volume : Measure EuclideanR4).toSphere).prod
          (volume.restrict (Set.Ioc 0 period))) =
      Measure.map (positiveFundamentalDomainMap period)
        (((volume : Measure EuclideanR4).toSphere).prod
          (volume.restrict (Set.Ioc (min 0 period) (max 0 period))))
  rw [min_eq_left hPeriodPos.out.le, max_eq_right hPeriodPos.out.le]

/-- Total mass of the positive fundamental product volume. -/
def canonicalTemporalMass : ENNReal :=
  (volume : Measure EuclideanR4).toSphere Set.univ *
    ENNReal.ofReal period

theorem canonicalTemporalMass_ne_zero :
    canonicalTemporalMass period ≠ 0 := by
  apply mul_ne_zero
  · exact (Measure.measure_univ_ne_zero).2
      (Measure.toSphere_ne_zero (volume : Measure EuclideanR4))
  · exact ENNReal.ofReal_ne_zero_iff.mpr hPeriodPos.out

theorem canonicalTemporalMass_ne_top :
    canonicalTemporalMass period ≠ (∞ : ENNReal) := by
  exact ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top

/-- Exact temporal marginal of the unnormalized canonical quotient volume. -/
theorem mappingTorusTimeCircle_positiveCanonical_marginal :
    Measure.map (mappingTorusTimeCircle period)
        (positiveCanonicalLorentzVolumeMeasure period) =
      canonicalTemporalMass period • AddCircle.haarAddCircle := by
  rw [positiveCanonicalLorentzVolumeMeasure]
  rw [Measure.map_map (mappingTorusTimeCircle_continuous period).measurable
    (positiveFundamentalDomainMap_continuous period).measurable]
  have hComposition :
      mappingTorusTimeCircle period ∘ positiveFundamentalDomainMap period =
        fun point : StandardSphere × Real =>
          (point.2 : AddCircle period) := by
    funext point
    rfl
  rw [hComposition]
  change
    Measure.map
        ((fun time : Real => (time : AddCircle period)) ∘ Prod.snd)
        (((volume : Measure EuclideanR4).toSphere).prod
          (volume.restrict (Set.Ioc 0 period))) = _
  rw [← Measure.map_map AddCircle.measurable_mk' measurable_snd]
  rw [Measure.map_snd_prod, Measure.map_smul]
  have hTime := (AddCircle.measurePreserving_mk period 0).map_eq
  simp only [zero_add] at hTime
  rw [hTime, AddCircle.volume_eq_smul_haarAddCircle, smul_smul]
  rfl

/-- Probability normalization of the same canonical physical volume. -/
def normalizedCanonicalLorentzVolumeMeasure :
    Measure (EffectiveQuotient period) :=
  (canonicalTemporalMass period)⁻¹ •
    intrinsicCanonicalLorentzVolumeMeasure period hPeriodPos.out.ne'

local instance normalizedCanonicalLorentzVolumeMeasure_isFinite :
    IsFiniteMeasure (normalizedCanonicalLorentzVolumeMeasure period) := by
  letI : IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriodPos.out.ne') :=
    intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriodPos.out.ne'
  unfold normalizedCanonicalLorentzVolumeMeasure
  exact Measure.smul_finite _
    (ENNReal.inv_ne_top.mpr (canonicalTemporalMass_ne_zero period))

/-- The global quotient time map is measure preserving after the canonical
probability normalization. -/
theorem mappingTorusTimeCircle_measurePreserving :
    MeasurePreserving (mappingTorusTimeCircle period)
      (normalizedCanonicalLorentzVolumeMeasure period)
      AddCircle.haarAddCircle := by
  refine ⟨(mappingTorusTimeCircle_continuous period).measurable, ?_⟩
  rw [normalizedCanonicalLorentzVolumeMeasure, Measure.map_smul,
    ← positiveCanonicalLorentzVolumeMeasure_eq_intrinsic period,
    mappingTorusTimeCircle_positiveCanonical_marginal period, smul_smul]
  have hMass :
      (canonicalTemporalMass period)⁻¹ * canonicalTemporalMass period = 1 :=
    ENNReal.inv_mul_cancel
      (canonicalTemporalMass_ne_zero period)
      (canonicalTemporalMass_ne_top period)
  rw [hMass, one_smul]

/-- Complex `L²` sections on the actual D8 quotient with the normalized
canonical Lorentz volume. -/
abbrev CanonicalTemporalQuotientL2 :=
  Lp Complex 2 (normalizedCanonicalLorentzVolumeMeasure period)

/-- Fourier synthesis on the ordinary time circle. -/
def circleFourierSynthesis :
    CircleHilbert ≃ₗᵢ[Complex]
      Lp Complex 2 (@AddCircle.haarAddCircle period hPeriodPos) :=
  (@fourierBasis period hPeriodPos).repr.symm

/-- Infinite Fourier synthesis as a genuine `L²` section on the actual
mapping-torus quotient. -/
def mappingTorusTemporalL2Synthesis :
    CircleHilbert →ₗᵢ[Complex] CanonicalTemporalQuotientL2 period :=
  (Lp.compMeasurePreservingₗᵢ Complex
    (mappingTorusTimeCircle period)
    (mappingTorusTimeCircle_measurePreserving period)).comp
      (circleFourierSynthesis period).toLinearIsometry

/-- The true quotient `L²` Fourier mode. -/
def mappingTorusTemporalModeL2 (mode : Int) :
    CanonicalTemporalQuotientL2 period :=
  mappingTorusTemporalL2Synthesis period
    (lp.single 2 mode (1 : Complex))

/-- Every square-summable coefficient sequence has a convergent infinite
Fourier series in the actual quotient `L²` norm. -/
theorem mappingTorusTemporalL2_hasSum
    (coefficients : CircleHilbert) :
    HasSum
      (fun mode : Int => coefficients mode •
        mappingTorusTemporalModeL2 period mode)
      (mappingTorusTemporalL2Synthesis period coefficients) := by
  have hSeries :
      HasSum (fun mode : Int =>
        lp.single 2 mode (coefficients mode)) coefficients :=
    lp.hasSum_single ENNReal.ofNat_ne_top coefficients
  have hMapped := hSeries.map
    (mappingTorusTemporalL2Synthesis period)
    (mappingTorusTemporalL2Synthesis period).continuous
  simpa only [Function.comp_def, mappingTorusTemporalModeL2, ← map_smul,
    ← lp.single_smul, smul_eq_mul, mul_one] using hMapped

/-- Haar-integral Fourier coefficients recover the input sequence exactly
before the measure-preserving pullback to the quotient. -/
theorem circleFourierSynthesis_coefficient
    (coefficients : CircleHilbert) (mode : Int) :
    fourierCoeff (circleFourierSynthesis period coefficients) mode =
      coefficients mode := by
  rw [← fourierBasis_repr]
  exact congrArg (fun state : CircleHilbert => state mode)
    ((@fourierBasis period hPeriodPos).repr.apply_symm_apply coefficients)

theorem mappingTorusTemporalL2Synthesis_injective :
    Function.Injective (mappingTorusTemporalL2Synthesis period) :=
  (mappingTorusTemporalL2Synthesis period).injective

/-- Embed the previously used finite coefficient sequences into the complete
coefficient Hilbert space. -/
def finiteTemporalCoefficientsToCircleHilbert :
    FiniteTemporalFourierCoefficients →ₗ[Complex] CircleHilbert :=
  Finsupp.linearCombination Complex
    (fun mode : Int => lp.single 2 mode (1 : Complex))

@[simp]
theorem finiteTemporalCoefficientsToCircleHilbert_apply
    (coefficients : FiniteTemporalFourierCoefficients) (mode : Int) :
    finiteTemporalCoefficientsToCircleHilbert coefficients mode =
      coefficients mode := by
  classical
  rw [finiteTemporalCoefficientsToCircleHilbert,
    Finsupp.linearCombination_apply]
  simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply,
    lp.coeFn_sum, lp.coeFn_smul, lp.single_apply, smul_eq_mul,
    Pi.single_apply]
  rw [Finset.sum_eq_single mode]
  · simp
  · intro other _ hOther
    simp [lp.single_apply, Ne.symm hOther]
  · intro hMode
    have hCoeff : coefficients mode = 0 := by
      simpa [Finsupp.mem_support_iff] using hMode
    simp [hCoeff]

/-- On finite support, complete Fourier synthesis is exactly the old smooth
Fourier polynomial viewed in circle `L²`. -/
theorem circleFourierSynthesis_finite_eq_polynomialL2
    (coefficients : FiniteTemporalFourierCoefficients) :
    circleFourierSynthesis period
        (finiteTemporalCoefficientsToCircleHilbert coefficients) =
      ((temporalFourierPolynomialCircleLinearMap period coefficients).continuous
        |>.memLp_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace
            (temporalFourierPolynomialCircleLinearMap period coefficients))).toLp
        (temporalFourierPolynomialCircleLinearMap period coefficients) := by
  apply (@fourierBasis period hPeriodPos).repr.injective
  ext mode
  rw [fourierBasis_repr, fourierBasis_repr,
    circleFourierSynthesis_coefficient period,
    finiteTemporalCoefficientsToCircleHilbert_apply]
  have hMem : MemLp
      (temporalFourierPolynomialCircleLinearMap period coefficients) 2
      (@AddCircle.haarAddCircle period hPeriodPos) :=
    (temporalFourierPolynomialCircleLinearMap period coefficients).continuous
      |>.memLp_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace
          (temporalFourierPolynomialCircleLinearMap period coefficients))
  have hCoeff := congrFun
    (fourierCoeff_congr_ae hMem.coeFn_toLp) mode
  rw [hCoeff]
  exact (temporalFourierPolynomialCircle_coefficient
    period coefficients mode).symm

/-- Consequently the infinite construction extends the actual finite smooth
mapping-torus fields, after their canonical inclusion into quotient `L²`. -/
theorem mappingTorusTemporalL2Synthesis_finite_eq_smoothFieldToL2
    (coefficients : FiniteTemporalFourierCoefficients) :
    mappingTorusTemporalL2Synthesis period
        (finiteTemporalCoefficientsToCircleHilbert coefficients) =
      smoothFieldToL2 period hPeriodPos.out.ne' Complex
        (normalizedCanonicalLorentzVolumeMeasure period)
        (finiteTemporalFourierFieldLinearMap period coefficients) := by
  let polynomial := temporalFourierPolynomialCircleLinearMap period coefficients
  have hMem : MemLp polynomial 2 AddCircle.haarAddCircle :=
    polynomial.continuous.memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace polynomial)
  change Lp.compMeasurePreserving
      (mappingTorusTimeCircle period)
      (mappingTorusTimeCircle_measurePreserving period)
      (circleFourierSynthesis period
        (finiteTemporalCoefficientsToCircleHilbert coefficients)) = _
  rw [circleFourierSynthesis_finite_eq_polynomialL2 period]
  change Lp.compMeasurePreserving
      (mappingTorusTimeCircle period)
      (mappingTorusTimeCircle_measurePreserving period)
      (hMem.toLp polynomial) = _
  rw [Lp.toLp_compMeasurePreserving hMem
    (mappingTorusTimeCircle_measurePreserving period)]
  apply Lp.ext
  filter_upwards
    [(hMem.comp_measurePreserving
      (mappingTorusTimeCircle_measurePreserving period)).coeFn_toLp,
      smoothFieldToL2_ae period hPeriodPos.out.ne' Complex
        (normalizedCanonicalLorentzVolumeMeasure period)
        (finiteTemporalFourierFieldLinearMap period coefficients)]
    with point hLeft hRight
  rw [hLeft, hRight]
  obtain ⟨representative, rfl⟩ :=
    mappingTorusMk_surjective (sphereData period) point
  exact (finiteTemporalFourierField_mk_eq_circle
    period coefficients representative).symm

/-- Physical first-order temporal Sobolev weight. -/
def temporalH1Weight (mode : Int) : Real :=
  1 + ‖temporalFourierDerivativeMultiplier period mode‖ ^ 2

theorem temporalH1Weight_pos (mode : Int) :
    0 < temporalH1Weight period mode := by
  unfold temporalH1Weight
  positivity

/-- The weighted coefficient completion stores
`sqrt(1 + |2π i n/T|²) * a_n` as an ordinary `ℓ²` sequence. -/
abbrev TemporalH1CoefficientHilbert (_period : Real) := CircleHilbert

/-- Coefficient multiplier recovering the underlying field coefficients. -/
def temporalH1FieldScale (mode : Int) : Complex :=
  (Real.sqrt (temporalH1Weight period mode) : Complex)⁻¹

/-- Coefficient multiplier recovering the temporal derivative. -/
def temporalH1DerivativeScale (mode : Int) : Complex :=
  temporalFourierDerivativeMultiplier period mode *
    temporalH1FieldScale period mode

theorem one_le_sqrt_temporalH1Weight (mode : Int) :
    1 ≤ Real.sqrt (temporalH1Weight period mode) := by
  rw [← Real.sqrt_one]
  apply Real.sqrt_le_sqrt
  unfold temporalH1Weight
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem temporalH1FieldScale_norm_le_one (mode : Int) :
    ‖temporalH1FieldScale period mode‖ ≤ 1 := by
  rw [temporalH1FieldScale, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact inv_le_one_of_one_le₀ (one_le_sqrt_temporalH1Weight period mode)

theorem temporalMultiplier_norm_le_sqrtWeight (mode : Int) :
    ‖temporalFourierDerivativeMultiplier period mode‖ ≤
      Real.sqrt (temporalH1Weight period mode) := by
  rw [← abs_of_nonneg (norm_nonneg
      (temporalFourierDerivativeMultiplier period mode)),
    ← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  unfold temporalH1Weight
  exact le_add_of_nonneg_left zero_le_one

theorem temporalH1DerivativeScale_norm_le_one (mode : Int) :
    ‖temporalH1DerivativeScale period mode‖ ≤ 1 := by
  rw [temporalH1DerivativeScale, norm_mul, temporalH1FieldScale,
    norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_inv_le_one_of_le₀
    (temporalMultiplier_norm_le_sqrtWeight period mode)
    (Real.sqrt_nonneg _)

/-- A bounded diagonal multiplier on `ℓ²`. -/
def boundedDiagonalImage
    (scale : Int → Complex) (hScale : ∀ mode, ‖scale mode‖ ≤ 1)
    (state : CircleHilbert) : CircleHilbert := by
  let image : Int → Complex := fun mode => scale mode * state mode
  have hImage : Memℓp image 2 := (lp.memℓp state).mono' (fun mode => by
    rw [show image mode = scale mode * state mode by rfl, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hScale mode))
  exact ⟨image, hImage⟩

@[simp]
theorem boundedDiagonalImage_apply
    (scale : Int → Complex) (hScale : ∀ mode, ‖scale mode‖ ≤ 1)
    (state : CircleHilbert) (mode : Int) :
    boundedDiagonalImage scale hScale state mode = scale mode * state mode :=
  rfl

theorem boundedDiagonalImage_norm_le
    (scale : Int → Complex) (hScale : ∀ mode, ‖scale mode‖ ≤ 1)
    (state : CircleHilbert) :
    ‖boundedDiagonalImage scale hScale state‖ ≤ ‖state‖ := by
  exact lp.norm_mono (by norm_num) (fun mode => by
    rw [boundedDiagonalImage_apply, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hScale mode))

/-- Bounded diagonal multiplier as a continuous linear operator. -/
def boundedDiagonalOperator
    (scale : Int → Complex) (hScale : ∀ mode, ‖scale mode‖ ≤ 1) :
    CircleHilbert →L[Complex] CircleHilbert :=
  LinearMap.mkContinuous
    { toFun := boundedDiagonalImage scale hScale
      map_add' := by
        intro first second
        ext mode
        simp [boundedDiagonalImage_apply, mul_add]
      map_smul' := by
        intro scalar state
        ext mode
        simp [boundedDiagonalImage_apply]
        ring }
    1 (fun state => by
      simpa using boundedDiagonalImage_norm_le scale hScale state)

/-- Decode the field coefficients from the completed weighted coordinates. -/
def temporalH1FieldCoefficientOperator :
    TemporalH1CoefficientHilbert period →L[Complex] CircleHilbert :=
  boundedDiagonalOperator (temporalH1FieldScale period)
    (temporalH1FieldScale_norm_le_one period)

/-- Decode the physical temporal-derivative coefficients. -/
def temporalH1DerivativeCoefficientOperator :
    TemporalH1CoefficientHilbert period →L[Complex] CircleHilbert :=
  boundedDiagonalOperator (temporalH1DerivativeScale period)
    (temporalH1DerivativeScale_norm_le_one period)

@[simp]
theorem temporalH1FieldCoefficientOperator_apply
    (state : TemporalH1CoefficientHilbert period) (mode : Int) :
    temporalH1FieldCoefficientOperator period state mode =
      temporalH1FieldScale period mode * state mode :=
  rfl

@[simp]
theorem temporalH1DerivativeCoefficientOperator_apply
    (state : TemporalH1CoefficientHilbert period) (mode : Int) :
    temporalH1DerivativeCoefficientOperator period state mode =
      temporalFourierDerivativeMultiplier period mode *
        temporalH1FieldCoefficientOperator period state mode := by
  change temporalH1DerivativeScale period mode * state mode = _
  rw [temporalH1DerivativeScale,
    temporalH1FieldCoefficientOperator_apply]
  ring

theorem temporalH1FieldCoefficientOperator_injective :
    Function.Injective (temporalH1FieldCoefficientOperator period) := by
  intro first second hEqual
  ext mode
  have hMode := congrArg (fun state : CircleHilbert => state mode) hEqual
  rw [temporalH1FieldCoefficientOperator_apply,
    temporalH1FieldCoefficientOperator_apply] at hMode
  exact mul_left_cancel₀
    (inv_ne_zero (Complex.ofReal_ne_zero.mpr
      (Real.sqrt_ne_zero'.2 (temporalH1Weight_pos period mode)))) hMode

/-- The completed weighted field as an actual quotient `L²` section. -/
def temporalH1FieldL2 :
    TemporalH1CoefficientHilbert period →L[Complex]
      CanonicalTemporalQuotientL2 period :=
  (mappingTorusTemporalL2Synthesis period).toContinuousLinearMap.comp
    (temporalH1FieldCoefficientOperator period)

/-- Its physical temporal spectral derivative as a second quotient `L²`
section. -/
def temporalH1DerivativeL2 :
    TemporalH1CoefficientHilbert period →L[Complex]
      CanonicalTemporalQuotientL2 period :=
  (mappingTorusTemporalL2Synthesis period).toContinuousLinearMap.comp
    (temporalH1DerivativeCoefficientOperator period)

theorem temporalH1FieldL2_injective :
    Function.Injective (temporalH1FieldL2 period) := by
  exact (mappingTorusTemporalL2Synthesis_injective period).comp
    (temporalH1FieldCoefficientOperator_injective period)

/-- Infinite field series of every weighted coefficient vector converges in
the true quotient `L²` norm. -/
theorem temporalH1FieldL2_hasSum
    (state : TemporalH1CoefficientHilbert period) :
    HasSum
      (fun mode : Int =>
        (temporalH1FieldCoefficientOperator period state mode) •
          mappingTorusTemporalModeL2 period mode)
      (temporalH1FieldL2 period state) :=
  by
    simpa [temporalH1FieldL2] using
      mappingTorusTemporalL2_hasSum period
        (temporalH1FieldCoefficientOperator period state)

/-- The physical temporal-derivative series converges independently in the
same quotient `L²` space. -/
theorem temporalH1DerivativeL2_hasSum
    (state : TemporalH1CoefficientHilbert period) :
    HasSum
      (fun mode : Int =>
        (temporalFourierDerivativeMultiplier period mode *
          temporalH1FieldCoefficientOperator period state mode) •
            mappingTorusTemporalModeL2 period mode)
      (temporalH1DerivativeL2 period state) := by
  simpa [temporalH1DerivativeL2,
    temporalH1DerivativeCoefficientOperator_apply] using
    mappingTorusTemporalL2_hasSum period
      (temporalH1DerivativeCoefficientOperator period state)

/-- Summary of the honest infinite temporal result. -/
theorem mappingTorus_infiniteTemporalFourierSobolev_bridge4D :
    Function.Injective (mappingTorusTemporalL2Synthesis period) ∧
      (∀ coefficients : CircleHilbert,
        HasSum
          (fun mode : Int => coefficients mode •
            mappingTorusTemporalModeL2 period mode)
          (mappingTorusTemporalL2Synthesis period coefficients)) ∧
      Function.Injective (temporalH1FieldL2 period) ∧
      (∀ state : TemporalH1CoefficientHilbert period,
        HasSum
          (fun mode : Int =>
            (temporalFourierDerivativeMultiplier period mode *
              temporalH1FieldCoefficientOperator period state mode) •
                mappingTorusTemporalModeL2 period mode)
          (temporalH1DerivativeL2 period state)) :=
  ⟨mappingTorusTemporalL2Synthesis_injective period,
    mappingTorusTemporalL2_hasSum period,
    temporalH1FieldL2_injective period,
    temporalH1DerivativeL2_hasSum period⟩

end

end P0EFTJanusMappingTorusInfiniteTemporalFourierSobolevBridge4D
end JanusFormal
