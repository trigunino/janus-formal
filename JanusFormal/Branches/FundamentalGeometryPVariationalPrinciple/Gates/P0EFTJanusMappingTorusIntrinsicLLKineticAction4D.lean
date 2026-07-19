import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicMetricBVThroatBracket4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalThroatPTMeasureInvariance4D

/-!
# Intrinsic LL kinetic action on the actual throat

The auxiliary positive weight is replaced by the genuine inverse of the
nondegenerate intrinsic throat metric.  The resulting Lorentzian contraction
is not claimed positive.  Its first variation, symmetric Hessian and canonical
PT covariance are exact; global differentiation uses explicit integrability
hypotheses and asserts no strong PDE.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusIntrinsicLLKineticAction4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped Manifold ContDiff Topology
open Bundle MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusMappingTorusPTInvolution
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothPTInvolution
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatPTRadical4D
open P0EFTJanusMappingTorusIntrinsicMetricThroatNondegenerate4D
open P0EFTJanusMappingTorusIntrinsicMetricBVThroatBracket4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusCanonicalThroatPTMeasureInvariance4D
open P0EFTJanusMappingTorusGlobalLLCovariance4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

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

/-- One scalar component of the genuine manifold derivative of an LL field. -/
def intrinsicLLDifferentialCovector
    (field : SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) (component : Fin 4) :
    ThroatCotangentFiber period hPeriod point :=
  (EuclideanSpace.proj (𝕜 := Real) component).comp
    (mvfderiv throatCoverModelWithCorners field.toFun point)

theorem intrinsicLLDifferentialCovector_add
    (first second : SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) (component : Fin 4) :
    intrinsicLLDifferentialCovector period hPeriod (first + second) point component =
      intrinsicLLDifferentialCovector period hPeriod first point component +
        intrinsicLLDifferentialCovector period hPeriod second point component := by
  unfold intrinsicLLDifferentialCovector
  change (EuclideanSpace.proj component).comp
      (mvfderiv throatCoverModelWithCorners
        (first.toFun + second.toFun) point) = _
  rw [mvfderiv_add
    ((first.contMDiff_toFun.mdifferentiable (by simp)) point)
    ((second.contMDiff_toFun.mdifferentiable (by simp)) point)]
  ext vector
  rfl

theorem intrinsicLLDifferentialCovector_smul
    (scalar : Real) (field : SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) (component : Fin 4) :
    intrinsicLLDifferentialCovector period hPeriod (scalar • field) point component =
      scalar • intrinsicLLDifferentialCovector period hPeriod field point component := by
  unfold intrinsicLLDifferentialCovector
  change (EuclideanSpace.proj component).comp
      (mvfderiv throatCoverModelWithCorners
        (scalar • field.toFun) point) = _
  unfold mvfderiv
  rw [const_smul_mfderiv
    ((field.contMDiff_toFun.mdifferentiable (by simp)) point) scalar]
  ext vector
  rfl

/-- Pairing of cotangent vectors by the inverse intrinsic throat metric. -/
def intrinsicThroatInversePairingAt
    (point : EffectiveThroat period hPeriod)
    (first second : ThroatCotangentFiber period hPeriod point) : Real :=
  second (intrinsicThroatInverseMusical period hPeriod point first)

theorem intrinsicThroatInversePairingAt_symmetric
    (point : EffectiveThroat period hPeriod)
    (first second : ThroatCotangentFiber period hPeriod point) :
    intrinsicThroatInversePairingAt period hPeriod point first second =
      intrinsicThroatInversePairingAt period hPeriod point second first := by
  unfold intrinsicThroatInversePairingAt
  calc
    second (intrinsicThroatInverseMusical period hPeriod point first) =
        (intrinsicSmoothNondegenerateThroatMetric period hPeriod).1.tensor point
          (intrinsicThroatInverseMusical period hPeriod point second)
          (intrinsicThroatInverseMusical period hPeriod point first) := by
      rw [← intrinsicThroatMusical_apply period hPeriod point,
        intrinsicThroatMusical_inverse_apply]
    _ = (intrinsicSmoothNondegenerateThroatMetric period hPeriod).1.tensor point
          (intrinsicThroatInverseMusical period hPeriod point first)
          (intrinsicThroatInverseMusical period hPeriod point second) :=
      (intrinsicSmoothNondegenerateThroatMetric period hPeriod).1.symmetric
        point _ _
    _ = first (intrinsicThroatInverseMusical period hPeriod point second) := by
      rw [← intrinsicThroatMusical_apply period hPeriod point,
        intrinsicThroatMusical_inverse_apply]

theorem intrinsicThroatInversePairingAt_add_left
    (point : EffectiveThroat period hPeriod)
    (first second third : ThroatCotangentFiber period hPeriod point) :
    intrinsicThroatInversePairingAt period hPeriod point (first + second) third =
      intrinsicThroatInversePairingAt period hPeriod point first third +
        intrinsicThroatInversePairingAt period hPeriod point second third := by
  simp [intrinsicThroatInversePairingAt]

theorem intrinsicThroatInversePairingAt_smul_left
    (point : EffectiveThroat period hPeriod) (scalar : Real)
    (first second : ThroatCotangentFiber period hPeriod point) :
    intrinsicThroatInversePairingAt period hPeriod point (scalar • first) second =
      scalar * intrinsicThroatInversePairingAt period hPeriod point first second := by
  simp [intrinsicThroatInversePairingAt]

theorem intrinsicThroatInversePairingAt_add_right
    (point : EffectiveThroat period hPeriod)
    (first second third : ThroatCotangentFiber period hPeriod point) :
    intrinsicThroatInversePairingAt period hPeriod point first (second + third) =
      intrinsicThroatInversePairingAt period hPeriod point first second +
        intrinsicThroatInversePairingAt period hPeriod point first third := by
  simp [intrinsicThroatInversePairingAt]

theorem intrinsicThroatInversePairingAt_smul_right
    (point : EffectiveThroat period hPeriod) (scalar : Real)
    (first second : ThroatCotangentFiber period hPeriod point) :
    intrinsicThroatInversePairingAt period hPeriod point first (scalar • second) =
      scalar * intrinsicThroatInversePairingAt period hPeriod point first second := by
  simp [intrinsicThroatInversePairingAt]

/-- The true inverse-metric contraction of two LL first derivatives. -/
def intrinsicLLDerivativePairing
    (first second : SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) : Real :=
  ∑ component : Fin 4,
    intrinsicThroatInversePairingAt period hPeriod point
      (intrinsicLLDifferentialCovector period hPeriod first point component)
      (intrinsicLLDifferentialCovector period hPeriod second point component)

theorem intrinsicLLDerivativePairing_symmetric
    (first second : SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) :
    intrinsicLLDerivativePairing period hPeriod first second point =
      intrinsicLLDerivativePairing period hPeriod second first point := by
  apply Finset.sum_congr rfl
  intro component _
  exact intrinsicThroatInversePairingAt_symmetric period hPeriod point _ _

theorem intrinsicLLDerivativePairing_add_left
    (first second third : SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) :
    intrinsicLLDerivativePairing period hPeriod (first + second) third point =
      intrinsicLLDerivativePairing period hPeriod first third point +
        intrinsicLLDerivativePairing period hPeriod second third point := by
  unfold intrinsicLLDerivativePairing
  simp_rw [intrinsicLLDifferentialCovector_add,
    intrinsicThroatInversePairingAt_add_left]
  exact Finset.sum_add_distrib

theorem intrinsicLLDerivativePairing_add_right
    (first second third : SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) :
    intrinsicLLDerivativePairing period hPeriod first (second + third) point =
      intrinsicLLDerivativePairing period hPeriod first second point +
        intrinsicLLDerivativePairing period hPeriod first third point := by
  unfold intrinsicLLDerivativePairing
  simp_rw [intrinsicLLDifferentialCovector_add,
    intrinsicThroatInversePairingAt_add_right]
  exact Finset.sum_add_distrib

theorem intrinsicLLDerivativePairing_smul_left
    (scalar : Real)
    (first second : SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) :
    intrinsicLLDerivativePairing period hPeriod (scalar • first) second point =
      scalar * intrinsicLLDerivativePairing period hPeriod first second point := by
  unfold intrinsicLLDerivativePairing
  simp_rw [intrinsicLLDifferentialCovector_smul,
    intrinsicThroatInversePairingAt_smul_left, Finset.mul_sum]

theorem intrinsicLLDerivativePairing_smul_right
    (scalar : Real)
    (first second : SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) :
    intrinsicLLDerivativePairing period hPeriod first (scalar • second) point =
      scalar * intrinsicLLDerivativePairing period hPeriod first second point := by
  unfold intrinsicLLDerivativePairing
  simp_rw [intrinsicLLDifferentialCovector_smul,
    intrinsicThroatInversePairingAt_smul_right, Finset.mul_sum]

/-- Intrinsic Lorentzian kinetic density; no positivity is asserted. -/
def intrinsicLLKineticDensity
    (field : SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) : Real :=
  (1 / 2 : Real) *
    intrinsicLLDerivativePairing period hPeriod field field point

/-- Intrinsic LL kinetic action on an arbitrary throat measure. -/
def intrinsicLLKineticAction
    (field : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) : Real :=
  ∫ point, intrinsicLLKineticDensity period hPeriod field point ∂mu

/-- Exact quadratic expansion along an arbitrary smooth LL variation. -/
theorem intrinsicLLKineticDensity_affine_quadratic
    (field direction : SmoothThroatField period hPeriod LLFieldFiber)
    (epsilon : Real) (point : EffectiveThroat period hPeriod) :
    intrinsicLLKineticDensity period hPeriod
        (field + epsilon • direction) point =
      intrinsicLLKineticDensity period hPeriod field point +
        epsilon * intrinsicLLDerivativePairing period hPeriod
          field direction point +
        epsilon ^ 2 * intrinsicLLKineticDensity period hPeriod direction point := by
  unfold intrinsicLLKineticDensity
  rw [intrinsicLLDerivativePairing_add_left,
    intrinsicLLDerivativePairing_add_right,
    intrinsicLLDerivativePairing_add_right,
    intrinsicLLDerivativePairing_smul_left,
    intrinsicLLDerivativePairing_smul_right,
    intrinsicLLDerivativePairing_smul_right,
    intrinsicLLDerivativePairing_smul_left,
    intrinsicLLDerivativePairing_symmetric period hPeriod direction field]
  ring

/-- Integrated first variation of the intrinsic kinetic action. -/
def intrinsicLLKineticFirstVariation
    (field direction : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) : Real :=
  ∫ point, intrinsicLLDerivativePairing period hPeriod
    field direction point ∂mu

/-- Bilinear Hessian of the intrinsic kinetic action. -/
def intrinsicLLKineticHessian
    (first second : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) : Real :=
  ∫ point, intrinsicLLDerivativePairing period hPeriod
    first second point ∂mu

theorem intrinsicLLKineticHessian_symmetric
    (first second : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    intrinsicLLKineticHessian period hPeriod first second mu =
      intrinsicLLKineticHessian period hPeriod second first mu := by
  unfold intrinsicLLKineticHessian
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun point =>
    intrinsicLLDerivativePairing_symmetric period hPeriod first second point

/-- Exact integrated quadratic expansion under precisely the three required
integrability hypotheses. -/
theorem intrinsicLLKineticAction_affine_quadratic
    (field direction : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) (epsilon : Real)
    (hBase : Integrable (intrinsicLLKineticDensity period hPeriod field) mu)
    (hFirst : Integrable
      (intrinsicLLDerivativePairing period hPeriod field direction) mu)
    (hDirection : Integrable
      (intrinsicLLKineticDensity period hPeriod direction) mu) :
    intrinsicLLKineticAction period hPeriod (field + epsilon • direction) mu =
      intrinsicLLKineticAction period hPeriod field mu +
        epsilon * intrinsicLLKineticFirstVariation period hPeriod
          field direction mu +
        epsilon ^ 2 * intrinsicLLKineticAction period hPeriod direction mu := by
  unfold intrinsicLLKineticAction intrinsicLLKineticFirstVariation
  simp_rw [intrinsicLLKineticDensity_affine_quadratic period hPeriod
    field direction epsilon]
  calc
    (∫ point,
        intrinsicLLKineticDensity period hPeriod field point +
            epsilon * intrinsicLLDerivativePairing period hPeriod
              field direction point +
          epsilon ^ 2 * intrinsicLLKineticDensity period hPeriod direction point
        ∂mu) =
      (∫ point,
        intrinsicLLKineticDensity period hPeriod field point +
          epsilon * intrinsicLLDerivativePairing period hPeriod
            field direction point ∂mu) +
        ∫ point, epsilon ^ 2 *
          intrinsicLLKineticDensity period hPeriod direction point ∂mu := by
      simpa only [Pi.add_apply] using
        integral_add (hBase.add (hFirst.const_mul epsilon))
          (hDirection.const_mul (epsilon ^ 2))
    _ = ((∫ point, intrinsicLLKineticDensity period hPeriod field point ∂mu) +
          ∫ point, epsilon * intrinsicLLDerivativePairing period hPeriod
            field direction point ∂mu) +
        ∫ point, epsilon ^ 2 *
          intrinsicLLKineticDensity period hPeriod direction point ∂mu := by
      congr 1
      simpa only [Pi.add_apply] using
        integral_add hBase (hFirst.const_mul epsilon)
    _ = _ := by simp only [integral_const_mul]

private theorem intrinsic_quadratic_hasDerivAt
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

/-- The actual first derivative of the intrinsic action. -/
theorem intrinsicLLKineticAction_affine_hasDerivAt
    (field direction : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (EffectiveThroat period hPeriod))
    (hBase : Integrable (intrinsicLLKineticDensity period hPeriod field) mu)
    (hFirst : Integrable
      (intrinsicLLDerivativePairing period hPeriod field direction) mu)
    (hDirection : Integrable
      (intrinsicLLKineticDensity period hPeriod direction) mu) :
    HasDerivAt
      (fun epsilon : Real => intrinsicLLKineticAction period hPeriod
        (field + epsilon • direction) mu)
      (intrinsicLLKineticFirstVariation period hPeriod field direction mu) 0 := by
  rw [show (fun epsilon : Real => intrinsicLLKineticAction period hPeriod
      (field + epsilon • direction) mu) = fun epsilon : Real =>
        intrinsicLLKineticAction period hPeriod field mu +
          epsilon * intrinsicLLKineticFirstVariation period hPeriod
            field direction mu +
          epsilon ^ 2 * intrinsicLLKineticAction period hPeriod direction mu from by
      funext epsilon
      exact intrinsicLLKineticAction_affine_quadratic period hPeriod
        field direction mu epsilon hBase hFirst hDirection]
  exact intrinsic_quadratic_hasDerivAt
    (intrinsicLLKineticAction period hPeriod field mu)
    (intrinsicLLKineticFirstVariation period hPeriod field direction mu)
    (intrinsicLLKineticAction period hPeriod direction mu)

/-- Canonical PT pullback of an LL field on the actual throat. -/
def intrinsicLLFieldPT
    (field : SmoothThroatField period hPeriod LLFieldFiber) :
    SmoothThroatField period hPeriod LLFieldFiber where
  toFun point := field (fixedThroatPT period hPeriod point)
  contMDiff_toFun := field.contMDiff_toFun.comp
    ((fixedThroatPT_contMDiff period hPeriod).of_le (by simp))

/-- Pullback of a throat covector through the true PT differential. -/
def intrinsicThroatCovectorPTPullback
    (point : EffectiveThroat period hPeriod)
    (covector : ThroatCotangentFiber period hPeriod
      (fixedThroatPT period hPeriod point)) :
    ThroatCotangentFiber period hPeriod point :=
  covector.comp
    (throatPTDerivativeEquiv period hPeriod point).toContinuousLinearMap

theorem intrinsicLLDifferentialCovector_pt
    (field : SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) (component : Fin 4) :
    intrinsicLLDifferentialCovector period hPeriod
        (intrinsicLLFieldPT period hPeriod field) point component =
      intrinsicThroatCovectorPTPullback period hPeriod point
        (intrinsicLLDifferentialCovector period hPeriod field
          (fixedThroatPT period hPeriod point) component) := by
  ext vector
  change (mvfderiv throatCoverModelWithCorners
      (field.toFun ∘ fixedThroatPT period hPeriod) point vector) component =
    (mvfderiv throatCoverModelWithCorners field.toFun
      (fixedThroatPT period hPeriod point)
      (throatPTDerivativeEquiv period hPeriod point vector)) component
  have hRaw :
      mfderiv throatCoverModelWithCorners (modelWithCornersSelf Real LLFieldFiber)
          (field.toFun ∘ fixedThroatPT period hPeriod) point vector =
        mfderiv throatCoverModelWithCorners (modelWithCornersSelf Real LLFieldFiber)
          field.toFun (fixedThroatPT period hPeriod point)
          (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
            (fixedThroatPT period hPeriod) point vector) :=
    mfderiv_comp_apply point
      (field.contMDiff_toFun.mdifferentiableAt (by simp))
      ((fixedThroatPT_contMDiff period hPeriod).mdifferentiableAt (by simp))
      vector
  simp only [Function.comp_apply] at hRaw
  have hValue := congrArg
    (fun tangent => NormedSpace.fromTangentSpace
      (field.toFun (fixedThroatPT period hPeriod point)) tangent) hRaw
  exact congrArg (fun value : LLFieldFiber => value component) hValue

theorem intrinsicThroatInversePairingAt_pt
    (point : EffectiveThroat period hPeriod)
    (first second : ThroatCotangentFiber period hPeriod
      (fixedThroatPT period hPeriod point)) :
    intrinsicThroatInversePairingAt period hPeriod point
        (intrinsicThroatCovectorPTPullback period hPeriod point first)
        (intrinsicThroatCovectorPTPullback period hPeriod point second) =
      intrinsicThroatInversePairingAt period hPeriod
        (fixedThroatPT period hPeriod point) first second := by
  unfold intrinsicThroatInversePairingAt intrinsicThroatCovectorPTPullback
  simp only [ContinuousLinearMap.comp_apply]
  have hRaised :
      throatPTDerivativeEquiv period hPeriod point
          (intrinsicThroatInverseMusical period hPeriod point
            (first.comp
              (throatPTDerivativeEquiv period hPeriod point).toContinuousLinearMap)) =
        intrinsicThroatInverseMusical period hPeriod
          (fixedThroatPT period hPeriod point) first := by
    apply (intrinsicThroatMusical period hPeriod
      (fixedThroatPT period hPeriod point)).injective
    apply ContinuousLinearMap.ext
    intro vector
    rw [intrinsicThroatMusical_apply, intrinsicThroatMusical_apply]
    rw [← (throatPTDerivativeEquiv period hPeriod point).apply_symm_apply vector,
      ← intrinsicThroatMetric_pt_natural period hPeriod point]
    rw [← intrinsicThroatMusical_apply period hPeriod point,
      intrinsicThroatMusical_inverse_apply period hPeriod point,
      ← intrinsicThroatMusical_apply period hPeriod
        (fixedThroatPT period hPeriod point),
      intrinsicThroatMusical_inverse_apply period hPeriod
        (fixedThroatPT period hPeriod point)]
    simp
  exact congrArg second hRaised

theorem intrinsicLLDerivativePairing_pt
    (first second : SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) :
    intrinsicLLDerivativePairing period hPeriod
        (intrinsicLLFieldPT period hPeriod first)
        (intrinsicLLFieldPT period hPeriod second) point =
      intrinsicLLDerivativePairing period hPeriod first second
        (fixedThroatPT period hPeriod point) := by
  unfold intrinsicLLDerivativePairing
  apply Finset.sum_congr rfl
  intro component _
  rw [intrinsicLLDifferentialCovector_pt,
    intrinsicLLDifferentialCovector_pt]
  exact intrinsicThroatInversePairingAt_pt period hPeriod point _ _

theorem intrinsicLLKineticDensity_pt
    (field : SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) :
    intrinsicLLKineticDensity period hPeriod
        (intrinsicLLFieldPT period hPeriod field) point =
      intrinsicLLKineticDensity period hPeriod field
        (fixedThroatPT period hPeriod point) := by
  unfold intrinsicLLKineticDensity
  rw [intrinsicLLDerivativePairing_pt]

/-- Intrinsic LL kinetic action with the installed canonical throat volume. -/
def canonicalIntrinsicLLKineticAction
    (field : SmoothThroatField period hPeriod LLFieldFiber) : Real :=
  intrinsicLLKineticAction period hPeriod field
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod)

/-- Unconditional canonical PT covariance of the integrated intrinsic action. -/
theorem canonicalIntrinsicLLKineticAction_pt
    (field : SmoothThroatField period hPeriod LLFieldFiber) :
    canonicalIntrinsicLLKineticAction period hPeriod
        (intrinsicLLFieldPT period hPeriod field) =
      canonicalIntrinsicLLKineticAction period hPeriod field := by
  unfold canonicalIntrinsicLLKineticAction intrinsicLLKineticAction
  calc
    (∫ point, intrinsicLLKineticDensity period hPeriod
        (intrinsicLLFieldPT period hPeriod field) point
      ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) =
      ∫ point, intrinsicLLKineticDensity period hPeriod field
          (fixedThroatPT period hPeriod point)
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall
        (intrinsicLLKineticDensity_pt period hPeriod field)
    _ = _ := by
      simpa [fixedThroatPTMeasurableEquiv] using
        (intrinsicCanonicalThroatVolumeMeasure_pt_measurePreserving
          period hPeriod).integral_comp'
          (intrinsicLLKineticDensity period hPeriod field)

/-- Componentwise inverse-metric contraction of an LL cotangent one-jet. -/
def intrinsicLLCotangentJetPairingAt
    (point : EffectiveThroat period hPeriod)
    (first second : Fin 4 → ThroatCotangentFiber period hPeriod point) : Real :=
  ∑ component : Fin 4,
    intrinsicThroatInversePairingAt period hPeriod point
      (first component) (second component)

/-- Canonical PT pullback of all four LL cotangent components. -/
def intrinsicLLCotangentJetPTPullback
    (point : EffectiveThroat period hPeriod)
    (jet : Fin 4 → ThroatCotangentFiber period hPeriod
      (fixedThroatPT period hPeriod point)) :
    Fin 4 → ThroatCotangentFiber period hPeriod point :=
  fun component => intrinsicThroatCovectorPTPullback period hPeriod point
    (jet component)

/-- Canonical covariance of the genuine inverse-metric LL contraction under
the true throat PT differential. -/
theorem intrinsicLLCotangentJetPairingAt_pt
    (point : EffectiveThroat period hPeriod)
    (first second : Fin 4 → ThroatCotangentFiber period hPeriod
      (fixedThroatPT period hPeriod point)) :
    intrinsicLLCotangentJetPairingAt period hPeriod point
        (intrinsicLLCotangentJetPTPullback period hPeriod point first)
        (intrinsicLLCotangentJetPTPullback period hPeriod point second) =
      intrinsicLLCotangentJetPairingAt period hPeriod
        (fixedThroatPT period hPeriod point) first second := by
  apply Finset.sum_congr rfl
  intro component _
  exact intrinsicThroatInversePairingAt_pt period hPeriod point
    (first component) (second component)

end

end P0EFTJanusMappingTorusIntrinsicLLKineticAction4D
end JanusFormal
