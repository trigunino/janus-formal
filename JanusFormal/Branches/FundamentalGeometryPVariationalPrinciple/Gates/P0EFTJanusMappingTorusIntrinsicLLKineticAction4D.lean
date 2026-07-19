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
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatPTRadical4D
open P0EFTJanusMappingTorusIntrinsicMetricThroatNondegenerate4D
open P0EFTJanusMappingTorusIntrinsicMetricBVThroatBracket4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusCanonicalThroatPTMeasureInvariance4D

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

end

end P0EFTJanusMappingTorusIntrinsicLLKineticAction4D
end JanusFormal
