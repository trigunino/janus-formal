import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGlobalDiagonalLorentzRoot4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusSmoothPTFieldAction4D

/-!
# Smooth diagonal Lorentz pairs and their principal root on D8

This gate puts the complete positive fixed-frame diagonal Lorentz domain on
the actual smooth D8 quotient.  Two independent smooth magnitude fields give
two smooth Lorentz metrics, a smooth relative metric and its pointwise unique
positive principal root.  PT/exchange preserves the same global field domain.

The construction is global in spacetime and in the positive diagonal cone,
but it does not cover noncommuting Lorentz metric pairs.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusSmoothDiagonalLorentzFields4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Matrix.Norms.Frobenius
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusPTInvolution
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothPTFieldAction4D
open P0EFTJanusGlobalDiagonalLorentzRoot4D

variable (period : ℝ) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Two independent smooth magnitude fields in the complete positive diagonal
Lorentz cone. -/
structure SmoothPositiveDiagonalMetricPair where
  plusMagnitude :
    SmoothQuotientField period hPeriod Coefficients4
  minusMagnitude :
    SmoothQuotientField period hPeriod Coefficients4
  plus_pos : ∀ point i, 0 < plusMagnitude point i
  minus_pos : ∀ point i, 0 < minusMagnitude point i

@[ext]
theorem SmoothPositiveDiagonalMetricPair.ext
    {first second : SmoothPositiveDiagonalMetricPair period hPeriod}
    (hPlus : first.plusMagnitude = second.plusMagnitude)
    (hMinus : first.minusMagnitude = second.minusMagnitude) :
    first = second := by
  cases first
  cases second
  cases hPlus
  cases hMinus
  rfl

/-- The two coefficient fields evaluated at one point form an element of the
same global diagonal domain used by the principal-root theorem. -/
def coefficientPairAt
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (point : EffectiveQuotient period hPeriod) : CoefficientPair :=
  (metrics.plusMagnitude point, metrics.minusMagnitude point)

theorem coefficientPairAt_mem_domain
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    coefficientPairAt period hPeriod metrics point ∈
      globalDiagonalLorentzDomain := by
  exact ⟨metrics.plus_pos point, metrics.minus_pos point⟩

private def signedSpectrumField
    (field : SmoothQuotientField period hPeriod Coefficients4) :
    SmoothQuotientField period hPeriod Coefficients4 where
  toFun := fun point i => signature i * field point i
  contMDiff_toFun := by
    rw [contMDiff_pi_space]
    intro i
    exact contMDiff_const.mul
      ((contMDiff_pi_space.mp field.contMDiff_toFun) i)

private def diagonalMatrixField
    (field : SmoothQuotientField period hPeriod Coefficients4) :
    SmoothQuotientField period hPeriod Matrix4 where
  toFun := fun point => Matrix.diagonal (field point)
  contMDiff_toFun :=
    diagonalContinuousLinearMap.contMDiff.comp field.contMDiff_toFun

/-- The plus Lorentz metric is a genuine smooth matrix field. -/
def plusLorentzMetricField
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod) :
    SmoothQuotientField period hPeriod Matrix4 :=
  diagonalMatrixField period hPeriod
    (signedSpectrumField period hPeriod metrics.plusMagnitude)

/-- The minus Lorentz metric is a genuine smooth matrix field. -/
def minusLorentzMetricField
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod) :
    SmoothQuotientField period hPeriod Matrix4 :=
  diagonalMatrixField period hPeriod
    (signedSpectrumField period hPeriod metrics.minusMagnitude)

@[simp]
theorem plusLorentzMetricField_apply
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    plusLorentzMetricField period hPeriod metrics point =
      lorentzMetric (metrics.plusMagnitude point) :=
  rfl

@[simp]
theorem minusLorentzMetricField_apply
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    minusLorentzMetricField period hPeriod metrics point =
      lorentzMetric (metrics.minusMagnitude point) :=
  rfl

/-- Smooth eigenvalue ratios of the relative metric. -/
def relativeRatioField
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod) :
    SmoothQuotientField period hPeriod Coefficients4 where
  toFun := fun point i =>
    metrics.minusMagnitude point i / metrics.plusMagnitude point i
  contMDiff_toFun := by
    rw [contMDiff_pi_space]
    intro i
    exact
      ((contMDiff_pi_space.mp
          metrics.minusMagnitude.contMDiff_toFun) i).div₀
        ((contMDiff_pi_space.mp
          metrics.plusMagnitude.contMDiff_toFun) i)
        (fun point => ne_of_gt (metrics.plus_pos point i))

theorem relativeRatioField_pos
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (point : EffectiveQuotient period hPeriod) (i : Fin 4) :
    0 < relativeRatioField period hPeriod metrics point i :=
  div_pos (metrics.minus_pos point i) (metrics.plus_pos point i)

/-- Positive square root of a smooth strictly-positive diagonal spectrum. -/
def positiveSquareRootField
    (field : SmoothQuotientField period hPeriod Coefficients4)
    (hPositive : ∀ point i, 0 < field point i) :
    SmoothQuotientField period hPeriod Coefficients4 where
  toFun := fun point i => Real.sqrt (field point i)
  contMDiff_toFun := by
    rw [contMDiff_pi_space]
    intro i point
    have hCoordinate := (contMDiff_pi_space.mp field.contMDiff_toFun) i
    exact
      (Real.contDiffAt_sqrt (ne_of_gt (hPositive point i))).contMDiffAt.comp
        point hCoordinate.contMDiffAt

/-- Co-diagonal plus scales whose squares recover the plus metric
magnitudes. -/
def plusScaleField
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod) :
    SmoothQuotientField period hPeriod Coefficients4 :=
  positiveSquareRootField period hPeriod metrics.plusMagnitude metrics.plus_pos

/-- Co-diagonal minus scales whose squares recover the minus metric
magnitudes. -/
def minusScaleField
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod) :
    SmoothQuotientField period hPeriod Coefficients4 :=
  positiveSquareRootField period hPeriod metrics.minusMagnitude metrics.minus_pos

theorem plusScaleField_pos
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (point : EffectiveQuotient period hPeriod) (i : Fin 4) :
    0 < plusScaleField period hPeriod metrics point i :=
  Real.sqrt_pos.2 (metrics.plus_pos point i)

theorem minusScaleField_pos
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (point : EffectiveQuotient period hPeriod) (i : Fin 4) :
    0 < minusScaleField period hPeriod metrics point i :=
  Real.sqrt_pos.2 (metrics.minus_pos point i)

/-- The pointwise positive principal-root spectrum is smooth on the complete
positive field domain. -/
def principalRootSpectrumField
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod) :
    SmoothQuotientField period hPeriod Coefficients4 where
  toFun := fun point i =>
    Real.sqrt (relativeRatioField period hPeriod metrics point i)
  contMDiff_toFun := by
    rw [contMDiff_pi_space]
    intro i point
    have hRatio :=
      (contMDiff_pi_space.mp
        (relativeRatioField period hPeriod metrics).contMDiff_toFun) i
    exact
      (Real.contDiffAt_sqrt
        (ne_of_gt (relativeRatioField_pos period hPeriod metrics point i))).contMDiffAt.comp
        point hRatio.contMDiffAt

/-- Smooth principal-root matrix field on the actual quotient. -/
def principalRootField
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod) :
    SmoothQuotientField period hPeriod Matrix4 :=
  diagonalMatrixField period hPeriod
    (principalRootSpectrumField period hPeriod metrics)

@[simp]
theorem principalRootField_apply
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    principalRootField period hPeriod metrics point =
      principalRoot (coefficientPairAt period hPeriod metrics point) :=
  rfl

/-- The smooth root squares pointwise to the relative metric built from the
same two independent smooth Lorentz metric fields. -/
theorem principalRootField_square
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    principalRootField period hPeriod metrics point *
        principalRootField period hPeriod metrics point =
      lorentzMetricInverse (metrics.plusMagnitude point) *
        minusLorentzMetricField period hPeriod metrics point := by
  simpa [coefficientPairAt] using principalRoot_square
    (coefficientPairAt period hPeriod metrics point)
    (coefficientPairAt_mem_domain period hPeriod metrics point)

/-- Pointwise uniqueness holds in the positive diagonal branch at every point
of the same global quotient. -/
theorem principalRootField_exists_unique
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    ∃! root : Matrix4,
      P0EFTJanusCoDiagonalLorentzRootChart.IsPositiveDiagonalRoot root ∧
        root * root =
          lorentzMetricInverse (metrics.plusMagnitude point) *
            minusLorentzMetricField period hPeriod metrics point := by
  simpa [coefficientPairAt] using principalRoot_exists_unique
    (coefficientPairAt period hPeriod metrics point)
    (coefficientPairAt_mem_domain period hPeriod metrics point)

/-- PT pullback followed by sector exchange preserves smoothness and strict
positivity, hence preserves the complete diagonal field domain. -/
def ptExchange
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod) :
    SmoothPositiveDiagonalMetricPair period hPeriod where
  plusMagnitude := ptPullback period hPeriod _ metrics.minusMagnitude
  minusMagnitude := ptPullback period hPeriod _ metrics.plusMagnitude
  plus_pos := fun point i =>
    metrics.minus_pos (reflectedSpherePT period hPeriod point) i
  minus_pos := fun point i =>
    metrics.plus_pos (reflectedSpherePT period hPeriod point) i

@[simp]
theorem ptExchange_involutive
    (metrics : SmoothPositiveDiagonalMetricPair period hPeriod) :
    ptExchange period hPeriod (ptExchange period hPeriod metrics) = metrics := by
  apply SmoothPositiveDiagonalMetricPair.ext
  · exact ptPullback_involutive period hPeriod _ metrics.plusMagnitude
  · exact ptPullback_involutive period hPeriod _ metrics.minusMagnitude

/-- PT/exchange is an exact equivalence of the global smooth diagonal metric
domain. -/
def ptExchangeEquiv :
    SmoothPositiveDiagonalMetricPair period hPeriod ≃
      SmoothPositiveDiagonalMetricPair period hPeriod where
  toFun := ptExchange period hPeriod
  invFun := ptExchange period hPeriod
  left_inv := ptExchange_involutive period hPeriod
  right_inv := ptExchange_involutive period hPeriod

end

end P0EFTJanusMappingTorusSmoothDiagonalLorentzFields4D
end JanusFormal
