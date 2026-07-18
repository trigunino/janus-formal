import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.SpecialFunctions.Sqrt
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCoDiagonalLorentzRootChart
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMetricInverseRelativeRootFrechet

/-!
# Global positive diagonal Lorentz root domain in four dimensions

This file works on the complete fixed-frame domain of diagonal Lorentz metric
pairs

`g_+ = diag(-a_0,a_1,a_2,a_3)`,  `g_- = diag(-b_0,b_1,b_2,b_3)`

with all eight magnitudes strictly positive.  Thus all four eigenvalue ratios
`b_i / a_i` are positive.  The principal diagonal root is defined everywhere
on this (convex, hence connected) domain by `sqrt (b_i / a_i)`.

The construction is global on this entire diagonal domain, not merely near
the Minkowski point.  It deliberately says nothing about noncommuting or
nonsimultaneously-diagonal Lorentz metric pairs.
-/

namespace JanusFormal
namespace P0EFTJanusGlobalDiagonalLorentzRoot4D

set_option autoImplicit false

noncomputable section

open scoped Matrix.Norms.Frobenius RightActions
open P0EFTJanusMatrixSquareRootInteractionDensity
open P0EFTJanusMatrixSquareRootFrechetSylvester
open P0EFTJanusPositiveDiagonalSylvesterInverse
open P0EFTJanusCoDiagonalLorentzRootChart
open P0EFTJanusMetricInverseRelativeRootFrechet

abbrev Matrix4 := P0EFTJanusMatrixSquareRootInteractionDensity.Matrix4
abbrev Coefficients4 := Fin 4 → ℝ
abbrev CoefficientPair := Coefficients4 × Coefficients4

/-- Strictly positive diagonal magnitudes. -/
def positiveMagnitudeDomain : Set Coefficients4 :=
  { coefficients | ∀ i, 0 < coefficients i }

/-- The complete fixed-frame diagonal Lorentz domain. -/
def globalDiagonalLorentzDomain : Set CoefficientPair :=
  positiveMagnitudeDomain ×ˢ positiveMagnitudeDomain

theorem positiveMagnitudeDomain_isOpen : IsOpen positiveMagnitudeDomain := by
  rw [show positiveMagnitudeDomain =
      ⋂ i : Fin 4, { coefficients : Coefficients4 | 0 < coefficients i } by
    ext coefficients
    simp [positiveMagnitudeDomain]]
  apply isOpen_iInter_of_finite
  intro i
  exact isOpen_Ioi.preimage (continuous_apply i)

theorem globalDiagonalLorentzDomain_isOpen :
    IsOpen globalDiagonalLorentzDomain :=
  positiveMagnitudeDomain_isOpen.prod positiveMagnitudeDomain_isOpen

theorem positiveMagnitudeDomain_convex :
    Convex ℝ positiveMagnitudeDomain := by
  intro first hFirst second hSecond u v hu hv huv i
  dsimp [positiveMagnitudeDomain] at hFirst hSecond
  dsimp
  have hFirstScaled : 0 ≤ u * first i :=
    mul_nonneg hu (le_of_lt (hFirst i))
  have hSecondScaled : 0 ≤ v * second i :=
    mul_nonneg hv (le_of_lt (hSecond i))
  by_cases hU : u = 0
  · subst u
    have hV : v = 1 := by linarith
    simpa [hV] using hSecond i
  · have hUPos : 0 < u := lt_of_le_of_ne hu (Ne.symm hU)
    exact add_pos_of_pos_of_nonneg (mul_pos hUPos (hFirst i)) hSecondScaled

theorem globalDiagonalLorentzDomain_convex :
    Convex ℝ globalDiagonalLorentzDomain :=
  positiveMagnitudeDomain_convex.prod positiveMagnitudeDomain_convex

theorem globalDiagonalLorentzDomain_nonempty :
    globalDiagonalLorentzDomain.Nonempty := by
  refine ⟨(fun _ => 1, fun _ => 1), ?_⟩
  constructor <;> intro i <;> norm_num [positiveMagnitudeDomain]

/-- The domain is one connected branch, not a disjoint collection of local
root neighborhoods. -/
theorem globalDiagonalLorentzDomain_isConnected :
    IsConnected globalDiagonalLorentzDomain :=
  globalDiagonalLorentzDomain_convex.isConnected
    globalDiagonalLorentzDomain_nonempty

/-- Fixed Lorentz signature with coordinate zero timelike. -/
def signature (i : Fin 4) : ℝ := if i = 0 then -1 else 1

@[simp]
theorem signature_sq (i : Fin 4) : signature i * signature i = 1 := by
  fin_cases i <;> norm_num [signature]

/-- Diagonal Lorentz metric from its positive magnitudes. -/
def lorentzMetric (coefficients : Coefficients4) : Matrix4 :=
  Matrix.diagonal (fun i => signature i * coefficients i)

/-- Explicit inverse metric on the positive domain. -/
def lorentzMetricInverse (coefficients : Coefficients4) : Matrix4 :=
  Matrix.diagonal (fun i => signature i / coefficients i)

theorem lorentzMetricInverse_mul
    (coefficients : Coefficients4)
    (hCoefficients : coefficients ∈ positiveMagnitudeDomain) :
    lorentzMetricInverse coefficients * lorentzMetric coefficients = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [lorentzMetricInverse, lorentzMetric]
    field_simp [ne_of_gt (hCoefficients i)]
    nlinarith [signature_sq i]
  · simp [lorentzMetricInverse, lorentzMetric, hij]

theorem lorentzMetric_mul_inverse
    (coefficients : Coefficients4)
    (hCoefficients : coefficients ∈ positiveMagnitudeDomain) :
    lorentzMetric coefficients * lorentzMetricInverse coefficients = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [lorentzMetricInverse, lorentzMetric]
    field_simp [ne_of_gt (hCoefficients i)]
    nlinarith [signature_sq i]
  · simp [lorentzMetricInverse, lorentzMetric, hij]

/-- All four positive eigenvalue ratios of `g_+^{-1}g_-`. -/
def relativeRatio (point : CoefficientPair) : Coefficients4 :=
  fun i => point.2 i / point.1 i

/-- Principal positive root eigenvalues. -/
def principalRootSpectrum (point : CoefficientPair) : Coefficients4 :=
  fun i => Real.sqrt (relativeRatio point i)

/-- Principal diagonal square root on the entire global domain. -/
def principalRoot (point : CoefficientPair) : Matrix4 :=
  Matrix.diagonal (principalRootSpectrum point)

theorem relativeRatio_pos
    (point : CoefficientPair) (hPoint : point ∈ globalDiagonalLorentzDomain)
    (i : Fin 4) :
    0 < relativeRatio point i :=
  div_pos (hPoint.2 i) (hPoint.1 i)

theorem principalRootSpectrum_pos
    (point : CoefficientPair) (hPoint : point ∈ globalDiagonalLorentzDomain)
    (i : Fin 4) :
    0 < principalRootSpectrum point i :=
  Real.sqrt_pos.2 (relativeRatio_pos point hPoint i)

/-- The displayed root squares to the actual relative metric. -/
theorem principalRoot_square
    (point : CoefficientPair) (hPoint : point ∈ globalDiagonalLorentzDomain) :
    principalRoot point * principalRoot point =
      lorentzMetricInverse point.1 * lorentzMetric point.2 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [principalRoot, principalRootSpectrum, relativeRatio,
      lorentzMetricInverse, lorentzMetric]
    rw [Real.mul_self_sqrt
      (le_of_lt (div_pos (hPoint.2 i) (hPoint.1 i)))]
    field_simp [ne_of_gt (hPoint.1 i)]
    have hSignature : signature i ^ 2 = 1 := by
      simpa [pow_two] using signature_sq i
    rw [hSignature]
    ring
  · simp [principalRoot, principalRootSpectrum, relativeRatio,
      lorentzMetricInverse, lorentzMetric, hij]

/-- The selected root lies in the strictly positive diagonal branch. -/
theorem principalRoot_isPositiveDiagonal
    (point : CoefficientPair) (hPoint : point ∈ globalDiagonalLorentzDomain) :
    IsPositiveDiagonalRoot (principalRoot point) := by
  exact ⟨⟨principalRootSpectrum point,
    principalRootSpectrum_pos point hPoint⟩, rfl⟩

/-- Existence and uniqueness in the full positive diagonal branch. -/
theorem principalRoot_exists_unique
    (point : CoefficientPair) (hPoint : point ∈ globalDiagonalLorentzDomain) :
    ∃! root : Matrix4,
      IsPositiveDiagonalRoot root ∧
        root * root = lorentzMetricInverse point.1 * lorentzMetric point.2 := by
  refine ⟨principalRoot point,
    ⟨principalRoot_isPositiveDiagonal point hPoint,
      principalRoot_square point hPoint⟩, ?_⟩
  intro other hOther
  exact positiveDiagonalRoot_unique hOther.1
    (principalRoot_isPositiveDiagonal point hPoint)
    hOther.2 (principalRoot_square point hPoint)

/-- Positive spectrum packaged for the existing explicit Sylvester inverse. -/
def typedPrincipalRootSpectrum
    (point : CoefficientPair) (hPoint : point ∈ globalDiagonalLorentzDomain) :
    PositiveDiagonalSpectrum :=
  ⟨principalRootSpectrum point, principalRootSpectrum_pos point hPoint⟩

/-- The Sylvester operator is globally invertible at every root in this
domain, entrywise by division by `sqrt(r_i)+sqrt(r_j)`. -/
def principalRootSylvesterInverseWitness
    (point : CoefficientPair) (hPoint : point ∈ globalDiagonalLorentzDomain) :
    SylvesterInverseWitness (principalRoot point) := by
  simpa [principalRoot, typedPrincipalRootSpectrum] using
    positiveDiagonalSylvesterInverseWitness
      (typedPrincipalRootSpectrum point hPoint)

/-- Continuous diagonal embedding for the Frobenius matrix norm. -/
def diagonalContinuousLinearMap : Coefficients4 →L[ℝ] Matrix4 :=
  LinearMap.toContinuousLinearMap (Matrix.diagonalLinearMap (Fin 4) ℝ ℝ)

/-- Complete coefficient variation of the relative metric, including the
derivative of the inverse plus metric. -/
def relativeRatioVariation
    (point : CoefficientPair) : CoefficientPair →L[ℝ] Coefficients4 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun (variation : CoefficientPair) i =>
        variation.2 i / point.1 i -
          point.2 i * variation.1 i / point.1 i ^ 2
      map_add' := by
        intro first second
        ext i
        simp
        ring
      map_smul' := by
        intro scalar variation
        ext i
        simp
        ring }

/-- Complete first variation of the relative metric as a diagonal matrix. -/
def relativeMetricVariation
    (point : CoefficientPair) : CoefficientPair →L[ℝ] Matrix4 :=
  diagonalContinuousLinearMap.comp (relativeRatioVariation point)

/-- Explicit coefficient variation of all four positive root eigenvalues. -/
def principalRootSpectrumVariation
    (point : CoefficientPair) : CoefficientPair →L[ℝ] Coefficients4 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun (variation : CoefficientPair) i =>
        (variation.2 i / point.1 i -
          point.2 i * variation.1 i / point.1 i ^ 2) /
            (2 * principalRootSpectrum point i)
      map_add' := by
        intro first second
        ext i
        simp
        ring
      map_smul' := by
        intro scalar variation
        ext i
        simp
        ring }

/-- Explicit root variation with respect to both metrics. -/
def principalRootVariation
    (point : CoefficientPair) : CoefficientPair →L[ℝ] Matrix4 :=
  diagonalContinuousLinearMap.comp (principalRootSpectrumVariation point)

/-- The displayed relative-ratio variation is the genuine derivative whenever
the denominator spectrum is positive. -/
theorem relativeRatio_hasFDerivAt_of_first_positive
    (point : CoefficientPair) (hFirstPositive : point.1 ∈ positiveMagnitudeDomain) :
    HasFDerivAt relativeRatio (relativeRatioVariation point) point := by
  letI : Module ℝ ℝ := Semiring.toModule
  rw [hasFDerivAt_pi']
  intro i
  let firstCoordinate : CoefficientPair →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj i : Coefficients4 →L[ℝ] ℝ).comp
      (ContinuousLinearMap.fst ℝ Coefficients4 Coefficients4)
  let secondCoordinate : CoefficientPair →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj i : Coefficients4 →L[ℝ] ℝ).comp
      (ContinuousLinearMap.snd ℝ Coefficients4 Coefficients4)
  have hFirst := firstCoordinate.hasFDerivAt (x := point)
  have hSecond := secondCoordinate.hasFDerivAt (x := point)
  have hInverse := (hasFDerivAt_inv (ne_of_gt (hFirstPositive i))).comp
    point hFirst
  have hProduct := hSecond.mul hInverse
  change HasFDerivAt (fun varied : CoefficientPair =>
      varied.2 i / varied.1 i)
    ((ContinuousLinearMap.proj i : Coefficients4 →L[ℝ] ℝ).comp
      (relativeRatioVariation point)) point
  have hProduct' : HasFDerivAt (fun varied : CoefficientPair =>
      varied.2 i * (varied.1 i)⁻¹) _ point :=
    hProduct.congr_of_eventuallyEq (Filter.Eventually.of_forall fun varied => by
      simp [firstCoordinate, secondCoordinate])
  refine hProduct'.congr_fderiv ?_
  apply ContinuousLinearMap.ext
  intro variation
  simp [firstCoordinate, secondCoordinate, relativeRatioVariation]
  field_simp [ne_of_gt (hFirstPositive i)]
  ring

/-- Domain-specialized form of the relative-ratio derivative. -/
theorem relativeRatio_hasFDerivAt
    (point : CoefficientPair) (hPoint : point ∈ globalDiagonalLorentzDomain) :
    HasFDerivAt relativeRatio (relativeRatioVariation point) point :=
  relativeRatio_hasFDerivAt_of_first_positive point hPoint.1

/-- The fixed Lorentz sign spectrum used as numerator for the inverse metric. -/
def signatureSpectrum : Coefficients4 := fun i => signature i

/-- Affine input whose ratio is the inverse-metric diagonal spectrum. -/
def inverseRatioInput (coefficients : Coefficients4) : CoefficientPair :=
  (coefficients, signatureSpectrum)

/-- Complete derivative of the explicit inverse Lorentz metric. -/
def lorentzMetricInverseVariation
    (coefficients : Coefficients4) : Coefficients4 →L[ℝ] Matrix4 :=
  diagonalContinuousLinearMap.comp
    ((relativeRatioVariation (inverseRatioInput coefficients)).comp
      (ContinuousLinearMap.inl ℝ Coefficients4 Coefficients4))

/-- The explicit inverse formula is genuinely Frechet differentiable on the
whole positive magnitude cone. -/
theorem lorentzMetricInverse_hasFDerivAt
    (coefficients : Coefficients4)
    (hCoefficients : coefficients ∈ positiveMagnitudeDomain) :
    HasFDerivAt lorentzMetricInverse
      (lorentzMetricInverseVariation coefficients) coefficients := by
  have hInput : HasFDerivAt inverseRatioInput
      (ContinuousLinearMap.inl ℝ Coefficients4 Coefficients4)
      coefficients := by
    let inclusion : Coefficients4 →L[ℝ] CoefficientPair :=
      ContinuousLinearMap.inl ℝ Coefficients4 Coefficients4
    have hLinear := inclusion.hasFDerivAt (x := coefficients)
    have hAffine := hLinear.add_const (0, signatureSpectrum)
    exact hAffine.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun varied => by
        simp [inclusion, inverseRatioInput])
  have hRatio : HasFDerivAt (relativeRatio ∘ inverseRatioInput)
      ((relativeRatioVariation (inverseRatioInput coefficients)).comp
        (ContinuousLinearMap.inl ℝ Coefficients4 Coefficients4))
      coefficients :=
    (relativeRatio_hasFDerivAt_of_first_positive
      (inverseRatioInput coefficients) hCoefficients).comp coefficients hInput
  change HasFDerivAt
    (fun varied => diagonalContinuousLinearMap
      (relativeRatio (inverseRatioInput varied)))
    (diagonalContinuousLinearMap.comp
      ((relativeRatioVariation (inverseRatioInput coefficients)).comp
        (ContinuousLinearMap.inl ℝ Coefficients4 Coefficients4)))
    coefficients
  exact diagonalContinuousLinearMap.hasFDerivAt.comp coefficients hRatio

/-- Entrywise inverse-metric variation, including the minus sign from
differentiating inversion. -/
@[simp]
theorem lorentzMetricInverseVariation_apply
    (coefficients variation : Coefficients4) (i : Fin 4) :
    lorentzMetricInverseVariation coefficients variation i i =
      -(signature i * variation i / coefficients i ^ 2) := by
  simp [lorentzMetricInverseVariation, relativeRatioVariation,
    inverseRatioInput, signatureSpectrum, diagonalContinuousLinearMap]

/-- Relative metric written as the diagonal ratio matrix. -/
def diagonalRelativeMetric (point : CoefficientPair) : Matrix4 :=
  diagonalContinuousLinearMap (relativeRatio point)

/-- On the Lorentz domain, the diagonal ratio is exactly
`g_+^{-1} g_-`. -/
theorem diagonalRelativeMetric_eq_metricProduct
    (point : CoefficientPair) (hPoint : point ∈ globalDiagonalLorentzDomain) :
    diagonalRelativeMetric point =
      lorentzMetricInverse point.1 * lorentzMetric point.2 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [diagonalRelativeMetric, diagonalContinuousLinearMap, relativeRatio,
      lorentzMetricInverse, lorentzMetric]
    field_simp [ne_of_gt (hPoint.1 i)]
    have hSignature : signature i ^ 2 = 1 := by
      simpa [pow_two] using signature_sq i
    rw [hSignature]
    ring
  · simp [diagonalRelativeMetric, diagonalContinuousLinearMap, relativeRatio,
      lorentzMetricInverse, lorentzMetric, hij]

/-- The complete ratio formula is the derivative of the diagonal relative
metric. -/
theorem diagonalRelativeMetric_hasFDerivAt
    (point : CoefficientPair) (hPoint : point ∈ globalDiagonalLorentzDomain) :
    HasFDerivAt diagonalRelativeMetric (relativeMetricVariation point) point := by
  change HasFDerivAt
    (fun varied => diagonalContinuousLinearMap (relativeRatio varied))
    (diagonalContinuousLinearMap.comp (relativeRatioVariation point)) point
  exact diagonalContinuousLinearMap.hasFDerivAt.comp point
    (relativeRatio_hasFDerivAt point hPoint)

/-- Hence the actual product `g_+^{-1} g_-` has the full two-metric
variation on the open global domain. -/
theorem metricProduct_hasFDerivAt
    (point : CoefficientPair) (hPoint : point ∈ globalDiagonalLorentzDomain) :
    HasFDerivAt
      (fun varied => lorentzMetricInverse varied.1 * lorentzMetric varied.2)
      (relativeMetricVariation point) point := by
  apply (diagonalRelativeMetric_hasFDerivAt point hPoint).congr_of_eventuallyEq
  filter_upwards [globalDiagonalLorentzDomain_isOpen.mem_nhds hPoint]
    with varied hVar
  exact (diagonalRelativeMetric_eq_metricProduct varied hVar).symm

/-- Expanded complete relative-metric variation. -/
@[simp]
theorem relativeMetricVariation_apply
    (point variation : CoefficientPair) (i : Fin 4) :
    relativeMetricVariation point variation i i =
      variation.2 i / point.1 i -
        point.2 i * variation.1 i / point.1 i ^ 2 := by
  simp [relativeMetricVariation, relativeRatioVariation,
    diagonalContinuousLinearMap]

/-- The root spectrum is smooth to every finite order on the domain. -/
theorem principalRootSpectrum_contDiffOn (n : WithTop ℕ∞) :
    ContDiffOn ℝ n principalRootSpectrum globalDiagonalLorentzDomain := by
  rw [contDiffOn_pi]
  intro i point hPoint
  apply ContDiffAt.contDiffWithinAt
  unfold principalRootSpectrum relativeRatio
  fun_prop (disch :=
    first | exact ne_of_gt (hPoint.1 i)
          | exact ne_of_gt (relativeRatio_pos point hPoint i))

/-- The root map is smooth to every finite order throughout the global
diagonal domain. -/
theorem principalRoot_contDiffOn (n : WithTop ℕ∞) :
    ContDiffOn ℝ n principalRoot globalDiagonalLorentzDomain := by
  have hDiagonal : ContDiff ℝ n diagonalContinuousLinearMap :=
    diagonalContinuousLinearMap.contDiff
  have hCompose := hDiagonal.comp_contDiffOn
    (principalRootSpectrum_contDiffOn n)
  change ContDiffOn ℝ n
    (fun point => diagonalContinuousLinearMap (principalRootSpectrum point))
    globalDiagonalLorentzDomain
  exact hCompose

/-- Genuine Frechet derivative of the four root eigenvalues. -/
theorem principalRootSpectrum_hasFDerivAt
    (point : CoefficientPair) (hPoint : point ∈ globalDiagonalLorentzDomain) :
    HasFDerivAt principalRootSpectrum
      (principalRootSpectrumVariation point) point := by
  letI : Module ℝ ℝ := Semiring.toModule
  rw [hasFDerivAt_pi']
  intro i
  change HasFDerivAt (fun varied => Real.sqrt (relativeRatio varied i))
    ((ContinuousLinearMap.proj i : Coefficients4 →L[ℝ] ℝ).comp
      (principalRootSpectrumVariation point)) point
  have hCoordinate : HasFDerivAt
      (fun varied => relativeRatio varied i)
      ((ContinuousLinearMap.proj i : Coefficients4 →L[ℝ] ℝ).comp
        (relativeRatioVariation point))
      point := by
    let evaluation : Coefficients4 →L[ℝ] ℝ :=
      ContinuousLinearMap.proj i
    have hComp := evaluation.hasFDerivAt (x := relativeRatio point) |>.comp point
      (relativeRatio_hasFDerivAt point hPoint)
    exact hComp.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun varied => by simp [evaluation])
  have hSqrt := hCoordinate.sqrt
    (ne_of_gt (relativeRatio_pos point hPoint i))
  refine hSqrt.congr_fderiv ?_
  apply ContinuousLinearMap.ext
  intro variation
  simp [principalRootSpectrumVariation, relativeRatioVariation,
    principalRootSpectrum]
  ring

/-- Genuine Frechet derivative of the global diagonal principal root. -/
theorem principalRoot_hasFDerivAt
    (point : CoefficientPair) (hPoint : point ∈ globalDiagonalLorentzDomain) :
    HasFDerivAt principalRoot (principalRootVariation point) point := by
  change HasFDerivAt
    (fun varied => diagonalContinuousLinearMap (principalRootSpectrum varied))
    (diagonalContinuousLinearMap.comp
      (principalRootSpectrumVariation point)) point
  exact diagonalContinuousLinearMap.hasFDerivAt.comp point
    (principalRootSpectrum_hasFDerivAt point hPoint)

/-- The full formula is exactly the Sylvester inverse applied to the complete
variation of `g_+^{-1}g_-`. -/
theorem principalRootVariation_eq_sylvester
    (point : CoefficientPair) (hPoint : point ∈ globalDiagonalLorentzDomain) :
    principalRootVariation point =
      (diagonalSylvesterInverse (typedPrincipalRootSpectrum point hPoint)).comp
        (relativeMetricVariation point) := by
  apply ContinuousLinearMap.ext
  intro variation
  ext i j
  by_cases hij : i = j
  · subst j
    simp [principalRootVariation, principalRootSpectrumVariation,
      relativeMetricVariation, relativeRatioVariation,
      diagonalContinuousLinearMap, typedPrincipalRootSpectrum]
    ring
  · simp [principalRootVariation, principalRootSpectrumVariation,
      relativeMetricVariation, relativeRatioVariation,
      diagonalContinuousLinearMap, typedPrincipalRootSpectrum, hij]

/-- Expanded variation formula, displaying both metric contributions. -/
@[simp]
theorem principalRootVariation_apply
    (point variation : CoefficientPair) (i : Fin 4) :
    principalRootVariation point variation i i =
      (variation.2 i / point.1 i -
        point.2 i * variation.1 i / point.1 i ^ 2) /
          (2 * Real.sqrt (point.2 i / point.1 i)) := by
  simp [principalRootVariation, principalRootSpectrumVariation,
    diagonalContinuousLinearMap, principalRootSpectrum, relativeRatio]

end

end P0EFTJanusGlobalDiagonalLorentzRoot4D
end JanusFormal
