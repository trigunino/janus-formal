import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicEinsteinHilbertCurvature4D

/-!
# Local Einstein--Hilbert bulk/Palatini split

This finite-index identity separates the exact density velocity into the
Einstein tensor paired with the inverse-metric velocity and the contraction
of the Ricci (Palatini) velocity.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusLocalEinsteinHilbertPalatiniVariation4D

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open scoped BigOperators

abbrev Index4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Index4
abbrev Matrix4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Matrix4

local instance localRealNormedAddCommGroup : NormedAddCommGroup ℝ :=
  inferInstance

local instance localRealNormedSpace : NormedSpace ℝ ℝ :=
  inferInstance

local instance localRealAddCommGroup : AddCommGroup ℝ :=
  localRealNormedAddCommGroup.toAddCommGroup

local instance (priority := 10000) localRealModule : Module ℝ ℝ :=
  localRealNormedSpace.toModule

def tensorPairing (first second : Matrix4) : ℝ :=
  ∑ μ : Index4, ∑ ν : Index4, first μ ν * second μ ν

def scalarCurvatureAt (inverse ricci : Matrix4) : ℝ :=
  tensorPairing inverse ricci

def einsteinTensorAt
    (metric inverse ricci : Matrix4) (cosmologicalConstant : ℝ) : Matrix4 :=
  fun μ ν =>
    ricci μ ν -
      (1 / 2 : ℝ) * metric μ ν * scalarCurvatureAt inverse ricci +
      cosmologicalConstant * metric μ ν

def palatiniScalarVelocity
    (inverse ricciVelocity : Matrix4) : ℝ :=
  tensorPairing inverse ricciVelocity

def inverseMetricScalarVelocity
    (ricci inverseVelocity : Matrix4) : ℝ :=
  tensorPairing inverseVelocity ricci

/-- The scalar-curvature product rule along actual inverse-metric and Ricci
curves. -/
theorem scalarCurvatureCurve_hasDerivAt
    (inverseCurve ricciCurve : ℝ → Matrix4)
    (inverseVelocity ricciVelocity : Matrix4) (parameter : ℝ)
    (hInverse : ∀ μ ν,
      HasDerivAt (fun varied => inverseCurve varied μ ν)
        (inverseVelocity μ ν) parameter)
    (hRicci : ∀ μ ν,
      HasDerivAt (fun varied => ricciCurve varied μ ν)
        (ricciVelocity μ ν) parameter) :
    HasDerivAt
      (fun varied =>
        scalarCurvatureAt (inverseCurve varied) (ricciCurve varied))
      (inverseMetricScalarVelocity (ricciCurve parameter) inverseVelocity +
        palatiniScalarVelocity (inverseCurve parameter) ricciVelocity)
      parameter := by
  unfold scalarCurvatureAt tensorPairing inverseMetricScalarVelocity
    palatiniScalarVelocity
  have hSum : HasDerivAt
      (fun varied =>
        ∑ μ : Index4, ∑ ν : Index4,
          inverseCurve varied μ ν * ricciCurve varied μ ν)
      (∑ μ : Index4, ∑ ν : Index4,
        (inverseVelocity μ ν * ricciCurve parameter μ ν +
          inverseCurve parameter μ ν * ricciVelocity μ ν))
      parameter := by
    apply HasDerivAt.fun_sum
    intro μ _
    apply HasDerivAt.fun_sum
    intro ν _
    exact (hInverse μ ν).mul (hRicci μ ν)
  convert hSum using 1
  simp_rw [Finset.sum_add_distrib]
  rfl

/-- A Levi-Civita connection and an actual first connection jet. -/
structure ConnectionVariationJet4 where
  connection : Index4 → Index4 → Index4 → ℝ
  variation : Index4 → Index4 → Index4 → ℝ
  partialVariation : Index4 → Index4 → Index4 → Index4 → ℝ
  connection_torsionFree : ∀ upper first second,
    connection upper first second = connection upper second first

/-- Product-rule velocity of the Ricci tensor computed from the coordinate
curvature formula. -/
def ricciVelocityFromConnection
    (jet : ConnectionVariationJet4) (first second : Index4) : ℝ :=
  ∑ contracted : Index4,
    (jet.partialVariation contracted contracted second first -
      jet.partialVariation second contracted contracted first +
      (∑ auxiliary : Index4,
        (jet.variation contracted contracted auxiliary *
            jet.connection auxiliary second first +
          jet.connection contracted contracted auxiliary *
            jet.variation auxiliary second first)) -
      ∑ auxiliary : Index4,
        (jet.variation contracted second auxiliary *
            jet.connection auxiliary contracted first +
          jet.connection contracted second auxiliary *
            jet.variation auxiliary contracted first))

/-- Covariant derivative of a `(1,2)` connection-variation tensor. -/
def covariantConnectionVariationDerivative
    (jet : ConnectionVariationJet4)
    (derivative upper first second : Index4) : ℝ :=
  jet.partialVariation derivative upper first second +
    (∑ auxiliary : Index4,
      jet.connection upper derivative auxiliary *
        jet.variation auxiliary first second) -
    (∑ auxiliary : Index4,
      jet.connection auxiliary derivative first *
        jet.variation upper auxiliary second) -
    ∑ auxiliary : Index4,
      jet.connection auxiliary derivative second *
        jet.variation upper first auxiliary

/-- Palatini form `δR_{μν} = ∇ρ C^ρ_{νμ} - ∇ν C^ρ_{ρμ}`. -/
def palatiniRicciVelocity
    (jet : ConnectionVariationJet4) (first second : Index4) : ℝ :=
  ∑ contracted : Index4,
    (covariantConnectionVariationDerivative jet contracted contracted second
        first -
      covariantConnectionVariationDerivative jet second contracted contracted
        first)

/-- The coordinate product-rule variation of Ricci is exactly the Palatini
covariant derivative; only torsion-freeness of the base connection is used. -/
theorem ricciVelocityFromConnection_eq_palatini
    (jet : ConnectionVariationJet4) (first second : Index4) :
    ricciVelocityFromConnection jet first second =
      palatiniRicciVelocity jet first second := by
  unfold ricciVelocityFromConnection palatiniRicciVelocity
    covariantConnectionVariationDerivative
  apply Finset.sum_congr rfl
  intro contracted _
  have hCancel :
      (∑ auxiliary : Index4,
          jet.connection auxiliary contracted second *
            jet.variation contracted auxiliary first) =
        ∑ auxiliary : Index4,
          jet.connection auxiliary second contracted *
            jet.variation contracted auxiliary first := by
    apply Finset.sum_congr rfl
    intro auxiliary _
    rw [jet.connection_torsionFree auxiliary contracted second]
  have hFirstProduct :
      (∑ auxiliary : Index4,
          jet.variation contracted contracted auxiliary *
            jet.connection auxiliary second first) =
        ∑ auxiliary : Index4,
          jet.connection auxiliary second first *
            jet.variation contracted contracted auxiliary := by
    apply Finset.sum_congr rfl
    intro auxiliary _
    ring
  have hSecondProduct :
      (∑ auxiliary : Index4,
          jet.variation contracted second auxiliary *
            jet.connection auxiliary contracted first) =
        ∑ auxiliary : Index4,
          jet.connection auxiliary contracted first *
            jet.variation contracted second auxiliary := by
    apply Finset.sum_congr rfl
    intro auxiliary _
    ring
  simp_rw [Finset.sum_add_distrib]
  rw [hCancel, hFirstProduct, hSecondProduct]
  ring

/-- Contraction of the genuine Palatini Ricci derivative. -/
def contractedPalatiniDerivative
    (inverse : Matrix4) (jet : ConnectionVariationJet4) : ℝ :=
  ∑ first : Index4, ∑ second : Index4,
    inverse first second * palatiniRicciVelocity jet first second

/-- A connection-variation jet together with the inverse metric and its
coordinate derivative.  The displayed equation is precisely
`∇ g⁻¹ = 0` for the base Levi-Civita connection. -/
structure MetricCompatiblePalatiniJet4 where
  connectionJet : ConnectionVariationJet4
  inverse : Matrix4
  partialInverse : Index4 → Index4 → Index4 → ℝ
  inverse_symmetric : ∀ first second,
    inverse first second = inverse second first
  inverse_metric_compatible : ∀ derivative first second,
    partialInverse derivative first second +
      (∑ auxiliary : Index4,
        connectionJet.connection first derivative auxiliary *
          inverse auxiliary second) +
      ∑ auxiliary : Index4,
        connectionJet.connection second derivative auxiliary *
          inverse first auxiliary = 0

theorem MetricCompatiblePalatiniJet4.partialInverse_eq
    (jet : MetricCompatiblePalatiniJet4)
    (derivative first second : Index4) :
    jet.partialInverse derivative first second =
      -(∑ auxiliary : Index4,
          jet.connectionJet.connection first derivative auxiliary *
            jet.inverse auxiliary second) -
        ∑ auxiliary : Index4,
          jet.connectionJet.connection second derivative auxiliary *
            jet.inverse first auxiliary := by
  linarith [jet.inverse_metric_compatible derivative first second]

/-- The actual Palatini vector
`V^ρ = g^{μν} C^ρ_{νμ} - g^{μρ} C^ν_{νμ}`. -/
def palatiniVector
    (jet : MetricCompatiblePalatiniJet4) (vector : Index4) : ℝ :=
  (∑ first : Index4, ∑ second : Index4,
      jet.inverse first second *
        jet.connectionJet.variation vector second first) -
    ∑ first : Index4, ∑ contracted : Index4,
      jet.inverse first vector *
        jet.connectionJet.variation contracted contracted first

/-- Coordinate product-rule derivative of the Palatini vector. -/
def palatiniVectorPartialDerivative
    (jet : MetricCompatiblePalatiniJet4)
    (derivative vector : Index4) : ℝ :=
  (∑ first : Index4, ∑ second : Index4,
      (jet.partialInverse derivative first second *
          jet.connectionJet.variation vector second first +
        jet.inverse first second *
          jet.connectionJet.partialVariation derivative vector second first)) -
    ∑ first : Index4, ∑ contracted : Index4,
      (jet.partialInverse derivative first vector *
          jet.connectionJet.variation contracted contracted first +
        jet.inverse first vector *
          jet.connectionJet.partialVariation derivative contracted contracted
            first)

/-- Coordinate expression `∂ρ V^ρ + Γ^ρ_{ρλ} V^λ` for the covariant
divergence of the genuine Palatini vector. -/
def palatiniVectorCovariantDivergence
    (jet : MetricCompatiblePalatiniJet4) : ℝ :=
  ∑ derivative : Index4,
    (palatiniVectorPartialDerivative jet derivative derivative +
      ∑ auxiliary : Index4,
        jet.connectionJet.connection derivative derivative auxiliary *
          palatiniVector jet auxiliary)

/-- Metric compatibility turns the contracted Palatini identity into the
covariant divergence of its explicitly constructed vector. -/
theorem contractedPalatiniDerivative_eq_covariantDivergence
    (jet : MetricCompatiblePalatiniJet4) :
    contractedPalatiniDerivative jet.inverse jet.connectionJet =
      palatiniVectorCovariantDivergence jet := by
  unfold contractedPalatiniDerivative palatiniRicciVelocity
    covariantConnectionVariationDerivative
    palatiniVectorCovariantDivergence palatiniVectorPartialDerivative
    palatiniVector
  simp_rw [jet.partialInverse_eq]
  simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [Fin.sum_univ_four]
  ring

/-- The compatible volume-density jet, characterized by
`∂ρ √|g| = √|g| Γ^μ_{μρ}`. -/
structure DensitizedPalatiniJet4 extends MetricCompatiblePalatiniJet4 where
  volume : ℝ
  partialVolume : Index4 → ℝ
  volume_compatible : ∀ derivative,
    partialVolume derivative =
      volume * ∑ contracted : Index4,
        connectionJet.connection contracted contracted derivative

/-- Product-rule coordinate derivative of `√|g| V`. -/
def densitizedPalatiniVectorPartialDerivative
    (jet : DensitizedPalatiniJet4)
    (derivative vector : Index4) : ℝ :=
  jet.partialVolume derivative *
      palatiniVector jet.toMetricCompatiblePalatiniJet4 vector +
    jet.volume *
      palatiniVectorPartialDerivative
        jet.toMetricCompatiblePalatiniJet4 derivative vector

/-- Ordinary coordinate divergence `∂ρ(√|g| V^ρ)`, the density to which
the divergence theorem applies. -/
def densitizedPalatiniCoordinateDivergence
    (jet : DensitizedPalatiniJet4) : ℝ :=
  ∑ derivative : Index4,
    densitizedPalatiniVectorPartialDerivative jet derivative derivative

/-- The local Palatini term is exactly a coordinate divergence density,
with no independently supplied boundary coefficient. -/
theorem volume_mul_contractedPalatiniDerivative_eq_coordinateDivergence
    (jet : DensitizedPalatiniJet4) :
    jet.volume *
        contractedPalatiniDerivative jet.inverse jet.connectionJet =
      densitizedPalatiniCoordinateDivergence jet := by
  rw [contractedPalatiniDerivative_eq_covariantDivergence
    jet.toMetricCompatiblePalatiniJet4]
  unfold densitizedPalatiniCoordinateDivergence
    densitizedPalatiniVectorPartialDerivative
    palatiniVectorCovariantDivergence
  simp_rw [jet.volume_compatible]
  simp only [Fin.sum_univ_four]
  ring

theorem palatiniScalarVelocity_fromConnection
    (inverse : Matrix4) (jet : ConnectionVariationJet4) :
    palatiniScalarVelocity inverse
        (fun first second =>
          ricciVelocityFromConnection jet first second) =
      contractedPalatiniDerivative inverse jet := by
  unfold palatiniScalarVelocity tensorPairing contractedPalatiniDerivative
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  change inverse first second * ricciVelocityFromConnection jet first second =
    inverse first second * palatiniRicciVelocity jet first second
  rw [ricciVelocityFromConnection_eq_palatini]

/-- Exact first velocity of `√|g| (R-2Λ)/(2κ)` written from the product
rule and the scalar-curvature contraction. -/
def einsteinHilbertDensityVelocity
    (gravitationalCoupling cosmologicalConstant volume volumeVelocity : ℝ)
    (inverse ricci inverseVelocity ricciVelocity : Matrix4) : ℝ :=
  (1 / (2 * gravitationalCoupling)) *
    (volumeVelocity *
        (scalarCurvatureAt inverse ricci - 2 * cosmologicalConstant) +
      volume *
        (inverseMetricScalarVelocity ricci inverseVelocity +
          palatiniScalarVelocity inverse ricciVelocity))

private theorem einsteinTensor_pairing_expansion
    (metric inverse ricci inverseVelocity : Matrix4)
    (cosmologicalConstant : ℝ) :
    tensorPairing inverseVelocity
        (einsteinTensorAt metric inverse ricci cosmologicalConstant) =
      inverseMetricScalarVelocity ricci inverseVelocity -
        (1 / 2 : ℝ) * scalarCurvatureAt inverse ricci *
          tensorPairing metric inverseVelocity +
        cosmologicalConstant * tensorPairing metric inverseVelocity := by
  unfold tensorPairing einsteinTensorAt inverseMetricScalarVelocity
  simp_rw [mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  apply congrArg₂ (· + ·)
  · apply congrArg₂ (· - ·)
    · rfl
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro μ _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ν _
      ring
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro μ _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ν _
    ring

/-- Local EH split:

`δL_EH = √|g|/(2κ) (E_{μν} δg^{μν} + g^{μν} δR_{μν})`.
-/
theorem einsteinHilbertDensityVelocity_eq_einstein_add_palatini
    (gravitationalCoupling cosmologicalConstant volume : ℝ)
    (metric inverse ricci inverseVelocity ricciVelocity : Matrix4) :
    einsteinHilbertDensityVelocity gravitationalCoupling
        cosmologicalConstant volume
        (-(volume / 2) * tensorPairing metric inverseVelocity)
        inverse ricci inverseVelocity ricciVelocity =
      (volume / (2 * gravitationalCoupling)) *
        (tensorPairing inverseVelocity
            (einsteinTensorAt metric inverse ricci cosmologicalConstant) +
          palatiniScalarVelocity inverse ricciVelocity) := by
  rw [einsteinHilbertDensityVelocity,
    einsteinTensor_pairing_expansion]
  ring

/-- Actual local EH density derivative in Einstein-plus-Palatini form. -/
theorem einsteinHilbertDensityCurve_hasDerivAt_einstein_add_palatini
    (gravitationalCoupling cosmologicalConstant : ℝ)
    (volumeCurve : ℝ → ℝ) (metric : Matrix4)
    (inverseCurve ricciCurve : ℝ → Matrix4)
    (inverseVelocity ricciVelocity : Matrix4) (parameter : ℝ)
    (hVolume : HasDerivAt volumeCurve
      (-(volumeCurve parameter / 2) *
        tensorPairing metric inverseVelocity) parameter)
    (hInverse : ∀ μ ν,
      HasDerivAt (fun varied => inverseCurve varied μ ν)
        (inverseVelocity μ ν) parameter)
    (hRicci : ∀ μ ν,
      HasDerivAt (fun varied => ricciCurve varied μ ν)
        (ricciVelocity μ ν) parameter) :
    HasDerivAt
      (fun varied =>
        volumeCurve varied *
          ((1 / (2 * gravitationalCoupling)) *
            (scalarCurvatureAt (inverseCurve varied) (ricciCurve varied) -
              2 * cosmologicalConstant)))
      ((volumeCurve parameter / (2 * gravitationalCoupling)) *
        (tensorPairing inverseVelocity
            (einsteinTensorAt metric (inverseCurve parameter)
              (ricciCurve parameter) cosmologicalConstant) +
          palatiniScalarVelocity (inverseCurve parameter) ricciVelocity))
      parameter := by
  have hScalar := scalarCurvatureCurve_hasDerivAt
    inverseCurve ricciCurve inverseVelocity ricciVelocity parameter
    hInverse hRicci
  have hLagrangian :=
    (hScalar.sub_const (2 * cosmologicalConstant)).const_mul
      (1 / (2 * gravitationalCoupling))
  have hProduct := hVolume.mul hLagrangian
  have hCoefficient :
      -(volumeCurve parameter / 2) *
            tensorPairing metric inverseVelocity *
          ((1 / (2 * gravitationalCoupling)) *
            (scalarCurvatureAt (inverseCurve parameter)
                (ricciCurve parameter) -
              2 * cosmologicalConstant)) +
        volumeCurve parameter *
          ((1 / (2 * gravitationalCoupling)) *
            (inverseMetricScalarVelocity (ricciCurve parameter)
                inverseVelocity +
              palatiniScalarVelocity (inverseCurve parameter)
                ricciVelocity)) =
        (volumeCurve parameter / (2 * gravitationalCoupling)) *
          (tensorPairing inverseVelocity
              (einsteinTensorAt metric (inverseCurve parameter)
                (ricciCurve parameter) cosmologicalConstant) +
            palatiniScalarVelocity (inverseCurve parameter)
              ricciVelocity) := by
    rw [← einsteinHilbertDensityVelocity_eq_einstein_add_palatini]
    unfold einsteinHilbertDensityVelocity
    ring
  exact (hProduct.congr_deriv hCoefficient).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)

end

end P0EFTJanusMappingTorusLocalEinsteinHilbertPalatiniVariation4D
end JanusFormal
