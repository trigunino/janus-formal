import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2SmoothPalatiniCurrent4D

/-! # Concrete smooth first-jet coefficients of the Palatini current

The exact inverse-metric, Koszul and Christoffel variation formulas define
a linear map on 16 values and 64 first derivatives. Its values on the
coordinate units are smooth coefficient fields. Applying the actual metric
first jet recovers the existing Palatini current, without a representation
hypothesis or a volume-gauge assumption.
-/

namespace JanusFormal
namespace P0EFTJanusSmoothPalatiniCurrentLinearCoefficients4D

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 600000
noncomputable section
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalTotalHolonomicAtlasScalarStressClosure4D
open P0EFTJanusProgramPRegularFrameMetricInverse4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvatureBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothMetricParameterJet4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothInverseVelocity4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothKoszulVelocity4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothChristoffelVelocity4D
open P0EFTJanusProgramPRegularGeneralMetricC2SmoothPalatiniCurrent4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Separate labels for the values `hᵢⱼ` and derivatives `Eₖ(hᵢⱼ)`. -/
abbrev SmoothPalatiniJetIndex := (Fin 4 × Fin 4) ⊕ (Fin 4 × Fin 4 × Fin 4)
abbrev SmoothPalatiniFirstJet := SmoothPalatiniJetIndex → Real

private def jetEntry (index : SmoothPalatiniJetIndex) :
    SmoothPalatiniFirstJet →ₗ[Real] SmoothScalarField period hPeriod where
  toFun input := ⟨fun _ => input index, contMDiff_const⟩
  map_add' := by
    intro first second
    apply SmoothQuotientField.ext period hPeriod Real
    intro point
    rfl
  map_smul' := by
    intro scalar input
    apply SmoothQuotientField.ext period hPeriod Real
    intro point
    rfl

private theorem jetEntry_apply (index : SmoothPalatiniJetIndex)
    (input : SmoothPalatiniFirstJet) (point : EffectiveQuotient period hPeriod) :
    jetEntry period hPeriod index input point = input index := rfl

private def multiplyLeft (coefficient : SmoothScalarField period hPeriod) :
    SmoothScalarField period hPeriod →ₗ[Real] SmoothScalarField period hPeriod where
  toFun field := smoothScalarFieldMul period hPeriod coefficient field
  map_add' := by
    intro first second
    apply SmoothQuotientField.ext period hPeriod Real
    intro point
    exact mul_add _ _ _
  map_smul' := by
    intro scalar field
    apply SmoothQuotientField.ext period hPeriod Real
    intro point
    change coefficient point * (scalar * field point) = scalar * (coefficient point * field point)
    ring

private def multiplyRight (coefficient : SmoothScalarField period hPeriod) :
    SmoothScalarField period hPeriod →ₗ[Real] SmoothScalarField period hPeriod where
  toFun field := smoothScalarFieldMul period hPeriod field coefficient
  map_add' := by
    intro first second
    apply SmoothQuotientField.ext period hPeriod Real
    intro point
    exact add_mul _ _ _
  map_smul' := by
    intro scalar field
    apply SmoothQuotientField.ext period hPeriod Real
    intro point
    change (scalar * field point) * coefficient point = scalar * (field point * coefficient point)
    ring

private theorem multiplyLeft_apply (coefficient field : SmoothScalarField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    multiplyLeft period hPeriod coefficient field point = coefficient point * field point := rfl
private theorem multiplyRight_apply (coefficient field : SmoothScalarField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    multiplyRight period hPeriod coefficient field point = field point * coefficient point := rfl

/-- The exact inverse variation `-g⁻¹ h g⁻¹`, linear in the value slots. -/
def smoothPalatiniInverseJetMap (metric : RegularGeneralLorentzMetric period hPeriod)
    (row column : Fin 4) : SmoothPalatiniFirstJet →ₗ[Real] SmoothScalarField period hPeriod :=
  (-1 : Real) • ∑ second : Fin 4,
    (multiplyRight period hPeriod (regularFrameMetricInverseMatrix period hPeriod metric second column)).comp
      (∑ first : Fin 4,
        (multiplyLeft period hPeriod (regularFrameMetricInverseMatrix period hPeriod metric row first)).comp
          (jetEntry period hPeriod (.inl (first, second))))

/-- The lowered Koszul variation, including all three anholonomy terms. -/
def smoothPalatiniKoszulJetMap (metric : RegularGeneralLorentzMetric period hPeriod)
    (first second lower : Fin 4) : SmoothPalatiniFirstJet →ₗ[Real] SmoothScalarField period hPeriod :=
  (1 / 2 : Real) •
    (jetEntry period hPeriod (.inr (first, second, lower)) +
      jetEntry period hPeriod (.inr (second, lower, first)) -
      jetEntry period hPeriod (.inr (lower, first, second)) -
      ∑ contracted : Fin 4,
        (multiplyLeft period hPeriod
          (regularFrameStructureCoefficient period hPeriod metric second lower contracted)).comp
          (jetEntry period hPeriod (.inl (first, contracted))) +
      ∑ contracted : Fin 4,
        (multiplyLeft period hPeriod
          (regularFrameStructureCoefficient period hPeriod metric lower first contracted)).comp
          (jetEntry period hPeriod (.inl (second, contracted))) +
      ∑ contracted : Fin 4,
        (multiplyLeft period hPeriod
          (regularFrameStructureCoefficient period hPeriod metric first second contracted)).comp
          (jetEntry period hPeriod (.inl (lower, contracted))))

/-- The actual product-rule Christoffel variation. -/
def smoothPalatiniChristoffelJetMap (metric : RegularGeneralLorentzMetric period hPeriod)
    (upper first second : Fin 4) : SmoothPalatiniFirstJet →ₗ[Real] SmoothScalarField period hPeriod :=
  ∑ lower : Fin 4,
    ((multiplyRight period hPeriod
        (regularFrameSmoothKoszulLowerCoefficient period hPeriod metric first second lower)).comp
        (smoothPalatiniInverseJetMap period hPeriod metric upper lower) +
      (multiplyLeft period hPeriod
        (regularFrameMetricInverseMatrix period hPeriod metric upper lower)).comp
        (smoothPalatiniKoszulJetMap period hPeriod metric first second lower))

/-- The precise Palatini contraction, with the input jet kept independent. -/
def smoothPalatiniFirstJetMap (metric : RegularGeneralLorentzMetric period hPeriod)
    (vector : Fin 4) : SmoothPalatiniFirstJet →ₗ[Real] SmoothScalarField period hPeriod :=
  (∑ first : Fin 4, ∑ second : Fin 4,
      (multiplyLeft period hPeriod
        (regularFrameMetricInverseMatrix period hPeriod metric first second)).comp
        (smoothPalatiniChristoffelJetMap period hPeriod metric vector second first)) -
    ∑ first : Fin 4, ∑ contracted : Fin 4,
      (multiplyLeft period hPeriod
        (regularFrameMetricInverseMatrix period hPeriod metric first vector)).comp
        (smoothPalatiniChristoffelJetMap period hPeriod metric contracted contracted first)

/-- Explicit smooth zeroth-order coefficients, obtained from the value units. -/
def smoothPalatiniValueCoefficient (metric : RegularGeneralLorentzMetric period hPeriod)
    (vector first second : Fin 4) : SmoothScalarField period hPeriod :=
  smoothPalatiniFirstJetMap period hPeriod metric vector (Pi.single (.inl (first, second)) 1)

/-- Explicit smooth first-order coefficients, obtained from the derivative units. -/
def smoothPalatiniDerivativeCoefficient (metric : RegularGeneralLorentzMetric period hPeriod)
    (vector derivative first second : Fin 4) : SmoothScalarField period hPeriod :=
  smoothPalatiniFirstJetMap period hPeriod metric vector (Pi.single (.inr (derivative, first, second)) 1)

/-- The true first jet of the covariant test components, with no independent data. -/
def smoothPalatiniActualFirstJetAt (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) : SmoothPalatiniFirstJet :=
  Sum.elim
    (fun index => regularFrameSmoothCovariantVariationCoefficient period hPeriod metric tensor
      index.1 index.2 point)
    (fun index => regularFrameSmoothCovariantVariationFirstDerivative period hPeriod metric tensor
      index.1 index.2.1 index.2.2 point)

/-- Substituting the genuine first jet gives the already established current. -/
theorem smoothPalatiniFirstJetMap_actual (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) (vector : Fin 4) :
    smoothPalatiniFirstJetMap period hPeriod metric vector
        (smoothPalatiniActualFirstJetAt period hPeriod metric tensor point) point =
      regularFrameSmoothPalatiniCoefficient period hPeriod metric tensor vector point := by
  simp only [smoothPalatiniFirstJetMap, smoothPalatiniChristoffelJetMap,
    smoothPalatiniInverseJetMap, smoothPalatiniKoszulJetMap,
    regularFrameSmoothPalatiniCoefficient, regularFrameSmoothChristoffelVariationCoefficient,
    regularFrameSmoothInverseVariationCoefficient, regularFrameSmoothKoszulLowerVariationCoefficient,
    LinearMap.sum_apply, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.smul_apply, smoothQuotientField_smul_apply, smul_eq_mul,
    smoothScalarFieldFinsetSum_apply, smoothScalarFieldSub_apply, smoothScalarFieldAdd_apply,
    smoothScalarFieldMul_apply, multiplyLeft_apply, multiplyRight_apply, jetEntry_apply,
    smoothPalatiniActualFirstJetAt, Sum.elim_inl, Sum.elim_inr]

/-- Finite-dimensional linearity produces the coefficients without assuming a representation. -/
theorem smoothPalatiniFirstJetMap_expansion (metric : RegularGeneralLorentzMetric period hPeriod)
    (vector : Fin 4) (input : SmoothPalatiniFirstJet)
    (point : EffectiveQuotient period hPeriod) :
    smoothPalatiniFirstJetMap period hPeriod metric vector input point =
      (∑ first : Fin 4, ∑ second : Fin 4,
        smoothPalatiniValueCoefficient period hPeriod metric vector first second point *
          input (.inl (first, second))) +
      ∑ derivative : Fin 4, ∑ first : Fin 4, ∑ second : Fin 4,
        smoothPalatiniDerivativeCoefficient period hPeriod metric vector derivative first second point *
          input (.inr (derivative, first, second)) := by
  have hInput : input = ∑ index : SmoothPalatiniJetIndex, input index • Pi.single index (1 : Real) := by
    funext index
    simp [Pi.single_apply]
  have hLinear := congrArg (smoothPalatiniFirstJetMap period hPeriod metric vector) hInput
  simp only [map_sum, map_smul] at hLinear
  have hPoint := congrArg (fun field : SmoothScalarField period hPeriod => field point) hLinear
  simp only [smoothScalarFieldFinsetSum_apply, smoothQuotientField_smul_apply, smul_eq_mul] at hPoint
  calc
    _ = _ := hPoint
    _ = _ := by
      simp only [Fintype.sum_sum_type, Fintype.sum_prod_type,
        smoothPalatiniValueCoefficient, smoothPalatiniDerivativeCoefficient, mul_comm]

/-- The actual Palatini coefficient is linear in `hᵢⱼ` and its frame derivatives. -/
theorem regularFrameSmoothPalatiniCoefficient_eq_firstJet
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) (vector : Fin 4) :
    regularFrameSmoothPalatiniCoefficient period hPeriod metric tensor vector point =
      (∑ first : Fin 4, ∑ second : Fin 4,
        smoothPalatiniValueCoefficient period hPeriod metric vector first second point *
          tensor.tensor point (metric.frame first point) (metric.frame second point)) +
      ∑ derivative : Fin 4, ∑ first : Fin 4, ∑ second : Fin 4,
        smoothPalatiniDerivativeCoefficient period hPeriod metric vector derivative first second point *
          regularFrameSmoothCovariantVariationFirstDerivative period hPeriod metric tensor
            derivative first second point := by
  rw [← smoothPalatiniFirstJetMap_actual period hPeriod metric tensor point vector]
  simpa only [smoothPalatiniActualFirstJetAt, Sum.elim_inl, Sum.elim_inr,
    regularFrameSmoothCovariantVariationCoefficient_apply] using
    smoothPalatiniFirstJetMap_expansion period hPeriod metric vector
      (smoothPalatiniActualFirstJetAt period hPeriod metric tensor point) point

/-- Bundled smooth-field identity, ready for canonical integration by parts. -/
theorem regularFrameSmoothPalatiniCoefficient_eq_firstJet_fields
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) (vector : Fin 4) :
    regularFrameSmoothPalatiniCoefficient period hPeriod metric tensor vector =
      (∑ first : Fin 4, ∑ second : Fin 4,
        smoothScalarFieldMul period hPeriod
          (smoothPalatiniValueCoefficient period hPeriod metric vector first second)
          (regularFrameSmoothCovariantVariationCoefficient period hPeriod metric tensor first second)) +
      ∑ derivative : Fin 4, ∑ first : Fin 4, ∑ second : Fin 4,
        smoothScalarFieldMul period hPeriod
          (smoothPalatiniDerivativeCoefficient period hPeriod metric vector derivative first second)
          (frameDerivativeComponentField period hPeriod
            (regularGeneralLorentzMetricSmoothD8Frame period hPeriod metric)
            (regularFrameSmoothCovariantVariationCoefficient period hPeriod metric tensor first second)
            derivative) := by
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  simpa only [smoothScalarFieldAdd_apply, smoothScalarFieldFinsetSum_apply,
    smoothScalarFieldMul_apply, regularFrameSmoothCovariantVariationCoefficient_apply,
    regularFrameSmoothCovariantVariationFirstDerivative] using
    regularFrameSmoothPalatiniCoefficient_eq_firstJet period hPeriod metric tensor point vector

end
end P0EFTJanusSmoothPalatiniCurrentLinearCoefficients4D
end JanusFormal
