import Mathlib
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusRieszShapeOperatorSmoothReducedJetBase

namespace JanusFormal
namespace P0EFTJanusRieszShapeOperatorContinuousStructuredJetReduction

set_option autoImplicit false

noncomputable section

open Module
open scoped ContDiff InnerProductSpace
open P0EFTJanusConcreteSecondJetChainRule
open P0EFTJanusConcreteAbelianConnectionJet
open P0EFTJanusLowOrderStructuredBackground
open P0EFTJanusRieszShapeOperatorSmoothDependence
open P0EFTJanusRieszShapeOperatorPointwiseNormalBasisCover
open P0EFTJanusRieszShapeOperatorSmoothReducedJetBase

universe u v w x y

variable {Tangent : Type u} {Normal : Type v}
variable [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
variable [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
variable [FiniteDimensional ℝ Tangent]
variable [FiniteDimensional ℝ Normal]

/-- Continuous tangent-valued quadratic coefficient of a normalized immersion
second jet. -/
abbrev ContinuousTangentialQuadratic :=
  Tangent →L[ℝ] Tangent →L[ℝ] Tangent

/-- Continuous value of a local abelian connection one-form. -/
abbrev ContinuousConnectionValue := Tangent →L[ℝ] ℝ

/-- Continuous derivative of a local abelian connection one-form. -/
abbrev ContinuousConnectionDerivative :=
  Tangent →L[ℝ] Tangent →L[ℝ] ℝ

/-- Continuous split immersion second jet `(Qᵀ,Qᴺ)`. -/
abbrev SmoothSplitImmersionSecondJet :=
  ContinuousTangentialQuadratic (Tangent := Tangent) ×
    ContinuousSecondFundamentalForm
      (Tangent := Tangent) (Normal := Normal)

/-- Continuous abelian connection one-jet `(A,dA)`. -/
abbrev SmoothConnectionOneJet :=
  ContinuousConnectionValue (Tangent := Tangent) ×
    ContinuousConnectionDerivative (Tangent := Tangent)

/-- Honest normed-vector-space model of an unreduced low-order structured jet. -/
abbrev SmoothLowOrderStructuredJet :=
  SmoothSplitImmersionSecondJet
      (Tangent := Tangent) (Normal := Normal) ×
    SmoothConnectionOneJet (Tangent := Tangent)

/-- Geometric symmetry conditions on the immersion part of a continuous
structured jet. No symmetry is imposed on `dA`; its alternating part is extracted
canonically as curvature. -/
def SmoothLowOrderStructuredJet.IsGeometric
    (jet : SmoothLowOrderStructuredJet
      (Tangent := Tangent) (Normal := Normal)) : Prop :=
  (∀ first second, jet.1.1 first second = jet.1.1 second first) ∧
    (∀ first second, jet.1.2 first second = jet.1.2 second first)

/-- Projection from an unreduced continuous structured jet to its normal
quadratic coefficient. -/
def structuredNormalQuadraticProjection :
    SmoothLowOrderStructuredJet
        (Tangent := Tangent) (Normal := Normal) →L[ℝ]
      ContinuousSecondFundamentalForm
        (Tangent := Tangent) (Normal := Normal) :=
  (ContinuousLinearMap.snd ℝ
      (ContinuousTangentialQuadratic (Tangent := Tangent))
      (ContinuousSecondFundamentalForm
        (Tangent := Tangent) (Normal := Normal))).comp
    (ContinuousLinearMap.fst ℝ
      (SmoothSplitImmersionSecondJet
        (Tangent := Tangent) (Normal := Normal))
      (SmoothConnectionOneJet (Tangent := Tangent)))

/-- Projection from an unreduced continuous structured jet to `dA`. -/
def structuredConnectionDerivativeProjection :
    SmoothLowOrderStructuredJet
        (Tangent := Tangent) (Normal := Normal) →L[ℝ]
      ContinuousConnectionDerivative (Tangent := Tangent) :=
  (ContinuousLinearMap.snd ℝ
      (ContinuousConnectionValue (Tangent := Tangent))
      (ContinuousConnectionDerivative (Tangent := Tangent))).comp
    (ContinuousLinearMap.snd ℝ
      (SmoothSplitImmersionSecondJet
        (Tangent := Tangent) (Normal := Normal))
      (SmoothConnectionOneJet (Tangent := Tangent)))

/-- Continuous-linear flip of the two arguments of a bilinear connection
coefficient. -/
def continuousDerivativeFlip :
    ContinuousConnectionDerivative (Tangent := Tangent) →L[ℝ]
      ContinuousConnectionDerivative (Tangent := Tangent) :=
  (ContinuousLinearMap.flipₗᵢ ℝ Tangent Tangent ℝ :
    ContinuousConnectionDerivative (Tangent := Tangent) →L[ℝ]
      ContinuousConnectionDerivative (Tangent := Tangent))

@[simp]
theorem continuousDerivativeFlip_apply
    (derivative : ContinuousConnectionDerivative (Tangent := Tangent))
    (first second : Tangent) :
    continuousDerivativeFlip
        (Tangent := Tangent) derivative first second =
      derivative second first := by
  simp [continuousDerivativeFlip]

/-- Continuous-linear antisymmetrization `dA ↦ F`, with
`F(x,y)=dA(x,y)-dA(y,x)`. -/
def continuousCurvatureFromDerivative :
    ContinuousConnectionDerivative (Tangent := Tangent) →L[ℝ]
      ContinuousGaugeCurvature (Tangent := Tangent) :=
  (ContinuousLinearMap.id ℝ
      (ContinuousConnectionDerivative (Tangent := Tangent))) -
    continuousDerivativeFlip (Tangent := Tangent)

@[simp]
theorem continuousCurvatureFromDerivative_apply
    (derivative : ContinuousConnectionDerivative (Tangent := Tangent))
    (first second : Tangent) :
    continuousCurvatureFromDerivative
        (Tangent := Tangent) derivative first second =
      derivative first second - derivative second first := by
  simp [continuousCurvatureFromDerivative]

/-- Curvature projection from the full continuous structured jet. -/
def structuredGaugeCurvatureProjection :
    SmoothLowOrderStructuredJet
        (Tangent := Tangent) (Normal := Normal) →L[ℝ]
      ContinuousGaugeCurvature (Tangent := Tangent) :=
  (continuousCurvatureFromDerivative (Tangent := Tangent)).comp
    (structuredConnectionDerivativeProjection
      (Tangent := Tangent) (Normal := Normal))

/-- Continuous-linear quotient map
`(Qᵀ,Qᴺ,A,dA) ↦ (Qᴺ,dA-dAᵀ)`. -/
def smoothLowOrderReduction :
    SmoothLowOrderStructuredJet
        (Tangent := Tangent) (Normal := Normal) →L[ℝ]
      SmoothLowOrderReducedJet
        (Tangent := Tangent) (Normal := Normal) :=
  (structuredNormalQuadraticProjection
    (Tangent := Tangent) (Normal := Normal)).prod
      (structuredGaugeCurvatureProjection
        (Tangent := Tangent) (Normal := Normal))

@[simp]
theorem smoothLowOrderReduction_secondFundamental
    (jet : SmoothLowOrderStructuredJet
      (Tangent := Tangent) (Normal := Normal)) :
    (smoothLowOrderReduction
      (Tangent := Tangent) (Normal := Normal) jet).1 = jet.1.2 := by
  simp [smoothLowOrderReduction, structuredNormalQuadraticProjection]

@[simp]
theorem smoothLowOrderReduction_curvature_apply
    (jet : SmoothLowOrderStructuredJet
      (Tangent := Tangent) (Normal := Normal))
    (first second : Tangent) :
    (smoothLowOrderReduction
      (Tangent := Tangent) (Normal := Normal) jet).2 first second =
      jet.2.2 first second - jet.2.2 second first := by
  simp [smoothLowOrderReduction, structuredGaugeCurvatureProjection,
    structuredConnectionDerivativeProjection]

/-- The continuous reduction map is globally smooth. -/
theorem smoothLowOrderReduction_contDiff :
    ContDiff ℝ ∞
      (smoothLowOrderReduction
        (Tangent := Tangent) (Normal := Normal)) := by
  change ContDiff ℝ ∞
    (fun jet : SmoothLowOrderStructuredJet
        (Tangent := Tangent) (Normal := Normal) =>
      (structuredNormalQuadraticProjection
          (Tangent := Tangent) (Normal := Normal) jet,
        structuredGaugeCurvatureProjection
          (Tangent := Tangent) (Normal := Normal) jet))
  fun_prop

/-- Forget the continuous-linear bundling and recover the earlier algebraic
low-order structured-jet carrier. -/
def forgetContinuousLowOrderStructuredJet
    (jet : SmoothLowOrderStructuredJet
      (Tangent := Tangent) (Normal := Normal)) :
    LowOrderStructuredJet Tangent Normal where
  immersion :=
    { tangentialQuadratic := fun first second => jet.1.1 first second
      normalQuadratic := fun first second => jet.1.2 first second }
  connection :=
    { value := fun tangent => jet.2.1 tangent
      derivative := fun first second => jet.2.2 first second }

/-- The continuous reduction is an exact bundled lift of the earlier algebraic
quotient map. -/
def continuousReductionLiftsAlgebraic
    (jet : SmoothLowOrderStructuredJet
      (Tangent := Tangent) (Normal := Normal)) :
    ContinuousLiftOfLowOrderReducedData
      (reduceLowOrderJet (forgetContinuousLowOrderStructuredJet jet)) where
  smoothJet := smoothLowOrderReduction
    (Tangent := Tangent) (Normal := Normal) jet
  secondFundamental_apply := by
    intro first second
    simp [forgetContinuousLowOrderStructuredJet, reduceLowOrderJet]
  gaugeCurvature_apply := by
    intro first second
    simp [forgetContinuousLowOrderStructuredJet, reduceLowOrderJet, curvature]

/-- A geometric continuous structured jet reduces to a symmetric `II` and an
alternating curvature form. -/
theorem smoothLowOrderReduction_isGeometric
    (jet : SmoothLowOrderStructuredJet
      (Tangent := Tangent) (Normal := Normal))
    (hJet : jet.IsGeometric) :
    (smoothLowOrderReduction
      (Tangent := Tangent) (Normal := Normal) jet).IsGeometric := by
  constructor
  · intro first second
    simpa using hJet.2 first second
  · intro first second
    simp

variable {Base : Type w} {Ambient : Type x}
variable [NormedAddCommGroup Base] [NormedSpace ℝ Base]
variable [NormedAddCommGroup Ambient] [InnerProductSpace ℝ Ambient]
variable [FiniteDimensional ℝ Ambient]
variable {ι κ : Type y}
variable [Fintype ι] [Fintype κ]
variable [LinearOrder κ] [LocallyFiniteOrderBot κ] [WellFoundedLT κ]

/-- Smooth family of unreduced continuous structured jets, together with the
projected-seed geometry used by Riesz descent. -/
structure ContinuousStructuredJetRieszFamilyData where
  basisData : PointwiseNormalBasisData Base Ambient ι κ
  ambientDimension :
    Fintype.card ι + Fintype.card κ = finrank ℝ Ambient
  tangentBasis : Basis ι ℝ Tangent
  tangentBasis_orthonormal : Orthonormal ℝ tangentBasis
  normalBasis : Basis κ ℝ Normal
  normalBasis_orthonormal : Orthonormal ℝ normalBasis
  structuredJet : Base → SmoothLowOrderStructuredJet
    (Tangent := Tangent) (Normal := Normal)
  physicalNormal : Base → Normal
  structuredJet_contDiff : ContDiff ℝ ∞ structuredJet
  physicalNormal_contDiff : ContDiff ℝ ∞ physicalNormal
  structuredJet_geometric : ∀ base, (structuredJet base).IsGeometric

/-- Canonical reduced family obtained from the continuous structured jet. -/
def ContinuousStructuredJetRieszFamilyData.reducedJet
    (data : ContinuousStructuredJetRieszFamilyData
      (Base := Base) (Tangent := Tangent) (Normal := Normal)
      (Ambient := Ambient) (ι := ι) (κ := κ)) :
    Base → SmoothLowOrderReducedJet
      (Tangent := Tangent) (Normal := Normal) :=
  fun base => smoothLowOrderReduction
    (Tangent := Tangent) (Normal := Normal) (data.structuredJet base)

/-- Reduction of a smooth structured-jet family remains smooth. -/
theorem ContinuousStructuredJetRieszFamilyData.reducedJet_contDiff
    (data : ContinuousStructuredJetRieszFamilyData
      (Base := Base) (Tangent := Tangent) (Normal := Normal)
      (Ambient := Ambient) (ι := ι) (κ := κ)) :
    ContDiff ℝ ∞ data.reducedJet := by
  change ContDiff ℝ ∞
    (fun base => smoothLowOrderReduction
      (Tangent := Tangent) (Normal := Normal) (data.structuredJet base))
  exact (smoothLowOrderReduction_contDiff
    (Tangent := Tangent) (Normal := Normal)).fun_comp
      data.structuredJet_contDiff

/-- Pointwise geometricity descends through the continuous quotient map. -/
theorem ContinuousStructuredJetRieszFamilyData.reducedJet_geometric
    (data : ContinuousStructuredJetRieszFamilyData
      (Base := Base) (Tangent := Tangent) (Normal := Normal)
      (Ambient := Ambient) (ι := ι) (κ := κ)) :
    ∀ base, (data.reducedJet base).IsGeometric := by
  intro base
  exact smoothLowOrderReduction_isGeometric
    (data.structuredJet base) (data.structuredJet_geometric base)

/-- The unreduced continuous family automatically instantiates the smooth
reduced-jet Riesz interface. -/
def ContinuousStructuredJetRieszFamilyData.toSmoothReducedJetRieszFamilyData
    (data : ContinuousStructuredJetRieszFamilyData
      (Base := Base) (Tangent := Tangent) (Normal := Normal)
      (Ambient := Ambient) (ι := ι) (κ := κ)) :
    SmoothReducedJetRieszFamilyData
      (Base := Base) (Tangent := Tangent) (Normal := Normal)
      (Ambient := Ambient) (ι := ι) (κ := κ) where
  basisData := data.basisData
  ambientDimension := data.ambientDimension
  tangentBasis := data.tangentBasis
  tangentBasis_orthonormal := data.tangentBasis_orthonormal
  normalBasis := data.normalBasis
  normalBasis_orthonormal := data.normalBasis_orthonormal
  reducedJet := data.reducedJet
  physicalNormal := data.physicalNormal
  reducedJet_contDiff := data.reducedJet_contDiff
  physicalNormal_contDiff := data.physicalNormal_contDiff
  reducedJet_geometric := data.reducedJet_geometric

/-- Global smoothness of the physical Riesz family directly from the unreduced
continuous structured-jet family. -/
theorem ContinuousStructuredJetRieszFamilyData.physicalOperator_contDiff_direct
    (data : ContinuousStructuredJetRieszFamilyData
      (Base := Base) (Tangent := Tangent) (Normal := Normal)
      (Ambient := Ambient) (ι := ι) (κ := κ)) :
    ContDiff ℝ ∞
      ((SmoothReducedJetRieszFamilyData.toGlobalRieszCoefficientData
        data.toSmoothReducedJetRieszFamilyData).physicalOperator) := by
  exact SmoothReducedJetRieszFamilyData.physicalOperator_contDiff_direct
    data.toSmoothReducedJetRieszFamilyData

/-- The same smoothness conclusion through projected-seed atlas descent. -/
theorem ContinuousStructuredJetRieszFamilyData.physicalOperator_contDiff_via_atlas
    {AtlasTangent AtlasNormal : Type y}
    (data : ContinuousStructuredJetRieszFamilyData
      (Base := Base) (Tangent := Tangent) (Normal := Normal)
      (Ambient := Ambient) (ι := ι) (κ := κ)) :
    ContDiff ℝ ∞
      ((SmoothReducedJetRieszFamilyData.toGlobalRieszCoefficientData
        data.toSmoothReducedJetRieszFamilyData).physicalOperator) := by
  exact SmoothReducedJetRieszFamilyData.physicalOperator_contDiff_via_atlas
    (AtlasTangent := AtlasTangent) (AtlasNormal := AtlasNormal)
    data.toSmoothReducedJetRieszFamilyData

/-- Audit boundary after connecting continuous unreduced structured jets to the
smooth reduced Riesz base. -/
structure ContinuousStructuredJetReductionStatus where
  continuousImmersionJetConstructed : Prop
  continuousConnectionJetConstructed : Prop
  continuousCurvatureProjectionConstructed : Prop
  continuousReductionMapConstructed : Prop
  reductionMapSmooth : Prop
  algebraicReductionCompatibilityProved : Prop
  geometricityPreserved : Prop
  smoothFamilyReductionProved : Prop
  globalRieszSmoothnessDerived : Prop
  genuineJanusJetFamilyConstructed : Prop

/-- Closure of the continuous structured-jet reduction stage. -/
def continuousStructuredJetReductionClosed
    (s : ContinuousStructuredJetReductionStatus) : Prop :=
  s.continuousImmersionJetConstructed ∧
  s.continuousConnectionJetConstructed ∧
  s.continuousCurvatureProjectionConstructed ∧
  s.continuousReductionMapConstructed ∧
  s.reductionMapSmooth ∧
  s.algebraicReductionCompatibilityProved ∧
  s.geometricityPreserved ∧
  s.smoothFamilyReductionProved ∧
  s.globalRieszSmoothnessDerived ∧
  s.genuineJanusJetFamilyConstructed

/-- The remaining boundary is construction of the continuous structured-jet
family from genuine Janus immersion and connection jets. -/
theorem missing_genuine_janus_jet_family_blocks_closure
    (s : ContinuousStructuredJetReductionStatus)
    (hMissing : Not s.genuineJanusJetFamilyConstructed) :
    Not (continuousStructuredJetReductionClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.2.2.2

end

end P0EFTJanusRieszShapeOperatorContinuousStructuredJetReduction
end JanusFormal
