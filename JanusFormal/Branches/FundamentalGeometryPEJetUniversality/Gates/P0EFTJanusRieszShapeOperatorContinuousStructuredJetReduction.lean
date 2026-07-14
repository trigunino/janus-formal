import Mathlib
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusSecondFundamentalFormJet
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusRieszShapeOperatorSmoothReducedJetBase

namespace JanusFormal
namespace P0EFTJanusRieszShapeOperatorContinuousStructuredJetReduction

set_option autoImplicit false

noncomputable section

open Module
open scoped ContDiff InnerProductSpace
open P0EFTJanusConcreteSecondJetChainRule
open P0EFTJanusConcreteAbelianConnectionJet
open P0EFTJanusAdaptedOrthogonalSplitting
open P0EFTJanusSecondFundamentalFormJet
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

abbrev ContinuousTangentialQuadratic :=
  Tangent →L[ℝ] Tangent →L[ℝ] Tangent

abbrev ContinuousConnectionValue := Tangent →L[ℝ] ℝ

abbrev ContinuousConnectionDerivative :=
  Tangent →L[ℝ] Tangent →L[ℝ] ℝ

abbrev SmoothSplitImmersionSecondJet :=
  ContinuousTangentialQuadratic (Tangent := Tangent) ×
    ContinuousSecondFundamentalForm
      (Tangent := Tangent) (Normal := Normal)

abbrev SmoothConnectionOneJet :=
  ContinuousConnectionValue (Tangent := Tangent) ×
    ContinuousConnectionDerivative (Tangent := Tangent)

abbrev SmoothLowOrderStructuredJet :=
  SmoothSplitImmersionSecondJet
      (Tangent := Tangent) (Normal := Normal) ×
    SmoothConnectionOneJet (Tangent := Tangent)

def SmoothLowOrderStructuredJet.IsGeometric
    (jet : SmoothLowOrderStructuredJet
      (Tangent := Tangent) (Normal := Normal)) : Prop :=
  (∀ first second, jet.1.1 first second = jet.1.1 second first) ∧
    (∀ first second, jet.1.2 first second = jet.1.2 second first)

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

/-- Continuous-linear antisymmetrization `dA ↦ dA-dAᵀ`. -/
def continuousCurvatureFromDerivative :
    ContinuousConnectionDerivative (Tangent := Tangent) →L[ℝ]
      ContinuousConnectionDerivative (Tangent := Tangent) :=
  ContinuousLinearMap.id ℝ _ -
    continuousDerivativeFlip (Tangent := Tangent)

@[simp]
theorem continuousCurvatureFromDerivative_apply
    (derivative : ContinuousConnectionDerivative (Tangent := Tangent))
    (first second : Tangent) :
    continuousCurvatureFromDerivative
        (Tangent := Tangent) derivative first second =
      derivative first second - derivative second first := by
  simp [continuousCurvatureFromDerivative]

def structuredGaugeCurvatureProjection :
    SmoothLowOrderStructuredJet
        (Tangent := Tangent) (Normal := Normal) →L[ℝ]
      ContinuousGaugeCurvature (Tangent := Tangent) :=
  (continuousCurvatureFromDerivative (Tangent := Tangent)).comp
    (structuredConnectionDerivativeProjection
      (Tangent := Tangent) (Normal := Normal))

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

theorem smoothLowOrderReduction_contDiff :
    ContDiff ℝ ∞
      (smoothLowOrderReduction
        (Tangent := Tangent) (Normal := Normal)) := by
  exact (smoothLowOrderReduction
    (Tangent := Tangent) (Normal := Normal)).contDiff

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

section ConnectionCorrectedBridge

variable {Ambient : Type x}
variable [NormedAddCommGroup Ambient] [InnerProductSpace ℝ Ambient]
variable [FiniteDimensional ℝ Ambient]

abbrev ContinuousAmbientQuadratic :=
  Tangent →L[ℝ] Tangent →L[ℝ] Ambient

abbrev SmoothConnectionCorrectedSecondJet :=
  (ContinuousAmbientQuadratic
      (Tangent := Tangent) (Ambient := Ambient) ×
    ContinuousAmbientQuadratic
      (Tangent := Tangent) (Ambient := Ambient)) ×
    ContinuousTangentialQuadratic (Tangent := Tangent)

def forgetContinuousConnectionCorrectedSecondJet
    (jet : SmoothConnectionCorrectedSecondJet
      (Tangent := Tangent) (Ambient := Ambient)) :
    ConnectionCorrectedSecondJet Tangent Ambient where
  rawSecond first second := jet.1.1 first second
  ambientConnection first second := jet.1.2 first second
  sourceConnection first second := jet.2 first second

def continuousCovariantSecondDerivative
    (derivative : Tangent →ₗᵢ[ℝ] Ambient)
    (jet : SmoothConnectionCorrectedSecondJet
      (Tangent := Tangent) (Ambient := Ambient)) :
    Tangent → Tangent → Ambient :=
  fun first second =>
    jet.1.1 first second + jet.1.2 first second -
      derivative (jet.2 first second)

theorem continuousCovariantSecondDerivative_eq_pointwise
    (derivative : Tangent →ₗᵢ[ℝ] Ambient)
    (jet : SmoothConnectionCorrectedSecondJet
      (Tangent := Tangent) (Ambient := Ambient)) :
    continuousCovariantSecondDerivative derivative jet =
      covariantSecondDerivative derivative
        (forgetContinuousConnectionCorrectedSecondJet jet) := by
  rfl

structure ContinuousConnectionCorrectedSecondJetLift
    (derivative : Tangent →ₗᵢ[ℝ] Ambient) where
  jet : SmoothConnectionCorrectedSecondJet
    (Tangent := Tangent) (Ambient := Ambient)
  secondFundamental : ContinuousSecondFundamentalForm
    (Tangent := Tangent)
    (Normal := P0EFTJanusAdaptedOrthogonalSplitting.NormalSpace derivative)
  secondFundamental_apply :
    ∀ first second,
      secondFundamental first second =
        normalProjection derivative
          (continuousCovariantSecondDerivative derivative jet first second)
  rawSecond_symmetric :
    ∀ first second, jet.1.1 first second = jet.1.1 second first
  ambientConnection_symmetric :
    ∀ first second, jet.1.2 first second = jet.1.2 second first
  sourceConnection_symmetric :
    ∀ first second, jet.2 first second = jet.2 second first

theorem ContinuousConnectionCorrectedSecondJetLift.secondFundamental_eq_pointwise
    (derivative : Tangent →ₗᵢ[ℝ] Ambient)
    (data : ContinuousConnectionCorrectedSecondJetLift derivative)
    (first second : Tangent) :
    data.secondFundamental first second =
      secondFundamentalForm derivative
        (forgetContinuousConnectionCorrectedSecondJet data.jet)
        first second := by
  rw [data.secondFundamental_apply first second]
  rfl

theorem ContinuousConnectionCorrectedSecondJetLift.secondFundamental_symmetric
    (derivative : Tangent →ₗᵢ[ℝ] Ambient)
    (data : ContinuousConnectionCorrectedSecondJetLift derivative) :
    ∀ first second,
      data.secondFundamental first second =
        data.secondFundamental second first := by
  intro first second
  rw [data.secondFundamental_apply first second,
    data.secondFundamental_apply second first]
  apply congrArg (normalProjection derivative)
  simp only [continuousCovariantSecondDerivative]
  rw [data.rawSecond_symmetric first second,
    data.ambientConnection_symmetric first second,
    data.sourceConnection_symmetric first second]

end ConnectionCorrectedBridge

variable {Base : Type w} {Ambient : Type x}
variable [NormedAddCommGroup Base] [NormedSpace ℝ Base]
variable [NormedAddCommGroup Ambient] [InnerProductSpace ℝ Ambient]
variable [FiniteDimensional ℝ Ambient]
variable {ι κ : Type y}
variable [Fintype ι] [Fintype κ]
variable [LinearOrder κ] [LocallyFiniteOrderBot κ] [WellFoundedLT κ]

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

def ContinuousStructuredJetRieszFamilyData.reducedJet
    (data : ContinuousStructuredJetRieszFamilyData
      (Base := Base) (Tangent := Tangent) (Normal := Normal)
      (Ambient := Ambient) (ι := ι) (κ := κ)) :
    Base → SmoothLowOrderReducedJet
      (Tangent := Tangent) (Normal := Normal) :=
  fun base => smoothLowOrderReduction
    (Tangent := Tangent) (Normal := Normal) (data.structuredJet base)

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

theorem ContinuousStructuredJetRieszFamilyData.reducedJet_geometric
    (data : ContinuousStructuredJetRieszFamilyData
      (Base := Base) (Tangent := Tangent) (Normal := Normal)
      (Ambient := Ambient) (ι := ι) (κ := κ)) :
    ∀ base, (data.reducedJet base).IsGeometric := by
  intro base
  exact smoothLowOrderReduction_isGeometric
    (data.structuredJet base) (data.structuredJet_geometric base)

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

theorem ContinuousStructuredJetRieszFamilyData.physicalOperator_contDiff_direct
    (data : ContinuousStructuredJetRieszFamilyData
      (Base := Base) (Tangent := Tangent) (Normal := Normal)
      (Ambient := Ambient) (ι := ι) (κ := κ)) :
    ContDiff ℝ ∞
      ((SmoothReducedJetRieszFamilyData.toGlobalRieszCoefficientData
        data.toSmoothReducedJetRieszFamilyData).physicalOperator) := by
  exact SmoothReducedJetRieszFamilyData.physicalOperator_contDiff_direct
    data.toSmoothReducedJetRieszFamilyData

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

structure ContinuousStructuredJetComponentFamilyData where
  basisData : PointwiseNormalBasisData Base Ambient ι κ
  ambientDimension :
    Fintype.card ι + Fintype.card κ = finrank ℝ Ambient
  tangentBasis : Basis ι ℝ Tangent
  tangentBasis_orthonormal : Orthonormal ℝ tangentBasis
  normalBasis : Basis κ ℝ Normal
  normalBasis_orthonormal : Orthonormal ℝ normalBasis
  tangentialQuadratic : Base → ContinuousTangentialQuadratic
    (Tangent := Tangent)
  normalQuadratic : Base → ContinuousSecondFundamentalForm
    (Tangent := Tangent) (Normal := Normal)
  connectionValue : Base → ContinuousConnectionValue
    (Tangent := Tangent)
  connectionDerivative : Base → ContinuousConnectionDerivative
    (Tangent := Tangent)
  physicalNormal : Base → Normal
  tangentialQuadratic_contDiff : ContDiff ℝ ∞ tangentialQuadratic
  normalQuadratic_contDiff : ContDiff ℝ ∞ normalQuadratic
  connectionValue_contDiff : ContDiff ℝ ∞ connectionValue
  connectionDerivative_contDiff : ContDiff ℝ ∞ connectionDerivative
  physicalNormal_contDiff : ContDiff ℝ ∞ physicalNormal
  tangentialQuadratic_symmetric :
    ∀ base first second,
      tangentialQuadratic base first second =
        tangentialQuadratic base second first
  normalQuadratic_symmetric :
    ∀ base first second,
      normalQuadratic base first second =
        normalQuadratic base second first

def ContinuousStructuredJetComponentFamilyData.structuredJet
    (data : ContinuousStructuredJetComponentFamilyData
      (Base := Base) (Tangent := Tangent) (Normal := Normal)
      (Ambient := Ambient) (ι := ι) (κ := κ)) :
    Base → SmoothLowOrderStructuredJet
      (Tangent := Tangent) (Normal := Normal) :=
  fun base =>
    ((data.tangentialQuadratic base, data.normalQuadratic base),
      (data.connectionValue base, data.connectionDerivative base))

theorem ContinuousStructuredJetComponentFamilyData.structuredJet_contDiff
    (data : ContinuousStructuredJetComponentFamilyData
      (Base := Base) (Tangent := Tangent) (Normal := Normal)
      (Ambient := Ambient) (ι := ι) (κ := κ)) :
    ContDiff ℝ ∞ data.structuredJet := by
  exact
    (data.tangentialQuadratic_contDiff.prodMk
      data.normalQuadratic_contDiff).prodMk
        (data.connectionValue_contDiff.prodMk
          data.connectionDerivative_contDiff)

theorem ContinuousStructuredJetComponentFamilyData.structuredJet_geometric
    (data : ContinuousStructuredJetComponentFamilyData
      (Base := Base) (Tangent := Tangent) (Normal := Normal)
      (Ambient := Ambient) (ι := ι) (κ := κ)) :
    ∀ base, (data.structuredJet base).IsGeometric := by
  intro base
  exact ⟨data.tangentialQuadratic_symmetric base,
    data.normalQuadratic_symmetric base⟩

def ContinuousStructuredJetComponentFamilyData.toContinuousStructuredJetRieszFamilyData
    (data : ContinuousStructuredJetComponentFamilyData
      (Base := Base) (Tangent := Tangent) (Normal := Normal)
      (Ambient := Ambient) (ι := ι) (κ := κ)) :
    ContinuousStructuredJetRieszFamilyData
      (Base := Base) (Tangent := Tangent) (Normal := Normal)
      (Ambient := Ambient) (ι := ι) (κ := κ) where
  basisData := data.basisData
  ambientDimension := data.ambientDimension
  tangentBasis := data.tangentBasis
  tangentBasis_orthonormal := data.tangentBasis_orthonormal
  normalBasis := data.normalBasis
  normalBasis_orthonormal := data.normalBasis_orthonormal
  structuredJet := data.structuredJet
  physicalNormal := data.physicalNormal
  structuredJet_contDiff := data.structuredJet_contDiff
  physicalNormal_contDiff := data.physicalNormal_contDiff
  structuredJet_geometric := data.structuredJet_geometric

def ContinuousStructuredJetComponentFamilyData.physicalOperator
    (data : ContinuousStructuredJetComponentFamilyData
      (Base := Base) (Tangent := Tangent) (Normal := Normal)
      (Ambient := Ambient) (ι := ι) (κ := κ)) :
    Base → Tangent →L[ℝ] Tangent :=
  (SmoothReducedJetRieszFamilyData.toGlobalRieszCoefficientData
    (ContinuousStructuredJetRieszFamilyData.toSmoothReducedJetRieszFamilyData
      data.toContinuousStructuredJetRieszFamilyData)).physicalOperator

theorem ContinuousStructuredJetComponentFamilyData.physicalOperator_contDiff_direct
    (data : ContinuousStructuredJetComponentFamilyData
      (Base := Base) (Tangent := Tangent) (Normal := Normal)
      (Ambient := Ambient) (ι := ι) (κ := κ)) :
    ContDiff ℝ ∞ data.physicalOperator := by
  unfold ContinuousStructuredJetComponentFamilyData.physicalOperator
  exact ContinuousStructuredJetRieszFamilyData.physicalOperator_contDiff_direct
    data.toContinuousStructuredJetRieszFamilyData

theorem ContinuousStructuredJetComponentFamilyData.physicalOperator_contDiff_via_atlas
    {AtlasTangent AtlasNormal : Type y}
    (data : ContinuousStructuredJetComponentFamilyData
      (Base := Base) (Tangent := Tangent) (Normal := Normal)
      (Ambient := Ambient) (ι := ι) (κ := κ)) :
    ContDiff ℝ ∞ data.physicalOperator := by
  unfold ContinuousStructuredJetComponentFamilyData.physicalOperator
  exact ContinuousStructuredJetRieszFamilyData.physicalOperator_contDiff_via_atlas
    (AtlasTangent := AtlasTangent) (AtlasNormal := AtlasNormal)
    data.toContinuousStructuredJetRieszFamilyData

structure ContinuousStructuredJetReductionStatus where
  continuousImmersionJetConstructed : Prop
  continuousConnectionJetConstructed : Prop
  continuousCurvatureProjectionConstructed : Prop
  continuousReductionMapConstructed : Prop
  reductionMapSmooth : Prop
  algebraicReductionCompatibilityProved : Prop
  connectionCorrectedLiftConnected : Prop
  componentFamilyPackaged : Prop
  geometricityPreserved : Prop
  smoothFamilyReductionProved : Prop
  globalRieszSmoothnessDerived : Prop
  genuineJanusJetFamilyConstructed : Prop

def continuousStructuredJetReductionClosed
    (s : ContinuousStructuredJetReductionStatus) : Prop :=
  s.continuousImmersionJetConstructed ∧
  s.continuousConnectionJetConstructed ∧
  s.continuousCurvatureProjectionConstructed ∧
  s.continuousReductionMapConstructed ∧
  s.reductionMapSmooth ∧
  s.algebraicReductionCompatibilityProved ∧
  s.connectionCorrectedLiftConnected ∧
  s.componentFamilyPackaged ∧
  s.geometricityPreserved ∧
  s.smoothFamilyReductionProved ∧
  s.globalRieszSmoothnessDerived ∧
  s.genuineJanusJetFamilyConstructed

theorem missing_genuine_janus_jet_family_blocks_closure
    (s : ContinuousStructuredJetReductionStatus)
    (hMissing : Not s.genuineJanusJetFamilyConstructed) :
    Not (continuousStructuredJetReductionClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.2.2.2.2.2

end

end P0EFTJanusRieszShapeOperatorContinuousStructuredJetReduction
end JanusFormal
