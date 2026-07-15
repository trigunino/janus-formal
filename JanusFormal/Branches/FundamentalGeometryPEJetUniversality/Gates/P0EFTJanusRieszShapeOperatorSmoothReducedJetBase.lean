import Mathlib
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusLowOrderStructuredBackground
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusRieszShapeOperatorGlobalCoefficientInstantiation

namespace JanusFormal
namespace P0EFTJanusRieszShapeOperatorSmoothReducedJetBase

set_option autoImplicit false

noncomputable section

open Module
open scoped ContDiff InnerProductSpace
open P0EFTJanusLowOrderStructuredBackground
open P0EFTJanusRieszShapeOperatorSmoothDependence
open P0EFTJanusRieszShapeOperatorPointwiseNormalBasisCover
open P0EFTJanusRieszShapeOperatorGlobalCoefficientInstantiation

universe u v w x y

variable {Tangent : Type u} {Normal : Type v}
variable [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
variable [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
variable [FiniteDimensional ℝ Tangent]
variable [FiniteDimensional ℝ Normal]

/-- Continuous fixed-model representative of the abelian curvature two-form. -/
abbrev ContinuousGaugeCurvature :=
  Tangent →L[ℝ] Tangent →L[ℝ] ℝ

/-- Smooth finite-dimensional model of the reduced low-order coefficient pair
`(II,F)`. It is an honest normed vector space, unlike the earlier function-valued
quotient carrier used only for algebraic orbit classification. -/
abbrev SmoothLowOrderReducedJet :=
  ContinuousSecondFundamentalForm
      (Tangent := Tangent) (Normal := Normal) ×
    ContinuousGaugeCurvature (Tangent := Tangent)

/-- Geometric symmetry and alternating conditions on the smooth reduced model. -/
def SmoothLowOrderReducedJet.IsGeometric
    (jet : SmoothLowOrderReducedJet
      (Tangent := Tangent) (Normal := Normal)) : Prop :=
  (∀ x y, jet.1 x y = jet.1 y x) ∧
    (∀ x y, jet.2 y x = -jet.2 x y)

/-- Continuous-linear projection to the second fundamental form coefficient. -/
def reducedSecondFundamentalProjection :
    SmoothLowOrderReducedJet
        (Tangent := Tangent) (Normal := Normal) →L[ℝ]
      ContinuousSecondFundamentalForm
        (Tangent := Tangent) (Normal := Normal) :=
  ContinuousLinearMap.fst ℝ
    (ContinuousSecondFundamentalForm
      (Tangent := Tangent) (Normal := Normal))
    (ContinuousGaugeCurvature (Tangent := Tangent))

/-- Continuous-linear projection to the abelian curvature coefficient. -/
def reducedGaugeCurvatureProjection :
    SmoothLowOrderReducedJet
        (Tangent := Tangent) (Normal := Normal) →L[ℝ]
      ContinuousGaugeCurvature (Tangent := Tangent) :=
  ContinuousLinearMap.snd ℝ
    (ContinuousSecondFundamentalForm
      (Tangent := Tangent) (Normal := Normal))
    (ContinuousGaugeCurvature (Tangent := Tangent))

@[simp]
theorem reducedSecondFundamentalProjection_apply
    (jet : SmoothLowOrderReducedJet
      (Tangent := Tangent) (Normal := Normal)) :
    reducedSecondFundamentalProjection
        (Tangent := Tangent) (Normal := Normal) jet = jet.1 := by
  rfl

@[simp]
theorem reducedGaugeCurvatureProjection_apply
    (jet : SmoothLowOrderReducedJet
      (Tangent := Tangent) (Normal := Normal)) :
    reducedGaugeCurvatureProjection
        (Tangent := Tangent) (Normal := Normal) jet = jet.2 := by
  rfl

/-- Reduced Riesz input: one smooth reduced jet together with a selected normal
parameter. -/
abbrev SmoothLowOrderRieszPoint :=
  SmoothLowOrderReducedJet
      (Tangent := Tangent) (Normal := Normal) × Normal

/-- Projection from a reduced Riesz point to `II`. -/
def reducedRieszSecondFundamentalProjection :
    SmoothLowOrderRieszPoint
        (Tangent := Tangent) (Normal := Normal) →L[ℝ]
      ContinuousSecondFundamentalForm
        (Tangent := Tangent) (Normal := Normal) :=
  (reducedSecondFundamentalProjection
    (Tangent := Tangent) (Normal := Normal)).comp
      (ContinuousLinearMap.fst ℝ
        (SmoothLowOrderReducedJet
          (Tangent := Tangent) (Normal := Normal)) Normal)

/-- Projection from a reduced Riesz point to its normal parameter. -/
def reducedRieszNormalProjection :
    SmoothLowOrderRieszPoint
        (Tangent := Tangent) (Normal := Normal) →L[ℝ] Normal :=
  ContinuousLinearMap.snd ℝ
    (SmoothLowOrderReducedJet
      (Tangent := Tangent) (Normal := Normal)) Normal

/-- Riesz shape operator evaluated directly on the smooth reduced jet base. -/
def smoothLowOrderRieszOperator
    (point : SmoothLowOrderRieszPoint
      (Tangent := Tangent) (Normal := Normal)) :
    Tangent →L[ℝ] Tangent :=
  continuousIIRieszShapeOperator point.1.1 point.2

/-- The Riesz evaluator is globally smooth on the explicit reduced jet vector
space. -/
theorem smoothLowOrderRieszOperator_contDiff :
    ContDiff ℝ ∞
      (smoothLowOrderRieszOperator
        (Tangent := Tangent) (Normal := Normal)) := by
  unfold smoothLowOrderRieszOperator
  exact continuousIIRieszShape_family_contDiff
    (Tangent := Tangent) (Normal := Normal)
    (fun point : SmoothLowOrderRieszPoint
      (Tangent := Tangent) (Normal := Normal) => point.1.1)
    (fun point : SmoothLowOrderRieszPoint
      (Tangent := Tangent) (Normal := Normal) => point.2)
    (by fun_prop) (by fun_prop)

variable {Base : Type w} {Ambient : Type x}
variable [NormedAddCommGroup Base] [NormedSpace ℝ Base]
variable [NormedAddCommGroup Ambient] [InnerProductSpace ℝ Ambient]
variable [FiniteDimensional ℝ Ambient]
variable {ι κ : Type y}
variable [Fintype ι] [Fintype κ]
variable [LinearOrder κ] [LocallyFiniteOrderBot κ] [WellFoundedLT κ]

/-- A smooth family of reduced low-order jets together with all projected-seed
geometry needed by the canonical Riesz descent. -/
structure SmoothReducedJetRieszFamilyData where
  basisData : PointwiseNormalBasisData Base Ambient ι κ
  ambientDimension :
    Fintype.card ι + Fintype.card κ = finrank ℝ Ambient
  tangentBasis : Basis ι ℝ Tangent
  tangentBasis_orthonormal : Orthonormal ℝ tangentBasis
  normalBasis : Basis κ ℝ Normal
  normalBasis_orthonormal : Orthonormal ℝ normalBasis
  reducedJet : Base → SmoothLowOrderReducedJet
    (Tangent := Tangent) (Normal := Normal)
  physicalNormal : Base → Normal
  reducedJet_contDiff : ContDiff ℝ ∞ reducedJet
  physicalNormal_contDiff : ContDiff ℝ ∞ physicalNormal
  reducedJet_geometric : ∀ base, (reducedJet base).IsGeometric

/-- Extract the smooth second fundamental form family from the reduced jet. -/
def SmoothReducedJetRieszFamilyData.secondFundamental
    (data : SmoothReducedJetRieszFamilyData
      (Base := Base) (Tangent := Tangent) (Normal := Normal)
      (Ambient := Ambient) (ι := ι) (κ := κ)) :
    Base → ContinuousSecondFundamentalForm
      (Tangent := Tangent) (Normal := Normal) :=
  fun base => (data.reducedJet base).1

/-- Extraction of `II` from a smooth reduced-jet family is smooth. -/
theorem SmoothReducedJetRieszFamilyData.secondFundamental_contDiff
    (data : SmoothReducedJetRieszFamilyData
      (Base := Base) (Tangent := Tangent) (Normal := Normal)
      (Ambient := Ambient) (ι := ι) (κ := κ)) :
    ContDiff ℝ ∞ data.secondFundamental := by
  change ContDiff ℝ ∞ (fun base => (data.reducedJet base).1)
  exact data.reducedJet_contDiff.fst

/-- Smooth reduced-jet data automatically instantiates the global coefficient
interface used by canonical projected-seed descent. -/
def SmoothReducedJetRieszFamilyData.toGlobalRieszCoefficientData
    (data : SmoothReducedJetRieszFamilyData
      (Base := Base) (Tangent := Tangent) (Normal := Normal)
      (Ambient := Ambient) (ι := ι) (κ := κ)) :
    GlobalRieszCoefficientData
      (Base := Base) (Tangent := Tangent) (Normal := Normal)
      (Ambient := Ambient) (ι := ι) (κ := κ) where
  basisData := data.basisData
  ambientDimension := data.ambientDimension
  tangentBasis := data.tangentBasis
  tangentBasis_orthonormal := data.tangentBasis_orthonormal
  normalBasis := data.normalBasis
  normalBasis_orthonormal := data.normalBasis_orthonormal
  secondFundamental := data.secondFundamental
  physicalNormal := data.physicalNormal
  secondFundamental_contDiff := data.secondFundamental_contDiff
  physicalNormal_contDiff := data.physicalNormal_contDiff

/-- Direct global smoothness of the shape-operator family extracted from a smooth
reduced jet family. -/
theorem SmoothReducedJetRieszFamilyData.physicalOperator_contDiff_direct
    (data : SmoothReducedJetRieszFamilyData
      (Base := Base) (Tangent := Tangent) (Normal := Normal)
      (Ambient := Ambient) (ι := ι) (κ := κ)) :
    ContDiff ℝ ∞ data.toGlobalRieszCoefficientData.physicalOperator :=
  data.toGlobalRieszCoefficientData.physicalOperator_contDiff_direct

/-- The same conclusion through projected-seed atlas descent. -/
theorem SmoothReducedJetRieszFamilyData.physicalOperator_contDiff_via_atlas
    {AtlasTangent AtlasNormal : Type y}
    (data : SmoothReducedJetRieszFamilyData
      (Base := Base) (Tangent := Tangent) (Normal := Normal)
      (Ambient := Ambient) (ι := ι) (κ := κ)) :
    ContDiff ℝ ∞ data.toGlobalRieszCoefficientData.physicalOperator :=
  data.toGlobalRieszCoefficientData.physicalOperator_contDiff_via_atlas
    (AtlasTangent := AtlasTangent) (AtlasNormal := AtlasNormal)

/-- Exact relation to the earlier algebraic quotient carrier: a continuous lift
supplies bundled linear representatives of its two raw tensor fields. -/
structure ContinuousLiftOfLowOrderReducedData
    (data : LowOrderReducedData Tangent Normal) where
  smoothJet : SmoothLowOrderReducedJet
    (Tangent := Tangent) (Normal := Normal)
  secondFundamental_apply :
    ∀ x y, smoothJet.1 x y = data.secondFundamental x y
  gaugeCurvature_apply :
    ∀ x y, smoothJet.2 x y = data.gaugeCurvature x y

/-- Audit boundary after constructing an honest smooth reduced jet base. -/
structure SmoothReducedJetBaseStatus where
  continuousSecondFundamentalSpaceUsed : Prop
  continuousGaugeCurvatureSpaceConstructed : Prop
  productNormedVectorSpaceConstructed : Prop
  geometricSymmetryPredicatesInserted : Prop
  RieszEvaluatorSmooth : Prop
  smoothFamilyExtractionProved : Prop
  globalCoefficientInterfaceInstantiated : Prop
  directAndAtlasSmoothnessProved : Prop
  continuousLiftFromAlgebraicQuotientConstructed : Prop
  actualJanusJetMapConstructed : Prop

/-- Closure of the smooth reduced-jet stage. -/
def smoothReducedJetBaseClosed (s : SmoothReducedJetBaseStatus) : Prop :=
  s.continuousSecondFundamentalSpaceUsed ∧
  s.continuousGaugeCurvatureSpaceConstructed ∧
  s.productNormedVectorSpaceConstructed ∧
  s.geometricSymmetryPredicatesInserted ∧
  s.RieszEvaluatorSmooth ∧
  s.smoothFamilyExtractionProved ∧
  s.globalCoefficientInterfaceInstantiated ∧
  s.directAndAtlasSmoothnessProved ∧
  s.continuousLiftFromAlgebraicQuotientConstructed ∧
  s.actualJanusJetMapConstructed

/-- The remaining step is the concrete smooth map from genuine Janus jets to the
continuous reduced coefficient model. -/
theorem missing_actual_janus_jet_map_blocks_closure
    (s : SmoothReducedJetBaseStatus)
    (hMissing : Not s.actualJanusJetMapConstructed) :
    Not (smoothReducedJetBaseClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.2.2.2

end

end P0EFTJanusRieszShapeOperatorSmoothReducedJetBase
end JanusFormal
