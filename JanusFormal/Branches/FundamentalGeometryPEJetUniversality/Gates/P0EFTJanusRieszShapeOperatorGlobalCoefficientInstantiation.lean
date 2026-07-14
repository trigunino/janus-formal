import Mathlib
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusRieszShapeOperatorCanonicalProjectedSeedAssembly

namespace JanusFormal
namespace P0EFTJanusRieszShapeOperatorGlobalCoefficientInstantiation

set_option autoImplicit false

noncomputable section

open Set Module
open scoped ContDiff InnerProductSpace
open P0EFTJanusRieszShapeOperatorEquivariance
open P0EFTJanusRieszShapeOperatorSmoothDependence
open P0EFTJanusRieszShapeOperatorOpenMovingFrame
open P0EFTJanusRieszShapeOperatorPointwiseNormalBasisCover
open P0EFTJanusRieszShapeOperatorCanonicalProjectedSeedAssembly

universe u v w x y

variable {Base : Type w} {Tangent : Type u}
variable {Normal : Type v} {Ambient : Type x}
variable [NormedAddCommGroup Base] [NormedSpace ℝ Base]
variable [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
variable [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
variable [NormedAddCommGroup Ambient] [InnerProductSpace ℝ Ambient]
variable [FiniteDimensional ℝ Tangent]
variable [FiniteDimensional ℝ Normal]
variable [FiniteDimensional ℝ Ambient]

variable {ι κ : Type y}
variable [Fintype ι] [Fintype κ]
variable [LinearOrder κ] [LocallyFiniteOrderBot κ] [WellFoundedLT κ]

/-- Concrete coefficient input after the projected-seed frame geometry has been
constructed: a globally smooth fixed-model second fundamental form and a smooth
normal field. The physical operator is no longer an independent field; it is
constructed canonically by Riesz. -/
structure GlobalRieszCoefficientData where
  basisData : PointwiseNormalBasisData Base Ambient ι κ
  ambientDimension :
    Fintype.card ι + Fintype.card κ = finrank ℝ Ambient
  tangentBasis : Basis ι ℝ Tangent
  tangentBasis_orthonormal : Orthonormal ℝ tangentBasis
  normalBasis : Basis κ ℝ Normal
  normalBasis_orthonormal : Orthonormal ℝ normalBasis
  secondFundamental : Base → ContinuousSecondFundamentalForm
    (Tangent := Tangent) (Normal := Normal)
  physicalNormal : Base → Normal
  secondFundamental_contDiff : ContDiff ℝ ∞ secondFundamental
  physicalNormal_contDiff : ContDiff ℝ ∞ physicalNormal

/-- Coordinate-free physical shape-operator family obtained directly from the
coefficient pair `(II, ξ)`. -/
def GlobalRieszCoefficientData.physicalOperator
    (data : GlobalRieszCoefficientData
      (Base := Base) (Tangent := Tangent) (Normal := Normal)
      (Ambient := Ambient) (ι := ι) (κ := κ)) :
    Base → Tangent →L[ℝ] Tangent :=
  fun base => continuousIIRieszShapeOperator
    (data.secondFundamental base) (data.physicalNormal base)

/-- With identity reference frames, the open-chart geometric Riesz expression is
exactly the fixed-model Riesz operator. -/
theorem identity_geometricRieszShapeFamilyOn_apply
    (domain : Set Base)
    (form : Base → ContinuousSecondFundamentalForm
      (Tangent := Tangent) (Normal := Normal))
    (normal : Base → Normal)
    (base : Base) :
    geometricRieszShapeFamilyOn
        (identitySmoothOrthogonalFrameFamilyOn
          (Fiber := Tangent) domain)
        (identitySmoothOrthogonalFrameFamilyOn
          (Fiber := Normal) domain)
        form normal base =
      continuousIIRieszShapeOperator (form base) (normal base) := by
  apply ContinuousLinearMap.ext
  intro tangent
  simp [geometricRieszShapeFamilyOn, framedRieszShapeFamilyOn,
    movingFrameCoordinatesOn, conjugatedOperatorFamilyOn,
    identitySmoothOrthogonalFrameFamilyOn, conjugateShapeOperator]

/-- Global coefficient data automatically fills the canonical projected-seed
assembly. Chartwise regularity is obtained by restricting global smoothness, and
the realization law follows from the identity reference frames. -/
def GlobalRieszCoefficientData.toCanonicalProjectedSeedRieszData
    (data : GlobalRieszCoefficientData
      (Base := Base) (Tangent := Tangent) (Normal := Normal)
      (Ambient := Ambient) (ι := ι) (κ := κ)) :
    CanonicalProjectedSeedRieszData
      (Base := Base) (Tangent := Tangent) (Normal := Normal)
      (Ambient := Ambient) (ι := ι) (κ := κ) where
  basisData := data.basisData
  ambientDimension := data.ambientDimension
  tangentBasis := data.tangentBasis
  tangentBasis_orthonormal := data.tangentBasis_orthonormal
  normalBasis := data.normalBasis
  normalBasis_orthonormal := data.normalBasis_orthonormal
  physicalOperator := data.physicalOperator
  referenceForm := fun _ => data.secondFundamental
  physicalNormal := data.physicalNormal
  referenceForm_contDiffOn := by
    intro center
    exact data.secondFundamental_contDiff.contDiffOn
  physicalNormal_contDiffOn := by
    intro center
    exact data.physicalNormal_contDiff.contDiffOn
  reference_realizes_physical := by
    intro center base hBase
    exact identity_geometricRieszShapeFamilyOn_apply
      (pointwiseBasisChartDomain data.basisData center)
      data.secondFundamental data.physicalNormal base

/-- Direct fixed-model smoothness of the physical Riesz family. -/
theorem GlobalRieszCoefficientData.physicalOperator_contDiff_direct
    (data : GlobalRieszCoefficientData
      (Base := Base) (Tangent := Tangent) (Normal := Normal)
      (Ambient := Ambient) (ι := ι) (κ := κ)) :
    ContDiff ℝ ∞ data.physicalOperator := by
  exact continuousIIRieszShape_family_contDiff
    data.secondFundamental data.physicalNormal
    data.secondFundamental_contDiff data.physicalNormal_contDiff

/-- The same global smoothness conclusion derived through projected-seed atlas
construction and descent. This verifies that the abstract atlas machinery and
the direct fixed-model theorem meet on the same physical family. -/
theorem GlobalRieszCoefficientData.physicalOperator_contDiff_via_atlas
    {AtlasTangent AtlasNormal : Type y}
    (data : GlobalRieszCoefficientData
      (Base := Base) (Tangent := Tangent) (Normal := Normal)
      (Ambient := Ambient) (ι := ι) (κ := κ)) :
    ContDiff ℝ ∞ data.physicalOperator := by
  exact CanonicalProjectedSeedRieszData.physicalOperator_contDiff
    (AtlasTangent := AtlasTangent) (AtlasNormal := AtlasNormal)
    data.toCanonicalProjectedSeedRieszData

/-- Audit boundary after replacing an assumed physical operator and realization
law by the canonical Riesz construction from smooth global coefficients. -/
structure GlobalCoefficientInstantiationStatus where
  projectedSeedGeometrySupplied : Prop
  globalSecondFundamentalFormSupplied : Prop
  globalNormalFieldSupplied : Prop
  coefficientSmoothnessProved : Prop
  physicalOperatorConstructedByRiesz : Prop
  referenceRealizationAutomatic : Prop
  canonicalAtlasInstantiated : Prop
  directGlobalSmoothnessProved : Prop
  atlasGlobalSmoothnessProved : Prop
  coefficientsExtractedFromActualJanusJets : Prop

/-- Closure of the global coefficient instantiation stage. -/
def globalCoefficientInstantiationClosed
    (s : GlobalCoefficientInstantiationStatus) : Prop :=
  s.projectedSeedGeometrySupplied ∧
  s.globalSecondFundamentalFormSupplied ∧
  s.globalNormalFieldSupplied ∧
  s.coefficientSmoothnessProved ∧
  s.physicalOperatorConstructedByRiesz ∧
  s.referenceRealizationAutomatic ∧
  s.canonicalAtlasInstantiated ∧
  s.directGlobalSmoothnessProved ∧
  s.atlasGlobalSmoothnessProved ∧
  s.coefficientsExtractedFromActualJanusJets

/-- The remaining substantive boundary is now extraction of the smooth fixed-model
coefficient pair `(II, ξ)` from the genuine Janus structured-jet base. -/
theorem missing_actual_jet_coefficient_extraction_blocks_closure
    (s : GlobalCoefficientInstantiationStatus)
    (hMissing : Not s.coefficientsExtractedFromActualJanusJets) :
    Not (globalCoefficientInstantiationClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.2.2.2

end

end P0EFTJanusRieszShapeOperatorGlobalCoefficientInstantiation
end JanusFormal
