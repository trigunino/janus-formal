import Mathlib
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusRieszShapeOperatorContinuousStructuredJetReduction

namespace JanusFormal
namespace P0EFTJanusActualStructuredJetExtraction

set_option autoImplicit false

noncomputable section

open scoped ContDiff InnerProductSpace
open P0EFTJanusRieszShapeOperatorSmoothDependence
open P0EFTJanusRieszShapeOperatorSmoothReducedJetBase
open P0EFTJanusRieszShapeOperatorContinuousStructuredJetReduction

universe u v w

variable {Base : Type w} {Tangent : Type u} {Normal : Type v}
variable [NormedAddCommGroup Base] [NormedSpace ℝ Base]
variable [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
variable [NormedAddCommGroup Normal] [InnerProductSpace ℝ Normal]
variable [FiniteDimensional ℝ Tangent]
variable [FiniteDimensional ℝ Normal]

/-- Local coefficient package expected from a genuine Janus/SpinC jet after
choosing compatible tangent and normal trivializations.  This is the precise
interface between manifold-level jet extraction and the already closed
continuous reduction/Riesz pipeline. -/
structure ActualJanusLocalJetData where
  tangentialQuadratic : ContinuousTangentialQuadratic Tangent
  normalQuadratic : ContinuousSecondFundamentalForm
    (Tangent := Tangent) (Normal := Normal)
  connectionValue : ContinuousConnectionValue Tangent
  connectionDerivative : ContinuousConnectionDerivative Tangent
  physicalNormal : Normal
  tangentialQuadratic_symmetric :
    ∀ first second : Tangent,
      tangentialQuadratic first second = tangentialQuadratic second first
  normalQuadratic_symmetric :
    ∀ first second : Tangent,
      normalQuadratic first second = normalQuadratic second first

/-- Forget the geometric provenance and retain the continuous structured jet
consumed by the reduction theorem. -/
def ActualJanusLocalJetData.toStructuredJet
    (data : ActualJanusLocalJetData
      (Tangent := Tangent) (Normal := Normal)) :
    SmoothLowOrderStructuredJet Tangent Normal :=
  ((data.tangentialQuadratic, data.normalQuadratic),
    (data.connectionValue, data.connectionDerivative))

@[simp]
theorem ActualJanusLocalJetData.toStructuredJet_tangentialQuadratic
    (data : ActualJanusLocalJetData
      (Tangent := Tangent) (Normal := Normal)) :
    data.toStructuredJet.1.1 = data.tangentialQuadratic := by
  rfl

@[simp]
theorem ActualJanusLocalJetData.toStructuredJet_normalQuadratic
    (data : ActualJanusLocalJetData
      (Tangent := Tangent) (Normal := Normal)) :
    data.toStructuredJet.1.2 = data.normalQuadratic := by
  rfl

@[simp]
theorem ActualJanusLocalJetData.toStructuredJet_connectionDerivative
    (data : ActualJanusLocalJetData
      (Tangent := Tangent) (Normal := Normal)) :
    data.toStructuredJet.2.2 = data.connectionDerivative := by
  rfl

theorem ActualJanusLocalJetData.toStructuredJet_isGeometric
    (data : ActualJanusLocalJetData
      (Tangent := Tangent) (Normal := Normal)) :
    data.toStructuredJet.IsGeometric := by
  exact ⟨data.tangentialQuadratic_symmetric,
    data.normalQuadratic_symmetric⟩

/-- The reduced coefficient pair extracted from one local Janus jet. -/
def ActualJanusLocalJetData.toReducedJet
    (data : ActualJanusLocalJetData
      (Tangent := Tangent) (Normal := Normal)) :
    SmoothLowOrderReducedJet
      (Tangent := Tangent) (Normal := Normal) :=
  smoothLowOrderReduction data.toStructuredJet

@[simp]
theorem ActualJanusLocalJetData.toReducedJet_secondFundamental
    (data : ActualJanusLocalJetData
      (Tangent := Tangent) (Normal := Normal)) :
    data.toReducedJet.1 = data.normalQuadratic := by
  rfl

@[simp]
theorem ActualJanusLocalJetData.toReducedJet_curvature_apply
    (data : ActualJanusLocalJetData
      (Tangent := Tangent) (Normal := Normal))
    (first second : Tangent) :
    data.toReducedJet.2 first second =
      data.connectionDerivative first second -
        data.connectionDerivative second first := by
  simp [ActualJanusLocalJetData.toReducedJet,
    ActualJanusLocalJetData.toStructuredJet]

theorem ActualJanusLocalJetData.toReducedJet_isGeometric
    (data : ActualJanusLocalJetData
      (Tangent := Tangent) (Normal := Normal)) :
    data.toReducedJet.IsGeometric := by
  exact smoothLowOrderReduction_isGeometric
    data.toStructuredJet data.toStructuredJet_isGeometric

/-- A smooth family of local Janus coefficient packages.  The remaining
manifold-level problem is exactly to construct this object from genuine jets
and prove its trivialization-change laws. -/
structure ActualJanusLocalJetFamilyData where
  localJet : Base → ActualJanusLocalJetData
    (Tangent := Tangent) (Normal := Normal)
  tangentialQuadratic_contDiff : ContDiff ℝ ∞
    (fun base => (localJet base).tangentialQuadratic)
  normalQuadratic_contDiff : ContDiff ℝ ∞
    (fun base => (localJet base).normalQuadratic)
  connectionValue_contDiff : ContDiff ℝ ∞
    (fun base => (localJet base).connectionValue)
  connectionDerivative_contDiff : ContDiff ℝ ∞
    (fun base => (localJet base).connectionDerivative)
  physicalNormal_contDiff : ContDiff ℝ ∞
    (fun base => (localJet base).physicalNormal)

/-- Extract the structured jet family componentwise. -/
def ActualJanusLocalJetFamilyData.structuredJet
    (data : ActualJanusLocalJetFamilyData
      (Base := Base) (Tangent := Tangent) (Normal := Normal)) :
    Base → SmoothLowOrderStructuredJet Tangent Normal :=
  fun base => (data.localJet base).toStructuredJet

theorem ActualJanusLocalJetFamilyData.structuredJet_contDiff
    (data : ActualJanusLocalJetFamilyData
      (Base := Base) (Tangent := Tangent) (Normal := Normal)) :
    ContDiff ℝ ∞ data.structuredJet := by
  exact
    (data.tangentialQuadratic_contDiff.prodMk
      data.normalQuadratic_contDiff).prodMk
        (data.connectionValue_contDiff.prodMk
          data.connectionDerivative_contDiff)

/-- Extract the smooth reduced coefficient family `(II,F)`. -/
def ActualJanusLocalJetFamilyData.reducedJet
    (data : ActualJanusLocalJetFamilyData
      (Base := Base) (Tangent := Tangent) (Normal := Normal)) :
    Base → SmoothLowOrderReducedJet
      (Tangent := Tangent) (Normal := Normal) :=
  fun base => smoothLowOrderReduction (data.structuredJet base)

theorem ActualJanusLocalJetFamilyData.reducedJet_contDiff
    (data : ActualJanusLocalJetFamilyData
      (Base := Base) (Tangent := Tangent) (Normal := Normal)) :
    ContDiff ℝ ∞ data.reducedJet := by
  exact (smoothLowOrderReduction_contDiff
    (Tangent := Tangent) (Normal := Normal)).comp
      data.structuredJet_contDiff

/-- Honest status ledger for the remaining geometric extraction problem. -/
structure ActualJanusJetExtractionStatus where
  localCoefficientInterfaceConstructed : Prop
  structuredJetExtractionDefined : Prop
  reducedJetExtractionDefined : Prop
  smoothFamilyExtractionProved : Prop
  manifoldJetRealizationConstructed : Prop
  trivializationChangeCompatibilityProved : Prop
  globalSpinCJetExtractionConstructed : Prop

def actualJanusJetExtractionClosed
    (s : ActualJanusJetExtractionStatus) : Prop :=
  s.localCoefficientInterfaceConstructed ∧
  s.structuredJetExtractionDefined ∧
  s.reducedJetExtractionDefined ∧
  s.smoothFamilyExtractionProved ∧
  s.manifoldJetRealizationConstructed ∧
  s.trivializationChangeCompatibilityProved ∧
  s.globalSpinCJetExtractionConstructed

theorem missing_manifold_realization_blocks_extraction
    (s : ActualJanusJetExtractionStatus)
    (hMissing : Not s.manifoldJetRealizationConstructed) :
    Not (actualJanusJetExtractionClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.1

end

end P0EFTJanusActualStructuredJetExtraction
end JanusFormal
