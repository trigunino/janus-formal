import Mathlib
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusRieszShapeOperatorProjectedSeedNormalRangeTransition
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusRieszShapeOperatorOpenMovingFrame

namespace JanusFormal
namespace P0EFTJanusRieszShapeOperatorProjectedSeedAdaptedOverlap

set_option autoImplicit false

noncomputable section

open Set
open scoped ContDiff InnerProductSpace
open P0EFTJanusRieszShapeOperatorSmoothDependence
open P0EFTJanusRieszShapeOperatorOpenMovingFrame
open P0EFTJanusRieszShapeOperatorProjectedSeedAtlas
open P0EFTJanusRieszShapeOperatorPointwiseNormalBasisCover
open P0EFTJanusRieszShapeOperatorProjectedSeedSynthesisSmoothness
open P0EFTJanusRieszShapeOperatorProjectedSeedNormalRangeTransition

universe u v w x y

variable {Base : Type w} {TangentModel : Type u}
variable {NormalModel : Type v} {Ambient : Type x}
variable [NormedAddCommGroup Base] [NormedSpace ℝ Base]
variable [NormedAddCommGroup TangentModel]
variable [InnerProductSpace ℝ TangentModel]
variable [NormedAddCommGroup NormalModel]
variable [InnerProductSpace ℝ NormalModel]
variable [NormedAddCommGroup Ambient] [InnerProductSpace ℝ Ambient]
variable [FiniteDimensional ℝ TangentModel]
variable [FiniteDimensional ℝ NormalModel]
variable [FiniteDimensional ℝ Ambient]

variable {ι κ : Type y}
variable [Fintype ι] [Fintype κ] [LinearOrder κ]
variable [LocallyFiniteOrderBot κ] [WellFoundedLT κ]

/-- Linear synthesis of the physical tangent frame from fixed tangent
coordinates. -/
def tangentFrameSynthesisLinearMap
    (coordinateBasis : Basis ι ℝ TangentModel)
    (tangentFrame : ι → Base → Ambient)
    (base : Base) : TangentModel →ₗ[ℝ] Ambient :=
  coordinateBasis.constr ℝ (fun i => tangentFrame i base)

/-- Continuous-linear tangent synthesis operator. -/
def tangentFrameSynthesisCLM
    (coordinateBasis : Basis ι ℝ TangentModel)
    (tangentFrame : ι → Base → Ambient)
    (base : Base) : TangentModel →L[ℝ] Ambient :=
  (tangentFrameSynthesisLinearMap coordinateBasis tangentFrame base)
    .toContinuousLinearMap

@[simp]
theorem tangentFrameSynthesisCLM_basis
    (coordinateBasis : Basis ι ℝ TangentModel)
    (tangentFrame : ι → Base → Ambient)
    (base : Base) (i : ι) :
    tangentFrameSynthesisCLM coordinateBasis tangentFrame base
        (coordinateBasis i) = tangentFrame i base := by
  change coordinateBasis.constr ℝ (fun j => tangentFrame j base)
      (coordinateBasis i) = tangentFrame i base
  exact coordinateBasis.constr_basis ℝ _ i

/-- Finite rank-one expansion of tangent synthesis. -/
def tangentFrameSynthesisSumCLM
    (coordinateBasis : Basis ι ℝ TangentModel)
    (tangentFrame : ι → Base → Ambient)
    (base : Base) : TangentModel →L[ℝ] Ambient :=
  ∑ i, basisRankOneSynthesisCLM coordinateBasis i
    (tangentFrame i base)

@[simp]
theorem tangentFrameSynthesisSumCLM_basis
    (coordinateBasis : Basis ι ℝ TangentModel)
    (tangentFrame : ι → Base → Ambient)
    (base : Base) (i : ι) :
    tangentFrameSynthesisSumCLM coordinateBasis tangentFrame base
        (coordinateBasis i) = tangentFrame i base := by
  classical
  change (∑ j, coordinateBasis.coord j (coordinateBasis i) •
    tangentFrame j base) = tangentFrame i base
  simp

/-- Basis construction and rank-one construction of the tangent synthesis map
agree. -/
theorem tangentFrameSynthesisCLM_eq_sum
    (coordinateBasis : Basis ι ℝ TangentModel)
    (tangentFrame : ι → Base → Ambient)
    (base : Base) :
    tangentFrameSynthesisCLM coordinateBasis tangentFrame base =
      tangentFrameSynthesisSumCLM coordinateBasis tangentFrame base := by
  apply ContinuousLinearMap.ext
  intro vector
  conv_lhs => rw [← coordinateBasis.sum_equivFun vector]
  conv_rhs => rw [← coordinateBasis.sum_equivFun vector]
  simp only [map_sum, map_smul]
  simp

/-- A componentwise smooth finite tangent frame has a smooth synthesis operator. -/
theorem tangentFrameSynthesisCLM_contDiff
    (coordinateBasis : Basis ι ℝ TangentModel)
    (tangentFrame : ι → Base → Ambient)
    (hTangent : ∀ i, ContDiff ℝ ∞ (tangentFrame i)) :
    ContDiff ℝ ∞ (tangentFrameSynthesisCLM coordinateBasis tangentFrame) := by
  have hSum : ContDiff ℝ ∞
      (tangentFrameSynthesisSumCLM coordinateBasis tangentFrame) := by
    classical
    unfold tangentFrameSynthesisSumCLM
    apply ContDiff.sum
    intro i hi
    exact (basisRankOneSynthesisCLM coordinateBasis i).contDiff.comp
      (hTangent i)
  apply hSum.congr
  intro base
  exact (tangentFrameSynthesisCLM_eq_sum
    coordinateBasis tangentFrame base).symm

/-- Pointwise tangent isometry produced from a fixed orthonormal coordinate
basis and a physical orthonormal tangent frame. -/
def tangentFrameIsometry
    (coordinateBasis : Basis ι ℝ TangentModel)
    (hCoordinateOrthonormal : Orthonormal ℝ coordinateBasis)
    (tangentFrame : ι → Base → Ambient)
    (hTangentOrthonormal : ∀ base,
      Orthonormal ℝ (fun i => tangentFrame i base))
    (base : Base) : TangentModel →ₗᵢ[ℝ] Ambient := by
  let synthesis := tangentFrameSynthesisLinearMap
    coordinateBasis tangentFrame base
  have hImage : Orthonormal ℝ (synthesis ∘ coordinateBasis) := by
    simpa [synthesis, Function.comp_def] using hTangentOrthonormal base
  exact synthesis.isometryOfOrthonormal hCoordinateOrthonormal hImage

/-- The tangent isometry has the expected synthesis operator. -/
theorem tangentFrameIsometry_toContinuousLinearMap
    (coordinateBasis : Basis ι ℝ TangentModel)
    (hCoordinateOrthonormal : Orthonormal ℝ coordinateBasis)
    (tangentFrame : ι → Base → Ambient)
    (hTangentOrthonormal : ∀ base,
      Orthonormal ℝ (fun i => tangentFrame i base))
    (base : Base) :
    (tangentFrameIsometry coordinateBasis hCoordinateOrthonormal
      tangentFrame hTangentOrthonormal base).toContinuousLinearMap =
      tangentFrameSynthesisCLM coordinateBasis tangentFrame base := by
  apply ContinuousLinearMap.ext
  intro vector
  rfl

/-- The physical tangent frame packages as a smooth isometric frame family on
any chosen chart domain. -/
def tangentSmoothIsometricFrameFamilyOn
    {domain : Set Base}
    (coordinateBasis : Basis ι ℝ TangentModel)
    (hCoordinateOrthonormal : Orthonormal ℝ coordinateBasis)
    (tangentFrame : ι → Base → Ambient)
    (hTangent : ∀ i, ContDiff ℝ ∞ (tangentFrame i))
    (hTangentOrthonormal : ∀ base,
      Orthonormal ℝ (fun i => tangentFrame i base)) :
    P0EFTJanusRieszShapeOperatorOpenCanonicalTransition.SmoothIsometricFrameFamilyOn
      Base TangentModel Ambient domain where
  frame := tangentFrameIsometry coordinateBasis hCoordinateOrthonormal
    tangentFrame hTangentOrthonormal
  forward_contDiffOn := by
    apply (tangentFrameSynthesisCLM_contDiff
      coordinateBasis tangentFrame hTangent).contDiffOn.congr
    intro base hBase
    exact tangentFrameIsometry_toContinuousLinearMap coordinateBasis
      hCoordinateOrthonormal tangentFrame hTangentOrthonormal base

/-- Identity tangent-coordinate transition on one open overlap. -/
def identitySmoothOrthogonalFrameFamilyOn
    {Fiber : Type*}
    [NormedAddCommGroup Fiber] [InnerProductSpace ℝ Fiber]
    {domain : Set Base} :
    SmoothOrthogonalFrameFamilyOn Base Fiber domain where
  frame := fun _ => LinearIsometryEquiv.refl ℝ Fiber
  forward_contDiffOn := contDiffOn_const
  inverse_contDiffOn := contDiffOn_const

/-- Full residual tangent/normal transition between two projected-seed charts.
The tangent chart is common, hence its transition is the identity; the normal
transition is the canonical constant-rank transition constructed previously. -/
def pointwiseBasisAdaptedResidualTransitionOnOverlap
    (tangentCoordinateBasis : Basis ι ℝ TangentModel)
    (hTangentCoordinateOrthonormal : Orthonormal ℝ tangentCoordinateBasis)
    (normalCoordinateBasis : Basis κ ℝ NormalModel)
    (hNormalCoordinateOrthonormal : Orthonormal ℝ normalCoordinateBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (hNormalRank : ∀ base,
      Module.finrank ℝ NormalModel =
        Module.finrank ℝ (tangentFrameNormalSubspace
          basisData.tangentFrame base))
    (first second : Base) :
    SmoothResidualOrthogonalFrameFamilyOn
      Base TangentModel NormalModel
      (pointwiseBasisOverlapDomain basisData first second) where
  tangent := identitySmoothOrthogonalFrameFamilyOn
  normal := pointwiseBasisNormalTransitionOnOverlap
    normalCoordinateBasis hNormalCoordinateOrthonormal
    basisData hNormalRank first second

/-- Invariance of the physical Riesz expression under the canonical full
projected-seed overlap transition. -/
theorem projectedSeedAdaptedOverlap_riesz_invariant
    (tangentCoordinateBasis : Basis ι ℝ TangentModel)
    (hTangentCoordinateOrthonormal : Orthonormal ℝ tangentCoordinateBasis)
    (normalCoordinateBasis : Basis κ ℝ NormalModel)
    (hNormalCoordinateOrthonormal : Orthonormal ℝ normalCoordinateBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (hNormalRank : ∀ base,
      Module.finrank ℝ NormalModel =
        Module.finrank ℝ (tangentFrameNormalSubspace
          basisData.tangentFrame base))
    (first second : Base)
    (tangentFrame : SmoothOrthogonalFrameFamilyOn
      Base TangentModel (pointwiseBasisOverlapDomain basisData first second))
    (normalFrame : SmoothOrthogonalFrameFamilyOn
      Base NormalModel (pointwiseBasisOverlapDomain basisData first second))
    (form : Base → ContinuousSecondFundamentalForm
      (Tangent := TangentModel) (Normal := NormalModel))
    (physicalNormal : Base → NormalModel) :
    geometricRieszShapeFamilyOn
        (reparametrizeSmoothOrthogonalFrameFamilyOn tangentFrame
          (pointwiseBasisAdaptedResidualTransitionOnOverlap
            tangentCoordinateBasis hTangentCoordinateOrthonormal
            normalCoordinateBasis hNormalCoordinateOrthonormal
            basisData hNormalRank first second).tangent)
        (reparametrizeSmoothOrthogonalFrameFamilyOn normalFrame
          (pointwiseBasisAdaptedResidualTransitionOnOverlap
            tangentCoordinateBasis hTangentCoordinateOrthonormal
            normalCoordinateBasis hNormalCoordinateOrthonormal
            basisData hNormalRank first second).normal)
        (transformContinuousIIOnOpenOverlap
          (pointwiseBasisAdaptedResidualTransitionOnOverlap
            tangentCoordinateBasis hTangentCoordinateOrthonormal
            normalCoordinateBasis hNormalCoordinateOrthonormal
            basisData hNormalRank first second) form)
        physicalNormal =
      geometricRieszShapeFamilyOn tangentFrame normalFrame form physicalNormal := by
  exact geometricRieszShapeFamilyOn_variable_coordinate_invariant
    tangentFrame normalFrame
    (pointwiseBasisAdaptedResidualTransitionOnOverlap
      tangentCoordinateBasis hTangentCoordinateOrthonormal
      normalCoordinateBasis hNormalCoordinateOrthonormal
      basisData hNormalRank first second)
    form physicalNormal

/-- Chartwise smoothness after canonical projected-seed overlap
reparametrization. -/
theorem projectedSeedAdaptedOverlap_riesz_contDiffOn
    (tangentCoordinateBasis : Basis ι ℝ TangentModel)
    (hTangentCoordinateOrthonormal : Orthonormal ℝ tangentCoordinateBasis)
    (normalCoordinateBasis : Basis κ ℝ NormalModel)
    (hNormalCoordinateOrthonormal : Orthonormal ℝ normalCoordinateBasis)
    (basisData : PointwiseNormalBasisData Base Ambient ι κ)
    (hNormalRank : ∀ base,
      Module.finrank ℝ NormalModel =
        Module.finrank ℝ (tangentFrameNormalSubspace
          basisData.tangentFrame base))
    (first second : Base)
    (tangentFrame : SmoothOrthogonalFrameFamilyOn
      Base TangentModel (pointwiseBasisOverlapDomain basisData first second))
    (normalFrame : SmoothOrthogonalFrameFamilyOn
      Base NormalModel (pointwiseBasisOverlapDomain basisData first second))
    (form : Base → ContinuousSecondFundamentalForm
      (Tangent := TangentModel) (Normal := NormalModel))
    (physicalNormal : Base → NormalModel)
    (hForm : ContDiffOn ℝ ∞ form
      (pointwiseBasisOverlapDomain basisData first second))
    (hPhysicalNormal : ContDiffOn ℝ ∞ physicalNormal
      (pointwiseBasisOverlapDomain basisData first second)) :
    ContDiffOn ℝ ∞
      (geometricRieszShapeFamilyOn
        (reparametrizeSmoothOrthogonalFrameFamilyOn tangentFrame
          (pointwiseBasisAdaptedResidualTransitionOnOverlap
            tangentCoordinateBasis hTangentCoordinateOrthonormal
            normalCoordinateBasis hNormalCoordinateOrthonormal
            basisData hNormalRank first second).tangent)
        (reparametrizeSmoothOrthogonalFrameFamilyOn normalFrame
          (pointwiseBasisAdaptedResidualTransitionOnOverlap
            tangentCoordinateBasis hTangentCoordinateOrthonormal
            normalCoordinateBasis hNormalCoordinateOrthonormal
            basisData hNormalRank first second).normal)
        (transformContinuousIIOnOpenOverlap
          (pointwiseBasisAdaptedResidualTransitionOnOverlap
            tangentCoordinateBasis hTangentCoordinateOrthonormal
            normalCoordinateBasis hNormalCoordinateOrthonormal
            basisData hNormalRank first second) form)
        physicalNormal)
      (pointwiseBasisOverlapDomain basisData first second) := by
  exact geometricRieszShapeFamilyOn_variable_overlap_contDiffOn
    tangentFrame normalFrame
    (pointwiseBasisAdaptedResidualTransitionOnOverlap
      tangentCoordinateBasis hTangentCoordinateOrthonormal
      normalCoordinateBasis hNormalCoordinateOrthonormal
      basisData hNormalRank first second)
    form physicalNormal hForm hPhysicalNormal

/-- Exact status after full adapted projected-seed overlap construction. -/
structure ProjectedSeedAdaptedOverlapStatus where
  tangentSynthesisConstructed : Prop
  tangentSynthesisSmooth : Prop
  tangentIsometricFramePackaged : Prop
  identityTangentTransitionConstructed : Prop
  canonicalNormalTransitionConstructed : Prop
  fullResidualTransitionConstructed : Prop
  RieszOverlapInvarianceProved : Prop
  RieszOverlapContDiffOnProved : Prop
  insertedIntoGlobalOpenAtlas : Prop

/-- Closure of the full adapted-overlap stage. -/
def projectedSeedAdaptedOverlapClosed
    (s : ProjectedSeedAdaptedOverlapStatus) : Prop :=
  s.tangentSynthesisConstructed ∧
  s.tangentSynthesisSmooth ∧
  s.tangentIsometricFramePackaged ∧
  s.identityTangentTransitionConstructed ∧
  s.canonicalNormalTransitionConstructed ∧
  s.fullResidualTransitionConstructed ∧
  s.RieszOverlapInvarianceProved ∧
  s.RieszOverlapContDiffOnProved ∧
  s.insertedIntoGlobalOpenAtlas

/-- The remaining operation is insertion into the existing global open-atlas
descent package. -/
theorem missing_global_open_atlas_insertion_blocks_closure
    (s : ProjectedSeedAdaptedOverlapStatus)
    (hMissing : Not s.insertedIntoGlobalOpenAtlas) :
    Not (projectedSeedAdaptedOverlapClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.2.2

end

end P0EFTJanusRieszShapeOperatorProjectedSeedAdaptedOverlap
end JanusFormal
