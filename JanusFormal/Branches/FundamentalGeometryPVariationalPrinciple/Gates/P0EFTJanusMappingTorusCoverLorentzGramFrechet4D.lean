import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteGramInducedMetricFrechetBridge
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicCoverLorentzTensor4D

/-!
# Pointwise Frechet linearization of the true cover Lorentz Gram map

At every point of the genuine mapping-torus cover, this gate regards the
ambient immersion derivative as an element of its full normed one-jet space.
It constructs the product-Minkowski Gram map `K`, computes its genuine
Frechet derivative `J`, and proves that `K` evaluated on the actual manifold
derivative is exactly the already constructed smooth intrinsic Lorentz tensor.

This is a pointwise fiber theorem on the cover.  It does not construct a
global differential complex, a quotient Sobolev operator, or boundary data.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCoverLorentzGramFrechet4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusFiniteGramInducedMetricFrechetBridge
open P0EFTJanusMappingTorusIntrinsicCoverLorentzTensor4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveCover := MappingTorusCover (sphereData period hPeriod)

local instance effectiveCoverChartedSpace :
    ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod

local instance effectiveCoverIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveCover period hPeriod) :=
  reflectedSphereCover_isManifold period hPeriod

abbrev CoverAmbientCoordinates := EuclideanR4 × Real

private abbrev CoverIntrinsicTangent
    (point : EffectiveCover period hPeriod) :=
  TangentSpace coverModelWithCorners point

abbrev CoverLorentzOneJet :=
  CoverCoordinates →L[Real] CoverAmbientCoordinates

local instance coverLorentzOneJetNormedAddCommGroup :
    NormedAddCommGroup CoverLorentzOneJet := inferInstance

local instance coverLorentzOneJetNormedSpace :
    NormedSpace Real CoverLorentzOneJet := inferInstance

local instance coverLorentzOneJetTopologicalSpace :
    TopologicalSpace CoverLorentzOneJet :=
  coverLorentzOneJetNormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

local instance coverLorentzOneJetAddCommGroup :
    AddCommGroup CoverLorentzOneJet :=
  coverLorentzOneJetNormedAddCommGroup.toAddCommGroup

local instance coverLorentzOneJetModule : Module Real CoverLorentzOneJet :=
  coverLorentzOneJetNormedSpace.toModule

local instance coverRealNormedAddCommGroup : NormedAddCommGroup Real :=
  inferInstance

local instance coverRealNormedSpace : NormedSpace Real Real :=
  inferInstance

local instance coverRealAddCommGroup : AddCommGroup Real :=
  coverRealNormedAddCommGroup.toAddCommGroup

local instance coverRealModule : Module Real Real :=
  coverRealNormedSpace.toModule

/-- The true manifold immersion derivative written in the fixed model
coordinates of the tangent and trivial ambient bundles. -/
def coverAmbientDerivativeCoordinates
    (point : EffectiveCover period hPeriod) : CoverLorentzOneJet :=
  (coverAmbientDerivative period hPeriod point).comp
    ((trivializationAt CoverCoordinates
      (CoverIntrinsicTangent period hPeriod) point).symmL Real point)

/-- Continuous product-Minkowski pairing on the fixed ambient model. -/
def coverAmbientLorentzPair :
    CoverAmbientCoordinates →L[Real]
      CoverAmbientCoordinates →L[Real] Real :=
  let spatialProjection :=
    ContinuousLinearMap.fst Real EuclideanR4 Real
  let timeProjection :=
    ContinuousLinearMap.snd Real EuclideanR4 Real
  let spatialPair :=
    ((ContinuousLinearMap.precompR CoverAmbientCoordinates
      ((innerSL Real : EuclideanR4 →L[Real] EuclideanR4 →L[Real] Real).comp
        spatialProjection)).flip) spatialProjection
  let timePair :=
    ((ContinuousLinearMap.precompR CoverAmbientCoordinates
      ((ContinuousLinearMap.lsmul Real Real).comp timeProjection)).flip)
        timeProjection
  spatialPair - timePair

@[simp]
theorem coverAmbientLorentzPair_apply
    (first second : CoverAmbientCoordinates) :
    coverAmbientLorentzPair first second =
      inner Real first.1 second.1 - first.2 * second.2 := by
  rfl

/-- Evaluation of a one-jet at a fixed model tangent vector. -/
def coverJetEvaluation (vector : CoverCoordinates) :
    CoverLorentzOneJet →L[Real] CoverAmbientCoordinates :=
  ContinuousLinearMap.apply Real CoverAmbientCoordinates vector

@[simp]
theorem coverJetEvaluation_apply
    (vector : CoverCoordinates) (jet : CoverLorentzOneJet) :
    coverJetEvaluation vector jet = jet vector := by
  rfl

/-- Continuous bilinear scalar component of the product-Minkowski Gram map. -/
def coverLorentzGramComponentBilinear (first second : CoverCoordinates) :
    CoverLorentzOneJet →L[Real] CoverLorentzOneJet →L[Real] Real :=
  ((ContinuousLinearMap.precompR CoverLorentzOneJet
    (coverAmbientLorentzPair.comp (coverJetEvaluation first))).flip)
      (coverJetEvaluation second)

@[simp]
theorem coverLorentzGramComponentBilinear_apply
    (first second : CoverCoordinates) (left right : CoverLorentzOneJet) :
    coverLorentzGramComponentBilinear first second left right =
      inner Real (left first).1 (right second).1 -
        (left first).2 * (right second).2 := by
  rfl

/-- Concrete scalar component of the pointwise compatibility map
`K(F) = F*η`. -/
def coverLorentzGramCompatibilityComponent
    (first second : CoverCoordinates) (jet : CoverLorentzOneJet) : Real :=
  coverLorentzGramComponentBilinear first second jet jet

/-- Concrete Jacobian of one scalar component of `K`. -/
def coverLorentzGramComponentLinearization
    (first second : CoverCoordinates) (jet : CoverLorentzOneJet) :
    CoverLorentzOneJet →L[Real] Real :=
  (coverLorentzGramComponentBilinear first second).precompR
      CoverLorentzOneJet jet
      (ContinuousLinearMap.id Real CoverLorentzOneJet) +
    (coverLorentzGramComponentBilinear first second).precompL
      CoverLorentzOneJet (ContinuousLinearMap.id Real CoverLorentzOneJet) jet

@[simp]
theorem coverLorentzGramComponentLinearization_apply
    (first second : CoverCoordinates) (jet variation : CoverLorentzOneJet) :
    coverLorentzGramComponentLinearization first second jet variation =
      (inner Real (variation first).1 (jet second).1 -
          (variation first).2 * (jet second).2) +
        (inner Real (jet first).1 (variation second).1 -
          (jet first).2 * (variation second).2) := by
  simp [coverLorentzGramComponentLinearization,
    coverLorentzGramComponentBilinear_apply]
  ring

/-- Every scalar component of `J` is the genuine Frechet derivative of the
corresponding component of the displayed `K`. -/
theorem coverLorentzGramCompatibilityComponent_hasFDerivAt
    (first second : CoverCoordinates) (jet : CoverLorentzOneJet) :
    HasFDerivAt (coverLorentzGramCompatibilityComponent first second)
      (coverLorentzGramComponentLinearization first second jet) jet := by
  change @HasFDerivAt Real _ CoverLorentzOneJet
    coverLorentzOneJetNormedAddCommGroup.toAddCommGroup
    coverLorentzOneJetNormedSpace.toModule
    coverLorentzOneJetNormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    Real coverRealNormedAddCommGroup.toAddCommGroup
    coverRealNormedSpace.toModule
    coverRealNormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    (fun varied : CoverLorentzOneJet =>
      coverLorentzGramComponentBilinear first second varied varied)
    (coverLorentzGramComponentLinearization first second jet) jet
  have h := (coverLorentzGramComponentBilinear first second).hasFDerivAt_of_bilinear
    (hasFDerivAt_id jet) (hasFDerivAt_id jet)
  simpa only [coverLorentzGramComponentLinearization, id_eq] using h

theorem coverLorentzGramCompatibilityComponent_fderiv
    (first second : CoverCoordinates) (jet : CoverLorentzOneJet) :
    fderiv Real (coverLorentzGramCompatibilityComponent first second) jet =
      coverLorentzGramComponentLinearization first second jet :=
  (coverLorentzGramCompatibilityComponent_hasFDerivAt first second jet).fderiv

/-- At the true manifold immersion derivative, the coordinate `K` evaluates
to the existing intrinsic Lorentz tensor on the corresponding tangent
vectors. -/
theorem coverLorentzGramCompatibility_actualDerivative_apply
    (point : EffectiveCover period hPeriod) (first second : CoverCoordinates) :
    coverLorentzGramCompatibilityComponent first second
        (coverAmbientDerivativeCoordinates period hPeriod point) =
      intrinsicCoverLorentzTensor period hPeriod point
        ((trivializationAt CoverCoordinates
          (CoverIntrinsicTangent period hPeriod) point).symmL Real point first)
        ((trivializationAt CoverCoordinates
          (CoverIntrinsicTangent period hPeriod) point).symmL Real point second) := by
  rw [intrinsicCoverLorentzTensor_apply]
  change coverAmbientLorentzPair
      (coverAmbientDerivativeCoordinates period hPeriod point first)
      (coverAmbientDerivativeCoordinates period hPeriod point second) = _
  simp only [coverAmbientDerivativeCoordinates,
    coverAmbientLorentzPair_apply]
  rfl

end

end P0EFTJanusMappingTorusCoverLorentzGramFrechet4D
end JanusFormal
