import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06ThroatSignedVectorPullbackPiola4D

namespace JanusFormal
namespace P0EFTJanusProgramPT06ThroatAbsoluteVectorPullbackPiola4D

set_option autoImplicit false
noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPT06ThroatSpatialMultiindexSecondJetBridge4D
open P0EFTJanusProgramPT06ThroatSignedDifferentialFormPiola4D
open P0EFTJanusProgramPT06ThroatSignedVectorPullbackPiola4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionGerm4D
open P0EFTJanusProgramPActualThroatGaugeBaseChartTransitionJacobianEquiv4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetTransitionSmoothRegularity4D
open P0EFTJanusProgramPT06ActualPhysicalThirdJetVectorDensityJointRegularity4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

/-- Absolute vector-density pullback through a pair of coordinate maps. -/
def programPT06ThroatAbsoluteVectorPullback
    (forward reverse field :
      ThroatCoverCoordinates → ThroatCoverCoordinates) :
    ThroatCoverCoordinates → ThroatCoverCoordinates :=
  fun coordinate =>
    |LinearMap.det (fderiv Real forward coordinate).toLinearMap| •
      fderiv Real reverse (forward coordinate) (field (forward coordinate))

/-- Coordinate divergence depends only on the germ of a vector field. -/
theorem programPT06ThroatCoordinateDivergence_congr
    {first second : ThroatCoverCoordinates → ThroatCoverCoordinates}
    {coordinate : ThroatCoverCoordinates}
    (hFields : first =ᶠ[nhds coordinate] second) :
    programPT06ThroatCoordinateDivergence first coordinate =
      programPT06ThroatCoordinateDivergence second coordinate := by
  unfold programPT06ThroatCoordinateDivergence
  rw [hFields.fderiv_eq]

/-- Coordinate divergence changes sign under pointwise negation. -/
theorem programPT06ThroatCoordinateDivergence_neg
    (field : ThroatCoverCoordinates → ThroatCoverCoordinates)
    (coordinate : ThroatCoverCoordinates) :
    programPT06ThroatCoordinateDivergence (fun nearby => -field nearby) coordinate =
      -programPT06ThroatCoordinateDivergence field coordinate := by
  simp [programPT06ThroatCoordinateDivergence, fderiv_fun_neg]

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev Base :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (Base period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω (Base period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- The abstract absolute pullback is the existing actual Jacobian-density
and inverse-Jacobian expression. -/
@[simp] theorem programPT06ActualThroatAbsoluteVectorPullback_apply
    (firstCenter secondCenter : Base period hPeriod)
    (field : ThroatCoverCoordinates → ThroatCoverCoordinates)
    (coordinate : ThroatCoverCoordinates) :
    programPT06ThroatAbsoluteVectorPullback
        (throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter)
        (throatGaugeBaseChartTransition period hPeriod secondCenter firstCenter)
        field coordinate =
      programPT06ActualThroatBaseJacobianDensityInCoordinates period hPeriod
          firstCenter secondCenter coordinate •
        programPT06ActualThroatBaseInverseJacobianInCoordinates period hPeriod
          firstCenter secondCenter coordinate
          (field (throatGaugeBaseChartTransition period hPeriod
            firstCenter secondCenter coordinate)) := by
  rfl

/-- The determinant of an actual transition Jacobian has a constant strict
sign in a neighborhood of every genuine overlap point. -/
theorem programPT06ActualThroatJacobianDeterminant_sign_eventually
    (firstCenter secondCenter current : Base period hPeriod)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source) :
    let forward :=
      throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter
    let coordinate := extChartAt throatCoverModelWithCorners firstCenter current
    let determinant := fun nearby =>
      LinearMap.det (fderiv Real forward nearby).toLinearMap
    (0 < determinant coordinate ∧
        ∀ᶠ nearby in nhds coordinate, 0 < determinant nearby) ∨
      (determinant coordinate < 0 ∧
        ∀ᶠ nearby in nhds coordinate, determinant nearby < 0) := by
  dsimp only
  let forward :=
    throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter
  let coordinate := extChartAt throatCoverModelWithCorners firstCenter current
  let determinant := fun nearby =>
    LinearMap.det (fderiv Real forward nearby).toLinearMap
  have hJacobian : ContDiffAt Real ∞ (fderiv Real forward) coordinate :=
    throatGaugeBaseChartTransition_fderiv_contDiffAt_infty period hPeriod
      firstCenter secondCenter current hFirst hSecond
  have hDeterminant : ContinuousAt determinant coordinate :=
    (programPT06ThroatEndomorphismDeterminant_contDiff.contDiffAt.comp
      coordinate hJacobian).continuousAt
  have hNonzero : determinant coordinate ≠ 0 := by
    dsimp only [determinant, forward, coordinate]
    rw [← throatGaugeBaseChartTransitionJacobianEquivAt_toLinearMap
      period hPeriod firstCenter secondCenter current hFirst hSecond]
    rw [← LinearEquiv.coe_det]
    exact Units.ne_zero _
  rcases hNonzero.lt_or_gt with hNegative | hPositive
  · exact Or.inr
      ⟨hNegative, hDeterminant.eventually (gt_mem_nhds hNegative)⟩
  · exact Or.inl
      ⟨hPositive, hDeterminant.eventually (lt_mem_nhds hPositive)⟩

/-- Absolute Piola transformation of coordinate divergence at a genuine
overlap point. -/
theorem programPT06ActualThroatAbsoluteVectorPullback_divergence_eq_abs_det_mul
    (firstCenter secondCenter current : Base period hPeriod)
    (hFirst : current ∈
      (extChartAt throatCoverModelWithCorners firstCenter).source)
    (hSecond : current ∈
      (extChartAt throatCoverModelWithCorners secondCenter).source)
    (field : ThroatCoverCoordinates → ThroatCoverCoordinates)
    (hField : DifferentiableAt Real field
      (extChartAt throatCoverModelWithCorners secondCenter current)) :
    programPT06ThroatCoordinateDivergence
        (programPT06ThroatAbsoluteVectorPullback
          (throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter)
          (throatGaugeBaseChartTransition period hPeriod secondCenter firstCenter)
          field)
        (extChartAt throatCoverModelWithCorners firstCenter current) =
      |LinearMap.det
          (fderiv Real
            (throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter)
            (extChartAt throatCoverModelWithCorners firstCenter current)).toLinearMap| *
        programPT06ThroatCoordinateDivergence field
          (extChartAt throatCoverModelWithCorners secondCenter current) := by
  rcases programPT06ActualThroatJacobianDeterminant_sign_eventually
      period hPeriod firstCenter secondCenter current hFirst hSecond with
    ⟨hPositive, hEventuallyPositive⟩ | ⟨hNegative, hEventuallyNegative⟩
  · have hPullback :
        programPT06ThroatAbsoluteVectorPullback
            (throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter)
            (throatGaugeBaseChartTransition period hPeriod secondCenter firstCenter)
            field =ᶠ[nhds
              (extChartAt throatCoverModelWithCorners firstCenter current)]
          programPT06ThroatSignedVectorPullback
            (throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter)
            (throatGaugeBaseChartTransition period hPeriod secondCenter firstCenter)
            field :=
      hEventuallyPositive.mono fun nearby hNearby => by
        unfold programPT06ThroatAbsoluteVectorPullback
          programPT06ThroatSignedVectorPullback
        rw [abs_eq_self.mpr hNearby.le]
    calc
      _ = programPT06ThroatCoordinateDivergence
          (programPT06ThroatSignedVectorPullback
            (throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter)
            (throatGaugeBaseChartTransition period hPeriod secondCenter firstCenter)
            field)
          (extChartAt throatCoverModelWithCorners firstCenter current) :=
        programPT06ThroatCoordinateDivergence_congr hPullback
      _ = LinearMap.det
          (fderiv Real
            (throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter)
            (extChartAt throatCoverModelWithCorners firstCenter current)).toLinearMap *
          programPT06ThroatCoordinateDivergence field
            (extChartAt throatCoverModelWithCorners secondCenter current) :=
        programPT06ActualThroatSignedVectorPullback_divergence_eq_det_mul
          period hPeriod firstCenter secondCenter current hFirst hSecond field hField
      _ = _ := by rw [abs_eq_self.mpr hPositive.le]
  · have hPullback :
        programPT06ThroatAbsoluteVectorPullback
            (throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter)
            (throatGaugeBaseChartTransition period hPeriod secondCenter firstCenter)
            field =ᶠ[nhds
              (extChartAt throatCoverModelWithCorners firstCenter current)]
          fun nearby =>
            -programPT06ThroatSignedVectorPullback
              (throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter)
              (throatGaugeBaseChartTransition period hPeriod secondCenter firstCenter)
              field nearby :=
      hEventuallyNegative.mono fun nearby hNearby => by
        unfold programPT06ThroatAbsoluteVectorPullback
          programPT06ThroatSignedVectorPullback
        rw [abs_eq_neg_self.mpr hNearby.le, neg_smul]
    calc
      _ = programPT06ThroatCoordinateDivergence
          (fun nearby =>
            -programPT06ThroatSignedVectorPullback
              (throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter)
              (throatGaugeBaseChartTransition period hPeriod secondCenter firstCenter)
              field nearby)
          (extChartAt throatCoverModelWithCorners firstCenter current) :=
        programPT06ThroatCoordinateDivergence_congr hPullback
      _ = -programPT06ThroatCoordinateDivergence
          (programPT06ThroatSignedVectorPullback
            (throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter)
            (throatGaugeBaseChartTransition period hPeriod secondCenter firstCenter)
            field)
          (extChartAt throatCoverModelWithCorners firstCenter current) :=
        programPT06ThroatCoordinateDivergence_neg _ _
      _ = -(LinearMap.det
          (fderiv Real
            (throatGaugeBaseChartTransition period hPeriod firstCenter secondCenter)
            (extChartAt throatCoverModelWithCorners firstCenter current)).toLinearMap *
          programPT06ThroatCoordinateDivergence field
            (extChartAt throatCoverModelWithCorners secondCenter current)) := by
        rw [programPT06ActualThroatSignedVectorPullback_divergence_eq_det_mul
          period hPeriod firstCenter secondCenter current hFirst hSecond field hField]
      _ = _ := by
        rw [abs_eq_neg_self.mpr hNegative.le]
        ring

end
end P0EFTJanusProgramPT06ThroatAbsoluteVectorPullbackPiola4D
end JanusFormal
