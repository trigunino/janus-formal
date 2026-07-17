import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusIsSmoothEmbedding
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusSmoothNormalVectorBundle
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicCanonicalLatitudeNormalLorentz4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D

/-!
# Global algebraic normal equivalence for the effective D8 throat

Mathlib currently has no normal-vector-bundle construction attached to a
`Manifold.IsSmoothEmbedding`.  In particular, the differential normal
quotients form a dependent family, but their total space has no independently
constructed bundle topology or smooth atlas.

This gate uses the explicit unit latitude normal to normalize every fiber
equivalence, packages them as one base-preserving equivalence of dependent
total spaces, and proves exact fiberwise linearity.  The following gate uses
this geometric equivalence to transport the sign-clutched bundle topology.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGlobalNormalEquivalence

set_option autoImplicit false

noncomputable section

open Set Topology Bundle Module
open scoped Manifold ContDiff RealInnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusMappingTorusIsSmoothEmbedding
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusIntrinsicCoverLorentzTensor4D
open P0EFTJanusMappingTorusIntrinsicLorentzMetricDescent4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionAlgebraic4D
open P0EFTJanusMappingTorusIntrinsicCanonicalLatitudeNormalLorentz4D

variable (period : ℝ) (hPeriod : period ≠ 0)

private abbrev ThroatBase :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveCover := MappingTorusCover (sphereData period hPeriod)
private abbrev EffectiveThroatCover :=
  MappingTorusCover (throatData period hPeriod)
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

private local instance throatBaseChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

private local instance ambientBaseChartedSpace :
    ChartedSpace CoverModel
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  reflectedSphereQuotientChartedSpace period hPeriod

private local instance effectiveCoverChartedSpace :
    ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod

private local instance effectiveCoverIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveCover period hPeriod) :=
  reflectedSphereCover_isManifold period hPeriod

private local instance throatCoverChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroatCover period hPeriod) :=
  fixedThroatCoverChartedSpace period hPeriod

private local instance throatCoverIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroatCover period hPeriod) :=
  fixedThroatCover_isManifold period hPeriod

private local instance throatBaseIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (ThroatBase period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

private local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- The actual differential normal quotient of the smooth throat embedding at
one base point. -/
abbrev DifferentialNormalFiber (point : ThroatBase period hPeriod) :=
  HasQuotient.Quotient
    (TangentSpace coverModelWithCorners
      (fixedThroatQuotientInclusion period hPeriod point))
    (LinearMap.range
      (mfderiv throatCoverModelWithCorners coverModelWithCorners
        (fixedThroatQuotientInclusion period hPeriod) point).toLinearMap)

/-- The range being quotiented is closed.  Consequently each differential
normal quotient carries its genuine Hausdorff normed-space topology. -/
theorem differentialNormalRange_isClosed
    (point : ThroatBase period hPeriod) :
    IsClosed
      (LinearMap.range
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatQuotientInclusion period hPeriod) point).toLinearMap :
        Set (TangentSpace coverModelWithCorners
          (fixedThroatQuotientInclusion period hPeriod point))) := by
  let targetTangent := TangentSpace coverModelWithCorners
    (fixedThroatQuotientInclusion period hPeriod point)
  let targetEquiv : targetTangent ≃L[ℝ] CoverCoordinates :=
    ContinuousLinearEquiv.refl ℝ CoverCoordinates
  letI : FiniteDimensional ℝ targetTangent :=
    targetEquiv.toLinearEquiv.symm.finiteDimensional
  letI : T2Space targetTangent := by
    change T2Space CoverCoordinates
    infer_instance
  exact (LinearMap.range
    (mfderiv throatCoverModelWithCorners coverModelWithCorners
      (fixedThroatQuotientInclusion period hPeriod) point).toLinearMap)
    |>.closed_of_finiteDimensional

/-- The differential normal fiber has the expected real rank one. -/
theorem differentialNormalFiber_finrank
    (point : ThroatBase period hPeriod) :
    Module.finrank ℝ (DifferentialNormalFiber period hPeriod point) = 1 :=
  mfderiv_fixedThroatQuotientInclusion_normal_finrank period hPeriod point

private abbrev throatPoint
    (anchor : EffectiveThroatCover period hPeriod) :
    ThroatBase period hPeriod :=
  mappingTorusMk (throatData period hPeriod) anchor

private abbrev ThroatTangent (point : ThroatBase period hPeriod) :=
  TangentSpace throatCoverModelWithCorners point

private abbrev AmbientTangent (point : ThroatBase period hPeriod) :=
  TangentSpace coverModelWithCorners
    (fixedThroatQuotientInclusion period hPeriod point)

private abbrev TangentialRange (point : ThroatBase period hPeriod) :
    Submodule Real (AmbientTangent period hPeriod point) :=
  LinearMap.range
    (mfderiv throatCoverModelWithCorners coverModelWithCorners
      (fixedThroatQuotientInclusion period hPeriod) point).toLinearMap

private local instance ambientTangentFiniteDimensional
    (point : ThroatBase period hPeriod) :
    FiniteDimensional Real (AmbientTangent period hPeriod point) :=
  let targetEquiv : AmbientTangent period hPeriod point ≃L[Real]
      CoverCoordinates := ContinuousLinearEquiv.refl Real CoverCoordinates
  targetEquiv.toLinearEquiv.symm.finiteDimensional

/-- The explicit unit latitude normal pushed to the quotient tangent fiber. -/
def canonicalDifferentialLatitudeNormal
    (anchor : EffectiveThroatCover period hPeriod) :
    AmbientTangent period hPeriod (throatPoint period hPeriod anchor) := by
  change TangentSpace coverModelWithCorners
    (fixedThroatQuotientInclusion period hPeriod
      (mappingTorusMk (throatData period hPeriod) anchor))
  rw [fixedThroatQuotientInclusion_mk]
  exact mfderiv coverModelWithCorners coverModelWithCorners
    (mappingTorusMk (sphereData period hPeriod))
    (fixedThroatCoverInclusion period hPeriod anchor)
    (coverLatitudeNormalVector period hPeriod anchor)

theorem canonicalDifferentialLatitudeNormal_square
    (anchor : EffectiveThroatCover period hPeriod) :
    (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor
        (fixedThroatQuotientInclusion period hPeriod
          (throatPoint period hPeriod anchor))
        (canonicalDifferentialLatitudeNormal period hPeriod anchor)
        (canonicalDifferentialLatitudeNormal period hPeriod anchor) = 1 := by
  rw [show fixedThroatQuotientInclusion period hPeriod
      (throatPoint period hPeriod anchor) =
      mappingTorusMk (sphereData period hPeriod)
        (fixedThroatCoverInclusion period hPeriod anchor) by
    exact fixedThroatQuotientInclusion_mk period hPeriod anchor]
  unfold canonicalDifferentialLatitudeNormal
  change
    (intrinsicTensorQuotientDescent period hPeriod).tensor
        (mappingTorusMk (sphereData period hPeriod)
          (fixedThroatCoverInclusion period hPeriod anchor))
        (mfderiv coverModelWithCorners coverModelWithCorners
          (mappingTorusMk (sphereData period hPeriod))
          (fixedThroatCoverInclusion period hPeriod anchor)
          (coverLatitudeNormalVector period hPeriod anchor))
        (mfderiv coverModelWithCorners coverModelWithCorners
          (mappingTorusMk (sphereData period hPeriod))
          (fixedThroatCoverInclusion period hPeriod anchor)
          (coverLatitudeNormalVector period hPeriod anchor)) = 1
  rw [(intrinsicTensorQuotientDescent period hPeriod).pullback]
  exact intrinsicCoverLorentzTensor_latitudeNormal_square
    period hPeriod anchor

theorem canonicalDifferentialLatitudeNormal_orthogonal
    (anchor : EffectiveThroatCover period hPeriod)
    (tangent : ThroatTangent period hPeriod
      (throatPoint period hPeriod anchor)) :
    (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor
        (fixedThroatQuotientInclusion period hPeriod
          (throatPoint period hPeriod anchor))
        (canonicalDifferentialLatitudeNormal period hPeriod anchor)
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatQuotientInclusion period hPeriod)
          (throatPoint period hPeriod anchor) tangent) = 0 := by
  let sourceDerivative :=
    (fixedThroat_projection_isLocalDiffeomorph period hPeriod)
      |>.mfderivToContinuousLinearEquiv (by simp) anchor
  obtain ⟨coverTangent, hCoverTangent⟩ := sourceDerivative.surjective tangent
  have hSourceAt : MDifferentiableAt throatCoverModelWithCorners
      throatCoverModelWithCorners
      (mappingTorusMk (throatData period hPeriod)) anchor :=
    (fixedThroat_projection_isLocalDiffeomorph period hPeriod).contMDiff
      |>.mdifferentiableAt (by simp)
  have hTargetAt : MDifferentiableAt coverModelWithCorners
      coverModelWithCorners
      (mappingTorusMk (sphereData period hPeriod))
      (fixedThroatCoverInclusion period hPeriod anchor) :=
    (reflectedSphere_projection_isLocalDiffeomorph period hPeriod).contMDiff
      |>.mdifferentiableAt (by simp)
  have hCoverAt : MDifferentiableAt throatCoverModelWithCorners
      coverModelWithCorners (fixedThroatCoverInclusion period hPeriod) anchor :=
    (fixedThroatCoverInclusion_contMDiff period hPeriod).mdifferentiableAt
      (by simp)
  have hQuotientAt : MDifferentiableAt throatCoverModelWithCorners
      coverModelWithCorners (fixedThroatQuotientInclusion period hPeriod)
      (throatPoint period hPeriod anchor) :=
    (fixedThroatQuotientInclusion_contMDiff period hPeriod).mdifferentiableAt
      (by simp)
  have hDerivative :
      (mfderiv coverModelWithCorners coverModelWithCorners
          (mappingTorusMk (sphereData period hPeriod))
          (fixedThroatCoverInclusion period hPeriod anchor)).comp
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatCoverInclusion period hPeriod) anchor) =
      (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatQuotientInclusion period hPeriod)
          (throatPoint period hPeriod anchor)).comp
        (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
          (mappingTorusMk (throatData period hPeriod)) anchor) := by
    rw [← mfderiv_comp anchor hTargetAt hCoverAt,
      ← mfderiv_comp anchor hQuotientAt hSourceAt]
    rfl
  have hSourceDerivative :
      mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
          (mappingTorusMk (throatData period hPeriod)) anchor coverTangent =
        tangent := by
    rw [← (fixedThroat_projection_isLocalDiffeomorph period hPeriod)
      |>.mfderivToContinuousLinearEquiv_coe (by simp)]
    exact hCoverTangent
  have hNaturality := congrArg (fun derivative => derivative coverTangent)
    hDerivative
  have hNaturality' :
      mfderiv coverModelWithCorners coverModelWithCorners
          (mappingTorusMk (sphereData period hPeriod))
          (fixedThroatCoverInclusion period hPeriod anchor)
          (mfderiv throatCoverModelWithCorners coverModelWithCorners
            (fixedThroatCoverInclusion period hPeriod) anchor coverTangent) =
        mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatQuotientInclusion period hPeriod)
          (throatPoint period hPeriod anchor)
          (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
            (mappingTorusMk (throatData period hPeriod)) anchor coverTangent) := by
    change
      mfderiv coverModelWithCorners coverModelWithCorners
          (mappingTorusMk (sphereData period hPeriod))
          (fixedThroatCoverInclusion period hPeriod anchor)
          (mfderiv throatCoverModelWithCorners coverModelWithCorners
            (fixedThroatCoverInclusion period hPeriod) anchor coverTangent) =
        mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatQuotientInclusion period hPeriod)
          (throatPoint period hPeriod anchor)
          (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
            (mappingTorusMk (throatData period hPeriod)) anchor coverTangent)
      at hNaturality
    exact hNaturality
  rw [← hSourceDerivative, ← hNaturality']
  rw [show fixedThroatQuotientInclusion period hPeriod
      (throatPoint period hPeriod anchor) =
      mappingTorusMk (sphereData period hPeriod)
        (fixedThroatCoverInclusion period hPeriod anchor) by
    exact fixedThroatQuotientInclusion_mk period hPeriod anchor]
  unfold canonicalDifferentialLatitudeNormal
  change
    (intrinsicTensorQuotientDescent period hPeriod).tensor
        (mappingTorusMk (sphereData period hPeriod)
          (fixedThroatCoverInclusion period hPeriod anchor))
        (mfderiv coverModelWithCorners coverModelWithCorners
          (mappingTorusMk (sphereData period hPeriod))
          (fixedThroatCoverInclusion period hPeriod anchor)
          (coverLatitudeNormalVector period hPeriod anchor))
        (mfderiv coverModelWithCorners coverModelWithCorners
          (mappingTorusMk (sphereData period hPeriod))
          (fixedThroatCoverInclusion period hPeriod anchor)
          (mfderiv throatCoverModelWithCorners coverModelWithCorners
            (fixedThroatCoverInclusion period hPeriod) anchor coverTangent)) = 0
  rw [(intrinsicTensorQuotientDescent period hPeriod).pullback]
  exact intrinsicCoverLorentzTensor_latitudeNormal_orthogonal
    period hPeriod anchor coverTangent

def canonicalDifferentialLatitudeNormalClass
    (anchor : EffectiveThroatCover period hPeriod) :
    DifferentialNormalFiber period hPeriod
      (throatPoint period hPeriod anchor) :=
  (TangentialRange period hPeriod (throatPoint period hPeriod anchor)).mkQ
    (canonicalDifferentialLatitudeNormal period hPeriod anchor)

theorem canonicalDifferentialLatitudeNormalClass_ne_zero
    (anchor : EffectiveThroatCover period hPeriod) :
    canonicalDifferentialLatitudeNormalClass period hPeriod anchor ≠ 0 := by
  intro hZero
  have hMem : canonicalDifferentialLatitudeNormal period hPeriod anchor ∈
      TangentialRange period hPeriod (throatPoint period hPeriod anchor) := by
    exact (Submodule.Quotient.mk_eq_zero _).mp (by simpa
      [canonicalDifferentialLatitudeNormalClass] using hZero)
  rcases hMem with ⟨tangent, hTangent⟩
  have hSquare := canonicalDifferentialLatitudeNormal_square
    period hPeriod anchor
  have hOrthogonal := canonicalDifferentialLatitudeNormal_orthogonal
    period hPeriod anchor tangent
  have hMetricZero :
      (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor
          (fixedThroatQuotientInclusion period hPeriod
            (throatPoint period hPeriod anchor))
          (canonicalDifferentialLatitudeNormal period hPeriod anchor)
          (canonicalDifferentialLatitudeNormal period hPeriod anchor) = 0 := by
    calc
      _ = (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor
          (fixedThroatQuotientInclusion period hPeriod
            (throatPoint period hPeriod anchor))
          (canonicalDifferentialLatitudeNormal period hPeriod anchor)
          (mfderiv throatCoverModelWithCorners coverModelWithCorners
            (fixedThroatQuotientInclusion period hPeriod)
            (throatPoint period hPeriod anchor) tangent) :=
        congrArg
          ((intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor
            (fixedThroatQuotientInclusion period hPeriod
              (throatPoint period hPeriod anchor))
            (canonicalDifferentialLatitudeNormal period hPeriod anchor))
          hTangent.symm
      _ = 0 := hOrthogonal
  linarith

def canonicalDifferentialNormalClassMap
    (anchor : EffectiveThroatCover period hPeriod) :
    Real →ₗ[Real] DifferentialNormalFiber period hPeriod
      (throatPoint period hPeriod anchor) :=
  LinearMap.toSpanSingleton Real _
    (canonicalDifferentialLatitudeNormalClass period hPeriod anchor)

theorem canonicalDifferentialNormalClassMap_bijective
    (anchor : EffectiveThroatCover period hPeriod) :
    Function.Bijective
      (canonicalDifferentialNormalClassMap period hPeriod anchor) := by
  have hInjective : Function.Injective
      (canonicalDifferentialNormalClassMap period hPeriod anchor) := by
    apply LinearMap.ker_eq_bot.mp
    exact LinearMap.ker_toSpanSingleton Real
      (canonicalDifferentialLatitudeNormalClass_ne_zero
        period hPeriod anchor)
  have hRank : Module.finrank Real Real = Module.finrank Real
      (DifferentialNormalFiber period hPeriod
        (throatPoint period hPeriod anchor)) := by
    rw [differentialNormalFiber_finrank]
    simp
  exact ⟨hInjective,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hRank).mp
      hInjective⟩

def canonicalDifferentialNormalClassEquiv
    (anchor : EffectiveThroatCover period hPeriod) :
    Real ≃ₗ[Real] DifferentialNormalFiber period hPeriod
      (throatPoint period hPeriod anchor) :=
  LinearEquiv.ofBijective
    (canonicalDifferentialNormalClassMap period hPeriod anchor)
    (canonicalDifferentialNormalClassMap_bijective period hPeriod anchor)

def differentialNormalFiberTransport
    {first second : ThroatBase period hPeriod} (h : first = second) :
    DifferentialNormalFiber period hPeriod first ≃ₗ[Real]
      DifferentialNormalFiber period hPeriod second := by
  subst second
  exact LinearEquiv.refl Real _

/-- The preferred cover lift and the unit latitude generator define the
fiber equivalence.  Its normalization is geometric rather than an arbitrary
pointwise choice. -/
noncomputable def differentialNormalFiberEquiv
    (point : ThroatBase period hPeriod) :
    FixedThroatNormalFiber period hPeriod point ≃ₗ[ℝ]
      DifferentialNormalFiber period hPeriod point := by
  let anchor := normalBundleIndexAt period hPeriod point
  have hPoint := normalBundleIndexAt_projects period hPeriod point
  exact (canonicalDifferentialNormalClassEquiv period hPeriod anchor).trans
    (differentialNormalFiberTransport period hPeriod hPoint)

theorem differentialNormalFiberEquiv_apply
    (point : ThroatBase period hPeriod)
    (normal : FixedThroatNormalFiber period hPeriod point) :
    differentialNormalFiberEquiv period hPeriod point normal =
      differentialNormalFiberTransport period hPeriod
        (normalBundleIndexAt_projects period hPeriod point)
        (canonicalDifferentialNormalClassEquiv period hPeriod
          (normalBundleIndexAt period hPeriod point) normal) :=
  rfl

/-- At each fixed point the algebraic comparison is automatically a
continuous linear equivalence, since both sides are finite-dimensional real
spaces.  This is still pointwise continuity, not smooth dependence on the
base. -/
theorem differentialNormalFiber_continuousEquiv
    (point : ThroatBase period hPeriod) :
    Nonempty
      (FixedThroatNormalFiber period hPeriod point ≃L[ℝ]
        DifferentialNormalFiber period hPeriod point) := by
  let targetTangent := TangentSpace coverModelWithCorners
    (fixedThroatQuotientInclusion period hPeriod point)
  let targetEquiv : targetTangent ≃L[ℝ] CoverCoordinates :=
    ContinuousLinearEquiv.refl ℝ CoverCoordinates
  letI : FiniteDimensional ℝ targetTangent :=
    targetEquiv.toLinearEquiv.symm.finiteDimensional
  letI : T2Space targetTangent := by
    change T2Space CoverCoordinates
    infer_instance
  letI : IsTopologicalAddGroup targetTangent := by
    change IsTopologicalAddGroup CoverCoordinates
    infer_instance
  letI : ContinuousSMul ℝ targetTangent := by
    change ContinuousSMul ℝ CoverCoordinates
    infer_instance
  let derivative :=
    (mfderiv throatCoverModelWithCorners coverModelWithCorners
      (fixedThroatQuotientInclusion period hPeriod) point).toLinearMap
  letI : IsClosed (LinearMap.range derivative : Set targetTangent) :=
    (LinearMap.range derivative).closed_of_finiteDimensional
  letI : FiniteDimensional ℝ
      (FixedThroatNormalFiber period hPeriod point) := by
    change FiniteDimensional ℝ ℝ
    infer_instance
  letI : IsTopologicalAddGroup
      (FixedThroatNormalFiber period hPeriod point) := by
    change IsTopologicalAddGroup ℝ
    infer_instance
  letI : ContinuousSMul ℝ
      (FixedThroatNormalFiber period hPeriod point) := by
    change ContinuousSMul ℝ ℝ
    infer_instance
  letI : T2Space (FixedThroatNormalFiber period hPeriod point) := by
    change T2Space ℝ
    infer_instance
  exact ⟨(differentialNormalFiberEquiv period hPeriod point)
    |>.toContinuousLinearEquiv⟩

/-- The global algebraic comparison transports the proved analytic one-loop
transition to multiplication by `-1` in the actual differential quotient.
This is the exact cocycle that an independently constructed smooth quotient
atlas must recover. -/
theorem differentialNormalFiberEquiv_oneLoop
    (anchor : MappingTorusCover (fixedEquatorData period hPeriod))
    (normal : ℝ) :
    let base := mappingTorusMk (fixedEquatorData period hPeriod) anchor
    differentialNormalFiberEquiv period hPeriod base
        ((fixedThroatNormalVectorBundleCore period hPeriod).coordChange
          anchor ((1 : ℤ) +ᵥ anchor) base normal) =
      -differentialNormalFiberEquiv period hPeriod base normal := by
  dsimp only
  rw [one_loop_coordChange_eq_neg_id]
  exact map_neg (differentialNormalFiberEquiv period hPeriod _) normal

@[simp] theorem differentialNormalFiberEquiv_apply_symm_apply
    (point : ThroatBase period hPeriod)
    (normal : DifferentialNormalFiber period hPeriod point) :
    differentialNormalFiberEquiv period hPeriod point
        ((differentialNormalFiberEquiv period hPeriod point).symm normal) =
      normal :=
  (differentialNormalFiberEquiv period hPeriod point).apply_symm_apply normal

@[simp] theorem differentialNormalFiberEquiv_symm_apply_apply
    (point : ThroatBase period hPeriod)
    (normal : FixedThroatNormalFiber period hPeriod point) :
    (differentialNormalFiberEquiv period hPeriod point).symm
        (differentialNormalFiberEquiv period hPeriod point normal) = normal :=
  (differentialNormalFiberEquiv period hPeriod point).symm_apply_apply normal

/-- The total space of the differential normal family.  This is intentionally
only a sigma type: a smooth bundle topology is the remaining frontier. -/
abbrev DifferentialNormalTotalSpace :=
  Bundle.TotalSpace ℝ (DifferentialNormalFiber period hPeriod)

/-- The analytic sign-clutched normal line and the differential normal family
are globally equivalent as dependent, fiberwise-linear families. -/
noncomputable def differentialNormalTotalEquiv :
    Bundle.TotalSpace ℝ (FixedThroatNormalFiber period hPeriod) ≃
      DifferentialNormalTotalSpace period hPeriod where
  toFun normal :=
    ⟨normal.1, differentialNormalFiberEquiv period hPeriod normal.1 normal.2⟩
  invFun normal :=
    ⟨normal.1, (differentialNormalFiberEquiv period hPeriod normal.1).symm normal.2⟩
  left_inv normal := by
    cases normal
    simp
  right_inv normal := by
    cases normal
    simp

@[simp] theorem differentialNormalTotalEquiv_base
    (normal : Bundle.TotalSpace ℝ
      (FixedThroatNormalFiber period hPeriod)) :
    (differentialNormalTotalEquiv period hPeriod normal).1 = normal.1 :=
  rfl

@[simp] theorem differentialNormalTotalEquiv_fiber
    (point : ThroatBase period hPeriod)
    (normal : FixedThroatNormalFiber period hPeriod point) :
    (differentialNormalTotalEquiv period hPeriod ⟨point, normal⟩).2 =
      differentialNormalFiberEquiv period hPeriod point normal :=
  rfl

@[simp] theorem differentialNormalTotalEquiv_zero
    (point : ThroatBase period hPeriod) :
    differentialNormalTotalEquiv period hPeriod
        (⟨point, 0⟩ : Bundle.TotalSpace ℝ
          (FixedThroatNormalFiber period hPeriod)) =
      (⟨point, 0⟩ : DifferentialNormalTotalSpace period hPeriod) := by
  ext <;> simp [differentialNormalTotalEquiv]

theorem differentialNormalTotalEquiv_add
    (point : ThroatBase period hPeriod)
    (first second : FixedThroatNormalFiber period hPeriod point) :
    differentialNormalTotalEquiv period hPeriod ⟨point, first + second⟩ =
      ⟨point,
        differentialNormalFiberEquiv period hPeriod point first +
          differentialNormalFiberEquiv period hPeriod point second⟩ := by
  ext <;> simp [differentialNormalTotalEquiv]

theorem differentialNormalTotalEquiv_smul
    (point : ThroatBase period hPeriod) (scalar : ℝ)
    (normal : FixedThroatNormalFiber period hPeriod point) :
    differentialNormalTotalEquiv period hPeriod ⟨point, scalar • normal⟩ =
      ⟨point, scalar •
        differentialNormalFiberEquiv period hPeriod point normal⟩ := by
  ext <;> simp [differentialNormalTotalEquiv]

/-- Exact non-smooth closure reached here: one global total-space equivalence,
base preservation, and linearity on every fiber. -/
theorem differentialNormalGlobalAlgebraicClosure :
    Nonempty
        (Bundle.TotalSpace ℝ (FixedThroatNormalFiber period hPeriod) ≃
          DifferentialNormalTotalSpace period hPeriod) ∧
      (∀ normal : Bundle.TotalSpace ℝ
          (FixedThroatNormalFiber period hPeriod),
        (differentialNormalTotalEquiv period hPeriod normal).1 = normal.1) ∧
      (∀ point (first second : FixedThroatNormalFiber period hPeriod point),
        differentialNormalTotalEquiv period hPeriod ⟨point, first + second⟩ =
          ⟨point,
            differentialNormalFiberEquiv period hPeriod point first +
              differentialNormalFiberEquiv period hPeriod point second⟩) ∧
      ∀ point (scalar : ℝ)
          (normal : FixedThroatNormalFiber period hPeriod point),
        differentialNormalTotalEquiv period hPeriod ⟨point, scalar • normal⟩ =
          ⟨point, scalar •
            differentialNormalFiberEquiv period hPeriod point normal⟩ := by
  exact ⟨⟨differentialNormalTotalEquiv period hPeriod⟩,
    differentialNormalTotalEquiv_base period hPeriod,
    differentialNormalTotalEquiv_add period hPeriod,
    differentialNormalTotalEquiv_smul period hPeriod⟩

end

end P0EFTJanusMappingTorusGlobalNormalEquivalence
end JanusFormal
