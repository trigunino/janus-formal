import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracDescent4D

/-!
# Differential equation for the primitive SpinC Hopf zero mode

This gate computes the intrinsic-frame derivatives of the polar throat
coordinates and uses them to identify the complete Hopf section as an
eigenspinor of the coupled geometric Dirac operator.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeDiracEquation4D

set_option autoImplicit false
noncomputable section

open Set
open scoped BigOperators Manifold ContDiff RealInnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusD8NonabelianGhostThroatBRST4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusProgramPAmbientHalfSpinorD9Bridge4D
open P0EFTJanusProgramPD9MatterSpinorDoubledCliffordConnectionCompatibility4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothSectionDescent4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9MatterSpinorDoubledIntrinsicDiracOperator4D
open P0EFTJanusProgramPD9MatterSpinorLeviCivitaConnection4D
open P0EFTJanusProgramPD9MatterSpinorSmoothSectionDescent4D
open P0EFTJanusProgramPD9PrimitiveMonopoleCartesianConnection4D
open P0EFTJanusProgramPD9PrimitiveMonopolePhaseDerivative4D
open P0EFTJanusProgramPD9PrimitiveMonopolePullbackBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCConnection4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracDescent4D
open P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCLocalDiracGaugeCovariance4D
open P0EFTJanusProgramPD9PrimitiveSpinCLocalGeometricDirac4D
open P0EFTJanusProgramPD9PrimitiveSpinCNormalModeSection4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionDescent4D
open P0EFTJanusProgramPPrimitiveMonopoleClutchingConnection4D
open P0EFTJanusProgramPPrimitiveMonopoleZeroModeSection4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatCover := MappingTorusCover (ThroatData period hPeriod)
private abbrev ThroatBase := MappingTorus (ThroatData period hPeriod)
private abbrev throatProjectionLocalHomeomorph :
    IsLocalHomeomorph
      (mappingTorusMk (ThroatData period hPeriod)) :=
  (mappingTorusMk_isCoveringMap
    (ThroatData period hPeriod)).isLocalHomeomorph

local instance throatCoverChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatCover period hPeriod) :=
  fixedThroatCoverChartedSpace period hPeriod

local instance throatCoverIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (ThroatCover period hPeriod) :=
  fixedThroatCover_isManifold period hPeriod

local instance throatBaseChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance throatBaseIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (ThroatBase period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance euclideanR3Finrank :
    Fact (Module.finrank Real (EuclideanSpace Real (Fin 3)) = 2 + 1) :=
  ⟨by simp⟩

/-- The logarithmic radius differentiates to the unit radial coordinate on
the intrinsic Euclidean radial frame. -/
private theorem euclideanLogNorm_fderiv_radialFrame
    (direction : Fin 3) (point : EuclideanR3) (hPoint : point ≠ 0) :
    fderiv Real (fun current : EuclideanR3 => Real.log ‖current‖) point
        (‖point‖ • EuclideanSpace.basisFun (Fin 3) Real direction) =
      (EuclideanSpace.proj (𝕜 := Real) direction) point / ‖point‖ := by
  have hSq :
      HasFDerivAt (fun current : EuclideanR3 => ‖current‖ ^ 2)
        (2 • innerSL Real point) point :=
    (hasStrictFDerivAt_norm_sq point).hasFDerivAt
  have hNorm :=
    hSq.sqrt (pow_ne_zero 2 (norm_ne_zero_iff.mpr hPoint))
  simp only [Real.sqrt_sq (norm_nonneg _)] at hNorm
  have hLog :=
    (Real.hasDerivAt_log (norm_ne_zero_iff.mpr hPoint)).comp_hasFDerivAt
      point hNorm
  have hLogFderiv := DFunLike.congr_fun hLog.fderiv
    (‖point‖ • EuclideanSpace.basisFun (Fin 3) Real direction)
  change
    fderiv Real (fun current : EuclideanR3 => Real.log ‖current‖) point
        (‖point‖ • EuclideanSpace.basisFun (Fin 3) Real direction) =
      _ at hLogFderiv
  rw [hLogFderiv]
  simp only [smul_apply, two_nsmul, add_apply, innerSL_apply_apply,
    real_inner_smul_right, EuclideanSpace.inner_basisFun_real,
    smul_eq_mul]
  change
    ‖point‖⁻¹ *
        (1 / (2 * ‖point‖) *
          (‖point‖ * point.ofLp direction +
            ‖point‖ * point.ofLp direction)) =
      point.ofLp direction / ‖point‖
  field_simp [norm_ne_zero_iff.mpr hPoint]
  ring

/-- Euclidean representative of one unit radial coordinate. -/
private def euclideanUnitRadialCoordinate
    (coordinate : Fin 3) (point : EuclideanR3) : Real :=
  (EuclideanSpace.proj (𝕜 := Real) coordinate) point / ‖point‖

/-- Derivative of a unit radial coordinate in the scaled Cartesian frame. -/
private theorem euclideanUnitRadialCoordinate_fderiv_radialFrame
    (coordinate direction : Fin 3)
    (point : EuclideanR3) (hPoint : point ≠ 0) :
    fderiv Real (euclideanUnitRadialCoordinate coordinate) point
        (‖point‖ • EuclideanSpace.basisFun (Fin 3) Real direction) =
      d9KroneckerDelta direction coordinate -
        ((EuclideanSpace.proj (𝕜 := Real) direction) point / ‖point‖) *
          ((EuclideanSpace.proj (𝕜 := Real) coordinate) point / ‖point‖) := by
  have hCoordinate :=
    (EuclideanSpace.proj (𝕜 := Real) coordinate).hasFDerivAt (x := point)
  have hSq :
      HasFDerivAt (fun current : EuclideanR3 => ‖current‖ ^ 2)
        (2 • innerSL Real point) point :=
    (hasStrictFDerivAt_norm_sq point).hasFDerivAt
  have hNorm :=
    hSq.sqrt (pow_ne_zero 2 (norm_ne_zero_iff.mpr hPoint))
  simp only [Real.sqrt_sq (norm_nonneg _)] at hNorm
  have hInverse :=
    (hasDerivAt_inv (norm_ne_zero_iff.mpr hPoint)).comp_hasFDerivAt
      point hNorm
  have hQuotient := hCoordinate.mul hInverse
  have hApplied := DFunLike.congr_fun hQuotient.fderiv
    (‖point‖ • EuclideanSpace.basisFun (Fin 3) Real direction)
  change
    fderiv Real (euclideanUnitRadialCoordinate coordinate) point
        (‖point‖ • EuclideanSpace.basisFun (Fin 3) Real direction) =
      _ at hApplied
  rw [hApplied]
  simp only [add_apply, smul_apply, two_nsmul, innerSL_apply_apply,
    real_inner_smul_right, EuclideanSpace.inner_basisFun_real,
    Function.comp_apply, smul_eq_mul]
  unfold d9KroneckerDelta
  by_cases hSame : direction = coordinate
  · subst coordinate
    simp only [if_pos]
    simp [EuclideanSpace.proj, EuclideanSpace.basisFun_apply]
    field_simp [norm_ne_zero_iff.mpr hPoint]
    ring
  · have hCoordinateDirection : coordinate ≠ direction := Ne.symm hSame
    simp only [hSame, if_false]
    simp [EuclideanSpace.proj, EuclideanSpace.basisFun_apply,
      hCoordinateDirection]
    field_simp [norm_ne_zero_iff.mpr hPoint]
    ring

/-- The polar radial map never meets the Euclidean origin. -/
private theorem throatCoverRadialMap_ne_zero
    (point : ThroatCover period hPeriod) :
    throatCoverRadialMap period hPeriod point ≠ 0 := by
  intro hZero
  have hNorm := throatCoverRadialMap_norm period hPeriod point
  rw [hZero, norm_zero] at hNorm
  exact (Real.exp_ne_zero point.time) hNorm.symm

private theorem euclideanLogNorm_throatCoverRadialMap
    (point : ThroatCover period hPeriod) :
    Real.log ‖throatCoverRadialMap period hPeriod point‖ =
      point.time := by
  rw [throatCoverRadialMap_norm, Real.log_exp]

private theorem euclideanUnitRadialCoordinate_throatCoverRadialMap
    (coordinate : Fin 3) (point : ThroatCover period hPeriod) :
    euclideanUnitRadialCoordinate coordinate
        (throatCoverRadialMap period hPeriod point) =
      d9UnitRadialCoordinate period hPeriod coordinate point := by
  unfold euclideanUnitRadialCoordinate
  rw [throatCoverRadialMap_norm, throatCoverRadialMap_apply]
  change
    (Real.exp point.time *
        (equatorialTwoSphereHomeomorph point.fiber).1 coordinate) /
        Real.exp point.time =
      (equatorialTwoSphereHomeomorph point.fiber).1 coordinate
  field_simp [Real.exp_ne_zero point.time]

/-- The cover time has radial-frame derivative `n_i`. -/
theorem fixedThroatCoverTime_mfderiv_intrinsicFrame
    (direction : Fin 3) (point : ThroatCover period hPeriod) :
    mfderiv throatCoverModelWithCorners 𝓘(Real, Real)
        MappingTorusCover.time point
        (d9IntrinsicThroatCoverFrame period hPeriod direction point) =
      d9UnitRadialCoordinate period hPeriod direction point := by
  let radialPoint := throatCoverRadialMap period hPeriod point
  have hRadialPoint : radialPoint ≠ 0 :=
    throatCoverRadialMap_ne_zero period hPeriod point
  have hSq :
      HasFDerivAt (fun current : EuclideanR3 => ‖current‖ ^ 2)
        (2 • innerSL Real radialPoint) radialPoint :=
    (hasStrictFDerivAt_norm_sq radialPoint).hasFDerivAt
  have hNorm :=
    hSq.sqrt (pow_ne_zero 2 (norm_ne_zero_iff.mpr hRadialPoint))
  simp only [Real.sqrt_sq (norm_nonneg _)] at hNorm
  have hLog :=
    (Real.hasDerivAt_log
      (norm_ne_zero_iff.mpr hRadialPoint)).comp_hasFDerivAt
        radialPoint hNorm
  have hOuter :
      MDifferentiableAt 𝓘(Real, EuclideanR3) 𝓘(Real, Real)
        (Real.log ∘ norm) radialPoint :=
    hLog.differentiableAt.mdifferentiableAt
  have hRadial :
      MDifferentiableAt throatCoverModelWithCorners
        𝓘(Real, EuclideanR3)
        (throatCoverRadialMap period hPeriod) point :=
    (throatCoverRadialMap_isLocalDiffeomorph
      period hPeriod point).mdifferentiableAt (by simp)
  have hTimeFunction :
      MappingTorusCover.time =
        (Real.log ∘ norm) ∘
          throatCoverRadialMap period hPeriod := by
    funext current
    exact (euclideanLogNorm_throatCoverRadialMap
      period hPeriod current).symm
  have hFrame :
      mfderiv throatCoverModelWithCorners 𝓘(Real, EuclideanR3)
          (throatCoverRadialMap period hPeriod) point
          (d9IntrinsicThroatCoverFrame
            period hPeriod direction point) =
        (NormedSpace.fromTangentSpace radialPoint).symm
          (‖radialPoint‖ •
            EuclideanSpace.basisFun (Fin 3) Real direction) := by
    apply (NormedSpace.fromTangentSpace radialPoint).injective
    change
      canonicalThroatRadialDerivativeEquiv period hPeriod point
          (d9IntrinsicThroatCoverFrame
            period hPeriod direction point) =
        ‖radialPoint‖ •
          EuclideanSpace.basisFun (Fin 3) Real direction
    rw [d9IntrinsicThroatCoverFrame_radial,
      throatCoverRadialMap_norm]
  apply (NormedSpace.fromTangentSpace point.time).injective
  rw [hTimeFunction]
  rw [mfderiv_comp_apply point hOuter hRadial]
  rw [hFrame]
  rw [mfderiv_eq_fderiv]
  change
    fderiv Real (fun current : EuclideanR3 => Real.log ‖current‖)
        radialPoint
        (‖radialPoint‖ •
          EuclideanSpace.basisFun (Fin 3) Real direction) =
      d9UnitRadialCoordinate period hPeriod direction point
  rw [← euclideanUnitRadialCoordinate_throatCoverRadialMap
    period hPeriod direction point]
  exact euclideanLogNorm_fderiv_radialFrame
    direction radialPoint hRadialPoint

/-- Unit-sphere coordinates differentiate by the tangential projector
`δ_ij - n_i n_j` in the intrinsic radial frame. -/
theorem d9UnitRadialCoordinate_mfderiv_intrinsicFrame
    (coordinate direction : Fin 3)
    (point : ThroatCover period hPeriod) :
    mfderiv throatCoverModelWithCorners 𝓘(Real, Real)
        (d9UnitRadialCoordinate period hPeriod coordinate) point
        (d9IntrinsicThroatCoverFrame period hPeriod direction point) =
      d9KroneckerDelta direction coordinate -
        d9UnitRadialCoordinate period hPeriod direction point *
          d9UnitRadialCoordinate period hPeriod coordinate point := by
  let radialPoint := throatCoverRadialMap period hPeriod point
  have hRadialPoint : radialPoint ≠ 0 :=
    throatCoverRadialMap_ne_zero period hPeriod point
  have hCoordinate :=
    (EuclideanSpace.proj (𝕜 := Real) coordinate).hasFDerivAt
      (x := radialPoint)
  have hSq :
      HasFDerivAt (fun current : EuclideanR3 => ‖current‖ ^ 2)
        (2 • innerSL Real radialPoint) radialPoint :=
    (hasStrictFDerivAt_norm_sq radialPoint).hasFDerivAt
  have hNorm :=
    hSq.sqrt (pow_ne_zero 2 (norm_ne_zero_iff.mpr hRadialPoint))
  simp only [Real.sqrt_sq (norm_nonneg _)] at hNorm
  have hInverse :=
    (hasDerivAt_inv
      (norm_ne_zero_iff.mpr hRadialPoint)).comp_hasFDerivAt
        radialPoint hNorm
  have hOuter :
      MDifferentiableAt 𝓘(Real, EuclideanR3) 𝓘(Real, Real)
        (euclideanUnitRadialCoordinate coordinate) radialPoint := by
    exact (hCoordinate.mul hInverse).differentiableAt.mdifferentiableAt
  have hRadial :
      MDifferentiableAt throatCoverModelWithCorners
        𝓘(Real, EuclideanR3)
        (throatCoverRadialMap period hPeriod) point :=
    (throatCoverRadialMap_isLocalDiffeomorph
      period hPeriod point).mdifferentiableAt (by simp)
  have hCoordinateFunction :
      d9UnitRadialCoordinate period hPeriod coordinate =
        euclideanUnitRadialCoordinate coordinate ∘
          throatCoverRadialMap period hPeriod := by
    funext current
    exact (euclideanUnitRadialCoordinate_throatCoverRadialMap
      period hPeriod coordinate current).symm
  have hFrame :
      mfderiv throatCoverModelWithCorners 𝓘(Real, EuclideanR3)
          (throatCoverRadialMap period hPeriod) point
          (d9IntrinsicThroatCoverFrame
            period hPeriod direction point) =
        (NormedSpace.fromTangentSpace radialPoint).symm
          (‖radialPoint‖ •
            EuclideanSpace.basisFun (Fin 3) Real direction) := by
    apply (NormedSpace.fromTangentSpace radialPoint).injective
    change
      canonicalThroatRadialDerivativeEquiv period hPeriod point
          (d9IntrinsicThroatCoverFrame
            period hPeriod direction point) =
        ‖radialPoint‖ •
          EuclideanSpace.basisFun (Fin 3) Real direction
    rw [d9IntrinsicThroatCoverFrame_radial,
      throatCoverRadialMap_norm]
  apply
    (NormedSpace.fromTangentSpace
      (d9UnitRadialCoordinate period hPeriod coordinate point)).injective
  rw [hCoordinateFunction]
  rw [mfderiv_comp_apply point hOuter hRadial]
  simp only [Function.comp_apply]
  rw [hFrame]
  rw [mfderiv_eq_fderiv]
  change
    fderiv Real (euclideanUnitRadialCoordinate coordinate) radialPoint
        (‖radialPoint‖ •
          EuclideanSpace.basisFun (Fin 3) Real direction) =
      d9KroneckerDelta direction coordinate -
        d9UnitRadialCoordinate period hPeriod direction point *
          euclideanUnitRadialCoordinate coordinate radialPoint
  rw [euclideanUnitRadialCoordinate_fderiv_radialFrame
    coordinate direction radialPoint hRadialPoint]
  have hDirection :
      (EuclideanSpace.proj (𝕜 := Real) direction) radialPoint /
          ‖radialPoint‖ =
        d9UnitRadialCoordinate period hPeriod direction point := by
    change euclideanUnitRadialCoordinate direction radialPoint = _
    simpa only [radialPoint] using
      euclideanUnitRadialCoordinate_throatCoverRadialMap
        period hPeriod direction point
  have hCoordinate :
      (EuclideanSpace.proj (𝕜 := Real) coordinate) radialPoint /
          ‖radialPoint‖ =
        d9UnitRadialCoordinate period hPeriod coordinate point := by
    change euclideanUnitRadialCoordinate coordinate radialPoint = _
    simpa only [radialPoint] using
      euclideanUnitRadialCoordinate_throatCoverRadialMap
        period hPeriod coordinate point
  rw [hDirection, hCoordinate]
  unfold euclideanUnitRadialCoordinate
  rw [hCoordinate]

/-- The quotient coordinate derivative is the same tangential projector. -/
theorem d9PrimitiveMonopoleCoordinateFrameDerivative_mk
    (coordinate direction : Fin 3)
    (point : ThroatCover period hPeriod) :
    d9PrimitiveMonopoleCoordinateFrameDerivative
        period hPeriod coordinate direction
        (mappingTorusMk (ThroatData period hPeriod) point) =
      d9KroneckerDelta direction coordinate -
        d9UnitRadialCoordinate period hPeriod direction point *
          d9UnitRadialCoordinate period hPeriod coordinate point := by
  have hCoordinate :
      MDifferentiableAt throatCoverModelWithCorners 𝓘(Real, Real)
        (d9PrimitiveMonopoleBaseCoordinate
          period hPeriod coordinate)
        (mappingTorusMk (ThroatData period hPeriod) point) :=
    (d9PrimitiveMonopoleBaseCoordinate_contMDiff
      period hPeriod coordinate).mdifferentiableAt (by simp)
  have hProjection :
      MDifferentiableAt throatCoverModelWithCorners
        throatCoverModelWithCorners
        (mappingTorusMk (ThroatData period hPeriod)) point :=
    (fixedThroat_projection_isLocalDiffeomorph
      period hPeriod).contMDiff.mdifferentiableAt (by simp)
  have hChain := mfderiv_comp_apply point hCoordinate hProjection
    (d9IntrinsicThroatCoverFrame period hPeriod direction point)
  have hFunction :
      d9PrimitiveMonopoleBaseCoordinate period hPeriod coordinate ∘
          mappingTorusMk (ThroatData period hPeriod) =
        d9UnitRadialCoordinate period hPeriod coordinate := by
    funext current
    rfl
  rw [hFunction] at hChain
  have hFrame :=
    d9IntrinsicThroatFrame_mk period hPeriod direction point
  change
    d9IntrinsicThroatFrame period hPeriod direction
        (mappingTorusMk (ThroatData period hPeriod) point) =
      mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
        (mappingTorusMk (ThroatData period hPeriod)) point
        (d9IntrinsicThroatCoverFrame
          period hPeriod direction point) at hFrame
  rw [← hFrame] at hChain
  unfold d9PrimitiveMonopoleCoordinateFrameDerivative
  rw [← hChain]
  exact d9UnitRadialCoordinate_mfderiv_intrinsicFrame
    period hPeriod coordinate direction point

/-- Derivative of the exponential normal phase as a real-time curve. -/
private theorem normalRootSpinFrameExponential_hasDerivAt
    (choice : NormalRootChoice) (mode : Int) (time : Real) :
    HasDerivAt (normalRootSpinFrameExponential period choice mode)
      ((normalRootSpinFrameFrequency period choice mode : Complex) *
        (Complex.I *
          normalRootSpinFrameExponential period choice mode time))
      time := by
  let coefficient : Complex :=
    (normalRootSpinFrameFrequency period choice mode : Complex) * Complex.I
  have hOfReal :
      HasDerivAt (fun input : Real => (input : Complex)) 1 time :=
    Complex.ofRealCLM.hasDerivAt
  have hLinear :
      HasDerivAt (fun input : Real => coefficient * (input : Complex))
        coefficient time := by
    simpa only [mul_one] using hOfReal.const_mul coefficient
  have hExponential := hLinear.cexp
  have hFunction :
      (fun input : Real => Complex.exp (coefficient * (input : Complex))) =
        normalRootSpinFrameExponential period choice mode := by
    funext input
    rfl
  rw [hFunction] at hExponential
  refine hExponential.congr_deriv ?_
  dsimp only [coefficient]
  rw [normalRootSpinFrameExponential]
  ring

/-- Exact derivative of the rotating normal phase in every intrinsic frame
direction. -/
theorem normalRootSpinFramePhase_mfderiv_intrinsicFrame
    (choice : NormalRootChoice) (mode : Int)
    (direction : Fin 3) (point : ThroatCover period hPeriod) :
    mfderiv throatCoverModelWithCorners 𝓘(Real, Complex)
        (normalRootSpinFramePhase period hPeriod choice mode) point
        (d9IntrinsicThroatCoverFrame period hPeriod direction point) =
      (d9UnitRadialCoordinate period hPeriod direction point : Real) •
        ((normalRootSpinFrameFrequency period choice mode : Complex) *
          (Complex.I *
            normalRootSpinFramePhase
              period hPeriod choice mode point)) := by
  have hOuterDerivative :=
    normalRootSpinFrameExponential_hasDerivAt
      period choice mode point.time
  have hOuter :
      MDifferentiableAt 𝓘(Real, Real) 𝓘(Real, Complex)
        (normalRootSpinFrameExponential period choice mode) point.time :=
    hOuterDerivative.differentiableAt.mdifferentiableAt
  have hTime :
      MDifferentiableAt throatCoverModelWithCorners 𝓘(Real, Real)
        MappingTorusCover.time point :=
    (fixedThroatCoverTime_contMDiff
      period hPeriod).mdifferentiableAt (by simp)
  have hFunction :
      normalRootSpinFramePhase period hPeriod choice mode =
        normalRootSpinFrameExponential period choice mode ∘
          MappingTorusCover.time := by
    funext current
    exact (normalRootSpinFrameExponential_eq_phase
      period hPeriod choice mode current).symm
  have hChain := mfderiv_comp_apply point hOuter hTime
    (d9IntrinsicThroatCoverFrame period hPeriod direction point)
  rw [← hFunction] at hChain
  apply
    (NormedSpace.fromTangentSpace
      (normalRootSpinFramePhase period hPeriod choice mode point)).injective
  rw [hChain]
  rw [fixedThroatCoverTime_mfderiv_intrinsicFrame
    period hPeriod direction point]
  rw [mfderiv_eq_fderiv]
  change
    fderiv Real (normalRootSpinFrameExponential period choice mode)
        point.time
        (d9UnitRadialCoordinate period hPeriod direction point) =
      (d9UnitRadialCoordinate period hPeriod direction point : Real) •
        ((normalRootSpinFrameFrequency period choice mode : Complex) *
          (Complex.I *
            normalRootSpinFramePhase
              period hPeriod choice mode point))
  rw [hOuterDerivative.hasFDerivAt.fderiv]
  simp only [ContinuousLinearMap.toSpanSingleton_apply]
  rw [normalRootSpinFrameExponential_eq_phase]

/-- The matter mode differentiates only through its normal Fourier phase. -/
theorem normalRootMatterModeValue_mfderiv_intrinsicFrame
    (choice : NormalRootChoice) (mode : Int)
    (direction : Fin 3) (point : ThroatCover period hPeriod) :
    mfderiv throatCoverModelWithCorners 𝓘(Real, MatterFiber)
        (normalRootMatterModeValue period hPeriod choice mode) point
        (d9IntrinsicThroatCoverFrame period hPeriod direction point) =
      (normalRootSpinFrameFrequency period choice mode *
          d9UnitRadialCoordinate period hPeriod direction point) •
        d9MatterComplexAction Complex.I
          (normalRootMatterModeValue period hPeriod choice mode point) := by
  have hOuter :
      MDifferentiableAt 𝓘(Real, Complex) 𝓘(Real, MatterFiber)
        d9MatterGammaPositiveEigenlineCLM
        (normalRootSpinFramePhase period hPeriod choice mode point) :=
    d9MatterGammaPositiveEigenlineCLM.differentiableAt.mdifferentiableAt
  have hPhase :
      MDifferentiableAt throatCoverModelWithCorners 𝓘(Real, Complex)
        (normalRootSpinFramePhase period hPeriod choice mode) point :=
    (normalRootSpinFramePhase_contMDiff
      period hPeriod choice mode).mdifferentiableAt (by simp)
  have hFunction :
      normalRootMatterModeValue period hPeriod choice mode =
        d9MatterGammaPositiveEigenlineCLM ∘
          normalRootSpinFramePhase period hPeriod choice mode := by
    rfl
  have hChain := mfderiv_comp_apply point hOuter hPhase
    (d9IntrinsicThroatCoverFrame period hPeriod direction point)
  rw [← hFunction] at hChain
  apply
    (NormedSpace.fromTangentSpace
      (normalRootMatterModeValue
        period hPeriod choice mode point)).injective
  rw [hChain]
  rw [normalRootSpinFramePhase_mfderiv_intrinsicFrame
    period hPeriod choice mode direction point]
  rw [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv]
  change
    d9MatterGammaPositiveEigenlineCLM
        ((d9UnitRadialCoordinate
            period hPeriod direction point : Real) •
          ((normalRootSpinFrameFrequency period choice mode : Complex) *
            (Complex.I *
              normalRootSpinFramePhase
                period hPeriod choice mode point))) =
      (normalRootSpinFrameFrequency period choice mode *
          d9UnitRadialCoordinate period hPeriod direction point) •
        d9MatterComplexAction Complex.I
          (normalRootMatterModeValue
            period hPeriod choice mode point)
  apply matterFiberHalfSpinorLinearEquiv.injective
  simp only [map_smul,
    normalRootMatterModeValue,
    d9MatterGammaPositiveEigenlineCLM_apply,
    matterFiberHalfSpinorLinearEquiv_d9MatterComplexAction,
    d9MatterGammaPositiveEigenvector,
    LinearEquiv.apply_symm_apply]
  funext index
  simp only [Pi.smul_apply, Complex.real_smul, smul_eq_mul]
  push_cast
  ring

/-- The infinitesimal SpinC phase acts componentwise by the transported
matter complex structure. -/
theorem d9PrimitiveSpinCImaginaryAction_eq_pair
    (matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCImaginaryAction matter =
      (d9MatterComplexAction Complex.I matter.1,
        d9MatterComplexAction Complex.I matter.2) := by
  apply d9DoubledMatterFiberHalfSpinorLinearEquiv.injective
  change
    d9DoubledMatterFiberHalfSpinorLinearEquiv
        (d9PrimitiveSpinCPhaseActionCLM
          d9PrimitiveSpinCImaginaryPhase matter) =
      d9DoubledMatterFiberHalfSpinorLinearEquiv
        (d9MatterComplexAction Complex.I matter.1,
          d9MatterComplexAction Complex.I matter.2)
  rw [d9DoubledMatterFiberHalfSpinorLinearEquiv_phaseAction]
  simp only [
    d9PrimitiveSpinCImaginaryPhase_coe,
    d9DoubledMatterFiberHalfSpinorLinearEquiv_apply,
    matterFiberHalfSpinorLinearEquiv_d9MatterComplexAction]
  rfl

/-- The doubled normal mode has the expected `k n_i J` derivative in either
normal-root sector. -/
theorem primitiveSpinCNormalModeDoubledLift_mfderiv_intrinsicFrame
    (sector : NormalRootChoice) (mode : Int)
    (direction : Fin 3) (point : ThroatCover period hPeriod) :
    mfderiv throatCoverModelWithCorners
        𝓘(Real, D9DoubledMatterFiber)
        (primitiveSpinCNormalModeDoubledLift
          period hPeriod sector mode) point
        (d9IntrinsicThroatCoverFrame period hPeriod direction point) =
      (normalRootSpinFrameFrequency period sector mode *
          d9UnitRadialCoordinate period hPeriod direction point) •
        d9PrimitiveSpinCImaginaryAction
          (primitiveSpinCNormalModeDoubledLift
            period hPeriod sector mode point) := by
  cases sector with
  | positiveQuarter =>
      let embedding :
          MatterFiber →L[Real] D9DoubledMatterFiber :=
        ContinuousLinearMap.inl Real MatterFiber MatterFiber
      have hOuter :
          MDifferentiableAt 𝓘(Real, MatterFiber)
            𝓘(Real, D9DoubledMatterFiber) embedding
            (normalRootMatterModeValue
              period hPeriod .positiveQuarter mode point) :=
        embedding.differentiableAt.mdifferentiableAt
      have hMode :
          MDifferentiableAt throatCoverModelWithCorners
            𝓘(Real, MatterFiber)
            (normalRootMatterModeValue
              period hPeriod .positiveQuarter mode) point :=
        (normalRootMatterModeValue_contMDiff
          period hPeriod .positiveQuarter mode).mdifferentiableAt (by simp)
      have hFunction :
          primitiveSpinCNormalModeDoubledLift
              period hPeriod .positiveQuarter mode =
            embedding ∘
              normalRootMatterModeValue
                period hPeriod .positiveQuarter mode := by
        rfl
      have hChain := mfderiv_comp_apply point hOuter hMode
        (d9IntrinsicThroatCoverFrame period hPeriod direction point)
      rw [← hFunction] at hChain
      apply
        (NormedSpace.fromTangentSpace
          (primitiveSpinCNormalModeDoubledLift
            period hPeriod .positiveQuarter mode point)).injective
      rw [hChain]
      rw [normalRootMatterModeValue_mfderiv_intrinsicFrame
        period hPeriod .positiveQuarter mode direction point]
      rw [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv]
      change
        embedding
            ((normalRootSpinFrameFrequency
                period .positiveQuarter mode *
              d9UnitRadialCoordinate
                period hPeriod direction point) •
              d9MatterComplexAction Complex.I
                (normalRootMatterModeValue
                  period hPeriod .positiveQuarter mode point)) =
          (normalRootSpinFrameFrequency
                period .positiveQuarter mode *
              d9UnitRadialCoordinate
                period hPeriod direction point) •
            d9PrimitiveSpinCImaginaryAction
              (normalRootMatterModeValue
                  period hPeriod .positiveQuarter mode point,
                0)
      rw [map_smul, d9PrimitiveSpinCImaginaryAction_eq_pair]
      simp [embedding, d9MatterComplexAction]
  | negativeQuarter =>
      let embedding :
          MatterFiber →L[Real] D9DoubledMatterFiber :=
        ContinuousLinearMap.inr Real MatterFiber MatterFiber
      have hOuter :
          MDifferentiableAt 𝓘(Real, MatterFiber)
            𝓘(Real, D9DoubledMatterFiber) embedding
            (normalRootMatterModeValue
              period hPeriod .negativeQuarter mode point) :=
        embedding.differentiableAt.mdifferentiableAt
      have hMode :
          MDifferentiableAt throatCoverModelWithCorners
            𝓘(Real, MatterFiber)
            (normalRootMatterModeValue
              period hPeriod .negativeQuarter mode) point :=
        (normalRootMatterModeValue_contMDiff
          period hPeriod .negativeQuarter mode).mdifferentiableAt (by simp)
      have hFunction :
          primitiveSpinCNormalModeDoubledLift
              period hPeriod .negativeQuarter mode =
            embedding ∘
              normalRootMatterModeValue
                period hPeriod .negativeQuarter mode := by
        rfl
      have hChain := mfderiv_comp_apply point hOuter hMode
        (d9IntrinsicThroatCoverFrame period hPeriod direction point)
      rw [← hFunction] at hChain
      apply
        (NormedSpace.fromTangentSpace
          (primitiveSpinCNormalModeDoubledLift
            period hPeriod .negativeQuarter mode point)).injective
      rw [hChain]
      rw [normalRootMatterModeValue_mfderiv_intrinsicFrame
        period hPeriod .negativeQuarter mode direction point]
      rw [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv]
      change
        embedding
            ((normalRootSpinFrameFrequency
                period .negativeQuarter mode *
              d9UnitRadialCoordinate
                period hPeriod direction point) •
              d9MatterComplexAction Complex.I
                (normalRootMatterModeValue
                  period hPeriod .negativeQuarter mode point)) =
          (normalRootSpinFrameFrequency
                period .negativeQuarter mode *
              d9UnitRadialCoordinate
                period hPeriod direction point) •
            d9PrimitiveSpinCImaginaryAction
              (0,
                normalRootMatterModeValue
                  period hPeriod .negativeQuarter mode point)
      rw [map_smul, d9PrimitiveSpinCImaginaryAction_eq_pair]
      simp [embedding, d9MatterComplexAction]

/-- Cartesian complex coordinates used by the two Hopf gauges. -/
private def euclideanComplexXYCLM : EuclideanR3 →L[Real] Complex :=
  Complex.ofRealCLM.comp
      (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 3)) +
    (normalModeComplexRightMulRealCLM Complex.I).comp
      (Complex.ofRealCLM.comp
        (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 3)))

private def euclideanComplexStarXYCLM : EuclideanR3 →L[Real] Complex :=
  Complex.ofRealCLM.comp
      (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 3)) -
    (normalModeComplexRightMulRealCLM Complex.I).comp
      (Complex.ofRealCLM.comp
        (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 3)))

@[simp]
private theorem euclideanComplexXYCLM_apply (point : EuclideanR3) :
    euclideanComplexXYCLM point =
      Complex.ofReal
          ((EuclideanSpace.proj (𝕜 := Real) (0 : Fin 3)) point) +
        Complex.I *
          Complex.ofReal
            ((EuclideanSpace.proj (𝕜 := Real) (1 : Fin 3)) point) := by
  simp [euclideanComplexXYCLM, mul_comm]

@[simp]
private theorem euclideanComplexStarXYCLM_apply (point : EuclideanR3) :
    euclideanComplexStarXYCLM point =
      Complex.ofReal
          ((EuclideanSpace.proj (𝕜 := Real) (0 : Fin 3)) point) -
        Complex.I *
          Complex.ofReal
            ((EuclideanSpace.proj (𝕜 := Real) (1 : Fin 3)) point) := by
  simp [euclideanComplexStarXYCLM, mul_comm]

private def euclideanHopfNorthFirst (point : EuclideanR3) : Complex :=
  Complex.ofReal
    (Real.sqrt
      (1 + (EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3)) point))

private def euclideanHopfNorthSecond (point : EuclideanR3) : Complex :=
  Complex.ofReal
      (Real.sqrt
        (1 + (EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3)) point))⁻¹ *
    euclideanComplexStarXYCLM point

private def euclideanHopfSouthFirst (point : EuclideanR3) : Complex :=
  Complex.ofReal
      (Real.sqrt
        (1 - (EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3)) point))⁻¹ *
    euclideanComplexXYCLM point

private def euclideanHopfSouthSecond (point : EuclideanR3) : Complex :=
  Complex.ofReal
    (Real.sqrt
      (1 - (EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3)) point))

private theorem euclideanHopfNorthFirst_fderiv
    (point increment : EuclideanR3)
    (hPositive :
      0 < 1 +
        (EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3)) point) :
    fderiv Real euclideanHopfNorthFirst point increment =
      Complex.ofReal
        ((EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3)) increment /
          (2 * Real.sqrt
            (1 +
              (EuclideanSpace.proj
                (𝕜 := Real) (2 : Fin 3)) point))) := by
  have hCoordinate :=
    (EuclideanSpace.proj
      (𝕜 := Real) (2 : Fin 3)).hasFDerivAt (x := point)
  have hRadicand :=
    (hasFDerivAt_const (x := point) (c := (1 : Real))).add hCoordinate
  have hSqrt :=
    hRadicand.sqrt (ne_of_gt hPositive)
  have hComplex :=
    Complex.ofRealCLM.hasFDerivAt.comp point hSqrt
  have hApplied := DFunLike.congr_fun hComplex.fderiv increment
  change fderiv Real euclideanHopfNorthFirst point increment = _ at hApplied
  rw [hApplied]
  simp only [ContinuousLinearMap.comp_apply, smul_apply, add_apply, zero_apply,
    Pi.add_apply,
    ContinuousLinearMap.proj_apply, Complex.ofRealCLM_apply]
  congr 1
  ring

private theorem euclideanHopfSouthSecond_fderiv
    (point increment : EuclideanR3)
    (hPositive :
      0 < 1 -
        (EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3)) point) :
    fderiv Real euclideanHopfSouthSecond point increment =
      Complex.ofReal
        (-(EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3)) increment /
          (2 * Real.sqrt
            (1 -
              (EuclideanSpace.proj
                (𝕜 := Real) (2 : Fin 3)) point))) := by
  have hCoordinate :=
    (EuclideanSpace.proj
      (𝕜 := Real) (2 : Fin 3)).hasFDerivAt (x := point)
  have hRadicand :=
    (hasFDerivAt_const (x := point) (c := (1 : Real))).sub hCoordinate
  have hSqrt :=
    hRadicand.sqrt (ne_of_gt hPositive)
  have hComplex :=
    Complex.ofRealCLM.hasFDerivAt.comp point hSqrt
  have hApplied := DFunLike.congr_fun hComplex.fderiv increment
  change fderiv Real euclideanHopfSouthSecond point increment = _ at hApplied
  rw [hApplied]
  simp only [ContinuousLinearMap.comp_apply, smul_apply, sub_apply, zero_apply,
    Pi.sub_apply,
    ContinuousLinearMap.proj_apply, Complex.ofRealCLM_apply]
  congr 1
  ring

private theorem euclideanHopfNorthSecond_fderiv
    (point increment : EuclideanR3)
    (hPositive :
      0 < 1 +
        (EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3)) point) :
    fderiv Real euclideanHopfNorthSecond point increment =
      Complex.ofReal
          (Real.sqrt
            (1 +
              (EuclideanSpace.proj
                (𝕜 := Real) (2 : Fin 3)) point))⁻¹ *
          euclideanComplexStarXYCLM increment -
        Complex.ofReal
          ((EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3)) increment /
            (2 *
              Real.sqrt
                  (1 +
                    (EuclideanSpace.proj
                      (𝕜 := Real) (2 : Fin 3)) point) ^ 3)) *
          euclideanComplexStarXYCLM point := by
  let radicand : EuclideanR3 → Real :=
    fun current =>
      1 + (EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3)) current
  have hCoordinate :=
    (EuclideanSpace.proj
      (𝕜 := Real) (2 : Fin 3)).hasFDerivAt (x := point)
  have hRadicand :
      HasFDerivAt radicand
        (0 + EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3)) point :=
    (hasFDerivAt_const (x := point) (c := (1 : Real))).add hCoordinate
  have hSqrt :=
    hRadicand.sqrt (ne_of_gt hPositive)
  have hSqrtNe :
      Real.sqrt (radicand point) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr hPositive
  have hInverse :=
    (hasDerivAt_inv hSqrtNe).comp_hasFDerivAt point hSqrt
  have hComplexInverse :=
    Complex.ofRealCLM.hasFDerivAt.comp point hInverse
  have hStar :=
    euclideanComplexStarXYCLM.hasFDerivAt (x := point)
  have hProduct := hComplexInverse.mul hStar
  have hApplied := DFunLike.congr_fun hProduct.fderiv increment
  change fderiv Real euclideanHopfNorthSecond point increment = _ at hApplied
  have hCoefficient :
      -(Real.sqrt (radicand point) ^ 2)⁻¹ *
          ((1 / (2 * Real.sqrt (radicand point))) *
            (0 +
              (EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3)) increment)) =
        -((EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3)) increment /
          (2 * Real.sqrt (radicand point) ^ 3)) := by
    field_simp [hSqrtNe]
    ring
  rw [hApplied]
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    Function.comp_apply, Complex.ofRealCLM_apply, zero_apply,
    euclideanComplexStarXYCLM_apply, smul_eq_mul]
  rw [hCoefficient]
  simp only [radicand]
  push_cast
  ring

private theorem euclideanHopfSouthFirst_fderiv
    (point increment : EuclideanR3)
    (hPositive :
      0 < 1 -
        (EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3)) point) :
    fderiv Real euclideanHopfSouthFirst point increment =
      Complex.ofReal
          (Real.sqrt
            (1 -
              (EuclideanSpace.proj
                (𝕜 := Real) (2 : Fin 3)) point))⁻¹ *
          euclideanComplexXYCLM increment +
        Complex.ofReal
          ((EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3)) increment /
            (2 *
              Real.sqrt
                  (1 -
                    (EuclideanSpace.proj
                      (𝕜 := Real) (2 : Fin 3)) point) ^ 3)) *
          euclideanComplexXYCLM point := by
  let radicand : EuclideanR3 → Real :=
    fun current =>
      1 - (EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3)) current
  have hCoordinate :=
    (EuclideanSpace.proj
      (𝕜 := Real) (2 : Fin 3)).hasFDerivAt (x := point)
  have hRadicand :
      HasFDerivAt radicand
        (0 - EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3)) point :=
    (hasFDerivAt_const (x := point) (c := (1 : Real))).sub hCoordinate
  have hSqrt :=
    hRadicand.sqrt (ne_of_gt hPositive)
  have hSqrtNe :
      Real.sqrt (radicand point) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr hPositive
  have hInverse :=
    (hasDerivAt_inv hSqrtNe).comp_hasFDerivAt point hSqrt
  have hComplexInverse :=
    Complex.ofRealCLM.hasFDerivAt.comp point hInverse
  have hXY := euclideanComplexXYCLM.hasFDerivAt (x := point)
  have hProduct := hComplexInverse.mul hXY
  have hApplied := DFunLike.congr_fun hProduct.fderiv increment
  change fderiv Real euclideanHopfSouthFirst point increment = _ at hApplied
  have hCoefficient :
      -(Real.sqrt (radicand point) ^ 2)⁻¹ *
          ((1 / (2 * Real.sqrt (radicand point))) *
            (0 -
              (EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3)) increment)) =
        (EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3)) increment /
          (2 * Real.sqrt (radicand point) ^ 3) := by
    field_simp [hSqrtNe]
    ring
  rw [hApplied]
  simp only [add_apply, sub_apply, smul_apply, ContinuousLinearMap.comp_apply,
    Function.comp_apply, Complex.ofRealCLM_apply, zero_apply,
    euclideanComplexXYCLM_apply, smul_eq_mul]
  rw [hCoefficient]
  simp only [radicand]
  push_cast
  ring

/-- Ambient unit vector underlying the spherical factor of the throat cover. -/
private def d9UnitRadialVector
    (point : ThroatCover period hPeriod) : EuclideanR3 :=
  (equatorialTwoSphereHomeomorph point.fiber).1

private theorem d9UnitRadialVector_contMDiff :
    ContMDiff throatCoverModelWithCorners
      𝓘(Real, EuclideanR3) ∞
      (d9UnitRadialVector period hPeriod) := by
  have hToProduct :
      ContMDiff throatCoverModelWithCorners
        ((𝓡 2).prod 𝓘(Real)) ∞
        (coverHomeomorphProd (ThroatData period hPeriod)) :=
    chartedSpacePullback_toFun_contMDiff
      throatCoverModelWithCorners ∞
      (coverHomeomorphProd (ThroatData period hPeriod))
  have hFiber :
      ContMDiff throatCoverModelWithCorners (𝓡 2) ∞
        (fun point : ThroatCover period hPeriod => point.fiber) :=
    contMDiff_fst.comp hToProduct
  have hSphere :
      ContMDiff throatCoverModelWithCorners (𝓡 2) ∞
        (fun point : ThroatCover period hPeriod =>
          equatorialTwoSphereHomeomorph point.fiber) :=
    (chartedSpacePullback_toFun_contMDiff
      (𝓡 2) ∞ equatorialTwoSphereHomeomorph).comp hFiber
  exact contMDiff_coe_sphere.comp hSphere

@[simp]
private theorem d9UnitRadialVector_proj
    (coordinate : Fin 3) (point : ThroatCover period hPeriod) :
    (EuclideanSpace.proj (𝕜 := Real) coordinate)
        (d9UnitRadialVector period hPeriod point) =
      d9UnitRadialCoordinate period hPeriod coordinate point :=
  rfl

/-- The ambient derivative of the unit radial vector is the tangential
projector, component by component. -/
private theorem d9UnitRadialVector_mfderiv_intrinsicFrame_proj
    (coordinate direction : Fin 3)
    (point : ThroatCover period hPeriod) :
    (EuclideanSpace.proj (𝕜 := Real) coordinate)
        (NormedSpace.fromTangentSpace
          (d9UnitRadialVector period hPeriod point)
          (mfderiv throatCoverModelWithCorners
            𝓘(Real, EuclideanR3)
            (d9UnitRadialVector period hPeriod) point
            (d9IntrinsicThroatCoverFrame
              period hPeriod direction point))) =
      d9KroneckerDelta direction coordinate -
        d9UnitRadialCoordinate period hPeriod direction point *
          d9UnitRadialCoordinate period hPeriod coordinate point := by
  have hVector :
      MDifferentiableAt throatCoverModelWithCorners
        𝓘(Real, EuclideanR3)
        (d9UnitRadialVector period hPeriod) point :=
    (d9UnitRadialVector_contMDiff period hPeriod).mdifferentiableAt (by simp)
  have hProjection :
      MDifferentiableAt 𝓘(Real, EuclideanR3) 𝓘(Real)
        (EuclideanSpace.proj (𝕜 := Real) coordinate)
        (d9UnitRadialVector period hPeriod point) :=
    (EuclideanSpace.proj (𝕜 := Real) coordinate).differentiableAt
      |>.mdifferentiableAt
  have hChain := mfderiv_comp_apply point hProjection hVector
    (d9IntrinsicThroatCoverFrame period hPeriod direction point)
  have hFunction :
      (EuclideanSpace.proj (𝕜 := Real) coordinate) ∘
          d9UnitRadialVector period hPeriod =
        d9UnitRadialCoordinate period hPeriod coordinate := by
    funext current
    rfl
  rw [hFunction] at hChain
  rw [d9UnitRadialCoordinate_mfderiv_intrinsicFrame
    period hPeriod coordinate direction point] at hChain
  rw [hChain]
  rw [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv]
  rfl

private def d9UnitRadialFrameIncrement
    (direction : Fin 3) (point : ThroatCover period hPeriod) :
    EuclideanR3 :=
  NormedSpace.fromTangentSpace
    (d9UnitRadialVector period hPeriod point)
    (mfderiv throatCoverModelWithCorners
      𝓘(Real, EuclideanR3)
      (d9UnitRadialVector period hPeriod) point
      (d9IntrinsicThroatCoverFrame period hPeriod direction point))

@[simp]
private theorem d9UnitRadialFrameIncrement_proj
    (coordinate direction : Fin 3)
    (point : ThroatCover period hPeriod) :
    (EuclideanSpace.proj (𝕜 := Real) coordinate)
        (d9UnitRadialFrameIncrement
          period hPeriod direction point) =
      d9KroneckerDelta direction coordinate -
        d9UnitRadialCoordinate period hPeriod direction point *
          d9UnitRadialCoordinate period hPeriod coordinate point :=
  d9UnitRadialVector_mfderiv_intrinsicFrame_proj
    period hPeriod coordinate direction point

@[simp]
private theorem euclideanHopfNorthFirst_unitRadialVector
    (point : ThroatCover period hPeriod) :
    euclideanHopfNorthFirst
        (d9UnitRadialVector period hPeriod point) =
      primitiveMonopoleZeroNorthValue
        (d9MonopoleSphereCoverProjection period hPeriod point) := by
  rfl

@[simp]
private theorem euclideanHopfNorthSecond_unitRadialVector
    (point : ThroatCover period hPeriod) :
    euclideanHopfNorthSecond
        (d9UnitRadialVector period hPeriod point) =
      primitiveMonopoleZeroComplementNorthValue
        (d9MonopoleSphereCoverProjection period hPeriod point) := by
  simp [euclideanHopfNorthSecond,
    primitiveMonopoleZeroComplementNorthValue,
    euclideanComplexStarXYCLM_apply,
    monopoleSphereXY_d9MonopoleSphereCoverProjection,
    d9UnitRadialVector, d9UnitRadialCoordinate, Complex.real_smul]
  ring

@[simp]
private theorem euclideanHopfSouthFirst_unitRadialVector
    (point : ThroatCover period hPeriod) :
    euclideanHopfSouthFirst
        (d9UnitRadialVector period hPeriod point) =
      primitiveMonopoleZeroSouthValue
        (d9MonopoleSphereCoverProjection period hPeriod point) := by
  simp [euclideanHopfSouthFirst, primitiveMonopoleZeroSouthValue,
    euclideanComplexXYCLM_apply,
    monopoleSphereXY_d9MonopoleSphereCoverProjection,
    d9UnitRadialVector, d9UnitRadialCoordinate, Complex.real_smul]
  ring

@[simp]
private theorem euclideanHopfSouthSecond_unitRadialVector
    (point : ThroatCover period hPeriod) :
    euclideanHopfSouthSecond
        (d9UnitRadialVector period hPeriod point) =
      primitiveMonopoleZeroComplementSouthValue
        (d9MonopoleSphereCoverProjection period hPeriod point) := by
  rfl

private theorem euclideanHopfNorthFirst_differentiableAt
    (point : EuclideanR3)
    (hPositive :
      0 < 1 +
        (EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3)) point) :
    DifferentiableAt Real euclideanHopfNorthFirst point := by
  have hCoordinate :=
    (EuclideanSpace.proj
      (𝕜 := Real) (2 : Fin 3)).hasFDerivAt (x := point)
  have hRadicand :=
    (hasFDerivAt_const (x := point) (c := (1 : Real))).add hCoordinate
  exact
    (Complex.ofRealCLM.hasFDerivAt.comp point
      (hRadicand.sqrt (ne_of_gt hPositive))).differentiableAt

private theorem euclideanHopfSouthSecond_differentiableAt
    (point : EuclideanR3)
    (hPositive :
      0 < 1 -
        (EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3)) point) :
    DifferentiableAt Real euclideanHopfSouthSecond point := by
  have hCoordinate :=
    (EuclideanSpace.proj
      (𝕜 := Real) (2 : Fin 3)).hasFDerivAt (x := point)
  have hRadicand :=
    (hasFDerivAt_const (x := point) (c := (1 : Real))).sub hCoordinate
  exact
    (Complex.ofRealCLM.hasFDerivAt.comp point
      (hRadicand.sqrt (ne_of_gt hPositive))).differentiableAt

private theorem euclideanHopfNorthSecond_differentiableAt
    (point : EuclideanR3)
    (hPositive :
      0 < 1 +
        (EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3)) point) :
    DifferentiableAt Real euclideanHopfNorthSecond point := by
  let radicand : EuclideanR3 → Real :=
    fun current =>
      1 + (EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3)) current
  have hCoordinate :=
    (EuclideanSpace.proj
      (𝕜 := Real) (2 : Fin 3)).hasFDerivAt (x := point)
  have hRadicand :
      HasFDerivAt radicand
        (0 + EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3)) point :=
    (hasFDerivAt_const (x := point) (c := (1 : Real))).add hCoordinate
  have hSqrt := hRadicand.sqrt (ne_of_gt hPositive)
  have hSqrtNe :
      Real.sqrt (radicand point) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr hPositive
  exact
    ((Complex.ofRealCLM.hasFDerivAt.comp point
        ((hasDerivAt_inv hSqrtNe).comp_hasFDerivAt point hSqrt)).mul
      (euclideanComplexStarXYCLM.hasFDerivAt
        (x := point))).differentiableAt

private theorem euclideanHopfSouthFirst_differentiableAt
    (point : EuclideanR3)
    (hPositive :
      0 < 1 -
        (EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3)) point) :
    DifferentiableAt Real euclideanHopfSouthFirst point := by
  let radicand : EuclideanR3 → Real :=
    fun current =>
      1 - (EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3)) current
  have hCoordinate :=
    (EuclideanSpace.proj
      (𝕜 := Real) (2 : Fin 3)).hasFDerivAt (x := point)
  have hRadicand :
      HasFDerivAt radicand
        (0 - EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3)) point :=
    (hasFDerivAt_const (x := point) (c := (1 : Real))).sub hCoordinate
  have hSqrt := hRadicand.sqrt (ne_of_gt hPositive)
  have hSqrtNe :
      Real.sqrt (radicand point) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr hPositive
  exact
    ((Complex.ofRealCLM.hasFDerivAt.comp point
        ((hasDerivAt_inv hSqrtNe).comp_hasFDerivAt point hSqrt)).mul
      (euclideanComplexXYCLM.hasFDerivAt
        (x := point))).differentiableAt

private theorem d9UnitRadialVector_comp_mfderiv
    (function : EuclideanR3 → Complex)
    (direction : Fin 3) (point : ThroatCover period hPeriod)
    (hDifferentiable :
      DifferentiableAt Real function
        (d9UnitRadialVector period hPeriod point)) :
    NormedSpace.fromTangentSpace
        (function (d9UnitRadialVector period hPeriod point))
        (mfderiv throatCoverModelWithCorners 𝓘(Real, Complex)
          (function ∘ d9UnitRadialVector period hPeriod) point
          (d9IntrinsicThroatCoverFrame
            period hPeriod direction point)) =
      fderiv Real function
        (d9UnitRadialVector period hPeriod point)
        (d9UnitRadialFrameIncrement
          period hPeriod direction point) := by
  rw [mfderiv_comp_apply point hDifferentiable.mdifferentiableAt
    ((d9UnitRadialVector_contMDiff
      period hPeriod).mdifferentiableAt (by simp))]
  rw [mfderiv_eq_fderiv]
  rfl

private def d9HopfNorthFirstFrameDerivative
    (direction : Fin 3) (point : ThroatCover period hPeriod) : Complex :=
  Complex.ofReal
    ((d9KroneckerDelta direction 2 -
        d9UnitRadialCoordinate period hPeriod direction point *
          d9UnitRadialCoordinate period hPeriod 2 point) /
      (2 * Real.sqrt
        (1 + d9UnitRadialCoordinate period hPeriod 2 point)))

private theorem primitiveMonopoleZeroNorthValue_mfderiv_intrinsicFrame
    (direction : Fin 3) (point : ThroatCover period hPeriod)
    (hChart :
      d9MonopoleSphereCoverProjection period hPeriod point ∈
        monopoleChartDomain .north) :
    NormedSpace.fromTangentSpace (𝕜 := Real) (E := Complex)
        (primitiveMonopoleZeroNorthValue
          (d9MonopoleSphereCoverProjection period hPeriod point))
        (mfderiv throatCoverModelWithCorners 𝓘(Real, Complex)
          (fun current =>
            primitiveMonopoleZeroNorthValue
              (d9MonopoleSphereCoverProjection
                period hPeriod current))
          point
          (d9IntrinsicThroatCoverFrame period hPeriod direction point)) =
      d9HopfNorthFirstFrameDerivative
        period hPeriod direction point := by
  have hPositiveSphere :=
    one_add_monopoleSphereCoordinate_two_pos_of_mem_north
      (d9MonopoleSphereCoverProjection period hPeriod point) hChart
  have hPositive :
      0 < 1 +
        (EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3))
          (d9UnitRadialVector period hPeriod point) := by
    change
      0 < 1 +
        d9UnitRadialCoordinate period hPeriod 2 point
    simpa only [
      monopoleSphereCoordinate_d9MonopoleSphereCoverProjection] using
      hPositiveSphere
  change
    NormedSpace.fromTangentSpace (𝕜 := Real) (E := Complex)
        (euclideanHopfNorthFirst
          (d9UnitRadialVector period hPeriod point))
        (mfderiv throatCoverModelWithCorners 𝓘(Real, Complex)
          (euclideanHopfNorthFirst ∘
            d9UnitRadialVector period hPeriod) point
          (d9IntrinsicThroatCoverFrame period hPeriod direction point)) =
      d9HopfNorthFirstFrameDerivative period hPeriod direction point
  rw [d9UnitRadialVector_comp_mfderiv
    period hPeriod euclideanHopfNorthFirst direction point
    (euclideanHopfNorthFirst_differentiableAt
      (d9UnitRadialVector period hPeriod point) hPositive)]
  rw [euclideanHopfNorthFirst_fderiv _ _ hPositive]
  simp only [d9HopfNorthFirstFrameDerivative,
    d9UnitRadialFrameIncrement_proj]
  change
    Complex.ofReal
        ((d9KroneckerDelta direction 2 -
            d9UnitRadialCoordinate period hPeriod direction point *
              d9UnitRadialCoordinate period hPeriod 2 point) /
          (2 * Real.sqrt
            (1 + d9UnitRadialCoordinate period hPeriod 2 point))) =
      Complex.ofReal
        ((d9KroneckerDelta direction 2 -
            d9UnitRadialCoordinate period hPeriod direction point *
              d9UnitRadialCoordinate period hPeriod 2 point) /
          (2 * Real.sqrt
            (1 + d9UnitRadialCoordinate period hPeriod 2 point)))
  rfl

private def d9HopfNorthSecondFrameDerivative
    (direction : Fin 3) (point : ThroatCover period hPeriod) : Complex :=
  Complex.ofReal
      (Real.sqrt
        (1 + d9UnitRadialCoordinate period hPeriod 2 point))⁻¹ *
      (Complex.ofReal
          (d9KroneckerDelta direction 0 -
            d9UnitRadialCoordinate period hPeriod direction point *
              d9UnitRadialCoordinate period hPeriod 0 point) -
        Complex.I *
          Complex.ofReal
            (d9KroneckerDelta direction 1 -
              d9UnitRadialCoordinate period hPeriod direction point *
                d9UnitRadialCoordinate period hPeriod 1 point)) -
    Complex.ofReal
        ((d9KroneckerDelta direction 2 -
            d9UnitRadialCoordinate period hPeriod direction point *
              d9UnitRadialCoordinate period hPeriod 2 point) /
          (2 *
            Real.sqrt
              (1 + d9UnitRadialCoordinate period hPeriod 2 point) ^ 3)) *
      (Complex.ofReal
          (d9UnitRadialCoordinate period hPeriod 0 point) -
        Complex.I *
          Complex.ofReal
            (d9UnitRadialCoordinate period hPeriod 1 point))

private def euclideanMonopoleSphereXYValue
    (point : EuclideanR3) : Complex :=
  ⟨(EuclideanSpace.proj (𝕜 := Real) (0 : Fin 3)) point,
    (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 3)) point⟩

private def euclideanHopfNorthSecondLocal
    (point : EuclideanR3) : Complex :=
  (Real.sqrt
    (1 + (EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3)) point))⁻¹ •
      star (euclideanMonopoleSphereXYValue point)

private theorem euclideanHopfNorthSecondLocal_eq :
    euclideanHopfNorthSecondLocal = euclideanHopfNorthSecond := by
  funext point
  apply Complex.ext <;>
    simp [euclideanHopfNorthSecondLocal,
      euclideanMonopoleSphereXYValue, euclideanHopfNorthSecond,
      euclideanComplexStarXYCLM_apply, Complex.real_smul,
      Complex.mul_re, Complex.mul_im] <;>
    ring

private theorem
    primitiveMonopoleZeroComplementNorthValue_mfderiv_intrinsicFrame
    (direction : Fin 3) (point : ThroatCover period hPeriod)
    (hChart :
      d9MonopoleSphereCoverProjection period hPeriod point ∈
        monopoleChartDomain .north) :
    NormedSpace.fromTangentSpace (𝕜 := Real) (E := Complex)
        (primitiveMonopoleZeroComplementNorthValue
          (d9MonopoleSphereCoverProjection period hPeriod point))
        (mfderiv throatCoverModelWithCorners 𝓘(Real, Complex)
          (fun current =>
            primitiveMonopoleZeroComplementNorthValue
              (d9MonopoleSphereCoverProjection
                period hPeriod current))
          point
          (d9IntrinsicThroatCoverFrame period hPeriod direction point)) =
      d9HopfNorthSecondFrameDerivative
        period hPeriod direction point := by
  have hPositiveSphere :=
    one_add_monopoleSphereCoordinate_two_pos_of_mem_north
      (d9MonopoleSphereCoverProjection period hPeriod point) hChart
  have hPositive :
      0 < 1 +
        (EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3))
          (d9UnitRadialVector period hPeriod point) := by
    change
      0 < 1 +
        d9UnitRadialCoordinate period hPeriod 2 point
    simpa only [
      monopoleSphereCoordinate_d9MonopoleSphereCoverProjection] using
      hPositiveSphere
  change
    NormedSpace.fromTangentSpace (𝕜 := Real) (E := Complex)
        (euclideanHopfNorthSecondLocal
          (d9UnitRadialVector period hPeriod point))
        (mfderiv throatCoverModelWithCorners 𝓘(Real, Complex)
          (euclideanHopfNorthSecondLocal ∘
            d9UnitRadialVector period hPeriod) point
          (d9IntrinsicThroatCoverFrame period hPeriod direction point)) =
      d9HopfNorthSecondFrameDerivative period hPeriod direction point
  rw [d9UnitRadialVector_comp_mfderiv
    period hPeriod euclideanHopfNorthSecondLocal direction point
    (by
      rw [euclideanHopfNorthSecondLocal_eq]
      exact euclideanHopfNorthSecond_differentiableAt
        (d9UnitRadialVector period hPeriod point) hPositive)]
  rw [euclideanHopfNorthSecondLocal_eq]
  rw [euclideanHopfNorthSecond_fderiv _ _ hPositive]
  simp only [d9HopfNorthSecondFrameDerivative,
    euclideanComplexStarXYCLM_apply,
    d9UnitRadialFrameIncrement_proj]
  change
    d9HopfNorthSecondFrameDerivative period hPeriod direction point =
      d9HopfNorthSecondFrameDerivative period hPeriod direction point
  rfl

private def d9HopfSouthFirstFrameDerivative
    (direction : Fin 3) (point : ThroatCover period hPeriod) : Complex :=
  Complex.ofReal
      (Real.sqrt
        (1 - d9UnitRadialCoordinate period hPeriod 2 point))⁻¹ *
      (Complex.ofReal
          (d9KroneckerDelta direction 0 -
            d9UnitRadialCoordinate period hPeriod direction point *
              d9UnitRadialCoordinate period hPeriod 0 point) +
        Complex.I *
          Complex.ofReal
            (d9KroneckerDelta direction 1 -
              d9UnitRadialCoordinate period hPeriod direction point *
                d9UnitRadialCoordinate period hPeriod 1 point)) +
    Complex.ofReal
        ((d9KroneckerDelta direction 2 -
            d9UnitRadialCoordinate period hPeriod direction point *
              d9UnitRadialCoordinate period hPeriod 2 point) /
          (2 *
            Real.sqrt
              (1 - d9UnitRadialCoordinate period hPeriod 2 point) ^ 3)) *
      (Complex.ofReal
          (d9UnitRadialCoordinate period hPeriod 0 point) +
        Complex.I *
          Complex.ofReal
            (d9UnitRadialCoordinate period hPeriod 1 point))

private def euclideanHopfSouthFirstLocal
    (point : EuclideanR3) : Complex :=
  (Real.sqrt
    (1 - (EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3)) point))⁻¹ •
      euclideanMonopoleSphereXYValue point

private theorem euclideanHopfSouthFirstLocal_eq :
    euclideanHopfSouthFirstLocal = euclideanHopfSouthFirst := by
  funext point
  apply Complex.ext <;>
    simp [euclideanHopfSouthFirstLocal,
      euclideanMonopoleSphereXYValue, euclideanHopfSouthFirst,
      euclideanComplexXYCLM_apply, Complex.real_smul,
      Complex.mul_re, Complex.mul_im] <;>
    ring

private theorem primitiveMonopoleZeroSouthValue_mfderiv_intrinsicFrame
    (direction : Fin 3) (point : ThroatCover period hPeriod)
    (hChart :
      d9MonopoleSphereCoverProjection period hPeriod point ∈
        monopoleChartDomain .south) :
    NormedSpace.fromTangentSpace (𝕜 := Real) (E := Complex)
        (primitiveMonopoleZeroSouthValue
          (d9MonopoleSphereCoverProjection period hPeriod point))
        (mfderiv throatCoverModelWithCorners 𝓘(Real, Complex)
          (fun current =>
            primitiveMonopoleZeroSouthValue
              (d9MonopoleSphereCoverProjection
                period hPeriod current))
          point
          (d9IntrinsicThroatCoverFrame period hPeriod direction point)) =
      d9HopfSouthFirstFrameDerivative
        period hPeriod direction point := by
  have hPositiveSphere :=
    one_sub_monopoleSphereCoordinate_two_pos_of_mem_south
      (d9MonopoleSphereCoverProjection period hPeriod point) hChart
  have hPositive :
      0 < 1 -
        (EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3))
          (d9UnitRadialVector period hPeriod point) := by
    change
      0 < 1 -
        d9UnitRadialCoordinate period hPeriod 2 point
    simpa only [
      monopoleSphereCoordinate_d9MonopoleSphereCoverProjection] using
      hPositiveSphere
  change
    NormedSpace.fromTangentSpace (𝕜 := Real) (E := Complex)
        (euclideanHopfSouthFirstLocal
          (d9UnitRadialVector period hPeriod point))
        (mfderiv throatCoverModelWithCorners 𝓘(Real, Complex)
          (euclideanHopfSouthFirstLocal ∘
            d9UnitRadialVector period hPeriod) point
          (d9IntrinsicThroatCoverFrame period hPeriod direction point)) =
      d9HopfSouthFirstFrameDerivative period hPeriod direction point
  rw [d9UnitRadialVector_comp_mfderiv
    period hPeriod euclideanHopfSouthFirstLocal direction point
    (by
      rw [euclideanHopfSouthFirstLocal_eq]
      exact euclideanHopfSouthFirst_differentiableAt
        (d9UnitRadialVector period hPeriod point) hPositive)]
  rw [euclideanHopfSouthFirstLocal_eq]
  rw [euclideanHopfSouthFirst_fderiv _ _ hPositive]
  simp only [d9HopfSouthFirstFrameDerivative,
    euclideanComplexXYCLM_apply,
    d9UnitRadialFrameIncrement_proj]
  change
    d9HopfSouthFirstFrameDerivative period hPeriod direction point =
      d9HopfSouthFirstFrameDerivative period hPeriod direction point
  rfl

private def d9HopfSouthSecondFrameDerivative
    (direction : Fin 3) (point : ThroatCover period hPeriod) : Complex :=
  Complex.ofReal
    (-((d9KroneckerDelta direction 2 -
          d9UnitRadialCoordinate period hPeriod direction point *
            d9UnitRadialCoordinate period hPeriod 2 point) /
      (2 * Real.sqrt
        (1 - d9UnitRadialCoordinate period hPeriod 2 point))))

private theorem
    primitiveMonopoleZeroComplementSouthValue_mfderiv_intrinsicFrame
    (direction : Fin 3) (point : ThroatCover period hPeriod)
    (hChart :
      d9MonopoleSphereCoverProjection period hPeriod point ∈
        monopoleChartDomain .south) :
    NormedSpace.fromTangentSpace (𝕜 := Real) (E := Complex)
        (primitiveMonopoleZeroComplementSouthValue
          (d9MonopoleSphereCoverProjection period hPeriod point))
        (mfderiv throatCoverModelWithCorners 𝓘(Real, Complex)
          (fun current =>
            primitiveMonopoleZeroComplementSouthValue
              (d9MonopoleSphereCoverProjection
                period hPeriod current))
          point
          (d9IntrinsicThroatCoverFrame period hPeriod direction point)) =
      d9HopfSouthSecondFrameDerivative
        period hPeriod direction point := by
  have hPositiveSphere :=
    one_sub_monopoleSphereCoordinate_two_pos_of_mem_south
      (d9MonopoleSphereCoverProjection period hPeriod point) hChart
  have hPositive :
      0 < 1 -
        (EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3))
          (d9UnitRadialVector period hPeriod point) := by
    change
      0 < 1 -
        d9UnitRadialCoordinate period hPeriod 2 point
    simpa only [
      monopoleSphereCoordinate_d9MonopoleSphereCoverProjection] using
      hPositiveSphere
  change
    NormedSpace.fromTangentSpace (𝕜 := Real) (E := Complex)
        (euclideanHopfSouthSecond
          (d9UnitRadialVector period hPeriod point))
        (mfderiv throatCoverModelWithCorners 𝓘(Real, Complex)
          (euclideanHopfSouthSecond ∘
            d9UnitRadialVector period hPeriod) point
          (d9IntrinsicThroatCoverFrame period hPeriod direction point)) =
      d9HopfSouthSecondFrameDerivative period hPeriod direction point
  rw [d9UnitRadialVector_comp_mfderiv
    period hPeriod euclideanHopfSouthSecond direction point
    (euclideanHopfSouthSecond_differentiableAt
      (d9UnitRadialVector period hPeriod point) hPositive)]
  rw [euclideanHopfSouthSecond_fderiv _ _ hPositive]
  simp only [d9HopfSouthSecondFrameDerivative,
    d9UnitRadialFrameIncrement_proj]
  rw [d9UnitRadialVector_proj]
  rw [neg_div]

/-- Monopole coefficient pulled back to the cover and evaluated on one
intrinsic frame direction. -/
private def d9HopfMonopoleFrameCoefficient
    (chart : MonopoleChart) (direction : Fin 3)
    (point : ThroatCover period hPeriod) : Real :=
  primitiveMonopoleCartesianPotential 1 chart
    (d9MonopoleSphereCoverProjection period hPeriod point)
    (d9KroneckerDelta direction 0 -
      d9UnitRadialCoordinate period hPeriod direction point *
        d9UnitRadialCoordinate period hPeriod 0 point)
    (d9KroneckerDelta direction 1 -
      d9UnitRadialCoordinate period hPeriod direction point *
        d9UnitRadialCoordinate period hPeriod 1 point)

private theorem d9HopfMonopoleFrameCoefficient_north
    (direction : Fin 3) (point : ThroatCover period hPeriod) :
    d9HopfMonopoleFrameCoefficient
        period hPeriod .north direction point =
      (d9UnitRadialCoordinate period hPeriod 0 point *
            d9KroneckerDelta direction 1 -
          d9UnitRadialCoordinate period hPeriod 1 point *
            d9KroneckerDelta direction 0) /
        (2 *
          (1 + d9UnitRadialCoordinate period hPeriod 2 point)) := by
  unfold d9HopfMonopoleFrameCoefficient
    primitiveMonopoleCartesianPotential
    primitiveMonopoleAngularNumerator
  simp only [
    monopoleSphereCoordinate_d9MonopoleSphereCoverProjection,
    Int.cast_one]
  simp [div_eq_mul_inv]
  ring

private theorem d9HopfMonopoleFrameCoefficient_south
    (direction : Fin 3) (point : ThroatCover period hPeriod) :
    d9HopfMonopoleFrameCoefficient
        period hPeriod .south direction point =
      -(d9UnitRadialCoordinate period hPeriod 0 point *
            d9KroneckerDelta direction 1 -
          d9UnitRadialCoordinate period hPeriod 1 point *
            d9KroneckerDelta direction 0) /
        (2 *
          (1 - d9UnitRadialCoordinate period hPeriod 2 point)) := by
  unfold d9HopfMonopoleFrameCoefficient
    primitiveMonopoleCartesianPotential
    primitiveMonopoleAngularNumerator
  simp only [
    monopoleSphereCoordinate_d9MonopoleSphereCoverProjection,
    Int.cast_one]
  simp [div_eq_mul_inv]
  ring

private def d9HopfFirstScalar
    (chart : MonopoleChart) (point : ThroatCover period hPeriod) : Complex :=
  primitiveMonopoleZeroLocalValue chart
    (d9MonopoleSphereCoverProjection period hPeriod point)

private def d9HopfSecondScalar
    (chart : MonopoleChart) (point : ThroatCover period hPeriod) : Complex :=
  primitiveMonopoleZeroComplementLocalValue chart
    (d9MonopoleSphereCoverProjection period hPeriod point)

private def d9HopfFirstFrameDerivative
    (chart : MonopoleChart) (direction : Fin 3)
    (point : ThroatCover period hPeriod) : Complex :=
  match chart with
  | .north =>
      d9HopfNorthFirstFrameDerivative period hPeriod direction point
  | .south =>
      d9HopfSouthFirstFrameDerivative period hPeriod direction point

private def d9HopfSecondFrameDerivative
    (chart : MonopoleChart) (direction : Fin 3)
    (point : ThroatCover period hPeriod) : Complex :=
  match chart with
  | .north =>
      d9HopfNorthSecondFrameDerivative period hPeriod direction point
  | .south =>
      d9HopfSouthSecondFrameDerivative period hPeriod direction point

private def d9HopfFirstCovariantFrameDerivative
    (chart : MonopoleChart) (direction : Fin 3)
    (point : ThroatCover period hPeriod) : Complex :=
  d9HopfFirstFrameDerivative period hPeriod chart direction point +
    Complex.ofReal
        (d9HopfMonopoleFrameCoefficient
          period hPeriod chart direction point) *
      (Complex.I * d9HopfFirstScalar period hPeriod chart point)

private def d9HopfSecondCovariantFrameDerivative
    (chart : MonopoleChart) (direction : Fin 3)
    (point : ThroatCover period hPeriod) : Complex :=
  d9HopfSecondFrameDerivative period hPeriod chart direction point +
    Complex.ofReal
        (d9HopfMonopoleFrameCoefficient
          period hPeriod chart direction point) *
      (Complex.I * d9HopfSecondScalar period hPeriod chart point)

private def hopfTangentialIncrement
    (coordinate direction : Fin 3) (n : Fin 3 → Real) : Real :=
  d9KroneckerDelta direction coordinate -
    n direction * n coordinate

private def hopfNorthFirstScalarAlgebra
    (s : Real) : Complex :=
  Complex.ofReal s

private def hopfNorthSecondScalarAlgebra
    (n : Fin 3 → Real) (s : Real) : Complex :=
  Complex.ofReal (s⁻¹) *
    (Complex.ofReal (n 0) - Complex.I * Complex.ofReal (n 1))

private def hopfNorthConnectionAlgebra
    (n : Fin 3 → Real) (direction : Fin 3) : Real :=
  (n 0 * d9KroneckerDelta direction 1 -
      n 1 * d9KroneckerDelta direction 0) /
    (2 * (1 + n 2))

private def hopfNorthFirstDerivativeAlgebra
    (n : Fin 3 → Real) (s : Real) (direction : Fin 3) : Complex :=
  Complex.ofReal
    (hopfTangentialIncrement 2 direction n / (2 * s))

private def hopfNorthSecondDerivativeAlgebra
    (n : Fin 3 → Real) (s : Real) (direction : Fin 3) : Complex :=
  Complex.ofReal (s⁻¹) *
      (Complex.ofReal (hopfTangentialIncrement 0 direction n) -
        Complex.I *
          Complex.ofReal (hopfTangentialIncrement 1 direction n)) -
    Complex.ofReal
        (hopfTangentialIncrement 2 direction n / (2 * s ^ 3)) *
      (Complex.ofReal (n 0) - Complex.I * Complex.ofReal (n 1))

private def hopfNorthFirstCovariantAlgebra
    (n : Fin 3 → Real) (s : Real) (direction : Fin 3) : Complex :=
  hopfNorthFirstDerivativeAlgebra n s direction +
    Complex.ofReal (hopfNorthConnectionAlgebra n direction) *
      (Complex.I * hopfNorthFirstScalarAlgebra s)

private def hopfNorthSecondCovariantAlgebra
    (n : Fin 3 → Real) (s : Real) (direction : Fin 3) : Complex :=
  hopfNorthSecondDerivativeAlgebra n s direction +
    Complex.ofReal (hopfNorthConnectionAlgebra n direction) *
      (Complex.I * hopfNorthSecondScalarAlgebra n s)

private def hopfDirectionalFirstCovariantTarget
    (n : Fin 3 → Real) (firstScalar secondScalar : Complex)
    (direction : Fin 3) : Complex :=
  if direction = 0 then
    (1 / 2 : Real) •
      (secondScalar - Complex.ofReal (n 0) * firstScalar)
  else if direction = 1 then
    (1 / 2 : Real) •
      (Complex.I * secondScalar -
        Complex.ofReal (n 1) * firstScalar)
  else
    Complex.ofReal ((1 - n 2) / 2) * firstScalar

private def hopfDirectionalSecondCovariantTarget
    (n : Fin 3 → Real) (firstScalar secondScalar : Complex)
    (direction : Fin 3) : Complex :=
  if direction = 0 then
    (1 / 2 : Real) •
      (firstScalar - Complex.ofReal (n 0) * secondScalar)
  else if direction = 1 then
    (1 / 2 : Real) •
      (-Complex.I * firstScalar -
        Complex.ofReal (n 1) * secondScalar)
  else
    -Complex.ofReal ((1 + n 2) / 2) * secondScalar

@[simp] private theorem hopfTangentialIncrement_zero_zero
    (n : Fin 3 → Real) :
    hopfTangentialIncrement 0 0 n = 1 - n 0 ^ 2 := by
  simp [hopfTangentialIncrement, d9KroneckerDelta, pow_two]

@[simp] private theorem hopfTangentialIncrement_one_zero
    (n : Fin 3 → Real) :
    hopfTangentialIncrement 1 0 n = -(n 0 * n 1) := by
  simp [hopfTangentialIncrement, d9KroneckerDelta]

@[simp] private theorem hopfTangentialIncrement_two_zero
    (n : Fin 3 → Real) :
    hopfTangentialIncrement 2 0 n = -(n 0 * n 2) := by
  simp [hopfTangentialIncrement, d9KroneckerDelta]

@[simp] private theorem hopfTangentialIncrement_zero_one
    (n : Fin 3 → Real) :
    hopfTangentialIncrement 0 1 n = -(n 1 * n 0) := by
  simp [hopfTangentialIncrement, d9KroneckerDelta]

@[simp] private theorem hopfTangentialIncrement_one_one
    (n : Fin 3 → Real) :
    hopfTangentialIncrement 1 1 n = 1 - n 1 ^ 2 := by
  simp [hopfTangentialIncrement, d9KroneckerDelta, pow_two]

@[simp] private theorem hopfTangentialIncrement_two_one
    (n : Fin 3 → Real) :
    hopfTangentialIncrement 2 1 n = -(n 1 * n 2) := by
  simp [hopfTangentialIncrement, d9KroneckerDelta]

@[simp] private theorem hopfTangentialIncrement_zero_two
    (n : Fin 3 → Real) :
    hopfTangentialIncrement 0 2 n = -(n 2 * n 0) := by
  simp [hopfTangentialIncrement, d9KroneckerDelta]

@[simp] private theorem hopfTangentialIncrement_one_two
    (n : Fin 3 → Real) :
    hopfTangentialIncrement 1 2 n = -(n 2 * n 1) := by
  simp [hopfTangentialIncrement, d9KroneckerDelta]

@[simp] private theorem hopfTangentialIncrement_two_two
    (n : Fin 3 → Real) :
    hopfTangentialIncrement 2 2 n = 1 - n 2 ^ 2 := by
  simp [hopfTangentialIncrement, d9KroneckerDelta, pow_two]

@[simp] private theorem hopfNorthConnectionAlgebra_zero
    (n : Fin 3 → Real) :
    hopfNorthConnectionAlgebra n 0 =
      -n 1 / (2 * (1 + n 2)) := by
  simp [hopfNorthConnectionAlgebra, d9KroneckerDelta]

@[simp] private theorem hopfNorthConnectionAlgebra_one
    (n : Fin 3 → Real) :
    hopfNorthConnectionAlgebra n 1 =
      n 0 / (2 * (1 + n 2)) := by
  simp [hopfNorthConnectionAlgebra, d9KroneckerDelta]

@[simp] private theorem hopfNorthConnectionAlgebra_two
    (n : Fin 3 → Real) :
    hopfNorthConnectionAlgebra n 2 = 0 := by
  simp [hopfNorthConnectionAlgebra, d9KroneckerDelta]

private theorem hopfNorthCovariantDirectional_zero_algebra
    (n : Fin 3 → Real) (s : Real)
    (hSqrtNe : s ≠ 0)
    (hPlus : 1 + n 2 ≠ 0)
    (hSqrtSq : s ^ 2 = 1 + n 2)
    (hSphere : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1) :
    hopfNorthFirstCovariantAlgebra n s 0 =
        (1 / 2 : Real) •
          (hopfNorthSecondScalarAlgebra n s -
            Complex.ofReal (n 0) * hopfNorthFirstScalarAlgebra s) ∧
      hopfNorthSecondCovariantAlgebra n s 0 =
        (1 / 2 : Real) •
          (hopfNorthFirstScalarAlgebra s -
            Complex.ofReal (n 0) *
              hopfNorthSecondScalarAlgebra n s) := by
  have hSqrtCube : s ^ 3 = s * (1 + n 2) := by
    calc
      s ^ 3 = s * s ^ 2 := by ring
      _ = s * (1 + n 2) := by rw [hSqrtSq]
  have hSqrtFourth : s ^ 4 = (1 + n 2) ^ 2 := by
    calc
      s ^ 4 = (s ^ 2) ^ 2 := by ring
      _ = (1 + n 2) ^ 2 := by rw [hSqrtSq]
  constructor <;>
    apply Complex.ext <;>
    simp only [hopfNorthFirstCovariantAlgebra,
      hopfNorthSecondCovariantAlgebra,
      hopfNorthFirstDerivativeAlgebra,
      hopfNorthSecondDerivativeAlgebra,
      hopfNorthFirstScalarAlgebra,
      hopfNorthSecondScalarAlgebra,
      hopfNorthConnectionAlgebra_zero,
      hopfNorthConnectionAlgebra_one,
      hopfNorthConnectionAlgebra_two,
      hopfTangentialIncrement_zero_zero,
      hopfTangentialIncrement_one_zero,
      hopfTangentialIncrement_two_zero,
      hopfTangentialIncrement_zero_one,
      hopfTangentialIncrement_one_one,
      hopfTangentialIncrement_two_one,
      hopfTangentialIncrement_zero_two,
      hopfTangentialIncrement_one_two,
      hopfTangentialIncrement_two_two,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.real_smul,
      zero_mul, mul_zero, one_mul, mul_one,
      zero_add, add_zero, sub_zero, zero_sub, neg_zero] <;>
    field_simp [hSqrtNe, hPlus] <;>
    (try simp only [hSqrtSq, hSqrtCube, hSqrtFourth]) <;>
    ring_nf <;>
    nlinarith [hSqrtSq, hSphere]

private theorem hopfNorthCovariantDirectional_one_algebra
    (n : Fin 3 → Real) (s : Real)
    (hSqrtNe : s ≠ 0)
    (hPlus : 1 + n 2 ≠ 0)
    (hSqrtSq : s ^ 2 = 1 + n 2)
    (hSphere : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1) :
    hopfNorthFirstCovariantAlgebra n s 1 =
        (1 / 2 : Real) •
          (Complex.I * hopfNorthSecondScalarAlgebra n s -
            Complex.ofReal (n 1) * hopfNorthFirstScalarAlgebra s) ∧
      hopfNorthSecondCovariantAlgebra n s 1 =
        (1 / 2 : Real) •
          (-Complex.I * hopfNorthFirstScalarAlgebra s -
            Complex.ofReal (n 1) *
              hopfNorthSecondScalarAlgebra n s) := by
  have hSqrtCube : s ^ 3 = s * (1 + n 2) := by
    calc
      s ^ 3 = s * s ^ 2 := by ring
      _ = s * (1 + n 2) := by rw [hSqrtSq]
  have hSqrtFourth : s ^ 4 = (1 + n 2) ^ 2 := by
    calc
      s ^ 4 = (s ^ 2) ^ 2 := by ring
      _ = (1 + n 2) ^ 2 := by rw [hSqrtSq]
  constructor <;>
    apply Complex.ext <;>
    simp only [hopfNorthFirstCovariantAlgebra,
      hopfNorthSecondCovariantAlgebra,
      hopfNorthFirstDerivativeAlgebra,
      hopfNorthSecondDerivativeAlgebra,
      hopfNorthFirstScalarAlgebra,
      hopfNorthSecondScalarAlgebra,
      hopfNorthConnectionAlgebra_zero,
      hopfNorthConnectionAlgebra_one,
      hopfNorthConnectionAlgebra_two,
      hopfTangentialIncrement_zero_zero,
      hopfTangentialIncrement_one_zero,
      hopfTangentialIncrement_two_zero,
      hopfTangentialIncrement_zero_one,
      hopfTangentialIncrement_one_one,
      hopfTangentialIncrement_two_one,
      hopfTangentialIncrement_zero_two,
      hopfTangentialIncrement_one_two,
      hopfTangentialIncrement_two_two,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.real_smul,
      zero_mul, mul_zero, one_mul, mul_one,
      zero_add, add_zero, sub_zero, zero_sub, neg_zero] <;>
    field_simp [hSqrtNe, hPlus] <;>
    (try simp only [hSqrtSq, hSqrtCube, hSqrtFourth]) <;>
    ring_nf <;>
    nlinarith [hSqrtSq, hSphere]

private theorem hopfNorthCovariantDirectional_two_algebra
    (n : Fin 3 → Real) (s : Real)
    (hSqrtNe : s ≠ 0)
    (hPlus : 1 + n 2 ≠ 0)
    (hSqrtSq : s ^ 2 = 1 + n 2)
    (hSphere : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1) :
    hopfNorthFirstCovariantAlgebra n s 2 =
        Complex.ofReal ((1 - n 2) / 2) *
          hopfNorthFirstScalarAlgebra s ∧
      hopfNorthSecondCovariantAlgebra n s 2 =
        -Complex.ofReal ((1 + n 2) / 2) *
          hopfNorthSecondScalarAlgebra n s := by
  have hSqrtCube : s ^ 3 = s * (1 + n 2) := by
    calc
      s ^ 3 = s * s ^ 2 := by ring
      _ = s * (1 + n 2) := by rw [hSqrtSq]
  have hSqrtFourth : s ^ 4 = (1 + n 2) ^ 2 := by
    calc
      s ^ 4 = (s ^ 2) ^ 2 := by ring
      _ = (1 + n 2) ^ 2 := by rw [hSqrtSq]
  constructor <;>
    apply Complex.ext <;>
    simp only [hopfNorthFirstCovariantAlgebra,
      hopfNorthSecondCovariantAlgebra,
      hopfNorthFirstDerivativeAlgebra,
      hopfNorthSecondDerivativeAlgebra,
      hopfNorthFirstScalarAlgebra,
      hopfNorthSecondScalarAlgebra,
      hopfNorthConnectionAlgebra_zero,
      hopfNorthConnectionAlgebra_one,
      hopfNorthConnectionAlgebra_two,
      hopfTangentialIncrement_zero_zero,
      hopfTangentialIncrement_one_zero,
      hopfTangentialIncrement_two_zero,
      hopfTangentialIncrement_zero_one,
      hopfTangentialIncrement_one_one,
      hopfTangentialIncrement_two_one,
      hopfTangentialIncrement_zero_two,
      hopfTangentialIncrement_one_two,
      hopfTangentialIncrement_two_two,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      zero_mul, mul_zero, one_mul, mul_one,
      zero_add, add_zero, sub_zero, zero_sub, neg_zero] <;>
    field_simp [hSqrtNe, hPlus] <;>
    (try simp only [hSqrtSq, hSqrtCube, hSqrtFourth]) <;>
    ring_nf <;>
    nlinarith [hSqrtSq, hSphere]

private theorem hopfNorthCovariantContraction_algebra
    (n : Fin 3 → Real) (s : Real)
    (hSqrtNe : s ≠ 0)
    (hPlus : 1 + n 2 ≠ 0)
    (hSqrtSq : s ^ 2 = 1 + n 2)
    (hSphere : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1) :
    (Complex.I * hopfNorthSecondCovariantAlgebra n s 0 -
          hopfNorthSecondCovariantAlgebra n s 1 +
        Complex.I * hopfNorthFirstCovariantAlgebra n s 2 =
      Complex.I * hopfNorthFirstScalarAlgebra s) ∧
    (Complex.I * hopfNorthFirstCovariantAlgebra n s 0 +
          hopfNorthFirstCovariantAlgebra n s 1 -
        Complex.I * hopfNorthSecondCovariantAlgebra n s 2 =
      Complex.I * hopfNorthSecondScalarAlgebra n s) := by
  have hSqrtCube : s ^ 3 = s * (1 + n 2) := by
    calc
      s ^ 3 = s * s ^ 2 := by ring
      _ = s * (1 + n 2) := by rw [hSqrtSq]
  have hSqrtFourth : s ^ 4 = (1 + n 2) ^ 2 := by
    calc
      s ^ 4 = (s ^ 2) ^ 2 := by ring
      _ = (1 + n 2) ^ 2 := by rw [hSqrtSq]
  constructor <;>
    apply Complex.ext <;>
    simp only [hopfNorthFirstCovariantAlgebra,
      hopfNorthSecondCovariantAlgebra,
      hopfNorthFirstDerivativeAlgebra,
      hopfNorthSecondDerivativeAlgebra,
      hopfNorthFirstScalarAlgebra,
      hopfNorthSecondScalarAlgebra,
      hopfNorthConnectionAlgebra_zero,
      hopfNorthConnectionAlgebra_one,
      hopfNorthConnectionAlgebra_two,
      hopfTangentialIncrement_zero_zero,
      hopfTangentialIncrement_one_zero,
      hopfTangentialIncrement_two_zero,
      hopfTangentialIncrement_zero_one,
      hopfTangentialIncrement_one_one,
      hopfTangentialIncrement_two_one,
      hopfTangentialIncrement_zero_two,
      hopfTangentialIncrement_one_two,
      hopfTangentialIncrement_two_two,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      if_pos, if_neg, zero_mul, mul_zero, one_mul, mul_one,
      zero_add, add_zero, sub_zero, zero_sub, neg_zero] <;>
    field_simp [hSqrtNe, hPlus] <;>
    simp only [hSqrtSq, hSqrtCube, hSqrtFourth] <;>
    ring_nf <;>
    nlinarith [hSqrtSq, hSphere]

private theorem d9HopfNorthCovariantContraction
    (point : ThroatCover period hPeriod)
    (hChart :
      d9MonopoleSphereCoverProjection period hPeriod point ∈
        monopoleChartDomain .north) :
    (Complex.I *
            d9HopfSecondCovariantFrameDerivative
              period hPeriod .north 0 point -
          d9HopfSecondCovariantFrameDerivative
            period hPeriod .north 1 point +
        Complex.I *
          d9HopfFirstCovariantFrameDerivative
            period hPeriod .north 2 point =
      Complex.I * d9HopfFirstScalar period hPeriod .north point) ∧
    (Complex.I *
            d9HopfFirstCovariantFrameDerivative
              period hPeriod .north 0 point +
          d9HopfFirstCovariantFrameDerivative
            period hPeriod .north 1 point -
        Complex.I *
          d9HopfSecondCovariantFrameDerivative
            period hPeriod .north 2 point =
      Complex.I * d9HopfSecondScalar period hPeriod .north point) := by
  have hPositive :=
    one_add_monopoleSphereCoordinate_two_pos_of_mem_north
      (d9MonopoleSphereCoverProjection period hPeriod point) hChart
  rw [monopoleSphereCoordinate_d9MonopoleSphereCoverProjection] at hPositive
  have hSqrtNe :
      Real.sqrt
          (1 + d9UnitRadialCoordinate period hPeriod 2 point) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr hPositive
  have hSqrtSq :
      Real.sqrt
          (1 + d9UnitRadialCoordinate period hPeriod 2 point) ^ 2 =
        1 + d9UnitRadialCoordinate period hPeriod 2 point :=
    Real.sq_sqrt (le_of_lt hPositive)
  have hSphere :=
    d9UnitRadialCoordinate_norm_sq period hPeriod point
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hSphere
  norm_num at hSphere
  let n : Fin 3 → Real :=
    fun direction =>
      d9UnitRadialCoordinate period hPeriod direction point
  have hSphereAlgebra :
      n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1 := by
    dsimp only [n]
    nlinarith [hSphere]
  have hAlgebra :=
    hopfNorthCovariantContraction_algebra n
      (Real.sqrt (1 + n 2))
      hSqrtNe (ne_of_gt hPositive) hSqrtSq hSphereAlgebra
  simpa [n, d9HopfFirstCovariantFrameDerivative,
    d9HopfSecondCovariantFrameDerivative,
    d9HopfFirstFrameDerivative, d9HopfSecondFrameDerivative,
    d9HopfNorthFirstFrameDerivative,
    d9HopfNorthSecondFrameDerivative,
    d9HopfFirstScalar, d9HopfSecondScalar,
    primitiveMonopoleZeroLocalValue,
    primitiveMonopoleZeroComplementLocalValue,
    primitiveMonopoleZeroNorthValue,
    primitiveMonopoleZeroComplementNorthValue,
    d9HopfMonopoleFrameCoefficient_north,
    hopfNorthFirstCovariantAlgebra,
    hopfNorthSecondCovariantAlgebra,
    hopfNorthFirstDerivativeAlgebra,
    hopfNorthSecondDerivativeAlgebra,
    hopfNorthConnectionAlgebra,
    hopfNorthFirstScalarAlgebra,
    hopfNorthSecondScalarAlgebra,
    hopfTangentialIncrement,
    monopoleSphereCoordinate_d9MonopoleSphereCoverProjection,
    star_monopoleSphereXY_d9MonopoleSphereCoverProjection,
    Complex.real_smul] using hAlgebra

private def hopfSouthFirstScalarAlgebra
    (n : Fin 3 → Real) (s : Real) : Complex :=
  Complex.ofReal (s⁻¹) *
    (Complex.ofReal (n 0) + Complex.I * Complex.ofReal (n 1))

private def hopfSouthSecondScalarAlgebra
    (s : Real) : Complex :=
  Complex.ofReal s

private def hopfSouthConnectionAlgebra
    (n : Fin 3 → Real) (direction : Fin 3) : Real :=
  -(n 0 * d9KroneckerDelta direction 1 -
      n 1 * d9KroneckerDelta direction 0) /
    (2 * (1 - n 2))

private def hopfSouthFirstDerivativeAlgebra
    (n : Fin 3 → Real) (s : Real) (direction : Fin 3) : Complex :=
  Complex.ofReal (s⁻¹) *
      (Complex.ofReal (hopfTangentialIncrement 0 direction n) +
        Complex.I *
          Complex.ofReal (hopfTangentialIncrement 1 direction n)) +
    Complex.ofReal
        (hopfTangentialIncrement 2 direction n / (2 * s ^ 3)) *
      (Complex.ofReal (n 0) + Complex.I * Complex.ofReal (n 1))

private def hopfSouthSecondDerivativeAlgebra
    (n : Fin 3 → Real) (s : Real) (direction : Fin 3) : Complex :=
  Complex.ofReal
    (-(hopfTangentialIncrement 2 direction n / (2 * s)))

private def hopfSouthFirstCovariantAlgebra
    (n : Fin 3 → Real) (s : Real) (direction : Fin 3) : Complex :=
  hopfSouthFirstDerivativeAlgebra n s direction +
    Complex.ofReal (hopfSouthConnectionAlgebra n direction) *
      (Complex.I * hopfSouthFirstScalarAlgebra n s)

private def hopfSouthSecondCovariantAlgebra
    (n : Fin 3 → Real) (s : Real) (direction : Fin 3) : Complex :=
  hopfSouthSecondDerivativeAlgebra n s direction +
    Complex.ofReal (hopfSouthConnectionAlgebra n direction) *
      (Complex.I * hopfSouthSecondScalarAlgebra s)

@[simp] private theorem hopfSouthConnectionAlgebra_zero
    (n : Fin 3 → Real) :
    hopfSouthConnectionAlgebra n 0 =
      n 1 / (2 * (1 - n 2)) := by
  simp [hopfSouthConnectionAlgebra, d9KroneckerDelta]

@[simp] private theorem hopfSouthConnectionAlgebra_one
    (n : Fin 3 → Real) :
    hopfSouthConnectionAlgebra n 1 =
      -n 0 / (2 * (1 - n 2)) := by
  simp [hopfSouthConnectionAlgebra, d9KroneckerDelta]

@[simp] private theorem hopfSouthConnectionAlgebra_two
    (n : Fin 3 → Real) :
    hopfSouthConnectionAlgebra n 2 = 0 := by
  simp [hopfSouthConnectionAlgebra, d9KroneckerDelta]

private theorem hopfSouthCovariantDirectional_zero_algebra
    (n : Fin 3 → Real) (s : Real)
    (hSqrtNe : s ≠ 0)
    (hMinus : 1 - n 2 ≠ 0)
    (hSqrtSq : s ^ 2 = 1 - n 2)
    (hSphere : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1) :
    hopfSouthFirstCovariantAlgebra n s 0 =
        (1 / 2 : Real) •
          (hopfSouthSecondScalarAlgebra s -
            Complex.ofReal (n 0) *
              hopfSouthFirstScalarAlgebra n s) ∧
      hopfSouthSecondCovariantAlgebra n s 0 =
        (1 / 2 : Real) •
          (hopfSouthFirstScalarAlgebra n s -
            Complex.ofReal (n 0) *
              hopfSouthSecondScalarAlgebra s) := by
  have hSqrtCube : s ^ 3 = s * (1 - n 2) := by
    calc
      s ^ 3 = s * s ^ 2 := by ring
      _ = s * (1 - n 2) := by rw [hSqrtSq]
  have hSqrtFourth : s ^ 4 = (1 - n 2) ^ 2 := by
    calc
      s ^ 4 = (s ^ 2) ^ 2 := by ring
      _ = (1 - n 2) ^ 2 := by rw [hSqrtSq]
  constructor <;>
    apply Complex.ext <;>
    simp only [hopfSouthFirstCovariantAlgebra,
      hopfSouthSecondCovariantAlgebra,
      hopfSouthFirstDerivativeAlgebra,
      hopfSouthSecondDerivativeAlgebra,
      hopfSouthFirstScalarAlgebra,
      hopfSouthSecondScalarAlgebra,
      hopfSouthConnectionAlgebra_zero,
      hopfSouthConnectionAlgebra_one,
      hopfSouthConnectionAlgebra_two,
      hopfTangentialIncrement_zero_zero,
      hopfTangentialIncrement_one_zero,
      hopfTangentialIncrement_two_zero,
      hopfTangentialIncrement_zero_one,
      hopfTangentialIncrement_one_one,
      hopfTangentialIncrement_two_one,
      hopfTangentialIncrement_zero_two,
      hopfTangentialIncrement_one_two,
      hopfTangentialIncrement_two_two,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.real_smul,
      zero_mul, mul_zero, one_mul, mul_one,
      zero_add, add_zero, sub_zero, zero_sub, neg_zero] <;>
    field_simp [hSqrtNe, hMinus] <;>
    (try simp only [hSqrtSq, hSqrtCube, hSqrtFourth]) <;>
    ring_nf <;>
    nlinarith [hSqrtSq, hSphere]

private theorem hopfSouthCovariantDirectional_one_algebra
    (n : Fin 3 → Real) (s : Real)
    (hSqrtNe : s ≠ 0)
    (hMinus : 1 - n 2 ≠ 0)
    (hSqrtSq : s ^ 2 = 1 - n 2)
    (hSphere : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1) :
    hopfSouthFirstCovariantAlgebra n s 1 =
        (1 / 2 : Real) •
          (Complex.I * hopfSouthSecondScalarAlgebra s -
            Complex.ofReal (n 1) *
              hopfSouthFirstScalarAlgebra n s) ∧
      hopfSouthSecondCovariantAlgebra n s 1 =
        (1 / 2 : Real) •
          (-Complex.I * hopfSouthFirstScalarAlgebra n s -
            Complex.ofReal (n 1) *
              hopfSouthSecondScalarAlgebra s) := by
  have hSqrtCube : s ^ 3 = s * (1 - n 2) := by
    calc
      s ^ 3 = s * s ^ 2 := by ring
      _ = s * (1 - n 2) := by rw [hSqrtSq]
  have hSqrtFourth : s ^ 4 = (1 - n 2) ^ 2 := by
    calc
      s ^ 4 = (s ^ 2) ^ 2 := by ring
      _ = (1 - n 2) ^ 2 := by rw [hSqrtSq]
  constructor <;>
    apply Complex.ext <;>
    simp only [hopfSouthFirstCovariantAlgebra,
      hopfSouthSecondCovariantAlgebra,
      hopfSouthFirstDerivativeAlgebra,
      hopfSouthSecondDerivativeAlgebra,
      hopfSouthFirstScalarAlgebra,
      hopfSouthSecondScalarAlgebra,
      hopfSouthConnectionAlgebra_zero,
      hopfSouthConnectionAlgebra_one,
      hopfSouthConnectionAlgebra_two,
      hopfTangentialIncrement_zero_zero,
      hopfTangentialIncrement_one_zero,
      hopfTangentialIncrement_two_zero,
      hopfTangentialIncrement_zero_one,
      hopfTangentialIncrement_one_one,
      hopfTangentialIncrement_two_one,
      hopfTangentialIncrement_zero_two,
      hopfTangentialIncrement_one_two,
      hopfTangentialIncrement_two_two,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.real_smul,
      zero_mul, mul_zero, one_mul, mul_one,
      zero_add, add_zero, sub_zero, zero_sub, neg_zero] <;>
    field_simp [hSqrtNe, hMinus] <;>
    (try simp only [hSqrtSq, hSqrtCube, hSqrtFourth]) <;>
    ring_nf <;>
    nlinarith [hSqrtSq, hSphere]

private theorem hopfSouthCovariantDirectional_two_algebra
    (n : Fin 3 → Real) (s : Real)
    (hSqrtNe : s ≠ 0)
    (hMinus : 1 - n 2 ≠ 0)
    (hSqrtSq : s ^ 2 = 1 - n 2)
    (hSphere : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1) :
    hopfSouthFirstCovariantAlgebra n s 2 =
        Complex.ofReal ((1 - n 2) / 2) *
          hopfSouthFirstScalarAlgebra n s ∧
      hopfSouthSecondCovariantAlgebra n s 2 =
        -Complex.ofReal ((1 + n 2) / 2) *
          hopfSouthSecondScalarAlgebra s := by
  have hSqrtCube : s ^ 3 = s * (1 - n 2) := by
    calc
      s ^ 3 = s * s ^ 2 := by ring
      _ = s * (1 - n 2) := by rw [hSqrtSq]
  have hSqrtFourth : s ^ 4 = (1 - n 2) ^ 2 := by
    calc
      s ^ 4 = (s ^ 2) ^ 2 := by ring
      _ = (1 - n 2) ^ 2 := by rw [hSqrtSq]
  constructor <;>
    apply Complex.ext <;>
    simp only [hopfSouthFirstCovariantAlgebra,
      hopfSouthSecondCovariantAlgebra,
      hopfSouthFirstDerivativeAlgebra,
      hopfSouthSecondDerivativeAlgebra,
      hopfSouthFirstScalarAlgebra,
      hopfSouthSecondScalarAlgebra,
      hopfSouthConnectionAlgebra_zero,
      hopfSouthConnectionAlgebra_one,
      hopfSouthConnectionAlgebra_two,
      hopfTangentialIncrement_zero_zero,
      hopfTangentialIncrement_one_zero,
      hopfTangentialIncrement_two_zero,
      hopfTangentialIncrement_zero_one,
      hopfTangentialIncrement_one_one,
      hopfTangentialIncrement_two_one,
      hopfTangentialIncrement_zero_two,
      hopfTangentialIncrement_one_two,
      hopfTangentialIncrement_two_two,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      zero_mul, mul_zero, one_mul, mul_one,
      zero_add, add_zero, sub_zero, zero_sub, neg_zero] <;>
    field_simp [hSqrtNe, hMinus] <;>
    (try simp only [hSqrtSq, hSqrtCube, hSqrtFourth]) <;>
    ring_nf <;>
    nlinarith [hSqrtSq, hSphere]

private theorem hopfSouthCovariantContraction_algebra
    (n : Fin 3 → Real) (s : Real)
    (hSqrtNe : s ≠ 0)
    (hMinus : 1 - n 2 ≠ 0)
    (hSqrtSq : s ^ 2 = 1 - n 2)
    (hSphere : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1) :
    (Complex.I * hopfSouthSecondCovariantAlgebra n s 0 -
          hopfSouthSecondCovariantAlgebra n s 1 +
        Complex.I * hopfSouthFirstCovariantAlgebra n s 2 =
      Complex.I * hopfSouthFirstScalarAlgebra n s) ∧
    (Complex.I * hopfSouthFirstCovariantAlgebra n s 0 +
          hopfSouthFirstCovariantAlgebra n s 1 -
        Complex.I * hopfSouthSecondCovariantAlgebra n s 2 =
      Complex.I * hopfSouthSecondScalarAlgebra s) := by
  have hSqrtCube : s ^ 3 = s * (1 - n 2) := by
    calc
      s ^ 3 = s * s ^ 2 := by ring
      _ = s * (1 - n 2) := by rw [hSqrtSq]
  have hSqrtFourth : s ^ 4 = (1 - n 2) ^ 2 := by
    calc
      s ^ 4 = (s ^ 2) ^ 2 := by ring
      _ = (1 - n 2) ^ 2 := by rw [hSqrtSq]
  constructor <;>
    apply Complex.ext <;>
    simp only [hopfSouthFirstCovariantAlgebra,
      hopfSouthSecondCovariantAlgebra,
      hopfSouthFirstDerivativeAlgebra,
      hopfSouthSecondDerivativeAlgebra,
      hopfSouthFirstScalarAlgebra,
      hopfSouthSecondScalarAlgebra,
      hopfSouthConnectionAlgebra_zero,
      hopfSouthConnectionAlgebra_one,
      hopfSouthConnectionAlgebra_two,
      hopfTangentialIncrement_zero_zero,
      hopfTangentialIncrement_one_zero,
      hopfTangentialIncrement_two_zero,
      hopfTangentialIncrement_zero_one,
      hopfTangentialIncrement_one_one,
      hopfTangentialIncrement_two_one,
      hopfTangentialIncrement_zero_two,
      hopfTangentialIncrement_one_two,
      hopfTangentialIncrement_two_two,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      zero_mul, mul_zero, one_mul, mul_one,
      zero_add, add_zero, sub_zero, zero_sub] <;>
    field_simp [hSqrtNe, hMinus] <;>
    simp only [hSqrtSq, hSqrtCube, hSqrtFourth] <;>
    ring_nf <;>
    nlinarith [hSqrtSq, hSphere]

private theorem d9HopfSouthCovariantContraction
    (point : ThroatCover period hPeriod)
    (hChart :
      d9MonopoleSphereCoverProjection period hPeriod point ∈
        monopoleChartDomain .south) :
    (Complex.I *
            d9HopfSecondCovariantFrameDerivative
              period hPeriod .south 0 point -
          d9HopfSecondCovariantFrameDerivative
            period hPeriod .south 1 point +
        Complex.I *
          d9HopfFirstCovariantFrameDerivative
            period hPeriod .south 2 point =
      Complex.I * d9HopfFirstScalar period hPeriod .south point) ∧
    (Complex.I *
            d9HopfFirstCovariantFrameDerivative
              period hPeriod .south 0 point +
          d9HopfFirstCovariantFrameDerivative
            period hPeriod .south 1 point -
        Complex.I *
          d9HopfSecondCovariantFrameDerivative
            period hPeriod .south 2 point =
      Complex.I * d9HopfSecondScalar period hPeriod .south point) := by
  have hPositive :=
    one_sub_monopoleSphereCoordinate_two_pos_of_mem_south
      (d9MonopoleSphereCoverProjection period hPeriod point) hChart
  rw [monopoleSphereCoordinate_d9MonopoleSphereCoverProjection] at hPositive
  have hSqrtNe :
      Real.sqrt
          (1 - d9UnitRadialCoordinate period hPeriod 2 point) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr hPositive
  have hSqrtSq :
      Real.sqrt
          (1 - d9UnitRadialCoordinate period hPeriod 2 point) ^ 2 =
        1 - d9UnitRadialCoordinate period hPeriod 2 point :=
    Real.sq_sqrt (le_of_lt hPositive)
  have hSphere :=
    d9UnitRadialCoordinate_norm_sq period hPeriod point
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hSphere
  norm_num at hSphere
  let n : Fin 3 → Real :=
    fun direction =>
      d9UnitRadialCoordinate period hPeriod direction point
  have hSphereAlgebra :
      n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1 := by
    dsimp only [n]
    nlinarith [hSphere]
  have hAlgebra :=
    hopfSouthCovariantContraction_algebra n
      (Real.sqrt (1 - n 2))
      hSqrtNe (ne_of_gt hPositive) hSqrtSq hSphereAlgebra
  simpa [n, d9HopfFirstCovariantFrameDerivative,
    d9HopfSecondCovariantFrameDerivative,
    d9HopfFirstFrameDerivative, d9HopfSecondFrameDerivative,
    d9HopfSouthFirstFrameDerivative,
    d9HopfSouthSecondFrameDerivative,
    d9HopfFirstScalar, d9HopfSecondScalar,
    primitiveMonopoleZeroLocalValue,
    primitiveMonopoleZeroComplementLocalValue,
    primitiveMonopoleZeroSouthValue,
    primitiveMonopoleZeroComplementSouthValue,
    d9HopfMonopoleFrameCoefficient_south,
    hopfSouthFirstCovariantAlgebra,
    hopfSouthSecondCovariantAlgebra,
    hopfSouthFirstDerivativeAlgebra,
    hopfSouthSecondDerivativeAlgebra,
    hopfSouthConnectionAlgebra,
    hopfSouthFirstScalarAlgebra,
    hopfSouthSecondScalarAlgebra,
    hopfTangentialIncrement,
    monopoleSphereCoordinate_d9MonopoleSphereCoverProjection,
    monopoleSphereXY_d9MonopoleSphereCoverProjection,
    Complex.real_smul, mul_add] using hAlgebra

private theorem d9HopfCovariantDirectionalCoefficients
    (point : ThroatCover period hPeriod)
    (chart : MonopoleChart) (direction : Fin 3)
    (hChart :
      d9MonopoleSphereCoverProjection period hPeriod point ∈
        monopoleChartDomain chart) :
    d9HopfFirstCovariantFrameDerivative
        period hPeriod chart direction point =
        hopfDirectionalFirstCovariantTarget
          (fun coordinate =>
            d9UnitRadialCoordinate period hPeriod coordinate point)
          (d9HopfFirstScalar period hPeriod chart point)
          (d9HopfSecondScalar period hPeriod chart point) direction ∧
      d9HopfSecondCovariantFrameDerivative
          period hPeriod chart direction point =
        hopfDirectionalSecondCovariantTarget
          (fun coordinate =>
            d9UnitRadialCoordinate period hPeriod coordinate point)
          (d9HopfFirstScalar period hPeriod chart point)
          (d9HopfSecondScalar period hPeriod chart point) direction := by
  have hDirection :
      direction = 0 ∨ direction = 1 ∨ direction = 2 := by
    omega
  cases chart with
  | north =>
      have hPositive :=
        one_add_monopoleSphereCoordinate_two_pos_of_mem_north
          (d9MonopoleSphereCoverProjection period hPeriod point) hChart
      rw [monopoleSphereCoordinate_d9MonopoleSphereCoverProjection]
        at hPositive
      have hSqrtNe :
          Real.sqrt
              (1 + d9UnitRadialCoordinate period hPeriod 2 point) ≠ 0 :=
        Real.sqrt_ne_zero'.mpr hPositive
      have hSqrtSq :
          Real.sqrt
              (1 + d9UnitRadialCoordinate period hPeriod 2 point) ^ 2 =
            1 + d9UnitRadialCoordinate period hPeriod 2 point :=
        Real.sq_sqrt (le_of_lt hPositive)
      have hSphere := d9UnitRadialCoordinate_norm_sq period hPeriod point
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hSphere
      norm_num at hSphere
      let n : Fin 3 → Real :=
        fun coordinate =>
          d9UnitRadialCoordinate period hPeriod coordinate point
      have hSphereAlgebra :
          n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1 := by
        dsimp only [n]
        nlinarith [hSphere]
      rcases hDirection with rfl | rfl | rfl
      · have hAlgebra :=
          hopfNorthCovariantDirectional_zero_algebra n
            (Real.sqrt (1 + n 2))
            hSqrtNe (ne_of_gt hPositive) hSqrtSq hSphereAlgebra
        simpa [n, hopfDirectionalFirstCovariantTarget,
          hopfDirectionalSecondCovariantTarget,
          d9HopfFirstCovariantFrameDerivative,
          d9HopfSecondCovariantFrameDerivative,
          d9HopfFirstFrameDerivative, d9HopfSecondFrameDerivative,
          d9HopfNorthFirstFrameDerivative,
          d9HopfNorthSecondFrameDerivative,
          d9HopfFirstScalar, d9HopfSecondScalar,
          primitiveMonopoleZeroLocalValue,
          primitiveMonopoleZeroComplementLocalValue,
          primitiveMonopoleZeroNorthValue,
          primitiveMonopoleZeroComplementNorthValue,
          d9HopfMonopoleFrameCoefficient_north,
          hopfNorthFirstCovariantAlgebra,
          hopfNorthSecondCovariantAlgebra,
          hopfNorthFirstDerivativeAlgebra,
          hopfNorthSecondDerivativeAlgebra,
          hopfNorthConnectionAlgebra,
          hopfNorthFirstScalarAlgebra,
          hopfNorthSecondScalarAlgebra,
          hopfTangentialIncrement,
          monopoleSphereCoordinate_d9MonopoleSphereCoverProjection,
          star_monopoleSphereXY_d9MonopoleSphereCoverProjection,
          Complex.real_smul] using hAlgebra
      · have hAlgebra :=
          hopfNorthCovariantDirectional_one_algebra n
            (Real.sqrt (1 + n 2))
            hSqrtNe (ne_of_gt hPositive) hSqrtSq hSphereAlgebra
        simpa [n, hopfDirectionalFirstCovariantTarget,
          hopfDirectionalSecondCovariantTarget,
          d9HopfFirstCovariantFrameDerivative,
          d9HopfSecondCovariantFrameDerivative,
          d9HopfFirstFrameDerivative, d9HopfSecondFrameDerivative,
          d9HopfNorthFirstFrameDerivative,
          d9HopfNorthSecondFrameDerivative,
          d9HopfFirstScalar, d9HopfSecondScalar,
          primitiveMonopoleZeroLocalValue,
          primitiveMonopoleZeroComplementLocalValue,
          primitiveMonopoleZeroNorthValue,
          primitiveMonopoleZeroComplementNorthValue,
          d9HopfMonopoleFrameCoefficient_north,
          hopfNorthFirstCovariantAlgebra,
          hopfNorthSecondCovariantAlgebra,
          hopfNorthFirstDerivativeAlgebra,
          hopfNorthSecondDerivativeAlgebra,
          hopfNorthConnectionAlgebra,
          hopfNorthFirstScalarAlgebra,
          hopfNorthSecondScalarAlgebra,
          hopfTangentialIncrement,
          monopoleSphereCoordinate_d9MonopoleSphereCoverProjection,
          star_monopoleSphereXY_d9MonopoleSphereCoverProjection,
          Complex.real_smul] using hAlgebra
      · have hAlgebra :=
          hopfNorthCovariantDirectional_two_algebra n
            (Real.sqrt (1 + n 2))
            hSqrtNe (ne_of_gt hPositive) hSqrtSq hSphereAlgebra
        simpa [n, hopfDirectionalFirstCovariantTarget,
          hopfDirectionalSecondCovariantTarget,
          d9HopfFirstCovariantFrameDerivative,
          d9HopfSecondCovariantFrameDerivative,
          d9HopfFirstFrameDerivative, d9HopfSecondFrameDerivative,
          d9HopfNorthFirstFrameDerivative,
          d9HopfNorthSecondFrameDerivative,
          d9HopfFirstScalar, d9HopfSecondScalar,
          primitiveMonopoleZeroLocalValue,
          primitiveMonopoleZeroComplementLocalValue,
          primitiveMonopoleZeroNorthValue,
          primitiveMonopoleZeroComplementNorthValue,
          d9HopfMonopoleFrameCoefficient_north,
          hopfNorthFirstCovariantAlgebra,
          hopfNorthSecondCovariantAlgebra,
          hopfNorthFirstDerivativeAlgebra,
          hopfNorthSecondDerivativeAlgebra,
          hopfNorthConnectionAlgebra,
          hopfNorthFirstScalarAlgebra,
          hopfNorthSecondScalarAlgebra,
          hopfTangentialIncrement,
          monopoleSphereCoordinate_d9MonopoleSphereCoverProjection,
          star_monopoleSphereXY_d9MonopoleSphereCoverProjection,
          Complex.real_smul] using hAlgebra
  | south =>
      have hPositive :=
        one_sub_monopoleSphereCoordinate_two_pos_of_mem_south
          (d9MonopoleSphereCoverProjection period hPeriod point) hChart
      rw [monopoleSphereCoordinate_d9MonopoleSphereCoverProjection]
        at hPositive
      have hSqrtNe :
          Real.sqrt
              (1 - d9UnitRadialCoordinate period hPeriod 2 point) ≠ 0 :=
        Real.sqrt_ne_zero'.mpr hPositive
      have hSqrtSq :
          Real.sqrt
              (1 - d9UnitRadialCoordinate period hPeriod 2 point) ^ 2 =
            1 - d9UnitRadialCoordinate period hPeriod 2 point :=
        Real.sq_sqrt (le_of_lt hPositive)
      have hSphere := d9UnitRadialCoordinate_norm_sq period hPeriod point
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hSphere
      norm_num at hSphere
      let n : Fin 3 → Real :=
        fun coordinate =>
          d9UnitRadialCoordinate period hPeriod coordinate point
      have hSphereAlgebra :
          n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1 := by
        dsimp only [n]
        nlinarith [hSphere]
      rcases hDirection with rfl | rfl | rfl
      · have hAlgebra :=
          hopfSouthCovariantDirectional_zero_algebra n
            (Real.sqrt (1 - n 2))
            hSqrtNe (ne_of_gt hPositive) hSqrtSq hSphereAlgebra
        simpa [n, hopfDirectionalFirstCovariantTarget,
          hopfDirectionalSecondCovariantTarget,
          d9HopfFirstCovariantFrameDerivative,
          d9HopfSecondCovariantFrameDerivative,
          d9HopfFirstFrameDerivative, d9HopfSecondFrameDerivative,
          d9HopfSouthFirstFrameDerivative,
          d9HopfSouthSecondFrameDerivative,
          d9HopfFirstScalar, d9HopfSecondScalar,
          primitiveMonopoleZeroLocalValue,
          primitiveMonopoleZeroComplementLocalValue,
          primitiveMonopoleZeroSouthValue,
          primitiveMonopoleZeroComplementSouthValue,
          d9HopfMonopoleFrameCoefficient_south,
          hopfSouthFirstCovariantAlgebra,
          hopfSouthSecondCovariantAlgebra,
          hopfSouthFirstDerivativeAlgebra,
          hopfSouthSecondDerivativeAlgebra,
          hopfSouthConnectionAlgebra,
          hopfSouthFirstScalarAlgebra,
          hopfSouthSecondScalarAlgebra,
          hopfTangentialIncrement,
          monopoleSphereCoordinate_d9MonopoleSphereCoverProjection,
          monopoleSphereXY_d9MonopoleSphereCoverProjection,
          Complex.real_smul, mul_add] using hAlgebra
      · have hAlgebra :=
          hopfSouthCovariantDirectional_one_algebra n
            (Real.sqrt (1 - n 2))
            hSqrtNe (ne_of_gt hPositive) hSqrtSq hSphereAlgebra
        simpa [n, hopfDirectionalFirstCovariantTarget,
          hopfDirectionalSecondCovariantTarget,
          d9HopfFirstCovariantFrameDerivative,
          d9HopfSecondCovariantFrameDerivative,
          d9HopfFirstFrameDerivative, d9HopfSecondFrameDerivative,
          d9HopfSouthFirstFrameDerivative,
          d9HopfSouthSecondFrameDerivative,
          d9HopfFirstScalar, d9HopfSecondScalar,
          primitiveMonopoleZeroLocalValue,
          primitiveMonopoleZeroComplementLocalValue,
          primitiveMonopoleZeroSouthValue,
          primitiveMonopoleZeroComplementSouthValue,
          d9HopfMonopoleFrameCoefficient_south,
          hopfSouthFirstCovariantAlgebra,
          hopfSouthSecondCovariantAlgebra,
          hopfSouthFirstDerivativeAlgebra,
          hopfSouthSecondDerivativeAlgebra,
          hopfSouthConnectionAlgebra,
          hopfSouthFirstScalarAlgebra,
          hopfSouthSecondScalarAlgebra,
          hopfTangentialIncrement,
          monopoleSphereCoordinate_d9MonopoleSphereCoverProjection,
          monopoleSphereXY_d9MonopoleSphereCoverProjection,
          Complex.real_smul, mul_add] using hAlgebra
      · have hAlgebra :=
          hopfSouthCovariantDirectional_two_algebra n
            (Real.sqrt (1 - n 2))
            hSqrtNe (ne_of_gt hPositive) hSqrtSq hSphereAlgebra
        simpa [n, hopfDirectionalFirstCovariantTarget,
          hopfDirectionalSecondCovariantTarget,
          d9HopfFirstCovariantFrameDerivative,
          d9HopfSecondCovariantFrameDerivative,
          d9HopfFirstFrameDerivative, d9HopfSecondFrameDerivative,
          d9HopfSouthFirstFrameDerivative,
          d9HopfSouthSecondFrameDerivative,
          d9HopfFirstScalar, d9HopfSecondScalar,
          primitiveMonopoleZeroLocalValue,
          primitiveMonopoleZeroComplementLocalValue,
          primitiveMonopoleZeroSouthValue,
          primitiveMonopoleZeroComplementSouthValue,
          d9HopfMonopoleFrameCoefficient_south,
          hopfSouthFirstCovariantAlgebra,
          hopfSouthSecondCovariantAlgebra,
          hopfSouthFirstDerivativeAlgebra,
          hopfSouthSecondDerivativeAlgebra,
          hopfSouthConnectionAlgebra,
          hopfSouthFirstScalarAlgebra,
          hopfSouthSecondScalarAlgebra,
          hopfTangentialIncrement,
          monopoleSphereCoordinate_d9MonopoleSphereCoverProjection,
          monopoleSphereXY_d9MonopoleSphereCoverProjection,
          Complex.real_smul, mul_add] using hAlgebra

private theorem d9PrimitiveSpinCImaginaryAction_complexAction
    (scalar : Complex) (matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCImaginaryAction
        (d9PrimitiveSpinCComplexActionCLM scalar matter) =
      d9PrimitiveSpinCComplexActionCLM scalar
        (d9PrimitiveSpinCImaginaryAction matter) := by
  apply d9DoubledMatterFiberHalfSpinorLinearEquiv.injective
  simp only [
    d9DoubledMatterFiberHalfSpinorLinearEquiv_complexAction,
    d9PrimitiveSpinCImaginaryAction,
    d9DoubledMatterFiberHalfSpinorLinearEquiv_phaseAction,
    d9PrimitiveSpinCImaginaryPhase_coe, smul_smul]
  rw [mul_comm]

private theorem
    d9PrimitiveSpinCHopfFrameCombination_directional_target
    (sector : NormalRootChoice) (matter : D9DoubledMatterFiber)
    (n : Fin 3 → Real) (firstScalar secondScalar : Complex)
    (direction : Fin 3)
    (hZero :
      d9DoubledMatterFiberCliffordGammaCLM 0 matter =
        d9PrimitiveSpinCImaginaryAction matter)
    (hOne :
      d9DoubledMatterFiberCliffordGammaCLM 1 matter =
        d9PrimitiveSpinCImaginaryAction
          (d9DoubledMatterFiberCliffordGammaCLM 2 matter)) :
    d9PrimitiveSpinCHopfFrameCombination sector matter
        (hopfDirectionalFirstCovariantTarget
          n firstScalar secondScalar direction)
        (hopfDirectionalSecondCovariantTarget
          n firstScalar secondScalar direction) =
      -(1 / 2 : Real) •
        (d9PrimitiveSpinCImaginaryAction
            (d9DoubledMatterFiberCliffordGammaCLM direction
              (d9PrimitiveSpinCHopfFrameCombination sector matter
                firstScalar secondScalar)) +
          n direction •
            d9PrimitiveSpinCHopfFrameCombination sector matter
              firstScalar secondScalar) := by
  have hZeroFirst :=
    d9PrimitiveSpinCHopfFirstFrameCLM_gamma_zero_of
      sector matter hZero
  have hZeroSecond :=
    d9PrimitiveSpinCHopfSecondFrameCLM_gamma_zero_of
      sector matter hZero
  have hOneFirst :=
    d9PrimitiveSpinCHopfFirstFrameCLM_gamma_one_of
      sector matter hOne
  have hOneSecond :=
    d9PrimitiveSpinCHopfSecondFrameCLM_gamma_one_of
      sector matter hOne
  have hTwoFirst :=
    d9PrimitiveSpinCHopfFirstFrameCLM_gamma_two sector matter
  have hTwoSecond :=
    d9PrimitiveSpinCHopfSecondFrameCLM_gamma_two sector matter
  have hDirection :
      direction = 0 ∨ direction = 1 ∨ direction = 2 := by
    omega
  rcases hDirection with rfl | rfl | rfl
  · have hFirstTarget :
        hopfDirectionalFirstCovariantTarget
            n firstScalar secondScalar 0 =
          (1 / 2 : Real) •
            (secondScalar - Complex.ofReal (n 0) * firstScalar) := by
      simp [hopfDirectionalFirstCovariantTarget]
    have hSecondTarget :
        hopfDirectionalSecondCovariantTarget
            n firstScalar secondScalar 0 =
          (1 / 2 : Real) •
            (firstScalar - Complex.ofReal (n 0) * secondScalar) := by
      simp [hopfDirectionalSecondCovariantTarget]
    rw [hFirstTarget, hSecondTarget]
    unfold d9PrimitiveSpinCHopfFrameCombination
    simp only [map_add]
    rw [← d9PrimitiveSpinCComplexAction_clifford firstScalar 0,
      ← d9PrimitiveSpinCComplexAction_clifford secondScalar 0,
      hZeroFirst, hZeroSecond]
    simp_rw [d9PrimitiveSpinCImaginaryAction_complexAction]
    simp_rw [d9PrimitiveSpinCImaginaryAction_sq]
    apply d9DoubledMatterFiberHalfSpinorLinearEquiv.injective
    simp only [map_add, map_neg, map_smul,
      d9DoubledMatterFiberHalfSpinorLinearEquiv_complexAction,
      d9PrimitiveSpinCImaginaryAction,
      d9DoubledMatterFiberHalfSpinorLinearEquiv_phaseAction,
      d9PrimitiveSpinCImaginaryPhase_coe]
    simp_rw [d9DoubledMatterSpinor_real_smul_eq_complex]
    simp only [Complex.real_smul, smul_smul, Complex.I_mul_I,
      neg_one_smul] <;> module
  · have hFirstTarget :
        hopfDirectionalFirstCovariantTarget
            n firstScalar secondScalar 1 =
          (1 / 2 : Real) •
            (Complex.I * secondScalar -
              Complex.ofReal (n 1) * firstScalar) := by
      simp [hopfDirectionalFirstCovariantTarget]
    have hSecondTarget :
        hopfDirectionalSecondCovariantTarget
            n firstScalar secondScalar 1 =
          (1 / 2 : Real) •
            (-Complex.I * firstScalar -
              Complex.ofReal (n 1) * secondScalar) := by
      simp [hopfDirectionalSecondCovariantTarget]
    rw [hFirstTarget, hSecondTarget]
    unfold d9PrimitiveSpinCHopfFrameCombination
    simp only [map_add]
    rw [← d9PrimitiveSpinCComplexAction_clifford firstScalar 1,
      ← d9PrimitiveSpinCComplexAction_clifford secondScalar 1,
      hOneFirst, hOneSecond]
    simp_rw [d9PrimitiveSpinCImaginaryAction_complexAction]
    apply d9DoubledMatterFiberHalfSpinorLinearEquiv.injective
    simp only [map_add, map_neg, map_smul,
      d9DoubledMatterFiberHalfSpinorLinearEquiv_complexAction,
      d9PrimitiveSpinCImaginaryAction,
      d9DoubledMatterFiberHalfSpinorLinearEquiv_phaseAction,
      d9PrimitiveSpinCImaginaryPhase_coe]
    simp_rw [d9DoubledMatterSpinor_real_smul_eq_complex]
    simp only [Complex.real_smul, smul_smul, Complex.I_mul_I,
      neg_one_smul] <;> module
  · have hFirstTarget :
        hopfDirectionalFirstCovariantTarget
            n firstScalar secondScalar 2 =
          Complex.ofReal ((1 - n 2) / 2) * firstScalar := by
      simp [hopfDirectionalFirstCovariantTarget]
    have hSecondTarget :
        hopfDirectionalSecondCovariantTarget
            n firstScalar secondScalar 2 =
          -Complex.ofReal ((1 + n 2) / 2) * secondScalar := by
      simp [hopfDirectionalSecondCovariantTarget]
    rw [hFirstTarget, hSecondTarget]
    unfold d9PrimitiveSpinCHopfFrameCombination
    simp only [map_add]
    rw [← d9PrimitiveSpinCComplexAction_clifford firstScalar 2,
      ← d9PrimitiveSpinCComplexAction_clifford secondScalar 2,
      hTwoFirst, hTwoSecond]
    simp_rw [d9PrimitiveSpinCImaginaryAction_complexAction]
    simp_rw [d9PrimitiveSpinCImaginaryAction_sq]
    apply d9DoubledMatterFiberHalfSpinorLinearEquiv.injective
    simp only [map_add, map_neg, map_smul,
      d9DoubledMatterFiberHalfSpinorLinearEquiv_complexAction,
      d9PrimitiveSpinCImaginaryAction,
      d9DoubledMatterFiberHalfSpinorLinearEquiv_phaseAction,
      d9PrimitiveSpinCImaginaryPhase_coe]
    simp_rw [d9DoubledMatterSpinor_real_smul_eq_complex]
    simp only [Complex.real_smul, smul_smul, Complex.I_mul_I,
      neg_one_smul] <;> module

/-- At the anchor of a normal chart, differentiating the local coordinate of
an upstairs doubled lift is exactly differentiating that lift upstairs. -/
private theorem doubledSpinorLiftLocalValue_mfderiv_intrinsicFrame_mk
    (choice : NormalRootChoice)
    (lift : SmoothThroatDoubledMatterSpinorLift
      period hPeriod choice)
    (anchor : ThroatCover period hPeriod) (direction : Fin 3) :
    NormedSpace.fromTangentSpace (𝕜 := Real)
        (E := D9DoubledMatterFiber)
        (doubledSpinorLiftLocalValue period hPeriod choice lift anchor
          (mappingTorusMk (ThroatData period hPeriod) anchor))
        (mfderiv throatCoverModelWithCorners
          𝓘(Real, D9DoubledMatterFiber)
          (doubledSpinorLiftLocalValue
            period hPeriod choice lift anchor)
          (mappingTorusMk (ThroatData period hPeriod) anchor)
          (d9IntrinsicThroatFrame period hPeriod direction
            (mappingTorusMk (ThroatData period hPeriod) anchor))) =
      NormedSpace.fromTangentSpace (𝕜 := Real)
        (E := D9DoubledMatterFiber) (lift anchor)
        (mfderiv throatCoverModelWithCorners
          𝓘(Real, D9DoubledMatterFiber) lift anchor
          (d9IntrinsicThroatCoverFrame
            period hPeriod direction anchor)) := by
  let projection :=
    mappingTorusMk (ThroatData period hPeriod)
  let localInverse :=
    (throatProjectionLocalHomeomorph period hPeriod).localInverseAt anchor
  let base := projection anchor
  have hBase : base ∈ normalBundleBaseSet period hPeriod anchor := by
    exact
      (throatProjectionLocalHomeomorph period hPeriod)
        |>.apply_self_mem_localInverseAt_source
  have hTarget : localInverse.target ∈ nhds anchor :=
    localInverse.open_target.mem_nhds
      ((throatProjectionLocalHomeomorph period hPeriod)
        |>.self_mem_localInverseAt_target)
  have hEventually :
      (doubledSpinorLiftLocalValue
          period hPeriod choice lift anchor) ∘ projection =ᶠ[nhds anchor]
        lift := by
    filter_upwards [hTarget] with current hCurrent
    have hSymm :
        localInverse.symm current = projection current := by
      exact congrFun
        ((throatProjectionLocalHomeomorph period hPeriod)
          |>.localInverseAt_symm anchor) current
    have hSource :
        projection current ∈ normalBundleBaseSet period hPeriod anchor := by
      change projection current ∈ localInverse.source
      rw [← hSymm]
      exact localInverse.map_target hCurrent
    have hRight := localInverse.right_inv hCurrent
    rw [hSymm] at hRight
    dsimp only [Function.comp_apply]
    unfold doubledSpinorLiftLocalValue
    rw [d9DoubledMatterSpinorBundleSection_localTriv
      period hPeriod choice lift anchor (projection current) hSource]
    exact congrArg lift hRight
  have hLocal :
      MDifferentiableAt throatCoverModelWithCorners
        𝓘(Real, D9DoubledMatterFiber)
        (doubledSpinorLiftLocalValue
          period hPeriod choice lift anchor) base := by
    exact
      ((doubledSpinorLiftLocalValue_contMDiffOn
        period hPeriod choice lift anchor).contMDiffAt
          ((normalBundleBaseSet_isOpen period hPeriod anchor).mem_nhds
            hBase)).mdifferentiableAt (by simp)
  have hProjection :
      MDifferentiableAt throatCoverModelWithCorners
        throatCoverModelWithCorners projection anchor :=
    (fixedThroat_projection_isLocalDiffeomorph
      period hPeriod).contMDiff.mdifferentiableAt (by simp)
  have hChain :=
    mfderiv_comp_apply anchor hLocal hProjection
      (d9IntrinsicThroatCoverFrame period hPeriod direction anchor)
  change
    mfderiv throatCoverModelWithCorners
        𝓘(Real, D9DoubledMatterFiber)
        ((doubledSpinorLiftLocalValue
          period hPeriod choice lift anchor) ∘ projection) anchor
        (d9IntrinsicThroatCoverFrame
          period hPeriod direction anchor) =
      mfderiv throatCoverModelWithCorners
          𝓘(Real, D9DoubledMatterFiber)
          (doubledSpinorLiftLocalValue
            period hPeriod choice lift anchor) base
          (mfderiv throatCoverModelWithCorners
            throatCoverModelWithCorners projection anchor
            (d9IntrinsicThroatCoverFrame
              period hPeriod direction anchor)) at hChain
  have hFrame :=
    d9IntrinsicThroatFrame_mk period hPeriod direction anchor
  change
    d9IntrinsicThroatFrame period hPeriod direction
        base =
      mfderiv throatCoverModelWithCorners throatCoverModelWithCorners
        projection anchor
        (d9IntrinsicThroatCoverFrame
          period hPeriod direction anchor) at hFrame
  have hChainFiber := congrArg
    (NormedSpace.fromTangentSpace (𝕜 := Real)
      (E := D9DoubledMatterFiber)
      (doubledSpinorLiftLocalValue
        period hPeriod choice lift anchor base))
    hChain
  have hDerivative :
      mfderiv throatCoverModelWithCorners
          𝓘(Real, D9DoubledMatterFiber)
          ((doubledSpinorLiftLocalValue
            period hPeriod choice lift anchor) ∘ projection) anchor =
        mfderiv throatCoverModelWithCorners
          𝓘(Real, D9DoubledMatterFiber)
          (fun current : ThroatCover period hPeriod =>
            (lift.first.toFun current, lift.second.toFun current)) anchor :=
    Filter.EventuallyEq.mfderiv_eq
      (I := throatCoverModelWithCorners)
      (I' := 𝓘(Real, D9DoubledMatterFiber)) hEventually
  have hDerivativeApply := congrArg
    (fun derivative =>
      derivative
        (d9IntrinsicThroatCoverFrame
          period hPeriod direction anchor))
    hDerivative
  have hDerivativeFiber := congrArg
    (NormedSpace.fromTangentSpace (𝕜 := Real)
      (E := D9DoubledMatterFiber)
      (doubledSpinorLiftLocalValue
        period hPeriod choice lift anchor base))
    hDerivativeApply
  change
    NormedSpace.fromTangentSpace (𝕜 := Real)
        (E := D9DoubledMatterFiber)
        (doubledSpinorLiftLocalValue
          period hPeriod choice lift anchor base)
        (mfderiv throatCoverModelWithCorners
          𝓘(Real, D9DoubledMatterFiber)
          (doubledSpinorLiftLocalValue
            period hPeriod choice lift anchor) base
          (d9IntrinsicThroatFrame period hPeriod direction base)) =
      NormedSpace.fromTangentSpace (𝕜 := Real)
        (E := D9DoubledMatterFiber)
        (doubledSpinorLiftLocalValue
          period hPeriod choice lift anchor base)
        (mfderiv throatCoverModelWithCorners
          𝓘(Real, D9DoubledMatterFiber)
          (fun current : ThroatCover period hPeriod =>
            (lift.first.toFun current, lift.second.toFun current)) anchor
          (d9IntrinsicThroatCoverFrame
            period hPeriod direction anchor))
  rw [hFrame]
  rw [← hChainFiber]
  exact hDerivativeFiber

private theorem doubledSpinorMappedLiftLocalValue_mfderiv_intrinsicFrame_mk
    (map : D9DoubledMatterFiber →L[Real] D9DoubledMatterFiber)
    (hMap :
      ∀ winding matter,
        map (d9DoubledMatterSpinorMonodromy
            .positiveQuarter winding matter) =
          d9DoubledMatterSpinorMonodromy .positiveQuarter winding
            (map matter))
    (lift : SmoothThroatDoubledMatterSpinorLift
      period hPeriod .positiveQuarter)
    (anchor : ThroatCover period hPeriod) (direction : Fin 3) :
    NormedSpace.fromTangentSpace (𝕜 := Real)
        (E := D9DoubledMatterFiber)
        (doubledSpinorLiftLocalValue period hPeriod .positiveQuarter
          (d9PrimitiveSpinCMapDoubledLift
            period hPeriod map hMap lift)
          anchor (mappingTorusMk (ThroatData period hPeriod) anchor))
        (mfderiv throatCoverModelWithCorners
          𝓘(Real, D9DoubledMatterFiber)
          (doubledSpinorLiftLocalValue period hPeriod .positiveQuarter
            (d9PrimitiveSpinCMapDoubledLift
              period hPeriod map hMap lift)
            anchor)
          (mappingTorusMk (ThroatData period hPeriod) anchor)
          (d9IntrinsicThroatFrame period hPeriod direction
            (mappingTorusMk (ThroatData period hPeriod) anchor))) =
      map
        (NormedSpace.fromTangentSpace (𝕜 := Real)
          (E := D9DoubledMatterFiber) (lift anchor)
          (mfderiv throatCoverModelWithCorners
            𝓘(Real, D9DoubledMatterFiber) lift anchor
            (d9IntrinsicThroatCoverFrame
              period hPeriod direction anchor))) := by
  let mapped :=
    d9PrimitiveSpinCMapDoubledLift
      period hPeriod map hMap lift
  have hLift :
      MDifferentiableAt throatCoverModelWithCorners
        𝓘(Real, D9DoubledMatterFiber) lift anchor :=
    lift.contMDiff_toFun.mdifferentiableAt (by simp)
  have hOuter :
      MDifferentiableAt 𝓘(Real, D9DoubledMatterFiber)
        𝓘(Real, D9DoubledMatterFiber) map (lift anchor) :=
    map.differentiableAt.mdifferentiableAt
  have hChain :=
    mfderiv_comp_apply anchor hOuter hLift
      (d9IntrinsicThroatCoverFrame
        period hPeriod direction anchor)
  have hFunction :
      mapped = map ∘ lift := by
    funext current
    exact d9PrimitiveSpinCMapDoubledLift_apply
      period hPeriod map hMap lift current
  rw [← hFunction] at hChain
  have hBridge :=
    doubledSpinorLiftLocalValue_mfderiv_intrinsicFrame_mk
      period hPeriod .positiveQuarter mapped anchor direction
  rw [hBridge]
  rw [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv] at hChain
  change
    mfderiv throatCoverModelWithCorners
        𝓘(Real, D9DoubledMatterFiber) mapped anchor
        (d9IntrinsicThroatCoverFrame
          period hPeriod direction anchor) =
      map
        (mfderiv throatCoverModelWithCorners
          𝓘(Real, D9DoubledMatterFiber) lift anchor
          (d9IntrinsicThroatCoverFrame
            period hPeriod direction anchor))
  exact hChain

private theorem d9PrimitiveSpinCHopfFirstFrameCLM_imaginary
    (sector : NormalRootChoice) (matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCHopfFirstFrameCLM sector
        (d9PrimitiveSpinCImaginaryAction matter) =
      d9PrimitiveSpinCImaginaryAction
        (d9PrimitiveSpinCHopfFirstFrameCLM sector matter) := by
  simp only [d9PrimitiveSpinCHopfFirstFrameCLM_apply, map_sub]
  rw [← d9PrimitiveSpinCImaginaryAction_clifford]

private theorem d9PrimitiveSpinCHopfSecondFrameCLM_imaginary
    (sector : NormalRootChoice) (matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCHopfSecondFrameCLM sector
        (d9PrimitiveSpinCImaginaryAction matter) =
      d9PrimitiveSpinCImaginaryAction
        (d9PrimitiveSpinCHopfSecondFrameCLM sector matter) := by
  simp only [d9PrimitiveSpinCHopfSecondFrameCLM_apply, map_add]
  rw [← d9PrimitiveSpinCImaginaryAction_clifford]

private theorem d9PrimitiveSpinCComplexAction_imaginary
    (scalar : Complex) (matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCComplexActionCLM scalar
        (d9PrimitiveSpinCImaginaryAction matter) =
      d9PrimitiveSpinCImaginaryAction
        (d9PrimitiveSpinCComplexActionCLM scalar matter) := by
  change
    d9PrimitiveSpinCComplexActionCLM scalar
        (d9PrimitiveSpinCComplexActionCLM Complex.I matter) =
      d9PrimitiveSpinCComplexActionCLM Complex.I
        (d9PrimitiveSpinCComplexActionCLM scalar matter)
  rw [← d9PrimitiveSpinCComplexAction_mul,
    ← d9PrimitiveSpinCComplexAction_mul, mul_comm]

private theorem primitiveSpinCNormalModeDoubledLift_fromTangentSpace_mfderiv
    (sector : NormalRootChoice) (mode : Int)
    (direction : Fin 3) (point : ThroatCover period hPeriod) :
    NormedSpace.fromTangentSpace (𝕜 := Real)
        (E := D9DoubledMatterFiber)
        (primitiveSpinCNormalModeDoubledLift
          period hPeriod sector mode point)
        (mfderiv throatCoverModelWithCorners
          𝓘(Real, D9DoubledMatterFiber)
          (primitiveSpinCNormalModeDoubledLift
            period hPeriod sector mode)
          point
          (d9IntrinsicThroatCoverFrame
            period hPeriod direction point)) =
      (normalRootSpinFrameFrequency period sector mode *
          d9UnitRadialCoordinate period hPeriod direction point) •
        d9PrimitiveSpinCImaginaryAction
          (primitiveSpinCNormalModeDoubledLift
            period hPeriod sector mode point) := by
  have hDerivative :=
    primitiveSpinCNormalModeDoubledLift_mfderiv_intrinsicFrame
      period hPeriod sector mode direction point
  have hFiber := congrArg
    (NormedSpace.fromTangentSpace (𝕜 := Real)
      (E := D9DoubledMatterFiber)
      (primitiveSpinCNormalModeDoubledLift
        period hPeriod sector mode point))
    hDerivative
  change
    NormedSpace.fromTangentSpace (𝕜 := Real)
        (E := D9DoubledMatterFiber)
        (primitiveSpinCNormalModeDoubledLift
          period hPeriod sector mode point)
        (mfderiv throatCoverModelWithCorners
          𝓘(Real, D9DoubledMatterFiber)
          (primitiveSpinCNormalModeDoubledLift
            period hPeriod sector mode)
          point
          (d9IntrinsicThroatCoverFrame
            period hPeriod direction point)) =
      (normalRootSpinFrameFrequency period sector mode *
          d9UnitRadialCoordinate period hPeriod direction point) •
        d9PrimitiveSpinCImaginaryAction
          (primitiveSpinCNormalModeDoubledLift
            period hPeriod sector mode point) at hFiber
  exact hFiber

private def d9HopfFirstBaseMatter
    (sector : NormalRootChoice) (mode : Int)
    (anchor : ThroatCover period hPeriod)
    (base : ThroatBase period hPeriod) : D9DoubledMatterFiber :=
  doubledSpinorLiftLocalValue period hPeriod .positiveQuarter
    (d9PrimitiveSpinCMapDoubledLift period hPeriod
      (d9PrimitiveSpinCHopfFirstFrameCLM sector)
      (d9PrimitiveSpinCHopfFirstFrameCLM_monodromy sector)
      (primitiveSpinCNormalModeDoubledLift
        period hPeriod sector mode))
    anchor base

private def d9HopfSecondBaseMatter
    (sector : NormalRootChoice) (mode : Int)
    (anchor : ThroatCover period hPeriod)
    (base : ThroatBase period hPeriod) : D9DoubledMatterFiber :=
  doubledSpinorLiftLocalValue period hPeriod .positiveQuarter
    (d9PrimitiveSpinCMapDoubledLift period hPeriod
      (d9PrimitiveSpinCHopfSecondFrameCLM sector)
      (d9PrimitiveSpinCHopfSecondFrameCLM_monodromy sector)
      (primitiveSpinCNormalModeDoubledLift
        period hPeriod sector mode))
    anchor base

private theorem d9HopfFirstBaseMatter_mdifferentiableAt_mk
    (sector : NormalRootChoice) (mode : Int)
    (point : ThroatCover period hPeriod) :
    MDifferentiableAt throatCoverModelWithCorners
      𝓘(Real, D9DoubledMatterFiber)
      (d9HopfFirstBaseMatter
        period hPeriod sector mode point)
      (mappingTorusMk (ThroatData period hPeriod) point) := by
  have hBase :
      mappingTorusMk (ThroatData period hPeriod) point ∈
        normalBundleBaseSet period hPeriod point :=
    (throatProjectionLocalHomeomorph period hPeriod)
      |>.apply_self_mem_localInverseAt_source
  unfold d9HopfFirstBaseMatter
  exact
    ((doubledSpinorLiftLocalValue_contMDiffOn
      period hPeriod .positiveQuarter
      (d9PrimitiveSpinCMapDoubledLift period hPeriod
        (d9PrimitiveSpinCHopfFirstFrameCLM sector)
        (d9PrimitiveSpinCHopfFirstFrameCLM_monodromy sector)
        (primitiveSpinCNormalModeDoubledLift
          period hPeriod sector mode))
      point).contMDiffAt
        ((normalBundleBaseSet_isOpen period hPeriod point).mem_nhds
          hBase)).mdifferentiableAt (by simp)

private theorem d9HopfSecondBaseMatter_mdifferentiableAt_mk
    (sector : NormalRootChoice) (mode : Int)
    (point : ThroatCover period hPeriod) :
    MDifferentiableAt throatCoverModelWithCorners
      𝓘(Real, D9DoubledMatterFiber)
      (d9HopfSecondBaseMatter
        period hPeriod sector mode point)
      (mappingTorusMk (ThroatData period hPeriod) point) := by
  have hBase :
      mappingTorusMk (ThroatData period hPeriod) point ∈
        normalBundleBaseSet period hPeriod point :=
    (throatProjectionLocalHomeomorph period hPeriod)
      |>.apply_self_mem_localInverseAt_source
  unfold d9HopfSecondBaseMatter
  exact
    ((doubledSpinorLiftLocalValue_contMDiffOn
      period hPeriod .positiveQuarter
      (d9PrimitiveSpinCMapDoubledLift period hPeriod
        (d9PrimitiveSpinCHopfSecondFrameCLM sector)
        (d9PrimitiveSpinCHopfSecondFrameCLM_monodromy sector)
        (primitiveSpinCNormalModeDoubledLift
          period hPeriod sector mode))
      point).contMDiffAt
        ((normalBundleBaseSet_isOpen period hPeriod point).mem_nhds
          hBase)).mdifferentiableAt (by simp)

@[simp]
private theorem d9HopfFirstBaseMatter_mk
    (sector : NormalRootChoice) (mode : Int)
    (point : ThroatCover period hPeriod) :
    d9HopfFirstBaseMatter period hPeriod sector mode point
        (mappingTorusMk (ThroatData period hPeriod) point) =
      d9PrimitiveSpinCHopfFirstFrameCLM sector
        (primitiveSpinCNormalModeDoubledLift
          period hPeriod sector mode point) := by
  simp [d9HopfFirstBaseMatter,
    d9PrimitiveSpinCMapDoubledLift_apply,
    doubledSpinorLiftLocalValue_mk]

@[simp]
private theorem d9HopfSecondBaseMatter_mk
    (sector : NormalRootChoice) (mode : Int)
    (point : ThroatCover period hPeriod) :
    d9HopfSecondBaseMatter period hPeriod sector mode point
        (mappingTorusMk (ThroatData period hPeriod) point) =
      d9PrimitiveSpinCHopfSecondFrameCLM sector
        (primitiveSpinCNormalModeDoubledLift
          period hPeriod sector mode point) := by
  simp [d9HopfSecondBaseMatter,
    d9PrimitiveSpinCMapDoubledLift_apply,
    doubledSpinorLiftLocalValue_mk]

private theorem d9HopfFirstBaseMatter_mfderiv_intrinsicFrame_mk
    (sector : NormalRootChoice) (mode : Int)
    (direction : Fin 3) (point : ThroatCover period hPeriod) :
    NormedSpace.fromTangentSpace (𝕜 := Real)
        (E := D9DoubledMatterFiber)
        (d9HopfFirstBaseMatter period hPeriod sector mode point
          (mappingTorusMk (ThroatData period hPeriod) point))
        (mfderiv throatCoverModelWithCorners
          𝓘(Real, D9DoubledMatterFiber)
          (d9HopfFirstBaseMatter period hPeriod sector mode point)
          (mappingTorusMk (ThroatData period hPeriod) point)
          (d9IntrinsicThroatFrame period hPeriod direction
            (mappingTorusMk (ThroatData period hPeriod) point))) =
      (normalRootSpinFrameFrequency period sector mode *
          d9UnitRadialCoordinate period hPeriod direction point) •
        d9PrimitiveSpinCImaginaryAction
          (d9PrimitiveSpinCHopfFirstFrameCLM sector
            (primitiveSpinCNormalModeDoubledLift
              period hPeriod sector mode point)) := by
  have hMapped :=
    doubledSpinorMappedLiftLocalValue_mfderiv_intrinsicFrame_mk
      period hPeriod
      (d9PrimitiveSpinCHopfFirstFrameCLM sector)
      (d9PrimitiveSpinCHopfFirstFrameCLM_monodromy sector)
      (primitiveSpinCNormalModeDoubledLift
        period hPeriod sector mode)
      point direction
  change
    NormedSpace.fromTangentSpace (𝕜 := Real)
        (E := D9DoubledMatterFiber)
        (d9HopfFirstBaseMatter period hPeriod sector mode point
          (mappingTorusMk (ThroatData period hPeriod) point))
        (mfderiv throatCoverModelWithCorners
          𝓘(Real, D9DoubledMatterFiber)
          (d9HopfFirstBaseMatter period hPeriod sector mode point)
          (mappingTorusMk (ThroatData period hPeriod) point)
          (d9IntrinsicThroatFrame period hPeriod direction
            (mappingTorusMk (ThroatData period hPeriod) point))) =
      _ at hMapped
  rw [hMapped,
    primitiveSpinCNormalModeDoubledLift_fromTangentSpace_mfderiv,
    map_smul, d9PrimitiveSpinCHopfFirstFrameCLM_imaginary]

private theorem d9HopfSecondBaseMatter_mfderiv_intrinsicFrame_mk
    (sector : NormalRootChoice) (mode : Int)
    (direction : Fin 3) (point : ThroatCover period hPeriod) :
    NormedSpace.fromTangentSpace (𝕜 := Real)
        (E := D9DoubledMatterFiber)
        (d9HopfSecondBaseMatter period hPeriod sector mode point
          (mappingTorusMk (ThroatData period hPeriod) point))
        (mfderiv throatCoverModelWithCorners
          𝓘(Real, D9DoubledMatterFiber)
          (d9HopfSecondBaseMatter period hPeriod sector mode point)
          (mappingTorusMk (ThroatData period hPeriod) point)
          (d9IntrinsicThroatFrame period hPeriod direction
            (mappingTorusMk (ThroatData period hPeriod) point))) =
      (normalRootSpinFrameFrequency period sector mode *
          d9UnitRadialCoordinate period hPeriod direction point) •
        d9PrimitiveSpinCImaginaryAction
          (d9PrimitiveSpinCHopfSecondFrameCLM sector
            (primitiveSpinCNormalModeDoubledLift
              period hPeriod sector mode point)) := by
  have hMapped :=
    doubledSpinorMappedLiftLocalValue_mfderiv_intrinsicFrame_mk
      period hPeriod
      (d9PrimitiveSpinCHopfSecondFrameCLM sector)
      (d9PrimitiveSpinCHopfSecondFrameCLM_monodromy sector)
      (primitiveSpinCNormalModeDoubledLift
        period hPeriod sector mode)
      point direction
  change
    NormedSpace.fromTangentSpace (𝕜 := Real)
        (E := D9DoubledMatterFiber)
        (d9HopfSecondBaseMatter period hPeriod sector mode point
          (mappingTorusMk (ThroatData period hPeriod) point))
        (mfderiv throatCoverModelWithCorners
          𝓘(Real, D9DoubledMatterFiber)
          (d9HopfSecondBaseMatter period hPeriod sector mode point)
          (mappingTorusMk (ThroatData period hPeriod) point)
          (d9IntrinsicThroatFrame period hPeriod direction
            (mappingTorusMk (ThroatData period hPeriod) point))) =
      _ at hMapped
  rw [hMapped,
    primitiveSpinCNormalModeDoubledLift_fromTangentSpace_mfderiv,
    map_smul, d9PrimitiveSpinCHopfSecondFrameCLM_imaginary]

private theorem d9PrimitiveSpinCComplexActionField_mfderiv
    (scalar : ThroatBase period hPeriod → Complex)
    (matter : ThroatBase period hPeriod → D9DoubledMatterFiber)
    (base : ThroatBase period hPeriod)
    (tangent :
      TangentSpace throatCoverModelWithCorners base)
    (hScalar :
      MDifferentiableAt throatCoverModelWithCorners
        𝓘(Real, Complex) scalar base)
    (hMatter :
      MDifferentiableAt throatCoverModelWithCorners
        𝓘(Real, D9DoubledMatterFiber) matter base) :
    NormedSpace.fromTangentSpace (𝕜 := Real)
        (E := D9DoubledMatterFiber)
        (d9PrimitiveSpinCComplexActionCLM
          (scalar base) (matter base))
        (mfderiv throatCoverModelWithCorners
          𝓘(Real, D9DoubledMatterFiber)
          (fun current =>
            d9PrimitiveSpinCComplexActionCLM
              (scalar current) (matter current))
          base tangent) =
      d9PrimitiveSpinCComplexActionCLM (scalar base)
          (NormedSpace.fromTangentSpace (𝕜 := Real)
            (E := D9DoubledMatterFiber) (matter base)
            (mfderiv throatCoverModelWithCorners
              𝓘(Real, D9DoubledMatterFiber)
              matter base tangent)) +
        d9PrimitiveSpinCComplexActionCLM
          (NormedSpace.fromTangentSpace (𝕜 := Real)
            (E := Complex) (scalar base)
            (mfderiv throatCoverModelWithCorners
              𝓘(Real, Complex) scalar base tangent))
          (matter base) := by
  let pairField :
      ThroatBase period hPeriod →
        Complex × D9DoubledMatterFiber :=
    fun current => (scalar current, matter current)
  have hPair :
      MDifferentiableAt throatCoverModelWithCorners
        𝓘(Real, Complex × D9DoubledMatterFiber)
        pairField base := by
    dsimp [pairField]
    exact hScalar.prodMk_space hMatter
  have hAction :
      MDifferentiableAt
        𝓘(Real, Complex × D9DoubledMatterFiber)
        𝓘(Real, D9DoubledMatterFiber)
        d9PrimitiveSpinCComplexActionPair
        (pairField base) :=
    (d9PrimitiveSpinCComplexActionPair_differentiable
      (pairField base)).mdifferentiableAt
  have hPairMap :
      mfderiv throatCoverModelWithCorners
          𝓘(Real, Complex × D9DoubledMatterFiber)
          pairField base =
        (mfderiv throatCoverModelWithCorners
          𝓘(Real, Complex) scalar base).prod
        (mfderiv throatCoverModelWithCorners
          𝓘(Real, D9DoubledMatterFiber) matter base) := by
    dsimp [pairField]
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact mfderiv_prodMk hScalar hMatter
  let pairDerivative :=
    mfderiv throatCoverModelWithCorners
      𝓘(Real, Complex × D9DoubledMatterFiber)
      pairField base tangent
  let pairIncrement : Complex × D9DoubledMatterFiber :=
    NormedSpace.fromTangentSpace (𝕜 := Real)
      (E := Complex × D9DoubledMatterFiber)
      (pairField base) pairDerivative
  have hPairIncrement :
      pairIncrement =
        (NormedSpace.fromTangentSpace (𝕜 := Real)
            (E := Complex) (scalar base)
            (mfderiv throatCoverModelWithCorners
              𝓘(Real, Complex) scalar base tangent),
          NormedSpace.fromTangentSpace (𝕜 := Real)
            (E := D9DoubledMatterFiber) (matter base)
            (mfderiv throatCoverModelWithCorners
              𝓘(Real, D9DoubledMatterFiber)
              matter base tangent)) := by
    dsimp [pairIncrement, pairDerivative]
    rw [hPairMap]
    rfl
  have hChain :=
    mfderiv_comp_apply base hAction hPair tangent
  have hOuter :=
    d9PrimitiveSpinCComplexActionPair_mfderiv
      (pairField base) pairIncrement
  have hOuter' :
      NormedSpace.fromTangentSpace (𝕜 := Real)
          (E := D9DoubledMatterFiber)
          (d9PrimitiveSpinCComplexActionPair (pairField base))
          (mfderiv
            𝓘(Real, Complex × D9DoubledMatterFiber)
            𝓘(Real, D9DoubledMatterFiber)
            d9PrimitiveSpinCComplexActionPair
            (pairField base) pairDerivative) =
        d9PrimitiveSpinCComplexActionCLM
            (pairField base).1 pairIncrement.2 +
          d9PrimitiveSpinCComplexActionCLM
            pairIncrement.1 (pairField base).2 := by
    simpa [pairIncrement] using hOuter
  have hChainFiber := congrArg
    (NormedSpace.fromTangentSpace (𝕜 := Real)
      (E := D9DoubledMatterFiber)
      (d9PrimitiveSpinCComplexActionPair (pairField base)))
    hChain
  have hResult := hChainFiber.trans hOuter'
  have hFunction :
      d9PrimitiveSpinCComplexActionPair ∘ pairField =
        fun current =>
          d9PrimitiveSpinCComplexActionCLM
            (scalar current) (matter current) := by
    funext current
    rfl
  rw [hFunction] at hResult
  dsimp only [pairField,
    d9PrimitiveSpinCComplexActionPair] at hResult
  change
    mfderiv throatCoverModelWithCorners
        𝓘(Real, D9DoubledMatterFiber)
        (fun current =>
          d9PrimitiveSpinCComplexActionCLM
            (scalar current) (matter current))
        base tangent =
      d9PrimitiveSpinCComplexActionCLM
          (scalar base) pairIncrement.2 +
        d9PrimitiveSpinCComplexActionCLM
          pairIncrement.1 (matter base) at hResult
  change
    mfderiv throatCoverModelWithCorners
        𝓘(Real, D9DoubledMatterFiber)
        (fun current =>
          d9PrimitiveSpinCComplexActionCLM
            (scalar current) (matter current))
        base tangent =
      d9PrimitiveSpinCComplexActionCLM (scalar base)
          (mfderiv throatCoverModelWithCorners
            𝓘(Real, D9DoubledMatterFiber)
            matter base tangent) +
        d9PrimitiveSpinCComplexActionCLM
          (mfderiv throatCoverModelWithCorners
            𝓘(Real, Complex) scalar base tangent)
          (matter base)
  rw [hResult, hPairIncrement]
  rfl

private def d9HopfFirstBaseScalar
    (chart : MonopoleChart)
    (base : ThroatBase period hPeriod) : Complex :=
  primitiveMonopoleZeroLocalValue chart
    (d9ThroatMonopoleSphereProjection period hPeriod base)

private def d9HopfSecondBaseScalar
    (chart : MonopoleChart)
    (base : ThroatBase period hPeriod) : Complex :=
  primitiveMonopoleZeroComplementLocalValue chart
    (d9ThroatMonopoleSphereProjection period hPeriod base)

private theorem d9HopfBaseScalar_mfderiv_intrinsicFrame_mk
    (scalar : MonopoleSphere → Complex)
    (direction : Fin 3) (point : ThroatCover period hPeriod)
    (hScalar :
      MDifferentiableAt (𝓡 2) 𝓘(Real, Complex) scalar
        (d9MonopoleSphereCoverProjection
          period hPeriod point)) :
    mfderiv throatCoverModelWithCorners 𝓘(Real, Complex)
        (fun base =>
          scalar
            (d9ThroatMonopoleSphereProjection
              period hPeriod base))
        (mappingTorusMk (ThroatData period hPeriod) point)
        (d9IntrinsicThroatFrame period hPeriod direction
          (mappingTorusMk (ThroatData period hPeriod) point)) =
      mfderiv throatCoverModelWithCorners 𝓘(Real, Complex)
        (fun current =>
          scalar
            (d9MonopoleSphereCoverProjection
              period hPeriod current))
        point
        (d9IntrinsicThroatCoverFrame
          period hPeriod direction point) := by
  let projection :=
    mappingTorusMk (ThroatData period hPeriod)
  let base := projection point
  let baseScalar : ThroatBase period hPeriod → Complex :=
    fun current =>
      scalar
        (d9ThroatMonopoleSphereProjection
          period hPeriod current)
  have hBaseScalar :
      MDifferentiableAt throatCoverModelWithCorners
        𝓘(Real, Complex) baseScalar base := by
    dsimp [baseScalar, base]
    exact hScalar.comp
      (mappingTorusMk (ThroatData period hPeriod) point)
      ((d9ThroatMonopoleSphereProjection_contMDiff
        period hPeriod).mdifferentiableAt (by simp))
  have hProjection :
      MDifferentiableAt throatCoverModelWithCorners
        throatCoverModelWithCorners projection point :=
    (fixedThroat_projection_isLocalDiffeomorph
      period hPeriod).contMDiff.mdifferentiableAt (by simp)
  have hChain :=
    mfderiv_comp_apply point hBaseScalar hProjection
      (d9IntrinsicThroatCoverFrame
        period hPeriod direction point)
  change
    mfderiv throatCoverModelWithCorners 𝓘(Real, Complex)
        (baseScalar ∘ projection) point
        (d9IntrinsicThroatCoverFrame
          period hPeriod direction point) =
      mfderiv throatCoverModelWithCorners 𝓘(Real, Complex)
          baseScalar base
          (mfderiv throatCoverModelWithCorners
            throatCoverModelWithCorners projection point
            (d9IntrinsicThroatCoverFrame
              period hPeriod direction point)) at hChain
  have hFunction :
      baseScalar ∘ projection =
        fun current =>
          scalar
            (d9MonopoleSphereCoverProjection
              period hPeriod current) := by
    funext current
    rfl
  rw [hFunction] at hChain
  have hFrame :=
    d9IntrinsicThroatFrame_mk
      period hPeriod direction point
  change
    d9IntrinsicThroatFrame period hPeriod direction base =
      mfderiv throatCoverModelWithCorners
        throatCoverModelWithCorners projection point
        (d9IntrinsicThroatCoverFrame
          period hPeriod direction point) at hFrame
  change
    mfderiv throatCoverModelWithCorners 𝓘(Real, Complex)
        baseScalar base
        (d9IntrinsicThroatFrame
          period hPeriod direction base) =
      mfderiv throatCoverModelWithCorners 𝓘(Real, Complex)
        (fun current =>
          scalar
            (d9MonopoleSphereCoverProjection
              period hPeriod current))
        point
        (d9IntrinsicThroatCoverFrame
          period hPeriod direction point)
  rw [hFrame, ← hChain]

private theorem d9HopfFirstBaseScalar_mfderiv_intrinsicFrame_mk
    (chart : MonopoleChart) (direction : Fin 3)
    (point : ThroatCover period hPeriod)
    (hChart :
      d9MonopoleSphereCoverProjection period hPeriod point ∈
        monopoleChartDomain chart) :
    mfderiv throatCoverModelWithCorners 𝓘(Real, Complex)
        (d9HopfFirstBaseScalar period hPeriod chart)
        (mappingTorusMk (ThroatData period hPeriod) point)
        (d9IntrinsicThroatFrame period hPeriod direction
          (mappingTorusMk (ThroatData period hPeriod) point)) =
      d9HopfFirstFrameDerivative
        period hPeriod chart direction point := by
  have hScalar :=
    ((primitiveMonopoleZeroLocalScalarFamily
      |>.contMDiffOn_localValue chart).contMDiffAt
        ((monopoleChartDomain_isOpen chart).mem_nhds hChart)
      |>.mdifferentiableAt (by simp))
  have hBridge :=
    d9HopfBaseScalar_mfderiv_intrinsicFrame_mk
      period hPeriod
      (primitiveMonopoleZeroLocalValue chart)
      direction point hScalar
  unfold d9HopfFirstBaseScalar
  rw [hBridge]
  cases chart with
  | north =>
      change
        mfderiv throatCoverModelWithCorners 𝓘(Real, Complex)
            (fun current =>
              primitiveMonopoleZeroNorthValue
                (d9MonopoleSphereCoverProjection
                  period hPeriod current))
            point
            (d9IntrinsicThroatCoverFrame
              period hPeriod direction point) =
          d9HopfNorthFirstFrameDerivative
            period hPeriod direction point
      have hCover :=
        primitiveMonopoleZeroNorthValue_mfderiv_intrinsicFrame
          period hPeriod direction point hChart
      change
        mfderiv throatCoverModelWithCorners 𝓘(Real, Complex)
            (fun current =>
              primitiveMonopoleZeroNorthValue
                (d9MonopoleSphereCoverProjection
                  period hPeriod current))
            point
            (d9IntrinsicThroatCoverFrame
              period hPeriod direction point) =
          d9HopfNorthFirstFrameDerivative
            period hPeriod direction point at hCover
      exact hCover
  | south =>
      change
        mfderiv throatCoverModelWithCorners 𝓘(Real, Complex)
            (fun current =>
              primitiveMonopoleZeroSouthValue
                (d9MonopoleSphereCoverProjection
                  period hPeriod current))
            point
            (d9IntrinsicThroatCoverFrame
              period hPeriod direction point) =
          d9HopfSouthFirstFrameDerivative
            period hPeriod direction point
      have hCover :=
        primitiveMonopoleZeroSouthValue_mfderiv_intrinsicFrame
          period hPeriod direction point hChart
      change
        mfderiv throatCoverModelWithCorners 𝓘(Real, Complex)
            (fun current =>
              primitiveMonopoleZeroSouthValue
                (d9MonopoleSphereCoverProjection
                  period hPeriod current))
            point
            (d9IntrinsicThroatCoverFrame
              period hPeriod direction point) =
          d9HopfSouthFirstFrameDerivative
            period hPeriod direction point at hCover
      exact hCover

private theorem d9HopfSecondBaseScalar_mfderiv_intrinsicFrame_mk
    (chart : MonopoleChart) (direction : Fin 3)
    (point : ThroatCover period hPeriod)
    (hChart :
      d9MonopoleSphereCoverProjection period hPeriod point ∈
        monopoleChartDomain chart) :
    mfderiv throatCoverModelWithCorners 𝓘(Real, Complex)
        (d9HopfSecondBaseScalar period hPeriod chart)
        (mappingTorusMk (ThroatData period hPeriod) point)
        (d9IntrinsicThroatFrame period hPeriod direction
          (mappingTorusMk (ThroatData period hPeriod) point)) =
      d9HopfSecondFrameDerivative
        period hPeriod chart direction point := by
  have hScalar :=
    ((primitiveMonopoleZeroComplementLocalScalarFamily
      |>.contMDiffOn_localValue chart).contMDiffAt
        ((monopoleChartDomain_isOpen chart).mem_nhds hChart)
      |>.mdifferentiableAt (by simp))
  have hBridge :=
    d9HopfBaseScalar_mfderiv_intrinsicFrame_mk
      period hPeriod
      (primitiveMonopoleZeroComplementLocalValue chart)
      direction point hScalar
  unfold d9HopfSecondBaseScalar
  rw [hBridge]
  cases chart with
  | north =>
      change
        mfderiv throatCoverModelWithCorners 𝓘(Real, Complex)
            (fun current =>
              primitiveMonopoleZeroComplementNorthValue
                (d9MonopoleSphereCoverProjection
                  period hPeriod current))
            point
            (d9IntrinsicThroatCoverFrame
              period hPeriod direction point) =
          d9HopfNorthSecondFrameDerivative
            period hPeriod direction point
      have hCover :=
        primitiveMonopoleZeroComplementNorthValue_mfderiv_intrinsicFrame
          period hPeriod direction point hChart
      change
        mfderiv throatCoverModelWithCorners 𝓘(Real, Complex)
            (fun current =>
              primitiveMonopoleZeroComplementNorthValue
                (d9MonopoleSphereCoverProjection
                  period hPeriod current))
            point
            (d9IntrinsicThroatCoverFrame
              period hPeriod direction point) =
          d9HopfNorthSecondFrameDerivative
            period hPeriod direction point at hCover
      exact hCover
  | south =>
      change
        mfderiv throatCoverModelWithCorners 𝓘(Real, Complex)
            (fun current =>
              primitiveMonopoleZeroComplementSouthValue
                (d9MonopoleSphereCoverProjection
                  period hPeriod current))
            point
            (d9IntrinsicThroatCoverFrame
              period hPeriod direction point) =
          d9HopfSouthSecondFrameDerivative
            period hPeriod direction point
      have hCover :=
        primitiveMonopoleZeroComplementSouthValue_mfderiv_intrinsicFrame
          period hPeriod direction point hChart
      change
        mfderiv throatCoverModelWithCorners 𝓘(Real, Complex)
            (fun current =>
              primitiveMonopoleZeroComplementSouthValue
                (d9MonopoleSphereCoverProjection
                  period hPeriod current))
            point
            (d9IntrinsicThroatCoverFrame
              period hPeriod direction point) =
          d9HopfSouthSecondFrameDerivative
            period hPeriod direction point at hCover
      exact hCover

private theorem d9HopfFirstBaseScalar_fromTangentSpace_mfderiv_mk
    (chart : MonopoleChart) (direction : Fin 3)
    (point : ThroatCover period hPeriod)
    (hChart :
      d9MonopoleSphereCoverProjection period hPeriod point ∈
        monopoleChartDomain chart) :
    NormedSpace.fromTangentSpace (𝕜 := Real)
        (E := Complex)
        (d9HopfFirstBaseScalar period hPeriod chart
          (mappingTorusMk (ThroatData period hPeriod) point))
        (mfderiv throatCoverModelWithCorners 𝓘(Real, Complex)
          (d9HopfFirstBaseScalar period hPeriod chart)
          (mappingTorusMk (ThroatData period hPeriod) point)
          (d9IntrinsicThroatFrame period hPeriod direction
            (mappingTorusMk (ThroatData period hPeriod) point))) =
      d9HopfFirstFrameDerivative
        period hPeriod chart direction point := by
  have hDerivative :=
    d9HopfFirstBaseScalar_mfderiv_intrinsicFrame_mk
      period hPeriod chart direction point hChart
  have hFiber := congrArg
    (NormedSpace.fromTangentSpace (𝕜 := Real) (E := Complex)
      (d9HopfFirstBaseScalar period hPeriod chart
        (mappingTorusMk (ThroatData period hPeriod) point)))
    hDerivative
  change
    NormedSpace.fromTangentSpace (𝕜 := Real)
        (E := Complex)
        (d9HopfFirstBaseScalar period hPeriod chart
          (mappingTorusMk (ThroatData period hPeriod) point))
        (mfderiv throatCoverModelWithCorners 𝓘(Real, Complex)
          (d9HopfFirstBaseScalar period hPeriod chart)
          (mappingTorusMk (ThroatData period hPeriod) point)
          (d9IntrinsicThroatFrame period hPeriod direction
            (mappingTorusMk (ThroatData period hPeriod) point))) =
      d9HopfFirstFrameDerivative
        period hPeriod chart direction point at hFiber
  exact hFiber

private theorem d9HopfSecondBaseScalar_fromTangentSpace_mfderiv_mk
    (chart : MonopoleChart) (direction : Fin 3)
    (point : ThroatCover period hPeriod)
    (hChart :
      d9MonopoleSphereCoverProjection period hPeriod point ∈
        monopoleChartDomain chart) :
    NormedSpace.fromTangentSpace (𝕜 := Real)
        (E := Complex)
        (d9HopfSecondBaseScalar period hPeriod chart
          (mappingTorusMk (ThroatData period hPeriod) point))
        (mfderiv throatCoverModelWithCorners 𝓘(Real, Complex)
          (d9HopfSecondBaseScalar period hPeriod chart)
          (mappingTorusMk (ThroatData period hPeriod) point)
          (d9IntrinsicThroatFrame period hPeriod direction
            (mappingTorusMk (ThroatData period hPeriod) point))) =
      d9HopfSecondFrameDerivative
        period hPeriod chart direction point := by
  have hDerivative :=
    d9HopfSecondBaseScalar_mfderiv_intrinsicFrame_mk
      period hPeriod chart direction point hChart
  have hFiber := congrArg
    (NormedSpace.fromTangentSpace (𝕜 := Real) (E := Complex)
      (d9HopfSecondBaseScalar period hPeriod chart
        (mappingTorusMk (ThroatData period hPeriod) point)))
    hDerivative
  change
    NormedSpace.fromTangentSpace (𝕜 := Real)
        (E := Complex)
        (d9HopfSecondBaseScalar period hPeriod chart
          (mappingTorusMk (ThroatData period hPeriod) point))
        (mfderiv throatCoverModelWithCorners 𝓘(Real, Complex)
          (d9HopfSecondBaseScalar period hPeriod chart)
          (mappingTorusMk (ThroatData period hPeriod) point)
          (d9IntrinsicThroatFrame period hPeriod direction
            (mappingTorusMk (ThroatData period hPeriod) point))) =
      d9HopfSecondFrameDerivative
        period hPeriod chart direction point at hFiber
  exact hFiber

private theorem d9HopfFirstBaseScalar_mdifferentiableAt_mk
    (chart : MonopoleChart) (point : ThroatCover period hPeriod)
    (hChart :
      d9MonopoleSphereCoverProjection period hPeriod point ∈
        monopoleChartDomain chart) :
    MDifferentiableAt throatCoverModelWithCorners
      𝓘(Real, Complex)
      (d9HopfFirstBaseScalar period hPeriod chart)
      (mappingTorusMk (ThroatData period hPeriod) point) := by
  have hScalar :=
    ((primitiveMonopoleZeroLocalScalarFamily
      |>.contMDiffOn_localValue chart).contMDiffAt
        ((monopoleChartDomain_isOpen chart).mem_nhds hChart)
      |>.mdifferentiableAt (by simp))
  unfold d9HopfFirstBaseScalar
  exact hScalar.comp
    (mappingTorusMk (ThroatData period hPeriod) point)
    ((d9ThroatMonopoleSphereProjection_contMDiff
      period hPeriod).mdifferentiableAt (by simp))

private theorem d9HopfSecondBaseScalar_mdifferentiableAt_mk
    (chart : MonopoleChart) (point : ThroatCover period hPeriod)
    (hChart :
      d9MonopoleSphereCoverProjection period hPeriod point ∈
        monopoleChartDomain chart) :
    MDifferentiableAt throatCoverModelWithCorners
      𝓘(Real, Complex)
      (d9HopfSecondBaseScalar period hPeriod chart)
      (mappingTorusMk (ThroatData period hPeriod) point) := by
  have hScalar :=
    ((primitiveMonopoleZeroComplementLocalScalarFamily
      |>.contMDiffOn_localValue chart).contMDiffAt
        ((monopoleChartDomain_isOpen chart).mem_nhds hChart)
      |>.mdifferentiableAt (by simp))
  unfold d9HopfSecondBaseScalar
  exact hScalar.comp
    (mappingTorusMk (ThroatData period hPeriod) point)
    ((d9ThroatMonopoleSphereProjection_contMDiff
      period hPeriod).mdifferentiableAt (by simp))

private def d9HopfFirstBaseTerm
    (sector : NormalRootChoice) (mode : Int)
    (point : ThroatCover period hPeriod) (chart : MonopoleChart)
    (base : ThroatBase period hPeriod) : D9DoubledMatterFiber :=
  d9PrimitiveSpinCComplexActionCLM
    (d9HopfFirstBaseScalar period hPeriod chart base)
    (d9HopfFirstBaseMatter period hPeriod sector mode point base)

private def d9HopfSecondBaseTerm
    (sector : NormalRootChoice) (mode : Int)
    (point : ThroatCover period hPeriod) (chart : MonopoleChart)
    (base : ThroatBase period hPeriod) : D9DoubledMatterFiber :=
  d9PrimitiveSpinCComplexActionCLM
    (d9HopfSecondBaseScalar period hPeriod chart base)
    (d9HopfSecondBaseMatter period hPeriod sector mode point base)

private theorem d9HopfFirstBaseTerm_mdifferentiableAt_mk
    (sector : NormalRootChoice) (mode : Int)
    (point : ThroatCover period hPeriod) (chart : MonopoleChart)
    (hChart :
      d9MonopoleSphereCoverProjection period hPeriod point ∈
        monopoleChartDomain chart) :
    MDifferentiableAt throatCoverModelWithCorners
      𝓘(Real, D9DoubledMatterFiber)
      (d9HopfFirstBaseTerm
        period hPeriod sector mode point chart)
      (mappingTorusMk (ThroatData period hPeriod) point) := by
  have hPair :=
    (d9HopfFirstBaseScalar_mdifferentiableAt_mk
      period hPeriod chart point hChart).prodMk_space
      (d9HopfFirstBaseMatter_mdifferentiableAt_mk
        period hPeriod sector mode point)
  have hAction :
      MDifferentiableAt
        𝓘(Real, Complex × D9DoubledMatterFiber)
        𝓘(Real, D9DoubledMatterFiber)
        d9PrimitiveSpinCComplexActionPair
        (d9HopfFirstBaseScalar period hPeriod chart
            (mappingTorusMk (ThroatData period hPeriod) point),
          d9HopfFirstBaseMatter period hPeriod sector mode point
            (mappingTorusMk (ThroatData period hPeriod) point)) :=
    d9PrimitiveSpinCComplexActionPair_differentiable
      |>.differentiableAt.mdifferentiableAt
  change
    MDifferentiableAt throatCoverModelWithCorners
      𝓘(Real, D9DoubledMatterFiber)
      (d9PrimitiveSpinCComplexActionPair ∘
        fun base =>
          (d9HopfFirstBaseScalar period hPeriod chart base,
            d9HopfFirstBaseMatter
              period hPeriod sector mode point base))
      (mappingTorusMk (ThroatData period hPeriod) point)
  exact hAction.comp
    (mappingTorusMk (ThroatData period hPeriod) point) hPair

private theorem d9HopfSecondBaseTerm_mdifferentiableAt_mk
    (sector : NormalRootChoice) (mode : Int)
    (point : ThroatCover period hPeriod) (chart : MonopoleChart)
    (hChart :
      d9MonopoleSphereCoverProjection period hPeriod point ∈
        monopoleChartDomain chart) :
    MDifferentiableAt throatCoverModelWithCorners
      𝓘(Real, D9DoubledMatterFiber)
      (d9HopfSecondBaseTerm
        period hPeriod sector mode point chart)
      (mappingTorusMk (ThroatData period hPeriod) point) := by
  have hPair :=
    (d9HopfSecondBaseScalar_mdifferentiableAt_mk
      period hPeriod chart point hChart).prodMk_space
      (d9HopfSecondBaseMatter_mdifferentiableAt_mk
        period hPeriod sector mode point)
  have hAction :
      MDifferentiableAt
        𝓘(Real, Complex × D9DoubledMatterFiber)
        𝓘(Real, D9DoubledMatterFiber)
        d9PrimitiveSpinCComplexActionPair
        (d9HopfSecondBaseScalar period hPeriod chart
            (mappingTorusMk (ThroatData period hPeriod) point),
          d9HopfSecondBaseMatter period hPeriod sector mode point
            (mappingTorusMk (ThroatData period hPeriod) point)) :=
    d9PrimitiveSpinCComplexActionPair_differentiable
      |>.differentiableAt.mdifferentiableAt
  change
    MDifferentiableAt throatCoverModelWithCorners
      𝓘(Real, D9DoubledMatterFiber)
      (d9PrimitiveSpinCComplexActionPair ∘
        fun base =>
          (d9HopfSecondBaseScalar period hPeriod chart base,
            d9HopfSecondBaseMatter
              period hPeriod sector mode point base))
      (mappingTorusMk (ThroatData period hPeriod) point)
  exact hAction.comp
    (mappingTorusMk (ThroatData period hPeriod) point) hPair

private theorem d9HopfFirstBaseTerm_mfderiv_intrinsicFrame_mk
    (sector : NormalRootChoice) (mode : Int)
    (point : ThroatCover period hPeriod) (chart : MonopoleChart)
    (direction : Fin 3)
    (hChart :
      d9MonopoleSphereCoverProjection period hPeriod point ∈
        monopoleChartDomain chart) :
    NormedSpace.fromTangentSpace (𝕜 := Real)
        (E := D9DoubledMatterFiber)
        (d9HopfFirstBaseTerm period hPeriod sector mode point chart
          (mappingTorusMk (ThroatData period hPeriod) point))
        (mfderiv throatCoverModelWithCorners
          𝓘(Real, D9DoubledMatterFiber)
          (d9HopfFirstBaseTerm
            period hPeriod sector mode point chart)
          (mappingTorusMk (ThroatData period hPeriod) point)
          (d9IntrinsicThroatFrame period hPeriod direction
            (mappingTorusMk (ThroatData period hPeriod) point))) =
      d9PrimitiveSpinCComplexActionCLM
          (d9HopfFirstScalar period hPeriod chart point)
          ((normalRootSpinFrameFrequency period sector mode *
              d9UnitRadialCoordinate period hPeriod direction point) •
            d9PrimitiveSpinCImaginaryAction
              (d9PrimitiveSpinCHopfFirstFrameCLM sector
                (primitiveSpinCNormalModeDoubledLift
                  period hPeriod sector mode point))) +
        d9PrimitiveSpinCComplexActionCLM
          (d9HopfFirstFrameDerivative
            period hPeriod chart direction point)
          (d9PrimitiveSpinCHopfFirstFrameCLM sector
            (primitiveSpinCNormalModeDoubledLift
              period hPeriod sector mode point)) := by
  unfold d9HopfFirstBaseTerm
  have hProduct :=
    d9PrimitiveSpinCComplexActionField_mfderiv
      period hPeriod
      (d9HopfFirstBaseScalar period hPeriod chart)
      (d9HopfFirstBaseMatter period hPeriod sector mode point)
      (mappingTorusMk (ThroatData period hPeriod) point)
      (d9IntrinsicThroatFrame period hPeriod direction
        (mappingTorusMk (ThroatData period hPeriod) point))
      (d9HopfFirstBaseScalar_mdifferentiableAt_mk
        period hPeriod chart point hChart)
      (d9HopfFirstBaseMatter_mdifferentiableAt_mk
        period hPeriod sector mode point)
  rw [hProduct,
    d9HopfFirstBaseMatter_mfderiv_intrinsicFrame_mk,
    d9HopfFirstBaseScalar_fromTangentSpace_mfderiv_mk
      (hChart := hChart)]
  simp [d9HopfFirstBaseScalar, d9HopfFirstScalar,
    d9HopfFirstBaseMatter_mk]

private theorem d9HopfSecondBaseTerm_mfderiv_intrinsicFrame_mk
    (sector : NormalRootChoice) (mode : Int)
    (point : ThroatCover period hPeriod) (chart : MonopoleChart)
    (direction : Fin 3)
    (hChart :
      d9MonopoleSphereCoverProjection period hPeriod point ∈
        monopoleChartDomain chart) :
    NormedSpace.fromTangentSpace (𝕜 := Real)
        (E := D9DoubledMatterFiber)
        (d9HopfSecondBaseTerm period hPeriod sector mode point chart
          (mappingTorusMk (ThroatData period hPeriod) point))
        (mfderiv throatCoverModelWithCorners
          𝓘(Real, D9DoubledMatterFiber)
          (d9HopfSecondBaseTerm
            period hPeriod sector mode point chart)
          (mappingTorusMk (ThroatData period hPeriod) point)
          (d9IntrinsicThroatFrame period hPeriod direction
            (mappingTorusMk (ThroatData period hPeriod) point))) =
      d9PrimitiveSpinCComplexActionCLM
          (d9HopfSecondScalar period hPeriod chart point)
          ((normalRootSpinFrameFrequency period sector mode *
              d9UnitRadialCoordinate period hPeriod direction point) •
            d9PrimitiveSpinCImaginaryAction
              (d9PrimitiveSpinCHopfSecondFrameCLM sector
                (primitiveSpinCNormalModeDoubledLift
                  period hPeriod sector mode point))) +
        d9PrimitiveSpinCComplexActionCLM
          (d9HopfSecondFrameDerivative
            period hPeriod chart direction point)
          (d9PrimitiveSpinCHopfSecondFrameCLM sector
            (primitiveSpinCNormalModeDoubledLift
              period hPeriod sector mode point)) := by
  unfold d9HopfSecondBaseTerm
  have hProduct :=
    d9PrimitiveSpinCComplexActionField_mfderiv
      period hPeriod
      (d9HopfSecondBaseScalar period hPeriod chart)
      (d9HopfSecondBaseMatter period hPeriod sector mode point)
      (mappingTorusMk (ThroatData period hPeriod) point)
      (d9IntrinsicThroatFrame period hPeriod direction
        (mappingTorusMk (ThroatData period hPeriod) point))
      (d9HopfSecondBaseScalar_mdifferentiableAt_mk
        period hPeriod chart point hChart)
      (d9HopfSecondBaseMatter_mdifferentiableAt_mk
        period hPeriod sector mode point)
  rw [hProduct,
    d9HopfSecondBaseMatter_mfderiv_intrinsicFrame_mk,
    d9HopfSecondBaseScalar_fromTangentSpace_mfderiv_mk
      (hChart := hChart)]
  simp [d9HopfSecondBaseScalar, d9HopfSecondScalar,
    d9HopfSecondBaseMatter_mk]

private theorem primitiveSpinCHopfZeroModeLocalGaugeFamily_localValue_eq_terms
    (sector : NormalRootChoice) (mode : Int)
    (point : ThroatCover period hPeriod) (chart : MonopoleChart) :
    (primitiveSpinCHopfZeroModeLocalGaugeFamily
      period hPeriod sector mode).localValue (point, chart) =
      fun base =>
        d9HopfFirstBaseTerm
            period hPeriod sector mode point chart base +
          d9HopfSecondBaseTerm
            period hPeriod sector mode point chart base := by
  rfl

private theorem d9PrimitiveSpinCHopfTermDerivative_sum
    (sector : NormalRootChoice) (matter : D9DoubledMatterFiber)
    (normalCoefficient : Real)
    (firstScalar secondScalar
      firstDerivative secondDerivative : Complex) :
    (d9PrimitiveSpinCComplexActionCLM firstScalar
          (normalCoefficient •
            d9PrimitiveSpinCImaginaryAction
              (d9PrimitiveSpinCHopfFirstFrameCLM sector matter)) +
        d9PrimitiveSpinCComplexActionCLM firstDerivative
          (d9PrimitiveSpinCHopfFirstFrameCLM sector matter)) +
      (d9PrimitiveSpinCComplexActionCLM secondScalar
          (normalCoefficient •
            d9PrimitiveSpinCImaginaryAction
              (d9PrimitiveSpinCHopfSecondFrameCLM sector matter)) +
        d9PrimitiveSpinCComplexActionCLM secondDerivative
          (d9PrimitiveSpinCHopfSecondFrameCLM sector matter)) =
      d9PrimitiveSpinCHopfFrameCombination sector matter
          firstDerivative secondDerivative +
        normalCoefficient •
          d9PrimitiveSpinCImaginaryAction
            (d9PrimitiveSpinCHopfFrameCombination sector matter
              firstScalar secondScalar) := by
  unfold d9PrimitiveSpinCHopfFrameCombination
  rw [map_smul, map_smul,
    d9PrimitiveSpinCComplexAction_imaginary,
    d9PrimitiveSpinCComplexAction_imaginary,
    map_add, smul_add]
  abel

/-- The flat local derivative splits into the monopole angular derivative
and the rotating normal Fourier derivative. -/
theorem primitiveSpinCHopfZeroModeLocalFlatFrameDerivative_mk
    (sector : NormalRootChoice) (mode : Int)
    (point : ThroatCover period hPeriod) (chart : MonopoleChart)
    (direction : Fin 3)
    (hChart :
      d9MonopoleSphereCoverProjection period hPeriod point ∈
        monopoleChartDomain chart) :
    d9PrimitiveSpinCLocalFlatFrameDerivative
        period hPeriod .positiveQuarter
        (primitiveSpinCHopfZeroModeLocalGaugeFamily
          period hPeriod sector mode)
        (point, chart) direction
        (mappingTorusMk (ThroatData period hPeriod) point) =
      d9PrimitiveSpinCHopfFrameCombination sector
          (primitiveSpinCNormalModeDoubledLift
            period hPeriod sector mode point)
          (d9HopfFirstFrameDerivative
            period hPeriod chart direction point)
          (d9HopfSecondFrameDerivative
            period hPeriod chart direction point) +
        (normalRootSpinFrameFrequency period sector mode *
            d9UnitRadialCoordinate
              period hPeriod direction point) •
          d9PrimitiveSpinCImaginaryAction
            (d9PrimitiveSpinCHopfFrameCombination sector
              (primitiveSpinCNormalModeDoubledLift
                period hPeriod sector mode point)
              (d9HopfFirstScalar period hPeriod chart point)
              (d9HopfSecondScalar period hPeriod chart point)) := by
  let base :=
    mappingTorusMk (ThroatData period hPeriod) point
  let tangent :=
    d9IntrinsicThroatFrame period hPeriod direction base
  have hFirstDiff :=
    d9HopfFirstBaseTerm_mdifferentiableAt_mk
      period hPeriod sector mode point chart hChart
  have hSecondDiff :=
    d9HopfSecondBaseTerm_mdifferentiableAt_mk
      period hPeriod sector mode point chart hChart
  have hAdd :=
    mfderiv_add hFirstDiff hSecondDiff
  have hAddApply := congrArg
    (fun derivative =>
      NormedSpace.fromTangentSpace (𝕜 := Real)
        (E := D9DoubledMatterFiber)
        (d9HopfFirstBaseTerm period hPeriod sector mode point chart base +
          d9HopfSecondBaseTerm
            period hPeriod sector mode point chart base)
        (derivative tangent))
    hAdd
  have hAddFiber :
      NormedSpace.fromTangentSpace (𝕜 := Real)
          (E := D9DoubledMatterFiber)
          (d9HopfFirstBaseTerm period hPeriod sector mode point chart base +
            d9HopfSecondBaseTerm
              period hPeriod sector mode point chart base)
          (mfderiv throatCoverModelWithCorners
            𝓘(Real, D9DoubledMatterFiber)
            (fun current =>
              d9HopfFirstBaseTerm
                    period hPeriod sector mode point chart current +
                d9HopfSecondBaseTerm
                    period hPeriod sector mode point chart current)
            base tangent) =
        NormedSpace.fromTangentSpace (𝕜 := Real)
            (E := D9DoubledMatterFiber)
            (d9HopfFirstBaseTerm
              period hPeriod sector mode point chart base)
            (mfderiv throatCoverModelWithCorners
              𝓘(Real, D9DoubledMatterFiber)
              (d9HopfFirstBaseTerm
                period hPeriod sector mode point chart)
              base tangent) +
          NormedSpace.fromTangentSpace (𝕜 := Real)
            (E := D9DoubledMatterFiber)
            (d9HopfSecondBaseTerm
              period hPeriod sector mode point chart base)
            (mfderiv throatCoverModelWithCorners
              𝓘(Real, D9DoubledMatterFiber)
              (d9HopfSecondBaseTerm
                period hPeriod sector mode point chart)
              base tangent) := by
    change
      NormedSpace.fromTangentSpace (𝕜 := Real)
          (E := D9DoubledMatterFiber)
          (d9HopfFirstBaseTerm period hPeriod sector mode point chart base +
            d9HopfSecondBaseTerm
              period hPeriod sector mode point chart base)
          (mfderiv throatCoverModelWithCorners
            𝓘(Real, D9DoubledMatterFiber)
            (fun current =>
              d9HopfFirstBaseTerm
                    period hPeriod sector mode point chart current +
                d9HopfSecondBaseTerm
                    period hPeriod sector mode point chart current)
            base tangent) =
        NormedSpace.fromTangentSpace (𝕜 := Real)
            (E := D9DoubledMatterFiber)
            (d9HopfFirstBaseTerm
              period hPeriod sector mode point chart base)
            (mfderiv throatCoverModelWithCorners
              𝓘(Real, D9DoubledMatterFiber)
              (d9HopfFirstBaseTerm
                period hPeriod sector mode point chart)
              base tangent) +
          NormedSpace.fromTangentSpace (𝕜 := Real)
            (E := D9DoubledMatterFiber)
            (d9HopfSecondBaseTerm
              period hPeriod sector mode point chart base)
            (mfderiv throatCoverModelWithCorners
              𝓘(Real, D9DoubledMatterFiber)
              (d9HopfSecondBaseTerm
                period hPeriod sector mode point chart)
              base tangent) at hAddApply
    exact hAddApply
  have hFirstDerivative :=
    d9HopfFirstBaseTerm_mfderiv_intrinsicFrame_mk
      period hPeriod sector mode point chart direction hChart
  have hSecondDerivative :=
    d9HopfSecondBaseTerm_mfderiv_intrinsicFrame_mk
      period hPeriod sector mode point chart direction hChart
  have hDerivative :
      NormedSpace.fromTangentSpace (𝕜 := Real)
          (E := D9DoubledMatterFiber)
          ((primitiveSpinCHopfZeroModeLocalGaugeFamily
            period hPeriod sector mode).localValue
              (point, chart) base)
          (mfderiv throatCoverModelWithCorners
            𝓘(Real, D9DoubledMatterFiber)
            ((primitiveSpinCHopfZeroModeLocalGaugeFamily
              period hPeriod sector mode).localValue (point, chart))
            base tangent) =
        (d9PrimitiveSpinCComplexActionCLM
              (d9HopfFirstScalar period hPeriod chart point)
              ((normalRootSpinFrameFrequency period sector mode *
                  d9UnitRadialCoordinate
                    period hPeriod direction point) •
                d9PrimitiveSpinCImaginaryAction
                  (d9PrimitiveSpinCHopfFirstFrameCLM sector
                    (primitiveSpinCNormalModeDoubledLift
                      period hPeriod sector mode point))) +
            d9PrimitiveSpinCComplexActionCLM
              (d9HopfFirstFrameDerivative
                period hPeriod chart direction point)
              (d9PrimitiveSpinCHopfFirstFrameCLM sector
                (primitiveSpinCNormalModeDoubledLift
                  period hPeriod sector mode point))) +
          (d9PrimitiveSpinCComplexActionCLM
              (d9HopfSecondScalar period hPeriod chart point)
              ((normalRootSpinFrameFrequency period sector mode *
                  d9UnitRadialCoordinate
                    period hPeriod direction point) •
                d9PrimitiveSpinCImaginaryAction
                  (d9PrimitiveSpinCHopfSecondFrameCLM sector
                    (primitiveSpinCNormalModeDoubledLift
                      period hPeriod sector mode point))) +
            d9PrimitiveSpinCComplexActionCLM
              (d9HopfSecondFrameDerivative
                period hPeriod chart direction point)
              (d9PrimitiveSpinCHopfSecondFrameCLM sector
                (primitiveSpinCNormalModeDoubledLift
                  period hPeriod sector mode point))) := by
    rw [primitiveSpinCHopfZeroModeLocalGaugeFamily_localValue_eq_terms]
    change
      NormedSpace.fromTangentSpace (𝕜 := Real)
          (E := D9DoubledMatterFiber)
          (d9HopfFirstBaseTerm period hPeriod sector mode point chart base +
            d9HopfSecondBaseTerm
              period hPeriod sector mode point chart base)
          (mfderiv throatCoverModelWithCorners
            𝓘(Real, D9DoubledMatterFiber)
            (fun current =>
              d9HopfFirstBaseTerm
                    period hPeriod sector mode point chart current +
                d9HopfSecondBaseTerm
                    period hPeriod sector mode point chart current)
            base tangent) = _
    rw [hAddFiber, hFirstDerivative, hSecondDerivative]
  unfold d9PrimitiveSpinCLocalFlatFrameDerivative
  change
    NormedSpace.fromTangentSpace (𝕜 := Real)
        (E := D9DoubledMatterFiber)
        ((primitiveSpinCHopfZeroModeLocalGaugeFamily
          period hPeriod sector mode).localValue (point, chart) base)
        (mfderiv throatCoverModelWithCorners
          𝓘(Real, D9DoubledMatterFiber)
          ((primitiveSpinCHopfZeroModeLocalGaugeFamily
            period hPeriod sector mode).localValue (point, chart))
          base tangent) = _
  rw [hDerivative]
  exact d9PrimitiveSpinCHopfTermDerivative_sum
    sector
    (primitiveSpinCNormalModeDoubledLift
      period hPeriod sector mode point)
    (normalRootSpinFrameFrequency period sector mode *
      d9UnitRadialCoordinate period hPeriod direction point)
    (d9HopfFirstScalar period hPeriod chart point)
    (d9HopfSecondScalar period hPeriod chart point)
    (d9HopfFirstFrameDerivative
      period hPeriod chart direction point)
    (d9HopfSecondFrameDerivative
      period hPeriod chart direction point)

private theorem d9PrimitiveMonopoleConnectionFrameCoefficient_mk
    (chart : MonopoleChart) (direction : Fin 3)
    (point : ThroatCover period hPeriod) :
    d9PrimitiveMonopoleConnectionFrameCoefficient
        period hPeriod 1 chart direction
        (mappingTorusMk (ThroatData period hPeriod) point) =
      d9HopfMonopoleFrameCoefficient
        period hPeriod chart direction point := by
  unfold d9PrimitiveMonopoleConnectionFrameCoefficient
    d9HopfMonopoleFrameCoefficient
  rw [d9ThroatMonopoleSphereProjection_mk,
    d9PrimitiveMonopoleCoordinateFrameDerivative_mk,
    d9PrimitiveMonopoleCoordinateFrameDerivative_mk]

private theorem d9PrimitiveSpinCTotalConnectionFrameCoefficient_mk
    (chart : MonopoleChart) (direction : Fin 3)
    (point : ThroatCover period hPeriod) :
    d9PrimitiveSpinCTotalConnectionFrameCoefficient
        period hPeriod chart direction
        (mappingTorusMk (ThroatData period hPeriod) point) =
      d9HopfMonopoleFrameCoefficient
          period hPeriod chart direction point -
        Real.pi / (2 * period) *
          d9UnitRadialCoordinate
            period hPeriod direction point := by
  unfold d9PrimitiveSpinCTotalConnectionFrameCoefficient
    d9PrimitiveSpinCNormalFrameConnectionCoefficient
  rw [d9PrimitiveMonopoleConnectionFrameCoefficient_mk,
    d9PrimitiveSpinCBaseUnitRadialCoordinate_mk]
  ring

private theorem d9PrimitiveSpinCBaseLeviCivitaSpinCorrection_mk
    (direction : Fin 3) (point : ThroatCover period hPeriod)
    (matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCBaseLeviCivitaSpinCorrection
        period hPeriod direction
        (mappingTorusMk (ThroatData period hPeriod) point) matter =
      d9LeviCivitaSpinCorrection
        period hPeriod direction point matter := by
  unfold d9PrimitiveSpinCBaseLeviCivitaSpinCorrection
    d9LeviCivitaSpinCorrection
  apply Finset.sum_congr rfl
  intro other _
  by_cases hSame : other = direction
  · simp [hSame]
  · simp only [hSame, ↓reduceIte]
    rw [d9PrimitiveSpinCBaseUnitRadialCoordinate_mk]

private theorem d9PrimitiveSpinCComplexAction_covariantScalar
    (coefficient : Real) (derivative scalar : Complex)
    (matter : D9DoubledMatterFiber) :
    d9PrimitiveSpinCComplexActionCLM
        (derivative +
          Complex.ofReal coefficient * (Complex.I * scalar)) matter =
      d9PrimitiveSpinCComplexActionCLM derivative matter +
        coefficient •
          d9PrimitiveSpinCImaginaryAction
            (d9PrimitiveSpinCComplexActionCLM scalar matter) := by
  change
    d9PrimitiveSpinCComplexActionParameterCLM
        (derivative +
          Complex.ofReal coefficient * (Complex.I * scalar)) matter =
      _
  rw [map_add]
  change
    d9PrimitiveSpinCComplexActionCLM derivative matter +
        d9PrimitiveSpinCComplexActionCLM
          (Complex.ofReal coefficient * (Complex.I * scalar)) matter =
      _
  rw [show
    Complex.ofReal coefficient =
      Complex.ofRealCLM coefficient by rfl]
  rw [d9PrimitiveSpinCComplexAction_ofReal_mul]
  change
    d9PrimitiveSpinCComplexActionCLM derivative matter +
        coefficient •
          d9PrimitiveSpinCComplexActionCLM
            (Complex.I * scalar) matter =
      _
  rw [d9PrimitiveSpinCComplexAction_mul]
  rfl

private theorem d9PrimitiveSpinCHopfFrameCombination_covariant
    (sector : NormalRootChoice) (matter : D9DoubledMatterFiber)
    (coefficient : Real)
    (firstDerivative secondDerivative
      firstScalar secondScalar : Complex) :
    d9PrimitiveSpinCHopfFrameCombination sector matter
        (firstDerivative +
          Complex.ofReal coefficient * (Complex.I * firstScalar))
        (secondDerivative +
          Complex.ofReal coefficient * (Complex.I * secondScalar)) =
      d9PrimitiveSpinCHopfFrameCombination sector matter
          firstDerivative secondDerivative +
        coefficient •
          d9PrimitiveSpinCImaginaryAction
            (d9PrimitiveSpinCHopfFrameCombination sector matter
              firstScalar secondScalar) := by
  unfold d9PrimitiveSpinCHopfFrameCombination
  rw [d9PrimitiveSpinCComplexAction_covariantScalar,
    d9PrimitiveSpinCComplexAction_covariantScalar,
    map_add, smul_add]
  abel

private theorem d9PrimitiveSpinCHopfCovariantFrameCombination
    (sector : NormalRootChoice) (mode : Int)
    (point : ThroatCover period hPeriod) (chart : MonopoleChart)
    (direction : Fin 3) :
    d9PrimitiveSpinCHopfFrameCombination sector
        (primitiveSpinCNormalModeDoubledLift
          period hPeriod sector mode point)
        (d9HopfFirstCovariantFrameDerivative
          period hPeriod chart direction point)
        (d9HopfSecondCovariantFrameDerivative
          period hPeriod chart direction point) =
      d9PrimitiveSpinCHopfFrameCombination sector
          (primitiveSpinCNormalModeDoubledLift
            period hPeriod sector mode point)
          (d9HopfFirstFrameDerivative
            period hPeriod chart direction point)
          (d9HopfSecondFrameDerivative
            period hPeriod chart direction point) +
        d9HopfMonopoleFrameCoefficient
            period hPeriod chart direction point •
          d9PrimitiveSpinCImaginaryAction
            (d9PrimitiveSpinCHopfFrameCombination sector
              (primitiveSpinCNormalModeDoubledLift
                period hPeriod sector mode point)
              (d9HopfFirstScalar period hPeriod chart point)
              (d9HopfSecondScalar period hPeriod chart point)) := by
  unfold d9HopfFirstCovariantFrameDerivative
    d9HopfSecondCovariantFrameDerivative
  exact d9PrimitiveSpinCHopfFrameCombination_covariant
    sector
    (primitiveSpinCNormalModeDoubledLift
      period hPeriod sector mode point)
    (d9HopfMonopoleFrameCoefficient
      period hPeriod chart direction point)
    (d9HopfFirstFrameDerivative
      period hPeriod chart direction point)
    (d9HopfSecondFrameDerivative
      period hPeriod chart direction point)
    (d9HopfFirstScalar period hPeriod chart point)
    (d9HopfSecondScalar period hPeriod chart point)

/-- The monopole-covariant angular derivative cancels the radial
Levi--Civita spin correction in every intrinsic frame direction. -/
theorem d9PrimitiveSpinCHopfCovariantFrameCombination_add_levi_eq_zero
    (sector : NormalRootChoice) (mode : Int)
    (point : ThroatCover period hPeriod) (chart : MonopoleChart)
    (direction : Fin 3)
    (hChart :
      d9MonopoleSphereCoverProjection period hPeriod point ∈
        monopoleChartDomain chart) :
    d9PrimitiveSpinCHopfFrameCombination sector
          (primitiveSpinCNormalModeDoubledLift
            period hPeriod sector mode point)
          (d9HopfFirstCovariantFrameDerivative
            period hPeriod chart direction point)
          (d9HopfSecondCovariantFrameDerivative
            period hPeriod chart direction point) +
        d9LeviCivitaSpinCorrection period hPeriod direction point
          (d9PrimitiveSpinCHopfFrameCombination sector
            (primitiveSpinCNormalModeDoubledLift
              period hPeriod sector mode point)
            (d9HopfFirstScalar period hPeriod chart point)
            (d9HopfSecondScalar period hPeriod chart point)) =
      0 := by
  let matter :=
    d9PrimitiveSpinCHopfFrameCombination sector
      (primitiveSpinCNormalModeDoubledLift
        period hPeriod sector mode point)
      (d9HopfFirstScalar period hPeriod chart point)
      (d9HopfSecondScalar period hPeriod chart point)
  have hCoefficients :=
    d9HopfCovariantDirectionalCoefficients
      period hPeriod point chart direction hChart
  have hAngular :=
    d9PrimitiveSpinCHopfFrameCombination_directional_target
      sector
      (primitiveSpinCNormalModeDoubledLift
        period hPeriod sector mode point)
      (fun coordinate =>
        d9UnitRadialCoordinate period hPeriod coordinate point)
      (d9HopfFirstScalar period hPeriod chart point)
      (d9HopfSecondScalar period hPeriod chart point)
      direction
      (primitiveSpinCNormalModeDoubledLift_gamma_zero
        period hPeriod sector mode point)
      (primitiveSpinCNormalModeDoubledLift_gamma_one
        period hPeriod sector mode point)
  have hRadial :
      d9UnitRadialClifford period hPeriod point matter =
        d9PrimitiveSpinCImaginaryAction matter := by
    simpa [matter, d9HopfFirstScalar, d9HopfSecondScalar] using
      primitiveSpinCHopfFrameCombination_unitRadial_eigen
        period hPeriod sector mode point chart hChart
  change
    d9PrimitiveSpinCHopfFrameCombination sector
          (primitiveSpinCNormalModeDoubledLift
            period hPeriod sector mode point)
          (d9HopfFirstCovariantFrameDerivative
            period hPeriod chart direction point)
          (d9HopfSecondCovariantFrameDerivative
            period hPeriod chart direction point) +
        d9LeviCivitaSpinCorrection
          period hPeriod direction point matter =
      0
  rw [hCoefficients.1, hCoefficients.2, hAngular]
  change
    -(1 / 2 : Real) •
          (d9PrimitiveSpinCImaginaryAction
              (d9DoubledMatterFiberCliffordGammaCLM direction matter) +
            d9UnitRadialCoordinate period hPeriod direction point • matter) +
        d9LeviCivitaSpinCorrection
          period hPeriod direction point matter =
      0
  have hLevi :
      d9LeviCivitaSpinCorrection
          period hPeriod direction point matter =
        (1 / 2 : Real) •
          (d9PrimitiveSpinCImaginaryAction
              (d9DoubledMatterFiberCliffordGammaCLM direction matter) +
            d9UnitRadialCoordinate period hPeriod direction point • matter) :=
    d9LeviCivitaSpinCorrection_of_unitRadial_eigen
      period hPeriod direction point matter hRadial
  rw [hLevi]
  module

private theorem primitiveSpinCHopfZeroModeLocalDirectionalDerivative_mk
    (sector : NormalRootChoice) (mode : Int)
    (point : ThroatCover period hPeriod) (chart : MonopoleChart)
    (direction : Fin 3)
    (hChart :
      d9MonopoleSphereCoverProjection period hPeriod point ∈
        monopoleChartDomain chart) :
    d9PrimitiveSpinCLocalDirectionalDerivative
        (d9PrimitiveSpinCTotalConnectionFrameCoefficient
          period hPeriod chart direction
          (mappingTorusMk (ThroatData period hPeriod) point))
        (d9PrimitiveSpinCLocalLeviCivitaFrameDerivative
          period hPeriod .positiveQuarter
          (primitiveSpinCHopfZeroModeLocalGaugeFamily
            period hPeriod sector mode)
          (point, chart) direction
          (mappingTorusMk (ThroatData period hPeriod) point))
        ((primitiveSpinCHopfZeroModeLocalGaugeFamily
          period hPeriod sector mode).localValue
            (point, chart)
            (mappingTorusMk (ThroatData period hPeriod) point)) =
      d9PrimitiveSpinCHopfFrameCombination sector
          (primitiveSpinCNormalModeDoubledLift
            period hPeriod sector mode point)
          (d9HopfFirstCovariantFrameDerivative
            period hPeriod chart direction point)
          (d9HopfSecondCovariantFrameDerivative
            period hPeriod chart direction point) +
        (normalRootLeviCivitaCorrectedFrequency
            period sector mode *
          d9UnitRadialCoordinate
            period hPeriod direction point) •
          d9PrimitiveSpinCImaginaryAction
            (d9PrimitiveSpinCHopfFrameCombination sector
              (primitiveSpinCNormalModeDoubledLift
                period hPeriod sector mode point)
              (d9HopfFirstScalar period hPeriod chart point)
              (d9HopfSecondScalar period hPeriod chart point)) +
        d9LeviCivitaSpinCorrection period hPeriod direction point
          (d9PrimitiveSpinCHopfFrameCombination sector
            (primitiveSpinCNormalModeDoubledLift
              period hPeriod sector mode point)
            (d9HopfFirstScalar period hPeriod chart point)
            (d9HopfSecondScalar period hPeriod chart point)) := by
  unfold d9PrimitiveSpinCLocalDirectionalDerivative
    d9PrimitiveSpinCLocalLeviCivitaFrameDerivative
  rw [primitiveSpinCHopfZeroModeLocalFlatFrameDerivative_mk
      (hChart := hChart),
    d9PrimitiveSpinCTotalConnectionFrameCoefficient_mk,
    primitiveSpinCHopfZeroModeLocalGaugeFamily_mk,
    d9PrimitiveSpinCBaseLeviCivitaSpinCorrection_mk]
  change
    (d9PrimitiveSpinCHopfFrameCombination sector
          (primitiveSpinCNormalModeDoubledLift
            period hPeriod sector mode point)
          (d9HopfFirstFrameDerivative
            period hPeriod chart direction point)
          (d9HopfSecondFrameDerivative
            period hPeriod chart direction point) +
        (normalRootSpinFrameFrequency period sector mode *
            d9UnitRadialCoordinate
              period hPeriod direction point) •
          d9PrimitiveSpinCImaginaryAction
            (d9PrimitiveSpinCHopfFrameCombination sector
              (primitiveSpinCNormalModeDoubledLift
                period hPeriod sector mode point)
              (d9HopfFirstScalar period hPeriod chart point)
              (d9HopfSecondScalar period hPeriod chart point)) +
      d9LeviCivitaSpinCorrection period hPeriod direction point
        (d9PrimitiveSpinCHopfFrameCombination sector
          (primitiveSpinCNormalModeDoubledLift
            period hPeriod sector mode point)
          (d9HopfFirstScalar period hPeriod chart point)
          (d9HopfSecondScalar period hPeriod chart point))) +
      (d9HopfMonopoleFrameCoefficient
            period hPeriod chart direction point -
          Real.pi / (2 * period) *
            d9UnitRadialCoordinate
              period hPeriod direction point) •
        d9PrimitiveSpinCImaginaryAction
          (d9PrimitiveSpinCHopfFrameCombination sector
            (primitiveSpinCNormalModeDoubledLift
              period hPeriod sector mode point)
            (d9HopfFirstScalar period hPeriod chart point)
            (d9HopfSecondScalar period hPeriod chart point)) = _
  rw [d9PrimitiveSpinCHopfCovariantFrameCombination]
  unfold normalRootLeviCivitaCorrectedFrequency
  module

/-- Directionwise covariant equation for the complete Hopf zero mode.  The
angular monopole derivative and Levi--Civita correction cancel before
Clifford contraction. -/
theorem primitiveSpinCHopfZeroModeLocalDirectionalDerivative_mk_eq_normal
    (sector : NormalRootChoice) (mode : Int)
    (point : ThroatCover period hPeriod) (chart : MonopoleChart)
    (direction : Fin 3)
    (hChart :
      d9MonopoleSphereCoverProjection period hPeriod point ∈
        monopoleChartDomain chart) :
    d9PrimitiveSpinCLocalDirectionalDerivative
        (d9PrimitiveSpinCTotalConnectionFrameCoefficient
          period hPeriod chart direction
          (mappingTorusMk (ThroatData period hPeriod) point))
        (d9PrimitiveSpinCLocalLeviCivitaFrameDerivative
          period hPeriod .positiveQuarter
          (primitiveSpinCHopfZeroModeLocalGaugeFamily
            period hPeriod sector mode)
          (point, chart) direction
          (mappingTorusMk (ThroatData period hPeriod) point))
        ((primitiveSpinCHopfZeroModeLocalGaugeFamily
          period hPeriod sector mode).localValue
            (point, chart)
            (mappingTorusMk (ThroatData period hPeriod) point)) =
      (normalRootLeviCivitaCorrectedFrequency period sector mode *
          d9UnitRadialCoordinate period hPeriod direction point) •
        d9PrimitiveSpinCImaginaryAction
          ((primitiveSpinCHopfZeroModeLocalGaugeFamily
            period hPeriod sector mode).localValue
              (point, chart)
              (mappingTorusMk (ThroatData period hPeriod) point)) := by
  rw [primitiveSpinCHopfZeroModeLocalDirectionalDerivative_mk
      (hChart := hChart),
    primitiveSpinCHopfZeroModeLocalGaugeFamily_mk]
  have hCancel :=
    d9PrimitiveSpinCHopfCovariantFrameCombination_add_levi_eq_zero
      period hPeriod sector mode point chart direction hChart
  let matter :=
    d9PrimitiveSpinCHopfFrameCombination sector
      (primitiveSpinCNormalModeDoubledLift
        period hPeriod sector mode point)
      (d9HopfFirstScalar period hPeriod chart point)
      (d9HopfSecondScalar period hPeriod chart point)
  change
    (d9PrimitiveSpinCHopfFrameCombination sector
          (primitiveSpinCNormalModeDoubledLift
            period hPeriod sector mode point)
          (d9HopfFirstCovariantFrameDerivative
            period hPeriod chart direction point)
          (d9HopfSecondCovariantFrameDerivative
            period hPeriod chart direction point) +
        (normalRootLeviCivitaCorrectedFrequency period sector mode *
          d9UnitRadialCoordinate period hPeriod direction point) •
            d9PrimitiveSpinCImaginaryAction matter) +
        d9LeviCivitaSpinCorrection
          period hPeriod direction point matter =
      (normalRootLeviCivitaCorrectedFrequency period sector mode *
        d9UnitRadialCoordinate period hPeriod direction point) •
          d9PrimitiveSpinCImaginaryAction matter
  linear_combination (norm := module) (1 : Real) • hCancel

private theorem d9PrimitiveSpinCHopfNormalContraction
    (sector : NormalRootChoice) (mode : Int)
    (point : ThroatCover period hPeriod) (chart : MonopoleChart)
    (coefficient : Real)
    (hChart :
      d9MonopoleSphereCoverProjection period hPeriod point ∈
        monopoleChartDomain chart) :
    (∑ direction : Fin 3,
      d9DoubledMatterFiberCliffordGammaCLM direction
        ((coefficient *
            d9UnitRadialCoordinate
              period hPeriod direction point) •
          d9PrimitiveSpinCImaginaryAction
            (d9PrimitiveSpinCHopfFrameCombination sector
              (primitiveSpinCNormalModeDoubledLift
                period hPeriod sector mode point)
              (d9HopfFirstScalar period hPeriod chart point)
              (d9HopfSecondScalar period hPeriod chart point)))) =
      -coefficient •
        d9PrimitiveSpinCHopfFrameCombination sector
          (primitiveSpinCNormalModeDoubledLift
            period hPeriod sector mode point)
          (d9HopfFirstScalar period hPeriod chart point)
          (d9HopfSecondScalar period hPeriod chart point) := by
  let matter :=
    d9PrimitiveSpinCHopfFrameCombination sector
      (primitiveSpinCNormalModeDoubledLift
        period hPeriod sector mode point)
      (d9HopfFirstScalar period hPeriod chart point)
      (d9HopfSecondScalar period hPeriod chart point)
  have hRadial :
      d9UnitRadialClifford period hPeriod point matter =
        d9PrimitiveSpinCImaginaryAction matter := by
    exact primitiveSpinCHopfFrameCombination_unitRadial_eigen
      period hPeriod sector mode point chart hChart
  calc
    _ =
        ∑ direction : Fin 3,
          (coefficient *
              d9UnitRadialCoordinate
                period hPeriod direction point) •
            d9PrimitiveSpinCImaginaryAction
              (d9DoubledMatterFiberCliffordGammaCLM
                direction matter) := by
          apply Finset.sum_congr rfl
          intro direction _
          rw [map_smul,
            ← d9PrimitiveSpinCImaginaryAction_clifford]
    _ =
        coefficient •
          d9PrimitiveSpinCImaginaryAction
            (d9UnitRadialClifford
              period hPeriod point matter) := by
          unfold d9UnitRadialClifford
          rw [map_sum, Finset.smul_sum]
          apply Finset.sum_congr rfl
          intro direction _
          rw [map_smul, smul_smul]
    _ =
        coefficient •
          d9PrimitiveSpinCImaginaryAction
            (d9PrimitiveSpinCImaginaryAction matter) := by
          rw [hRadial]
    _ = -coefficient • matter := by
          rw [d9PrimitiveSpinCImaginaryAction_sq]
          module

private theorem d9PrimitiveSpinCHopfFrameDerivativeContraction_of
    (sector : NormalRootChoice) (matter : D9DoubledMatterFiber)
    (firstDerivative secondDerivative : Fin 3 → Complex)
    (firstScalar secondScalar : Complex)
    (hZero :
      d9DoubledMatterFiberCliffordGammaCLM 0 matter =
        d9PrimitiveSpinCImaginaryAction matter)
    (hOne :
      d9DoubledMatterFiberCliffordGammaCLM 1 matter =
        d9PrimitiveSpinCImaginaryAction
          (d9DoubledMatterFiberCliffordGammaCLM 2 matter))
    (hFirst :
      Complex.I * secondDerivative 0 - secondDerivative 1 +
          Complex.I * firstDerivative 2 =
        Complex.I * firstScalar)
    (hSecond :
      Complex.I * firstDerivative 0 + firstDerivative 1 -
          Complex.I * secondDerivative 2 =
        Complex.I * secondScalar) :
    d9DoubledMatterFiberCliffordGammaCLM 0
          (d9PrimitiveSpinCHopfFrameCombination sector matter
            (firstDerivative 0) (secondDerivative 0)) +
        d9DoubledMatterFiberCliffordGammaCLM 1
          (d9PrimitiveSpinCHopfFrameCombination sector matter
            (firstDerivative 1) (secondDerivative 1)) +
      d9DoubledMatterFiberCliffordGammaCLM 2
        (d9PrimitiveSpinCHopfFrameCombination sector matter
          (firstDerivative 2) (secondDerivative 2)) =
      d9PrimitiveSpinCImaginaryAction
        (d9PrimitiveSpinCHopfFrameCombination sector matter
          firstScalar secondScalar) := by
  have hZeroFirst :=
    d9PrimitiveSpinCHopfFirstFrameCLM_gamma_zero_of
      sector matter hZero
  have hZeroSecond :=
    d9PrimitiveSpinCHopfSecondFrameCLM_gamma_zero_of
      sector matter hZero
  have hOneFirst :=
    d9PrimitiveSpinCHopfFirstFrameCLM_gamma_one_of
      sector matter hOne
  have hOneSecond :=
    d9PrimitiveSpinCHopfSecondFrameCLM_gamma_one_of
      sector matter hOne
  have hTwoFirst :=
    d9PrimitiveSpinCHopfFirstFrameCLM_gamma_two sector matter
  have hTwoSecond :=
    d9PrimitiveSpinCHopfSecondFrameCLM_gamma_two sector matter
  unfold d9PrimitiveSpinCHopfFrameCombination
  simp only [map_add]
  rw [← d9PrimitiveSpinCComplexAction_clifford (firstDerivative 0) 0,
    ← d9PrimitiveSpinCComplexAction_clifford (secondDerivative 0) 0,
    hZeroFirst, hZeroSecond,
    ← d9PrimitiveSpinCComplexAction_clifford (firstDerivative 1) 1,
    ← d9PrimitiveSpinCComplexAction_clifford (secondDerivative 1) 1,
    hOneFirst, hOneSecond,
    ← d9PrimitiveSpinCComplexAction_clifford (firstDerivative 2) 2,
    ← d9PrimitiveSpinCComplexAction_clifford (secondDerivative 2) 2,
    hTwoFirst, hTwoSecond]
  apply d9DoubledMatterFiberHalfSpinorLinearEquiv.injective
  simp only [map_add, map_neg,
    d9DoubledMatterFiberHalfSpinorLinearEquiv_complexAction,
    d9PrimitiveSpinCImaginaryAction,
    d9DoubledMatterFiberHalfSpinorLinearEquiv_phaseAction,
    d9PrimitiveSpinCImaginaryPhase_coe]
  let firstImage :=
    d9DoubledMatterFiberHalfSpinorLinearEquiv
      (d9PrimitiveSpinCHopfFirstFrameCLM sector matter)
  let secondImage :=
    d9DoubledMatterFiberHalfSpinorLinearEquiv
      (d9PrimitiveSpinCHopfSecondFrameCLM sector matter)
  change
    firstDerivative 0 • (Complex.I • secondImage) +
          secondDerivative 0 • (Complex.I • firstImage) +
        (firstDerivative 1 • secondImage +
          -(secondDerivative 1 • firstImage)) +
      (firstDerivative 2 • (Complex.I • firstImage) +
        -(secondDerivative 2 • (Complex.I • secondImage))) =
      Complex.I • firstScalar • firstImage +
        Complex.I • secondScalar • secondImage
  calc
    _ =
        (Complex.I * secondDerivative 0 - secondDerivative 1 +
            Complex.I * firstDerivative 2) • firstImage +
          (Complex.I * firstDerivative 0 + firstDerivative 1 -
            Complex.I * secondDerivative 2) • secondImage := by
      module
    _ =
        (Complex.I * firstScalar) • firstImage +
          (Complex.I * secondScalar) • secondImage := by
      rw [hFirst, hSecond]
    _ = _ := by module

/-- Clifford contraction of the monopole-covariant angular derivative of the
Hopf mode.  The identity holds in either polar gauge. -/
theorem d9PrimitiveSpinCHopfCovariantAngularContraction
    (sector : NormalRootChoice) (mode : Int)
    (point : ThroatCover period hPeriod) (chart : MonopoleChart)
    (hChart :
      d9MonopoleSphereCoverProjection period hPeriod point ∈
        monopoleChartDomain chart) :
    d9DoubledMatterFiberCliffordGammaCLM 0
          (d9PrimitiveSpinCHopfFrameCombination sector
            (primitiveSpinCNormalModeDoubledLift
              period hPeriod sector mode point)
            (d9HopfFirstCovariantFrameDerivative
              period hPeriod chart 0 point)
            (d9HopfSecondCovariantFrameDerivative
              period hPeriod chart 0 point)) +
        d9DoubledMatterFiberCliffordGammaCLM 1
          (d9PrimitiveSpinCHopfFrameCombination sector
            (primitiveSpinCNormalModeDoubledLift
              period hPeriod sector mode point)
            (d9HopfFirstCovariantFrameDerivative
              period hPeriod chart 1 point)
            (d9HopfSecondCovariantFrameDerivative
              period hPeriod chart 1 point)) +
      d9DoubledMatterFiberCliffordGammaCLM 2
        (d9PrimitiveSpinCHopfFrameCombination sector
          (primitiveSpinCNormalModeDoubledLift
            period hPeriod sector mode point)
          (d9HopfFirstCovariantFrameDerivative
            period hPeriod chart 2 point)
          (d9HopfSecondCovariantFrameDerivative
            period hPeriod chart 2 point)) =
      d9PrimitiveSpinCImaginaryAction
        (d9PrimitiveSpinCHopfFrameCombination sector
          (primitiveSpinCNormalModeDoubledLift
            period hPeriod sector mode point)
          (d9HopfFirstScalar period hPeriod chart point)
          (d9HopfSecondScalar period hPeriod chart point)) := by
  cases chart with
  | north =>
      have hCoefficients :=
        d9HopfNorthCovariantContraction period hPeriod point hChart
      exact d9PrimitiveSpinCHopfFrameDerivativeContraction_of
        sector
        (primitiveSpinCNormalModeDoubledLift
          period hPeriod sector mode point)
        (d9HopfFirstCovariantFrameDerivative
          period hPeriod .north · point)
        (d9HopfSecondCovariantFrameDerivative
          period hPeriod .north · point)
        (d9HopfFirstScalar period hPeriod .north point)
        (d9HopfSecondScalar period hPeriod .north point)
        (primitiveSpinCNormalModeDoubledLift_gamma_zero
          period hPeriod sector mode point)
        (primitiveSpinCNormalModeDoubledLift_gamma_one
          period hPeriod sector mode point)
        hCoefficients.1 hCoefficients.2
  | south =>
      have hCoefficients :=
        d9HopfSouthCovariantContraction period hPeriod point hChart
      exact d9PrimitiveSpinCHopfFrameDerivativeContraction_of
        sector
        (primitiveSpinCNormalModeDoubledLift
          period hPeriod sector mode point)
        (d9HopfFirstCovariantFrameDerivative
          period hPeriod .south · point)
        (d9HopfSecondCovariantFrameDerivative
          period hPeriod .south · point)
        (d9HopfFirstScalar period hPeriod .south point)
        (d9HopfSecondScalar period hPeriod .south point)
        (primitiveSpinCNormalModeDoubledLift_gamma_zero
          period hPeriod sector mode point)
        (primitiveSpinCNormalModeDoubledLift_gamma_one
          period hPeriod sector mode point)
        hCoefficients.1 hCoefficients.2

/-- The complete local Hopf mode is an eigenspinor of the coupled geometric
Dirac operator with the Levi--Civita-corrected normal frequency. -/
theorem primitiveSpinCHopfZeroModeLocalGeometricDirac_mk
    (sector : NormalRootChoice) (mode : Int)
    (point : ThroatCover period hPeriod) (chart : MonopoleChart)
    (hChart :
      d9MonopoleSphereCoverProjection period hPeriod point ∈
        monopoleChartDomain chart) :
    d9PrimitiveSpinCLocalGeometricDirac
        period hPeriod .positiveQuarter
        (primitiveSpinCHopfZeroModeLocalGaugeFamily
          period hPeriod sector mode)
        (point, chart)
        (mappingTorusMk (ThroatData period hPeriod) point) =
      -normalRootLeviCivitaCorrectedFrequency period sector mode •
        (primitiveSpinCHopfZeroModeLocalGaugeFamily
          period hPeriod sector mode).localValue
            (point, chart)
            (mappingTorusMk (ThroatData period hPeriod) point) := by
  let matter :=
    d9PrimitiveSpinCHopfFrameCombination sector
      (primitiveSpinCNormalModeDoubledLift
        period hPeriod sector mode point)
      (d9HopfFirstScalar period hPeriod chart point)
      (d9HopfSecondScalar period hPeriod chart point)
  have hValue :
      (primitiveSpinCHopfZeroModeLocalGaugeFamily
        period hPeriod sector mode).localValue
          (point, chart)
          (mappingTorusMk (ThroatData period hPeriod) point) =
        matter := by
    rw [primitiveSpinCHopfZeroModeLocalGaugeFamily_mk]
    rfl
  have hAngular :=
    d9PrimitiveSpinCHopfCovariantAngularContraction
      period hPeriod sector mode point chart hChart
  have hAngularSum :
      (∑ direction : Fin 3,
        d9DoubledMatterFiberCliffordGammaCLM direction
          (d9PrimitiveSpinCHopfFrameCombination sector
            (primitiveSpinCNormalModeDoubledLift
              period hPeriod sector mode point)
            (d9HopfFirstCovariantFrameDerivative
              period hPeriod chart direction point)
            (d9HopfSecondCovariantFrameDerivative
              period hPeriod chart direction point))) =
        d9PrimitiveSpinCImaginaryAction matter := by
    simpa [Fin.sum_univ_succ, matter, add_assoc] using hAngular
  have hNormal :
      (∑ direction : Fin 3,
        d9DoubledMatterFiberCliffordGammaCLM direction
          ((normalRootLeviCivitaCorrectedFrequency
                period sector mode *
              d9UnitRadialCoordinate
                period hPeriod direction point) •
            d9PrimitiveSpinCImaginaryAction matter)) =
        -normalRootLeviCivitaCorrectedFrequency period sector mode •
          matter := by
    simpa [matter] using
      d9PrimitiveSpinCHopfNormalContraction
        period hPeriod sector mode point chart
        (normalRootLeviCivitaCorrectedFrequency
          period sector mode) hChart
  have hLevi :=
    d9LeviCivitaSpinCorrection_contraction
      period hPeriod point matter
  have hRadial :
      d9UnitRadialClifford period hPeriod point matter =
        d9PrimitiveSpinCImaginaryAction matter := by
    exact primitiveSpinCHopfFrameCombination_unitRadial_eigen
      period hPeriod sector mode point chart hChart
  unfold d9PrimitiveSpinCLocalGeometricDirac
    d9PrimitiveSpinCLocalDirac
  simp_rw [
    primitiveSpinCHopfZeroModeLocalDirectionalDerivative_mk
      (hChart := hChart)]
  simp only [map_add, Finset.sum_add_distrib]
  rw [hAngularSum, hNormal, hLevi, hRadial, hValue]
  abel

/-- Global descended eigenspinor equation for the complete Hopf mode. -/
theorem primitiveSpinCHopfZeroModeGeometricDiracSection_eigen
    (sector : NormalRootChoice) (mode : Int) :
    d9PrimitiveSpinCGeometricDiracSection
        period hPeriod .positiveQuarter
        (primitiveSpinCHopfZeroModeLocalGaugeFamily
          period hPeriod sector mode) =
      -normalRootLeviCivitaCorrectedFrequency period sector mode •
        primitiveSpinCHopfZeroModeSection
          period hPeriod sector mode := by
  ext base
  let core :=
    d9PrimitiveSpinCVectorBundleCore
      period hPeriod .positiveQuarter
  let point :=
    normalBundleIndexAt period hPeriod base
  let chart :=
    (d9PrimitiveMonopolePrincipalBundleCore
      period hPeriod 1).indexAt base
  have hProject :
      mappingTorusMk (ThroatData period hPeriod) point = base := by
    exact normalBundleIndexAt_projects period hPeriod base
  have hChartBase :
      base ∈ d9PrimitiveMonopoleChartDomain
        period hPeriod chart := by
    exact (core.mem_baseSet_at base).2
  have hChart :
      d9MonopoleSphereCoverProjection period hPeriod point ∈
        monopoleChartDomain chart := by
    unfold d9PrimitiveMonopoleChartDomain at hChartBase
    rw [← hProject] at hChartBase
    exact hChartBase
  have hLocal :=
    primitiveSpinCHopfZeroModeLocalGeometricDirac_mk
      period hPeriod sector mode point chart hChart
  rw [d9PrimitiveSpinCGeometricDiracSection_apply]
  change
    d9PrimitiveSpinCLocalGeometricDirac
        period hPeriod .positiveQuarter
        (primitiveSpinCHopfZeroModeLocalGaugeFamily
          period hPeriod sector mode)
        (point, chart) base =
      -normalRootLeviCivitaCorrectedFrequency period sector mode •
        (primitiveSpinCHopfZeroModeLocalGaugeFamily
          period hPeriod sector mode).localValue
            (point, chart) base
  rw [← hProject]
  exact hLocal

theorem d9PrimitiveSpinCGeometricDiracOperator_toSmoothSection
    (choice : NormalRootChoice)
    (family :
      SmoothPrimitiveSpinCLocalGaugeFamily period hPeriod choice) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod choice
        (family.toSmoothSection period hPeriod choice) =
      d9PrimitiveSpinCGeometricDiracSection
        period hPeriod choice family := by
  ext base
  let core :=
    d9PrimitiveSpinCVectorBundleCore period hPeriod choice
  let state :=
    family.toSmoothSection period hPeriod choice
  let recovered :=
    d9PrimitiveSpinCSmoothSectionLocalGaugeFamily
      period hPeriod choice state
  let index := core.indexAt base
  have hBase :
      base ∈ d9PrimitiveSpinCBaseSet period hPeriod index :=
    core.mem_baseSet_at base
  have hEventually :
      recovered.localValue index =ᶠ[nhds base]
        family.localValue index := by
    filter_upwards
      [(d9PrimitiveSpinCBaseSet_isOpen
        period hPeriod index).mem_nhds hBase] with current hCurrent
    change
      (core.localTriv index
        (primitiveSpinCBundleSection
          period hPeriod choice family current)).2 =
        family.localValue index current
    exact primitiveSpinCBundleSection_localTriv
      period hPeriod choice family index current hCurrent
  have hValue :
      recovered.localValue index base =
        family.localValue index base :=
    hEventually.self_of_nhds
  have hFlat (direction : Fin 3) :
      d9PrimitiveSpinCLocalFlatFrameDerivative
          period hPeriod choice recovered index direction base =
        d9PrimitiveSpinCLocalFlatFrameDerivative
          period hPeriod choice family index direction base := by
    unfold d9PrimitiveSpinCLocalFlatFrameDerivative
    rw [hEventually.mfderiv_eq]
    rfl
  unfold d9PrimitiveSpinCGeometricDiracOperator
  rw [d9PrimitiveSpinCGeometricDiracSection_apply,
    d9PrimitiveSpinCGeometricDiracSection_apply]
  change
    d9PrimitiveSpinCLocalGeometricDirac
        period hPeriod choice recovered index base =
      d9PrimitiveSpinCLocalGeometricDirac
        period hPeriod choice family index base
  unfold d9PrimitiveSpinCLocalGeometricDirac
    d9PrimitiveSpinCLocalDirac
    d9PrimitiveSpinCLocalDirectionalDerivative
    d9PrimitiveSpinCLocalLeviCivitaFrameDerivative
  simp_rw [hFlat, hValue]

/-- Operator-level global eigenspinor equation for every normal-root mode. -/
theorem primitiveSpinCHopfZeroModeGeometricDiracOperator_eigen
    (sector : NormalRootChoice) (mode : Int) :
    d9PrimitiveSpinCGeometricDiracOperator
        period hPeriod .positiveQuarter
        (primitiveSpinCHopfZeroModeSection
          period hPeriod sector mode) =
      -normalRootLeviCivitaCorrectedFrequency period sector mode •
        primitiveSpinCHopfZeroModeSection
          period hPeriod sector mode := by
  unfold primitiveSpinCHopfZeroModeSection
  rw [d9PrimitiveSpinCGeometricDiracOperator_toSmoothSection]
  exact primitiveSpinCHopfZeroModeGeometricDiracSection_eigen
    period hPeriod sector mode

end
end P0EFTJanusProgramPD9PrimitiveSpinCHopfZeroModeDiracEquation4D
end JanusFormal
