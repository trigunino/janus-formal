import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Geometry.Manifold.Algebra.SMul
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualBulkBackgroundChartwiseSecondOrderJetExtraction4D

/-!
# Actual throat Abelian-potential chartwise second-order jets

This gate pulls the two genuine Candidate-A `U(1)^2` potentials back to the
fixed throat.  Around a chosen throat point, the pullback is evaluated on the
three members of the tangent-bundle frame supplied by the centered
trivialization.  The resulting smooth coefficients determine a covector germ
and hence a genuine second-order jet.

An explicit fixed linear equivalence transports the throat-coordinate jet to
`EuclideanR3`, giving exactly the gauge-connection field type of the physical
structured-background carrier.

No throat Christoffel form, second fundamental form, physical normal, full
structured background, overlap law or global jet-bundle extraction is
asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatAbelianPotentialChartwiseSecondOrderJetExtraction4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 300000

noncomputable section

open Set
open scoped Manifold ContDiff RealInnerProductSpace
open Bundle
open Module
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPPhysicalSecondOrderJetChartwiseExtraction4D
open P0EFTJanusProgramPActualBulkBackgroundChartwiseSecondOrderJetExtraction4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*}
variable [Fintype NonNullFace] [Fintype NullFace]

/-! ## The intrinsic pullback -/

/-- A smooth paired Abelian covector on the actual throat.  Smoothness is
recorded intrinsically by evaluation on its genuine tangent bundle. -/
structure SmoothThroatAbelianGaugePotential where
  toFun : Fin 2 → ∀ point : EffectiveThroat period hPeriod,
    ThroatTangentFiber period hPeriod point →L[Real] Real
  contMDiff_eval : ∀ component : Fin 2,
    ContMDiff throatCoverModelWithCorners.tangent
      (modelWithCornersSelf Real Real) ∞
      (fun vector : TangentBundle throatCoverModelWithCorners
          (EffectiveThroat period hPeriod) =>
        toFun component vector.1 vector.2)

/-- Pointwise pullback of an ambient Abelian potential through the actual
fixed-throat inclusion. -/
def throatGaugePullbackValue
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2) (point : EffectiveThroat period hPeriod) :
    ThroatCotangentFiber period hPeriod point :=
  (potential.toFun component
      (fixedThroatQuotientInclusion period hPeriod point)).comp
    (mfderiv throatCoverModelWithCorners coverModelWithCorners
      (fixedThroatQuotientInclusion period hPeriod) point)

@[simp]
theorem throatGaugePullbackValue_apply
    (potential : SmoothAbelianGaugePotential period hPeriod)
    (component : Fin 2) (point : EffectiveThroat period hPeriod)
    (vector : ThroatTangentFiber period hPeriod point) :
    throatGaugePullbackValue period hPeriod potential component point vector =
      potential.toFun component
        (fixedThroatQuotientInclusion period hPeriod point)
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatQuotientInclusion period hPeriod) point vector) :=
  rfl

/-- The ambient paired potential restricted to the actual throat. -/
def restrictAbelianGaugePotentialToThroat
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    SmoothThroatAbelianGaugePotential period hPeriod where
  toFun := throatGaugePullbackValue period hPeriod potential
  contMDiff_eval := fun component => by
    have hTangent :=
      (fixedThroatQuotientInclusion_contMDiff period hPeriod)
        |>.contMDiff_tangentMap (m := ∞) (by simp)
    exact (potential.contMDiff_eval component).comp hTangent

/-- The two actual Candidate-A potentials, after intrinsic throat pullback. -/
def globalCandidateAThroatPotentialBySector
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace) :
    Sector → SmoothThroatAbelianGaugePotential period hPeriod :=
  fun sector =>
    restrictAbelianGaugePotentialToThroat period hPeriod
      (globalCandidateABulkPotentialBySector period hPeriod data sector)

@[simp]
theorem globalCandidateAThroatPotentialBySector_apply
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (sector : Sector) (component : Fin 2)
    (point : EffectiveThroat period hPeriod)
    (vector : ThroatTangentFiber period hPeriod point) :
    (globalCandidateAThroatPotentialBySector period hPeriod data sector).toFun
        component point vector =
      (globalCandidateABulkPotentialBySector period hPeriod data sector).toFun
        component (fixedThroatQuotientInclusion period hPeriod point)
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatQuotientInclusion period hPeriod) point vector) :=
  rfl

/-! ## A fixed three-dimensional coordinate equivalence -/

/-- The fixed split `(x₀,x₁,x₂) ↦ ((x₁,x₂),x₀)` from the
Euclidean carrier to the intrinsic throat-coordinate model. -/
def throatRadialReferenceLinearEquiv :
    EuclideanR3 ≃ₗ[Real] ThroatCoverCoordinates where
  toFun point :=
    ((EuclideanSpace.equiv (Fin 2) Real).symm
      (fun index => point index.succ), point 0)
  invFun coordinates :=
    (EuclideanSpace.equiv (Fin 3) Real).symm
      (fun index => Fin.cases coordinates.2
        (fun tail => coordinates.1 tail) index)
  left_inv point := by
    apply (EuclideanSpace.equiv (Fin 3) Real).injective
    funext index
    refine Fin.cases ?_ (fun tail => ?_) index <;> simp
  right_inv coordinates := by
    apply Prod.ext
    · apply (EuclideanSpace.equiv (Fin 2) Real).injective
      funext index
      simp
    · simp
  map_add' first second := by
    apply Prod.ext
    · apply (EuclideanSpace.equiv (Fin 2) Real).injective
      funext index
      simp
    · simp
  map_smul' scalar point := by
    apply Prod.ext
    · apply (EuclideanSpace.equiv (Fin 2) Real).injective
      funext index
      simp
    · simp

/-- Continuous version of the fixed three-dimensional split. -/
def throatRadialReferenceEquiv :
    EuclideanR3 ≃L[Real] ThroatCoverCoordinates :=
  throatRadialReferenceLinearEquiv.toContinuousLinearEquiv

/-- The inverse identification, oriented from throat coordinates to the
physical `EuclideanR3` carrier. -/
def throatToEuclideanEquiv :
    ThroatCoverCoordinates ≃L[Real] EuclideanR3 :=
  throatRadialReferenceEquiv.symm

/-- Coordinate basis of the throat model induced by the fixed split. -/
def throatRadialReferenceBasis :
    Basis (Fin 3) Real ThroatCoverCoordinates :=
  (EuclideanSpace.basisFun (Fin 3) Real).toBasis.map
    throatRadialReferenceEquiv.toLinearEquiv

/-- The fixed coordinate covectors dual to `throatRadialReferenceBasis`. -/
def throatRadialReferenceCovector (index : Fin 3) :
    FramedCovector ThroatCoverCoordinates :=
  (EuclideanSpace.proj index).comp
    throatRadialReferenceEquiv.symm.toContinuousLinearMap

@[simp]
theorem throatRadialReferenceCovector_apply
    (index : Fin 3) (vector : ThroatCoverCoordinates) :
    throatRadialReferenceCovector index vector =
      throatRadialReferenceEquiv.symm vector index :=
  rfl

/-! ## Centered trivialization coefficients and germs -/

/-- Evaluation of one throat potential component on one member of the local
frame associated with the tangent trivialization centered at `anchor`. -/
def throatGaugeLocalCoefficient
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2) (anchor : EffectiveThroat period hPeriod)
    (index : Fin 3) (current : EffectiveThroat period hPeriod) : Real :=
  potential.toFun component current
    ((trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) anchor).localFrame (𝕜 := Real)
        throatRadialReferenceBasis index current)

theorem throatGaugeLocalCoefficient_contMDiffAt
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2) (anchor : EffectiveThroat period hPeriod)
    (index : Fin 3) :
    ContMDiffAt throatCoverModelWithCorners
      (modelWithCornersSelf Real Real) ∞
      (throatGaugeLocalCoefficient period hPeriod potential component anchor
        index) anchor := by
  have hAnchor : anchor ∈
      (trivializationAt ThroatCoverCoordinates
        (ThroatTangentFiber period hPeriod) anchor).baseSet :=
    mem_baseSet_trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) anchor
  have hFrame := contMDiffAt_localFrame_of_mem
    (𝕜 := Real) (I := throatCoverModelWithCorners) (n := ∞)
    (e := trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) anchor)
    (b := throatRadialReferenceBasis) index hAnchor
  have hSmooth :=
    (potential.contMDiff_eval component).contMDiffAt.comp anchor hFrame
  refine hSmooth.congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
  intro current
  rfl

/-- Covector coefficients in the tangent trivialization centered at `anchor`.
The finite expansion makes its smoothness explicit. -/
def throatGaugeCovectorCoordinates
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2) (anchor current : EffectiveThroat period hPeriod) :
    FramedCovector ThroatCoverCoordinates :=
  ∑ index : Fin 3,
    throatGaugeLocalCoefficient period hPeriod potential component anchor
        index current •
      throatRadialReferenceCovector index

theorem throatGaugeCovectorCoordinates_contMDiffAt
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2) (anchor : EffectiveThroat period hPeriod) :
    ContMDiffAt throatCoverModelWithCorners
      (modelWithCornersSelf Real
        (FramedCovector ThroatCoverCoordinates)) ∞
      (throatGaugeCovectorCoordinates period hPeriod potential component
        anchor) anchor := by
  letI : IsBoundedSMul Real (FramedCovector ThroatCoverCoordinates) :=
    { dist_smul_pair' := fun scalar left right => by
        simp only [dist_eq_norm]
        rw [show scalar • left - scalar • right =
          scalar • (left - right) by exact (smul_sub scalar left right).symm]
        simpa using
          ContinuousLinearMap.opNorm_smul_le scalar (left - right)
      dist_pair_smul' := fun left right covector => by
        simp only [dist_eq_norm]
        rw [show left • covector - right • covector =
          (left - right) • covector by exact (sub_smul left right covector).symm]
        simpa using
          ContinuousLinearMap.opNorm_smul_le (left - right) covector }
  apply ContMDiffAt.sum
  intro index _
  exact (throatGaugeLocalCoefficient_contMDiffAt period hPeriod potential
    component anchor index).smul
      (contMDiffAt_const (c := throatRadialReferenceCovector index))

@[simp]
theorem throatGaugeCovectorCoordinates_apply
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2) (anchor current : EffectiveThroat period hPeriod)
    (vector : ThroatCoverCoordinates) :
    throatGaugeCovectorCoordinates period hPeriod potential component anchor
        current vector =
      ∑ index : Fin 3,
        throatGaugeLocalCoefficient period hPeriod potential component anchor
            index current *
          throatRadialReferenceEquiv.symm vector index := by
  simp [throatGaugeCovectorCoordinates]

/-- Coordinate germ of one pulled-back potential component in the extended
throat chart centered at `anchor`. -/
def throatGaugeCovectorChartGerm
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2) (anchor : EffectiveThroat period hPeriod) :
    ThroatCoverCoordinates → FramedCovector ThroatCoverCoordinates :=
  throatGaugeCovectorCoordinates period hPeriod potential component anchor ∘
    (extChartAt throatCoverModelWithCorners anchor).symm

theorem throatGaugeCovectorChartGerm_contDiffAt_two
    (potential : SmoothThroatAbelianGaugePotential period hPeriod)
    (component : Fin 2) (anchor : EffectiveThroat period hPeriod) :
    ContDiffAt Real 2
      (throatGaugeCovectorChartGerm period hPeriod potential component anchor)
      (extChartAt throatCoverModelWithCorners anchor anchor) := by
  have hCoordinates : ContMDiffAt throatCoverModelWithCorners
      (modelWithCornersSelf Real
        (FramedCovector ThroatCoverCoordinates)) 2
      (throatGaugeCovectorCoordinates period hPeriod potential component
        anchor) anchor :=
    (throatGaugeCovectorCoordinates_contMDiffAt period hPeriod potential
      component anchor).of_le (by
        show (2 : ℕ∞ω) ≤ ∞
        exact WithTop.coe_le_coe.mpr le_top)
  have hSource := (contMDiffAt_iff_source).mp hCoordinates
  have hRange : Set.range throatCoverModelWithCorners = Set.univ := by
    ext coordinate
    simp
  rw [hRange, contMDiffWithinAt_univ] at hSource
  exact hSource.contDiffAt

/-! ## Intrinsic throat-coordinate jets -/

/-- Actual second jet of one sector and Abelian component in intrinsic throat
coordinates. -/
def globalCandidateAThroatGaugeSecondOrderJetAt
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (sector : Sector) (component : Fin 2)
    (anchor : EffectiveThroat period hPeriod) :
    FramedSecondOrderJet ThroatCoverCoordinates
      (FramedCovector ThroatCoverCoordinates) :=
  chartwiseSecondOrderJetAt
    (throatGaugeCovectorChartGerm period hPeriod
      (globalCandidateAThroatPotentialBySector period hPeriod data sector)
      component anchor)
    (extChartAt throatCoverModelWithCorners anchor anchor)
    (throatGaugeCovectorChartGerm_contDiffAt_two period hPeriod
      (globalCandidateAThroatPotentialBySector period hPeriod data sector)
      component anchor)

@[simp]
theorem globalCandidateAThroatGaugeSecondOrderJetAt_value_apply
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (sector : Sector) (component : Fin 2)
    (anchor : EffectiveThroat period hPeriod)
    (vector : ThroatCoverCoordinates) :
    (globalCandidateAThroatGaugeSecondOrderJetAt period hPeriod data sector
        component anchor).value vector =
      ∑ index : Fin 3,
        throatGaugeLocalCoefficient period hPeriod
            (globalCandidateAThroatPotentialBySector
              period hPeriod data sector)
            component anchor index anchor *
          throatRadialReferenceEquiv.symm vector index := by
  rw [globalCandidateAThroatGaugeSecondOrderJetAt,
    chartwiseSecondOrderJetAt_value]
  unfold throatGaugeCovectorChartGerm
  rw [Function.comp_apply, extChartAt_to_inv]
  exact throatGaugeCovectorCoordinates_apply period hPeriod _ _ _ _ _

theorem globalCandidateAThroatGaugeSecondOrderJetAt_secondDerivative_symmetric
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (sector : Sector) (component : Fin 2)
    (anchor : EffectiveThroat period hPeriod)
    (first second : ThroatCoverCoordinates) :
    (globalCandidateAThroatGaugeSecondOrderJetAt period hPeriod data sector
        component anchor).secondDerivative first second =
      (globalCandidateAThroatGaugeSecondOrderJetAt period hPeriod data sector
        component anchor).secondDerivative second first :=
  (globalCandidateAThroatGaugeSecondOrderJetAt period hPeriod data sector
    component anchor).secondDerivative_symmetric first second

/-! ## Transport to the physical Euclidean carrier -/

/-- Fixed pullback equivalence on covector models. -/
def throatCovectorToEuclideanEquiv :
    FramedCovector ThroatCoverCoordinates ≃L[Real]
      FramedCovector EuclideanR3 :=
  throatToEuclideanEquiv.arrowCongr
    (ContinuousLinearEquiv.refl Real Real)

/-- Transport all three levels of a throat-coordinate jet to `EuclideanR3`. -/
def transportThroatGaugeSecondOrderJetToEuclidean
    (jet : FramedSecondOrderJet ThroatCoverCoordinates
      (FramedCovector ThroatCoverCoordinates)) :
    FramedSecondOrderJet EuclideanR3 (FramedCovector EuclideanR3) where
  value := throatCovectorToEuclideanEquiv jet.value
  firstDerivative :=
    throatToEuclideanEquiv.arrowCongr throatCovectorToEuclideanEquiv
      jet.firstDerivative
  secondDerivative :=
    throatToEuclideanEquiv.arrowCongr
      (throatToEuclideanEquiv.arrowCongr throatCovectorToEuclideanEquiv)
      jet.secondDerivative
  secondDerivative_symmetric := by
    intro first second
    simp only [ContinuousLinearEquiv.arrowCongr_apply]
    rw [jet.secondDerivative_symmetric
      (throatToEuclideanEquiv.symm first)
      (throatToEuclideanEquiv.symm second)]

@[simp]
theorem transportThroatGaugeSecondOrderJetToEuclidean_value_apply
    (jet : FramedSecondOrderJet ThroatCoverCoordinates
      (FramedCovector ThroatCoverCoordinates))
    (vector : EuclideanR3) :
    (transportThroatGaugeSecondOrderJetToEuclidean jet).value vector =
      jet.value (throatRadialReferenceEquiv vector) :=
  rfl

/-- Actual Candidate-A throat gauge jet with exactly the gauge-connection
field type of `StructuredBackgroundSecondJet EuclideanR3`. -/
def globalCandidateAThroatGaugeEuclideanSecondOrderJetAt
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (sector : Sector) (component : Fin 2)
    (anchor : EffectiveThroat period hPeriod) :
    FramedSecondOrderJet EuclideanR3 (FramedCovector EuclideanR3) :=
  transportThroatGaugeSecondOrderJetToEuclidean
    (globalCandidateAThroatGaugeSecondOrderJetAt period hPeriod data sector
      component anchor)

@[simp]
theorem globalCandidateAThroatGaugeEuclideanSecondOrderJetAt_value_apply
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (sector : Sector) (component : Fin 2)
    (anchor : EffectiveThroat period hPeriod)
    (vector : EuclideanR3) :
    (globalCandidateAThroatGaugeEuclideanSecondOrderJetAt period hPeriod data
        sector component anchor).value vector =
      ∑ index : Fin 3,
        throatGaugeLocalCoefficient period hPeriod
            (globalCandidateAThroatPotentialBySector
              period hPeriod data sector)
            component anchor index anchor * vector index := by
  rw [globalCandidateAThroatGaugeEuclideanSecondOrderJetAt,
    transportThroatGaugeSecondOrderJetToEuclidean_value_apply,
    globalCandidateAThroatGaugeSecondOrderJetAt_value_apply]
  simp

theorem globalCandidateAThroatGaugeEuclideanSecondOrderJetAt_secondDerivative_symmetric
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (sector : Sector) (component : Fin 2)
    (anchor : EffectiveThroat period hPeriod)
    (first second : EuclideanR3) :
    (globalCandidateAThroatGaugeEuclideanSecondOrderJetAt period hPeriod data
        sector component anchor).secondDerivative first second =
      (globalCandidateAThroatGaugeEuclideanSecondOrderJetAt period hPeriod data
        sector component anchor).secondDerivative second first :=
  (globalCandidateAThroatGaugeEuclideanSecondOrderJetAt period hPeriod data
    sector component anchor).secondDerivative_symmetric first second

/-! ## Exact partial gauge package -/

/-- The realized throat-background gauge core.  It deliberately contains no
tangential quadratic, normal quadratic or physical normal. -/
structure ActualThroatGaugeSecondJetCore
    (_configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) where
  point : ProgramPThroatJetBase period hPeriod
  gaugeConnection : Sector → Fin 2 →
    FramedSecondOrderJet EuclideanR3 (FramedCovector EuclideanR3)

/-- Simultaneous extraction of all four actual sector/component throat gauge
jets at one genuine throat point. -/
def globalCandidateAActualThroatGaugeSecondJetCore
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (anchor : EffectiveThroat period hPeriod) :
    ActualThroatGaugeSecondJetCore period hPeriod configuration where
  point := anchor
  gaugeConnection := fun sector component =>
    globalCandidateAThroatGaugeEuclideanSecondOrderJetAt
      period hPeriod data sector component anchor

@[simp]
theorem globalCandidateAActualThroatGaugeSecondJetCore_point
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (anchor : EffectiveThroat period hPeriod) :
    (globalCandidateAActualThroatGaugeSecondJetCore period hPeriod
      configuration data anchor).point = anchor :=
  rfl

@[simp]
theorem globalCandidateAActualThroatGaugeSecondJetCore_gaugeConnection
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (anchor : EffectiveThroat period hPeriod)
    (sector : Sector) (component : Fin 2) :
    (globalCandidateAActualThroatGaugeSecondJetCore period hPeriod
      configuration data anchor).gaugeConnection sector component =
      globalCandidateAThroatGaugeEuclideanSecondOrderJetAt
        period hPeriod data sector component anchor :=
  rfl

end
end P0EFTJanusProgramPActualThroatAbelianPotentialChartwiseSecondOrderJetExtraction4D
end JanusFormal
