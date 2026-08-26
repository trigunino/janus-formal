import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalMetricChartwiseSecondOrderJetExtraction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCovariantAction4D

/-!
# Actual chartwise bulk-background jets for Program P

This gate extracts the part of the bulk structured background which is
already supplied by the global Candidate-A action domain.  In each physical
sector it records the actual local Levi--Civita Christoffel coefficients and
their symmetric continuous bilinear representative.  It also takes the
genuine intrinsic `U(1)^2` potential from the regular Maxwell line and forms
the value, first derivative and symmetric second derivative of each local
covector representative.

Both the split cover-coordinate jets and their `EuclideanR4` versions are
exposed.  The latter have exactly the `tangentialQuadratic` and
`gaugeConnection` field types of `StructuredBackgroundSecondJet`.

No normal quadratic form, physical normal, full structured-background
constructor, chart-overlap law, or global jet-bundle extraction is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualBulkBackgroundChartwiseSecondOrderJetExtraction4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellCurvature4D
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusRieszShapeOperatorContinuousStructuredJetReduction
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPPhysicalSecondOrderJetChartwiseExtraction4D
open P0EFTJanusProgramPGlobalMetricChartwiseSecondOrderJetExtraction4D

variable (period : Real) (hPeriod : period ≠ 0)

abbrev Index4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Index4
abbrev Vector4 := P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4

variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*}
variable [Fintype NonNullFace] [Fintype NullFace]

/-! ## Actual sector selectors -/

/-- The regular metric line selected by an outer physical sector. -/
def globalCandidateABulkRegularMetricBySector
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace) :
    Sector → RegularGeneralLorentzMetric period hPeriod
  | .plus => data.plusGravity.metric
  | .minus => data.minusGravity.metric

/-- The genuine intrinsic paired Abelian potential selected by sector. -/
def globalCandidateABulkPotentialBySector
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace) :
    Sector → SmoothAbelianGaugePotential period hPeriod
  | .plus => data.plusMaxwell.potential
  | .minus => data.minusMaxwell.potential

/-- The coefficient-packet gauge field selected by sector. -/
def globalGaugeFixedBulkGaugeFieldBySector
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) :
    Sector → SmoothQuotientField period hPeriod GaugeFiber
  | .plus => configuration.physical.coefficientFields.gauge.1
  | .minus => configuration.physical.coefficientFields.gauge.2

/-- The regular action metric is the corresponding metric of the unique
physical configuration. -/
theorem globalCandidateABulkRegularMetricBySector_eq_configuration
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (sector : Sector) :
    (globalCandidateABulkRegularMetricBySector period hPeriod data sector).metric =
      globalGaugeFixedBulkMetricBySector period hPeriod configuration sector := by
  cases sector with
  | plus => exact data.plusMetric_eq
  | minus => exact data.minusMetric_eq

/-- The intrinsic potential reproduces the configuration's stored gauge
coefficients in the regular metric frame used by the action datum. -/
theorem globalCandidateABulkPotentialBySector_frame_coefficient
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (sector : Sector) (point : ProgramPBulkJetBase period hPeriod)
    (index : Index4) (component : Fin 2) :
    (globalCandidateABulkPotentialBySector period hPeriod data sector).toFun
        component point
        ((globalCandidateABulkRegularMetricBySector period hPeriod data sector).frame
          index point) =
      globalGaugeFixedBulkGaugeFieldBySector period hPeriod configuration sector
        point (index, component) := by
  cases sector with
  | plus => exact data.plusGauge_eq point index component
  | minus => exact data.minusGauge_eq point index component

/-! ## Christoffel transport to the structured-background carrier -/

/-- Continuous version of the local vector-valued Christoffel bilinear map.
Continuity is automatic because both coordinate spaces are finite
dimensional. -/
def localLeviCivitaChristoffelContinuousBilinear
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    Vector4 →L[Real] Vector4 →L[Real] Vector4 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun first =>
        LinearMap.toContinuousLinearMap
          ((localLeviCivitaChristoffelBilinearMap
            period hPeriod metric patch coordinate) first)
      map_add' := by
        intro first second
        apply ContinuousLinearMap.ext
        intro third
        change
          localLeviCivitaChristoffelBilinearMap period hPeriod metric patch
              coordinate (first + second) third = _
        simp
      map_smul' := by
        intro scalar first
        apply ContinuousLinearMap.ext
        intro second
        change
          localLeviCivitaChristoffelBilinearMap period hPeriod metric patch
              coordinate (scalar • first) second = _
        simp }

@[simp]
theorem localLeviCivitaChristoffelContinuousBilinear_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate first second : Vector4) :
    localLeviCivitaChristoffelContinuousBilinear
        period hPeriod metric patch coordinate first second =
      localLeviCivitaChristoffelApply
        period hPeriod metric patch coordinate first second :=
  rfl

theorem localLeviCivitaChristoffelContinuousBilinear_symmetric
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate first second : Vector4) :
    localLeviCivitaChristoffelContinuousBilinear
        period hPeriod metric patch coordinate first second =
      localLeviCivitaChristoffelContinuousBilinear
        period hPeriod metric patch coordinate second first :=
  localLeviCivitaChristoffelApply_symmetric
    period hPeriod metric patch coordinate first second

/-- Fixed identification used by the bulk background carrier. -/
def euclideanToHolonomicEquiv :
    EuclideanR4 ≃L[Real] Vector4 :=
  EuclideanSpace.equiv (Fin 4) Real

/-- Transport a continuous vector-valued bilinear map from holonomic
coordinates to the `EuclideanR4` background model. -/
def transportHolonomicTangentialQuadratic
    (quadratic : Vector4 →L[Real] Vector4 →L[Real] Vector4) :
    ContinuousTangentialQuadratic EuclideanR4 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun first =>
        euclideanToHolonomicEquiv.symm.toContinuousLinearMap.comp
          ((quadratic (euclideanToHolonomicEquiv first)).comp
            euclideanToHolonomicEquiv.toContinuousLinearMap)
      map_add' := by
        intro first second
        apply ContinuousLinearMap.ext
        intro third
        simp
      map_smul' := by
        intro scalar first
        apply ContinuousLinearMap.ext
        intro second
        simp }

@[simp]
theorem transportHolonomicTangentialQuadratic_apply
    (quadratic : Vector4 →L[Real] Vector4 →L[Real] Vector4)
    (first second : EuclideanR4) :
    euclideanToHolonomicEquiv
        (transportHolonomicTangentialQuadratic quadratic first second) =
      quadratic (euclideanToHolonomicEquiv first)
        (euclideanToHolonomicEquiv second) := by
  simp [transportHolonomicTangentialQuadratic]

/-- Actual Christoffel coefficients of one action sector in the supplied
holonomic chart. -/
def globalCandidateABulkChristoffel
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (sector : Sector) (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoverCoordinates) : Index4 → Index4 → Index4 → Real :=
  localLeviCivitaChristoffel period hPeriod
    (globalCandidateABulkRegularMetricBySector period hPeriod data sector).metric
    patch (coverToHolonomicEquiv coordinate)

/-- Actual sectorwise tangential connection quadratic, with the exact type of
`StructuredBackgroundSecondJet.tangentialQuadratic`. -/
def globalCandidateABulkTangentialQuadratic
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (sector : Sector) (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoverCoordinates) :
    ContinuousTangentialQuadratic EuclideanR4 :=
  transportHolonomicTangentialQuadratic
    (localLeviCivitaChristoffelContinuousBilinear period hPeriod
      (globalCandidateABulkRegularMetricBySector period hPeriod data sector).metric
      patch (coverToHolonomicEquiv coordinate))

theorem globalCandidateABulkTangentialQuadratic_symmetric
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (sector : Sector) (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoverCoordinates) (first second : EuclideanR4) :
    globalCandidateABulkTangentialQuadratic period hPeriod data sector patch
        coordinate first second =
      globalCandidateABulkTangentialQuadratic period hPeriod data sector patch
        coordinate second first := by
  apply euclideanToHolonomicEquiv.injective
  simp only [globalCandidateABulkTangentialQuadratic,
    transportHolonomicTangentialQuadratic_apply]
  exact localLeviCivitaChristoffelContinuousBilinear_symmetric
    period hPeriod
      (globalCandidateABulkRegularMetricBySector
        period hPeriod data sector).metric
      patch (coverToHolonomicEquiv coordinate)
      (euclideanToHolonomicEquiv first)
      (euclideanToHolonomicEquiv second)

/-! ## Actual paired Abelian covector jets -/

/-- Local gauge covector in an arbitrary linearly identified coordinate
model. -/
def globalCandidateABulkGaugeCovectorChartGerm
    {Domain : Type*} [NormedAddCommGroup Domain] [NormedSpace Real Domain]
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (sector : Sector) (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (transport : Domain ≃L[Real] Vector4) :
    Domain → FramedCovector Domain :=
  fun coordinate =>
    ∑ index : Index4,
      localGaugeCoefficient period hPeriod
          (globalCandidateABulkPotentialBySector period hPeriod data sector)
          component patch index (transport coordinate) •
        ((ContinuousLinearMap.proj index).comp
          transport.toContinuousLinearMap)

theorem globalCandidateABulkGaugeCovectorChartGerm_contDiff
    {Domain : Type*} [NormedAddCommGroup Domain] [NormedSpace Real Domain]
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (sector : Sector) (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (transport : Domain ≃L[Real] Vector4) :
    ContDiff Real ∞
      (globalCandidateABulkGaugeCovectorChartGerm period hPeriod data sector
        component patch transport) := by
  letI : IsBoundedSMul Real (FramedCovector Domain) :=
    { dist_smul_pair' := fun scalar left right => by
        simp only [dist_eq_norm]
        have hDifference :
            scalar • left - scalar • right =
              scalar • (left - right) := by
          exact (smul_sub scalar left right).symm
        rw [hDifference]
        simpa using
          ContinuousLinearMap.opNorm_smul_le scalar (left - right)
      dist_pair_smul' := fun left right covector => by
        simp only [dist_eq_norm]
        have hDifference :
            left • covector - right • covector =
              (left - right) • covector := by
          exact (sub_smul left right covector).symm
        rw [hDifference]
        simpa using
          ContinuousLinearMap.opNorm_smul_le (left - right) covector }
  apply ContDiff.sum
  intro index _
  exact
    ((localGaugeCoefficient_contDiff period hPeriod
        (globalCandidateABulkPotentialBySector period hPeriod data sector)
        component patch index).comp transport.contDiff).smul_const
      ((ContinuousLinearMap.proj index).comp
        transport.toContinuousLinearMap)

@[simp]
theorem globalCandidateABulkGaugeCovectorChartGerm_apply
    {Domain : Type*} [NormedAddCommGroup Domain] [NormedSpace Real Domain]
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (sector : Sector) (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (transport : Domain ≃L[Real] Vector4)
    (coordinate vector : Domain) :
    globalCandidateABulkGaugeCovectorChartGerm period hPeriod data sector
        component patch transport coordinate vector =
      (globalCandidateABulkPotentialBySector period hPeriod data sector).toFun
        component (patch.coordinateMap (transport coordinate))
        (((Pi.basisFun Real Index4).equiv
          (patch.frame (transport coordinate)) (Equiv.refl Index4))
            (transport vector)) := by
  have hFrame :
      ((Pi.basisFun Real Index4).equiv (patch.frame (transport coordinate))
        (Equiv.refl Index4)) (transport vector) =
        ∑ index : Index4,
          (transport vector) index • patch.frame (transport coordinate) index := by
    have hVector :
        transport vector = ∑ index : Index4,
          (transport vector) index • Pi.single index 1 := by
      ext index
      simp [Pi.single_apply]
    conv_lhs => rw [hVector]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro index _
    rw [map_smul]
    congr 1
    have hBasis :
        ((Pi.basisFun Real Index4).equiv
          (patch.frame (transport coordinate)) (Equiv.refl Index4))
            ((Pi.basisFun Real Index4) index) =
          patch.frame (transport coordinate) index := by
      exact Module.Basis.equiv_apply _ _ _ _
    simpa only [Pi.basisFun_apply] using hBasis
  rw [hFrame, map_sum]
  simp [globalCandidateABulkGaugeCovectorChartGerm,
    localGaugeCoefficient, mul_comm]

/-- The actual gauge covector germ in the split cover-coordinate model. -/
def globalCandidateABulkGaugeCoverChartGerm
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (sector : Sector) (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    CoverCoordinates → FramedCovector CoverCoordinates :=
  globalCandidateABulkGaugeCovectorChartGerm period hPeriod data sector
    component patch coverToHolonomicEquiv

/-- Actual second jet of one Abelian component in cover coordinates. -/
def globalCandidateABulkGaugeCoverSecondOrderJetAt
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (sector : Sector) (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoverCoordinates) :
    FramedSecondOrderJet CoverCoordinates (FramedCovector CoverCoordinates) :=
  chartwiseSecondOrderJetAt
    (globalCandidateABulkGaugeCoverChartGerm period hPeriod data sector
      component patch)
    coordinate
    ((globalCandidateABulkGaugeCovectorChartGerm_contDiff period hPeriod data
      sector component patch coverToHolonomicEquiv).contDiffAt.of_le (by
        show (2 : ℕ∞ω) ≤ ∞
        exact WithTop.coe_le_coe.mpr le_top))

@[simp]
theorem globalCandidateABulkGaugeCoverSecondOrderJetAt_value_apply
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (sector : Sector) (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate vector : CoverCoordinates) :
    (globalCandidateABulkGaugeCoverSecondOrderJetAt period hPeriod data sector
      component patch coordinate).value vector =
      (globalCandidateABulkPotentialBySector period hPeriod data sector).toFun
        component (patch.coordinateMap (coverToHolonomicEquiv coordinate))
        (((Pi.basisFun Real Index4).equiv
          (patch.frame (coverToHolonomicEquiv coordinate))
            (Equiv.refl Index4)) (coverToHolonomicEquiv vector)) := by
  rw [globalCandidateABulkGaugeCoverSecondOrderJetAt,
    chartwiseSecondOrderJetAt_value,
    globalCandidateABulkGaugeCoverChartGerm]
  exact globalCandidateABulkGaugeCovectorChartGerm_apply
    period hPeriod data sector component patch coverToHolonomicEquiv
      coordinate vector

/-- The same actual gauge germ in the `EuclideanR4` model used by the
structured-background field of the bulk carrier. -/
def globalCandidateABulkGaugeEuclideanChartGerm
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (sector : Sector) (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    EuclideanR4 → FramedCovector EuclideanR4 :=
  globalCandidateABulkGaugeCovectorChartGerm period hPeriod data sector
    component patch euclideanToHolonomicEquiv

/-- Actual Euclidean-background second jet corresponding to a selected cover
coordinate. -/
def globalCandidateABulkGaugeEuclideanSecondOrderJetAt
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (sector : Sector) (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoverCoordinates) :
    FramedSecondOrderJet EuclideanR4 (FramedCovector EuclideanR4) :=
  chartwiseSecondOrderJetAt
    (globalCandidateABulkGaugeEuclideanChartGerm period hPeriod data sector
      component patch)
    (euclideanToHolonomicEquiv.symm (coverToHolonomicEquiv coordinate))
    ((globalCandidateABulkGaugeCovectorChartGerm_contDiff period hPeriod data
      sector component patch euclideanToHolonomicEquiv).contDiffAt.of_le (by
        show (2 : ℕ∞ω) ≤ ∞
        exact WithTop.coe_le_coe.mpr le_top))

theorem globalCandidateABulkGaugeEuclideanSecondOrderJetAt_secondDerivative_symmetric
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (sector : Sector) (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoverCoordinates) (first second : EuclideanR4) :
    (globalCandidateABulkGaugeEuclideanSecondOrderJetAt period hPeriod data
      sector component patch coordinate).secondDerivative first second =
      (globalCandidateABulkGaugeEuclideanSecondOrderJetAt period hPeriod data
        sector component patch coordinate).secondDerivative second first :=
  (globalCandidateABulkGaugeEuclideanSecondOrderJetAt period hPeriod data
    sector component patch coordinate).secondDerivative_symmetric first second

/-! ## Exact partial carrier package -/

/-- The part of `StructuredBackgroundSecondJet EuclideanR4` which is already
realized by the actual bulk action data.  The two omitted fields are precisely
`normalQuadratic` and `physicalNormal`. -/
structure ActualBulkStructuredBackgroundSecondJetCore
    (_configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) where
  point : ProgramPBulkJetBase period hPeriod
  christoffel : Sector → Index4 → Index4 → Index4 → Real
  tangentialQuadratic :
    Sector → ContinuousTangentialQuadratic EuclideanR4
  gaugeConnection :
    Sector → Fin 2 →
      FramedSecondOrderJet EuclideanR4 (FramedCovector EuclideanR4)
  tangentialQuadratic_symmetric : ∀ sector first second,
    tangentialQuadratic sector first second =
      tangentialQuadratic sector second first

/-- Simultaneous extraction of the realized bulk-background core. -/
def globalCandidateAActualBulkStructuredBackgroundSecondJetCore
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoverCoordinates) :
    ActualBulkStructuredBackgroundSecondJetCore
      period hPeriod configuration where
  point := patch.coordinateMap (coverToHolonomicEquiv coordinate)
  christoffel := fun sector =>
    globalCandidateABulkChristoffel period hPeriod data sector patch coordinate
  tangentialQuadratic := fun sector =>
    globalCandidateABulkTangentialQuadratic
      period hPeriod data sector patch coordinate
  gaugeConnection := fun sector component =>
    globalCandidateABulkGaugeEuclideanSecondOrderJetAt
      period hPeriod data sector component patch coordinate
  tangentialQuadratic_symmetric := fun sector first second =>
    globalCandidateABulkTangentialQuadratic_symmetric
      period hPeriod data sector patch coordinate first second

@[simp]
theorem globalCandidateAActualBulkStructuredBackgroundSecondJetCore_point
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoverCoordinates) :
    (globalCandidateAActualBulkStructuredBackgroundSecondJetCore period hPeriod
      configuration data patch coordinate).point =
      patch.coordinateMap (coverToHolonomicEquiv coordinate) :=
  rfl

@[simp]
theorem globalCandidateAActualBulkStructuredBackgroundSecondJetCore_gaugeConnection
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoverCoordinates) (sector : Sector) (component : Fin 2) :
    (globalCandidateAActualBulkStructuredBackgroundSecondJetCore period hPeriod
      configuration data patch coordinate).gaugeConnection sector component =
      globalCandidateABulkGaugeEuclideanSecondOrderJetAt period hPeriod data
        sector component patch coordinate :=
  rfl

end
end P0EFTJanusProgramPActualBulkBackgroundChartwiseSecondOrderJetExtraction4D
end JanusFormal
