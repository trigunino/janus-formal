import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionGlobalLiftLocalRegularity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeometricNormalJunction4D

/-!
# Canonical orthogonal differential-normal splitting on the D8 throat

The canonical global orthogonal lift is a fiberwise-linear right inverse of
the differential-normal quotient.  This gate installs it in the geometric
junction interface, specializes the twisted normal flux and the Robin bridge,
and records the unconditional continuity of its intrinsic metric square.

The imported local-regularity theorem controls the quadratic metric value; it
does not by itself prove that the dependent lift is a smooth bundle morphism.
The exact operational remainder needed below is therefore isolated as
`CanonicalSmoothOrthogonalNormalSplittingContract`: smoothness of the scalar
flux paired with every genuine smooth twisted-normal test.

No global nonzero unit normal is constructed.  Such a scalar trivialization
would contradict the one-sided normal line; unit normalization must remain a
twisted/local datum on the non-null locus.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalSmoothOrthogonalNormalSplitting4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Topology
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusGlobalNormalEquivalence
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusGlobalHolonomicScalar4D
open P0EFTJanusMappingTorusScalarRobinJunctionBalance4D
open P0EFTJanusMappingTorusGeometricNormalJunction4D
open P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionGlobalLiftChoice4D
open P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionGlobalLiftContinuity4D
open P0EFTJanusMappingTorusIntrinsicCanonicalNormalProjectionGlobalLiftLocalRegularity4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance effectiveThroatCompactSpace :
    CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance effectiveThroatMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance effectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

local instance normalCoreIsContMDiff :
    (fixedThroatNormalVectorBundleCore period hPeriod).IsContMDiff
      throatCoverModelWithCorners ω :=
  fixedThroatNormalVectorBundleCore_isContMDiff period hPeriod

private abbrev AmbientTangent
    (point : EffectiveThroat period hPeriod) :=
  TangentSpace coverModelWithCorners
    (fixedThroatQuotientInclusion period hPeriod point)

private abbrev TangentialRange
    (point : EffectiveThroat period hPeriod) :
    Submodule Real (AmbientTangent period hPeriod point) :=
  LinearMap.range
    (mfderiv throatCoverModelWithCorners coverModelWithCorners
      (fixedThroatQuotientInclusion period hPeriod) point).toLinearMap

/-- Opaque field used by the dependent splitting record. -/
private def canonicalOrthogonalRepresentative
    (point : EffectiveThroat period hPeriod) :
    DifferentialNormalFiber period hPeriod point →ₗ[Real]
      AmbientTangent period hPeriod point :=
  canonicalGlobalOrthogonalNormalLift period hPeriod point

/-- Opaque right-inverse proof used by the dependent splitting record. -/
private theorem canonicalOrthogonalRepresentative_rightInverse
    (point : EffectiveThroat period hPeriod)
    (normal : DifferentialNormalFiber period hPeriod point) :
    (TangentialRange period hPeriod point).mkQ
        (canonicalOrthogonalRepresentative period hPeriod point normal) =
      normal := by
  change (TangentialRange period hPeriod point).mkQ
      (canonicalGlobalOrthogonalNormalLift period hPeriod point normal) = normal
  exact canonicalGlobalOrthogonalNormalLift_represents
    period hPeriod point normal

/-- Opaque orthogonality proof for the selected representative field. -/
private theorem canonicalOrthogonalRepresentative_orthogonal
    (point : EffectiveThroat period hPeriod)
    (normal : DifferentialNormalFiber period hPeriod point)
    (tangent : TangentSpace throatCoverModelWithCorners point) :
    (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor
        (fixedThroatQuotientInclusion period hPeriod point)
        (canonicalOrthogonalRepresentative period hPeriod point normal)
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatQuotientInclusion period hPeriod) point tangent) = 0 := by
  change
    (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor
        (fixedThroatQuotientInclusion period hPeriod point)
        (canonicalGlobalOrthogonalNormalLift period hPeriod point normal)
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatQuotientInclusion period hPeriod) point tangent) = 0
  exact canonicalGlobalOrthogonalNormalLift_orthogonal
    period hPeriod point normal tangent

/-- Opaque continuity proof for the quadratic value of the representative. -/
private theorem canonicalOrthogonalRepresentative_continuous_metric_square :
    Continuous
      (fun normal : DifferentialNormalTotalSpace period hPeriod =>
        (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor
          (fixedThroatQuotientInclusion period hPeriod normal.1)
          (canonicalOrthogonalRepresentative
            period hPeriod normal.1 normal.2)
          (canonicalOrthogonalRepresentative
            period hPeriod normal.1 normal.2)) := by
  change Continuous
    (fun normal : DifferentialNormalTotalSpace period hPeriod =>
      (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor
        (fixedThroatQuotientInclusion period hPeriod normal.1)
        (canonicalGlobalOrthogonalNormalLift period hPeriod normal.1 normal.2)
        (canonicalGlobalOrthogonalNormalLift period hPeriod normal.1 normal.2))
  exact canonicalGlobalOrthogonalNormalLift_continuous_metric_square
    period hPeriod
      (canonicalGlobalNormalMetricSquareLocalRegularity period hPeriod)

/-- The canonical orthogonal lift installed as the differential-normal
splitting used by the geometric junction gate. -/
def canonicalOrthogonalDifferentialNormalSplitting :
    DifferentialNormalSplitting period hPeriod where
  representative := canonicalOrthogonalRepresentative period hPeriod
  rightInverse := canonicalOrthogonalRepresentative_rightInverse period hPeriod

@[simp] theorem canonicalOrthogonalDifferentialNormalSplitting_representative
    (point : EffectiveThroat period hPeriod)
    (normal : DifferentialNormalFiber period hPeriod point) :
    (canonicalOrthogonalDifferentialNormalSplitting period hPeriod).representative
        point normal =
      canonicalGlobalOrthogonalNormalLift period hPeriod point normal :=
  by
    change canonicalOrthogonalRepresentative period hPeriod point normal =
      canonicalGlobalOrthogonalNormalLift period hPeriod point normal
    rfl

/-- The installed representative is orthogonal to the actual embedded throat
tangent range. -/
theorem canonicalOrthogonalDifferentialNormalSplitting_orthogonal
    (point : EffectiveThroat period hPeriod)
    (normal : DifferentialNormalFiber period hPeriod point)
    (tangent : TangentSpace throatCoverModelWithCorners point) :
    (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor
        (fixedThroatQuotientInclusion period hPeriod point)
        ((canonicalOrthogonalDifferentialNormalSplitting
          period hPeriod).representative point normal)
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatQuotientInclusion period hPeriod) point tangent) = 0 := by
  change
    (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor
        (fixedThroatQuotientInclusion period hPeriod point)
        (canonicalOrthogonalRepresentative period hPeriod point normal)
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatQuotientInclusion period hPeriod) point tangent) = 0
  exact canonicalOrthogonalRepresentative_orthogonal
    period hPeriod point normal tangent

/-- The strongest unconditional base-regularity result currently available:
the intrinsic metric square of the canonical representative is continuous on
the full differential-normal total space. -/
theorem canonicalOrthogonalDifferentialNormalSplitting_continuous_metric_square :
    Continuous
      (fun normal : DifferentialNormalTotalSpace period hPeriod =>
        (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor
          (fixedThroatQuotientInclusion period hPeriod normal.1)
          ((canonicalOrthogonalDifferentialNormalSplitting
            period hPeriod).representative normal.1 normal.2)
          ((canonicalOrthogonalDifferentialNormalSplitting
            period hPeriod).representative normal.1 normal.2)) := by
  change Continuous
    (fun normal : DifferentialNormalTotalSpace period hPeriod =>
      (intrinsicSmoothGeneralLorentzMetric period hPeriod).tensor.tensor
        (fixedThroatQuotientInclusion period hPeriod normal.1)
        (canonicalOrthogonalRepresentative period hPeriod normal.1 normal.2)
        (canonicalOrthogonalRepresentative period hPeriod normal.1 normal.2))
  exact canonicalOrthogonalRepresentative_continuous_metric_square
    period hPeriod

/-- Canonical twisted scalar flux selected by the orthogonal splitting. -/
def canonicalGeometricNormalFlux
    (field : SmoothQuotientField period hPeriod Real)
    (point : EffectiveThroat period hPeriod) :
    FixedThroatNormalFiber period hPeriod point →ₗ[Real] Real :=
  geometricNormalFlux period hPeriod
    (canonicalOrthogonalDifferentialNormalSplitting period hPeriod) field point

@[simp] theorem canonicalGeometricNormalFlux_apply
    (field : SmoothQuotientField period hPeriod Real)
    (point : EffectiveThroat period hPeriod)
    (normal : FixedThroatNormalFiber period hPeriod point) :
    canonicalGeometricNormalFlux period hPeriod field point normal =
      scalarDifferential period hPeriod field
        (fixedThroatQuotientInclusion period hPeriod point)
        (canonicalGlobalOrthogonalNormalLift period hPeriod point
          (differentialNormalFiberEquiv period hPeriod point normal)) :=
  rfl

/-- The vector used by the canonical flux represents exactly the supplied
twisted differential-normal class. -/
theorem canonicalGeometricNormalLift_has_expected_class
    (point : EffectiveThroat period hPeriod)
    (normal : FixedThroatNormalFiber period hPeriod point) :
    (LinearMap.range
      (mfderiv throatCoverModelWithCorners coverModelWithCorners
        (fixedThroatQuotientInclusion period hPeriod) point).toLinearMap).mkQ
        (canonicalGlobalOrthogonalNormalLift period hPeriod point
          (differentialNormalFiberEquiv period hPeriod point normal)) =
      differentialNormalFiberEquiv period hPeriod point normal :=
  canonicalGlobalOrthogonalNormalLift_represents period hPeriod point _

/-- The canonical flux has the required sign-clutched one-loop law. -/
theorem canonicalGeometricNormalFlux_oneLoop
    (field : SmoothQuotientField period hPeriod Real)
    (anchor : MappingTorusCover (fixedEquatorData period hPeriod))
    (normal : Real) :
    let base := mappingTorusMk (fixedEquatorData period hPeriod) anchor
    canonicalGeometricNormalFlux period hPeriod field base
        ((fixedThroatNormalVectorBundleCore period hPeriod).coordChange
          anchor ((1 : Int) +ᵥ anchor) base normal) =
      -canonicalGeometricNormalFlux period hPeriod field base normal := by
  exact geometricNormalFlux_oneLoop period hPeriod
    (canonicalOrthogonalDifferentialNormalSplitting period hPeriod)
      field anchor normal

/-- Canonical sum of the two twisted normal fluxes. -/
def canonicalGeometricJunctionResidual
    (firstField secondField : SmoothQuotientField period hPeriod Real)
    (point : EffectiveThroat period hPeriod) :
    FixedThroatNormalFiber period hPeriod point →ₗ[Real] Real :=
  canonicalGeometricNormalFlux period hPeriod firstField point +
    canonicalGeometricNormalFlux period hPeriod secondField point

/-- The canonical two-sector residual inherits the sign-clutched one-loop
law. -/
theorem canonicalGeometricJunctionResidual_oneLoop
    (firstField secondField : SmoothQuotientField period hPeriod Real)
    (anchor : MappingTorusCover (fixedEquatorData period hPeriod))
    (normal : Real) :
    let base := mappingTorusMk (fixedEquatorData period hPeriod) anchor
    canonicalGeometricJunctionResidual period hPeriod firstField secondField base
        ((fixedThroatNormalVectorBundleCore period hPeriod).coordChange
          anchor ((1 : Int) +ᵥ anchor) base normal) =
      -canonicalGeometricJunctionResidual period hPeriod
        firstField secondField base normal := by
  exact geometricJunctionResidual_oneLoop period hPeriod
    (canonicalOrthogonalDifferentialNormalSplitting period hPeriod)
      firstField secondField anchor normal

/-- Pairing the canonical twisted residual with a genuine twisted test gives
a globally defined scalar. -/
def canonicalDescendedFluxPairing
    (firstField secondField : SmoothQuotientField period hPeriod Real)
    (test : SmoothNormalTest period hPeriod)
    (point : EffectiveThroat period hPeriod) : Real :=
  canonicalGeometricJunctionResidual period hPeriod firstField secondField point
    (test point)

/-- Exact residual smoothness interface.  It asks only for the operational
regularity used by the junction functional; no global normal frame or scalar
orientation is hidden in the contract. -/
structure CanonicalSmoothOrthogonalNormalSplittingContract : Prop where
  pairedFlux_contMDiff : ∀
      (field : SmoothQuotientField period hPeriod Real)
      (test : SmoothNormalTest period hPeriod),
    ContMDiff throatCoverModelWithCorners 𝓘(Real, Real) ω
      (fun point : EffectiveThroat period hPeriod =>
        canonicalGeometricNormalFlux period hPeriod field point (test point))

/-- Under the exact residual contract, the paired two-sector junction
residual is a smooth scalar on the throat. -/
theorem canonicalDescendedFluxPairing_contMDiff
    (regularity : CanonicalSmoothOrthogonalNormalSplittingContract
      period hPeriod)
    (firstField secondField : SmoothQuotientField period hPeriod Real)
    (test : SmoothNormalTest period hPeriod) :
    ContMDiff throatCoverModelWithCorners 𝓘(Real, Real) ω
      (canonicalDescendedFluxPairing period hPeriod
        firstField secondField test) := by
  change ContMDiff throatCoverModelWithCorners 𝓘(Real, Real) ω
    (fun point : EffectiveThroat period hPeriod =>
      canonicalGeometricNormalFlux period hPeriod firstField point
          (test point) +
        canonicalGeometricNormalFlux period hPeriod secondField point
          (test point))
  exact (regularity.pairedFlux_contMDiff firstField test).add
    (regularity.pairedFlux_contMDiff secondField test)

/-- Smooth paired canonical fluxes are integrable against every finite Borel
measure on the compact throat. -/
theorem canonicalDescendedFluxPairing_integrable
    (regularity : CanonicalSmoothOrthogonalNormalSplittingContract
      period hPeriod)
    (firstField secondField : SmoothQuotientField period hPeriod Real)
    (test : SmoothNormalTest period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    Integrable
      (canonicalDescendedFluxPairing period hPeriod
        firstField secondField test) mu :=
  (canonicalDescendedFluxPairing_contMDiff period hPeriod regularity
      firstField secondField test).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Canonical weak integrated balance. -/
def canonicalWeakGeometricNormalBalance
    (firstField secondField : SmoothQuotientField period hPeriod Real)
    (test : SmoothNormalTest period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) : Real :=
  weakGeometricNormalBalance period hPeriod
    (canonicalOrthogonalDifferentialNormalSplitting period hPeriod)
      firstField secondField test mu

/-- Canonical junction action, still paired with a twisted normal section. -/
def canonicalGeometricJunctionAction
    (firstField secondField : SmoothQuotientField period hPeriod Real)
    (junction : SmoothNormalTest period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) : Real :=
  geometricJunctionAction period hPeriod
    (canonicalOrthogonalDifferentialNormalSplitting period hPeriod)
      firstField secondField junction mu

/-- Stationarity specialized to the canonical orthogonal splitting. -/
def CanonicalGeometricJunctionStationary
    (firstField secondField : SmoothQuotientField period hPeriod Real)
    (junction : SmoothNormalTest period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) : Prop :=
  GeometricJunctionStationary period hPeriod
    (canonicalOrthogonalDifferentialNormalSplitting period hPeriod)
      firstField secondField junction mu

/-- Canonical geometric stationarity implies the weak twisted normal balance. -/
theorem canonicalStationary_weak_geometric_normal_balance
    (firstField secondField : SmoothQuotientField period hPeriod Real)
    (junction test : SmoothNormalTest period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod))
    (hJunction : Integrable
      (canonicalDescendedFluxPairing period hPeriod
        firstField secondField junction) mu)
    (hTest : Integrable
      (canonicalDescendedFluxPairing period hPeriod
        firstField secondField test) mu)
    (hStationary : CanonicalGeometricJunctionStationary period hPeriod
      firstField secondField junction mu) :
    canonicalWeakGeometricNormalBalance period hPeriod
      firstField secondField test mu = 0 := by
  exact stationary_weak_geometric_normal_balance period hPeriod
    (canonicalOrthogonalDifferentialNormalSplitting period hPeriod)
      firstField secondField junction test mu hJunction hTest hStationary

/-- The residual smoothness contract discharges both integrability hypotheses
in the canonical stationarity-to-balance theorem. -/
theorem canonicalStationary_weak_geometric_normal_balance_of_smoothness
    (regularity : CanonicalSmoothOrthogonalNormalSplittingContract
      period hPeriod)
    (firstField secondField : SmoothQuotientField period hPeriod Real)
    (junction test : SmoothNormalTest period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu]
    (hStationary : CanonicalGeometricJunctionStationary period hPeriod
      firstField secondField junction mu) :
    canonicalWeakGeometricNormalBalance period hPeriod
      firstField secondField test mu = 0 := by
  exact canonicalStationary_weak_geometric_normal_balance period hPeriod
    firstField secondField junction test mu
      (canonicalDescendedFluxPairing_integrable period hPeriod regularity
        firstField secondField junction mu)
      (canonicalDescendedFluxPairing_integrable period hPeriod regularity
        firstField secondField test mu)
      hStationary

/-- Robin constitutive law specialized to the canonical orthogonal lift. -/
def CanonicalGeometricRobinNormalLaw
    (coefficient : Real)
    (bulk : SmoothQuotientField period hPeriod Real)
    (junction : SmoothThroatField period hPeriod Real)
    (referenceNormal : SmoothNormalTest period hPeriod) : Prop :=
  GeometricRobinNormalLaw period hPeriod
    (canonicalOrthogonalDifferentialNormalSplitting period hPeriod)
      coefficient bulk junction referenceNormal

private theorem canonicalWeakGeometricNormalBalance_eq_robin_proof
    (kFirst kSecond : Real)
    (firstField secondField : SmoothQuotientField period hPeriod Real)
    (junction scalarTest : SmoothThroatField period hPeriod Real)
    (referenceNormal : SmoothNormalTest period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod))
    (hFirst : CanonicalGeometricRobinNormalLaw period hPeriod kFirst
      firstField junction referenceNormal)
    (hSecond : CanonicalGeometricRobinNormalLaw period hPeriod kSecond
      secondField junction referenceNormal) :
    canonicalWeakGeometricNormalBalance period hPeriod firstField secondField
        (scalarTimesNormalTest period hPeriod scalarTest referenceNormal) mu =
      robinFirstVariation period hPeriod kFirst kSecond firstField secondField
        junction scalarTest mu := by
  exact weakGeometricNormalBalance_eq_robinFirstVariation period hPeriod
    (canonicalOrthogonalDifferentialNormalSplitting period hPeriod)
      kFirst kSecond firstField secondField junction scalarTest referenceNormal
      mu hFirst hSecond

/-- The canonical geometric balance restricts exactly to the compiled Robin
first variation under the explicit constitutive laws. -/
theorem canonicalWeakGeometricNormalBalance_eq_robinFirstVariation
    (kFirst kSecond : Real)
    (firstField secondField : SmoothQuotientField period hPeriod Real)
    (junction scalarTest : SmoothThroatField period hPeriod Real)
    (referenceNormal : SmoothNormalTest period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod))
    (hFirst : CanonicalGeometricRobinNormalLaw period hPeriod kFirst
      firstField junction referenceNormal)
    (hSecond : CanonicalGeometricRobinNormalLaw period hPeriod kSecond
      secondField junction referenceNormal) :
    canonicalWeakGeometricNormalBalance period hPeriod firstField secondField
        (scalarTimesNormalTest period hPeriod scalarTest referenceNormal) mu =
      robinFirstVariation period hPeriod kFirst kSecond firstField secondField
        junction scalarTest mu := by
  exact canonicalWeakGeometricNormalBalance_eq_robin_proof period hPeriod
    kFirst kSecond firstField secondField junction scalarTest referenceNormal
      mu hFirst hSecond

private theorem canonicalStationary_weak_robin_balance_proof
    (kFirst kSecond : Real)
    (firstField secondField : SmoothQuotientField period hPeriod Real)
    (junctionNormal : SmoothNormalTest period hPeriod)
    (junction scalarTest : SmoothThroatField period hPeriod Real)
    (referenceNormal : SmoothNormalTest period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod))
    (hJunction : Integrable
      (canonicalDescendedFluxPairing period hPeriod
        firstField secondField junctionNormal) mu)
    (hTest : Integrable
      (canonicalDescendedFluxPairing period hPeriod firstField secondField
        (scalarTimesNormalTest period hPeriod scalarTest referenceNormal)) mu)
    (hStationary : CanonicalGeometricJunctionStationary period hPeriod
      firstField secondField junctionNormal mu)
    (hFirst : CanonicalGeometricRobinNormalLaw period hPeriod kFirst
      firstField junction referenceNormal)
    (hSecond : CanonicalGeometricRobinNormalLaw period hPeriod kSecond
      secondField junction referenceNormal) :
    robinFirstVariation period hPeriod kFirst kSecond firstField secondField
      junction scalarTest mu = 0 := by
  exact stationary_weak_robin_balance_of_geometricNormalLaw period hPeriod
    (canonicalOrthogonalDifferentialNormalSplitting period hPeriod)
      kFirst kSecond firstField secondField junctionNormal junction scalarTest
      referenceNormal mu hJunction hTest hStationary hFirst hSecond

/-- Canonical geometric stationarity implies the compiled weak Robin balance
for every admissible scalar-times-twisted-normal test. -/
theorem canonicalStationary_weak_robin_balance
    (kFirst kSecond : Real)
    (firstField secondField : SmoothQuotientField period hPeriod Real)
    (junctionNormal : SmoothNormalTest period hPeriod)
    (junction scalarTest : SmoothThroatField period hPeriod Real)
    (referenceNormal : SmoothNormalTest period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod))
    (hJunction : Integrable
      (canonicalDescendedFluxPairing period hPeriod
        firstField secondField junctionNormal) mu)
    (hTest : Integrable
      (canonicalDescendedFluxPairing period hPeriod firstField secondField
        (scalarTimesNormalTest period hPeriod scalarTest referenceNormal)) mu)
    (hStationary : CanonicalGeometricJunctionStationary period hPeriod
      firstField secondField junctionNormal mu)
    (hFirst : CanonicalGeometricRobinNormalLaw period hPeriod kFirst
      firstField junction referenceNormal)
    (hSecond : CanonicalGeometricRobinNormalLaw period hPeriod kSecond
      secondField junction referenceNormal) :
    robinFirstVariation period hPeriod kFirst kSecond firstField secondField
      junction scalarTest mu = 0 := by
  exact canonicalStationary_weak_robin_balance_proof period hPeriod
    kFirst kSecond firstField secondField junctionNormal junction scalarTest
      referenceNormal mu hJunction hTest hStationary hFirst hSecond

/-- With the exact smooth-pairing contract, canonical stationarity and the two
constitutive laws imply the Robin balance without separate integrability
inputs. -/
theorem canonicalStationary_weak_robin_balance_of_smoothness
    (regularity : CanonicalSmoothOrthogonalNormalSplittingContract
      period hPeriod)
    (kFirst kSecond : Real)
    (firstField secondField : SmoothQuotientField period hPeriod Real)
    (junctionNormal : SmoothNormalTest period hPeriod)
    (junction scalarTest : SmoothThroatField period hPeriod Real)
    (referenceNormal : SmoothNormalTest period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu]
    (hStationary : CanonicalGeometricJunctionStationary period hPeriod
      firstField secondField junctionNormal mu)
    (hFirst : CanonicalGeometricRobinNormalLaw period hPeriod kFirst
      firstField junction referenceNormal)
    (hSecond : CanonicalGeometricRobinNormalLaw period hPeriod kSecond
      secondField junction referenceNormal) :
    robinFirstVariation period hPeriod kFirst kSecond firstField secondField
      junction scalarTest mu = 0 := by
  exact canonicalStationary_weak_robin_balance period hPeriod
    kFirst kSecond firstField secondField junctionNormal junction scalarTest
      referenceNormal mu
      (canonicalDescendedFluxPairing_integrable period hPeriod regularity
        firstField secondField junctionNormal mu)
      (canonicalDescendedFluxPairing_integrable period hPeriod regularity
        firstField secondField
          (scalarTimesNormalTest period hPeriod scalarTest referenceNormal) mu)
      hStationary hFirst hSecond

end

end P0EFTJanusMappingTorusCanonicalSmoothOrthogonalNormalSplitting4D
end JanusFormal
