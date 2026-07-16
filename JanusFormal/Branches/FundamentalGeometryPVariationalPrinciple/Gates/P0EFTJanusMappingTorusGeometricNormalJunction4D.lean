import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusGlobalNormalEquivalence
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalHolonomicScalar4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarRobinJunctionBalance4D

/-!
# Geometric scalar normal flux on the D8 throat

The flux in this gate is the actual ambient differential `d phi` evaluated on
a representative of the differential normal class of the genuine D8 throat
embedding.  A pointwise linear splitting of that quotient is constructed, but
no continuity or smoothness of the family is claimed.

The normal line is one-sided.  Thus the normal flux is a covector in the dual
sign-clutched line, not a global scalar.  Its pairing with a smooth section of
the same sign-clutched normal line is a descended scalar on the quotient.  The
integral of that pairing defines the junction action, whose first variation
gives the weak normal-flux balance.

This does not construct a metric unit normal, a smooth differential-normal
bundle equivalence, extrinsic curvature, an Israel condition, or a null
junction.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGeometricNormalJunction4D

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

local instance effectiveThroatMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance effectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

local instance normalCoreIsContMDiff :
    (fixedThroatNormalVectorBundleCore period hPeriod).IsContMDiff
      throatCoverModelWithCorners ω :=
  fixedThroatNormalVectorBundleCore_isContMDiff period hPeriod

/-- Smooth tests in the genuine sign-clutched D8 normal line. -/
abbrev SmoothNormalTest :=
  ContMDiffSection throatCoverModelWithCorners Real ω
    (FixedThroatNormalFiber period hPeriod)

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

/-- A right inverse of the quotient map defining the differential normal
fiber.  This is the exact extra datum needed to evaluate an ambient covector
on a normal class when no metric unit normal has been constructed. -/
structure DifferentialNormalSplitting where
  representative : forall point : EffectiveThroat period hPeriod,
    DifferentialNormalFiber period hPeriod point →ₗ[Real]
      AmbientTangent period hPeriod point
  rightInverse : forall (point : EffectiveThroat period hPeriod)
      (normal : DifferentialNormalFiber period hPeriod point),
    (TangentialRange period hPeriod point).mkQ
        (representative point normal) = normal

/-- An algebraic complement of the tangent range at one throat point. -/
def algebraicNormalComplement
    (point : EffectiveThroat period hPeriod) :
    Submodule Real (AmbientTangent period hPeriod point) :=
  Classical.choose (TangentialRange period hPeriod point).exists_isCompl

theorem tangentialRange_isCompl_algebraicNormalComplement
    (point : EffectiveThroat period hPeriod) :
    IsCompl (TangentialRange period hPeriod point)
      (algebraicNormalComplement period hPeriod point) :=
  Classical.choose_spec (TangentialRange period hPeriod point).exists_isCompl

/-- Fiberwise linear representative selected by the algebraic complement. -/
def algebraicNormalRepresentative
    (point : EffectiveThroat period hPeriod) :
    DifferentialNormalFiber period hPeriod point →ₗ[Real]
      AmbientTangent period hPeriod point :=
  (algebraicNormalComplement period hPeriod point).subtype.comp
    (((TangentialRange period hPeriod point).quotientEquivOfIsCompl
      (algebraicNormalComplement period hPeriod point)
      (tangentialRange_isCompl_algebraicNormalComplement period hPeriod point)).toLinearMap)

theorem algebraicNormalRepresentative_rightInverse
    (point : EffectiveThroat period hPeriod)
    (normal : DifferentialNormalFiber period hPeriod point) :
    (TangentialRange period hPeriod point).mkQ
        (algebraicNormalRepresentative period hPeriod point normal) = normal := by
  change
    (Submodule.Quotient.mk
      (((TangentialRange period hPeriod point).quotientEquivOfIsCompl
        (algebraicNormalComplement period hPeriod point)
        (tangentialRange_isCompl_algebraicNormalComplement period hPeriod point))
          normal).1 :
      DifferentialNormalFiber period hPeriod point) = normal
  exact Submodule.mk_quotientEquivOfIsCompl_apply
    (tangentialRange_isCompl_algebraicNormalComplement period hPeriod point)
    normal

/-- The available global splitting is algebraic and pointwise.  No regularity
of its dependence on the base point is asserted. -/
def algebraicDifferentialNormalSplitting :
    DifferentialNormalSplitting period hPeriod where
  representative := algebraicNormalRepresentative period hPeriod
  rightInverse := algebraicNormalRepresentative_rightInverse period hPeriod

/-- Lift a sign-clutched normal vector through the actual differential normal
quotient and then evaluate the genuine differential of the same scalar. -/
def geometricNormalFlux
    (splitting : DifferentialNormalSplitting period hPeriod)
    (field : SmoothQuotientField period hPeriod Real)
    (point : EffectiveThroat period hPeriod) :
    FixedThroatNormalFiber period hPeriod point →ₗ[Real] Real :=
  (scalarDifferential period hPeriod field
      (fixedThroatQuotientInclusion period hPeriod point)).toLinearMap.comp
    ((splitting.representative point).comp
      (differentialNormalFiberEquiv period hPeriod point).toLinearMap)

theorem geometricNormalFlux_apply
    (splitting : DifferentialNormalSplitting period hPeriod)
    (field : SmoothQuotientField period hPeriod Real)
    (point : EffectiveThroat period hPeriod)
    (normal : FixedThroatNormalFiber period hPeriod point) :
    geometricNormalFlux period hPeriod splitting field point normal =
      scalarDifferential period hPeriod field
        (fixedThroatQuotientInclusion period hPeriod point)
        (splitting.representative point
          (differentialNormalFiberEquiv period hPeriod point normal)) :=
  rfl

/-- The lifted vector represents exactly the differential normal class carried
by the sign-clutched normal fiber. -/
theorem geometricNormalLift_has_expected_class
    (splitting : DifferentialNormalSplitting period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (normal : FixedThroatNormalFiber period hPeriod point) :
    (TangentialRange period hPeriod point).mkQ
        (splitting.representative point
          (differentialNormalFiberEquiv period hPeriod point normal)) =
      differentialNormalFiberEquiv period hPeriod point normal :=
  splitting.rightInverse point _

/-- A one-loop chart transition negates the local scalar flux coordinate.
This is the precise twisted behavior forced by one-sidedness. -/
theorem geometricNormalFlux_oneLoop
    (splitting : DifferentialNormalSplitting period hPeriod)
    (field : SmoothQuotientField period hPeriod Real)
    (anchor : MappingTorusCover (fixedEquatorData period hPeriod))
    (normal : Real) :
    let base := mappingTorusMk (fixedEquatorData period hPeriod) anchor
    geometricNormalFlux period hPeriod splitting field base
        ((fixedThroatNormalVectorBundleCore period hPeriod).coordChange
          anchor ((1 : Int) +ᵥ anchor) base normal) =
      -geometricNormalFlux period hPeriod splitting field base normal := by
  dsimp only
  rw [geometricNormalFlux_apply, geometricNormalFlux_apply,
    differentialNormalFiberEquiv_oneLoop]
  rw [map_neg, map_neg]

/-- Sum of two one-sided scalar fluxes.  It remains a normal covector; it is
not incorrectly trivialized to a scalar. -/
def geometricJunctionResidual
    (splitting : DifferentialNormalSplitting period hPeriod)
    (firstField secondField : SmoothQuotientField period hPeriod Real)
    (point : EffectiveThroat period hPeriod) :
    FixedThroatNormalFiber period hPeriod point →ₗ[Real] Real :=
  geometricNormalFlux period hPeriod splitting firstField point +
    geometricNormalFlux period hPeriod splitting secondField point

theorem geometricJunctionResidual_oneLoop
    (splitting : DifferentialNormalSplitting period hPeriod)
    (firstField secondField : SmoothQuotientField period hPeriod Real)
    (anchor : MappingTorusCover (fixedEquatorData period hPeriod))
    (normal : Real) :
    let base := mappingTorusMk (fixedEquatorData period hPeriod) anchor
    geometricJunctionResidual period hPeriod splitting firstField secondField base
        ((fixedThroatNormalVectorBundleCore period hPeriod).coordChange
          anchor ((1 : Int) +ᵥ anchor) base normal) =
      -geometricJunctionResidual period hPeriod splitting firstField secondField base normal := by
  dsimp only
  simp only [geometricJunctionResidual, LinearMap.add_apply]
  rw [geometricNormalFlux_oneLoop, geometricNormalFlux_oneLoop]
  ring

/-- Pairing the twisted residual with a twisted normal test produces a genuine
global scalar function on the quotient throat. -/
def descendedFluxPairing
    (splitting : DifferentialNormalSplitting period hPeriod)
    (firstField secondField : SmoothQuotientField period hPeriod Real)
    (test : SmoothNormalTest period hPeriod)
    (point : EffectiveThroat period hPeriod) : Real :=
  geometricJunctionResidual period hPeriod splitting firstField secondField point
    (test point)

/-- Weak integrated normal-flux balance. -/
def weakGeometricNormalBalance
    (splitting : DifferentialNormalSplitting period hPeriod)
    (firstField secondField : SmoothQuotientField period hPeriod Real)
    (test : SmoothNormalTest period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) : Real :=
  ∫ point, descendedFluxPairing period hPeriod splitting
    firstField secondField test point ∂mu

/-- Junction action obtained by pairing the geometric normal residual with an
independent smooth normal junction section. -/
def geometricJunctionAction
    (splitting : DifferentialNormalSplitting period hPeriod)
    (firstField secondField : SmoothQuotientField period hPeriod Real)
    (junction : SmoothNormalTest period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) : Real :=
  weakGeometricNormalBalance period hPeriod splitting
    firstField secondField junction mu

/-- Affine variation inside the genuine normal-section space. -/
def normalAffineCurve
    (junction test : SmoothNormalTest period hPeriod)
    (epsilon : Real) : SmoothNormalTest period hPeriod :=
  junction + epsilon • test

theorem descendedFluxPairing_affine
    (splitting : DifferentialNormalSplitting period hPeriod)
    (firstField secondField : SmoothQuotientField period hPeriod Real)
    (junction test : SmoothNormalTest period hPeriod)
    (epsilon : Real) (point : EffectiveThroat period hPeriod) :
    descendedFluxPairing period hPeriod splitting firstField secondField
        (normalAffineCurve period hPeriod junction test epsilon) point =
      descendedFluxPairing period hPeriod splitting firstField secondField
          junction point +
        epsilon * descendedFluxPairing period hPeriod splitting
          firstField secondField test point := by
  simp [descendedFluxPairing, normalAffineCurve, map_add, map_smul]

/-- Exact affine expansion of the junction action.  Integrability is stated
explicitly because the pointwise normal splitting is not claimed smooth. -/
theorem geometricJunctionAction_affine
    (splitting : DifferentialNormalSplitting period hPeriod)
    (firstField secondField : SmoothQuotientField period hPeriod Real)
    (junction test : SmoothNormalTest period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod))
    (hJunction : Integrable (descendedFluxPairing period hPeriod splitting
      firstField secondField junction) mu)
    (hTest : Integrable (descendedFluxPairing period hPeriod splitting
      firstField secondField test) mu)
    (epsilon : Real) :
    geometricJunctionAction period hPeriod splitting firstField secondField
        (normalAffineCurve period hPeriod junction test epsilon) mu =
      geometricJunctionAction period hPeriod splitting firstField secondField
          junction mu +
        epsilon * weakGeometricNormalBalance period hPeriod splitting
          firstField secondField test mu := by
  unfold geometricJunctionAction weakGeometricNormalBalance
  simp_rw [descendedFluxPairing_affine period hPeriod splitting
    firstField secondField junction test epsilon]
  rw [integral_add hJunction (hTest.const_mul epsilon)]
  simp only [integral_const_mul]

/-- The weak balance is the exact first variation of the geometric action. -/
theorem geometricJunctionAction_affine_hasDerivAt
    (splitting : DifferentialNormalSplitting period hPeriod)
    (firstField secondField : SmoothQuotientField period hPeriod Real)
    (junction test : SmoothNormalTest period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod))
    (hJunction : Integrable (descendedFluxPairing period hPeriod splitting
      firstField secondField junction) mu)
    (hTest : Integrable (descendedFluxPairing period hPeriod splitting
      firstField secondField test) mu) :
    HasDerivAt
      (fun epsilon : Real =>
        geometricJunctionAction period hPeriod splitting firstField secondField
          (normalAffineCurve period hPeriod junction test epsilon) mu)
      (weakGeometricNormalBalance period hPeriod splitting
        firstField secondField test mu) 0 := by
  rw [show (fun epsilon : Real =>
      geometricJunctionAction period hPeriod splitting firstField secondField
        (normalAffineCurve period hPeriod junction test epsilon) mu) =
      (fun epsilon : Real =>
        geometricJunctionAction period hPeriod splitting firstField secondField
            junction mu +
          epsilon * weakGeometricNormalBalance period hPeriod splitting
            firstField secondField test mu) from by
      funext epsilon
      exact geometricJunctionAction_affine period hPeriod splitting
        firstField secondField junction test mu hJunction hTest epsilon]
  simpa using
    ((hasDerivAt_id' (0 : Real)).mul_const
      (weakGeometricNormalBalance period hPeriod splitting
        firstField secondField test mu))

/-- Stationarity of the geometric junction action in all integrable normal
directions. -/
def GeometricJunctionStationary
    (splitting : DifferentialNormalSplitting period hPeriod)
    (firstField secondField : SmoothQuotientField period hPeriod Real)
    (junction : SmoothNormalTest period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) : Prop :=
  forall test : SmoothNormalTest period hPeriod,
    Integrable (descendedFluxPairing period hPeriod splitting
      firstField secondField test) mu ->
    HasDerivAt
      (fun epsilon : Real =>
        geometricJunctionAction period hPeriod splitting firstField secondField
          (normalAffineCurve period hPeriod junction test epsilon) mu)
      0 0

/-- Stationarity derives the weak balance; the balance is not an input to the
normal splitting or to the action. -/
theorem stationary_weak_geometric_normal_balance
    (splitting : DifferentialNormalSplitting period hPeriod)
    (firstField secondField : SmoothQuotientField period hPeriod Real)
    (junction test : SmoothNormalTest period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod))
    (hJunction : Integrable (descendedFluxPairing period hPeriod splitting
      firstField secondField junction) mu)
    (hTest : Integrable (descendedFluxPairing period hPeriod splitting
      firstField secondField test) mu)
    (hStationary : GeometricJunctionStationary period hPeriod splitting
      firstField secondField junction mu) :
    weakGeometricNormalBalance period hPeriod splitting
      firstField secondField test mu = 0 :=
  (geometricJunctionAction_affine_hasDerivAt period hPeriod splitting
    firstField secondField junction test mu hJunction hTest).unique
      (hStationary test hTest)

/-- Multiply a genuine twisted normal section by a global scalar throat test.
No nonvanishing normal frame is created. -/
def scalarTimesNormalTest
    (scalar : SmoothThroatField period hPeriod Real)
    (normal : SmoothNormalTest period hPeriod) :
    SmoothNormalTest period hPeriod where
  toFun point := scalar point • normal point
  contMDiff_toFun := scalar.contMDiff_toFun.smul_section normal.contMDiff

/-- Conditional constitutive identification of the old scalar Robin flux with
the geometric derivative of the same bulk scalar along a selected normal
section.  Existence, nonvanishing, and smooth regularity of a global normal
frame are deliberately not asserted. -/
def GeometricRobinNormalLaw
    (splitting : DifferentialNormalSplitting period hPeriod)
    (coefficient : Real)
    (bulk : SmoothQuotientField period hPeriod Real)
    (junction : SmoothThroatField period hPeriod Real)
    (referenceNormal : SmoothNormalTest period hPeriod) : Prop :=
  forall point : EffectiveThroat period hPeriod,
    geometricNormalFlux period hPeriod splitting bulk point
        (referenceNormal point) =
      coefficient *
        (junction point - throatTrace period hPeriod Real bulk point)

/-- Under the explicitly isolated constitutive law, pairing the true twisted
normal residual with a scalar multiple of the reference normal is exactly the
already compiled Robin first-variation density. -/
theorem descendedFluxPairing_eq_robinFirstVariationDensity
    (splitting : DifferentialNormalSplitting period hPeriod)
    (kFirst kSecond : Real)
    (firstField secondField : SmoothQuotientField period hPeriod Real)
    (junction scalarTest : SmoothThroatField period hPeriod Real)
    (referenceNormal : SmoothNormalTest period hPeriod)
    (hFirst : GeometricRobinNormalLaw period hPeriod splitting kFirst
      firstField junction referenceNormal)
    (hSecond : GeometricRobinNormalLaw period hPeriod splitting kSecond
      secondField junction referenceNormal)
    (point : EffectiveThroat period hPeriod) :
    descendedFluxPairing period hPeriod splitting firstField secondField
        (scalarTimesNormalTest period hPeriod scalarTest referenceNormal) point =
      robinFirstVariationDensity period hPeriod kFirst kSecond
        firstField secondField junction scalarTest point := by
  change
    (geometricNormalFlux period hPeriod splitting firstField point +
        geometricNormalFlux period hPeriod splitting secondField point)
        (scalarTest point • referenceNormal point) =
      (kFirst *
          (junction point - throatTrace period hPeriod Real firstField point) +
        kSecond *
          (junction point - throatTrace period hPeriod Real secondField point)) *
        scalarTest point
  rw [LinearMap.add_apply, map_smul, map_smul, hFirst point, hSecond point]
  ring

/-- The geometric junction functional restricts to the compiled Robin first
variation whenever the conditional normal law holds. -/
theorem weakGeometricNormalBalance_eq_robinFirstVariation
    (splitting : DifferentialNormalSplitting period hPeriod)
    (kFirst kSecond : Real)
    (firstField secondField : SmoothQuotientField period hPeriod Real)
    (junction scalarTest : SmoothThroatField period hPeriod Real)
    (referenceNormal : SmoothNormalTest period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod))
    (hFirst : GeometricRobinNormalLaw period hPeriod splitting kFirst
      firstField junction referenceNormal)
    (hSecond : GeometricRobinNormalLaw period hPeriod splitting kSecond
      secondField junction referenceNormal) :
    weakGeometricNormalBalance period hPeriod splitting firstField secondField
        (scalarTimesNormalTest period hPeriod scalarTest referenceNormal) mu =
      robinFirstVariation period hPeriod kFirst kSecond firstField secondField
        junction scalarTest mu := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun point =>
    descendedFluxPairing_eq_robinFirstVariationDensity period hPeriod splitting
      kFirst kSecond firstField secondField junction scalarTest referenceNormal
      hFirst hSecond point

/-- Geometric stationarity implies the compiled weak Robin balance along every
admissible scalar-times-normal test satisfying the constitutive bridge. -/
theorem stationary_weak_robin_balance_of_geometricNormalLaw
    (splitting : DifferentialNormalSplitting period hPeriod)
    (kFirst kSecond : Real)
    (firstField secondField : SmoothQuotientField period hPeriod Real)
    (junctionNormal : SmoothNormalTest period hPeriod)
    (junction scalarTest : SmoothThroatField period hPeriod Real)
    (referenceNormal : SmoothNormalTest period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod))
    (hJunction : Integrable (descendedFluxPairing period hPeriod splitting
      firstField secondField junctionNormal) mu)
    (hTest : Integrable (descendedFluxPairing period hPeriod splitting
      firstField secondField
        (scalarTimesNormalTest period hPeriod scalarTest referenceNormal)) mu)
    (hStationary : GeometricJunctionStationary period hPeriod splitting
      firstField secondField junctionNormal mu)
    (hFirst : GeometricRobinNormalLaw period hPeriod splitting kFirst
      firstField junction referenceNormal)
    (hSecond : GeometricRobinNormalLaw period hPeriod splitting kSecond
      secondField junction referenceNormal) :
    robinFirstVariation period hPeriod kFirst kSecond firstField secondField
      junction scalarTest mu = 0 := by
  rw [← weakGeometricNormalBalance_eq_robinFirstVariation period hPeriod
    splitting kFirst kSecond firstField secondField junction scalarTest
    referenceNormal mu hFirst hSecond]
  exact stationary_weak_geometric_normal_balance period hPeriod splitting
    firstField secondField junctionNormal
    (scalarTimesNormalTest period hPeriod scalarTest referenceNormal) mu
    hJunction hTest hStationary

end

end P0EFTJanusMappingTorusGeometricNormalJunction4D
end JanusFormal
