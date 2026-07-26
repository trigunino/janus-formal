import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAmbientPinMinusCechCoherenceClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAmbientPinMinusTopologicalGroup4D

/-!
# Explicit Pin-minus gauge from the reference axis to the real normal

The actual latitude normal has zero reference-axis component.  After
normalization it is therefore orthogonal to the fixed reference vector.  The
normalized Clifford vector proportional to `e + n` is a global half-angle
gauge and obeys

`e * gauge = gauge * n`.

Consequently it intertwines every integer winding, giving the exact
vertex-gauge restriction equation pointwise and without path choices.
Continuity is isolated below as continuity of this one explicit formula.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusAmbientPinMinusRealNormalRestrictionGauge4D

set_option autoImplicit false

noncomputable section

open Set Topology
open CliffordAlgebra
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusAmbientTangentQuadraticReduction
open P0EFTJanusMappingTorusAmbientPinMinusProjection4D
open P0EFTJanusMappingTorusAmbientPinMinusTopologicalGroup4D
open P0EFTJanusMappingTorusAmbientJacobianWindingChartGaugeNoGo4D
open P0EFTJanusMappingTorusAmbientCanonicalReferenceWinding4D
open P0EFTJanusMappingTorusAmbientCanonicalLatitudePinMinusLift4D
open P0EFTJanusMappingTorusAmbientPinMinusCechCoherenceClosure4D
open P0EFTJanusMappingTorusIntrinsicCanonicalLatitudeNormalImage4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatCover := MappingTorusCover (ThroatData period hPeriod)
private abbrev ThroatBase := MappingTorus (ThroatData period hPeriod)

/-- Normalization preserves a zero reference-axis component. -/
theorem ambientNormalizeNormal_snd_eq_zero
    (normal : CoverCoordinates) (hHorizontal : normal.2 = 0) :
    (ambientNormalizeNormal normal).2 = 0 := by
  simp [ambientNormalizeNormal, hHorizontal]

/-- Half-angle vector joining the fixed reference axis to a nonzero
horizontal normal. -/
def ambientPinMinusHalfAngleVector
    (normal : CoverCoordinates) : CoverCoordinates :=
  ambientPinMinusReferenceVector + ambientNormalizeNormal normal

theorem ambientPinMinusHalfAngleVector_ne_zero
    (normal : CoverCoordinates) (hHorizontal : normal.2 = 0) :
    ambientPinMinusHalfAngleVector normal ≠ 0 := by
  intro hZero
  have hSecond := congrArg Prod.snd hZero
  simp [ambientPinMinusHalfAngleVector, ambientPinMinusReferenceVector,
    ambientNormalizeNormal_snd_eq_zero normal hHorizontal] at hSecond

/-- Explicit Pin-minus half-angle gauge. -/
def ambientPinMinusHalfAngleGauge
    (normal : CoverCoordinates) (hHorizontal : normal.2 = 0) :
    AmbientCoordinatePinMinusGroup :=
  ambientNormalizedPinMinusGenerator
    (ambientPinMinusHalfAngleVector normal)
    (ambientPinMinusHalfAngleVector_ne_zero normal hHorizontal)

theorem ambientPinMinusHalfAngleGauge_congr
    {first second : CoverCoordinates}
    (hFirst : first.2 = 0) (hSecond : second.2 = 0)
    (hNormal : first = second) :
    ambientPinMinusHalfAngleGauge first hFirst =
      ambientPinMinusHalfAngleGauge second hSecond := by
  subst second
  rfl

/-- The reference generator and normalized normal generator are intertwined
by the explicit half-angle gauge. -/
theorem ambientPinMinusHalfAngleGauge_intertwines
    (normal : CoverCoordinates) (hNormal : normal ≠ 0)
    (hHorizontal : normal.2 = 0) :
    ambientPinMinusReferenceGenerator *
        ambientPinMinusHalfAngleGauge normal hHorizontal =
      ambientPinMinusHalfAngleGauge normal hHorizontal *
        ambientNormalizedPinMinusGenerator normal hNormal := by
  let reference := ambientPinMinusReferenceVector
  let unitNormal := ambientNormalizeNormal normal
  let sumNormal := reference + unitNormal
  let unitSum := ambientNormalizeNormal sumNormal
  have hUnitNormal :
      ambientCoverEuclideanQuadraticForm unitNormal = 1 :=
    ambientNormalizeNormal_unit normal hNormal
  have hSumNonzero : sumNormal ≠ 0 := by
    exact ambientPinMinusHalfAngleVector_ne_zero normal hHorizontal
  have hReferenceSq :
      CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm reference *
          CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm reference =
        -(1 : AmbientPinMinusCliffordAlgebra) := by
    rw [CliffordAlgebra.ι_sq_scalar]
    have hReference :
        ambientCoverPinMinusQuadraticForm reference = -1 := by
      simpa [reference] using
        ambientPinMinusReferenceVector_negative_unit
    rw [hReference]
    simp
  have hNormalSq :
      CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm unitNormal *
          CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm unitNormal =
        -(1 : AmbientPinMinusCliffordAlgebra) := by
    rw [CliffordAlgebra.ι_sq_scalar]
    have hNormalNegative :
        ambientCoverPinMinusQuadraticForm unitNormal = -1 := by
      simp [ambientCoverPinMinusQuadraticForm, hUnitNormal]
    rw [hNormalNegative]
    simp
  apply Subtype.ext
  change
    CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm reference *
        CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm unitSum =
      CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm unitSum *
        CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm unitNormal
  change
    CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm reference *
        CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm
          ((Real.sqrt
            (ambientCoverEuclideanQuadraticForm sumNormal))⁻¹ • sumNormal) =
      CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm
          ((Real.sqrt
            (ambientCoverEuclideanQuadraticForm sumNormal))⁻¹ • sumNormal) *
        CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm unitNormal
  simp only [map_smul]
  rw [mul_smul_comm, smul_mul_assoc]
  change
    _ •
        (CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm reference *
          CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm
            (reference + unitNormal)) =
      _ •
        (CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm
            (reference + unitNormal) *
          CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm unitNormal)
  simp only [(CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm).map_add,
    mul_add, add_mul, hReferenceSq, hNormalSq]
  rw [add_comm]

/-- The same gauge intertwines every positive or negative winding. -/
theorem ambientPinMinusHalfAngleGauge_intertwines_zpow
    (normal : CoverCoordinates) (hNormal : normal ≠ 0)
    (hHorizontal : normal.2 = 0) (winding : Int) :
    ambientPinMinusReferenceGenerator ^ winding *
        ambientPinMinusHalfAngleGauge normal hHorizontal =
      ambientPinMinusHalfAngleGauge normal hHorizontal *
        ambientNormalizedPinMinusGenerator normal hNormal ^ winding :=
  integerHolonomy_intertwined_of_generator
    ambientPinMinusReferenceGenerator
    (ambientNormalizedPinMinusGenerator normal hNormal)
    (ambientPinMinusHalfAngleGauge normal hHorizontal)
    (ambientPinMinusHalfAngleGauge_intertwines normal hNormal hHorizontal)
    winding

/-- The explicit half-angle construction is continuous along every continuous
nonvanishing horizontal normal field. -/
theorem ambientPinMinusHalfAngleGauge_continuousOn
    {Parameter : Type*} [TopologicalSpace Parameter]
    {domain : Set Parameter}
    (normal : Parameter → CoverCoordinates)
    (hContinuous : ContinuousOn normal domain)
    (hNonzero : ∀ point ∈ domain, normal point ≠ 0)
    (hHorizontal : ∀ point, (normal point).2 = 0) :
    ContinuousOn
      (fun point =>
        ambientPinMinusHalfAngleGauge
          (normal point) (hHorizontal point))
      domain := by
  rw [ambientCoordinatePinMinus_coe_isEmbedding.continuousOn_iff]
  intro point hPoint
  have hNormalized :
      ContinuousWithinAt
        (fun current => ambientNormalizeNormal (normal current))
        domain point :=
    (ambientNormalizeNormal_contDiffAt
      (normal point) (hNonzero point hPoint)).continuousAt
      |>.comp_continuousWithinAt (hContinuous point hPoint)
  have hSum :
      ContinuousWithinAt
        (fun current =>
          ambientPinMinusReferenceVector +
            ambientNormalizeNormal (normal current))
        domain point :=
    continuousWithinAt_const.add hNormalized
  have hSumNonzero :
      ambientPinMinusReferenceVector +
          ambientNormalizeNormal (normal point) ≠ 0 :=
    ambientPinMinusHalfAngleVector_ne_zero
      (normal point) (hHorizontal point)
  have hRenormalized :
      ContinuousWithinAt
        (fun current =>
          ambientNormalizeNormal
            (ambientPinMinusReferenceVector +
              ambientNormalizeNormal (normal current)))
        domain point :=
    by
      have hOuter :
          ContinuousAt ambientNormalizeNormal
            (ambientPinMinusReferenceVector +
              ambientNormalizeNormal (normal point)) :=
        (ambientNormalizeNormal_contDiffAt
          (ambientPinMinusReferenceVector +
            ambientNormalizeNormal (normal point)) hSumNonzero).continuousAt
      change ContinuousWithinAt
        (ambientNormalizeNormal ∘
          fun current =>
            ambientPinMinusReferenceVector +
              ambientNormalizeNormal (normal current))
        domain point
      exact hOuter.comp_continuousWithinAt
        (f := fun current =>
          ambientPinMinusReferenceVector +
            ambientNormalizeNormal (normal current)) hSum
  have hIota :
      Continuous
        (CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm) :=
    LinearMap.continuous_of_finiteDimensional _
  change ContinuousWithinAt
    (fun current =>
      CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm
        (ambientNormalizeNormal
          (ambientPinMinusReferenceVector +
            ambientNormalizeNormal (normal current))))
    domain point
  exact hIota.continuousAt.comp_continuousWithinAt hRenormalized

/-- Product coordinates of the real latitude normal are horizontal relative
to the fixed reference axis. -/
theorem canonicalLatitudeNormalCoordinates_snd_eq_zero
    (anchor : ThroatCover period hPeriod) :
    (canonicalLatitudeNormalCoordinates period hPeriod anchor).2 = 0 := by
  unfold canonicalLatitudeNormalCoordinates
  rw [coverProductDerivative_latitudeNormal]

theorem canonicalLatitudeSectionNormal_snd_eq_zero
    (chart : ThroatCover period hPeriod)
    (base : ThroatBase period hPeriod) :
    (canonicalLatitudeSectionNormal period hPeriod chart base).2 = 0 := by
  unfold canonicalLatitudeSectionNormal
  exact canonicalLatitudeNormalCoordinates_snd_eq_zero period hPeriod _

/-- Concrete chartwise half-angle gauge for the actual real normal. -/
def canonicalAmbientRealNormalRestrictionGauge
    (chart : ThroatCover period hPeriod)
    (base : ThroatBase period hPeriod) :
    AmbientCoordinatePinMinusGroup :=
  ambientPinMinusHalfAngleGauge
    (canonicalLatitudeSectionNormal period hPeriod chart base)
    (canonicalLatitudeSectionNormal_snd_eq_zero period hPeriod chart base)

/-- The explicit gauge is independent of the chart on every genuine
overlap, because the selected normal coordinates themselves agree there. -/
theorem canonicalAmbientRealNormalRestrictionGauge_eq_on_overlap
    (first second : ThroatCover period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈
      normalBundleBaseSet period hPeriod first ∩
        normalBundleBaseSet period hPeriod second) :
    canonicalAmbientRealNormalRestrictionGauge period hPeriod first base =
      canonicalAmbientRealNormalRestrictionGauge period hPeriod second base := by
  unfold canonicalAmbientRealNormalRestrictionGauge
  have hNormal := canonicalLatitudeSectionNormal_eq_on_overlap
    period hPeriod first second base hBase
  exact ambientPinMinusHalfAngleGauge_congr _ _ hNormal.symm

/-- Exact pointwise restriction equation on every compatible overlap. -/
theorem canonicalAmbientRealNormalRestrictionGauge_realizes
    (first second : ThroatCover period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase :
      base ∈ throatAmbientChartCompatibilityOverlap
        period hPeriod first second) :
    vertexGaugedTransition
        (canonicalAmbientReferenceCechTransitionOnRealNormalOverlap
          period hPeriod first second base)
        (canonicalAmbientRealNormalRestrictionGauge
          period hPeriod first base)
        (canonicalAmbientRealNormalRestrictionGauge
          period hPeriod second base) =
      canonicalRealNormalPinMinusCechTransition
        period hPeriod first second base := by
  have hNormalBase :=
    throatAmbientChartCompatibilityOverlap_subset_normalBundleOverlap
      period hPeriod first second hBase
  have hGauge :=
    canonicalAmbientRealNormalRestrictionGauge_eq_on_overlap
      period hPeriod first second base hNormalBase
  rw [hGauge]
  rw [canonicalAmbientReferenceCechTransitionOnRealNormalOverlap_eq_reference
    period hPeriod first second base hBase]
  rw [ambientPinMinusReferenceZ4Character_intCast]
  unfold canonicalRealNormalPinMinusCechTransition
    canonicalLatitudeAmbientPinMinusTransitionLift
    ambientNormalizedPinMinusWindingLift
    ambientPinMinusUnitNormalWindingLift
  let normal :=
    canonicalLatitudeSectionNormal period hPeriod second base
  let gauge :=
    canonicalAmbientRealNormalRestrictionGauge period hPeriod second base
  have hIntertwines :=
    ambientPinMinusHalfAngleGauge_intertwines_zpow
      normal
      (canonicalLatitudeSectionNormal_ne_zero period hPeriod second base)
      (canonicalLatitudeSectionNormal_snd_eq_zero
        period hPeriod second base)
      (localTransitionWinding period hPeriod second first base)
  change
    ambientPinMinusReferenceGenerator ^
          localTransitionWinding period hPeriod second first base * gauge =
      gauge *
        ambientNormalizedPinMinusGenerator normal
            (canonicalLatitudeSectionNormal_ne_zero
              period hPeriod second base) ^
          localTransitionWinding period hPeriod second first base
    at hIntertwines
  change vertexGaugedTransition
      (ambientPinMinusReferenceGenerator ^
        localTransitionWinding period hPeriod second first base)
      gauge gauge =
    ambientNormalizedPinMinusGenerator normal
        (canonicalLatitudeSectionNormal_ne_zero
          period hPeriod second base) ^
      localTransitionWinding period hPeriod second first base
  unfold vertexGaugedTransition
  calc
    gauge⁻¹ *
          ambientPinMinusReferenceGenerator ^
            localTransitionWinding period hPeriod second first base *
        gauge =
        gauge⁻¹ *
          (ambientPinMinusReferenceGenerator ^
              localTransitionWinding period hPeriod second first base *
            gauge) := by group
    _ = gauge⁻¹ *
        (gauge *
          ambientNormalizedPinMinusGenerator normal
              (canonicalLatitudeSectionNormal_ne_zero
                period hPeriod second base) ^
            localTransitionWinding period hPeriod second first base) := by
      rw [hIntertwines]
    _ = ambientNormalizedPinMinusGenerator normal
          (canonicalLatitudeSectionNormal_ne_zero
            period hPeriod second base) ^
        localTransitionWinding period hPeriod second first base := by
      group

/-- The only remaining analytic statement is continuity of one explicit
formula, rather than existence and path independence of an unspecified
zero-cochain. -/
def CanonicalAmbientRealNormalRestrictionGaugeContinuous : Prop :=
  ∀ chart : ThroatCover period hPeriod,
    ContinuousOn
      (canonicalAmbientRealNormalRestrictionGauge period hPeriod chart)
      (throatAmbientChartCompatibilityDomain period hPeriod chart)

/-- Exact remaining geometric input: continuity of the already explicit
normal coordinates on each compatible chart domain. -/
def CanonicalLatitudeSectionNormalContinuous : Prop :=
  ∀ chart : ThroatCover period hPeriod,
    ContinuousOn
      (canonicalLatitudeSectionNormal period hPeriod chart)
      (throatAmbientChartCompatibilityDomain period hPeriod chart)

theorem canonicalAmbientRealNormalRestrictionGauge_continuous_of_normal
    (hNormal : CanonicalLatitudeSectionNormalContinuous period hPeriod) :
    CanonicalAmbientRealNormalRestrictionGaugeContinuous period hPeriod := by
  intro chart
  exact ambientPinMinusHalfAngleGauge_continuousOn
    (canonicalLatitudeSectionNormal period hPeriod chart)
    (hNormal chart)
    (fun point _ =>
      canonicalLatitudeSectionNormal_ne_zero period hPeriod chart point)
    (canonicalLatitudeSectionNormal_snd_eq_zero period hPeriod chart)

theorem ambientPinMinusRealNormalRestrictionVertexGaugeExists_of_continuous
    (hContinuous :
      CanonicalAmbientRealNormalRestrictionGaugeContinuous period hPeriod) :
    AmbientPinMinusRealNormalRestrictionVertexGaugeExists period hPeriod := by
  exact ⟨{
    gauge := canonicalAmbientRealNormalRestrictionGauge period hPeriod
    continuousOn := hContinuous
    realizes_restriction :=
      canonicalAmbientRealNormalRestrictionGauge_realizes period hPeriod
  }⟩

theorem ambientPinMinusRealNormalRestrictionVertexGaugeExists_of_normalContinuous
    (hNormal : CanonicalLatitudeSectionNormalContinuous period hPeriod) :
    AmbientPinMinusRealNormalRestrictionVertexGaugeExists period hPeriod :=
  ambientPinMinusRealNormalRestrictionVertexGaugeExists_of_continuous
    period hPeriod
    (canonicalAmbientRealNormalRestrictionGauge_continuous_of_normal
      period hPeriod hNormal)

end

end P0EFTJanusMappingTorusAmbientPinMinusRealNormalRestrictionGauge4D
end JanusFormal
