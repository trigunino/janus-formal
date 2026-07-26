import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAmbientPinMinusLocalSectionsPropagation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAmbientCanonicalPinMinusActualPrincipalBundle4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAmbientCanonicalLatitudePinMinusLift4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPAmbientPinCCechExtension4D

/-!
# Ambient Pin-minus Cech coherence closure

The closed local-section theorem supplies local lifts for every reduced
orthogonal transition.  For the canonical radial reduction the true deck
winding does more: it selects continuous lifts on whole overlaps.  The
existing canonical construction then gives normalized, inverse and strict
triple-overlap laws, an actual Cech presentation and a genuine principal
`Pin⁻(4)` bundle.

The geometric latitude normal has its own exact `Pin⁻(4)` Cech cocycle.  It
is normalized, inverse coherent and triple coherent, and its projection is
the reflection aligned with the actual nonzero normal.  Identifying this
normal-aligned cocycle with the restriction of the reference-axis ambient
cocycle is a change-of-frame problem, not another Cech law.  The final
structure below isolates its exact non-circular datum: one continuous
vertex gauge on each throat chart.  Pointwise such a gauge always exists
uniquely after fixing the target-chart gauge; only global continuity and
path independence remain.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusAmbientPinMinusCechCoherenceClosure4D

set_option autoImplicit false

noncomputable section

open Set Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusNormalPinMinusPrincipalBundle
open P0EFTJanusMappingTorusAmbientTangentOrientationCocycle
open P0EFTJanusMappingTorusAmbientTangentQuadraticReduction
open P0EFTJanusMappingTorusAmbientPinMinusProjection4D
open P0EFTJanusMappingTorusAmbientPinMinusLocalSectionCriterion4D
open P0EFTJanusMappingTorusAmbientPinMinusLocalSectionsClosure4D
open P0EFTJanusMappingTorusAmbientPinMinusLocalSectionsPropagation4D
open P0EFTJanusMappingTorusAmbientCanonicalReferenceWinding4D
open P0EFTJanusMappingTorusAmbientCanonicalReferencePinMinusCech4D
open P0EFTJanusMappingTorusAmbientRadialReferenceSmoothReduction4D
open P0EFTJanusMappingTorusAmbientPinMinusPrincipalBundle4D
open P0EFTJanusMappingTorusAmbientCanonicalPinMinusActualPrincipalBundle4D
open P0EFTJanusMappingTorusAmbientJacobianWindingChartGaugeNoGo4D
open P0EFTJanusMappingTorusAmbientCanonicalLatitudePinMinusLift4D
open P0EFTJanusProgramPAmbientPinCCechExtension4D
open P0EFTJanusEuclideanGlobalSpinCJetRealization

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev AmbientData := reflectedSphereData period hPeriod
private abbrev AmbientCover := MappingTorusCover (AmbientData period hPeriod)
private abbrev AmbientBase := MappingTorus (AmbientData period hPeriod)
private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatCover := MappingTorusCover (ThroatData period hPeriod)
private abbrev ThroatBase := MappingTorus (ThroatData period hPeriod)

/-! ## Whole-overlap ambient Cech closure -/

/-- The canonical whole-overlap transition is normalized. -/
theorem canonicalAmbientPinMinusCechTransition_normalized
    (anchor : AmbientCover period hPeriod)
    (base : AmbientBase period hPeriod)
    (hBase :
      base ∈ (canonicalAmbientPinMinusCechBundle period hPeriod).domain anchor) :
    (canonicalAmbientPinMinusCechBundle period hPeriod).transition
        anchor anchor base = 1 :=
  (canonicalAmbientPinMinusCechBundle period hPeriod).transition_self
    anchor base hBase

/-- The reverse whole-overlap transition is the group inverse. -/
theorem canonicalAmbientPinMinusCechTransition_inverse
    (first second : AmbientCover period hPeriod)
    (base : AmbientBase period hPeriod)
    (hFirst :
      base ∈ (canonicalAmbientPinMinusCechBundle period hPeriod).domain first)
    (hSecond :
      base ∈ (canonicalAmbientPinMinusCechBundle period hPeriod).domain second) :
    (canonicalAmbientPinMinusCechBundle period hPeriod).transition
        second first base =
      ((canonicalAmbientPinMinusCechBundle period hPeriod).transition
        first second base)⁻¹ :=
  eq_inv_of_mul_eq_one_right
    ((canonicalAmbientPinMinusCechBundle period hPeriod).transition_inverse
      first second base hFirst hSecond)

/-- Strict whole-overlap triple coherence. -/
theorem canonicalAmbientPinMinusCechTransition_cocycle
    (first second third : AmbientCover period hPeriod)
    (base : AmbientBase period hPeriod)
    (hFirst :
      base ∈ (canonicalAmbientPinMinusCechBundle period hPeriod).domain first)
    (hSecond :
      base ∈ (canonicalAmbientPinMinusCechBundle period hPeriod).domain second)
    (hThird :
      base ∈ (canonicalAmbientPinMinusCechBundle period hPeriod).domain third) :
    (canonicalAmbientPinMinusCechBundle period hPeriod).transition
          first second base *
        (canonicalAmbientPinMinusCechBundle period hPeriod).transition
          second third base =
      (canonicalAmbientPinMinusCechBundle period hPeriod).transition
        first third base :=
  (canonicalAmbientPinMinusCechBundle period hPeriod).transition_cocycle
    first second third base hFirst hSecond hThird

/-- The selected whole-overlap transition is continuous. -/
theorem canonicalAmbientPinMinusCechTransition_continuousOn
    (first second : AmbientCover period hPeriod) :
    ContinuousOn
      ((canonicalAmbientPinMinusCechBundle period hPeriod).transition
        first second)
      ((canonicalAmbientPinMinusCechBundle period hPeriod).domain first ∩
        (canonicalAmbientPinMinusCechBundle period hPeriod).domain second) := by
  simpa [canonicalAmbientPinMinusCechBundle,
    canonicalAmbientPinMinusPrincipalBundleCore, Set.inter_comm] using
    canonicalAmbientPinMinusPrincipalTransition_continuousOn
      period hPeriod second first

/-- Its Pin-minus projection is exactly the canonical smooth radial
orthogonal reduction on every genuine overlap. -/
theorem canonicalAmbientPinMinusWholeOverlapLift_projects_to_radialReduction
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate :
      coordinate ∈
        (ambientAtlasTransition period hPeriod first second).source) :
    ambientPinMinusProjection
        (canonicalAmbientReferencePinMinusTransitionLift period hPeriod
          first second coordinate) =
      (ambientRadialReferenceContMDiffOrthonormalAtlasReduction period hPeriod
        |>.toPointwise.orthogonalTransition period hPeriod first second
          coordinate hCoordinate).toLinearEquiv :=
  canonicalAmbientPinMinusTransitionLift_projects_to_radialReduction
    period hPeriod first second coordinate hCoordinate

/-- The genuine canonical principal Pin-minus bundle is now unconditional. -/
theorem canonicalAmbientPinMinusActualPrincipalBundle_nonempty :
    Nonempty (CanonicalAmbientPinMinusActualPrincipalBundle period hPeriod) :=
  ⟨canonicalAmbientPinMinusActualPrincipalBundle period hPeriod⟩

/-! ## Cech cocycle of the actual real normal -/

/-- Cech-convention transition of the geometric latitude normal.  Reversing
the two chart indices matches the convention used by
`CechPrincipalBundleData`. -/
def canonicalRealNormalPinMinusCechTransition
    (first second : ThroatCover period hPeriod)
    (base : ThroatBase period hPeriod) : AmbientCoordinatePinMinusGroup :=
  canonicalLatitudeAmbientPinMinusTransitionLift
    period hPeriod second first base

/-- Exact Cech data carried by the actual nonzero latitude normal. -/
structure AmbientRealNormalPinMinusCechData where
  transition :
    ThroatCover period hPeriod → ThroatCover period hPeriod →
      ThroatBase period hPeriod → AmbientCoordinatePinMinusGroup
  normalized :
    ∀ chart base,
      base ∈ normalBundleBaseSet period hPeriod chart →
        transition chart chart base = 1
  inverse :
    ∀ first second base,
      base ∈ normalBundleBaseSet period hPeriod first →
      base ∈ normalBundleBaseSet period hPeriod second →
        transition first second base * transition second first base = 1
  cocycle :
    ∀ first second third base,
      base ∈ normalBundleBaseSet period hPeriod first →
      base ∈ normalBundleBaseSet period hPeriod second →
      base ∈ normalBundleBaseSet period hPeriod third →
        transition first second base * transition second third base =
          transition first third base
  projects_to_aligned_real_normal :
    ∀ first second base,
      ambientPinMinusProjection (transition first second base) =
        (ambientNormalizedQuaternionAlignedReflection
          (canonicalLatitudeSectionNormal period hPeriod second base)
          (canonicalLatitudeSectionNormal_ne_zero
            period hPeriod second base)).toLinearEquiv ^
          localTransitionWinding period hPeriod second first base

/-- The actual latitude normal supplies the preceding Cech data without any
additional choice. -/
def canonicalAmbientRealNormalPinMinusCechData :
    AmbientRealNormalPinMinusCechData period hPeriod where
  transition := canonicalRealNormalPinMinusCechTransition period hPeriod
  normalized chart base hBase :=
    canonicalLatitudeAmbientPinMinusTransitionLift_normalized
      period hPeriod chart base hBase
  inverse first second base hFirst hSecond := by
    rw [canonicalRealNormalPinMinusCechTransition,
      canonicalRealNormalPinMinusCechTransition,
      canonicalLatitudeAmbientPinMinusTransitionLift_inverse
        period hPeriod first second base ⟨hFirst, hSecond⟩]
    simp
  cocycle first second third base hFirst hSecond hThird :=
    canonicalLatitudeAmbientPinMinusTransitionLift_cocycle
      period hPeriod third second first base
        ⟨⟨hThird, hSecond⟩, hFirst⟩
  projects_to_aligned_real_normal first second base :=
    canonicalLatitudeAmbientPinMinusTransitionLift_projection
      period hPeriod second first base

theorem canonicalRealNormalPinMinusCechTransition_inverse
    (first second : ThroatCover period hPeriod)
    (base : ThroatBase period hPeriod)
    (hFirst : base ∈ normalBundleBaseSet period hPeriod first)
    (hSecond : base ∈ normalBundleBaseSet period hPeriod second) :
    canonicalRealNormalPinMinusCechTransition period hPeriod second first base =
      (canonicalRealNormalPinMinusCechTransition
        period hPeriod first second base)⁻¹ := by
  exact eq_inv_of_mul_eq_one_right
    ((canonicalAmbientRealNormalPinMinusCechData period hPeriod).inverse
      first second base hFirst hSecond)

theorem canonicalRealNormalPinMinusCechTransition_cocycle
    (first second third : ThroatCover period hPeriod)
    (base : ThroatBase period hPeriod)
    (hFirst : base ∈ normalBundleBaseSet period hPeriod first)
    (hSecond : base ∈ normalBundleBaseSet period hPeriod second)
    (hThird : base ∈ normalBundleBaseSet period hPeriod third) :
    canonicalRealNormalPinMinusCechTransition period hPeriod first second base *
        canonicalRealNormalPinMinusCechTransition
          period hPeriod second third base =
      canonicalRealNormalPinMinusCechTransition
        period hPeriod first third base :=
  (canonicalAmbientRealNormalPinMinusCechData period hPeriod).cocycle
    first second third base hFirst hSecond hThird

/-! ## Exact residual comparison datum -/

/-- Restriction of the canonical ambient reference-axis Cech transition to a
genuine throat/ambient compatibility overlap, in Cech index convention. -/
def canonicalAmbientReferenceCechTransitionOnRealNormalOverlap
    (first second : ThroatCover period hPeriod)
    (base : ThroatBase period hPeriod) : AmbientCoordinatePinMinusGroup :=
  canonicalAmbientReferencePinMinusTransitionLift period hPeriod
    (fixedThroatCoverInclusion period hPeriod second)
    (fixedThroatCoverInclusion period hPeriod first)
    (throatAmbientOverlapCoordinate period hPeriod second base)

theorem canonicalAmbientReferenceCechTransitionOnRealNormalOverlap_eq_reference
    (first second : ThroatCover period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase :
      base ∈ throatAmbientChartCompatibilityOverlap
        period hPeriod first second) :
    canonicalAmbientReferenceCechTransitionOnRealNormalOverlap
        period hPeriod first second base =
      ambientPinMinusReferenceZ4Character
        (localTransitionWinding period hPeriod second first base : ZMod 4) := by
  exact canonicalAmbientReferencePinMinusTransitionLift_restricts_to_throat
    period hPeriod second first base ⟨hBase.2, hBase.1⟩

/-- Minimal non-circular compatibility datum.  It is a continuous Cech
zero-cochain, not another independently postulated family of edge lifts. -/
structure AmbientPinMinusRealNormalRestrictionVertexGauge where
  gauge :
    ThroatCover period hPeriod → ThroatBase period hPeriod →
      AmbientCoordinatePinMinusGroup
  continuousOn : ∀ chart,
    ContinuousOn (gauge chart)
      (throatAmbientChartCompatibilityDomain period hPeriod chart)
  realizes_restriction :
    ∀ first second base,
      base ∈ throatAmbientChartCompatibilityOverlap
        period hPeriod first second →
      vertexGaugedTransition
          (canonicalAmbientReferenceCechTransitionOnRealNormalOverlap
            period hPeriod first second base)
          (gauge first base) (gauge second base) =
        canonicalRealNormalPinMinusCechTransition
          period hPeriod first second base

/-- Exact remaining proposition for identifying the canonical ambient bundle
with the actual-normal restriction. -/
def AmbientPinMinusRealNormalRestrictionVertexGaugeExists : Prop :=
  Nonempty (AmbientPinMinusRealNormalRestrictionVertexGauge period hPeriod)

/-- There is no pointwise algebraic obstruction: after fixing the gauge in
the target chart, the source-chart gauge exists uniquely. -/
theorem existsUnique_sourceGauge_realizing_realNormalRestriction
    (first second : ThroatCover period hPeriod)
    (base : ThroatBase period hPeriod)
    (targetGauge : AmbientCoordinatePinMinusGroup) :
    ∃! sourceGauge : AmbientCoordinatePinMinusGroup,
      vertexGaugedTransition
          (canonicalAmbientReferenceCechTransitionOnRealNormalOverlap
            period hPeriod first second base)
          sourceGauge targetGauge =
        canonicalRealNormalPinMinusCechTransition
          period hPeriod first second base :=
  vertexGauge_source_existsUnique
    (canonicalAmbientReferenceCechTransitionOnRealNormalOverlap
      period hPeriod first second base)
    (canonicalRealNormalPinMinusCechTransition
      period hPeriod first second base)
    targetGauge

/-- The residual datum is exactly one continuous vertex zero-cochain obeying
the displayed restriction equation. -/
theorem ambientPinMinusRealNormalRestrictionVertexGaugeExists_iff :
    AmbientPinMinusRealNormalRestrictionVertexGaugeExists period hPeriod ↔
      ∃ gauge :
          ThroatCover period hPeriod → ThroatBase period hPeriod →
            AmbientCoordinatePinMinusGroup,
        (∀ chart,
          ContinuousOn (gauge chart)
            (throatAmbientChartCompatibilityDomain period hPeriod chart)) ∧
        ∀ first second base,
          base ∈ throatAmbientChartCompatibilityOverlap
              period hPeriod first second →
            vertexGaugedTransition
                (canonicalAmbientReferenceCechTransitionOnRealNormalOverlap
                  period hPeriod first second base)
                (gauge first base) (gauge second base) =
              canonicalRealNormalPinMinusCechTransition
                period hPeriod first second base := by
  constructor
  · rintro ⟨choice⟩
    exact ⟨choice.gauge, choice.continuousOn, choice.realizes_restriction⟩
  · rintro ⟨gauge, hContinuous, hRestriction⟩
    exact ⟨{
      gauge := gauge
      continuousOn := hContinuous
      realizes_restriction := hRestriction
    }⟩

/-- Packaged unconditional closure: local sections, the canonical global
Cech bundle, the genuine principal bundle and the coherent real-normal Cech
data all coexist.  Only their continuous vertex-gauge identification is kept
as the explicit proposition above. -/
structure AmbientPinMinusCechCoherenceClosureCertificate4D where
  projectionLocalSections : AmbientPinMinusProjectionHasLocalSections
  ambientCech :
    CechPrincipalBundleData (AmbientBase period hPeriod)
      (AmbientCover period hPeriod) AmbientCoordinatePinMinusGroup
  ambientCech_eq :
    ambientCech = canonicalAmbientPinMinusCechBundle period hPeriod
  principalBundle :
    CanonicalAmbientPinMinusActualPrincipalBundle period hPeriod
  realNormalCech : AmbientRealNormalPinMinusCechData period hPeriod
  realNormalCech_eq :
    realNormalCech = canonicalAmbientRealNormalPinMinusCechData
      period hPeriod

def ambientPinMinusCechCoherenceClosureCertificate4D :
    AmbientPinMinusCechCoherenceClosureCertificate4D period hPeriod where
  projectionLocalSections := ambientPinMinusProjectionHasLocalSections_closed
  ambientCech := canonicalAmbientPinMinusCechBundle period hPeriod
  ambientCech_eq := rfl
  principalBundle := canonicalAmbientPinMinusActualPrincipalBundle
    period hPeriod
  realNormalCech := canonicalAmbientRealNormalPinMinusCechData period hPeriod
  realNormalCech_eq := rfl

theorem ambientPinMinusCechCoherenceClosureCertificate4D_nonempty :
    Nonempty (AmbientPinMinusCechCoherenceClosureCertificate4D
      period hPeriod) :=
  ⟨ambientPinMinusCechCoherenceClosureCertificate4D period hPeriod⟩

end

end P0EFTJanusMappingTorusAmbientPinMinusCechCoherenceClosure4D
end JanusFormal
