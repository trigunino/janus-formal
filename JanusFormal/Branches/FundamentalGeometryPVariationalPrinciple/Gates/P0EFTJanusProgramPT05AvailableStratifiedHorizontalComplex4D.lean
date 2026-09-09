import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT05GeometricNullReparametrizationIntegrationNaturality4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT05CutBulkLocalDensityStokesBridge4D

/-!
# Available stratified horizontal integration complex

This module combines the two horizontal components that already have genuine
geometric integration laws: the cut-bulk to non-null scalar-current component
and the finite null-transgression to joint component.  They occur in different
horizontal degrees, so the carrier is their graded product.  The differential
is exactly Gate 819's cellular `dH` on each factor and its square is zero.

Only the non-null component of the cut-bulk image has a supplied geometric
density.  Its simultaneous bulk-to-null cellular component remains formal.
Consequently the cut-bulk comparison below is componentwise, while the
null-to-joint comparison is an equality of whole cochains.  No density-level
global `dH`, contact differential, or terminal T05 certificate is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT05AvailableStratifiedHorizontalComplex4D

set_option autoImplicit false
noncomputable section

open Set
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusNullJointReparametrizationCancellation
open P0EFTJanusFiniteNullFaceAction
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLMobileGHYNullPhysicalProductEuler4D
open P0EFTJanusFiniteNullFaceMobileGeometricRealization4D
open P0EFTJanusFiniteNullFaceMobileCanonicalFaithfulness4D
open P0EFTJanusProgramPRelativeJetVariationalBicomplexCore4D
open P0EFTJanusProgramPRelativeJetVariationalBicomplexCore4D.RelativeJetStratum4D
open P0EFTJanusProgramPT05ExactT03RelativeVariationalRealization4D
open P0EFTJanusProgramPT05CutBulkLocalDensityStokesBridge4D
open P0EFTJanusProgramPT05BulkActionLocalDensityBridge4D
open P0EFTJanusProgramPT05GHYLocalDensityRelativeBridge4D
open P0EFTJanusProgramPT05GeometricStratifiedDensityCochain4D
open P0EFTJanusProgramPT05GeometricDensityIntegrationToRelativeCochain4D
open P0EFTJanusProgramPT05FiniteNullHorizontalIntegrationMorphism4D
open P0EFTJanusProgramPT05GeometricNullReparametrizationIntegrationNaturality4D

/-- Graded source: a degree-four cut-bulk current and a degree-three finite
null transgression. -/
abbrev ProgramPT05AvailableStratifiedHorizontalSource :=
  RelativeJetCochain ProgramPT05PhysicalJetComponent 4 0 ×
    RelativeJetCochain ProgramPT05PhysicalJetComponent 3 0

/-- Their two cellular horizontal images. -/
abbrev ProgramPT05AvailableStratifiedHorizontalTarget :=
  RelativeJetCochain ProgramPT05PhysicalJetComponent 5 0 ×
    RelativeJetCochain ProgramPT05PhysicalJetComponent 4 0

/-- The degrees reached by one further horizontal step. -/
abbrev ProgramPT05AvailableStratifiedHorizontalSecondTarget :=
  RelativeJetCochain ProgramPT05PhysicalJetComponent 6 0 ×
    RelativeJetCochain ProgramPT05PhysicalJetComponent 5 0

/-- Gate 819's horizontal differential on the two actually populated source
degrees.  This is an integrated cellular operator, not a local-density
differential. -/
def programPT05AvailableStratifiedIntegratedDH :
    ProgramPT05AvailableStratifiedHorizontalSource →ₗ[Real]
      ProgramPT05AvailableStratifiedHorizontalTarget where
  toFun source :=
    (programPT05ExactT03RelativeBicomplex.dH 4 0 source.1,
      programPT05ExactT03RelativeBicomplex.dH 3 0 source.2)
  map_add' first second := by
    apply Prod.ext <;> simp
  map_smul' scalar source := by
    apply Prod.ext <;> simp

/-- The next Gate-819 horizontal step on both graded factors. -/
def programPT05AvailableStratifiedIntegratedDHNext :
    ProgramPT05AvailableStratifiedHorizontalTarget →ₗ[Real]
      ProgramPT05AvailableStratifiedHorizontalSecondTarget where
  toFun target :=
    (programPT05ExactT03RelativeBicomplex.dH 5 0 target.1,
      programPT05ExactT03RelativeBicomplex.dH 4 0 target.2)
  map_add' first second := by
    apply Prod.ext <;> simp
  map_smul' scalar target := by
    apply Prod.ext <;> simp

/-- The available graded operator inherits the genuine cellular square-zero
law.  This law does not realize the still-missing bulk-to-null density. -/
theorem programPT05AvailableStratifiedIntegratedDH_squared
    (source : ProgramPT05AvailableStratifiedHorizontalSource) :
    programPT05AvailableStratifiedIntegratedDHNext
        (programPT05AvailableStratifiedIntegratedDH source) = 0 := by
  apply Prod.ext
  · simpa [programPT05AvailableStratifiedIntegratedDH,
      programPT05AvailableStratifiedIntegratedDHNext] using
      (programPT05ExactT03RelativeBicomplex.dH_dH 4 0 source.1)
  · simpa [programPT05AvailableStratifiedIntegratedDH,
      programPT05AvailableStratifiedIntegratedDHNext] using
      (programPT05ExactT03RelativeBicomplex.dH_dH 3 0 source.2)

variable (period : Real) (hPeriod : period ≠ 0)

/-- Integrated source built from the actual cut-bulk current and every finite
null-face normalization transgression. -/
def programPT05CanonicalAvailableStratifiedHorizontalSource
    {NullFace : Type*} [Fintype NullFace]
    (field test : SmoothQuotientField period hPeriod Real)
    (faces : NullFace → FiniteNullFaceActionDatum) :
    ProgramPT05AvailableStratifiedHorizontalSource :=
  (programPT05CutBulkDensityIntegratedCochain period hPeriod
      (programPT05CanonicalCutBulkLocalDensityCochain period hPeriod
        field test),
    programPT05FiniteNullTransgressionSourceIntegratedCochain faces)

/-- The supplied geometric targets: the non-null boundary integral and the
complete finite-family joint integral. -/
def programPT05CanonicalAvailableStratifiedHorizontalTarget
    {NullFace : Type*} [Fintype NullFace]
    (field test : SmoothQuotientField period hPeriod Real)
    (faces : NullFace → FiniteNullFaceActionDatum) :
    ProgramPT05AvailableStratifiedHorizontalTarget :=
  (programPT05NonNullBoundaryDensityIntegratedCochain period hPeriod
      (programPT05CanonicalCutBulkLocalDensityCochain period hPeriod
        field test),
    programPT05FiniteNullTransgressionTargetIntegratedCochain faces)

/-- Integration commutes on both available geometric components.  The first
equality is deliberately projected to `nonNullBoundary`; the second is an
equality of the complete null-to-joint cochains. -/
theorem programPT05CanonicalAvailableStratifiedHorizontalIntegration_commutes
    {NullFace : Type*} [Fintype NullFace]
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (faces : NullFace → FiniteNullFaceActionDatum)
    (contracts : ∀ face, NullFaceIntervalIntegrability (faces face)) :
    let source := programPT05CanonicalAvailableStratifiedHorizontalSource
      period hPeriod field test faces
    let target := programPT05CanonicalAvailableStratifiedHorizontalTarget
      period hPeriod field test faces
    (programPT05AvailableStratifiedIntegratedDH source).1 .nonNullBoundary =
        target.1 .nonNullBoundary ∧
      (programPT05AvailableStratifiedIntegratedDH source).2 = target.2 := by
  dsimp only [programPT05CanonicalAvailableStratifiedHorizontalSource,
    programPT05CanonicalAvailableStratifiedHorizontalTarget,
    programPT05AvailableStratifiedIntegratedDH]
  constructor
  · exact programPT05CanonicalCutBulkLocalDensity_dH_nonNull
      period hPeriod massSquared field test
  · exact programPT05FiniteNullTransgressionIntegration_commutes_dH
      faces contracts

/-- The cellular differential on the canonical integrated source pair remains
square-zero.  The preceding theorem supplies the two geometric component
identities. -/
theorem programPT05CanonicalAvailableStratifiedHorizontalIntegration_squared
    {NullFace : Type*} [Fintype NullFace]
    (field test : SmoothQuotientField period hPeriod Real)
    (faces : NullFace → FiniteNullFaceActionDatum) :
    programPT05AvailableStratifiedIntegratedDHNext
        (programPT05AvailableStratifiedIntegratedDH
          (programPT05CanonicalAvailableStratifiedHorizontalSource
            period hPeriod field test faces)) = 0 := by
  exact programPT05AvailableStratifiedIntegratedDH_squared _

/-- Raw Gate-833 integration of the faithful geometric packet. -/
def programPT05T03RawGeometricDensityIntegratedCochain
    {NullFace : Type*} [Fintype NullFace]
    (couplings : GlobalCandidateAActionCouplings)
    (bulk : ProgramPT05BulkActionLocalDensityPacket period hPeriod couplings)
    (ghy : ProgramPT05GHYLocalDensityCochain period hPeriod)
    (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) :
    RelativeJetCochain ProgramPT05PhysicalJetComponent 4 0 :=
  programPT05GeometricDensityIntegrationMap period hPeriod couplings
    (programPT05GeometricStratifiedDensityCochainOfPackets period hPeriod
      couplings bulk ghy faithful input)

/-- Gate-833 integration after the actual finite null reparametrization from
Gate 835. -/
def programPT05T03ReparametrizedGeometricDensityIntegratedCochain
    {NullFace : Type*} [Fintype NullFace]
    (couplings : GlobalCandidateAActionCouplings)
    (bulk : ProgramPT05BulkActionLocalDensityPacket period hPeriod couplings)
    (ghy : ProgramPT05GHYLocalDensityCochain period hPeriod)
    (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) :
    RelativeJetCochain ProgramPT05PhysicalJetComponent 4 0 :=
  programPT05GeometricDensityIntegrationMap period hPeriod couplings
    (programPT05ReparametrizedGeometricStratifiedDensityCochainOfPackets
      period hPeriod couplings bulk ghy faithful input)

/-- Faithful T03 specialization of the two available integrated sources. -/
def programPT05T03AvailableStratifiedHorizontalSource
    {NullFace : Type*} [Fintype NullFace]
    (field test : SmoothQuotientField period hPeriod Real)
    (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) :
    ProgramPT05AvailableStratifiedHorizontalSource :=
  (programPT05CutBulkDensityIntegratedCochain period hPeriod
      (programPT05CanonicalCutBulkLocalDensityCochain period hPeriod
        field test),
    programPT05T03FaithfulNullTransgressionSourceIntegratedCochain
      faithful input)

/-- Faithful T03 specialization of the two supplied geometric targets. -/
def programPT05T03AvailableStratifiedHorizontalTarget
    {NullFace : Type*} [Fintype NullFace]
    (field test : SmoothQuotientField period hPeriod Real)
    (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace) :
    ProgramPT05AvailableStratifiedHorizontalTarget :=
  (programPT05NonNullBoundaryDensityIntegratedCochain period hPeriod
      (programPT05CanonicalCutBulkLocalDensityCochain period hPeriod
        field test),
    programPT05T03FaithfulNullTransgressionTargetIntegratedCochain
      faithful input)

/-- On faithful T03 data, the graded operator commutes with both supplied
geometric targets and with the first null/joint coordinates of the Gate-833
geometric integration packet. -/
theorem programPT05T03AvailableStratifiedHorizontalIntegration_commutes
    {NullFace : Type*} [Fintype NullFace]
    (massSquared : Real)
    (field test : SmoothQuotientField period hPeriod Real)
    (couplings : GlobalCandidateAActionCouplings)
    (bulk : ProgramPT05BulkActionLocalDensityPacket period hPeriod couplings)
    (ghy : ProgramPT05GHYLocalDensityCochain period hPeriod)
    (faithful : FiniteNullFaceMobileCanonicalFaithfulActionRealization NullFace)
    (input : FiniteNullFacePhysicalHilbert NullFace)
    (hInput : input ∈ faithful.realization.geometry.domain) :
    let source := programPT05T03AvailableStratifiedHorizontalSource
      period hPeriod field test faithful input
    let target := programPT05T03AvailableStratifiedHorizontalTarget
      period hPeriod field test faithful input
    let raw := programPT05T03RawGeometricDensityIntegratedCochain
      period hPeriod couplings bulk ghy faithful input
    let reparametrized :=
      programPT05T03ReparametrizedGeometricDensityIntegratedCochain
        period hPeriod couplings bulk ghy faithful input
    (programPT05AvailableStratifiedIntegratedDH source).1 .nonNullBoundary =
        target.1 .nonNullBoundary ∧
      (programPT05AvailableStratifiedIntegratedDH source).2 = target.2 ∧
      (reparametrized .nullBoundary).1 - (raw .nullBoundary).1 =
        (source.2 .nullBoundary).1 ∧
      ((reparametrized .joint).1 - (raw .joint).1, 0) =
        (programPT05AvailableStratifiedIntegratedDH source).2 .joint := by
  dsimp only [programPT05T03AvailableStratifiedHorizontalSource,
    programPT05T03AvailableStratifiedHorizontalTarget,
    programPT05T03RawGeometricDensityIntegratedCochain,
    programPT05T03ReparametrizedGeometricDensityIntegratedCochain,
    programPT05AvailableStratifiedIntegratedDH]
  constructor
  · exact programPT05CanonicalCutBulkLocalDensity_dH_nonNull
      period hPeriod massSquared field test
  constructor
  · exact programPT05T03FaithfulNullTransgressionIntegration_commutes_dH
      faithful input hInput
  constructor
  · exact
      programPT05ReparametrizedGeometricDensityIntegrationMap_null_difference_eq_source
        period hPeriod couplings bulk ghy faithful input hInput
  · exact
      programPT05ReparametrizedGeometricDensityIntegrationMap_joint_difference_eq_dH
        period hPeriod couplings bulk ghy faithful input hInput

end
end P0EFTJanusProgramPT05AvailableStratifiedHorizontalComplex4D
end JanusFormal
