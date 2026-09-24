import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBulkDiagonalGhostInfiniteKernel4D

/-! A realization preserving the bulk pairing on dense tests cannot have finite
kernel while retaining all smooth ghosts. Its domain may be a partial operator's
domain. No concrete H11, boundary realization, or quotient is asserted here. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkGhostRealizationObstruction4D
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPCandidateADiagonalDiffeomorphismKineticAdjointBridge4D
open P0EFTJanusProgramPT12IntrinsicBulkGeometry4D P0EFTJanusProgramPT12IntrinsicBulkActionCore4D
open P0EFTJanusProgramPT12IntrinsicBulkHessian4D
open P0EFTJanusProgramPT12IntrinsicBulkDiagonalGhostKernel4D
open P0EFTJanusProgramPT12SmoothGhostInfiniteDimension4D
open P0EFTJanusReciprocalBimetricPotential
attribute [local instance 2000]
  NonUnitalNormedRing.toNormedAddCommGroup NormedAlgebra.toNormedSpace

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev Q := MappingTorus (reflectedSphereData period hPeriod)
private abbrev Throat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace CoverModel (Q period hPeriod) := reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (Q period hPeriod) := reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (Q period hPeriod) := reflectedSphereQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (Q period hPeriod) := borel _
local instance : BorelSpace (Q period hPeriod) where measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
local instance : ChartedSpace ThroatCoverModel (Throat period hPeriod) := fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (Throat period hPeriod) := fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (Throat period hPeriod) := fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (Throat period hPeriod) := borel _
local instance : BorelSpace (Throat period hPeriod) where measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod
local instance : NormedAddCommGroup (CanonicalPhysicalScalarC2JetCore period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (CanonicalPhysicalScalarC2JetCore period hPeriod) := inferInstance
local instance : CompleteSpace (CanonicalPhysicalScalarC2JetCore period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod
local instance : InnerProductSpace Real ProgramPPrimitiveSpinCMatterHilbert := InnerProductSpace.complexToReal

variable (couplings : GlobalCandidateAActionCouplings)
local notation "Core" => IntrinsicBulkCore period hPeriod couplings
local instance coreNormedAddCommGroup : NormedAddCommGroup Core := inferInstance
local instance : NormedSpace Real Core :=
  P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D.instNormedSpaceRealFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCore
    period hPeriod (intrinsicBulkGeometry period hPeriod) (finiteSmoothTangentFrame period hPeriod) couplings
local instance : AddZeroClass Core :=
  (coreNormedAddCommGroup period hPeriod couplings).toAddCommGroup.toAddZeroClass
variable (interactionScale : Real) (coefficients : PotentialCoefficients)
variable (hWeights : candidateAPlusEinsteinKineticWeight couplings +
  candidateAMinusEinsteinKineticWeight couplings = 0)
variable {Domain Ambient : Type*} [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
variable (operator : Domain →ₗ[Real] Ambient)
  (lift : IntrinsicBulkCore period hPeriod couplings →ₗ[Real] Domain)
  (testEmbedding : IntrinsicBulkCore period hPeriod couplings →ₗ[Real] Ambient)
  (hDense : DenseRange testEmbedding)
  (hPairing : ∀ first second : IntrinsicBulkCore period hPeriod couplings,
    ⟪operator (lift first), testEmbedding second⟫_ℝ =
    intrinsicBulkHessian period hPeriod couplings interactionScale coefficients first second)

include hWeights hDense hPairing in
theorem intrinsicBulkGhost_faithfulRealization_zero
    (ghost : GlobalDiffeomorphismGhostField period hPeriod) :
    operator (lift (intrinsicBulkSmoothDiffeomorphismGhostInsertion period hPeriod couplings ghost)) = 0 := by
  let output : Ambient :=
    operator (lift (intrinsicBulkSmoothDiffeomorphismGhostInsertion period hPeriod couplings ghost))
  have hContinuous : Continuous (fun test : Ambient => inner Real output test) :=
    continuous_const.inner continuous_id
  have hClosed : IsClosed {test : Ambient | inner Real output test = 0} :=
    isClosed_eq hContinuous continuous_const
  have hRange : Set.range testEmbedding ⊆ {test : Ambient | inner Real output test = 0} := by
    rintro _ ⟨test, rfl⟩
    exact (hPairing (intrinsicBulkSmoothDiffeomorphismGhostInsertion period hPeriod couplings ghost) test).trans
      (intrinsicBulkHessian_smoothDiagonalGhost_column_zero period hPeriod couplings
        interactionScale coefficients hWeights ghost test)
  have hVanish : closure (Set.range testEmbedding) ⊆
      {test : Ambient | inner Real output test = 0} := closure_minimal hRange hClosed
  have hSelf : inner Real output output = 0 := hVanish (hDense output)
  exact inner_self_eq_zero.mp hSelf

variable [Fact (0 < period)]

include hWeights hDense hPairing in
theorem intrinsicBulkGhost_faithfulRealization_kernel_not_finiteDimensional
    (hFaithful : Function.Injective
      (lift.comp (intrinsicBulkSmoothDiffeomorphismGhostInsertion period hPeriod couplings))) :
    ¬ FiniteDimensional Real (LinearMap.ker operator) := by
  intro hFinite
  letI := hFinite
  let ghostLift := lift.comp (intrinsicBulkSmoothDiffeomorphismGhostInsertion period hPeriod couplings)
  let inclusion := ghostLift.codRestrict (LinearMap.ker operator) (by
    intro ghost
    exact intrinsicBulkGhost_faithfulRealization_zero period hPeriod couplings interactionScale coefficients
      hWeights operator lift testEmbedding hDense hPairing ghost)
  have hInjective : Function.Injective inclusion := by
    intro first second hEqual
    exact hFaithful (congrArg Subtype.val hEqual)
  exact smoothDiffeomorphismGhost_not_finiteDimensional period hPeriod
    (FiniteDimensional.of_injective inclusion hInjective)

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicBulkGhostRealizationObstruction4D
