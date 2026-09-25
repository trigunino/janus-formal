import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBoundaryDiffeomorphismAntighostCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBulkAntighostHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicBoundaryCompleteAction4D

/-! The genuine shared smooth antighost is a null column of the complete
bulk + GHY Hessian under the explicit opposite-Einstein-weight equation. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicBoundaryAntighostHessian4D
set_option autoImplicit false
noncomputable section

private theorem scalar_sum_zero {total bulk plus minus : Real}
    (hTotal : total = bulk + plus + minus) (hBulk : bulk = 0)
    (hPlus : plus = 0) (hMinus : minus = 0) : total = 0 := by
  rw [hTotal, hBulk, hPlus, hMinus, zero_add, zero_add]
open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusProgramPT12IntrinsicBoundaryBulkHessian4D

private theorem secondDerivative_linear_zero_left
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    (action : F → Real) (projection : E →L[Real] F)
    (hC2 : ContDiffAt Real 2 action 0) (first second : E) (hFirst : projection first = 0) :
    scalarActionSecondDerivative (fun point => action (projection point)) first second = 0 := by
  rw [scalarActionSecondDerivative_linear_pullback action projection hC2 first second,
    hFirst, (scalarActionSecondDerivative action).map_zero, zero_apply]

open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusProgramPGlobalCovariantAction4D P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPCandidateADiagonalDiffeomorphismKineticAdjointBridge4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPT12IntrinsicBulkGeometry4D P0EFTJanusProgramPT12IntrinsicBulkActionCore4D
open P0EFTJanusProgramPT12IntrinsicBulkAntighostHessian4D
open P0EFTJanusProgramPT12IntrinsicBoundaryBulkCore4D
open P0EFTJanusProgramPT12IntrinsicBoundaryCompleteAction4D
open P0EFTJanusProgramPT12IntrinsicBoundaryDiffeomorphismAntighostCore4D
open P0EFTJanusReciprocalBimetricPotential

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev Q := MappingTorus (reflectedSphereData period hPeriod)
private abbrev Throat := MappingTorus (fixedEquatorData period hPeriod)
local instance : ChartedSpace CoverModel (Q period hPeriod) := reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (Q period hPeriod) := reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (Q period hPeriod) := reflectedSphereQuotientCompactSpace period hPeriod
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
local notation "Bulk" => IntrinsicBulkCore period hPeriod couplings
local notation "Core" => IntrinsicBoundaryBulkCore period hPeriod couplings
local instance : NormedAddCommGroup Bulk := inferInstance
local instance : NormedSpace Real Bulk :=
  P0EFTJanusFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLAction4D.instNormedSpaceRealFiniteFramePairedC2PhysicalMaxwellSpinCMatterLLCore
    period hPeriod (intrinsicBulkGeometry period hPeriod) (finiteSmoothTangentFrame period hPeriod) couplings
local instance coreNormedAddCommGroup : NormedAddCommGroup Core :=
  intrinsicBoundaryBulkCoreNormedAddCommGroup period hPeriod couplings
local instance : SeminormedAddCommGroup Core :=
  (coreNormedAddCommGroup period hPeriod couplings).toSeminormedAddCommGroup
local instance : AddCommGroup Core := (coreNormedAddCommGroup period hPeriod couplings).toAddCommGroup
local instance : NormedSpace Real Core := intrinsicBoundaryBulkCoreNormedSpace period hPeriod couplings
local instance : NormedAddCommGroup (Core →L[Real] Real) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace Real (Core →L[Real] Real) := ContinuousLinearMap.toNormedSpace

theorem intrinsicBoundaryPlusGHYHessian_antighost_zero (einsteinScale : Real)
    (antighost : GlobalDiffeomorphismAntighostField period hPeriod) (test : Core) :
    scalarActionSecondDerivative (intrinsicBoundaryPlusGHYAction period hPeriod couplings einsteinScale)
      (intrinsicBoundarySmoothAntighostInsertion period hPeriod couplings antighost) test = 0 :=
  secondDerivative_linear_zero_left (intrinsicBoundaryFixedGHYAction period hPeriod einsteinScale)
    (intrinsicBoundaryBulkPlusJoint period hPeriod couplings)
    (intrinsicBoundaryFixedGHYAction_contDiffAt_zero period hPeriod einsteinScale) _ test
    (intrinsicBoundarySmoothAntighostInsertion_plusJoint period hPeriod couplings antighost)

theorem intrinsicBoundaryMinusGHYHessian_antighost_zero (einsteinScale : Real)
    (antighost : GlobalDiffeomorphismAntighostField period hPeriod) (test : Core) :
    scalarActionSecondDerivative (intrinsicBoundaryMinusGHYAction period hPeriod couplings einsteinScale)
      (intrinsicBoundarySmoothAntighostInsertion period hPeriod couplings antighost) test = 0 :=
  secondDerivative_linear_zero_left (intrinsicBoundaryFixedGHYAction period hPeriod einsteinScale)
    (intrinsicBoundaryBulkMinusJoint period hPeriod couplings)
    (intrinsicBoundaryFixedGHYAction_contDiffAt_zero period hPeriod einsteinScale) _ test
    (intrinsicBoundarySmoothAntighostInsertion_minusJoint period hPeriod couplings antighost)

theorem intrinsicBoundaryBulkHessian_antighost_column_zero
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (hWeights : candidateAPlusEinsteinKineticWeight couplings + candidateAMinusEinsteinKineticWeight couplings = 0)
    (antighost : GlobalDiffeomorphismAntighostField period hPeriod) (test : Core) :
    intrinsicBoundaryBulkHessian period hPeriod couplings interactionScale coefficients
      (intrinsicBoundarySmoothAntighostInsertion period hPeriod couplings antighost) test = 0 := by
  have hPullback := intrinsicBoundaryBulkAction_hessian period hPeriod couplings interactionScale coefficients
    (intrinsicBoundarySmoothAntighostInsertion period hPeriod couplings antighost) test
  have hBulk := intrinsicBulkHessian_smoothAntighost_column_zero period hPeriod couplings
    interactionScale coefficients hWeights antighost (intrinsicBoundaryBulkProjection period hPeriod couplings test)
  exact hPullback.trans hBulk

theorem intrinsicBoundaryCompleteHessian_antighost_column_zero
    (plusEinsteinScale minusEinsteinScale interactionScale : Real) (coefficients : PotentialCoefficients)
    (hWeights : candidateAPlusEinsteinKineticWeight couplings + candidateAMinusEinsteinKineticWeight couplings = 0)
    (antighost : GlobalDiffeomorphismAntighostField period hPeriod) (test : Core) :
    intrinsicBoundaryCompleteHessian period hPeriod couplings
      plusEinsteinScale minusEinsteinScale interactionScale coefficients
      (intrinsicBoundarySmoothAntighostInsertion period hPeriod couplings antighost) test = 0 := by
  have hSum := intrinsicBoundaryCompleteHessian_apply period hPeriod couplings
    plusEinsteinScale minusEinsteinScale interactionScale coefficients
    (intrinsicBoundarySmoothAntighostInsertion period hPeriod couplings antighost) test
  have hBulk := intrinsicBoundaryBulkHessian_antighost_column_zero period hPeriod couplings
    interactionScale coefficients hWeights antighost test
  have hPlus := intrinsicBoundaryPlusGHYHessian_antighost_zero period hPeriod couplings
    plusEinsteinScale antighost test
  have hMinus := intrinsicBoundaryMinusGHYHessian_antighost_zero period hPeriod couplings
    minusEinsteinScale antighost test
  have h := scalar_sum_zero hSum hBulk hPlus hMinus
  exact h

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicBoundaryAntighostHessian4D
