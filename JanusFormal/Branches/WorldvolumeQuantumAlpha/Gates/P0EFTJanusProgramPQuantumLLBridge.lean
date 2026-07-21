import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalLLWorldvolume4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusPTSymmetricLLH1FredholmOperator4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusD8NonabelianGhostSmoothThroatBVMaster4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusShiftedSobolevPhysicalQuotient

namespace JanusFormal.P0EFTJanusProgramPQuantumLLBridge

set_option autoImplicit false

open scoped InnerProductSpace
open P0EFTJanusLatticeFourierSaintVenantExactness
open P0EFTJanusWeightedL2LatticeSaintVenantExactness
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusMappingTorusPTSymmetricLLH1FredholmOperator4D
open P0EFTJanusMappingTorusD8NonabelianGhostSmoothThroatBVMaster4D
open P0EFTJanusShiftedSobolevLatticeLorentzGram
open P0EFTJanusShiftedSobolevPullbackHessian
open P0EFTJanusShiftedSobolevPhysicalQuotient

noncomputable section

/-- Program P supplies an actual self-adjoint Fredholm realization with zero
kernel, full range and index zero on its Jacobi-energy Hilbert completion. -/
theorem program_p_energy_hilbert_ll_packet
    (period : ℝ) (hPeriod : period ≠ 0)
    (data : PositiveLLH1Data period hPeriod) :
    IsSelfAdjoint (completedLLJacobiOperator period hPeriod data) ∧
      LinearMap.ker
          (completedLLJacobiOperator period hPeriod data).toLinearMap = ⊥ ∧
      LinearMap.range
          (completedLLJacobiOperator period hPeriod data).toLinearMap = ⊤ ∧
      completedLLJacobiIndex period hPeriod data = 0 := by
  exact ⟨completedLLJacobiOperator_isSelfAdjoint period hPeriod data,
    completedLLJacobiOperator_ker_eq_bot period hPeriod data,
    completedLLJacobiOperator_range_eq_top period hPeriod data,
    completedLLJacobiIndex_zero period hPeriod data⟩

/-- Program P also supplies a smooth throat BV differential that is genuinely
square-zero. -/
theorem program_p_smooth_throat_bv_square_zero
    (period : ℝ) (hPeriod : period ≠ 0)
    (field : SmoothFiniteMetricBVField period hPeriod) :
    smoothThroatBVBRST period hPeriod
        (smoothThroatBVBRST period hPeriod field) = 0 :=
  smoothThroatBVBRST_square_zero period hPeriod field

/-- Program P already supplies a periodic shifted-Sobolev quotient with its
zero mode removed and a nondegenerate positive pullback Hessian. -/
theorem program_p_shifted_sobolev_quotient_packet
    (targetWeight : LatticeMode → Real) :
    Nonempty (PhysicalPotentialQuotient targetWeight ≃L[Real]
      ZeroFreePotentialSubspace targetWeight) ∧
    (∀ potential : ZeroFreePotentialSubspace targetWeight,
      ⟪shiftedPullbackHessian targetWeight potential.1, potential.1⟫_Real = 0 ↔
        potential = 0) := by
  rcases shifted_sobolev_physical_quotient_gate targetWeight with
    ⟨_, _, hEquivalence, hNondegenerate⟩
  exact ⟨hEquivalence, hNondegenerate⟩

structure ProgramPToAQuantumLLStatus where
  globalLLActionImported : Prop
  ptVariationImported : Prop
  hessianImported : Prop
  energyHilbertFredholmPacketImported : Prop
  smoothUltralocalBVMasterImported : Prop
  periodicShiftedSobolevQuotientImported : Prop
  physicalSobolevComparisonDerived : Prop
  compactResolventOrPrimedDeterminantDerived : Prop
  perturbativeGaugeFermionFixed : Prop
  llBetaAndAnomalousDimensionComputed : Prop

def programPBridgeAvailable (s : ProgramPToAQuantumLLStatus) : Prop :=
  s.globalLLActionImported ∧
  s.ptVariationImported ∧
  s.hessianImported ∧
  s.energyHilbertFredholmPacketImported ∧
  s.smoothUltralocalBVMasterImported ∧
  s.periodicShiftedSobolevQuotientImported

def physicalQuantumLLClosed (s : ProgramPToAQuantumLLStatus) : Prop :=
  programPBridgeAvailable s ∧
  s.physicalSobolevComparisonDerived ∧
  s.compactResolventOrPrimedDeterminantDerived ∧
  s.perturbativeGaugeFermionFixed ∧
  s.llBetaAndAnomalousDimensionComputed

/-- Status after importing every LL result currently supplied by Program P. -/
def importedProgramPStatus
    (physicalSobolevComparisonDerived
      compactResolventOrPrimedDeterminantDerived
      perturbativeGaugeFermionFixed
      llBetaAndAnomalousDimensionComputed : Prop) :
    ProgramPToAQuantumLLStatus where
  globalLLActionImported := True
  ptVariationImported := True
  hessianImported := True
  energyHilbertFredholmPacketImported := True
  smoothUltralocalBVMasterImported := True
  periodicShiftedSobolevQuotientImported := True
  physicalSobolevComparisonDerived := physicalSobolevComparisonDerived
  compactResolventOrPrimedDeterminantDerived :=
    compactResolventOrPrimedDeterminantDerived
  perturbativeGaugeFermionFixed := perturbativeGaugeFermionFixed
  llBetaAndAnomalousDimensionComputed := llBetaAndAnomalousDimensionComputed

theorem imported_program_p_bridge_available
    (physicalSobolevComparisonDerived
      compactResolventOrPrimedDeterminantDerived
      perturbativeGaugeFermionFixed
      llBetaAndAnomalousDimensionComputed : Prop) :
    programPBridgeAvailable
      (importedProgramPStatus physicalSobolevComparisonDerived
        compactResolventOrPrimedDeterminantDerived perturbativeGaugeFermionFixed
        llBetaAndAnomalousDimensionComputed) := by
  simp [programPBridgeAvailable, importedProgramPStatus]

/-- After the Program P import, no classical/Fredholm/BV premise remains:
quantum LL closure is exactly the four physical completion obligations. -/
theorem physical_quantum_ll_closed_iff_remaining_obligations
    (physicalSobolevComparisonDerived
      compactResolventOrPrimedDeterminantDerived
      perturbativeGaugeFermionFixed
      llBetaAndAnomalousDimensionComputed : Prop) :
    physicalQuantumLLClosed
        (importedProgramPStatus physicalSobolevComparisonDerived
          compactResolventOrPrimedDeterminantDerived perturbativeGaugeFermionFixed
          llBetaAndAnomalousDimensionComputed) ↔
      physicalSobolevComparisonDerived ∧
      compactResolventOrPrimedDeterminantDerived ∧
      perturbativeGaugeFermionFixed ∧
      llBetaAndAnomalousDimensionComputed := by
  simp [physicalQuantumLLClosed, programPBridgeAvailable, importedProgramPStatus]

end

end JanusFormal.P0EFTJanusProgramPQuantumLLBridge
