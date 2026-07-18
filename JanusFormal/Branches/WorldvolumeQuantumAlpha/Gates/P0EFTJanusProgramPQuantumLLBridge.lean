import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalLLWorldvolume4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusPTSymmetricLLH1FredholmOperator4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusD8NonabelianGhostSmoothThroatBVMaster4D

namespace JanusFormal.P0EFTJanusProgramPQuantumLLBridge

set_option autoImplicit false

open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusMappingTorusPTSymmetricLLH1FredholmOperator4D
open P0EFTJanusMappingTorusD8NonabelianGhostSmoothThroatBVMaster4D

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

structure ProgramPToAQuantumLLStatus where
  globalLLActionImported : Prop
  ptVariationImported : Prop
  hessianImported : Prop
  energyHilbertFredholmPacketImported : Prop
  smoothUltralocalBVMasterImported : Prop
  physicalSobolevComparisonDerived : Prop
  compactResolventOrPrimedDeterminantDerived : Prop
  perturbativeGaugeFermionFixed : Prop
  llBetaAndAnomalousDimensionComputed : Prop

def programPBridgeAvailable (s : ProgramPToAQuantumLLStatus) : Prop :=
  s.globalLLActionImported ∧
  s.ptVariationImported ∧
  s.hessianImported ∧
  s.energyHilbertFredholmPacketImported ∧
  s.smoothUltralocalBVMasterImported

def physicalQuantumLLClosed (s : ProgramPToAQuantumLLStatus) : Prop :=
  programPBridgeAvailable s ∧
  s.physicalSobolevComparisonDerived ∧
  s.compactResolventOrPrimedDeterminantDerived ∧
  s.perturbativeGaugeFermionFixed ∧
  s.llBetaAndAnomalousDimensionComputed

end

end JanusFormal.P0EFTJanusProgramPQuantumLLBridge
