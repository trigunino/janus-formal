import Mathlib.Analysis.Normed.Operator.Prod
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalPhysicalLLHessianHeatRegulator4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusTemporalGhostContinuumHeatRegulator4D

/-!
# Common heat time for the physical LL and temporal ghost blocks

This gate places the existing bounded physical spectral--LL heat operator and
the compact nuclear temporal-ghost heat operator in one `WithLp 2` Hilbert
sum at the same positive time.

No compactness or trace-class claim is made for the full sum: the LL identity
heat block and the current D9 data do not yet provide it.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPPhysicalLLTemporalGhostHeatRegulator4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusMappingTorusInfiniteTemporalFourierSobolevBridge4D
open P0EFTJanusMappingTorusInfiniteTemporalH1ZeroModeCohomology4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusMappingTorusTemporalGhostContinuumHeatRegulator4D
open P0EFTJanusProgramPGlobalPhysicalLLHessianFredholm4D
open P0EFTJanusProgramPGlobalPhysicalLLHessianHeatRegulator4D

open scoped ENNReal lp

variable (period : Real) [hPeriodPos : Fact (0 < period)]

/-- Hilbert sum of the assembled physical spectral--LL sector and the
completed spatially constant temporal ghost. -/
abbrev ProgramPPhysicalLLTemporalGhostHeatHilbert
    (ι : Type*)
    (spectralData : ProductThroatSpectralData)
    (llData : PositiveLLH1Data period hPeriodPos.out.ne') :=
  WithLp 2
    (ProgramPGlobalPhysicalLLHessianHilbert
        period hPeriodPos.out.ne' ι spectralData llData ×
      TemporalH1CoefficientHilbert period)

/-- One common positive heat time on the assembled physical--ghost partial
Hilbert space. -/
def programPPhysicalLLTemporalGhostHeatOperator
    {ι : Type*}
    (covector : ι → TangentVector3)
    (spectralData : ProductThroatSpectralData)
    (matterMass : Real)
    (llData : PositiveLLH1Data period hPeriodPos.out.ne')
    (time : HeatTime) :
    ProgramPPhysicalLLTemporalGhostHeatHilbert
        period ι spectralData llData →L[Real]
      ProgramPPhysicalLLTemporalGhostHeatHilbert
        period ι spectralData llData :=
  (WithLp.prodContinuousLinearEquiv 2 Real
      (ProgramPGlobalPhysicalLLHessianHilbert
        period hPeriodPos.out.ne' ι spectralData llData)
      (TemporalH1CoefficientHilbert period)).symm.toContinuousLinearMap ∘L
    ((programPGlobalPhysicalLLCommonHeatOperator
        period hPeriodPos.out.ne' covector spectralData matterMass llData time
      ).prodMap
      ((temporalGhostHeatOperator period time).restrictScalars Real)) ∘L
    (WithLp.prodContinuousLinearEquiv 2 Real
      (ProgramPGlobalPhysicalLLHessianHilbert
        period hPeriodPos.out.ne' ι spectralData llData)
      (TemporalH1CoefficientHilbert period)).toContinuousLinearMap

@[simp]
theorem programPPhysicalLLTemporalGhostHeatOperator_apply
    {ι : Type*}
    (covector : ι → TangentVector3)
    (spectralData : ProductThroatSpectralData)
    (matterMass : Real)
    (llData : PositiveLLH1Data period hPeriodPos.out.ne')
    (time : HeatTime)
    (state : ProgramPPhysicalLLTemporalGhostHeatHilbert
      period ι spectralData llData) :
    WithLp.ofLp
      (programPPhysicalLLTemporalGhostHeatOperator
        period covector spectralData matterMass llData time state) =
      (programPGlobalPhysicalLLCommonHeatOperator
          period hPeriodPos.out.ne' covector spectralData matterMass llData time
          (WithLp.ofLp state).1,
        temporalGhostHeatOperator period time (WithLp.ofLp state).2) :=
  rfl

/-- Exact common-time certificate for the currently assembled physical and
temporal-ghost sectors. -/
structure ProgramPPhysicalLLTemporalGhostHeatRegulatorCertificate4D
    {ι : Type*}
    (covector : ι → TangentVector3)
    (spectralData : ProductThroatSpectralData)
    (matterMass : Real)
    (llData : PositiveLLH1Data period hPeriodPos.out.ne')
    (time : HeatTime) : Prop where
  common_operator :
    Nonempty
      (ProgramPPhysicalLLTemporalGhostHeatHilbert
          period ι spectralData llData →L[Real]
        ProgramPPhysicalLLTemporalGhostHeatHilbert
          period ι spectralData llData)
  temporal_ghost :
    TemporalGhostContinuumHeatRegulatorCertificate4D period time

def programPPhysicalLLTemporalGhostHeatRegulatorCertificate4D
    {ι : Type*}
    (covector : ι → TangentVector3)
    (spectralData : ProductThroatSpectralData)
    (matterMass : Real)
    (llData : PositiveLLH1Data period hPeriodPos.out.ne')
    (time : HeatTime) :
    ProgramPPhysicalLLTemporalGhostHeatRegulatorCertificate4D
      period covector spectralData matterMass llData time where
  common_operator :=
    ⟨programPPhysicalLLTemporalGhostHeatOperator
      period covector spectralData matterMass llData time⟩
  temporal_ghost :=
    temporalGhostContinuumHeatRegulatorCertificate4D period time

end

end P0EFTJanusProgramPPhysicalLLTemporalGhostHeatRegulator4D
end JanusFormal
