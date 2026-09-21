import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12D9GaugeGhostWeylHeat4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLFriedrichsWeylHeat4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSpinCMatterContinuumHeatRegulator4D

/-!
# T12 reference D11 block nuclear heat

The D9, SpinC matter and reduced LL Friedrichs blocks already have explicit
nuclear positive-time heat expansions.  This file places those three exact
certificates at one heat time in a single reference-D11 packet.

The packet is deliberately blockwise.  It does not identify a heat functional
calculus for the compactly perturbed physical operator; that requires a
separate Schatten/Duhamel perturbation theorem.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12GaugeFixedLLFriedrichsD11BlockNuclearHeat4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusD9GaugeGhostContinuumHeatRegulator4D
open P0EFTJanusGaugeGhostBlockD9UnboundedFredholm4D
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPLL2EllipticNuclearHeatRegulator4D
open P0EFTJanusProgramPSpinCMatterContinuumHeatRegulator4D
open P0EFTJanusProgramPT12D9GaugeGhostWeylHeat4D
open P0EFTJanusProgramPT12LLFriedrichsWeylHeat4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- The three exact nuclear heat blocks of the unperturbed D11 reference
realization, all evaluated at the same positive time. -/
structure ReferenceD11BlockNuclearHeatCertificate4D
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Spectral : D9GaugeGhostInverseSquareData4D covector)
    {LLMode : Type*} [DecidableEq LLMode]
    (llSpectral : CanonicalLLFriedrichsInverseSquareData
      period hPeriod analysis LLMode)
    (matterMass : Real)
    (time : HeatTime) where
  d9 : D9GaugeGhostHeatNuclearCertificate4D covector time
  matter : ProgramPSpinCMatterHeatNuclearCertificate4D
    period hPeriod matterMass time
  ll : ProgramPLL2HeatNuclearCertificate period hPeriod
    (llSpectral.toProgramPLL2EllipticHeatData period hPeriod) time

/-- Canonical reference-D11 block packet from the two inverse-square inputs;
the SpinC matter block is already nuclear unconditionally. -/
def referenceD11BlockNuclearHeatCertificate4D
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Spectral : D9GaugeGhostInverseSquareData4D covector)
    {LLMode : Type*} [DecidableEq LLMode]
    (llSpectral : CanonicalLLFriedrichsInverseSquareData
      period hPeriod analysis LLMode)
    (matterMass : Real)
    (time : HeatTime) :
    ReferenceD11BlockNuclearHeatCertificate4D period hPeriod analysis
      d9Spectral llSpectral matterMass time where
  d9 := d9Spectral.toHeatNuclearCertificate time
  matter := programPSpinCMatterHeatNuclearCertificate4D
    period hPeriod matterMass time
  ll := programPLL2HeatNuclearCertificate period hPeriod
    (llSpectral.toProgramPLL2EllipticHeatData period hPeriod) time

/-- Each operator in the reference-D11 packet is compact. -/
theorem referenceD11BlockNuclearHeat_compact
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Spectral : D9GaugeGhostInverseSquareData4D covector)
    {LLMode : Type*} [DecidableEq LLMode]
    (llSpectral : CanonicalLLFriedrichsInverseSquareData
      period hPeriod analysis LLMode)
    (matterMass : Real)
    (time : HeatTime) :
    IsCompactOperator (d9GaugeGhostHeatOperator covector time) ∧
      IsCompactOperator
        (programPSpinCMatterHeatOperator period hPeriod matterMass time) ∧
      IsCompactOperator
        (programPLL2HeatOperator period hPeriod
          (llSpectral.toProgramPLL2EllipticHeatData period hPeriod) time) := by
  exact ⟨(d9Spectral.toHeatNuclearCertificate time).operator_compact,
    (programPSpinCMatterHeatNuclearCertificate4D
      period hPeriod matterMass time).operator_compact,
    programPLL2HeatOperator_isCompact period hPeriod
      (llSpectral.toProgramPLL2EllipticHeatData period hPeriod) time⟩

/-- Public reference-D11 block nuclear heat checkpoint. -/
theorem referenceD11BlockNuclearHeat_gate
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    {iota : Type*} [DecidableEq iota]
    {covector : iota → TangentVector3}
    (d9Spectral : D9GaugeGhostInverseSquareData4D covector)
    {LLMode : Type*} [DecidableEq LLMode]
    (llSpectral : CanonicalLLFriedrichsInverseSquareData
      period hPeriod analysis LLMode)
    (matterMass : Real)
    (time : HeatTime) :
    Nonempty
      (ReferenceD11BlockNuclearHeatCertificate4D period hPeriod analysis
        d9Spectral llSpectral matterMass time) :=
  ⟨referenceD11BlockNuclearHeatCertificate4D period hPeriod analysis
    d9Spectral llSpectral matterMass time⟩

end
end P0EFTJanusProgramPT12GaugeFixedLLFriedrichsD11BlockNuclearHeat4D
end JanusFormal
