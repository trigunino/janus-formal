import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusD9D10ExactFieldContentBridge4D

/-!
# Common finite-mode physical/ghost heat regulator

This gate records multiplicity and statistics signs for finite spectra while
using one literal heat time for every sector in a finite list.  It also
instantiates the construction on the truncated D10 spectrum and preserves the
exact PT-paired chiral cancellation.

The result is finite-mode only.  It supplies neither a global Janus operator
nor a common continuum domain or cutoff limit.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteModeCommonPhysicalGhostHeatRegulator4D

open P0EFTJanusFiniteModeHeatKernelAnomalyRegulator
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusGlobalSeparatedDiracModel

set_option autoImplicit false

noncomputable section

/-- Statistics labels used only to attach their standard heat-trace signs. -/
inductive FieldStatistics where
  | bosonic
  | fermionic
  | ghost
  deriving DecidableEq

/-- Bosons contribute positively; fermions and ghosts negatively. -/
def statisticsSign : FieldStatistics → ℝ
  | .bosonic => 1
  | .fermionic => -1
  | .ghost => -1

/-- Finite multiplicity and statistics attached to one finite spectrum. -/
structure WeightedSector (Mode : Type*) where
  multiplicity : ℕ
  statistics : FieldStatistics
  spectrum : FiniteChiralSpectrum Mode

/-- Signed even trace of one sector at the supplied common heat time. -/
def signedMultiplicityHeatTrace
    {Mode : Type*} [Fintype Mode]
    (regulatorTime : RegulatorTime) (sector : WeightedSector Mode) : ℝ :=
  statisticsSign sector.statistics * (sector.multiplicity : ℝ) *
    regulatedEvenHeatTrace regulatorTime sector.spectrum

/-- A finite collection of sectors is regulated at one literal heat time. -/
def commonFiniteHeatTrace
    {Mode : Type*} [Fintype Mode]
    (regulatorTime : RegulatorTime) (sectors : List (WeightedSector Mode)) : ℝ :=
  (sectors.map (signedMultiplicityHeatTrace regulatorTime)).sum

@[simp] theorem commonFiniteHeatTrace_nil
    {Mode : Type*} [Fintype Mode] (regulatorTime : RegulatorTime) :
    commonFiniteHeatTrace (Mode := Mode) regulatorTime [] = 0 := rfl

@[simp] theorem commonFiniteHeatTrace_cons
    {Mode : Type*} [Fintype Mode]
    (regulatorTime : RegulatorTime)
    (sector : WeightedSector Mode) (sectors : List (WeightedSector Mode)) :
    commonFiniteHeatTrace regulatorTime (sector :: sectors) =
      signedMultiplicityHeatTrace regulatorTime sector +
        commonFiniteHeatTrace regulatorTime sectors := rfl

/-- Multiplicities add exactly for two copies with common statistics and spectrum. -/
theorem signedMultiplicityHeatTrace_add
    {Mode : Type*} [Fintype Mode]
    (regulatorTime : RegulatorTime)
    (statistics : FieldStatistics) (spectrum : FiniteChiralSpectrum Mode)
    (first second : ℕ) :
    signedMultiplicityHeatTrace regulatorTime
        ⟨first + second, statistics, spectrum⟩ =
      signedMultiplicityHeatTrace regulatorTime ⟨first, statistics, spectrum⟩ +
        signedMultiplicityHeatTrace regulatorTime ⟨second, statistics, spectrum⟩ := by
  simp [signedMultiplicityHeatTrace, Nat.cast_add]
  ring

/-- Signed, multiplicity-weighted PT-paired chiral trace. -/
def signedPairedChiralTrace
    {Mode : Type*} [Fintype Mode]
    (regulatorTime : RegulatorTime) (sector : WeightedSector Mode) : ℝ :=
  statisticsSign sector.statistics * (sector.multiplicity : ℝ) *
    pairedRegulatedChiralTrace regulatorTime sector.spectrum

/-- PT cancellation is unaffected by either multiplicity or statistics sign. -/
theorem signedPairedChiralTrace_eq_zero
    {Mode : Type*} [Fintype Mode]
    (regulatorTime : RegulatorTime) (sector : WeightedSector Mode) :
    signedPairedChiralTrace regulatorTime sector = 0 := by
  rw [signedPairedChiralTrace, pairedRegulatedChiralTrace_eq_zero]
  ring

/-- The literal truncated D10 modes obey the same signed cancellation. -/
theorem truncated_d10_signed_chiral_trace_cancels
    (data : ProductThroatSpectralData)
    (chirality : RootChiralityAssignment)
    (sphereCutoff circleCutoff multiplicity : ℕ)
    (statistics : FieldStatistics)
    (regulatorTime : RegulatorTime) :
    signedPairedChiralTrace regulatorTime
        (⟨multiplicity, statistics,
          d10RegulatorSpectrum data chirality sphereCutoff circleCutoff⟩ :
          WeightedSector (TruncatedD10Mode data sphereCutoff circleCutoff)) = 0 := by
  exact signedPairedChiralTrace_eq_zero regulatorTime _

end

end P0EFTJanusFiniteModeCommonPhysicalGhostHeatRegulator4D
end JanusFormal
