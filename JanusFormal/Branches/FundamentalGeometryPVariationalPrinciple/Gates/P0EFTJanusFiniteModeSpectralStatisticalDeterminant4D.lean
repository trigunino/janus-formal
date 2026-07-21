import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteModeStatisticalDeterminant4D

/-!
# Spectrum-dependent finite statistical determinant

Unlike the cutoff-holonomy determinant, this finite product reads the actual
`eigenvalueSq` field of each supplied finite spectrum.  A strictly positive
shift keeps every factor nonzero.  No cutoff limit or global determinant is
asserted.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteModeSpectralStatisticalDeterminant4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusFiniteModeHeatKernelAnomalyRegulator
open P0EFTJanusFiniteModeCommonPhysicalGhostHeatRegulator4D

/-- Strictly positive spectral shift. -/
abbrev PositiveSpectralShift := {shift : Real // 0 < shift}

/-- Genuine finite product of the shifted squared eigenvalues. -/
def finiteSpectrumDeterminant
    {Mode : Type*} [Fintype Mode]
    (shift : PositiveSpectralShift)
    (spectrum : FiniteChiralSpectrum Mode) : Real :=
  ∏ mode, (shift.1 + spectrum.eigenvalueSq mode)

theorem finiteSpectrumDeterminant_pos
    {Mode : Type*} [Fintype Mode]
    (shift : PositiveSpectralShift)
    (spectrum : FiniteChiralSpectrum Mode) :
    0 < finiteSpectrumDeterminant shift spectrum := by
  unfold finiteSpectrumDeterminant
  exact Finset.prod_pos fun mode _ =>
    add_pos_of_pos_of_nonneg shift.2 (spectrum.eigenvalueSq_nonnegative mode)

theorem finiteSpectrumDeterminant_ext
    {Mode : Type*} [Fintype Mode]
    (shift : PositiveSpectralShift)
    (first second : FiniteChiralSpectrum Mode)
    (hSpectrum : ∀ mode, first.eigenvalueSq mode = second.eigenvalueSq mode) :
    finiteSpectrumDeterminant shift first =
      finiteSpectrumDeterminant shift second := by
  unfold finiteSpectrumDeterminant
  apply Finset.prod_congr rfl
  intro mode _
  rw [hSpectrum mode]

/-- Multiplicity and statistics applied to the actual spectral product. -/
def spectralStatisticalDeterminant
    {Mode : Type*} [Fintype Mode]
    (shift : PositiveSpectralShift) (sector : WeightedSector Mode) : Real :=
  match sector.statistics with
  | .bosonic => (finiteSpectrumDeterminant shift sector.spectrum) ^
      sector.multiplicity
  | .fermionic => ((finiteSpectrumDeterminant shift sector.spectrum) ^
      sector.multiplicity)⁻¹
  | .ghost => ((finiteSpectrumDeterminant shift sector.spectrum) ^
      sector.multiplicity)⁻¹

theorem spectralStatisticalDeterminant_ne_zero
    {Mode : Type*} [Fintype Mode]
    (shift : PositiveSpectralShift) (sector : WeightedSector Mode) :
    spectralStatisticalDeterminant shift sector ≠ 0 := by
  have hBase : finiteSpectrumDeterminant shift sector.spectrum ≠ 0 :=
    ne_of_gt (finiteSpectrumDeterminant_pos shift sector.spectrum)
  rcases sector with ⟨multiplicity, statistics, spectrum⟩
  cases statistics <;>
    simp [spectralStatisticalDeterminant, hBase]

theorem spectralStatisticalDeterminant_add_multiplicity
    {Mode : Type*} [Fintype Mode]
    (shift : PositiveSpectralShift) (statistics : FieldStatistics)
    (spectrum : FiniteChiralSpectrum Mode) (first second : Nat) :
    spectralStatisticalDeterminant shift
        ⟨first + second, statistics, spectrum⟩ =
      spectralStatisticalDeterminant shift ⟨first, statistics, spectrum⟩ *
        spectralStatisticalDeterminant shift
          ⟨second, statistics, spectrum⟩ := by
  cases statistics <;>
    simp [spectralStatisticalDeterminant, pow_add, mul_comm]

/-- Product of a finite list of sectors sharing one mode type and shift. -/
def finiteSectorListDeterminant
    {Mode : Type*} [Fintype Mode]
    (shift : PositiveSpectralShift) (sectors : List (WeightedSector Mode)) : Real :=
  (sectors.map (spectralStatisticalDeterminant shift)).prod

@[simp] theorem finiteSectorListDeterminant_append
    {Mode : Type*} [Fintype Mode]
    (shift : PositiveSpectralShift)
    (first second : List (WeightedSector Mode)) :
    finiteSectorListDeterminant shift (first ++ second) =
      finiteSectorListDeterminant shift first *
        finiteSectorListDeterminant shift second := by
  simp [finiteSectorListDeterminant]

/-- One-mode spectrum used to witness genuine spectral dependence. -/
def singletonFiniteSpectrum (eigenvalueSq : {value : Real // 0 ≤ value}) :
    FiniteChiralSpectrum (Fin 1) where
  eigenvalueSq := fun _ => eigenvalueSq.1
  eigenvalueSq_nonnegative := fun _ => eigenvalueSq.2
  chirality := fun _ => 0

@[simp] theorem finiteSpectrumDeterminant_singleton
    (shift : PositiveSpectralShift)
    (eigenvalueSq : {value : Real // 0 ≤ value}) :
    finiteSpectrumDeterminant shift (singletonFiniteSpectrum eigenvalueSq) =
      shift.1 + eigenvalueSq.1 := by
  simp [finiteSpectrumDeterminant, singletonFiniteSpectrum]

theorem finiteSpectrumDeterminant_singleton_ne
    (shift : PositiveSpectralShift)
    (first second : {value : Real // 0 ≤ value})
    (hDifferent : first.1 ≠ second.1) :
    finiteSpectrumDeterminant shift (singletonFiniteSpectrum first) ≠
      finiteSpectrumDeterminant shift (singletonFiniteSpectrum second) := by
  intro hEqual
  apply hDifferent
  apply add_left_cancel (a := shift.1)
  simpa using hEqual

end

end P0EFTJanusFiniteModeSpectralStatisticalDeterminant4D
end JanusFormal
