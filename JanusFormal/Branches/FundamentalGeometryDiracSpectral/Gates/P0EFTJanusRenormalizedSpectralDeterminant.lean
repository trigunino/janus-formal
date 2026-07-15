import JanusFormal.Branches.FundamentalGeometryDiracSpectral.Gates.P0EFTJanusSeparatedSpectrumProperness
import JanusFormal.Branches.FundamentalGeometryDiracSpectral.Gates.P0EFTJanusFullHolonomyDeterminant

namespace JanusFormal
namespace P0EFTJanusRenormalizedSpectralDeterminant

set_option autoImplicit false

open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusInfiniteL2DiracDomain
open P0EFTJanusFullHolonomyDeterminant
open P0EFTJanusSeparatedSpectrumProperness

noncomputable section

def cutoffModes (N : ℕ) : Finset ProductDiracMode :=
  (product_mode_bounding_box_finite N).toFinset

def separatedModeKernel (data : ProductThroatSpectralData)
    (holonomy : ℝ) (mode : ProductDiracMode) : ℝ :=
  modeDeterminantKernel
    (data.circlePeriod * separatedDiracWeight data mode) holonomy

def finiteCutoffLogDeterminant (data : ProductThroatSpectralData)
    (N : ℕ) (holonomy : ℝ) : ℝ :=
  ∑ mode ∈ cutoffModes N, Real.log (separatedModeKernel data holonomy mode)

/-- A regulator-independent family requires one holonomy-independent local subtraction. -/
structure RenormalizedDeterminantFamily (data : ProductThroatSpectralData) where
  localCounterterm : ℕ → ℝ
  renormalizedLog : ℝ → ℝ
  cutoffConverges : ∀ holonomy : ℝ,
    Filter.Tendsto
      (fun N => finiteCutoffLogDeterminant data N holonomy - localCounterterm N)
      Filter.atTop (nhds (renormalizedLog holonomy))

def RenormalizedDeterminantFamily.determinant
    {data : ProductThroatSpectralData}
    (family : RenormalizedDeterminantFamily data) (holonomy : ℝ) : ℝ :=
  Real.exp (family.renormalizedLog holonomy)

theorem renormalized_determinant_positive
    {data : ProductThroatSpectralData}
    (family : RenormalizedDeterminantFamily data) (holonomy : ℝ) :
    0 < family.determinant holonomy :=
  Real.exp_pos _

/-- The renormalized answer is unique once the local subtraction scheme is fixed. -/
theorem renormalized_log_unique
    {data : ProductThroatSpectralData}
    (first second : RenormalizedDeterminantFamily data)
    (hCounterterm : first.localCounterterm = second.localCounterterm) :
    first.renormalizedLog = second.renormalizedLog := by
  funext holonomy
  apply tendsto_nhds_unique (first.cutoffConverges holonomy)
  simpa [hCounterterm] using second.cutoffConverges holonomy

theorem renormalized_determinant_unique
    {data : ProductThroatSpectralData}
    (first second : RenormalizedDeterminantFamily data)
    (hCounterterm : first.localCounterterm = second.localCounterterm) :
    first.determinant = second.determinant := by
  funext holonomy
  simp [RenormalizedDeterminantFamily.determinant,
    renormalized_log_unique first second hCounterterm]

/-- Exact remaining analytic datum: existence of a common local subtraction for every holonomy. -/
def RenormalizedDeterminantExists (data : ProductThroatSpectralData) : Prop :=
  Nonempty (RenormalizedDeterminantFamily data)

structure RenormalizedDeterminantClosureCertificate
    (data : ProductThroatSpectralData) : Prop where
  compactResolvent :
    IsCompactOperator
      (P0EFTJanusDiagonalCompactResolvent.shiftIResolventCLM
        (separatedDiracWeight data))
  familyExists : RenormalizedDeterminantExists data
  fixedSchemeUnique : ∀ first second : RenormalizedDeterminantFamily data,
    first.localCounterterm = second.localCounterterm →
      first.determinant = second.determinant

theorem renormalized_determinant_closure_of_existence
    (data : ProductThroatSpectralData) (hExists : RenormalizedDeterminantExists data) :
    RenormalizedDeterminantClosureCertificate data where
  compactResolvent := separated_dirac_shift_I_resolvent_compact data
  familyExists := hExists
  fixedSchemeUnique := renormalized_determinant_unique

end

end P0EFTJanusRenormalizedSpectralDeterminant
end JanusFormal
