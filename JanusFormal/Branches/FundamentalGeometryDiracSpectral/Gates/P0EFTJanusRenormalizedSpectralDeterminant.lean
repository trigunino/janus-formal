import JanusFormal.Branches.FundamentalGeometryDiracSpectral.Gates.P0EFTJanusSeparatedSpectrumProperness
import JanusFormal.Branches.FundamentalGeometryDiracSpectral.Gates.P0EFTJanusFullHolonomyDeterminant

namespace JanusFormal
namespace P0EFTJanusRenormalizedSpectralDeterminant

set_option autoImplicit false

open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusFullHolonomyDeterminant
open P0EFTJanusSeparatedSpectrumProperness

noncomputable section

def cutoffSphereLevels (N : ℕ) : Finset ℕ :=
  Finset.range (N + 1)

/-- The circle momentum product has already been zeta-regularized in this kernel. -/
def sphereLevelKernel (data : ProductThroatSpectralData)
    (holonomy : ℝ) (level : ℕ) : ℝ :=
  modeDeterminantKernel
    (data.circlePeriod * Real.sqrt (sphereEigenvalueSquared data level)) holonomy

/--
Cut off only the sphere levels.  Circle modes must not be summed here because
`sphereLevelKernel` already represents their regularized infinite product.
-/
def finiteCutoffLogDeterminant (data : ProductThroatSpectralData)
    (N : ℕ) (holonomy : ℝ) : ℝ :=
  ∑ level ∈ cutoffSphereLevels N,
    (sphereMultiplicity data level : ℝ) *
      Real.log (sphereLevelKernel data holonomy level)

theorem finite_cutoff_is_circle_reduced (data : ProductThroatSpectralData)
    (N : ℕ) (holonomy : ℝ) :
    finiteCutoffLogDeterminant data N holonomy =
      ∑ level ∈ Finset.range (N + 1),
        (sphereMultiplicity data level : ℝ) *
          Real.log (modeDeterminantKernel
            (data.circlePeriod * Real.sqrt (sphereEigenvalueSquared data level))
            holonomy) := by
  rfl

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
