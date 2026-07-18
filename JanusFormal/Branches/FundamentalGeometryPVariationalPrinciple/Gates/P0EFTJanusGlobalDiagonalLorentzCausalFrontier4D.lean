import Mathlib.Topology.Constructions.SumProd
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGlobalDiagonalLorentzRoot4D

/-!
# Causal compatibility and spectral frontier of the diagonal Lorentz domain

The fixed-frame positive diagonal domain has a common timelike coordinate
direction. Its closure and frontier are computed exactly, so the selected
positive principal root branch has an explicit spectral boundary.
-/

namespace JanusFormal
namespace P0EFTJanusGlobalDiagonalLorentzCausalFrontier4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusGlobalDiagonalLorentzRoot4D

/-- Closed nonnegative orthant in the diagonal coefficient space. -/
def nonnegativeMagnitudeDomain : Set Coefficients4 :=
  { coefficients | ∀ i, 0 ≤ coefficients i }

/-- The boundary consists exactly of nonnegative coefficients with at least
one vanishing eigenvalue magnitude. -/
def magnitudeSpectralBoundary : Set Coefficients4 :=
  { coefficients | (∀ i, 0 ≤ coefficients i) ∧ ∃ i, coefficients i = 0 }

theorem closure_positiveMagnitudeDomain :
    closure positiveMagnitudeDomain = nonnegativeMagnitudeDomain := by
  rw [show positiveMagnitudeDomain = Set.pi Set.univ (fun _ : Fin 4 => Set.Ioi 0) by
    ext coefficients
    simp [positiveMagnitudeDomain]]
  rw [closure_pi_set]
  ext coefficients
  simp [nonnegativeMagnitudeDomain, closure_Ioi, Pi.le_def]

theorem frontier_positiveMagnitudeDomain :
    frontier positiveMagnitudeDomain = magnitudeSpectralBoundary := by
  rw [frontier, closure_positiveMagnitudeDomain,
    positiveMagnitudeDomain_isOpen.interior_eq]
  ext coefficients
  simp only [Set.mem_sdiff]
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    by_contra hNoZero
    apply h.2
    intro i
    exact lt_of_le_of_ne (h.1 i) (Ne.symm (fun hZero => hNoZero ⟨i, hZero⟩))
  · rintro ⟨hNonnegative, i, hi⟩
    refine ⟨hNonnegative, ?_⟩
    intro hPositive
    exact (ne_of_gt (hPositive i)) hi

/-- Exact topological boundary of the two-metric domain. -/
def globalDiagonalSpectralBoundary : Set CoefficientPair :=
  magnitudeSpectralBoundary ×ˢ nonnegativeMagnitudeDomain ∪
    nonnegativeMagnitudeDomain ×ˢ magnitudeSpectralBoundary

theorem closure_globalDiagonalLorentzDomain :
    closure globalDiagonalLorentzDomain =
      nonnegativeMagnitudeDomain ×ˢ nonnegativeMagnitudeDomain := by
  rw [globalDiagonalLorentzDomain, closure_prod_eq,
    closure_positiveMagnitudeDomain]

theorem frontier_globalDiagonalLorentzDomain :
    frontier globalDiagonalLorentzDomain = globalDiagonalSpectralBoundary := by
  rw [globalDiagonalLorentzDomain, frontier_prod_eq,
    frontier_positiveMagnitudeDomain, closure_positiveMagnitudeDomain]
  exact Set.union_comm _ _

/-- Quadratic form of a diagonal Lorentz metric in the fixed coefficient
frame. -/
def lorentzQuadraticForm (coefficients vector : Coefficients4) : Real :=
  ∑ i, signature i * coefficients i * vector i ^ 2

/-- Coordinate-zero unit direction. -/
def commonTimeDirection : Coefficients4 :=
  fun i => if i = 0 then 1 else 0

theorem lorentzQuadraticForm_commonTimeDirection
    (coefficients : Coefficients4) :
    lorentzQuadraticForm coefficients commonTimeDirection = -coefficients 0 := by
  simp [lorentzQuadraticForm, commonTimeDirection, signature]

/-- The two diagonal metrics share the same strict timelike direction. -/
def CausallyCompatible (point : CoefficientPair) : Prop :=
  ∃ vector : Coefficients4,
    lorentzQuadraticForm point.1 vector < 0 ∧
      lorentzQuadraticForm point.2 vector < 0

theorem globalDiagonalLorentzDomain_causallyCompatible
    (point : CoefficientPair) (hPoint : point ∈ globalDiagonalLorentzDomain) :
    CausallyCompatible point := by
  refine ⟨commonTimeDirection, ?_, ?_⟩
  · rw [lorentzQuadraticForm_commonTimeDirection]
    exact neg_lt_zero.mpr (hPoint.1 0)
  · rw [lorentzQuadraticForm_commonTimeDirection]
    exact neg_lt_zero.mpr (hPoint.2 0)

end

end P0EFTJanusGlobalDiagonalLorentzCausalFrontier4D
end JanusFormal
