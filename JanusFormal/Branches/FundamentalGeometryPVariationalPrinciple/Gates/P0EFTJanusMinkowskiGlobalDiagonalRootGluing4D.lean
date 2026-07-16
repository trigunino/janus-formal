import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMinkowskiRelativeRootOpenDomain4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGlobalDiagonalLorentzRoot4D

/-!
# Gluing the Minkowski IFT root to the global diagonal principal root

The global positive diagonal branch and the inverse-function branch at the
Minkowski pair are compared on an explicit common domain.  The only chart
condition retained in the overlap is that the global principal root lies in
the source of the actual IFT chart.  Membership of the associated metric pair
in the local target domain then follows, rather than being assumed.

This is an exact gluing theorem on the fixed-frame diagonal Lorentz sector.
It does not assert that the IFT source contains every positive diagonal root,
nor does it extend the conclusion to non-simultaneously-diagonal metrics.
-/

namespace JanusFormal
namespace P0EFTJanusMinkowskiGlobalDiagonalRootGluing4D

set_option autoImplicit false

noncomputable section

open scoped Matrix.Norms.Frobenius RightActions Topology
open P0EFTJanusLorentzLocalRootBranch4D
open P0EFTJanusMetricInverseRelativeRootFrechet
open P0EFTJanusMinkowskiRelativeRootBranch4D
open P0EFTJanusMinkowskiRelativeRootOpenDomain4D
open P0EFTJanusGlobalDiagonalLorentzRoot4D

abbrev Matrix4 := P0EFTJanusGlobalDiagonalLorentzRoot4D.Matrix4
abbrev Coefficients4 :=
  P0EFTJanusGlobalDiagonalLorentzRoot4D.Coefficients4
abbrev CoefficientPair :=
  P0EFTJanusGlobalDiagonalLorentzRoot4D.CoefficientPair
abbrev MetricPair :=
  P0EFTJanusMinkowskiRelativeRootOpenDomain4D.MetricPair

attribute [local instance]
  P0EFTJanusMinkowskiRelativeRootBranch4D.localMatrix4NormedAddCommGroup
  P0EFTJanusMinkowskiRelativeRootBranch4D.localMatrix4AddCommGroup
  P0EFTJanusMinkowskiRelativeRootBranch4D.localMatrix4TopologicalSpace
  P0EFTJanusMinkowskiRelativeRootBranch4D.localMatrix4NormedSpace
  P0EFTJanusMinkowskiRelativeRootBranch4D.localMatrix4Module
  P0EFTJanusMinkowskiRelativeRootBranch4D.localMetricPairNormedAddCommGroup
  P0EFTJanusMinkowskiRelativeRootBranch4D.localMetricPairAddCommGroup
  P0EFTJanusMinkowskiRelativeRootBranch4D.localMetricPairTopologicalSpace
  P0EFTJanusMinkowskiRelativeRootBranch4D.localMetricPairNormedSpace
  P0EFTJanusMinkowskiRelativeRootBranch4D.localMetricPairModule

/-- Embed global diagonal coefficients into the matrix-pair space of the
Minkowski IFT construction. -/
def diagonalMetricPair (point : CoefficientPair) : MetricPair :=
  (lorentzMetric point.1, lorentzMetric point.2)

/-- A positive diagonal Lorentz metric is a unit, with the explicit diagonal
inverse already constructed by the global gate. -/
theorem diagonalPlusMetric_isUnit
    (point : CoefficientPair) (hPoint : point ∈ globalDiagonalLorentzDomain) :
    IsUnit (diagonalMetricPair point).1 := by
  apply isUnit_iff_exists_inv.mpr
  exact ⟨lorentzMetricInverse point.1,
    lorentzMetric_mul_inverse point.1 hPoint.1⟩

/-- The nonsingular matrix inverse used by the local branch agrees with the
explicit diagonal inverse used by the global branch. -/
theorem diagonal_nonsingInverse_eq_explicit
    (point : CoefficientPair) (hPoint : point ∈ globalDiagonalLorentzDomain) :
    (lorentzMetric point.1)⁻¹ = lorentzMetricInverse point.1 := by
  have hUnit : IsUnit (lorentzMetric point.1) :=
    diagonalPlusMetric_isUnit point hPoint
  have hDet : IsUnit (Matrix.det (lorentzMetric point.1)) :=
    (Matrix.isUnit_iff_isUnit_det _).mp hUnit
  calc
    (lorentzMetric point.1)⁻¹ =
        (lorentzMetric point.1)⁻¹ * 1 := by rw [Matrix.mul_one]
    _ = (lorentzMetric point.1)⁻¹ *
        (lorentzMetric point.1 * lorentzMetricInverse point.1) := by
          rw [lorentzMetric_mul_inverse point.1 hPoint.1]
    _ = ((lorentzMetric point.1)⁻¹ * lorentzMetric point.1) *
        lorentzMetricInverse point.1 := by rw [Matrix.mul_assoc]
    _ = lorentzMetricInverse point.1 := by
      rw [Matrix.nonsing_inv_mul _ hDet, Matrix.one_mul]

/-- On diagonal coefficient pairs, the local relative-metric target and the
global explicit relative metric are literally the same matrix. -/
theorem diagonal_relativeMetricTarget_eq
    (point : CoefficientPair) (hPoint : point ∈ globalDiagonalLorentzDomain) :
    relativeMetricTarget (diagonalMetricPair point) =
      lorentzMetricInverse point.1 * lorentzMetric point.2 := by
  simp only [relativeMetricTarget, diagonalMetricPair]
  rw [diagonal_nonsingInverse_eq_explicit point hPoint]

/-- Explicit overlap of the global diagonal domain with the actual source of
the IFT chart.  The source-chart membership is the sole additional condition;
the corresponding local target-domain membership is proved below. -/
def minkowskiGlobalDiagonalOverlap : Set CoefficientPair :=
  globalDiagonalLorentzDomain ∩ principalRoot ⁻¹' identityRootSource

theorem minkowskiGlobalDiagonalOverlap_isOpen :
    IsOpen minkowskiGlobalDiagonalOverlap := by
  exact (principalRoot_contDiffOn 0).continuousOn.isOpen_inter_preimage
    globalDiagonalLorentzDomain_isOpen identityRootSource_isOpen

/-- The overlap is genuine: it contains the unit coefficient pair, which
maps to the Minkowski metric pair and has root equal to the identity. -/
def minkowskiCoefficientPair : CoefficientPair :=
  (fun _ => 1, fun _ => 1)

@[simp]
theorem principalRoot_minkowskiCoefficientPair :
    principalRoot minkowskiCoefficientPair = (1 : Matrix4) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [principalRoot, principalRootSpectrum, relativeRatio,
      minkowskiCoefficientPair]
  · simp [principalRoot, minkowskiCoefficientPair, hij]

theorem minkowskiCoefficientPair_mem_globalDomain :
    minkowskiCoefficientPair ∈ globalDiagonalLorentzDomain := by
  constructor <;> intro i <;>
    norm_num [positiveMagnitudeDomain, minkowskiCoefficientPair]

theorem minkowskiCoefficientPair_mem_overlap :
    minkowskiCoefficientPair ∈ minkowskiGlobalDiagonalOverlap := by
  refine ⟨minkowskiCoefficientPair_mem_globalDomain, ?_⟩
  change principalRoot minkowskiCoefficientPair ∈ identityRootSource
  rw [principalRoot_minkowskiCoefficientPair]
  exact root_mem_localSquareChart_source
    (1 : Matrix4) identitySylvesterWitness

theorem minkowskiGlobalDiagonalOverlap_nonempty :
    minkowskiGlobalDiagonalOverlap.Nonempty :=
  ⟨minkowskiCoefficientPair, minkowskiCoefficientPair_mem_overlap⟩

/-- Source membership of the global root forces the corresponding target to
belong to the IFT target, so the embedded metric pair lies in the explicit
local open domain. -/
theorem diagonalMetricPair_mem_minkowskiOpenDomain
    {point : CoefficientPair}
    (hPoint : point ∈ minkowskiGlobalDiagonalOverlap) :
    diagonalMetricPair point ∈ minkowskiRelativeRootOpenDomain := by
  refine ⟨diagonalPlusMetric_isUnit point hPoint.1, ?_⟩
  have hTarget :=
    (localSquareChart (1 : Matrix4) identitySylvesterWitness).map_source
      hPoint.2
  have hSquare : matrixSquare (principalRoot point) =
      relativeMetricTarget (diagonalMetricPair point) := by
    exact (principalRoot_square point hPoint.1).trans
      (diagonal_relativeMetricTarget_eq point hPoint.1).symm
  change relativeMetricTarget (diagonalMetricPair point) ∈ identityRootTarget
  rw [identityRootTarget]
  simpa only [localSquareChart_apply, hSquare] using hTarget

/-- Exact agreement of the two selected roots throughout their explicit
overlap.  This is the compatibility needed to glue the IFT germ to the
global positive diagonal branch. -/
theorem minkowskiIFT_eq_globalPrincipalRoot_on_overlap
    {point : CoefficientPair}
    (hPoint : point ∈ minkowskiGlobalDiagonalOverlap) :
    minkowskiRelativeRootBranch (diagonalMetricPair point) =
      principalRoot point := by
  symm
  apply root_unique_in_identityChart
    (diagonalMetricPair_mem_minkowskiOpenDomain hPoint) hPoint.2
  exact (principalRoot_square point hPoint.1).trans
    (diagonal_relativeMetricTarget_eq point hPoint.1).symm

/-- Compact closure statement for audit/facade integration. -/
theorem minkowski_global_diagonal_root_gluing_closure :
    IsOpen minkowskiGlobalDiagonalOverlap ∧
      minkowskiGlobalDiagonalOverlap.Nonempty ∧
      (∀ point ∈ minkowskiGlobalDiagonalOverlap,
        diagonalMetricPair point ∈ minkowskiRelativeRootOpenDomain ∧
        minkowskiRelativeRootBranch (diagonalMetricPair point) =
          principalRoot point) := by
  refine ⟨minkowskiGlobalDiagonalOverlap_isOpen,
    minkowskiGlobalDiagonalOverlap_nonempty, ?_⟩
  intro point hPoint
  exact ⟨diagonalMetricPair_mem_minkowskiOpenDomain hPoint,
    minkowskiIFT_eq_globalPrincipalRoot_on_overlap hPoint⟩

end

end P0EFTJanusMinkowskiGlobalDiagonalRootGluing4D
end JanusFormal
