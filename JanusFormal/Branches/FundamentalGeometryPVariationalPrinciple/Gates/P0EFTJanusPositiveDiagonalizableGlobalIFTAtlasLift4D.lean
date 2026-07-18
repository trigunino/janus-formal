import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPositiveDiagonalizableGlobalRootContinuity4D

/-!
# Global IFT atlas lift on the positive diagonalizable locus

The already constructed presentation-independent selector is continuous on
the full real-diagonalizable, strictly-positive spectral locus.  This gate
packages that selector as the global lift of all the local IFT root charts.
No extension to matrices outside that locus is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusPositiveDiagonalizableGlobalIFTAtlasLift4D

set_option autoImplicit false

noncomputable section

open scoped Matrix.Norms.Frobenius RightActions Topology
open P0EFTJanusLorentzLocalRootBranch4D
open P0EFTJanusPositiveDiagonalizableRelativeRoot4D
open P0EFTJanusPositiveDiagonalizableLocalRootBranch4D
open P0EFTJanusPositiveDiagonalizableRootGluing4D
open P0EFTJanusPositiveDiagonalizableGlobalRootRegularity4D
open P0EFTJanusPositiveDiagonalizableGlobalRootContinuity4D

abbrev Matrix4 := P0EFTJanusPositiveDiagonalizableRelativeRoot4D.Matrix4

/-- A global lift of the local square-root IFT atlas, restricted exactly to
the locus of real-diagonalizable matrices with strictly positive spectrum.
Values of `rootOn` outside this locus carry no meaning. -/
structure PositiveDiagonalizableIFTGlobalLift where
  rootOn : Matrix4 → Matrix4
  continuousOn_rootOn : ContinuousOn rootOn positiveDiagonalizableLocus
  square_on_locus : ∀ target ∈ positiveDiagonalizableLocus,
    matrixSquare (rootOn target) = target
  agrees_at_presentation : ∀ data : PositiveDiagonalizableRelativeMatrix,
    rootOn data.target = positiveSimilarityRoot data
  agrees_with_local_ift : ∀ data : PositiveDiagonalizableRelativeMatrix,
    PositiveDiagonalizableLocalIFTStable data

/-- The canonical algebraic selector supplies the global IFT-atlas lift. -/
def positiveDiagonalizableIFTGlobalLift :
    PositiveDiagonalizableIFTGlobalLift where
  rootOn := positiveDiagonalizableGlobalRootOn
  continuousOn_rootOn :=
    positiveDiagonalizableGlobalRoot_continuous_iff_continuousOn.mp
      positiveDiagonalizableGlobalRoot_continuous
  square_on_locus := positiveDiagonalizableGlobalRootOn_square
  agrees_at_presentation := positiveDiagonalizableGlobalRootOn_at_presentation
  agrees_with_local_ift := positiveDiagonalizableGlobalRoot_locallyStable

/-- Every global IFT-atlas lift agrees with the canonical selector throughout
the positive diagonalizable locus. -/
theorem positiveDiagonalizableIFTGlobalLift_unique_on_locus
    (lift : PositiveDiagonalizableIFTGlobalLift) :
    Set.EqOn lift.rootOn positiveDiagonalizableGlobalRootOn
      positiveDiagonalizableLocus := by
  intro target hTarget
  obtain ⟨data, hData⟩ := hTarget
  rw [← hData]
  exact (lift.agrees_at_presentation data).trans
    (positiveDiagonalizableGlobalRootOn_at_presentation data).symm

/-- Complete atlas statement: a continuous exact-square global lift exists,
agrees with every unconditional local IFT branch, and is unique on its exact
physical domain. -/
theorem exists_unique_positiveDiagonalizableIFTGlobalLift_on_locus :
    ∃ lift : PositiveDiagonalizableIFTGlobalLift,
      ∀ other : PositiveDiagonalizableIFTGlobalLift,
        Set.EqOn other.rootOn lift.rootOn positiveDiagonalizableLocus := by
  refine ⟨positiveDiagonalizableIFTGlobalLift, ?_⟩
  intro other
  exact positiveDiagonalizableIFTGlobalLift_unique_on_locus other

end

end P0EFTJanusPositiveDiagonalizableGlobalIFTAtlasLift4D
end JanusFormal
