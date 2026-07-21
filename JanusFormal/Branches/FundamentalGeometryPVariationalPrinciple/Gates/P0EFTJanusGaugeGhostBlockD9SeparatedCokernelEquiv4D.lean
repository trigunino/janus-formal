import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaugeGhostBlockD9SeparatedCokernelIndex4D

namespace JanusFormal
namespace P0EFTJanusGaugeGhostBlockD9SeparatedCokernelEquiv4D
set_option autoImplicit false
noncomputable section
open P0EFTJanusGaugeGhostBlockD9SymbolCokernel4D
open P0EFTJanusGaugeGhostBlockD9SymbolBridge4D
open P0EFTJanusGaugeGhostBlockD9SeparatedSymbols4D
open P0EFTJanusGaugeGhostBlockD9SeparatedFinrank4D
open P0EFTJanusGaugeGhostBlockD9PointwiseShortSequence4D
open P0EFTJanusGaugeGhostBlockD9SeparatedCokernelIndex4D
open P0EFTJanusGaugeGhostBlockD9ZeroModeDirectSum4D
open P0EFTJanusGaugeFixedPrincipalSymbols
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusD9PairedU1GhostZeroModeCohomology4D

private def separatedCokernelBaseMap (covector : TangentVector3) :
    D9GaugeGhostLinearCoordinate →ₗ[Real]
      D9GaugeCokernel covector × D9GhostCokernel covector :=
  ((LinearMap.range (d9GaugeLinearSymbol covector)).mkQ.comp
      (LinearMap.fst Real D9GaugeLinearCoordinate D9PairedGhostCoordinateSpace)).prod
    ((LinearMap.range (d9GhostLinearSymbol covector)).mkQ.comp
      (LinearMap.snd Real D9GaugeLinearCoordinate D9PairedGhostCoordinateSpace))

private theorem combinedRange_le_separatedCokernelBaseMap_ker (covector : TangentVector3) :
    LinearMap.range (d9GaugeGhostBlockLinearSymbol covector) ≤
      LinearMap.ker (separatedCokernelBaseMap covector) := by
  rw [combinedSymbol_range_prod]
  rintro coordinate ⟨hGauge, hGhost⟩
  change (Submodule.Quotient.mk coordinate.1, Submodule.Quotient.mk coordinate.2) = (0, 0)
  apply Prod.ext
  · rw [Submodule.Quotient.mk_eq_zero]
    exact hGauge
  · rw [Submodule.Quotient.mk_eq_zero]
    exact hGhost

def combinedToSeparatedCokernels (covector : TangentVector3) :
    D9GaugeGhostBlockCokernel covector →ₗ[Real]
      D9GaugeCokernel covector × D9GhostCokernel covector :=
  (LinearMap.range (d9GaugeGhostBlockLinearSymbol covector)).liftQ
    (separatedCokernelBaseMap covector)
    (combinedRange_le_separatedCokernelBaseMap_ker covector)

@[simp] theorem combinedToSeparatedCokernels_mk (covector : TangentVector3)
    (coordinate : D9GaugeGhostLinearCoordinate) :
    combinedToSeparatedCokernels covector
        (Submodule.Quotient.mk coordinate) =
      (Submodule.Quotient.mk coordinate.1, Submodule.Quotient.mk coordinate.2) := rfl

private theorem combinedToSeparatedCokernels_bijective (covector : TangentVector3) :
    Function.Bijective (combinedToSeparatedCokernels covector) := by
  have hSurjective : Function.Surjective (combinedToSeparatedCokernels covector) := by
    intro value
    obtain ⟨gauge, hGauge⟩ := Submodule.mkQ_surjective
      (LinearMap.range (d9GaugeLinearSymbol covector)) value.1
    obtain ⟨ghost, hGhost⟩ := Submodule.mkQ_surjective
      (LinearMap.range (d9GhostLinearSymbol covector)) value.2
    refine ⟨Submodule.Quotient.mk (gauge, ghost), ?_⟩
    rw [combinedToSeparatedCokernels_mk]
    exact Prod.ext hGauge hGhost
  have hFinrank :
      Module.finrank Real (D9GaugeGhostBlockCokernel covector) =
        Module.finrank Real (D9GaugeCokernel covector × D9GhostCokernel covector) :=
    (combinedCokernel_finrank_additive covector).trans (Module.finrank_prod (R := Real)).symm
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hFinrank).mpr hSurjective,
    hSurjective⟩

def combinedCokernelEquivSeparated (covector : TangentVector3) :
    D9GaugeGhostBlockCokernel covector ≃ₗ[Real]
      D9GaugeCokernel covector × D9GhostCokernel covector :=
  LinearEquiv.ofBijective (combinedToSeparatedCokernels covector)
    (combinedToSeparatedCokernels_bijective covector)

@[simp] theorem combinedCokernelEquivSeparated_mk (covector : TangentVector3)
    (coordinate : D9GaugeGhostLinearCoordinate) :
    combinedCokernelEquivSeparated covector (Submodule.Quotient.mk coordinate) =
      (Submodule.Quotient.mk coordinate.1, Submodule.Quotient.mk coordinate.2) := rfl

theorem combinedCokernelEquivSeparated_nonzero (covector : TangentVector3)
    (hCovector : covector ≠ zeroTangent)
    (c : D9GaugeGhostBlockCokernel covector) :
    combinedCokernelEquivSeparated covector c = (0, 0) := by
  apply Prod.ext
  · obtain ⟨coordinate, hCoordinate⟩ := Submodule.mkQ_surjective
      (LinearMap.range (d9GaugeLinearSymbol covector))
        (combinedCokernelEquivSeparated covector c).1
    rw [← hCoordinate]
    change Submodule.Quotient.mk coordinate = 0
    rw [Submodule.Quotient.mk_eq_zero,
      d9GaugeLinearSymbol_range_nonzero covector hCovector]
    trivial
  · obtain ⟨coordinate, hCoordinate⟩ := Submodule.mkQ_surjective
      (LinearMap.range (d9GhostLinearSymbol covector))
        (combinedCokernelEquivSeparated covector c).2
    rw [← hCoordinate]
    change Submodule.Quotient.mk coordinate = 0
    rw [Submodule.Quotient.mk_eq_zero,
      d9GhostLinearSymbol_range_nonzero covector hCovector]
    trivial

theorem combinedCokernelEquivSeparated_zero_mk
    (coordinate : D9GaugeGhostLinearCoordinate) :
    combinedCokernelEquivSeparated zeroTangent
        (d9GaugeGhostBlockCokernelProjection zeroTangent coordinate) =
      ((LinearMap.range (d9GaugeLinearSymbol zeroTangent)).mkQ coordinate.1,
        (LinearMap.range (d9GhostLinearSymbol zeroTangent)).mkQ coordinate.2) := rfl

/-- The cokernel class of any packed full-reading coordinate separates into
its gauge and ghost quotient classes.  This applies directly to
`fullGaugeGhostD9Reading` without adding global operator content. -/
theorem packedFullReadingClass_separates (covector : TangentVector3)
    (reading : D9GaugeGhostCoordinate) :
    combinedCokernelEquivSeparated covector
        (d9GaugeGhostBlockCokernelProjection covector
          (packGaugeGhostCoordinate reading)) =
      ((LinearMap.range (d9GaugeLinearSymbol covector)).mkQ
          (packGaugeGhostCoordinate reading).1,
        (LinearMap.range (d9GhostLinearSymbol covector)).mkQ
          (packGaugeGhostCoordinate reading).2) := rfl

def d9GaugeCokernelProjection (covector : TangentVector3) :
    D9GaugeLinearCoordinate →ₗ[Real] D9GaugeCokernel covector :=
  (LinearMap.range (d9GaugeLinearSymbol covector)).mkQ

def d9GhostCokernelProjection (covector : TangentVector3) :
    D9PairedGhostCoordinateSpace →ₗ[Real] D9GhostCokernel covector :=
  (LinearMap.range (d9GhostLinearSymbol covector)).mkQ

theorem combinedCokernelProjection_gauge_compatible (covector : TangentVector3) :
    (LinearMap.fst Real (D9GaugeCokernel covector) (D9GhostCokernel covector)).comp
        ((combinedCokernelEquivSeparated covector).toLinearMap.comp
          (d9GaugeGhostBlockCokernelProjection covector)) =
      (d9GaugeCokernelProjection covector).comp
        (LinearMap.fst Real D9GaugeLinearCoordinate D9PairedGhostCoordinateSpace) := by
  apply LinearMap.ext
  intro coordinate
  rfl

theorem combinedCokernelProjection_ghost_compatible (covector : TangentVector3) :
    (LinearMap.snd Real (D9GaugeCokernel covector) (D9GhostCokernel covector)).comp
        ((combinedCokernelEquivSeparated covector).toLinearMap.comp
          (d9GaugeGhostBlockCokernelProjection covector)) =
      (d9GhostCokernelProjection covector).comp
        (LinearMap.snd Real D9GaugeLinearCoordinate D9PairedGhostCoordinateSpace) := by
  apply LinearMap.ext
  intro coordinate
  rfl

theorem d9GaugeCokernelProjection_ker (covector : TangentVector3) :
    LinearMap.ker (d9GaugeCokernelProjection covector) =
      LinearMap.range (d9GaugeLinearSymbol covector) := by
  exact Submodule.ker_mkQ _

theorem d9GhostCokernelProjection_ker (covector : TangentVector3) :
    LinearMap.ker (d9GhostCokernelProjection covector) =
      LinearMap.range (d9GhostLinearSymbol covector) := by
  exact Submodule.ker_mkQ _

theorem separatedCokernelProjection_surjective (covector : TangentVector3) :
    Function.Surjective (d9GaugeCokernelProjection covector) ∧
      Function.Surjective (d9GhostCokernelProjection covector) :=
  ⟨Submodule.mkQ_surjective _, Submodule.mkQ_surjective _⟩

theorem d9Gauge_pointwise_short_exact (covector : TangentVector3) :
    LinearMap.range (d9GaugeLinearSymbol covector) =
        LinearMap.ker (d9GaugeCokernelProjection covector) ∧
      Function.Surjective (d9GaugeCokernelProjection covector) :=
  ⟨(d9GaugeCokernelProjection_ker covector).symm, Submodule.mkQ_surjective _⟩

theorem d9Ghost_pointwise_short_exact (covector : TangentVector3) :
    LinearMap.range (d9GhostLinearSymbol covector) =
        LinearMap.ker (d9GhostCokernelProjection covector) ∧
      Function.Surjective (d9GhostCokernelProjection covector) :=
  ⟨(d9GhostCokernelProjection_ker covector).symm, Submodule.mkQ_surjective _⟩

theorem combinedProjection_under_equiv_is_product (covector : TangentVector3) :
    (combinedCokernelEquivSeparated covector).toLinearMap.comp
        (d9GaugeGhostBlockCokernelProjection covector) =
      ((d9GaugeCokernelProjection covector).comp
          (LinearMap.fst Real D9GaugeLinearCoordinate D9PairedGhostCoordinateSpace)).prod
        ((d9GhostCokernelProjection covector).comp
          (LinearMap.snd Real D9GaugeLinearCoordinate D9PairedGhostCoordinateSpace)) := by
  apply LinearMap.ext
  intro coordinate
  rfl

theorem combinedExactMiddle_is_product (covector : TangentVector3) :
    LinearMap.range (d9GaugeGhostBlockLinearSymbol covector) =
      (LinearMap.ker (d9GaugeCokernelProjection covector)).prod
        (LinearMap.ker (d9GhostCokernelProjection covector)) := by
  rw [combinedSymbol_range_prod, d9GaugeCokernelProjection_ker,
    d9GhostCokernelProjection_ker]

/-- The combined pointwise quotient sequence is the product of the two
separated exact quotient sequences. -/
theorem combined_pointwise_short_exact_product_certificate
    (covector : TangentVector3) :
    LinearMap.range (d9GaugeGhostBlockLinearSymbol covector) =
        LinearMap.ker (d9GaugeGhostBlockCokernelProjection covector) ∧
      Function.Surjective (d9GaugeGhostBlockCokernelProjection covector) ∧
      LinearMap.range (d9GaugeGhostBlockLinearSymbol covector) =
        (LinearMap.ker (d9GaugeCokernelProjection covector)).prod
          (LinearMap.ker (d9GhostCokernelProjection covector)) ∧
      (combinedCokernelEquivSeparated covector).toLinearMap.comp
          (d9GaugeGhostBlockCokernelProjection covector) =
        ((d9GaugeCokernelProjection covector).comp
            (LinearMap.fst Real D9GaugeLinearCoordinate D9PairedGhostCoordinateSpace)).prod
          ((d9GhostCokernelProjection covector).comp
            (LinearMap.snd Real D9GaugeLinearCoordinate D9PairedGhostCoordinateSpace)) :=
  ⟨d9GaugeGhostBlock_pointwise_exact_at_coordinate covector,
    Submodule.mkQ_surjective _, combinedExactMiddle_is_product covector,
    combinedProjection_under_equiv_is_product covector⟩

end
end P0EFTJanusGaugeGhostBlockD9SeparatedCokernelEquiv4D
end JanusFormal
