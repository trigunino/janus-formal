import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiveSectorNaturalBaseOperatorCoordinates4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiveSectorNaturalBasePullback4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiveSectorComponentwiseProductMap4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiveSectorHilbertProjectorCoordinates4D

/-!
# Multidimensional natural linear family in the five physical sectors

This packet binds one continuous-linear ambient family `H_b` to a D11 natural
elliptic representation whose coordinates, pullbacks and operator all preserve
the unique five-sector Hilbert geometry.

The componentwise formula plus `H_b 0 = 0` proves family-wide projector
commutation; that commutation is not stored as a separate hypothesis.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiveSectorNaturalLinearBaseFamily4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPNaturalEllipticOperatorBaseRepresentation4D
open P0EFTJanusProgramPFiveSectorHilbertCoordinates4D
open P0EFTJanusProgramPFiveSectorHilbertProjectorCoordinates4D
open P0EFTJanusProgramPFiveSectorComponentwiseProductMap4D
open P0EFTJanusProgramPFiveSectorNaturalBaseRepresentation4D
open P0EFTJanusProgramPFiveSectorNaturalBaseOperatorFactorization4D
open P0EFTJanusProgramPFiveSectorNaturalBaseOperatorCoordinates4D
open P0EFTJanusProgramPFiveSectorNaturalBasePullback4D
open P0EFTJanusNaturalEllipticFamilyExistence

variable
  {Parameter State Metric Abelian Matter Longitudinal Boundary : Type*}
  [NormedAddCommGroup State] [InnerProductSpace Real State]
  [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
  [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
  [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
  [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
  [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
  {immersionCategory : P0EFTJanusSpinCImmersionCategory.SpinCImmersionCategory}
  {family : NaturalEllipticOperatorFamily immersionCategory}

/-- One multidimensional continuous-linear Hessian family equipped with its
exact five-sector D11 realization. -/
structure FiveSectorNaturalLinearBaseFamilyData
    (operator : Parameter → State →L[Real] State)
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary)) where
  representation : NaturalEllipticOperatorBaseRepresentationData
    Parameter State immersionCategory family (fun parameter state =>
      operator parameter state)
  refinement : FiveSectorNaturalBaseRepresentationData representation coordinates
  factorization : FiveSectorNaturalBaseOperatorFactorizationData
    representation coordinates refinement
  pullback : FiveSectorNaturalBasePullbackData representation coordinates refinement

namespace FiveSectorNaturalLinearBaseFamilyData

/-- Exact five-block formula for the ambient continuous-linear family. -/
theorem operator_blockFormula
    {operator : Parameter → State →L[Real] State}
    {coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary)}
    (data : FiveSectorNaturalLinearBaseFamilyData
      (family := family) operator coordinates)
    (parameter : Parameter) (state : State) :
    coordinates.decomposition (operator parameter state) =
      fiveSectorMetricAxis
          (data.factorization.representedMetricBlock data.representation coordinates
            data.refinement parameter
            (fiveSectorMetricCoordinate (coordinates.decomposition state))) +
        fiveSectorAbelianAxis
          (data.factorization.representedAbelianBlock data.representation coordinates
            data.refinement parameter
            (fiveSectorAbelianCoordinate (coordinates.decomposition state))) +
        fiveSectorMatterAxis
          (data.factorization.representedMatterBlock data.representation coordinates
            data.refinement parameter
            (fiveSectorMatterCoordinate (coordinates.decomposition state))) +
        fiveSectorLongitudinalAxis
          (data.factorization.representedLongitudinalBlock data.representation coordinates
            data.refinement parameter
            (fiveSectorLongitudinalCoordinate (coordinates.decomposition state))) +
        fiveSectorBoundaryAxis
          (data.factorization.representedBoundaryBlock data.representation coordinates
            data.refinement parameter
            (fiveSectorBoundaryCoordinate (coordinates.decomposition state))) := by
  rw [← data.representation.representedNaturalOperator_eq parameter]
  exact data.factorization.representedNaturalOperator_blockFormula
    data.representation coordinates data.refinement parameter state

private theorem metricBlock_zero
    {operator : Parameter → State →L[Real] State}
    {coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary)}
    (data : FiveSectorNaturalLinearBaseFamilyData
      (family := family) operator coordinates)
    (parameter : Parameter) :
    data.factorization.representedMetricBlock data.representation coordinates
        data.refinement parameter 0 = 0 := by
  have h := data.factorization.representedNaturalOperator_metricCoordinate
    data.representation coordinates data.refinement parameter (0 : State)
  rw [data.representation.representedNaturalOperator_eq parameter] at h
  simpa using h.symm

private theorem abelianBlock_zero
    {operator : Parameter → State →L[Real] State}
    {coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary)}
    (data : FiveSectorNaturalLinearBaseFamilyData
      (family := family) operator coordinates)
    (parameter : Parameter) :
    data.factorization.representedAbelianBlock data.representation coordinates
        data.refinement parameter 0 = 0 := by
  have h := data.factorization.representedNaturalOperator_abelianCoordinate
    data.representation coordinates data.refinement parameter (0 : State)
  rw [data.representation.representedNaturalOperator_eq parameter] at h
  simpa using h.symm

private theorem matterBlock_zero
    {operator : Parameter → State →L[Real] State}
    {coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary)}
    (data : FiveSectorNaturalLinearBaseFamilyData
      (family := family) operator coordinates)
    (parameter : Parameter) :
    data.factorization.representedMatterBlock data.representation coordinates
        data.refinement parameter 0 = 0 := by
  have h := data.factorization.representedNaturalOperator_matterCoordinate
    data.representation coordinates data.refinement parameter (0 : State)
  rw [data.representation.representedNaturalOperator_eq parameter] at h
  simpa using h.symm

private theorem longitudinalBlock_zero
    {operator : Parameter → State →L[Real] State}
    {coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary)}
    (data : FiveSectorNaturalLinearBaseFamilyData
      (family := family) operator coordinates)
    (parameter : Parameter) :
    data.factorization.representedLongitudinalBlock data.representation coordinates
        data.refinement parameter 0 = 0 := by
  have h := data.factorization.representedNaturalOperator_longitudinalCoordinate
    data.representation coordinates data.refinement parameter (0 : State)
  rw [data.representation.representedNaturalOperator_eq parameter] at h
  simpa using h.symm

private theorem boundaryBlock_zero
    {operator : Parameter → State →L[Real] State}
    {coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary)}
    (data : FiveSectorNaturalLinearBaseFamilyData
      (family := family) operator coordinates)
    (parameter : Parameter) :
    data.factorization.representedBoundaryBlock data.representation coordinates
        data.refinement parameter 0 = 0 := by
  have h := data.factorization.representedNaturalOperator_boundaryCoordinate
    data.representation coordinates data.refinement parameter (0 : State)
  rw [data.representation.representedNaturalOperator_eq parameter] at h
  simpa using h.symm

private theorem operator_componentwise
    {operator : Parameter → State →L[Real] State}
    {coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary)}
    (data : FiveSectorNaturalLinearBaseFamilyData
      (family := family) operator coordinates)
    (parameter : Parameter) (state : State) :
    coordinates.decomposition (operator parameter state) =
      fiveSectorComponentwiseMap
        (data.factorization.representedMetricBlock data.representation coordinates
          data.refinement parameter)
        (data.factorization.representedAbelianBlock data.representation coordinates
          data.refinement parameter)
        (data.factorization.representedMatterBlock data.representation coordinates
          data.refinement parameter)
        (data.factorization.representedLongitudinalBlock data.representation coordinates
          data.refinement parameter)
        (data.factorization.representedBoundaryBlock data.representation coordinates
          data.refinement parameter)
        (coordinates.decomposition state) := by
  rw [data.operator_blockFormula parameter state]
  rcases coordinates.decomposition state with
    ⟨metric, abelian, matter, longitudinal, boundary⟩
  rfl

private theorem decomposition_sectorProjector_eq_raw
    {operator : Parameter → State →L[Real] State}
    {coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary)}
    (_data : FiveSectorNaturalLinearBaseFamilyData
      (family := family) operator coordinates)
    (sector : FivePhysicalSector) (state : State) :
    coordinates.decomposition (coordinates.sectorProjector sector state) =
      fiveSectorProductProjector sector (coordinates.decomposition state) := by
  cases sector <;>
    simp [fiveSectorProductProjector,
      FiveSectorHilbertCoordinates.decomposition_sectorProjector,
      fiveSectorMetricAxis, fiveSectorAbelianAxis, fiveSectorMatterAxis,
      fiveSectorLongitudinalAxis, fiveSectorBoundaryAxis]

/-- Every operator in the multidimensional D11 family commutes with all five
physical projectors. -/
theorem operator_commutes_sectorProjector
    {operator : Parameter → State →L[Real] State}
    {coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary)}
    (data : FiveSectorNaturalLinearBaseFamilyData
      (family := family) operator coordinates)
    (parameter : Parameter) (sector : FivePhysicalSector) (state : State) :
    operator parameter (coordinates.sectorProjector sector state) =
      coordinates.sectorProjector sector (operator parameter state) := by
  apply coordinates.decomposition.injective
  rw [data.operator_componentwise parameter]
  rw [data.decomposition_sectorProjector_eq_raw sector]
  rw [fiveSectorComponentwiseMap_commutes_projector
    (data.factorization.representedMetricBlock data.representation coordinates
      data.refinement parameter)
    (data.factorization.representedAbelianBlock data.representation coordinates
      data.refinement parameter)
    (data.factorization.representedMatterBlock data.representation coordinates
      data.refinement parameter)
    (data.factorization.representedLongitudinalBlock data.representation coordinates
      data.refinement parameter)
    (data.factorization.representedBoundaryBlock data.representation coordinates
      data.refinement parameter)
    (data.metricBlock_zero parameter) (data.abelianBlock_zero parameter)
    (data.matterBlock_zero parameter) (data.longitudinalBlock_zero parameter)
    (data.boundaryBlock_zero parameter)]
  rw [← data.operator_componentwise parameter state]
  rw [← data.decomposition_sectorProjector_eq_raw sector state]

/-- Public multidimensional five-sector natural linear family checkpoint. -/
theorem five_sector_natural_linear_base_family_gate
    (operator : Parameter → State →L[Real] State)
    (coordinates : FiveSectorHilbertCoordinates
      (E := State) (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary))
    (data : FiveSectorNaturalLinearBaseFamilyData
      (family := family) operator coordinates) :
    (∀ parameter state,
      coordinates.decomposition (operator parameter state) =
        fiveSectorComponentwiseMap
          (data.factorization.representedMetricBlock data.representation coordinates
            data.refinement parameter)
          (data.factorization.representedAbelianBlock data.representation coordinates
            data.refinement parameter)
          (data.factorization.representedMatterBlock data.representation coordinates
            data.refinement parameter)
          (data.factorization.representedLongitudinalBlock data.representation coordinates
            data.refinement parameter)
          (data.factorization.representedBoundaryBlock data.representation coordinates
            data.refinement parameter)
          (coordinates.decomposition state)) ∧
    (∀ parameter sector state,
      operator parameter (coordinates.sectorProjector sector state) =
        coordinates.sectorProjector sector (operator parameter state)) :=
  ⟨data.operator_componentwise, data.operator_commutes_sectorProjector⟩

end FiveSectorNaturalLinearBaseFamilyData

end
end P0EFTJanusProgramPFiveSectorNaturalLinearBaseFamily4D
end JanusFormal
