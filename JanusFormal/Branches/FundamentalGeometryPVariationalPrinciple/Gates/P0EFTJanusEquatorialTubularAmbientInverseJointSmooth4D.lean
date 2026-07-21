import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusEquatorialTubularOpenEmbedding4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicCoverLorentzTensor4D

namespace JanusFormal
namespace P0EFTJanusEquatorialTubularAmbientInverseJointSmooth4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff
open TopologicalSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusIntrinsicCoverLorentzTensor4D
open P0EFTJanusMappingTorusEquatorialTubularCoverInjectivity4D
open P0EFTJanusEquatorialTubularRawInverseSmooth4D
open P0EFTJanusEquatorialTubularRangeEquiv4D
open P0EFTJanusEquatorialTubularOpenEmbedding4D

def equatorialSphericalBandOpen : Opens UnitThreeSphere :=
  ⟨EquatorialSphericalBand, by
    simpa [equatorialTubularImage_eq_band] using equatorialTubularImage_isOpen⟩

def unitThreeSphereRawCoordinates (point : UnitThreeSphere) : Fin 4 → Real :=
  EuclideanSpace.equiv (Fin 4) Real (sphereAmbientMap point)

theorem unitThreeSphereRawCoordinates_eq (point : UnitThreeSphere) :
    unitThreeSphereRawCoordinates point = point.1 := by
  exact (EuclideanSpace.equiv (Fin 4) Real).apply_symm_apply point.1

theorem unitThreeSphereRawCoordinates_contMDiff :
    ContMDiff (𝓡 3) 𝓘(Real, Fin 4 → Real) ∞ unitThreeSphereRawCoordinates := by
  exact (EuclideanSpace.equiv (Fin 4) Real).contDiff.contMDiff.comp
    sphereAmbientMap_contMDiff

def equatorialTubularAmbientInverse
    (point : equatorialSphericalBandOpen) : (Fin 3 → Real) × Real :=
  (rawEquatorialTubularTailInverse (unitThreeSphereRawCoordinates point.1),
    rawEquatorialTubularNormalInverse (unitThreeSphereRawCoordinates point.1))

theorem equatorialTubularAmbientInverse_eq (point : equatorialSphericalBandOpen) :
    equatorialTubularAmbientInverse point =
      (rawEquatorialTubularTailInverse point.1.1,
        rawEquatorialTubularNormalInverse point.1.1) := by
  rw [equatorialTubularAmbientInverse, unitThreeSphereRawCoordinates_eq]

theorem equatorialTubularAmbientInverse_contMDiff :
    ContMDiff (𝓡 3) (𝓘(Real, Fin 3 → Real).prod 𝓘(Real, Real)) ∞
      equatorialTubularAmbientInverse := by
  have hInput : ContMDiff (𝓡 3) 𝓘(Real, Fin 4 → Real) ∞
      (unitThreeSphereRawCoordinates ∘
        (Subtype.val : equatorialSphericalBandOpen → UnitThreeSphere)) :=
    unitThreeSphereRawCoordinates_contMDiff.comp contMDiff_subtype_val
  have hMaps : Set.univ ⊆
      (unitThreeSphereRawCoordinates ∘
        (Subtype.val : equatorialSphericalBandOpen → UnitThreeSphere)) ⁻¹'
          RawSphericalTubularBand := by
    intro point _
    change |unitThreeSphereRawCoordinates point.1 0| < 1
    rw [unitThreeSphereRawCoordinates_eq]
    exact point.2
  apply ContMDiff.prodMk
  · rw [← contMDiffOn_univ]
    intro point _
    have hRaw := rawEquatorialTubularTailInverse_contDiffOn
      (unitThreeSphereRawCoordinates point.1) (hMaps (Set.mem_univ point))
    have hAt := ContDiffWithinAt.comp_contMDiffWithinAt
      (f := unitThreeSphereRawCoordinates ∘
        (Subtype.val : equatorialSphericalBandOpen → UnitThreeSphere))
      (s := Set.univ) (t := RawSphericalTubularBand) hRaw
      (hInput.contMDiffOn point (Set.mem_univ point)) hMaps
    exact hAt
  · rw [← contMDiffOn_univ]
    intro point _
    have hRaw := rawEquatorialTubularNormalInverse_contDiffOn
      (unitThreeSphereRawCoordinates point.1) (hMaps (Set.mem_univ point))
    have hAt := ContDiffWithinAt.comp_contMDiffWithinAt
      (f := unitThreeSphereRawCoordinates ∘
        (Subtype.val : equatorialSphericalBandOpen → UnitThreeSphere))
      (s := Set.univ) (t := RawSphericalTubularBand) hRaw
      (hInput.contMDiffOn point (Set.mem_univ point)) hMaps
    exact hAt

end
end P0EFTJanusEquatorialTubularAmbientInverseJointSmooth4D
end JanusFormal
