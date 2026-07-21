import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.Instances.ZMod
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAmbientPinMinusProjection4D

/-!
# The inherited finite-dimensional topology on the ambient Pin-minus group

The ambient Clifford algebra is linearly identified with the exterior
algebra on the genuine four-dimensional cover tangent.  The exterior basis
therefore gives sixteen real Clifford coordinates.  We use the faithful left
regular matrix representation in those coordinates to induce a norm on the
Clifford algebra, and give `Pin⁻(4)` the resulting subtype topology.

This is the ordinary finite-dimensional coordinate topology: it is induced
by an injective algebra representation into real `16 × 16` matrices.  No
discrete, indiscrete or proposition-only topology is introduced.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusAmbientPinMinusTopologicalGroup4D

set_option autoImplicit false

noncomputable section

open CliffordAlgebra Module Topology
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusAmbientPinMinusProjection4D

open scoped Matrix.Norms.Operator

/-- A concrete four-element basis of the actual cover tangent space. -/
private def ambientPinMinusCoverBasis :
    Basis (Fin 4) Real CoverCoordinates :=
  Module.finBasisOfFinrankEq Real CoverCoordinates (by
    norm_num [CoverCoordinates])

/-- The sixteen PBW coordinates obtained from the exterior-algebra basis. -/
def ambientPinMinusCliffordBasis :
    Basis (Finset (Fin 4)) Real AmbientPinMinusCliffordAlgebra :=
  (ambientPinMinusCoverBasis.ExteriorAlgebra).map
    (CliffordAlgebra.equivExterior
      ambientCoverPinMinusQuadraticForm).symm

abbrev AmbientPinMinusCliffordCoordinateMatrix :=
  Matrix (Finset (Fin 4)) (Finset (Fin 4)) Real

/-- Faithful real matrix coordinates, given by left Clifford multiplication. -/
def ambientPinMinusCliffordLeftRegularCoordinates :
    AmbientPinMinusCliffordAlgebra →ₐ[Real]
      AmbientPinMinusCliffordCoordinateMatrix :=
  Algebra.leftMulMatrix ambientPinMinusCliffordBasis

theorem ambientPinMinusCliffordLeftRegularCoordinates_injective :
    Function.Injective ambientPinMinusCliffordLeftRegularCoordinates :=
  Algebra.leftMulMatrix_injective ambientPinMinusCliffordBasis

/-- The faithful coordinate norm on the actual Clifford algebra. -/
noncomputable instance ambientPinMinusCliffordNormedRing :
    NormedRing AmbientPinMinusCliffordAlgebra :=
  NormedRing.induced AmbientPinMinusCliffordAlgebra
    AmbientPinMinusCliffordCoordinateMatrix
    ambientPinMinusCliffordLeftRegularCoordinates
    ambientPinMinusCliffordLeftRegularCoordinates_injective

/-- The same coordinate norm is compatible with the real vector-space
structure. -/
noncomputable instance ambientPinMinusCliffordNormedSpace :
    NormedSpace Real AmbientPinMinusCliffordAlgebra :=
  NormedSpace.induced Real AmbientPinMinusCliffordAlgebra
    AmbientPinMinusCliffordCoordinateMatrix
    ambientPinMinusCliffordLeftRegularCoordinates.toLinearMap

/-- The coordinate construction really exhibits the Clifford algebra as a
finite-dimensional real vector space. -/
noncomputable instance ambientPinMinusCliffordFiniteDimensional :
    FiniteDimensional Real AmbientPinMinusCliffordAlgebra :=
  ambientPinMinusCliffordBasis.finiteDimensional_of_finite

/-- The coordinate representation is an isometry for the induced norm, hence
the topology is exactly the inherited matrix-coordinate topology. -/
theorem ambientPinMinusCliffordLeftRegularCoordinates_isometry :
    Isometry ambientPinMinusCliffordLeftRegularCoordinates :=
  AddMonoidHomClass.isometry_of_norm
    ambientPinMinusCliffordLeftRegularCoordinates (fun _ => rfl)

/-- Clifford conjugation is continuous in the genuine finite-dimensional
coordinate topology. -/
theorem continuous_ambientPinMinusClifford_star :
    Continuous (fun value : AmbientPinMinusCliffordAlgebra => star value) := by
  have hContinuous : Continuous
      (CliffordAlgebra.reverse.comp
        (CliffordAlgebra.involute
          (Q := ambientCoverPinMinusQuadraticForm)).toLinearMap :
        AmbientPinMinusCliffordAlgebra →ₗ[Real]
          AmbientPinMinusCliffordAlgebra) :=
    LinearMap.continuous_of_finiteDimensional _
  simpa only [CliffordAlgebra.star_def, LinearMap.coe_comp,
    Function.comp_def, AlgHom.toLinearMap_apply] using hContinuous

/-- With the subtype topology inherited from Clifford coordinates, the actual
Mathlib `pinGroup` is a topological group.  Inversion is Clifford
conjugation, not an artificially assigned operation. -/
noncomputable instance ambientCoordinatePinMinusIsTopologicalGroup :
    IsTopologicalGroup AmbientCoordinatePinMinusGroup where
  continuous_mul := ContinuousMul.continuous_mul
  continuous_inv := by
    apply continuous_induced_rng.mpr
    change Continuous (fun lift : AmbientCoordinatePinMinusGroup =>
      star (lift : AmbientPinMinusCliffordAlgebra))
    exact continuous_ambientPinMinusClifford_star.comp continuous_subtype_val

/-- The inclusion of the Pin-minus group into its Clifford algebra is the
honest subtype embedding. -/
theorem ambientCoordinatePinMinus_coe_isEmbedding :
    IsEmbedding (fun lift : AmbientCoordinatePinMinusGroup =>
      (lift : AmbientPinMinusCliffordAlgebra)) :=
  IsEmbedding.subtypeVal

/-- The concrete order-four reference character is continuous for this
topology. -/
theorem continuous_ambientPinMinusReferenceZ4Character :
    Continuous ambientPinMinusReferenceZ4Character :=
  continuous_of_discreteTopology

end

end P0EFTJanusMappingTorusAmbientPinMinusTopologicalGroup4D
end JanusFormal
