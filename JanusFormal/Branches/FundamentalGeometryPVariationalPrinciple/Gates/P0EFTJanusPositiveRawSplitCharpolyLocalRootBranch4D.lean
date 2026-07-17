import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPositiveRawSplitCharpolySylvesterClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusLorentzLocalRootBranch4D

/-!
# Local IFT branches on the positive split raw locus

At every strictly positive split raw matrix, the selected regular root makes
matrix squaring a genuine local homeomorphism.  Its inverse is an exact,
continuous local square-root branch with inverse-Sylvester derivative at the
centre.  Two such branches agree on any overlap where both selected roots
remain in the corresponding IFT uniqueness sources.

No continuity of the classical pointwise selector as the centre varies is
asserted.
-/

namespace JanusFormal
namespace P0EFTJanusPositiveRawSplitCharpolyLocalRootBranch4D

set_option autoImplicit false

noncomputable section

open scoped Matrix.Norms.Frobenius RightActions Topology
open P0EFTJanusMatrixSquareRootFrechetSylvester
open P0EFTJanusLorentzLocalRootBranch4D
open P0EFTJanusPositiveRawSplitCharpolySylvesterClosure4D
open P0EFTJanusPositiveRealJordanPresentationBridge4D

abbrev Matrix4 :=
  P0EFTJanusPositiveRawSplitCharpolySylvesterClosure4D.Matrix4

local instance matrix4NormedAddCommGroup : NormedAddCommGroup Matrix4 :=
  Matrix.frobeniusNormedAddCommGroup

local instance matrix4AddCommGroup : AddCommGroup Matrix4 :=
  matrix4NormedAddCommGroup.toAddCommGroup

local instance matrix4TopologicalSpace : TopologicalSpace Matrix4 :=
  matrix4NormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

local instance matrix4NormedSpace : NormedSpace Real Matrix4 :=
  Matrix.frobeniusNormedSpace

local instance matrix4Module : Module Real Matrix4 :=
  matrix4NormedSpace.toModule

/-- The selected Sylvester operator as a continuous linear equivalence. -/
def positiveRawSylvesterEquiv
    (target : Matrix4) (hSpectrum : PositiveRealSplitCharpoly4 target) :
    Matrix4 ≃L[Real] Matrix4 :=
  (LinearEquiv.ofBijective
    (sylvesterOperator (positiveRawRegularRoot target hSpectrum)).toLinearMap
    (positiveRawRegularRoot_sylvester_bijective target hSpectrum)).toContinuousLinearEquiv

def positiveRawSylvesterEquivWitness
    (target : Matrix4) (hSpectrum : PositiveRealSplitCharpoly4 target) :
    SylvesterEquivWitness (positiveRawRegularRoot target hSpectrum) where
  equiv := positiveRawSylvesterEquiv target hSpectrum
  forward_eq := rfl

/-- Explicit open target neighbourhood of the raw matrix. -/
def positiveRawLocalRootTarget
    (target : Matrix4) (hSpectrum : PositiveRealSplitCharpoly4 target) :
    Set Matrix4 :=
  (localSquareChart (positiveRawRegularRoot target hSpectrum)
    (positiveRawSylvesterEquivWitness target hSpectrum)).target

/-- Matching IFT uniqueness neighbourhood of the selected root. -/
def positiveRawLocalRootSource
    (target : Matrix4) (hSpectrum : PositiveRealSplitCharpoly4 target) :
    Set Matrix4 :=
  (localSquareChart (positiveRawRegularRoot target hSpectrum)
    (positiveRawSylvesterEquivWitness target hSpectrum)).source

theorem positiveRawLocalRootTarget_isOpen
    (target : Matrix4) (hSpectrum : PositiveRealSplitCharpoly4 target) :
    IsOpen (positiveRawLocalRootTarget target hSpectrum) :=
  (localSquareChart (positiveRawRegularRoot target hSpectrum)
    (positiveRawSylvesterEquivWitness target hSpectrum)).open_target

theorem positiveRawLocalRootSource_isOpen
    (target : Matrix4) (hSpectrum : PositiveRealSplitCharpoly4 target) :
    IsOpen (positiveRawLocalRootSource target hSpectrum) :=
  (localSquareChart (positiveRawRegularRoot target hSpectrum)
    (positiveRawSylvesterEquivWitness target hSpectrum)).open_source

theorem target_mem_positiveRawLocalRootTarget
    (target : Matrix4) (hSpectrum : PositiveRealSplitCharpoly4 target) :
    target ∈ positiveRawLocalRootTarget target hSpectrum := by
  have hBase : matrixSquare (positiveRawRegularRoot target hSpectrum) = target := by
    change positiveRawRegularRoot target hSpectrum *
      positiveRawRegularRoot target hSpectrum = target
    exact positiveRawRegularRoot_square target hSpectrum
  change target ∈
    (localSquareChart (positiveRawRegularRoot target hSpectrum)
      (positiveRawSylvesterEquivWitness target hSpectrum)).target
  have hMembership := square_mem_localSquareChart_target
    (positiveRawRegularRoot target hSpectrum)
    (positiveRawSylvesterEquivWitness target hSpectrum)
  rw [hBase] at hMembership
  exact hMembership

/-- The actual local inverse-function root branch at the selected raw root. -/
def positiveRawLocalRootBranch
    (target : Matrix4) (hSpectrum : PositiveRealSplitCharpoly4 target) :
    Matrix4 → Matrix4 :=
  localRootBranch (positiveRawRegularRoot target hSpectrum)
    (positiveRawSylvesterEquivWitness target hSpectrum)

theorem positiveRawLocalRootBranch_at_center
    (target : Matrix4) (hSpectrum : PositiveRealSplitCharpoly4 target) :
    positiveRawLocalRootBranch target hSpectrum target =
      positiveRawRegularRoot target hSpectrum := by
  have hBase : matrixSquare (positiveRawRegularRoot target hSpectrum) = target := by
    change positiveRawRegularRoot target hSpectrum *
      positiveRawRegularRoot target hSpectrum = target
    exact positiveRawRegularRoot_square target hSpectrum
  change localRootBranch (positiveRawRegularRoot target hSpectrum)
      (positiveRawSylvesterEquivWitness target hSpectrum) target =
    positiveRawRegularRoot target hSpectrum
  calc
    localRootBranch (positiveRawRegularRoot target hSpectrum)
        (positiveRawSylvesterEquivWitness target hSpectrum) target =
      localRootBranch (positiveRawRegularRoot target hSpectrum)
        (positiveRawSylvesterEquivWitness target hSpectrum)
        (matrixSquare (positiveRawRegularRoot target hSpectrum)) := by
          rw [hBase]
    _ = positiveRawRegularRoot target hSpectrum :=
      localRootBranch_at_base (positiveRawRegularRoot target hSpectrum)
        (positiveRawSylvesterEquivWitness target hSpectrum)

theorem positiveRawLocalRootBranch_square
    {target nearby : Matrix4}
    {hSpectrum : PositiveRealSplitCharpoly4 target}
    (hNearby : nearby ∈ positiveRawLocalRootTarget target hSpectrum) :
    matrixSquare (positiveRawLocalRootBranch target hSpectrum nearby) = nearby := by
  change
    (localSquareChart (positiveRawRegularRoot target hSpectrum)
      (positiveRawSylvesterEquivWitness target hSpectrum))
        ((localSquareChart (positiveRawRegularRoot target hSpectrum)
          (positiveRawSylvesterEquivWitness target hSpectrum)).symm nearby) =
      nearby
  exact (localSquareChart (positiveRawRegularRoot target hSpectrum)
    (positiveRawSylvesterEquivWitness target hSpectrum)).right_inv hNearby

theorem positiveRawLocalRootBranch_mem_source
    {target nearby : Matrix4}
    {hSpectrum : PositiveRealSplitCharpoly4 target}
    (hNearby : nearby ∈ positiveRawLocalRootTarget target hSpectrum) :
    positiveRawLocalRootBranch target hSpectrum nearby ∈
      positiveRawLocalRootSource target hSpectrum := by
  exact (localSquareChart (positiveRawRegularRoot target hSpectrum)
    (positiveRawSylvesterEquivWitness target hSpectrum)).map_target hNearby

theorem positiveRawLocalRootBranch_continuousOn
    (target : Matrix4) (hSpectrum : PositiveRealSplitCharpoly4 target) :
    ContinuousOn (positiveRawLocalRootBranch target hSpectrum)
      (positiveRawLocalRootTarget target hSpectrum) :=
  (localSquareChart (positiveRawRegularRoot target hSpectrum)
    (positiveRawSylvesterEquivWitness target hSpectrum)).continuousOn_symm

theorem positiveRawLocalRootBranch_hasStrictFDerivAt
    (target : Matrix4) (hSpectrum : PositiveRealSplitCharpoly4 target) :
    MatrixHasStrictFDerivAt (positiveRawLocalRootBranch target hSpectrum)
      ((positiveRawSylvesterEquiv target hSpectrum).symm :
        Matrix4 →L[Real] Matrix4) target := by
  have hBase : matrixSquare (positiveRawRegularRoot target hSpectrum) = target := by
    change positiveRawRegularRoot target hSpectrum *
      positiveRawRegularRoot target hSpectrum = target
    exact positiveRawRegularRoot_square target hSpectrum
  change MatrixHasStrictFDerivAt
    (localRootBranch (positiveRawRegularRoot target hSpectrum)
      (positiveRawSylvesterEquivWitness target hSpectrum))
    ((positiveRawSylvesterEquiv target hSpectrum).symm :
      Matrix4 →L[Real] Matrix4) target
  have hDerivative := localRootBranch_hasStrictFDerivAt
    (positiveRawRegularRoot target hSpectrum)
    (positiveRawSylvesterEquivWitness target hSpectrum)
  rw [hBase] at hDerivative
  exact hDerivative

theorem positiveRawLocalRootBranch_hasFDerivAt
    (target : Matrix4) (hSpectrum : PositiveRealSplitCharpoly4 target) :
    MatrixHasFDerivAt (positiveRawLocalRootBranch target hSpectrum)
      ((positiveRawSylvesterEquiv target hSpectrum).symm :
        Matrix4 →L[Real] Matrix4) target :=
  (positiveRawLocalRootBranch_hasStrictFDerivAt target hSpectrum).hasFDerivAt

theorem positiveRawLocalRootBranch_derivative_solves_sylvester
    (target : Matrix4) (hSpectrum : PositiveRealSplitCharpoly4 target)
    (variation : Matrix4) :
    sylvesterMap (positiveRawRegularRoot target hSpectrum)
        ((positiveRawSylvesterEquiv target hSpectrum).symm variation) =
      variation :=
  inverseSylvester_right (positiveRawRegularRoot target hSpectrum)
    (positiveRawSylvesterEquivWitness target hSpectrum) variation

/-- Open overlap on which both branches land in both IFT uniqueness sources. -/
def positiveRawLocalRootOverlap
    (first : Matrix4) (hFirst : PositiveRealSplitCharpoly4 first)
    (second : Matrix4) (hSecond : PositiveRealSplitCharpoly4 second) :
    Set Matrix4 :=
  (((positiveRawLocalRootTarget first hFirst ∩
      positiveRawLocalRootTarget second hSecond) ∩
    positiveRawLocalRootBranch first hFirst ⁻¹'
      positiveRawLocalRootSource second hSecond) ∩
    positiveRawLocalRootBranch second hSecond ⁻¹'
      positiveRawLocalRootSource first hFirst)

theorem positiveRawLocalRootOverlap_isOpen
    (first : Matrix4) (hFirst : PositiveRealSplitCharpoly4 first)
    (second : Matrix4) (hSecond : PositiveRealSplitCharpoly4 second) :
    IsOpen (positiveRawLocalRootOverlap first hFirst second hSecond) := by
  have hTargetsOpen : IsOpen
      (positiveRawLocalRootTarget first hFirst ∩
        positiveRawLocalRootTarget second hSecond) :=
    (positiveRawLocalRootTarget_isOpen first hFirst).inter
      (positiveRawLocalRootTarget_isOpen second hSecond)
  have hFirstContinuous : ContinuousOn
      (positiveRawLocalRootBranch first hFirst)
      (positiveRawLocalRootTarget first hFirst ∩
        positiveRawLocalRootTarget second hSecond) :=
    (positiveRawLocalRootBranch_continuousOn first hFirst).mono
      (fun _ hPoint => hPoint.1)
  have hFirstRestrictedOpen : IsOpen
      ((positiveRawLocalRootTarget first hFirst ∩
          positiveRawLocalRootTarget second hSecond) ∩
        positiveRawLocalRootBranch first hFirst ⁻¹'
          positiveRawLocalRootSource second hSecond) :=
    hFirstContinuous.isOpen_inter_preimage hTargetsOpen
      (positiveRawLocalRootSource_isOpen second hSecond)
  have hSecondContinuous : ContinuousOn
      (positiveRawLocalRootBranch second hSecond)
      ((positiveRawLocalRootTarget first hFirst ∩
          positiveRawLocalRootTarget second hSecond) ∩
        positiveRawLocalRootBranch first hFirst ⁻¹'
          positiveRawLocalRootSource second hSecond) :=
    (positiveRawLocalRootBranch_continuousOn second hSecond).mono
      (fun _ hPoint => hPoint.1.2)
  exact hSecondContinuous.isOpen_inter_preimage hFirstRestrictedOpen
    (positiveRawLocalRootSource_isOpen first hFirst)

/-- Exact gluing on overlaps inside both local uniqueness neighbourhoods. -/
theorem positiveRawLocalRootBranches_eq_on_overlap
    {first second nearby : Matrix4}
    {hFirst : PositiveRealSplitCharpoly4 first}
    {hSecond : PositiveRealSplitCharpoly4 second}
    (hNearby : nearby ∈
      positiveRawLocalRootOverlap first hFirst second hSecond) :
    positiveRawLocalRootBranch first hFirst nearby =
      positiveRawLocalRootBranch second hSecond nearby := by
  apply (localSquareChart (positiveRawRegularRoot first hFirst)
    (positiveRawSylvesterEquivWitness first hFirst)).injOn
  · exact positiveRawLocalRootBranch_mem_source hNearby.1.1.1
  · exact hNearby.2
  · change matrixSquare (positiveRawLocalRootBranch first hFirst nearby) =
      matrixSquare (positiveRawLocalRootBranch second hSecond nearby)
    rw [positiveRawLocalRootBranch_square hNearby.1.1.1,
      positiveRawLocalRootBranch_square hNearby.1.1.2]

end

end P0EFTJanusPositiveRawSplitCharpolyLocalRootBranch4D
end JanusFormal
