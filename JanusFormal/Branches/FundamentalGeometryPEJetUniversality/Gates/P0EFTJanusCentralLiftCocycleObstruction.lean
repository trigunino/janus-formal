import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusDeterminantOrientedReduction

namespace JanusFormal
namespace P0EFTJanusCentralLiftCocycleObstruction

set_option autoImplicit false

noncomputable section

universe u v w

/-- Abstract central covering homomorphism. This is the exact algebraic structure
needed to discuss lifting transition cocycles before a concrete Clifford-theoretic
Spin-to-SO projection has been constructed. -/
structure CentralCoverData
    (LiftGroup : Type u) (BaseGroup : Type v)
    [Group LiftGroup] [Group BaseGroup] where
  projection : LiftGroup →* BaseGroup
  kernel_central :
    ∀ z : LiftGroup, z ∈ projection.ker →
      ∀ g : LiftGroup, z * g = g * z

/-- A group-valued Čech transition cocycle, using the convention
`g_jk * g_ij = g_ik`. -/
structure TransitionCocycle
    (Index : Type w) (GroupValue : Type v)
    [Group GroupValue] where
  transition : Index → Index → GroupValue
  transition_self : ∀ i, transition i i = 1
  transition_reverse : ∀ i j, transition j i = (transition i j)⁻¹
  transition_cocycle :
    ∀ i j k, transition j k * transition i j = transition i k

/-- A pointwise choice of lifts of a base transition cocycle. No cocycle law is
assumed upstairs. Its failure is measured by `liftDefect`. -/
structure ChosenTransitionLift
    {LiftGroup : Type u} {BaseGroup : Type v}
    [Group LiftGroup] [Group BaseGroup]
    {Index : Type w}
    (cover : CentralCoverData LiftGroup BaseGroup)
    (base : TransitionCocycle Index BaseGroup) where
  lift : Index → Index → LiftGroup
  projects :
    ∀ i j, cover.projection (lift i j) = base.transition i j

/-- Triple-overlap defect of chosen lifts. It is trivial exactly when the chosen
lifts satisfy the Čech cocycle law. -/
def liftDefect
    {LiftGroup : Type u} {BaseGroup : Type v}
    [Group LiftGroup] [Group BaseGroup]
    {Index : Type w}
    (cover : CentralCoverData LiftGroup BaseGroup)
    (base : TransitionCocycle Index BaseGroup)
    (chosen : ChosenTransitionLift cover base)
    (i j k : Index) : LiftGroup :=
  (chosen.lift j k * chosen.lift i j) * (chosen.lift i k)⁻¹

/-- Every triple-overlap defect lies in the kernel of the covering projection. -/
theorem liftDefect_mem_kernel
    {LiftGroup : Type u} {BaseGroup : Type v}
    [Group LiftGroup] [Group BaseGroup]
    {Index : Type w}
    (cover : CentralCoverData LiftGroup BaseGroup)
    (base : TransitionCocycle Index BaseGroup)
    (chosen : ChosenTransitionLift cover base)
    (i j k : Index) :
    liftDefect cover base chosen i j k ∈ cover.projection.ker := by
  change cover.projection (liftDefect cover base chosen i j k) = 1
  simp [liftDefect, chosen.projects, base.transition_cocycle]

/-- The defect is central because it belongs to the central kernel. -/
theorem liftDefect_central
    {LiftGroup : Type u} {BaseGroup : Type v}
    [Group LiftGroup] [Group BaseGroup]
    {Index : Type w}
    (cover : CentralCoverData LiftGroup BaseGroup)
    (base : TransitionCocycle Index BaseGroup)
    (chosen : ChosenTransitionLift cover base)
    (i j k : Index)
    (g : LiftGroup) :
    liftDefect cover base chosen i j k * g =
      g * liftDefect cover base chosen i j k :=
  cover.kernel_central _
    (liftDefect_mem_kernel cover base chosen i j k) g

/-- A chosen lift satisfies the upstairs transition cocycle law. -/
def IsLiftedCocycle
    {LiftGroup : Type u} {BaseGroup : Type v}
    [Group LiftGroup] [Group BaseGroup]
    {Index : Type w}
    (cover : CentralCoverData LiftGroup BaseGroup)
    (base : TransitionCocycle Index BaseGroup)
    (chosen : ChosenTransitionLift cover base) : Prop :=
  ∀ i j k, chosen.lift j k * chosen.lift i j = chosen.lift i k

/-- A triple defect is one exactly when the cocycle law holds on that triple. -/
theorem liftDefect_eq_one_iff
    {LiftGroup : Type u} {BaseGroup : Type v}
    [Group LiftGroup] [Group BaseGroup]
    {Index : Type w}
    (cover : CentralCoverData LiftGroup BaseGroup)
    (base : TransitionCocycle Index BaseGroup)
    (chosen : ChosenTransitionLift cover base)
    (i j k : Index) :
    liftDefect cover base chosen i j k = 1 ↔
      chosen.lift j k * chosen.lift i j = chosen.lift i k := by
  constructor
  · intro hDefect
    have hMultiply := congrArg
      (fun element : LiftGroup => element * chosen.lift i k) hDefect
    simpa [liftDefect, mul_assoc] using hMultiply
  · intro hCocycle
    rw [liftDefect, hCocycle]
    exact mul_inv_cancel _

/-- Vanishing of all defects is equivalent to the chosen lifts being a genuine
Čech cocycle. -/
theorem isLiftedCocycle_iff_defects_eq_one
    {LiftGroup : Type u} {BaseGroup : Type v}
    [Group LiftGroup] [Group BaseGroup]
    {Index : Type w}
    (cover : CentralCoverData LiftGroup BaseGroup)
    (base : TransitionCocycle Index BaseGroup)
    (chosen : ChosenTransitionLift cover base) :
    IsLiftedCocycle cover base chosen ↔
      ∀ i j k, liftDefect cover base chosen i j k = 1 := by
  constructor
  · intro hLift i j k
    exact (liftDefect_eq_one_iff cover base chosen i j k).2
      (hLift i j k)
  · intro hDefect i j k
    exact (liftDefect_eq_one_iff cover base chosen i j k).1
      (hDefect i j k)

/-- A central double cover: the kernel consists exactly of the identity and one
specified nontrivial central involution. This is the abstract algebraic pattern
of a Spin-to-SO double cover. -/
structure CentralDoubleCoverData
    (LiftGroup : Type u) (BaseGroup : Type v)
    [Group LiftGroup] [Group BaseGroup]
    extends CentralCoverData LiftGroup BaseGroup where
  minusOne : LiftGroup
  minusOne_mem_kernel : minusOne ∈ projection.ker
  minusOne_ne_one : minusOne ≠ 1
  minusOne_sq : minusOne * minusOne = 1
  kernel_dichotomy :
    ∀ z : LiftGroup, z ∈ projection.ker →
      z = 1 ∨ z = minusOne

/-- For a double cover, each triple-overlap defect is either trivial or the
nontrivial central kernel element. -/
theorem doubleCover_liftDefect_dichotomy
    {LiftGroup : Type u} {BaseGroup : Type v}
    [Group LiftGroup] [Group BaseGroup]
    {Index : Type w}
    (cover : CentralDoubleCoverData LiftGroup BaseGroup)
    (base : TransitionCocycle Index BaseGroup)
    (chosen : ChosenTransitionLift cover.toCentralCoverData base)
    (i j k : Index) :
    liftDefect cover.toCentralCoverData base chosen i j k = 1 ∨
      liftDefect cover.toCentralCoverData base chosen i j k =
        cover.minusOne :=
  cover.kernel_dichotomy _
    (liftDefect_mem_kernel cover.toCentralCoverData base chosen i j k)

/-- If no triple carries the nontrivial kernel defect, the chosen double-cover
lifts form a genuine cocycle. -/
theorem doubleCover_no_minusOne_defect_implies_liftedCocycle
    {LiftGroup : Type u} {BaseGroup : Type v}
    [Group LiftGroup] [Group BaseGroup]
    {Index : Type w}
    (cover : CentralDoubleCoverData LiftGroup BaseGroup)
    (base : TransitionCocycle Index BaseGroup)
    (chosen : ChosenTransitionLift cover.toCentralCoverData base)
    (hNoMinusOne :
      ∀ i j k,
        liftDefect cover.toCentralCoverData base chosen i j k ≠
          cover.minusOne) :
    IsLiftedCocycle cover.toCentralCoverData base chosen := by
  apply (isLiftedCocycle_iff_defects_eq_one
    cover.toCentralCoverData base chosen).2
  intro i j k
  rcases doubleCover_liftDefect_dichotomy cover base chosen i j k with
    hTrivial | hMinusOne
  · exact hTrivial
  · exact False.elim (hNoMinusOne i j k hMinusOne)

/-- The exact obstruction boundary: constructing local lifts is insufficient;
their central triple-overlap defect must vanish or be compensated by additional
SpinC determinant-line data. -/
structure CentralLiftObstructionStatus where
  orientedBaseCocycleConstructed : Prop
  centralCoverProjectionConstructed : Prop
  localTransitionLiftsChosen : Prop
  defectKernelMembershipProved : Prop
  defectCentralityProved : Prop
  defectVanishingCriterionProved : Prop
  doubleCoverKernelIdentified : Prop
  spinCoverInstantiatedFromCliffordAlgebra : Prop
  determinantLinePhaseCocycleConstructed : Prop
  spinCDefectCancellationProved : Prop
  globalSpinCCocycleConstructed : Prop

/-- Closure of the Spin/SpinC cocycle-lift stage. -/
def centralLiftObstructionClosed
    (s : CentralLiftObstructionStatus) : Prop :=
  s.orientedBaseCocycleConstructed /\
  s.centralCoverProjectionConstructed /\
  s.localTransitionLiftsChosen /\
  s.defectKernelMembershipProved /\
  s.defectCentralityProved /\
  s.defectVanishingCriterionProved /\
  s.doubleCoverKernelIdentified /\
  s.spinCoverInstantiatedFromCliffordAlgebra /\
  s.determinantLinePhaseCocycleConstructed /\
  s.spinCDefectCancellationProved /\
  s.globalSpinCCocycleConstructed

/-- Abstract defect theory does not by itself provide the concrete
Clifford-theoretic Spin cover. -/
theorem missing_concrete_spin_cover_blocks_spinC_cocycle
    (s : CentralLiftObstructionStatus)
    (hMissing : Not s.spinCoverInstantiatedFromCliffordAlgebra) :
    Not (centralLiftObstructionClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.2.1

end

end P0EFTJanusCentralLiftCocycleObstruction
end JanusFormal
