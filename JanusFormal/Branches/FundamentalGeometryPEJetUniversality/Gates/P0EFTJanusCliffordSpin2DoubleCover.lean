import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusCliffordSpin2Bridge

namespace JanusFormal
namespace P0EFTJanusCliffordSpin2DoubleCover

set_option autoImplicit false

noncomputable section

open P0EFTJanusCentralLiftCocycleObstruction
open P0EFTJanusSpin2CircleModel
open P0EFTJanusCircleSO2Equivalence
open P0EFTJanusCliffordSpin2Bridge

universe u

/-- Mathlib's Clifford model of `Spin(2)` is commutative because it is group
isomorphic to the unit circle. -/
theorem cliffordSpin2_mul_comm
    (first second : CliffordSpin2) :
    first * second = second * first := by
  apply circleEquivCliffordSpin2.symm.toEquiv.injective
  simpa only [map_mul] using
    (mul_comm
      (circleEquivCliffordSpin2.symm.toFun first)
      (circleEquivCliffordSpin2.symm.toFun second))

/-- Distinguished central kernel element in the Clifford model. -/
def cliffordSpin2MinusOne : CliffordSpin2 :=
  circleEquivCliffordSpin2.toFun (-1)

@[simp]
theorem cliffordSpin2MinusOne_projection :
    cliffordSpin2ToMatrixSO2Projection.toFun
        cliffordSpin2MinusOne = 1 := by
  change
    cliffordSpin2ToMatrixSO2Projection.toFun
        (circleEquivCliffordSpin2.toFun (-1)) = 1
  rw [cliffordSpin2ToMatrixSO2Projection_circle]
  exact spin2ToMatrixSO2Projection_neg_one

/-- The distinguished Clifford kernel element is nontrivial. -/
theorem cliffordSpin2MinusOne_ne_one :
    cliffordSpin2MinusOne ≠ 1 := by
  intro hEqual
  apply circle_neg_one_ne_one
  have hTransported :=
    congrArg circleEquivCliffordSpin2.symm.toFun hEqual
  simpa [cliffordSpin2MinusOne] using hTransported

@[simp]
theorem cliffordSpin2MinusOne_sq :
    cliffordSpin2MinusOne * cliffordSpin2MinusOne = 1 := by
  apply circleEquivCliffordSpin2.symm.toEquiv.injective
  simp [cliffordSpin2MinusOne]

/-- Exact kernel theorem for the Clifford-valued Spin projection. -/
theorem cliffordSpin2_projection_eq_one_iff
    (rotor : CliffordSpin2) :
    cliffordSpin2ToMatrixSO2Projection.toFun rotor = 1 ↔
      rotor = 1 ∨ rotor = cliffordSpin2MinusOne := by
  constructor
  · intro hKernel
    have hFiber :
        cliffordSpin2ToMatrixSO2Projection.toFun rotor =
          cliffordSpin2ToMatrixSO2Projection.toFun 1 := by
      simpa using hKernel
    have hCases :=
      (cliffordSpin2ToMatrixSO2Projection_eq_iff rotor 1).1 hFiber
    simpa [cliffordSpin2MinusOne] using hCases
  · rintro (rfl | rfl)
    · simp
    · exact cliffordSpin2MinusOne_projection

/-- The transported Clifford projection is an actual central double cover in the
abstract cocycle interface. -/
def cliffordSpin2MatrixCentralDoubleCover :
    CentralDoubleCoverData CliffordSpin2 MatrixSO2 where
  projection := cliffordSpin2ToMatrixSO2Projection
  kernel_central := by
    intro kernelElement hKernel spinElement
    exact cliffordSpin2_mul_comm kernelElement spinElement
  minusOne := cliffordSpin2MinusOne
  minusOne_mem_kernel := cliffordSpin2MinusOne_projection
  minusOne_ne_one := cliffordSpin2MinusOne_ne_one
  minusOne_sq := cliffordSpin2MinusOne_sq
  kernel_dichotomy := by
    intro rotor hKernel
    exact (cliffordSpin2_projection_eq_one_iff rotor).1 hKernel

/-- The same projection packaged in the rank-two SpinC quotient interface. -/
def cliffordSpin2DoubleCoverData :
    Spin2DoubleCoverData CliffordSpin2 MatrixSO2 where
  projection := cliffordSpin2ToMatrixSO2Projection
  central_minusOne := by
    intro rotor
    exact cliffordSpin2_mul_comm cliffordSpin2MinusOne rotor
  projection_minusOne := cliffordSpin2MinusOne_projection
  minusOne_ne_one := cliffordSpin2MinusOne_ne_one
  minusOne_square := cliffordSpin2MinusOne_sq
  projection_surjective :=
    cliffordSpin2ToMatrixSO2Projection_surjective
  projection_kernel := by
    intro rotor hKernel
    exact (cliffordSpin2_projection_eq_one_iff rotor).1 hKernel

/-- Concrete rank-two SpinC group obtained by quotienting
`CliffordSpin2 × U(1)` by the diagonal central sign. -/
abbrev CliffordSpinC2 :=
  Spin2SpinCQuotient cliffordSpin2DoubleCoverData

/-- Projection from the concrete Clifford SpinC quotient to matrix `SO(2)`. -/
def cliffordSpinC2Projection : CliffordSpinC2 →* MatrixSO2 :=
  spin2SpinCProjection cliffordSpin2DoubleCoverData

/-- The concrete Clifford SpinC projection is surjective. -/
theorem cliffordSpinC2Projection_surjective :
    Function.Surjective cliffordSpinC2Projection.toFun :=
  spin2SpinCProjection_surjective cliffordSpin2DoubleCoverData

/-- The kernel of the Clifford SpinC projection is canonically the gauge circle. -/
def cliffordSpinC2KernelEquivCircle :
    {value : CliffordSpinC2 //
      cliffordSpinC2Projection.toFun value = 1} ≃* Circle :=
  spin2SpinCKernelEquivCircle cliffordSpin2DoubleCoverData

/-- For actual Clifford-valued frame lifts, the SpinC cocycle condition is
exactly cancellation of the frame and gauge sign defects. -/
theorem cliffordSpin2_spinC_cocycle_iff_defects_cancel
    {Index : Type u}
    (frameTransition : Index → Index → MatrixSO2)
    (frameLift : Index → Index → CliffordSpin2)
    (gaugeTransition : Index → Index → Circle)
    (gaugeLift : Index → Index → Circle)
    (frameDefect gaugeDefect : Index → Index → Index → Bool)
    (hFrameLift :
      ∀ first second,
        cliffordSpin2ToMatrixSO2Projection.toFun
            (frameLift first second) =
          frameTransition first second)
    (hGaugeLift :
      ∀ first second,
        circleSquareHom.toFun (gaugeLift first second) =
          gaugeTransition first second)
    (hFrameDefect :
      ∀ first second third,
        frameLift first second * frameLift second third =
          boolSpin cliffordSpin2DoubleCoverData
              (frameDefect first second third) *
            frameLift first third)
    (hGaugeDefect :
      ∀ first second third,
        gaugeLift first second * gaugeLift second third =
          boolSign (gaugeDefect first second third) *
            gaugeLift first third) :
    SpinCLiftedCocycle frameLift gaugeLift ↔
      gaugeDefect = Circle.inv frameDefect :=
  spin2SpinC_cocycle_iff_defects_cancel
    cliffordSpin2DoubleCoverData
    frameTransition frameLift gaugeTransition gaugeLift
    frameDefect gaugeDefect
    hFrameLift hGaugeLift hFrameDefect hGaugeDefect

/-- Exact progress boundary after promoting the algebraic Clifford bridge to the
central-double-cover and SpinC quotient interfaces. -/
structure CliffordSpin2DoubleCoverStatus where
  cliffordSpinGroupCommutativityProved : Prop
  distinguishedCentralSignConstructed : Prop
  exactProjectionKernelProved : Prop
  centralDoubleCoverPackaged : Prop
  spinCDiagonalQuotientConstructed : Prop
  spinCProjectionSurjective : Prop
  spinCProjectionKernelIdentifiedWithCircle : Prop
  spinCCocycleDefectCancellationProved : Prop
  smoothCoveringMapProved : Prop
  principalSpinCBundleConstructed : Prop

/-- Closure of the geometric rank-two Clifford SpinC double-cover stage. -/
def cliffordSpin2DoubleCoverClosed
    (s : CliffordSpin2DoubleCoverStatus) : Prop :=
  s.cliffordSpinGroupCommutativityProved /\
  s.distinguishedCentralSignConstructed /\
  s.exactProjectionKernelProved /\
  s.centralDoubleCoverPackaged /\
  s.spinCDiagonalQuotientConstructed /\
  s.spinCProjectionSurjective /\
  s.spinCProjectionKernelIdentifiedWithCircle /\
  s.spinCCocycleDefectCancellationProved /\
  s.smoothCoveringMapProved /\
  s.principalSpinCBundleConstructed

/-- The exact group extension still does not supply a smooth principal SpinC
bundle over the Janus frame bundle. -/
theorem missing_principal_spinC_bundle_blocks_geometric_stage
    (s : CliffordSpin2DoubleCoverStatus)
    (hMissing : Not s.principalSpinCBundleConstructed) :
    Not (cliffordSpin2DoubleCoverClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.2.2.2

end

end P0EFTJanusCliffordSpin2DoubleCover
end JanusFormal
