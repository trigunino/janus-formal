import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatrixInteractionDensityCovariance

/-!
# Finite-field lift of the diagonal local-frame symmetry

The pointwise bimetric root data are promoted to a field over an arbitrary
finite set of sites.  Each site has its own simultaneous invertible frame.
The inverse-frame determinant compensates the interaction-density weight, so
the finite weighted action is exactly invariant.

This is a finite field-space and local-frame result.  It is not a manifold
diffeomorphism action, an integral, or a covariant Bianchi identity.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteFieldLocalFrameGauge

set_option autoImplicit false

noncomputable section

open P0EFTJanusMatrixSquareRootInteractionDensity
open P0EFTJanusMatrixDiagonalGaugeNoether
open P0EFTJanusMatrixInteractionDensityCovariance
open P0EFTJanusReciprocalBimetricPotential

abbrev Matrix4 :=
  P0EFTJanusMatrixSquareRootInteractionDensity.Matrix4

abbrev FiniteBimetricRootField (Site : Type*) :=
  Site → PointwiseBimetricRootData

/-- Sitewise diagonal frame action.  The same local frame acts on both metric
sectors and on the relative root at each site. -/
def localDiagonalFrameAction
    {Site : Type*}
    (frame inverse : Site → Matrix4)
    (hFrame : ∀ site, FrameInverseWitness (frame site) (inverse site))
    (field : FiniteBimetricRootField Site) :
    FiniteBimetricRootField Site :=
  fun site => diagonalFrameAction (frame site) (inverse site)
    (hFrame site) (field site)

/-- Finite weighted interaction action. -/
def finiteInteractionAction
    {Site : Type*} [Fintype Site]
    (interactionScale : ℝ) (coefficients : PotentialCoefficients)
    (coordinateWeight : Site → ℝ)
    (field : FiniteBimetricRootField Site) : ℝ :=
  ∑ site, coordinateWeight site *
    pointwiseInteractionDensity interactionScale coefficients (field site)

/-- Each local inverse determinant compensates its transformed density. -/
theorem localInteractionDensity_inverseJacobian_compensated
    {Site : Type*}
    (interactionScale : ℝ) (coefficients : PotentialCoefficients)
    (frame inverse : Site → Matrix4)
    (hFrame : ∀ site, FrameInverseWitness (frame site) (inverse site))
    (field : FiniteBimetricRootField Site) (site : Site) :
    |Matrix.det (inverse site)| *
        pointwiseInteractionDensity interactionScale coefficients
          (localDiagonalFrameAction frame inverse hFrame field site) =
      pointwiseInteractionDensity interactionScale coefficients
        (field site) := by
  exact pointwiseInteractionDensity_inverseJacobian_compensated
    interactionScale coefficients (frame site) (inverse site)
      (hFrame site) (field site)

/-- Exact invariance of the finite action under independent sitewise diagonal
frames, with the coordinate weight transformed by the inverse Jacobian. -/
theorem finiteInteractionAction_localDiagonal_invariant
    {Site : Type*} [Fintype Site]
    (interactionScale : ℝ) (coefficients : PotentialCoefficients)
    (coordinateWeight : Site → ℝ)
    (frame inverse : Site → Matrix4)
    (hFrame : ∀ site, FrameInverseWitness (frame site) (inverse site))
    (field : FiniteBimetricRootField Site) :
    finiteInteractionAction interactionScale coefficients
        (fun site => coordinateWeight site * |Matrix.det (inverse site)|)
        (localDiagonalFrameAction frame inverse hFrame field) =
      finiteInteractionAction interactionScale coefficients coordinateWeight
        field := by
  classical
  unfold finiteInteractionAction
  apply Finset.sum_congr rfl
  intro site _
  change
    (coordinateWeight site * |Matrix.det (inverse site)|) *
        pointwiseInteractionDensity interactionScale coefficients
          (localDiagonalFrameAction frame inverse hFrame field site) =
      coordinateWeight site *
        pointwiseInteractionDensity interactionScale coefficients (field site)
  rw [mul_assoc,
    localInteractionDensity_inverseJacobian_compensated interactionScale
      coefficients frame inverse hFrame field site]

/-- The allowed local symmetry is genuinely diagonal: the already proved
one-site independent-frame counterexample remains a rejection witness. -/
theorem independent_sheet_frames_not_a_local_gauge_symmetry :
    matrixSpectralPotential traceOnlyCoefficients
        (independentRootAction 1 doubledFrame 1) ≠
      matrixSpectralPotential traceOnlyCoefficients (1 : Matrix4) :=
  independent_frame_interaction_counterexample

end

end P0EFTJanusFiniteFieldLocalFrameGauge
end JanusFormal
