import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiveSectorOrthogonalProductResolution4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FourSectorOffDiagonalOperatorNorm4D

/-!
# Five coordinate sectors with a finite boundary factor

The first four factors are the completed Candidate-A diagonal graph types
`D`, `A`, `M`, and `L`.  The fifth is a finite space of face coordinates.
This construction makes no claim that those coordinates carry the physical
boundary/BV Hessian or a coercive quadratic form.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12FiveSectorBoundaryCoordinateHilbertResolution4D

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 900000
noncomputable section

open scoped BigOperators InnerProductSpace
open P0EFTJanusProgramPFiveSectorOrthogonalProductResolution4D

variable {D A M L NonNullFace NullFace : Type*}
variable [NormedAddCommGroup D] [InnerProductSpace Real D]
variable [NormedAddCommGroup A] [InnerProductSpace Real A]
variable [NormedAddCommGroup M] [InnerProductSpace Real M]
variable [NormedAddCommGroup L] [InnerProductSpace Real L]
variable [Fintype NonNullFace] [Fintype NullFace]

/-- Finite coordinates indexed by the two kinds of boundary face. -/
abbrev BoundaryFaceCoordinates (NonNullFace NullFace : Type*)
    [Fintype NonNullFace] [Fintype NullFace] :=
  EuclideanSpace Real (NonNullFace ⊕ NullFace)

/-- The four completed graph factors with an additional finite face coordinate. -/
abbrev FiveSectorFaceGraph (D A M L NonNullFace NullFace : Type*)
    [Fintype NonNullFace] [Fintype NullFace] :=
  WithLp 2 (D × WithLp 2 (A × WithLp 2
    (M × WithLp 2 (L × BoundaryFaceCoordinates NonNullFace NullFace))))

/-- Canonical continuous linear coordinates for the five-factor graph. -/
def faceGraphCoordinates :
    FiveSectorFaceGraph D A M L NonNullFace NullFace ≃L[Real]
      FiveSectorProduct D A M L (BoundaryFaceCoordinates NonNullFace NullFace) :=
  (WithLp.prodContinuousLinearEquiv 2 Real D _).trans
    ((ContinuousLinearEquiv.refl Real D).prodCongr
      ((WithLp.prodContinuousLinearEquiv 2 Real A _).trans
        ((ContinuousLinearEquiv.refl Real A).prodCongr
          ((WithLp.prodContinuousLinearEquiv 2 Real M _).trans
            ((ContinuousLinearEquiv.refl Real M).prodCongr
              (WithLp.prodContinuousLinearEquiv 2 Real L
                (BoundaryFaceCoordinates NonNullFace NullFace)))))))

/-- The coordinate equivalence preserves the five-factor sum inner product. -/
def faceGraphDecomposition :
    FiveSectorOrthogonalProductDecomposition
      (E := FiveSectorFaceGraph D A M L NonNullFace NullFace)
      (MetricDiffeomorphism := D) (AbelianGauge := A)
      (PrimitiveSpinCMatter := M) (LongitudinalLL := L)
      (BoundaryFiniteBV := BoundaryFaceCoordinates NonNullFace NullFace) where
  decomposition := faceGraphCoordinates
  inner_map := by
    intro first second
    simp [faceGraphCoordinates, fiveSectorProductInner,
      WithLp.prod_inner_apply, add_assoc]

/-- Five orthogonal, self-adjoint coordinate projectors resolving the identity. -/
theorem faceGraph_orthogonal_resolution :
    (∀ sector state,
      (faceGraphDecomposition (D := D) (A := A) (M := M) (L := L)
        (NonNullFace := NonNullFace) (NullFace := NullFace)).projection sector
          ((faceGraphDecomposition (D := D) (A := A) (M := M) (L := L)
            (NonNullFace := NonNullFace) (NullFace := NullFace)).projection sector state) =
        (faceGraphDecomposition (D := D) (A := A) (M := M) (L := L)
          (NonNullFace := NonNullFace) (NullFace := NullFace)).projection sector state) ∧
    (∀ first second, first ≠ second →
      ((faceGraphDecomposition (D := D) (A := A) (M := M) (L := L)
        (NonNullFace := NonNullFace) (NullFace := NullFace)).projection first).comp
      ((faceGraphDecomposition (D := D) (A := A) (M := M) (L := L)
        (NonNullFace := NonNullFace) (NullFace := NullFace)).projection second) = 0) ∧
    (∀ sector first second,
      inner Real ((faceGraphDecomposition (D := D) (A := A) (M := M) (L := L)
        (NonNullFace := NonNullFace) (NullFace := NullFace)).projection sector first) second =
      inner Real first ((faceGraphDecomposition (D := D) (A := A) (M := M) (L := L)
        (NonNullFace := NonNullFace) (NullFace := NullFace)).projection sector second)) ∧
    (∀ first second, first ≠ second → ∀ x y,
      inner Real ((faceGraphDecomposition (D := D) (A := A) (M := M) (L := L)
        (NonNullFace := NonNullFace) (NullFace := NullFace)).projection first x)
        ((faceGraphDecomposition (D := D) (A := A) (M := M) (L := L)
          (NonNullFace := NonNullFace) (NullFace := NullFace)).projection second y) = 0) ∧
    (∀ state, ∑ sector : FiveSectorSlot,
      (faceGraphDecomposition (D := D) (A := A) (M := M) (L := L)
        (NonNullFace := NonNullFace) (NullFace := NullFace)).projection sector state = state) :=
  five_sector_orthogonal_product_resolution_gate faceGraphDecomposition

/-- A non-null face supplies a nonzero fifth projector on the enlarged graph. -/
theorem boundary_projection_ne_zero [Nonempty NonNullFace] :
    (faceGraphDecomposition (D := D) (A := A) (M := M) (L := L)
      (NonNullFace := NonNullFace) (NullFace := NullFace)).projection
        .boundaryFiniteBV ≠ 0 := by
  classical
  let face : NonNullFace := Classical.choice inferInstance
  let b : BoundaryFaceCoordinates NonNullFace NullFace :=
    EuclideanSpace.single (Sum.inl face) 1
  have hb : b ≠ 0 := by
    intro h
    have hs : EuclideanSpace.single (Sum.inl face : NonNullFace ⊕ NullFace)
        (1 : Real) = 0 := by
      simpa [b] using h
    exact one_ne_zero (EuclideanSpace.single_eq_zero_iff.mp hs)
  intro h
  let data := faceGraphDecomposition (D := D) (A := A) (M := M) (L := L)
    (NonNullFace := NonNullFace) (NullFace := NullFace)
  let coords : FiveSectorProduct D A M L
      (BoundaryFaceCoordinates NonNullFace NullFace) := (0, (0, (0, (0, b))))
  have hz := congrArg (fun map => map (data.decomposition.symm coords)) h
  have hcoords : coords = 0 := by
    have hz' := congrArg (fun x => data.decomposition x) hz
    simpa [data, coords, FiveSectorOrthogonalProductDecomposition.projection,
      fiveSectorProductProjection] using hz'
  exact hb (congrArg (fun x => x.2.2.2.2) hcoords)

section CandidateA

open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D

/-- Candidate-A four completed graph factors, enlarged only by finite face
coordinates. This type does not assert a boundary Hessian. -/
abbrev candidateAFiveSectorFaceGraph
    (period : Real) (hPeriod : period ≠ 0)
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :=
  FiveSectorFaceGraph
    (GlobalCandidateADiagonalDiffeomorphismOffShellGraphHilbert
      period hPeriod (globalCandidateAMetricBySector period hPeriod data))
    (GlobalPairedAbelianOffShellGraphHilbert period hPeriod
      (globalCandidateAMetricBySector period hPeriod data))
    (ProgramPPrimitiveSpinCMatterL2GraphDomain period hPeriod
      couplings.matterMassSquared)
    (GlobalFullLLGraphHilbert period hPeriod data analysis)
    NonNullFace NullFace

end CandidateA

end
end P0EFTJanusProgramPT12FiveSectorBoundaryCoordinateHilbertResolution4D
end JanusFormal
