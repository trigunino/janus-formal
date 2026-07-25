import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9MatterSpinorDoubledGlobalDiracOperator4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9MatterSpinorFlatCoverConnection4D

/-!
# Intrinsic radial Dirac operator on the doubled D9 spinor bundle

The fixed throat is the identity mapping torus of `S²`.  Its radial
local-diffeomorphism identifies the tangent bundle of `S² × ℝ` with
Euclidean three-space.  Rescaling that derivative by `exp (-time)` removes
the deck dilation and yields the canonical product-metric orthonormal frame.

This gate uses that genuine geometric frame for the Clifford symbol and the
Dirac contraction.  The resulting cover operator is smooth and obeys the
spinor deck law, so it descends to a genuine smooth section of the actual
doubled D9 bundle.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9MatterSpinorDoubledIntrinsicDiracOperator4D

set_option autoImplicit false
noncomputable section

open Set Bundle Module
open scoped Manifold ContDiff BigOperators InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothNormalVectorBundle
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusD8NonabelianGhostThroatBRST4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusProgramPThroatMatterSpinorSectionSpace4D
open P0EFTJanusProgramPD9MatterSpinorSmoothVectorBundle4D
open P0EFTJanusProgramPD9MatterSpinorSmoothSectionDescent4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothSectionDescent4D
open P0EFTJanusProgramPD9MatterSpinorFlatCoverConnection4D
open P0EFTJanusProgramPD9MatterSpinorDoubledFlatCoverConnection4D
open P0EFTJanusProgramPD9MatterSpinorDoubledGlobalCovariantDerivative4D
open P0EFTJanusProgramPD9MatterSpinorDoubledFlatGlobalConnectionBridge4D
open P0EFTJanusProgramPD9MatterSpinorDoubledGlobalDeckCliffordAction4D
open P0EFTJanusProgramPD9MatterSpinorDoubledCliffordConnectionCompatibility4D
open P0EFTJanusProgramPD9MatterSpinorDoubledGlobalDiracOperator4D
open P0EFTJanusProgramPD9MatterSpinorSmoothPullbackBridge4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatCover := MappingTorusCover (ThroatData period hPeriod)
private abbrev ThroatBase := MappingTorus (ThroatData period hPeriod)
private abbrev EuclideanR3 := EuclideanSpace Real (Fin 3)

local instance throatCoverChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatCover period hPeriod) :=
  fixedThroatCoverChartedSpace period hPeriod

local instance throatCoverIsManifold :
    IsManifold throatCoverModelWithCorners ω (ThroatCover period hPeriod) :=
  fixedThroatCover_isManifold period hPeriod

local instance throatBaseChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance throatBaseIsManifold :
    IsManifold throatCoverModelWithCorners ω (ThroatBase period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- Euclidean scaling by the positive radial factor at a cover point. -/
def d9ThroatRadialScale
    (point : ThroatCover period hPeriod) :
    EuclideanR3 ≃L[Real] EuclideanR3 :=
  ContinuousLinearEquiv.smulLeft
    (Units.mk0 (Real.exp point.time) (Real.exp_ne_zero point.time))

/-- The product-metric frame obtained by pulling the scaled Euclidean basis
back through the radial derivative. -/
def d9IntrinsicThroatCoverBasis
    (point : ThroatCover period hPeriod) :
    Basis (Fin 3) Real
      (TangentSpace throatCoverModelWithCorners point) :=
  (EuclideanSpace.basisFun (Fin 3) Real).toBasis.map
    (((d9ThroatRadialScale period hPeriod point).trans
      (canonicalThroatRadialDerivativeEquiv
        period hPeriod point).symm).toLinearEquiv)

/-- One vector of the intrinsic radial frame. -/
def d9IntrinsicThroatCoverFrame
    (direction : Fin 3) (point : ThroatCover period hPeriod) :
    TangentSpace throatCoverModelWithCorners point :=
  d9IntrinsicThroatCoverBasis period hPeriod point direction

theorem d9IntrinsicThroatCoverFrame_radial
    (direction : Fin 3) (point : ThroatCover period hPeriod) :
    canonicalThroatRadialDerivativeEquiv period hPeriod point
        (d9IntrinsicThroatCoverFrame period hPeriod direction point) =
      Real.exp point.time •
        (EuclideanSpace.basisFun (Fin 3) Real direction) := by
  simp [d9IntrinsicThroatCoverFrame, d9IntrinsicThroatCoverBasis,
    d9ThroatRadialScale]

/-- The radial map has exactly the exponential radius used in the frame. -/
theorem throatCoverRadialMap_norm
    (point : ThroatCover period hPeriod) :
    ‖throatCoverRadialMap period hPeriod point‖ =
      Real.exp point.time := by
  have hUnit :
      ‖(equatorialTwoSphereHomeomorph point.fiber).1‖ = 1 := by
    simpa [mem_sphere_zero_iff_norm] using
      (equatorialTwoSphereHomeomorph point.fiber).2
  rw [throatCoverRadialMap_apply, norm_smul, hUnit, mul_one]
  exact Real.norm_of_nonneg (Real.exp_pos _).le

/-- A throat deck translation is represented by a positive Euclidean
dilation under the radial local diffeomorphism. -/
theorem throatCoverRadialMap_deck
    (winding : Int) (point : ThroatCover period hPeriod) :
    throatCoverRadialMap period hPeriod (winding +ᵥ point) =
      Real.exp ((winding : Real) * period) •
        throatCoverRadialMap period hPeriod point := by
  have hFiber :
      ((Homeomorph.refl EquatorialTwoSphere) ^ winding) point.fiber =
        point.fiber := by
    rw [show ((Homeomorph.refl EquatorialTwoSphere) ^ winding) point.fiber =
        ((Homeomorph.refl EquatorialTwoSphere) ^ winding).toEquiv
          point.fiber from rfl,
      homeomorph_toEquiv_zpow]
    rw [show (Homeomorph.refl EquatorialTwoSphere).toEquiv = 1 from rfl,
      one_zpow]
    rfl
  rw [throatCoverRadialMap_apply, throatCoverRadialMap_apply]
  simp [fixedEquatorData, hFiber, Real.exp_add, smul_smul, mul_comm]

/-- Smooth homogeneous Euclidean frame away from the radial origin. -/
def d9EuclideanRadialFrame
    (direction : Fin 3) (point : EuclideanR3) : EuclideanR3 :=
  ‖point‖ • EuclideanSpace.basisFun (Fin 3) Real direction

/-- The radial frame regarded as a dependent Euclidean vector field. -/
def d9EuclideanRadialVectorField
    (direction : Fin 3) (point : EuclideanR3) :
    TangentSpace 𝓘(Real, EuclideanR3) point :=
  (NormedSpace.fromTangentSpace point).symm
    (d9EuclideanRadialFrame direction point)

@[simp]
theorem d9EuclideanRadialVectorField_apply
    (direction : Fin 3) (point : EuclideanR3) :
    d9EuclideanRadialVectorField direction point =
      d9EuclideanRadialFrame direction point := by
  rfl

theorem d9EuclideanRadialFrame_contDiffOn
    (direction : Fin 3) :
    ContDiffOn Real ∞ (d9EuclideanRadialFrame direction)
      ({0}ᶜ : Set EuclideanR3) := by
  apply (contDiffOn_id.norm Real ?_).smul contDiffOn_const
  intro point hPoint
  simpa only [id_eq, Set.mem_compl_iff, Set.mem_singleton_iff] using hPoint

theorem d9EuclideanRadialFrame_contMDiffOn
    (direction : Fin 3) :
    ContMDiffOn 𝓘(Real, EuclideanR3)
      𝓘(Real, EuclideanR3).tangent ∞
      (fun point =>
        (⟨point, d9EuclideanRadialVectorField direction point⟩ :
          TangentBundle 𝓘(Real, EuclideanR3) EuclideanR3))
      ({0}ᶜ : Set EuclideanR3) := by
  intro point hPoint
  rw [contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt]
  have hFrame :=
    d9EuclideanRadialFrame_contDiffOn direction point hPoint
  convert hFrame using 1
  funext current
  exact d9EuclideanRadialVectorField_apply direction current

private theorem throatRadialDerivative_isInvertible
    (point : ThroatCover period hPeriod) :
    (mfderiv throatCoverModelWithCorners 𝓘(Real, EuclideanR3)
      (throatCoverRadialMap period hPeriod) point).IsInvertible := by
  rw [← canonicalThroatRadialDerivativeEquiv_coe period hPeriod point]
  exact ⟨canonicalThroatRadialDerivativeEquiv period hPeriod point, rfl⟩

theorem d9IntrinsicThroatCoverFrame_eq_mpullback
    (direction : Fin 3) :
    d9IntrinsicThroatCoverFrame period hPeriod direction =
      VectorField.mpullback throatCoverModelWithCorners
        𝓘(Real, EuclideanR3)
        (throatCoverRadialMap period hPeriod)
        (d9EuclideanRadialVectorField direction) := by
  funext point
  rw [VectorField.mpullback_apply]
  symm
  rw [(throatRadialDerivative_isInvertible
    period hPeriod point).inverse_apply_eq]
  apply (NormedSpace.fromTangentSpace
    (throatCoverRadialMap period hPeriod point)).injective
  change d9EuclideanRadialFrame direction
      (throatCoverRadialMap period hPeriod point) =
    canonicalThroatRadialDerivativeEquiv period hPeriod point
      (d9IntrinsicThroatCoverFrame period hPeriod direction point)
  rw [d9IntrinsicThroatCoverFrame_radial]
  rw [d9EuclideanRadialFrame, throatCoverRadialMap_norm]

/-- Each intrinsic radial frame vector is a genuine smooth vector field on
the entire throat cover. -/
theorem d9IntrinsicThroatCoverFrame_contMDiff
    (direction : Fin 3) :
    ContMDiff throatCoverModelWithCorners
      throatCoverModelWithCorners.tangent ∞
      (fun point =>
        (⟨point,
          d9IntrinsicThroatCoverFrame
            period hPeriod direction point⟩ :
          TangentBundle throatCoverModelWithCorners
            (ThroatCover period hPeriod))) := by
  rw [d9IntrinsicThroatCoverFrame_eq_mpullback]
  have hPullback :=
    ContMDiffOn.mpullback_vectorField_preimage
      (m := ∞) (n := ∞)
      (d9EuclideanRadialFrame_contMDiffOn direction)
      (throatCoverRadialMap_isLocalDiffeomorph
        period hPeriod).contMDiff
      (fun point _ =>
        throatRadialDerivative_isInvertible period hPeriod point)
      (by simp)
  have hPreimage :
      throatCoverRadialMap period hPeriod ⁻¹'
          ({0}ᶜ : Set EuclideanR3) =
        Set.univ := by
    ext point
    simp only [Set.mem_preimage, Set.mem_compl_iff,
      Set.mem_singleton_iff, Set.mem_univ, iff_true]
    intro hZero
    have hNorm := congrArg norm hZero
    rw [throatCoverRadialMap_norm, norm_zero] at hNorm
    exact (Real.exp_ne_zero point.time) hNorm
  rw [hPreimage] at hPullback
  exact (contMDiffOn_univ.mp hPullback)

/-- Differential form of the radial/deck dilation identity. -/
theorem throatCoverRadialMap_mfderiv_deck
    (winding : Int) (point : ThroatCover period hPeriod)
    (vector : TangentSpace throatCoverModelWithCorners point) :
    canonicalThroatRadialDerivativeEquiv period hPeriod
        (winding +ᵥ point)
        (mfderiv throatCoverModelWithCorners
          throatCoverModelWithCorners
          (winding +ᵥ ·) point vector) =
      Real.exp ((winding : Real) * period) •
        canonicalThroatRadialDerivativeEquiv period hPeriod point vector := by
  let radial := throatCoverRadialMap period hPeriod
  let deck : ThroatCover period hPeriod → ThroatCover period hPeriod :=
    (winding +ᵥ ·)
  let scale := Real.exp ((winding : Real) * period)
  have hRadialAt :
      MDifferentiableAt throatCoverModelWithCorners
        𝓘(Real, EuclideanR3) radial point :=
    (throatCoverRadialMap_isLocalDiffeomorph period hPeriod).contMDiff
      |>.mdifferentiableAt (by simp)
  have hRadialDeckAt :
      MDifferentiableAt throatCoverModelWithCorners
        𝓘(Real, EuclideanR3) radial (deck point) :=
    (throatCoverRadialMap_isLocalDiffeomorph period hPeriod).contMDiff
      |>.mdifferentiableAt (by simp)
  have hDeckAt :
      MDifferentiableAt throatCoverModelWithCorners
        throatCoverModelWithCorners deck point :=
    (fixedThroatCover_deck_contMDiff period hPeriod winding)
      |>.mdifferentiableAt (by simp)
  have hFunction : radial ∘ deck = scale • radial := by
    funext current
    exact throatCoverRadialMap_deck
      period hPeriod winding current
  have hChain :
      mvfderiv throatCoverModelWithCorners
          (radial ∘ deck) point =
        (mvfderiv throatCoverModelWithCorners
          radial (deck point)).comp
          (mfderiv throatCoverModelWithCorners
            throatCoverModelWithCorners deck point) := by
    unfold mvfderiv
    rw [mfderiv_comp point hRadialDeckAt hDeckAt]
    rfl
  have hScaleDerivative :
      mvfderiv throatCoverModelWithCorners
          (scale • radial) point =
        scale • mvfderiv throatCoverModelWithCorners
          radial point := by
    have hConstSmul :
        scale • radial =
          (fun _ : ThroatCover period hPeriod => scale) • radial := by
      funext current
      rfl
    rw [hConstSmul]
    have h := mvfderiv_smul
      (mdifferentiableAt_const (c := scale)) hRadialAt
    simpa [mvfderiv_const] using h
  change mvfderiv throatCoverModelWithCorners
      radial (deck point)
        (mfderiv throatCoverModelWithCorners
          throatCoverModelWithCorners deck point vector) =
    scale • mvfderiv throatCoverModelWithCorners
      radial point vector
  calc
    _ = ((mvfderiv throatCoverModelWithCorners
          radial (deck point)).comp
          (mfderiv throatCoverModelWithCorners
            throatCoverModelWithCorners deck point)) vector := by
      rfl
    _ = mvfderiv throatCoverModelWithCorners
        (radial ∘ deck) point vector := by
      rw [hChain]
    _ = mvfderiv throatCoverModelWithCorners
        (scale • radial) point vector := by
      rw [hFunction]
    _ = (scale • mvfderiv throatCoverModelWithCorners
        radial point) vector := by
      rw [hScaleDerivative]
    _ = scale • mvfderiv throatCoverModelWithCorners
        radial point vector := by
      rfl

/-- The intrinsic frame satisfies the exact tangent deck cocycle. -/
theorem d9IntrinsicThroatCoverFrame_deck_equivariant
    (direction : Fin 3) (winding : Int)
    (point : ThroatCover period hPeriod) :
    d9IntrinsicThroatCoverFrame period hPeriod direction
        (winding +ᵥ point) =
      mfderiv throatCoverModelWithCorners
        throatCoverModelWithCorners
        (winding +ᵥ ·) point
        (d9IntrinsicThroatCoverFrame
          period hPeriod direction point) := by
  apply (canonicalThroatRadialDerivativeEquiv period hPeriod
    (winding +ᵥ point)).injective
  rw [d9IntrinsicThroatCoverFrame_radial,
    throatCoverRadialMap_mfderiv_deck,
    d9IntrinsicThroatCoverFrame_radial]
  simp [fixedEquatorData, Real.exp_add, smul_smul, mul_comm]

/-- The smooth intrinsic frame section together with its deck certificate. -/
def d9SmoothDeckEquivariantIntrinsicFrame
    (direction : Fin 3) :
    SmoothDeckEquivariantThroatCoverGhost period hPeriod where
  field :=
    { toFun := d9IntrinsicThroatCoverFrame period hPeriod direction
      contMDiff_toFun :=
        d9IntrinsicThroatCoverFrame_contMDiff
          period hPeriod direction }
  deck_equivariant :=
    d9IntrinsicThroatCoverFrame_deck_equivariant
      period hPeriod direction

/-- Intrinsic frame descended to the genuine fixed-throat quotient. -/
def d9IntrinsicThroatFrame
    (direction : Fin 3) :
    CInfinityThroatGhost period hPeriod :=
  descendSmoothDeckEquivariantThroatCoverGhost
    period hPeriod
    (d9SmoothDeckEquivariantIntrinsicFrame
      period hPeriod direction)

/-- Differential equivalence of the genuine quotient projection. -/
def d9ThroatProjectionDerivativeEquiv
    (point : ThroatCover period hPeriod) :
    TangentSpace throatCoverModelWithCorners point ≃L[Real]
      TangentSpace throatCoverModelWithCorners
        (mappingTorusMk (ThroatData period hPeriod) point) :=
  (fixedThroat_projection_isLocalDiffeomorph period hPeriod)
    |>.mfderivToContinuousLinearEquiv (by simp) point

@[simp]
theorem d9ThroatProjectionDerivativeEquiv_coe
    (point : ThroatCover period hPeriod) :
    (d9ThroatProjectionDerivativeEquiv period hPeriod point :
      TangentSpace throatCoverModelWithCorners point →L[Real]
        TangentSpace throatCoverModelWithCorners
          (mappingTorusMk (ThroatData period hPeriod) point)) =
      mfderiv throatCoverModelWithCorners
        throatCoverModelWithCorners
        (mappingTorusMk (ThroatData period hPeriod)) point :=
  IsLocalDiffeomorph.mfderivToContinuousLinearEquiv_coe
    (fixedThroat_projection_isLocalDiffeomorph period hPeriod)
      (by simp) point

@[simp]
theorem d9IntrinsicThroatFrame_mk
    (direction : Fin 3) (point : ThroatCover period hPeriod) :
    d9IntrinsicThroatFrame period hPeriod direction
        (mappingTorusMk (ThroatData period hPeriod) point) =
      d9ThroatProjectionDerivativeEquiv period hPeriod point
        (d9IntrinsicThroatCoverFrame
          period hPeriod direction point) := by
  rw [d9IntrinsicThroatFrame,
    descendSmoothDeckEquivariantThroatCoverGhost_mk]
  change mfderiv throatCoverModelWithCorners
      throatCoverModelWithCorners
      (mappingTorusMk (ThroatData period hPeriod)) point
        (d9IntrinsicThroatCoverFrame
          period hPeriod direction point) =
    mfderiv throatCoverModelWithCorners
      throatCoverModelWithCorners
      (mappingTorusMk (ThroatData period hPeriod)) point
        (d9IntrinsicThroatCoverFrame
          period hPeriod direction point)
  rfl

/-- The projected cover basis at a chosen quotient representative. -/
def d9ProjectedIntrinsicThroatBasis
    (point : ThroatCover period hPeriod) :
    Basis (Fin 3) Real
      (TangentSpace throatCoverModelWithCorners
        (mappingTorusMk (ThroatData period hPeriod) point)) :=
  (d9IntrinsicThroatCoverBasis period hPeriod point).map
    (d9ThroatProjectionDerivativeEquiv
      period hPeriod point).toLinearEquiv

@[simp]
theorem d9ProjectedIntrinsicThroatBasis_apply
    (point : ThroatCover period hPeriod) (direction : Fin 3) :
    d9ProjectedIntrinsicThroatBasis period hPeriod point direction =
      d9IntrinsicThroatFrame period hPeriod direction
        (mappingTorusMk (ThroatData period hPeriod) point) := by
  rw [d9IntrinsicThroatFrame_mk]
  rfl

/-- The three descended intrinsic frame vectors are pointwise independent. -/
theorem d9IntrinsicThroatFrame_linearIndependent
    (point : ThroatBase period hPeriod) :
    LinearIndependent Real
      (fun direction : Fin 3 =>
        d9IntrinsicThroatFrame period hPeriod direction point) := by
  obtain ⟨anchor, rfl⟩ :=
    mappingTorusMk_surjective
      (ThroatData period hPeriod) point
  have hFrame :
      (fun direction : Fin 3 =>
        d9IntrinsicThroatFrame period hPeriod direction
          (mappingTorusMk (ThroatData period hPeriod) anchor)) =
        d9ProjectedIntrinsicThroatBasis
          period hPeriod anchor := by
    funext direction
    exact (d9ProjectedIntrinsicThroatBasis_apply
      period hPeriod anchor direction).symm
  rw [hFrame]
  exact (d9ProjectedIntrinsicThroatBasis
    period hPeriod anchor).linearIndependent

/-- The descended intrinsic frame spans every quotient tangent space. -/
theorem d9IntrinsicThroatFrame_span
    (point : ThroatBase period hPeriod) :
    Submodule.span Real
        (Set.range fun direction : Fin 3 =>
          d9IntrinsicThroatFrame period hPeriod direction point) =
      ⊤ := by
  obtain ⟨anchor, rfl⟩ :=
    mappingTorusMk_surjective
      (ThroatData period hPeriod) point
  have hFrame :
      (fun direction : Fin 3 =>
        d9IntrinsicThroatFrame period hPeriod direction
          (mappingTorusMk (ThroatData period hPeriod) anchor)) =
        d9ProjectedIntrinsicThroatBasis
          period hPeriod anchor := by
    funext direction
    exact (d9ProjectedIntrinsicThroatBasis_apply
      period hPeriod anchor direction).symm
  rw [hFrame]
  exact (d9ProjectedIntrinsicThroatBasis
    period hPeriod anchor).span_eq

/-- Canonical global tangent basis on the D9 throat quotient. -/
def d9IntrinsicThroatBasis
    (point : ThroatBase period hPeriod) :
    Basis (Fin 3) Real
      (TangentSpace throatCoverModelWithCorners point) :=
  Basis.mk
    (d9IntrinsicThroatFrame_linearIndependent
      period hPeriod point)
    (by rw [d9IntrinsicThroatFrame_span period hPeriod point])

@[simp]
theorem d9IntrinsicThroatBasis_apply
    (point : ThroatBase period hPeriod) (direction : Fin 3) :
    d9IntrinsicThroatBasis period hPeriod point direction =
      d9IntrinsicThroatFrame period hPeriod direction point := by
  exact Basis.mk_apply _ _ direction

/-- Components of a genuine cotangent vector in the intrinsic global
orthonormal frame. -/
def d9IntrinsicCotangentCoordinates
    (point : ThroatBase period hPeriod)
    (covector :
      TangentSpace throatCoverModelWithCorners point →L[Real] Real) :
    ThroatCoverCoordinates :=
  d9ThroatModelBasis.repr.symm
    (Finsupp.equivFunOnFinite.symm
      (fun direction : Fin 3 =>
        covector
          (d9IntrinsicThroatFrame
            period hPeriod direction point)))

@[simp]
theorem d9IntrinsicCotangentCoordinates_repr
    (point : ThroatBase period hPeriod)
    (covector :
      TangentSpace throatCoverModelWithCorners point →L[Real] Real)
    (direction : Fin 3) :
    d9ThroatModelBasis.repr
        (d9IntrinsicCotangentCoordinates
          period hPeriod point covector) direction =
      covector
        (d9IntrinsicThroatFrame
          period hPeriod direction point) := by
  simp [d9IntrinsicCotangentCoordinates]

/-- Product-metric cotangent square norm induced by the intrinsic frame. -/
def d9IntrinsicCovectorNormSq
    (point : ThroatBase period hPeriod)
    (covector :
      TangentSpace throatCoverModelWithCorners point →L[Real] Real) :
    Real :=
  d9ThroatModelCovectorNormSq
    (d9IntrinsicCotangentCoordinates
      period hPeriod point covector)

theorem d9IntrinsicCovectorNormSq_eq_sum
    (point : ThroatBase period hPeriod)
    (covector :
      TangentSpace throatCoverModelWithCorners point →L[Real] Real) :
    d9IntrinsicCovectorNormSq period hPeriod point covector =
      ∑ direction : Fin 3,
        (covector
          (d9IntrinsicThroatFrame
            period hPeriod direction point)) ^ 2 := by
  simp [d9IntrinsicCovectorNormSq,
    d9ThroatModelCovectorNormSq]

/-- Principal Clifford symbol on the actual cotangent space of the throat. -/
def d9IntrinsicDoubledMatterCliffordSymbol
    (point : ThroatBase period hPeriod)
    (covector :
      TangentSpace throatCoverModelWithCorners point →L[Real] Real) :
    D9DoubledMatterFiber →L[Real] D9DoubledMatterFiber :=
  d9DoubledMatterFiberCliffordSymbol
    (d9IntrinsicCotangentCoordinates
      period hPeriod point covector)

theorem d9IntrinsicCotangentCoordinates_ne_zero
    (point : ThroatBase period hPeriod)
    (covector :
      TangentSpace throatCoverModelWithCorners point →L[Real] Real)
    (hCovector : covector ≠ 0) :
    d9IntrinsicCotangentCoordinates
        period hPeriod point covector ≠ 0 := by
  intro hCoordinates
  apply hCovector
  apply ContinuousLinearMap.coe_injective
  apply (d9IntrinsicThroatBasis
    period hPeriod point).ext
  intro direction
  have hComponent := congrArg
    (fun coordinate =>
      d9ThroatModelBasis.repr coordinate direction)
    hCoordinates
  simpa using hComponent

theorem d9IntrinsicCovectorNormSq_pos
    (point : ThroatBase period hPeriod)
    (covector :
      TangentSpace throatCoverModelWithCorners point →L[Real] Real)
    (hCovector : covector ≠ 0) :
    0 < d9IntrinsicCovectorNormSq
      period hPeriod point covector := by
  exact d9ThroatModelCovectorNormSq_pos
    (d9IntrinsicCotangentCoordinates
      period hPeriod point covector)
    (d9IntrinsicCotangentCoordinates_ne_zero
      period hPeriod point covector hCovector)

theorem d9IntrinsicCovectorNormSq_ne_zero
    (point : ThroatBase period hPeriod)
    (covector :
      TangentSpace throatCoverModelWithCorners point →L[Real] Real)
    (hCovector : covector ≠ 0) :
    d9IntrinsicCovectorNormSq
        period hPeriod point covector ≠ 0 :=
  ne_of_gt (d9IntrinsicCovectorNormSq_pos
    period hPeriod point covector hCovector)

/-- Intrinsic Clifford relation for the genuine product metric. -/
theorem d9IntrinsicDoubledMatterCliffordSymbol_sq
    (point : ThroatBase period hPeriod)
    (covector :
      TangentSpace throatCoverModelWithCorners point →L[Real] Real)
    (matter : D9DoubledMatterFiber) :
    d9IntrinsicDoubledMatterCliffordSymbol
        period hPeriod point covector
        (d9IntrinsicDoubledMatterCliffordSymbol
          period hPeriod point covector matter) =
      -(d9IntrinsicCovectorNormSq
        period hPeriod point covector) • matter := by
  exact d9DoubledMatterFiberCliffordSymbol_sq
    (d9IntrinsicCotangentCoordinates
      period hPeriod point covector) matter

/-- The intrinsic principal symbol has trivial kernel off the zero section. -/
theorem d9IntrinsicDoubledMatterCliffordSymbol_kernel_trivial
    (point : ThroatBase period hPeriod)
    (covector :
      TangentSpace throatCoverModelWithCorners point →L[Real] Real)
    (hCovector : covector ≠ 0)
    (matter : D9DoubledMatterFiber)
    (hKernel :
      d9IntrinsicDoubledMatterCliffordSymbol
        period hPeriod point covector matter = 0) :
    matter = 0 := by
  exact d9DoubledMatterFiberCliffordSymbol_kernel_trivial
    (d9IntrinsicCotangentCoordinates
      period hPeriod point covector)
    (d9IntrinsicCotangentCoordinates_ne_zero
      period hPeriod point covector hCovector)
    matter hKernel

/-- Explicit inverse of the intrinsic Clifford symbol away from the zero
cotangent section. -/
def d9IntrinsicDoubledMatterCliffordSymbolInverse
    (point : ThroatBase period hPeriod)
    (covector :
      TangentSpace throatCoverModelWithCorners point →L[Real] Real) :
    D9DoubledMatterFiber →L[Real] D9DoubledMatterFiber :=
  (-(d9IntrinsicCovectorNormSq
      period hPeriod point covector)⁻¹) •
    d9IntrinsicDoubledMatterCliffordSymbol
      period hPeriod point covector

theorem d9IntrinsicDoubledMatterCliffordSymbolInverse_left
    (point : ThroatBase period hPeriod)
    (covector :
      TangentSpace throatCoverModelWithCorners point →L[Real] Real)
    (hCovector : covector ≠ 0)
    (matter : D9DoubledMatterFiber) :
    d9IntrinsicDoubledMatterCliffordSymbolInverse
        period hPeriod point covector
        (d9IntrinsicDoubledMatterCliffordSymbol
          period hPeriod point covector matter) =
      matter := by
  have hNorm := d9IntrinsicCovectorNormSq_ne_zero
    period hPeriod point covector hCovector
  unfold d9IntrinsicDoubledMatterCliffordSymbolInverse
  rw [smul_apply,
    d9IntrinsicDoubledMatterCliffordSymbol_sq]
  simp [smul_smul, hNorm]

theorem d9IntrinsicDoubledMatterCliffordSymbolInverse_right
    (point : ThroatBase period hPeriod)
    (covector :
      TangentSpace throatCoverModelWithCorners point →L[Real] Real)
    (hCovector : covector ≠ 0)
    (matter : D9DoubledMatterFiber) :
    d9IntrinsicDoubledMatterCliffordSymbol
        period hPeriod point covector
        (d9IntrinsicDoubledMatterCliffordSymbolInverse
          period hPeriod point covector matter) =
      matter := by
  have hNorm := d9IntrinsicCovectorNormSq_ne_zero
    period hPeriod point covector hCovector
  unfold d9IntrinsicDoubledMatterCliffordSymbolInverse
  rw [smul_apply, map_smul,
    d9IntrinsicDoubledMatterCliffordSymbol_sq]
  simp [smul_smul, hNorm]

/-- The nonzero intrinsic Clifford symbol as an explicit continuous linear
equivalence. -/
def d9IntrinsicDoubledMatterCliffordSymbolEquiv
    (point : ThroatBase period hPeriod)
    (covector :
      TangentSpace throatCoverModelWithCorners point →L[Real] Real)
    (hCovector : covector ≠ 0) :
    D9DoubledMatterFiber ≃L[Real] D9DoubledMatterFiber where
  toFun :=
    d9IntrinsicDoubledMatterCliffordSymbol
      period hPeriod point covector
  invFun :=
    d9IntrinsicDoubledMatterCliffordSymbolInverse
      period hPeriod point covector
  left_inv :=
    d9IntrinsicDoubledMatterCliffordSymbolInverse_left
      period hPeriod point covector hCovector
  right_inv :=
    d9IntrinsicDoubledMatterCliffordSymbolInverse_right
      period hPeriod point covector hCovector
  map_add' :=
    (d9IntrinsicDoubledMatterCliffordSymbol
      period hPeriod point covector).map_add
  map_smul' :=
    (d9IntrinsicDoubledMatterCliffordSymbol
      period hPeriod point covector).map_smul
  continuous_toFun :=
    (d9IntrinsicDoubledMatterCliffordSymbol
      period hPeriod point covector).continuous
  continuous_invFun :=
    (d9IntrinsicDoubledMatterCliffordSymbolInverse
      period hPeriod point covector).continuous

theorem d9IntrinsicDoubledMatterCliffordSymbol_bijective
    (point : ThroatBase period hPeriod)
    (covector :
      TangentSpace throatCoverModelWithCorners point →L[Real] Real)
    (hCovector : covector ≠ 0) :
    Function.Bijective
      (d9IntrinsicDoubledMatterCliffordSymbol
        period hPeriod point covector) :=
  (d9IntrinsicDoubledMatterCliffordSymbolEquiv
    period hPeriod point covector hCovector).bijective

/-- Flat-cover covariant derivative contracted with one intrinsic frame
vector. -/
def d9IntrinsicDoubledMatterFlatFrameDerivative
    (choice : NormalRootChoice)
    (lift : SmoothThroatDoubledMatterSpinorLift
      period hPeriod choice)
    (direction : Fin 3) (point : ThroatCover period hPeriod) :
    D9DoubledMatterFiber :=
  (d9MatterSpinorFlatCoverDerivative
      period hPeriod choice lift.first point
      (d9IntrinsicThroatCoverFrame
        period hPeriod direction point),
    d9MatterSpinorFlatCoverDerivative
      period hPeriod (oppositeRoot choice) lift.second point
      (d9IntrinsicThroatCoverFrame
        period hPeriod direction point))

/-- The intrinsic frame derivative is the doubled flat derivative evaluated
on the geometric frame. -/
theorem d9IntrinsicDoubledMatterFlatFrameDerivative_eq_flatCoverDerivative
    (choice : NormalRootChoice)
    (lift : SmoothThroatDoubledMatterSpinorLift
      period hPeriod choice)
    (direction : Fin 3) (point : ThroatCover period hPeriod) :
    d9IntrinsicDoubledMatterFlatFrameDerivative
        period hPeriod choice lift direction point =
      d9DoubledMatterSpinorFlatCoverDerivative
        period hPeriod choice lift point
        (d9IntrinsicThroatCoverFrame
          period hPeriod direction point) := by
  have hFirst : MDifferentiableAt throatCoverModelWithCorners
      𝓘(Real, MatterFiber) lift.first point :=
    lift.first.contMDiff_toFun.mdifferentiableAt (by simp)
  have hSecond : MDifferentiableAt throatCoverModelWithCorners
      𝓘(Real, MatterFiber) lift.second point :=
    lift.second.contMDiff_toFun.mdifferentiableAt (by simp)
  have hProduct := mfderiv_prodMk hFirst hSecond
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hProduct
  have hApplied := DFunLike.congr_fun hProduct
    (d9IntrinsicThroatCoverFrame
      period hPeriod direction point)
  exact hApplied.symm

theorem d9IntrinsicDoubledMatterFlatFrameDerivative_contMDiff
    (choice : NormalRootChoice)
    (lift : SmoothThroatDoubledMatterSpinorLift
      period hPeriod choice)
    (direction : Fin 3) :
    ContMDiff throatCoverModelWithCorners
      𝓘(Real, D9DoubledMatterFiber) ∞
      (d9IntrinsicDoubledMatterFlatFrameDerivative
        period hPeriod choice lift direction) := by
  rw [contMDiff_prod_module_iff]
  constructor
  · have hDerivative :=
      (contMDiff_snd_tangentBundle_modelSpace
        MatterFiber 𝓘(Real, MatterFiber)).comp
      ((lift.first.contMDiff_toFun.contMDiff_tangentMap (by simp)).comp
        (d9IntrinsicThroatCoverFrame_contMDiff
          period hPeriod direction))
    convert hDerivative using 1
    rfl
  · have hDerivative :=
      (contMDiff_snd_tangentBundle_modelSpace
        MatterFiber 𝓘(Real, MatterFiber)).comp
      ((lift.second.contMDiff_toFun.contMDiff_tangentMap (by simp)).comp
        (d9IntrinsicThroatCoverFrame_contMDiff
          period hPeriod direction))
    convert hDerivative using 1
    rfl

theorem d9IntrinsicDoubledMatterFlatFrameDerivative_deck
    (choice : NormalRootChoice)
    (lift : SmoothThroatDoubledMatterSpinorLift
      period hPeriod choice)
    (direction : Fin 3) (winding : Int)
    (point : ThroatCover period hPeriod) :
    d9IntrinsicDoubledMatterFlatFrameDerivative
        period hPeriod choice lift direction (winding +ᵥ point) =
      d9DoubledMatterSpinorMonodromyCLM choice winding
        (d9IntrinsicDoubledMatterFlatFrameDerivative
          period hPeriod choice lift direction point) := by
  simp only [
    d9IntrinsicDoubledMatterFlatFrameDerivative_eq_flatCoverDerivative]
  have hDerivative := congrArg
    (fun derivative =>
      derivative
        (d9IntrinsicThroatCoverFrame
          period hPeriod direction point))
    (d9DoubledMatterSpinorFlatCoverDerivative_deck_equivariant
      period hPeriod choice lift winding point)
  change
    d9DoubledMatterSpinorFlatCoverDerivative
        period hPeriod choice lift (winding +ᵥ point)
        (mfderiv throatCoverModelWithCorners
          throatCoverModelWithCorners
          (winding +ᵥ ·) point
          (d9IntrinsicThroatCoverFrame
            period hPeriod direction point)) =
      d9DoubledMatterSpinorMonodromyCLM choice winding
        (d9DoubledMatterSpinorFlatCoverDerivative
          period hPeriod choice lift point
          (d9IntrinsicThroatCoverFrame
            period hPeriod direction point)) at hDerivative
  have hFrameModel :
      ((mfderiv throatCoverModelWithCorners
        throatCoverModelWithCorners
        (winding +ᵥ ·) point :
        TangentSpace throatCoverModelWithCorners point →L[Real]
          ThroatCoverCoordinates)
          (d9IntrinsicThroatCoverFrame
            period hPeriod direction point)) =
        (d9IntrinsicThroatCoverFrame
          period hPeriod direction (winding +ᵥ point) :
          ThroatCoverCoordinates) :=
    (d9IntrinsicThroatCoverFrame_deck_equivariant
      period hPeriod direction winding point).symm
  have hApplied := congrArg
    (d9DoubledMatterSpinorFlatCoverDerivative
      period hPeriod choice lift (winding +ᵥ point))
    hFrameModel
  exact hApplied.symm.trans hDerivative

/-- Intrinsic geometric Dirac contraction on the smooth cover. -/
def d9IntrinsicDoubledMatterSpinorCoverDirac
    (choice : NormalRootChoice)
    (lift : SmoothThroatDoubledMatterSpinorLift
      period hPeriod choice)
    (point : ThroatCover period hPeriod) :
    D9DoubledMatterFiber :=
  ∑ direction : Fin 3,
    d9DoubledMatterFiberCliffordGammaCLM direction
      (d9IntrinsicDoubledMatterFlatFrameDerivative
        period hPeriod choice lift direction point)

theorem d9IntrinsicDoubledMatterSpinorCoverDirac_contMDiff
    (choice : NormalRootChoice)
    (lift : SmoothThroatDoubledMatterSpinorLift
      period hPeriod choice) :
    ContMDiff throatCoverModelWithCorners
      𝓘(Real, D9DoubledMatterFiber) ∞
      (d9IntrinsicDoubledMatterSpinorCoverDirac
        period hPeriod choice lift) := by
  apply ContMDiff.sum
  intro direction _
  exact
    (d9DoubledMatterFiberCliffordGammaCLM
      direction).contDiff.contMDiff.comp
      (d9IntrinsicDoubledMatterFlatFrameDerivative_contMDiff
        period hPeriod choice lift direction)

theorem d9IntrinsicDoubledMatterSpinorCoverDirac_deck
    (choice : NormalRootChoice)
    (lift : SmoothThroatDoubledMatterSpinorLift
      period hPeriod choice)
    (winding : Int) (point : ThroatCover period hPeriod) :
    d9IntrinsicDoubledMatterSpinorCoverDirac
        period hPeriod choice lift (winding +ᵥ point) =
      d9DoubledMatterSpinorMonodromy choice winding
        (d9IntrinsicDoubledMatterSpinorCoverDirac
          period hPeriod choice lift point) := by
  unfold d9IntrinsicDoubledMatterSpinorCoverDirac
  calc
    _ = ∑ direction : Fin 3,
        d9DoubledMatterFiberCliffordGammaCLM direction
          (d9DoubledMatterSpinorMonodromyCLM choice winding
            (d9IntrinsicDoubledMatterFlatFrameDerivative
              period hPeriod choice lift direction point)) := by
      apply Finset.sum_congr rfl
      intro direction _
      rw [d9IntrinsicDoubledMatterFlatFrameDerivative_deck]
    _ = ∑ direction : Fin 3,
        d9DoubledMatterSpinorMonodromyCLM choice winding
          (d9DoubledMatterFiberCliffordGammaCLM direction
            (d9IntrinsicDoubledMatterFlatFrameDerivative
              period hPeriod choice lift direction point)) := by
      apply Finset.sum_congr rfl
      intro direction _
      exact d9DoubledMatterFiberCliffordGamma_monodromy
        choice direction winding _
    _ = d9DoubledMatterSpinorMonodromyCLM choice winding
        (∑ direction : Fin 3,
          d9DoubledMatterFiberCliffordGammaCLM direction
            (d9IntrinsicDoubledMatterFlatFrameDerivative
              period hPeriod choice lift direction point)) := by
      rw [map_sum]
    _ = _ := rfl

/-- The cover Dirac contraction packaged as a genuine smooth doubled spinor
lift. -/
def d9IntrinsicDoubledMatterSpinorDiracLift
    (choice : NormalRootChoice)
    (lift : SmoothThroatDoubledMatterSpinorLift
      period hPeriod choice) :
    SmoothThroatDoubledMatterSpinorLift
      period hPeriod choice where
  first :=
    { toFun := fun point =>
        (d9IntrinsicDoubledMatterSpinorCoverDirac
          period hPeriod choice lift point).1
      contMDiff_toFun := by
        have hSmooth :=
          d9IntrinsicDoubledMatterSpinorCoverDirac_contMDiff
            period hPeriod choice lift
        rw [contMDiff_prod_module_iff] at hSmooth
        exact hSmooth.1
      deck_equivariant := by
        intro winding point
        rw [throatAmbientPinCMatterCoordChange_deck_eq_monodromy]
        have hDeck := congrArg Prod.fst
          (d9IntrinsicDoubledMatterSpinorCoverDirac_deck
            period hPeriod choice lift winding point)
        simpa [d9DoubledMatterSpinorMonodromy] using hDeck }
  second :=
    { toFun := fun point =>
        (d9IntrinsicDoubledMatterSpinorCoverDirac
          period hPeriod choice lift point).2
      contMDiff_toFun := by
        have hSmooth :=
          d9IntrinsicDoubledMatterSpinorCoverDirac_contMDiff
            period hPeriod choice lift
        rw [contMDiff_prod_module_iff] at hSmooth
        exact hSmooth.2
      deck_equivariant := by
        intro winding point
        rw [throatAmbientPinCMatterCoordChange_deck_eq_monodromy]
        have hDeck := congrArg Prod.snd
          (d9IntrinsicDoubledMatterSpinorCoverDirac_deck
            period hPeriod choice lift winding point)
        simpa [d9DoubledMatterSpinorMonodromy] using hDeck }

@[simp]
theorem d9IntrinsicDoubledMatterSpinorDiracLift_apply
    (choice : NormalRootChoice)
    (lift : SmoothThroatDoubledMatterSpinorLift
      period hPeriod choice)
    (point : ThroatCover period hPeriod) :
    d9IntrinsicDoubledMatterSpinorDiracLift
        period hPeriod choice lift point =
      d9IntrinsicDoubledMatterSpinorCoverDirac
        period hPeriod choice lift point := by
  rfl

/-- Intrinsic Dirac operator as an endomorphism of the actual smooth
section space. -/
def d9IntrinsicDoubledMatterSpinorDiracOperator
    (choice : NormalRootChoice) :
    SmoothThroatDoubledMatterSpinorLift period hPeriod choice →
      SmoothThroatDoubledMatterSpinorLift period hPeriod choice :=
  d9IntrinsicDoubledMatterSpinorDiracLift
    period hPeriod choice

/-- The operator output descends to a genuine smooth section of the doubled
D9 vector bundle. -/
theorem d9IntrinsicDoubledMatterSpinorDiracBundleSection_contMDiff
    (choice : NormalRootChoice)
    (lift : SmoothThroatDoubledMatterSpinorLift
      period hPeriod choice) :
    ContMDiff throatCoverModelWithCorners
      (throatCoverModelWithCorners.prod
        𝓘(Real, D9DoubledMatterFiber)) ∞
      (d9DoubledMatterSpinorBundleSection
        period hPeriod choice
        (d9IntrinsicDoubledMatterSpinorDiracOperator
          period hPeriod choice lift)) :=
  d9DoubledMatterSpinorBundleSection_contMDiff
    period hPeriod choice
      (d9IntrinsicDoubledMatterSpinorDiracOperator
        period hPeriod choice lift)

/-- The chosen local inverse of the quotient projection sends every
descended frame vector back to its intrinsic cover representative. -/
theorem d9IntrinsicThroatFrame_localInverse_mfderiv
    (direction : Fin 3) (anchor : ThroatCover period hPeriod) :
    mfderiv throatCoverModelWithCorners
        throatCoverModelWithCorners
        ((mappingTorusMk_isCoveringMap
          (ThroatData period hPeriod)).isLocalHomeomorph.localInverseAt
            anchor)
        (mappingTorusMk (ThroatData period hPeriod) anchor)
        (d9IntrinsicThroatFrame period hPeriod direction
          (mappingTorusMk (ThroatData period hPeriod) anchor)) =
      d9IntrinsicThroatCoverFrame
        period hPeriod direction anchor := by
  let projection :=
    mappingTorusMk (ThroatData period hPeriod)
  let hLocal :=
    (mappingTorusMk_isCoveringMap
      (ThroatData period hPeriod)).isLocalHomeomorph
  let localInverse := hLocal.localInverseAt anchor
  let base := projection anchor
  have hInverseBase : localInverse base = anchor := by
    exact hLocal.localInverseAt_apply_self
  have hInverseAt :
      MDifferentiableAt throatCoverModelWithCorners
        throatCoverModelWithCorners localInverse base :=
    (throatProjectionLocalInverseAt_contMDiffAt
      period hPeriod anchor).mdifferentiableAt (by simp)
  have hProjectionAt :
      MDifferentiableAt throatCoverModelWithCorners
        throatCoverModelWithCorners projection (localInverse base) :=
    (fixedThroat_projection_isLocalDiffeomorph
      period hPeriod).contMDiff.mdifferentiableAt (by simp)
  have hEventually :
      projection ∘ localInverse =ᶠ[nhds base] id := by
    filter_upwards
      [localInverse.open_source.mem_nhds
        hLocal.apply_self_mem_localInverseAt_source] with current hCurrent
    exact hLocal.apply_localInverseAt_of_mem hCurrent
  have hMaps :
      (mfderiv throatCoverModelWithCorners
          throatCoverModelWithCorners projection (localInverse base)).comp
        (mfderiv throatCoverModelWithCorners
          throatCoverModelWithCorners localInverse base) =
        ContinuousLinearMap.id ℝ
          (TangentSpace throatCoverModelWithCorners base) := by
    rw [← mfderiv_id, ← hEventually.mfderiv_eq]
    exact (mfderiv_comp base hProjectionAt hInverseAt).symm
  rw [hInverseBase] at hMaps
  rw [d9IntrinsicThroatFrame_mk]
  apply (d9ThroatProjectionDerivativeEquiv
    period hPeriod anchor).injective
  change mfderiv throatCoverModelWithCorners
      throatCoverModelWithCorners projection anchor
        (mfderiv throatCoverModelWithCorners
          throatCoverModelWithCorners localInverse base
          (mfderiv throatCoverModelWithCorners
            throatCoverModelWithCorners projection anchor
            (d9IntrinsicThroatCoverFrame
              period hPeriod direction anchor))) =
    mfderiv throatCoverModelWithCorners
      throatCoverModelWithCorners projection anchor
      (d9IntrinsicThroatCoverFrame
        period hPeriod direction anchor)
  exact DFunLike.congr_fun hMaps
    (mfderiv throatCoverModelWithCorners
      throatCoverModelWithCorners projection anchor
      (d9IntrinsicThroatCoverFrame
        period hPeriod direction anchor))

/-- Clifford contraction of the actual global covariant derivative in the
intrinsic quotient frame. -/
def d9IntrinsicDoubledMatterSpinorGlobalDiracAt
    (choice : NormalRootChoice)
    (spinorSection : ∀ base : ThroatBase period hPeriod,
      D9DoubledMatterSpinorFiber period hPeriod choice base)
    (base : ThroatBase period hPeriod) :
    D9DoubledMatterSpinorFiber period hPeriod choice base :=
  ∑ direction : Fin 3,
    d9DoubledMatterFiberCliffordGammaCLM direction
      (d9DoubledMatterSpinorGlobalCovariantDerivativeAt
        period hPeriod choice spinorSection base
        (d9IntrinsicThroatFrame
          period hPeriod direction base))

/-- Intrinsic global Dirac contraction applied to a smooth doubled
section. -/
def d9IntrinsicDoubledMatterSpinorGlobalDirac
    (choice : NormalRootChoice)
    (lift : SmoothThroatDoubledMatterSpinorLift
      period hPeriod choice)
    (base : ThroatBase period hPeriod) :
    D9DoubledMatterSpinorFiber period hPeriod choice base :=
  d9IntrinsicDoubledMatterSpinorGlobalDiracAt
    period hPeriod choice
    (d9DoubledMatterSpinorSectionFiber
      period hPeriod choice lift) base

/-- Exact cover formula for the intrinsic global Dirac contraction. -/
theorem d9IntrinsicDoubledMatterSpinorGlobalDirac_descended_flatCover
    (choice : NormalRootChoice)
    (lift : SmoothThroatDoubledMatterSpinorLift
      period hPeriod choice)
    (base : ThroatBase period hPeriod) :
    d9IntrinsicDoubledMatterSpinorGlobalDirac
        period hPeriod choice lift base =
      d9IntrinsicDoubledMatterSpinorCoverDirac
        period hPeriod choice lift
        (normalBundleIndexAt period hPeriod base) := by
  let anchor := normalBundleIndexAt period hPeriod base
  have hProjects :
      mappingTorusMk (ThroatData period hPeriod) anchor = base :=
    normalBundleIndexAt_projects period hPeriod base
  change d9IntrinsicDoubledMatterSpinorGlobalDirac
      period hPeriod choice lift base =
    d9IntrinsicDoubledMatterSpinorCoverDirac
      period hPeriod choice lift anchor
  unfold d9IntrinsicDoubledMatterSpinorGlobalDirac
    d9IntrinsicDoubledMatterSpinorGlobalDiracAt
    d9IntrinsicDoubledMatterSpinorCoverDirac
  rw [d9DoubledMatterSpinorGlobalCovariantDerivative_descended_flatCover]
  apply Finset.sum_congr rfl
  intro direction _
  apply congrArg
    (d9DoubledMatterFiberCliffordGammaCLM direction)
  rw [
    d9IntrinsicDoubledMatterFlatFrameDerivative_eq_flatCoverDerivative]
  apply congrArg
    (d9DoubledMatterSpinorFlatCoverDerivative
      period hPeriod choice lift anchor)
  have hLocalInverse :=
    d9IntrinsicThroatFrame_localInverse_mfderiv
    period hPeriod direction anchor
  rw [hProjects] at hLocalInverse
  exact hLocalInverse

/-- The global covariant-derivative formula is exactly the section
represented by the intrinsic smooth-lift operator. -/
theorem d9IntrinsicDoubledMatterSpinorGlobalDirac_eq_sectionFiber
    (choice : NormalRootChoice)
    (lift : SmoothThroatDoubledMatterSpinorLift
      period hPeriod choice)
    (base : ThroatBase period hPeriod) :
    d9IntrinsicDoubledMatterSpinorGlobalDirac
        period hPeriod choice lift base =
      d9DoubledMatterSpinorSectionFiber
        period hPeriod choice
        (d9IntrinsicDoubledMatterSpinorDiracOperator
          period hPeriod choice lift) base := by
  rw [
    d9IntrinsicDoubledMatterSpinorGlobalDirac_descended_flatCover]
  exact (d9IntrinsicDoubledMatterSpinorDiracLift_apply
    period hPeriod choice lift
    (normalBundleIndexAt period hPeriod base)).symm

/-- Complete certificate for the intrinsic first-order elliptic Dirac
operator on the actual doubled D9 bundle. -/
structure ProgramPD9MatterSpinorDoubledIntrinsicDiracOperatorCertificate4D
    where
  choice : NormalRootChoice
  frame : ∀ point : ThroatBase period hPeriod, Fin 3 →
    TangentSpace throatCoverModelWithCorners point
  frameCanonical : frame =
    fun point direction =>
      d9IntrinsicThroatFrame period hPeriod direction point
  tangentBasis : ∀ point : ThroatBase period hPeriod,
    Basis (Fin 3) Real
      (TangentSpace throatCoverModelWithCorners point)
  tangentBasisCanonical :
    tangentBasis = d9IntrinsicThroatBasis period hPeriod
  basisFrame : ∀ point direction,
    tangentBasis point direction = frame point direction
  frameLinearIndependent : ∀ point,
    LinearIndependent Real (frame point)
  frameSpans : ∀ point,
    Submodule.span Real (Set.range (frame point)) = ⊤
  symbol : ∀ point : ThroatBase period hPeriod,
    (TangentSpace throatCoverModelWithCorners point →L[Real] Real) →
      D9DoubledMatterFiber →L[Real] D9DoubledMatterFiber
  symbolCanonical :
    symbol = d9IntrinsicDoubledMatterCliffordSymbol period hPeriod
  symbolSquare : ∀ point covector matter,
    symbol point covector (symbol point covector matter) =
      -(d9IntrinsicCovectorNormSq
        period hPeriod point covector) • matter
  symbolElliptic : ∀ point covector, covector ≠ 0 → ∀ matter,
    symbol point covector matter = 0 → matter = 0
  symbolBijective : ∀ point covector, covector ≠ 0 →
    Function.Bijective (symbol point covector)
  operator :
    SmoothThroatDoubledMatterSpinorLift period hPeriod choice →
      SmoothThroatDoubledMatterSpinorLift period hPeriod choice
  operatorCanonical :
    operator =
      d9IntrinsicDoubledMatterSpinorDiracOperator
        period hPeriod choice
  coverFormula : ∀ lift point,
    operator lift point =
      d9IntrinsicDoubledMatterSpinorCoverDirac
        period hPeriod choice lift point
  outputSmooth : ∀ lift,
    ContMDiff throatCoverModelWithCorners
      (throatCoverModelWithCorners.prod
        𝓘(Real, D9DoubledMatterFiber)) ∞
      (d9DoubledMatterSpinorBundleSection
        period hPeriod choice (operator lift))
  globalFormula : ∀ lift base,
    d9IntrinsicDoubledMatterSpinorGlobalDirac
        period hPeriod choice lift base =
      d9DoubledMatterSpinorSectionFiber
        period hPeriod choice (operator lift) base

def programPD9MatterSpinorDoubledIntrinsicDiracOperatorCertificate4D :
    ProgramPD9MatterSpinorDoubledIntrinsicDiracOperatorCertificate4D
      period hPeriod where
  choice := .positiveQuarter
  frame := fun point direction =>
    d9IntrinsicThroatFrame period hPeriod direction point
  frameCanonical := rfl
  tangentBasis := d9IntrinsicThroatBasis period hPeriod
  tangentBasisCanonical := rfl
  basisFrame :=
    d9IntrinsicThroatBasis_apply period hPeriod
  frameLinearIndependent :=
    d9IntrinsicThroatFrame_linearIndependent period hPeriod
  frameSpans :=
    d9IntrinsicThroatFrame_span period hPeriod
  symbol :=
    d9IntrinsicDoubledMatterCliffordSymbol period hPeriod
  symbolCanonical := rfl
  symbolSquare :=
    d9IntrinsicDoubledMatterCliffordSymbol_sq period hPeriod
  symbolElliptic :=
    d9IntrinsicDoubledMatterCliffordSymbol_kernel_trivial
      period hPeriod
  symbolBijective :=
    d9IntrinsicDoubledMatterCliffordSymbol_bijective
      period hPeriod
  operator :=
    d9IntrinsicDoubledMatterSpinorDiracOperator
      period hPeriod .positiveQuarter
  operatorCanonical := rfl
  coverFormula :=
    d9IntrinsicDoubledMatterSpinorDiracLift_apply
      period hPeriod .positiveQuarter
  outputSmooth :=
    d9IntrinsicDoubledMatterSpinorDiracBundleSection_contMDiff
      period hPeriod .positiveQuarter
  globalFormula :=
    d9IntrinsicDoubledMatterSpinorGlobalDirac_eq_sectionFiber
      period hPeriod .positiveQuarter

theorem
    programPD9MatterSpinorDoubledIntrinsicDiracOperatorCertificate4D_nonempty :
    Nonempty
      (ProgramPD9MatterSpinorDoubledIntrinsicDiracOperatorCertificate4D
        period hPeriod) :=
  ⟨programPD9MatterSpinorDoubledIntrinsicDiracOperatorCertificate4D
    period hPeriod⟩

end
end P0EFTJanusProgramPD9MatterSpinorDoubledIntrinsicDiracOperator4D
end JanusFormal
