import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteJetCompatibilityPrincipalSymbol

/-!
# Finite Lorentzian Gram compatibility and its Frechet derivative

On the explicit ambient Minkowski model `R^(1,3)`, with

`eta(x,y) = -x_0 y_0 + x_1 y_1 + x_2 y_2 + x_3 y_3`,

this gate constructs `K(F) = F^T eta F` and its genuine Frechet derivative

`J_F(H)(u,v) = eta(Hu,Fv) + eta(Fu,Hv)`.

Both maps are natural under source-frame changes and ambient `eta`-isometries.
Ambient infinitesimal `eta`-antisymmetric generators give elements of
`ker J_F`; when `F` is a continuous linear equivalence these are exactly the
kernel.  The nonzero-frequency rank-one symbol has kernel exactly the
`eta`-orthogonal complement of `range F`, and is injective when `F` is onto.

The ambient model is finite and the construction is pointwise.  No global bundle, connection,
compatibility complex, PDE, boundary condition, or integration theorem is
asserted.
-/

namespace JanusFormal
namespace P0EFTJanusLorentzianGramCompatibilityFrechet

set_option autoImplicit false

noncomputable section

open scoped InnerProductSpace
open P0EFTJanusFiniteGramInducedMetricFrechetBridge
open P0EFTJanusFiniteJetCompatibilityNaturality
open P0EFTJanusFiniteJetCompatibilityPrincipalSymbol

universe u

/-- Explicit finite ambient Minkowski vector space.  Its topology and norm are
the auxiliary Euclidean ones used to formulate Frechet differentiability. -/
abbrev Ambient4 := EuclideanSpace ℝ (Fin 4)

variable {Tangent : Type u}
variable [NormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]

abbrev LorentzOneJet := Tangent →L[ℝ] Ambient4
abbrev LorentzMetricTensor := GramMetricTensor (Tangent := Tangent)

/-- Diagonal signs of the explicit Minkowski form. -/
def lorentzSign (index : Fin 4) : ℝ :=
  if index = 0 then -1 else 1

/-- Linear diagonal representative `diag(-1,1,1,1)` of `eta`. -/
def etaLinearMap : Ambient4 →ₗ[ℝ] Ambient4 where
  toFun := fun vector =>
    WithLp.toLp 2 (fun index => lorentzSign index * vector index)
  map_add' := by
    intro first second
    apply PiLp.ext
    intro index
    simp only [PiLp.add_apply]
    ring
  map_smul' := by
    intro scalar vector
    apply PiLp.ext
    intro index
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- Continuous Minkowski-sign operator.  Continuity is genuine because this
is a linear map between finite-dimensional normed spaces. -/
def etaOperator : Ambient4 →L[ℝ] Ambient4 :=
  LinearMap.toContinuousLinearMap etaLinearMap

@[simp]
theorem etaOperator_apply (vector : Ambient4) (index : Fin 4) :
    etaOperator vector index = lorentzSign index * vector index := by
  rfl

theorem etaOperator_involutive (vector : Ambient4) :
    etaOperator (etaOperator vector) = vector := by
  ext index
  fin_cases index <;> norm_num [lorentzSign]

/-- Explicit ambient Lorentzian bilinear form. -/
def lorentzPair (first second : Ambient4) : ℝ :=
  ⟪etaOperator first, second⟫_ℝ

theorem lorentzPair_coordinate_formula (first second : Ambient4) :
    lorentzPair first second =
      -(first 0 * second 0) + first 1 * second 1 +
        first 2 * second 2 + first 3 * second 3 := by
  simp [lorentzPair, PiLp.inner_apply, etaOperator_apply,
    lorentzSign, Fin.sum_univ_succ]
  ring

theorem lorentzPair_symmetric (first second : Ambient4) :
    lorentzPair first second = lorentzPair second first := by
  rw [lorentzPair_coordinate_formula, lorentzPair_coordinate_formula]
  ring

theorem lorentzPair_etaOperator_right (vector : Ambient4) :
    lorentzPair vector (etaOperator vector) =
      ⟪etaOperator vector, etaOperator vector⟫_ℝ := by
  rfl

/-- The displayed `eta` is nondegenerate. -/
theorem lorentzPair_left_nondegenerate
    (vector : Ambient4)
    (hOrthogonal : ∀ test : Ambient4, lorentzPair vector test = 0) :
    vector = 0 := by
  have hSelf :
      ⟪etaOperator vector, etaOperator vector⟫_ℝ = 0 := by
    simpa only [lorentzPair_etaOperator_right] using
      hOrthogonal (etaOperator vector)
  have hEtaZero : etaOperator vector = 0 := inner_self_eq_zero.mp hSelf
  calc
    vector = etaOperator (etaOperator vector) :=
      (etaOperator_involutive vector).symm
    _ = 0 := by rw [hEtaZero, map_zero]

local instance lorentzOneJetNormedAddCommGroup :
    NormedAddCommGroup (LorentzOneJet (Tangent := Tangent)) :=
  inferInstance

local instance lorentzOneJetNormedSpace :
    NormedSpace ℝ (LorentzOneJet (Tangent := Tangent)) :=
  inferInstance

local instance lorentzOneJetTopologicalSpace :
    TopologicalSpace (LorentzOneJet (Tangent := Tangent)) :=
  lorentzOneJetNormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

local instance lorentzOneJetAddCommGroup :
    AddCommGroup (LorentzOneJet (Tangent := Tangent)) :=
  lorentzOneJetNormedAddCommGroup.toAddCommGroup

local instance lorentzOneJetModule :
    Module ℝ (LorentzOneJet (Tangent := Tangent)) :=
  lorentzOneJetNormedSpace.toModule

local instance lorentzMetricTensorNormedAddCommGroup :
    NormedAddCommGroup (LorentzMetricTensor (Tangent := Tangent)) :=
  inferInstance

local instance lorentzMetricTensorNormedSpace :
    NormedSpace ℝ (LorentzMetricTensor (Tangent := Tangent)) :=
  inferInstance

local instance lorentzMetricTensorTopologicalSpace :
    TopologicalSpace (LorentzMetricTensor (Tangent := Tangent)) :=
  lorentzMetricTensorNormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

local instance lorentzMetricTensorAddCommGroup :
    AddCommGroup (LorentzMetricTensor (Tangent := Tangent)) :=
  lorentzMetricTensorNormedAddCommGroup.toAddCommGroup

local instance lorentzMetricTensorModule :
    Module ℝ (LorentzMetricTensor (Tangent := Tangent)) :=
  lorentzMetricTensorNormedSpace.toModule

local instance lorentzDerivativeNormedAddCommGroup :
    NormedAddCommGroup
      (LorentzOneJet (Tangent := Tangent) →L[ℝ]
        LorentzMetricTensor (Tangent := Tangent)) :=
  inferInstance

local instance lorentzDerivativeNormedSpace :
    NormedSpace ℝ
      (LorentzOneJet (Tangent := Tangent) →L[ℝ]
        LorentzMetricTensor (Tangent := Tangent)) :=
  inferInstance

local instance lorentzDerivativeTopologicalSpace :
    TopologicalSpace
      (LorentzOneJet (Tangent := Tangent) →L[ℝ]
        LorentzMetricTensor (Tangent := Tangent)) :=
  lorentzDerivativeNormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

local instance lorentzDerivativeAddCommGroup :
    AddCommGroup
      (LorentzOneJet (Tangent := Tangent) →L[ℝ]
        LorentzMetricTensor (Tangent := Tangent)) :=
  lorentzDerivativeNormedAddCommGroup.toAddCommGroup

local instance lorentzDerivativeModule :
    Module ℝ
      (LorentzOneJet (Tangent := Tangent) →L[ℝ]
        LorentzMetricTensor (Tangent := Tangent)) :=
  lorentzDerivativeNormedSpace.toModule

/-- Postcomposition of one-jets by the fixed Minkowski-sign operator. -/
def etaJetAction :
    LorentzOneJet (Tangent := Tangent) →L[ℝ]
      LorentzOneJet (Tangent := Tangent) :=
  (ContinuousLinearMap.compL ℝ Tangent Ambient4 Ambient4) etaOperator

@[simp]
theorem etaJetAction_apply
    (F : LorentzOneJet (Tangent := Tangent)) (x : Tangent) :
    etaJetAction F x = etaOperator (F x) := by
  rfl

/-- Continuous bilinear Lorentzian Gram pairing on one-jets. -/
def lorentzGramBilinear :
    LorentzOneJet (Tangent := Tangent) →L[ℝ]
      LorentzOneJet (Tangent := Tangent) →L[ℝ]
        LorentzMetricTensor (Tangent := Tangent) :=
  (gramBilinear (Tangent := Tangent) (Ambient := Ambient4)).comp etaJetAction

@[simp]
theorem lorentzGramBilinear_apply
    (first second : LorentzOneJet (Tangent := Tangent))
    (x y : Tangent) :
    lorentzGramBilinear first second x y =
      lorentzPair (first x) (second y) := by
  rfl

/-- Explicit compatibility operator `K(F) = F^T eta F`. -/
def lorentzGramCompatibilityOperator
    (F : LorentzOneJet (Tangent := Tangent)) :
    LorentzMetricTensor (Tangent := Tangent) :=
  lorentzGramBilinear F F

@[simp]
theorem lorentzGramCompatibilityOperator_apply
    (F : LorentzOneJet (Tangent := Tangent)) (x y : Tangent) :
    lorentzGramCompatibilityOperator F x y =
      lorentzPair (F x) (F y) := by
  rfl

theorem lorentzGramCompatibilityOperator_symmetric
    (F : LorentzOneJet (Tangent := Tangent)) (x y : Tangent) :
    lorentzGramCompatibilityOperator F x y =
      lorentzGramCompatibilityOperator F y x := by
  simp only [lorentzGramCompatibilityOperator_apply]
  exact lorentzPair_symmetric _ _

/-- Constant second derivative of the Lorentzian Gram map. -/
def lorentzGramSecondDerivative :
    LorentzOneJet (Tangent := Tangent) →L[ℝ]
      LorentzOneJet (Tangent := Tangent) →L[ℝ]
        LorentzMetricTensor (Tangent := Tangent) :=
  lorentzGramBilinear +
    lorentzGramBilinear.precompL
      (LorentzOneJet (Tangent := Tangent))
      (ContinuousLinearMap.id ℝ
        (LorentzOneJet (Tangent := Tangent)))

/-- Concrete Jacobian `J_F`. -/
def lorentzGramLinearization
    (F : LorentzOneJet (Tangent := Tangent)) :
    LorentzOneJet (Tangent := Tangent) →L[ℝ]
      LorentzMetricTensor (Tangent := Tangent) :=
  lorentzGramSecondDerivative F

@[simp]
theorem lorentzGramLinearization_apply
    (F H : LorentzOneJet (Tangent := Tangent)) (x y : Tangent) :
    lorentzGramLinearization F H x y =
      lorentzPair (H x) (F y) + lorentzPair (F x) (H y) := by
  simp [lorentzGramLinearization, lorentzGramSecondDerivative,
    lorentzGramBilinear_apply, lorentzPair_symmetric, add_comm]

/-- `J_F` is the genuine Frechet derivative of `K` on the full normed
one-jet space. -/
theorem lorentzGramCompatibilityOperator_hasFDerivAt
    (F : LorentzOneJet (Tangent := Tangent)) :
    HasFDerivAt lorentzGramCompatibilityOperator
      (lorentzGramLinearization F) F := by
  change @HasFDerivAt ℝ _
    (LorentzOneJet (Tangent := Tangent))
    lorentzOneJetNormedAddCommGroup.toAddCommGroup
    lorentzOneJetNormedSpace.toModule
    lorentzOneJetNormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    (LorentzMetricTensor (Tangent := Tangent))
    lorentzMetricTensorNormedAddCommGroup.toAddCommGroup
    lorentzMetricTensorNormedSpace.toModule
    lorentzMetricTensorNormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    (fun varied => lorentzGramBilinear varied varied)
    (lorentzGramLinearization F) F
  have h := lorentzGramBilinear.hasFDerivAt_of_bilinear
    (hasFDerivAt_id F) (hasFDerivAt_id F)
  simpa [lorentzGramLinearization,
    lorentzGramSecondDerivative] using h

theorem lorentzGramCompatibilityOperator_fderiv
    (F : LorentzOneJet (Tangent := Tangent)) :
    fderiv ℝ lorentzGramCompatibilityOperator F =
      lorentzGramLinearization F :=
  (lorentzGramCompatibilityOperator_hasFDerivAt F).fderiv

/-- Naturality under an arbitrary invertible source-frame change. -/
theorem lorentzGramCompatibilityOperator_source_natural
    (frame : Tangent ≃L[ℝ] Tangent)
    (F : LorentzOneJet (Tangent := Tangent)) :
    lorentzGramCompatibilityOperator (sourceFrameAction frame F) =
      sourceTensorPullback frame (lorentzGramCompatibilityOperator F) := by
  ext x y
  rfl

/-- The actual Jacobian intertwines source-frame changes. -/
theorem lorentzGramLinearization_source_intertwines
    (frame : Tangent ≃L[ℝ] Tangent)
    (F H : LorentzOneJet (Tangent := Tangent)) :
    lorentzGramLinearization (sourceFrameAction frame F)
        (sourceFrameAction frame H) =
      sourceTensorPullback frame (lorentzGramLinearization F H) := by
  ext x y
  rfl

/-- Honest defining condition for a continuous ambient `eta`-isometry. -/
def EtaIsometry (ambientFrame : Ambient4 ≃L[ℝ] Ambient4) : Prop :=
  ∀ first second,
    lorentzPair (ambientFrame first) (ambientFrame second) =
      lorentzPair first second

def ambientEtaIsometryAction
    (ambientFrame : Ambient4 ≃L[ℝ] Ambient4)
    (F : LorentzOneJet (Tangent := Tangent)) :
    LorentzOneJet (Tangent := Tangent) :=
  ambientFrame.toContinuousLinearMap.comp F

@[simp]
theorem ambientEtaIsometryAction_apply
    (ambientFrame : Ambient4 ≃L[ℝ] Ambient4)
    (F : LorentzOneJet (Tangent := Tangent)) (x : Tangent) :
    ambientEtaIsometryAction ambientFrame F x = ambientFrame (F x) := by
  rfl

/-- Ambient `eta`-isometries leave `K` invariant. -/
theorem lorentzGramCompatibilityOperator_ambient_invariant
    (ambientFrame : Ambient4 ≃L[ℝ] Ambient4)
    (hFrame : EtaIsometry ambientFrame)
    (F : LorentzOneJet (Tangent := Tangent)) :
    lorentzGramCompatibilityOperator
        (ambientEtaIsometryAction ambientFrame F) =
      lorentzGramCompatibilityOperator F := by
  ext x y
  exact hFrame (F x) (F y)

/-- Simultaneous ambient `eta`-isometry action leaves `J` invariant. -/
theorem lorentzGramLinearization_ambient_intertwines
    (ambientFrame : Ambient4 ≃L[ℝ] Ambient4)
    (hFrame : EtaIsometry ambientFrame)
    (F H : LorentzOneJet (Tangent := Tangent)) :
    lorentzGramLinearization (ambientEtaIsometryAction ambientFrame F)
        (ambientEtaIsometryAction ambientFrame H) =
      lorentzGramLinearization F H := by
  ext x y
  simp only [lorentzGramLinearization_apply, ambientEtaIsometryAction_apply]
  rw [hFrame, hFrame]

/-- Lie-algebra condition for an infinitesimal ambient `eta`-isometry. -/
def EtaAntisymmetric (generator : Ambient4 →L[ℝ] Ambient4) : Prop :=
  ∀ first second,
    lorentzPair (generator first) second +
      lorentzPair first (generator second) = 0

def ambientEtaInfinitesimalDirection
    (generator : Ambient4 →L[ℝ] Ambient4)
    (F : LorentzOneJet (Tangent := Tangent)) :
    LorentzOneJet (Tangent := Tangent) :=
  generator.comp F

@[simp]
theorem ambientEtaInfinitesimalDirection_apply
    (generator : Ambient4 →L[ℝ] Ambient4)
    (F : LorentzOneJet (Tangent := Tangent)) (x : Tangent) :
    ambientEtaInfinitesimalDirection generator F x = generator (F x) := by
  rfl

/-- Every infinitesimal `eta`-isometry is killed by `J_F`. -/
theorem lorentzGramLinearization_ambientInfinitesimal_eq_zero
    (generator : Ambient4 →L[ℝ] Ambient4)
    (hGenerator : EtaAntisymmetric generator)
    (F : LorentzOneJet (Tangent := Tangent)) :
    lorentzGramLinearization F
        (ambientEtaInfinitesimalDirection generator F) = 0 := by
  ext x y
  simpa only [lorentzGramLinearization_apply,
    ambientEtaInfinitesimalDirection_apply, zero_apply] using
    hGenerator (F x) (F y)

theorem ambientEtaInfinitesimalDirection_mem_ker
    (generator : Ambient4 →L[ℝ] Ambient4)
    (hGenerator : EtaAntisymmetric generator)
    (F : LorentzOneJet (Tangent := Tangent)) :
    ambientEtaInfinitesimalDirection generator F ∈
      LinearMap.ker (lorentzGramLinearization F).toLinearMap := by
  rw [LinearMap.mem_ker]
  exact lorentzGramLinearization_ambientInfinitesimal_eq_zero
    generator hGenerator F

/-- For an invertible one-jet, the infinitesimal ambient Lorentz directions
are exactly the full kernel of `J_F`. -/
theorem lorentzGramLinearization_kernel_exact_of_equiv
    (frame : Tangent ≃L[ℝ] Ambient4)
    (H : LorentzOneJet (Tangent := Tangent)) :
    lorentzGramLinearization frame.toContinuousLinearMap H = 0 ↔
      ∃ generator : Ambient4 →L[ℝ] Ambient4,
        EtaAntisymmetric generator ∧
          H = generator.comp frame.toContinuousLinearMap := by
  constructor
  · intro hKernel
    let generator : Ambient4 →L[ℝ] Ambient4 :=
      H.comp frame.symm.toContinuousLinearMap
    refine ⟨generator, ?_, ?_⟩
    · intro first second
      have hApplied := congrArg
        (fun tensor => tensor (frame.symm first) (frame.symm second)) hKernel
      simp only [lorentzGramLinearization_apply, zero_apply] at hApplied
      have hApplied' :
          lorentzPair (H (frame.symm first)) second +
              lorentzPair first (H (frame.symm second)) = 0 := by
        simpa using hApplied
      change lorentzPair (H (frame.symm first)) second +
          lorentzPair first (H (frame.symm second)) = 0
      exact hApplied'
    · ext x
      simp [generator]
  · rintro ⟨generator, hGenerator, rfl⟩
    exact lorentzGramLinearization_ambientInfinitesimal_eq_zero
      generator hGenerator frame.toContinuousLinearMap

/-- Rank-one one-jet `x ↦ xi(x) V`. -/
def lorentzRankOneJet
    (covector : Tangent →L[ℝ] ℝ) (variation : Ambient4) :
    LorentzOneJet (Tangent := Tangent) :=
  covector.smulRight variation

@[simp]
theorem lorentzRankOneJet_apply
    (covector : Tangent →L[ℝ] ℝ) (variation : Ambient4)
    (x : Tangent) :
    lorentzRankOneJet covector variation x = covector x • variation := by
  rfl

/-- Nonzero-frequency principal symbol of the Lorentzian compatibility
linearization. -/
def lorentzGramPrincipalSymbol
    (F : LorentzOneJet (Tangent := Tangent))
    (covector : Tangent →L[ℝ] ℝ) :
    Ambient4 →L[ℝ] LorentzMetricTensor (Tangent := Tangent) :=
  (lorentzGramLinearization F).comp
    ((ContinuousLinearMap.smulRightL ℝ Tangent Ambient4) covector)

@[simp]
theorem lorentzGramPrincipalSymbol_apply
    (F : LorentzOneJet (Tangent := Tangent))
    (covector : Tangent →L[ℝ] ℝ) (variation : Ambient4)
    (x y : Tangent) :
    lorentzGramPrincipalSymbol F covector variation x y =
      covector x * lorentzPair variation (F y) +
        covector y * lorentzPair (F x) variation := by
  simp [lorentzGramPrincipalSymbol, lorentzGramLinearization_apply,
    lorentzPair, real_inner_smul_left, real_inner_smul_right]

/-- Exact kernel of the nonzero-frequency symbol: the ambient normal space
with respect to the nondegenerate Lorentzian form. -/
theorem lorentzGramPrincipalSymbol_eq_zero_iff_range_etaOrthogonal
    (F : LorentzOneJet (Tangent := Tangent))
    (covector : Tangent →L[ℝ] ℝ) (variation : Ambient4)
    (hCovector : covector ≠ 0) :
    lorentzGramPrincipalSymbol F covector variation = 0 ↔
      ∀ y : Tangent, lorentzPair variation (F y) = 0 := by
  constructor
  · intro hSymbol
    obtain ⟨x, hx⟩ := exists_apply_ne_zero_of_ne_zero covector hCovector
    have hDiagonal := congrArg (fun tensor => tensor x x) hSymbol
    simp only [lorentzGramPrincipalSymbol_apply, zero_apply] at hDiagonal
    rw [lorentzPair_symmetric (F x) variation] at hDiagonal
    have hInnerX : lorentzPair variation (F x) = 0 := by
      have hTwice :
          covector x * (2 * lorentzPair variation (F x)) = 0 := by
        calc
          covector x * (2 * lorentzPair variation (F x)) =
              covector x * lorentzPair variation (F x) +
                covector x * lorentzPair variation (F x) := by ring
          _ = 0 := hDiagonal
      have hTwoInner : 2 * lorentzPair variation (F x) = 0 :=
        (mul_eq_zero.mp hTwice).resolve_left hx
      linarith
    intro y
    have hMixed := congrArg (fun tensor => tensor x y) hSymbol
    simp only [lorentzGramPrincipalSymbol_apply, zero_apply] at hMixed
    rw [lorentzPair_symmetric (F x) variation, hInnerX,
      mul_zero, add_zero] at hMixed
    exact (mul_eq_zero.mp hMixed).resolve_left hx
  · intro hOrthogonal
    ext x y
    simp only [lorentzGramPrincipalSymbol_apply, zero_apply]
    rw [hOrthogonal y, lorentzPair_symmetric (F x) variation,
      hOrthogonal x]
    ring

/-- Surjectivity of `F`, together with explicit nondegeneracy of `eta`, makes
the nonzero-frequency symbol injective. -/
theorem lorentzGramPrincipalSymbol_injective_of_surjective
    (F : LorentzOneJet (Tangent := Tangent))
    (hSurjective : Function.Surjective F)
    (covector : Tangent →L[ℝ] ℝ) (hCovector : covector ≠ 0) :
    Function.Injective (lorentzGramPrincipalSymbol F covector) := by
  intro first second hEqual
  apply sub_eq_zero.mp
  have hKernel :
      lorentzGramPrincipalSymbol F covector (first - second) = 0 := by
    rw [map_sub, hEqual, sub_self]
  have hOrthogonal :=
    (lorentzGramPrincipalSymbol_eq_zero_iff_range_etaOrthogonal
      F covector (first - second) hCovector).mp hKernel
  apply lorentzPair_left_nondegenerate
  intro test
  obtain ⟨preimage, hPreimage⟩ := hSurjective test
  rw [← hPreimage]
  exact hOrthogonal preimage

end

end P0EFTJanusLorentzianGramCompatibilityFrechet
end JanusFormal
