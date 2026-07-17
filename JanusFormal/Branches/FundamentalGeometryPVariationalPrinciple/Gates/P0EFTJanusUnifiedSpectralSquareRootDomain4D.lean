import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusComplexConjugatePairRoot4D

/-!
# Unified four-dimensional spectral square-root domain

This gate combines the three spectral sectors already constructed:

* supplied positive real Jordan presentations;
* the exact negative/zero Jordan criterion;
* supplied purely nonreal real-Jordan presentations.

The final admissible datum contains one direct spectral certificate followed
by an arbitrary real similarity.  Its root selector and square law are
unconditional except that the criterion-only branch receives the classical
real Jordan classification as a local argument.

For raw matrices, exactly three missing presentation/classification results
are bundled in `RawMatrixSpectralBridges4`.  No exhaustiveness statement is
made without that bundle.
-/

namespace JanusFormal
namespace P0EFTJanusUnifiedSpectralSquareRootDomain4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusMatrixSquareRootFrechetSylvester
open P0EFTJanusPositiveRealJordanPartitionSelector4D
open P0EFTJanusPositiveRealJordanPresentationBridge4D
open P0EFTJanusRealSquareRootSpectralObstructions4D
open P0EFTJanusComplexConjugatePairRoot4D

abbrev Matrix4 := P0EFTJanusComplexConjugatePairRoot4D.Matrix4

/-- The three direct spectral certificates.  They may overlap; the purpose
is a sound union, not an artificial disjoint partition. -/
inductive DirectSpectralCertificate4 (target : Matrix4) where
  | positive :
      HasPositiveRealJordanPresentation target →
        DirectSpectralCertificate4 target
  | jordanCriterion :
      RealSquareRootJordanCriterion4 target →
        DirectSpectralCertificate4 target
  | pureNonreal :
      HasPureNonrealJordanPresentation4 target →
        DirectSpectralCertificate4 target

/-- Noncomputable selector on the exact Jordan criterion. -/
noncomputable def jordanCriterionSelectedRoot
    (bridge : RealSquareRootJordanClassificationBridge4)
    (target : Matrix4) (hCriterion : RealSquareRootJordanCriterion4 target) :
    Matrix4 :=
  Classical.choose ((bridge target).2 hCriterion)

theorem jordanCriterionSelectedRoot_square
    (bridge : RealSquareRootJordanClassificationBridge4)
    (target : Matrix4) (hCriterion : RealSquareRootJordanCriterion4 target) :
    jordanCriterionSelectedRoot bridge target hCriterion *
        jordanCriterionSelectedRoot bridge target hCriterion = target :=
  Classical.choose_spec ((bridge target).2 hCriterion)

/-- Noncomputable selector from a supplied purely nonreal presentation.  All
canonical block algebra behind this witness is unconditional. -/
noncomputable def pureNonrealPresentationSelectedRoot
    (target : Matrix4) (hPresentation : HasPureNonrealJordanPresentation4 target) :
    Matrix4 :=
  Classical.choose
    (hasRealSquareRoot_of_pureNonrealJordanPresentation hPresentation)

theorem pureNonrealPresentationSelectedRoot_square
    (target : Matrix4) (hPresentation : HasPureNonrealJordanPresentation4 target) :
    pureNonrealPresentationSelectedRoot target hPresentation *
        pureNonrealPresentationSelectedRoot target hPresentation = target :=
  Classical.choose_spec
    (hasRealSquareRoot_of_pureNonrealJordanPresentation hPresentation)

/-- Root selector for a direct certificate. -/
noncomputable def directSpectralRoot
    (bridge : RealSquareRootJordanClassificationBridge4)
    {target : Matrix4} : DirectSpectralCertificate4 target → Matrix4
  | .positive hPresentation =>
      positiveRealJordanRootOfPresentable ⟨target, hPresentation⟩
  | .jordanCriterion hCriterion =>
      jordanCriterionSelectedRoot bridge target hCriterion
  | .pureNonreal hPresentation =>
      pureNonrealPresentationSelectedRoot target hPresentation

theorem directSpectralRoot_square
    (bridge : RealSquareRootJordanClassificationBridge4)
    {target : Matrix4} (certificate : DirectSpectralCertificate4 target) :
    directSpectralRoot bridge certificate *
        directSpectralRoot bridge certificate = target := by
  cases certificate with
  | positive hPresentation =>
      exact positiveRealJordanRootOfPresentable_square
        ⟨target, hPresentation⟩
  | jordanCriterion hCriterion =>
      exact jordanCriterionSelectedRoot_square bridge target hCriterion
  | pureNonreal hPresentation =>
      exact pureNonrealPresentationSelectedRoot_square target hPresentation

/-- One final admissible type: a direct spectral certificate at a canonical
matrix and an invertible real change of basis to the requested target. -/
structure UnifiedSpectralAdmissible4 (target : Matrix4) where
  canonical : Matrix4
  certificate : DirectSpectralCertificate4 canonical
  change : Matrix4
  inverse : Matrix4
  change_inverse : change * inverse = 1
  inverse_change : inverse * change = 1
  target_eq : target = change * canonical * inverse

def DirectSpectralCertificate4.toUnified
    {target : Matrix4} (certificate : DirectSpectralCertificate4 target) :
    UnifiedSpectralAdmissible4 target where
  canonical := target
  certificate := certificate
  change := 1
  inverse := 1
  change_inverse := by simp
  inverse_change := by simp
  target_eq := by simp

/-- Similarities compose inside the unified admissible type. -/
def UnifiedSpectralAdmissible4.transport
    {sourceTarget target : Matrix4}
    (source : UnifiedSpectralAdmissible4 sourceTarget)
    (change inverse : Matrix4)
    (hChangeInverse : change * inverse = 1)
    (hInverseChange : inverse * change = 1)
    (hTarget : target = change * sourceTarget * inverse) :
    UnifiedSpectralAdmissible4 target where
  canonical := source.canonical
  certificate := source.certificate
  change := change * source.change
  inverse := source.inverse * inverse
  change_inverse := by
    calc
      (change * source.change) * (source.inverse * inverse) =
          change * (source.change * source.inverse) * inverse := by
        noncomm_ring
      _ = change * inverse := by rw [source.change_inverse]; simp
      _ = 1 := hChangeInverse
  inverse_change := by
    calc
      (source.inverse * inverse) * (change * source.change) =
          source.inverse * (inverse * change) * source.change := by
        noncomm_ring
      _ = source.inverse * source.change := by rw [hInverseChange]; simp
      _ = 1 := source.inverse_change
  target_eq := by
    calc
      target = change * sourceTarget * inverse := hTarget
      _ = change * (source.change * source.canonical * source.inverse) *
          inverse := by
        exact congrArg (fun matrix : Matrix4 => change * matrix * inverse)
          source.target_eq
      _ = (change * source.change) * source.canonical *
          (source.inverse * inverse) := by noncomm_ring

/-- Transport a root through one supplied similarity. -/
def similarityTransportRoot
    (change inverse root : Matrix4) : Matrix4 :=
  change * root * inverse

theorem similarityTransportRoot_square
    {target canonical change inverse root : Matrix4}
    (hRoot : root * root = canonical)
    (hInverseChange : inverse * change = 1)
    (hTarget : target = change * canonical * inverse) :
    similarityTransportRoot change inverse root *
        similarityTransportRoot change inverse root = target := by
  unfold similarityTransportRoot
  calc
    (change * root * inverse) * (change * root * inverse) =
        change * root * (inverse * change) * root * inverse := by
      noncomm_ring
    _ = change * (root * root) * inverse := by
      rw [hInverseChange]
      noncomm_ring
    _ = change * canonical * inverse := by rw [hRoot]
    _ = target := hTarget.symm

/-- Unified selector, including the stored similarity transport. -/
noncomputable def unifiedSpectralRoot
    (bridge : RealSquareRootJordanClassificationBridge4)
    {target : Matrix4} (admissible : UnifiedSpectralAdmissible4 target) :
    Matrix4 :=
  similarityTransportRoot admissible.change admissible.inverse
    (directSpectralRoot bridge admissible.certificate)

theorem unifiedSpectralRoot_square
    (bridge : RealSquareRootJordanClassificationBridge4)
    {target : Matrix4} (admissible : UnifiedSpectralAdmissible4 target) :
    unifiedSpectralRoot bridge admissible *
        unifiedSpectralRoot bridge admissible = target :=
  similarityTransportRoot_square
    (directSpectralRoot_square bridge admissible.certificate)
    admissible.inverse_change admissible.target_eq

def HasUnifiedSpectralAdmissibility4 (target : Matrix4) : Prop :=
  Nonempty (UnifiedSpectralAdmissible4 target)

/-- The three raw matrix conditions.  The general Jordan criterion branch is
the only one intended to be complete after its classification bridge. -/
inductive RawSpectralCertificate4 (target : Matrix4) where
  | positive :
      PositiveRealSplitCharpoly4 target → RawSpectralCertificate4 target
  | jordanCriterion :
      RealSquareRootJordanCriterion4 target → RawSpectralCertificate4 target
  | pureNonreal :
      PureNonrealConjugatePairCharpoly4 target → RawSpectralCertificate4 target

/-- Exactly the three raw-matrix results unavailable in the current library. -/
structure RawMatrixSpectralBridges4 where
  positivePresentation : PositiveRealJordanBasisBridge4
  jordanClassification : RealSquareRootJordanClassificationBridge4
  pureNonrealPresentation : PureNonrealJordanPresentationBridge4

/-- Resolve raw spectral evidence into a direct presentation/certificate. -/
def resolveRawSpectralCertificate
    (bridges : RawMatrixSpectralBridges4)
    {target : Matrix4} :
    RawSpectralCertificate4 target → DirectSpectralCertificate4 target
  | .positive hSpectrum =>
      .positive (bridges.positivePresentation target hSpectrum)
  | .jordanCriterion hCriterion => .jordanCriterion hCriterion
  | .pureNonreal hSpectrum =>
      .pureNonreal (bridges.pureNonrealPresentation target hSpectrum)

def resolveRawUnifiedAdmissible
    (bridges : RawMatrixSpectralBridges4)
    {target : Matrix4} (certificate : RawSpectralCertificate4 target) :
    UnifiedSpectralAdmissible4 target :=
  (resolveRawSpectralCertificate bridges certificate).toUnified

/-- Root selector directly from one raw spectral certificate and the three
explicit bridges. -/
noncomputable def rawSpectralRoot
    (bridges : RawMatrixSpectralBridges4)
    {target : Matrix4} (certificate : RawSpectralCertificate4 target) :
    Matrix4 :=
  unifiedSpectralRoot bridges.jordanClassification
    (resolveRawUnifiedAdmissible bridges certificate)

theorem rawSpectralRoot_square
    (bridges : RawMatrixSpectralBridges4)
    {target : Matrix4} (certificate : RawSpectralCertificate4 target) :
    rawSpectralRoot bridges certificate * rawSpectralRoot bridges certificate =
      target :=
  unifiedSpectralRoot_square bridges.jordanClassification
    (resolveRawUnifiedAdmissible bridges certificate)

def HasRawSpectralCertificate4 (target : Matrix4) : Prop :=
  Nonempty (RawSpectralCertificate4 target)

def RawSpectrallyAdmissibleMatrix4 :=
  {target : Matrix4 // HasRawSpectralCertificate4 target}

noncomputable def chosenRawSpectralCertificate
    (target : RawSpectrallyAdmissibleMatrix4) :
    RawSpectralCertificate4 target.1 :=
  Classical.choice target.property

noncomputable def rawAdmissibleMatrixRoot
    (bridges : RawMatrixSpectralBridges4)
    (target : RawSpectrallyAdmissibleMatrix4) : Matrix4 :=
  rawSpectralRoot bridges (chosenRawSpectralCertificate target)

theorem rawAdmissibleMatrixRoot_square
    (bridges : RawMatrixSpectralBridges4)
    (target : RawSpectrallyAdmissibleMatrix4) :
    rawAdmissibleMatrixRoot bridges target *
        rawAdmissibleMatrixRoot bridges target = target.1 :=
  rawSpectralRoot_square bridges (chosenRawSpectralCertificate target)

/-- Conditional completeness is stated only with all three missing raw
bridges visible.  The reverse implication uses the exact Jordan criterion. -/
theorem hasRealSquareRoot_iff_hasRawSpectralCertificate
    (bridges : RawMatrixSpectralBridges4) (target : Matrix4) :
    HasRealSquareRoot target ↔ HasRawSpectralCertificate4 target := by
  constructor
  · intro hRoot
    exact ⟨.jordanCriterion
      ((bridges.jordanClassification target).1 hRoot)⟩
  · rintro ⟨certificate⟩
    exact ⟨rawSpectralRoot bridges certificate,
      rawSpectralRoot_square bridges certificate⟩

/-- Coarse provenance tag.  It records which proof route was supplied; it is
not asserted to be a disjoint spectral decomposition. -/
inductive SpectralCertificateRegime4 where
  | positiveInterior
  | jordanBoundaryAware
  | pureNonrealOffCut
  deriving DecidableEq

def DirectSpectralCertificate4.regime
    {target : Matrix4} : DirectSpectralCertificate4 target →
      SpectralCertificateRegime4
  | .positive _ => .positiveInterior
  | .jordanCriterion _ => .jordanBoundaryAware
  | .pureNonreal _ => .pureNonrealOffCut

def RawSpectralCertificate4.regime
    {target : Matrix4} : RawSpectralCertificate4 target →
      SpectralCertificateRegime4
  | .positive _ => .positiveInterior
  | .jordanCriterion _ => .jordanBoundaryAware
  | .pureNonreal _ => .pureNonrealOffCut

theorem resolveRawSpectralCertificate_regime
    (bridges : RawMatrixSpectralBridges4)
    {target : Matrix4} (certificate : RawSpectralCertificate4 target) :
    (resolveRawSpectralCertificate bridges certificate).regime =
      certificate.regime := by
  cases certificate <;> rfl

/-- Positive raw data are strictly inside the positive-real root domain. -/
theorem positiveRaw_charpoly_roots_strictly_positive
    {target : Matrix4} (hSpectrum : PositiveRealSplitCharpoly4 target)
    (eigenvalue : Real) (hRoot : target.charpoly.IsRoot eigenvalue) :
    0 < eigenvalue :=
  hSpectrum.2 eigenvalue hRoot

/-- A purely nonreal factorization is automatically off the principal cut
for both conjugate pairs. -/
theorem pureNonrealRaw_parameters_off_principal_cut
    {target : Matrix4} (hSpectrum : PureNonrealConjugatePairCharpoly4 target) :
    ∃ firstReal firstImag secondReal secondImag : Real,
      firstImag ≠ 0 ∧ secondImag ≠ 0 ∧
        target.charpoly =
          conjugatePairQuadratic firstReal firstImag *
            conjugatePairQuadratic secondReal secondImag ∧
        0 < complexPairRadius firstReal firstImag + firstReal ∧
        0 < complexPairRadius secondReal secondImag + secondReal := by
  obtain ⟨firstReal, firstImag, secondReal, secondImag,
    hFirstImag, hSecondImag, hCharpoly⟩ := hSpectrum
  exact ⟨firstReal, firstImag, secondReal, secondImag,
    hFirstImag, hSecondImag, hCharpoly,
    (complexPairPrincipalBranch_iff firstReal firstImag).2 (Or.inl hFirstImag),
    (complexPairPrincipalBranch_iff secondReal secondImag).2
      (Or.inl hSecondImag)⟩

/-- The boundary-aware branch exposes exactly the already proved negative
parity and zero-primary admissibility conditions. -/
theorem jordanCriterion_boundary_components
    {target : Matrix4} (hCriterion : RealSquareRootJordanCriterion4 target) :
    NegativeJordanBlockParity4 target ∧ ZeroJordanSquareAdmissible4 target :=
  hCriterion

/-- The positive presented selector retains its Sylvester regularity inside
the unified raw selector. -/
theorem positiveRaw_root_sylvester_bijective
    (bridges : RawMatrixSpectralBridges4)
    {target : Matrix4} (hSpectrum : PositiveRealSplitCharpoly4 target) :
    Function.Bijective
      (sylvesterOperator
        (rawSpectralRoot bridges (.positive hSpectrum))) := by
  simpa [rawSpectralRoot, resolveRawUnifiedAdmissible,
    resolveRawSpectralCertificate, DirectSpectralCertificate4.toUnified,
    unifiedSpectralRoot, similarityTransportRoot, directSpectralRoot] using
    (positiveRealJordanRootOfPresentable_sylvester_bijective
      ⟨target, bridges.positivePresentation target hSpectrum⟩)

/-- At the zero endpoint the square-map linearization is genuinely singular. -/
theorem zero_boundary_sylvester_not_injective :
    ¬ Function.Injective (sylvesterOperator (0 : Matrix4)) :=
  sylvesterOperator_zero_not_injective

end

end P0EFTJanusUnifiedSpectralSquareRootDomain4D
end JanusFormal
