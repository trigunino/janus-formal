import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT06FullPhysicalGaugeGradientBRSTJetComplex4D

/-!
# Full physical carrier with scalar-ghost-derived Abelian BRST

This gate replaces Gate900's four independent gauge-gradient jets by the
formal spatial derivatives of four scalar ghost jets: two Abelian ghost
components in each of the two physical sectors.  A ghost jet has one order
more than the physical jet.  Its first spatial coefficients reconstruct four
actual framed covectors, which are inserted in the four genuine gauge slots.

The resulting heterogeneous jet differential is linear, square-zero, and
commutes with the correctly shifted truncation and formal total derivative
maps.  Its realization in Gate900 is a chain map.  The reconstruction uses
the fixed Gate870 throat basis.  It does not assert frame covariance, a
Grassmann realization, or the nonlinear diffeomorphism BRST differential.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT06FullPhysicalScalarGhostBRSTJetComplex4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000
noncomputable section

open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusD8NonabelianGhostFinitePositiveMetricBVMaster4D
open P0EFTJanusProgramPActualPhysicalSecondOrderJetProductVectorBundleCore4D
open P0EFTJanusProgramPT06ThroatSpatialMultiindexSecondJetBridge4D
open P0EFTJanusProgramPT06ThroatSpatialFinsuppJetTower4D
open P0EFTJanusProgramPT06ActualPhysicalValueProductSecondJetBridge4D
open P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D
open P0EFTJanusProgramPT06FiniteMetricBVJetProlongation4D
open P0EFTJanusProgramPT06FullPhysicalGaugeGradientBRSTJetComplex4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

attribute [local instance]
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductNormedAddCommGroup
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductNormedSpace
  P0EFTJanusProgramPT06ActualPhysicalFinsuppSecondJetLinearBridge4D.actualPhysicalValueProductFinsuppSecondJetFiniteDimensional

private abbrev GaugeCovector := ActualGaugeValueFiber
private abbrev GaugeValueFiber := ActualGaugeValueProductFiber
private abbrev PhysicalValueFiber := ActualPhysicalValueProductFiber

/-- Four scalar Abelian ghosts, nested as two ghost components in each of two
physical sectors. -/
abbrev ProgramPT06PairedAbelianScalarGhostFiber4D :=
  Prod (Prod Real Real) (Prod Real Real)

/-- Gate875 jets of the four scalar Abelian ghosts. -/
abbrev ProgramPT06PairedAbelianScalarGhostSpatialJet4D (order : Nat) :=
  TruncatedThroatSpatialMultiindexJet
    ProgramPT06PairedAbelianScalarGhostFiber4D order

private theorem programPT06GaugeCovector_ext_basis
    {first second : GaugeCovector}
    (hBasis : forall direction : Fin 3,
      first (programPT06ThroatSpatialBasis direction) =
        second (programPT06ThroatSpatialBasis direction)) :
    first = second := by
  apply ContinuousLinearMap.ext
  intro vector
  rw [(programPT06ThroatSpatialBasis.sum_repr vector).symm]
  simp only [map_sum, map_smul, hBasis]

/-- Reconstruct a genuine framed covector from the first spatial coefficients
of a scalar Gate875 jet above one fixed lower-order multi-index. -/
private def programPT06ScalarGhostSpatialGradientAt
    {order : Nat}
    (jet : TruncatedThroatSpatialMultiindexJet Real (order + 1))
    (index : ThroatSpatialTruncatedIndex order) : GaugeCovector :=
  LinearMap.toContinuousLinearMap
    (programPT06ThroatSpatialBasis.constr Real fun direction =>
      throatSpatialTotalDerivative direction jet index)

@[simp] private theorem programPT06ScalarGhostSpatialGradientAt_basis
    {order : Nat}
    (jet : TruncatedThroatSpatialMultiindexJet Real (order + 1))
    (index : ThroatSpatialTruncatedIndex order)
    (direction : Fin 3) :
    programPT06ScalarGhostSpatialGradientAt jet index
        (programPT06ThroatSpatialBasis direction) =
      throatSpatialTotalDerivative direction jet index := by
  simp [programPT06ScalarGhostSpatialGradientAt]

private theorem programPT06ScalarGhostSpatialGradientAt_add
    {order : Nat}
    (first second : TruncatedThroatSpatialMultiindexJet Real (order + 1))
    (index : ThroatSpatialTruncatedIndex order) :
    programPT06ScalarGhostSpatialGradientAt (first + second) index =
      programPT06ScalarGhostSpatialGradientAt first index +
        programPT06ScalarGhostSpatialGradientAt second index := by
  apply programPT06GaugeCovector_ext_basis
  intro direction
  simp [throatSpatialTotalDerivative]

private theorem programPT06ScalarGhostSpatialGradientAt_smul
    {order : Nat} (scalar : Real)
    (jet : TruncatedThroatSpatialMultiindexJet Real (order + 1))
    (index : ThroatSpatialTruncatedIndex order) :
    programPT06ScalarGhostSpatialGradientAt (scalar • jet) index =
      scalar • programPT06ScalarGhostSpatialGradientAt jet index := by
  apply programPT06GaugeCovector_ext_basis
  intro direction
  rw [programPT06ScalarGhostSpatialGradientAt_basis]
  calc
    throatSpatialTotalDerivative direction (scalar • jet) index =
        scalar * throatSpatialTotalDerivative direction jet index := by
      rfl
    _ = scalar *
        programPT06ScalarGhostSpatialGradientAt jet index
          (programPT06ThroatSpatialBasis direction) := by
      rw [programPT06ScalarGhostSpatialGradientAt_basis]
    _ = (scalar • programPT06ScalarGhostSpatialGradientAt jet index)
          (programPT06ThroatSpatialBasis direction) := by
      simpa only [smul_eq_mul] using
        (smul_apply
          (programPT06ScalarGhostSpatialGradientAt jet index) scalar
          (programPT06ThroatSpatialBasis direction)).symm

/-- The linear spatial differential from scalar jets of order `order + 1` to
covector jets of order `order`. -/
def programPT06ScalarGhostSpatialDC (order : Nat) :
    LinearMap (RingHom.id Real)
      (TruncatedThroatSpatialMultiindexJet Real (order + 1))
      (TruncatedThroatSpatialMultiindexJet GaugeCovector order) where
  toFun jet index := programPT06ScalarGhostSpatialGradientAt jet index
  map_add' first second := by
    funext index
    exact programPT06ScalarGhostSpatialGradientAt_add first second index
  map_smul' scalar jet := by
    funext index
    exact programPT06ScalarGhostSpatialGradientAt_smul scalar jet index

@[simp] theorem programPT06ScalarGhostSpatialDC_apply_basis
    (order : Nat)
    (jet : TruncatedThroatSpatialMultiindexJet Real (order + 1))
    (index : ThroatSpatialTruncatedIndex order)
    (direction : Fin 3) :
    programPT06ScalarGhostSpatialDC order jet index
        (programPT06ThroatSpatialBasis direction) =
      throatSpatialTotalDerivative direction jet index := by
  exact programPT06ScalarGhostSpatialGradientAt_basis jet index direction

/-- The scalar spatial differential uses the shifted jet order under
truncation. -/
theorem programPT06ScalarGhostSpatialDC_commutes_truncation
    {lower higher : Nat} (hOrder : lower <= higher)
    (jet : TruncatedThroatSpatialMultiindexJet Real (higher + 1)) :
    truncateThroatSpatialMultiindexJet hOrder
        (programPT06ScalarGhostSpatialDC higher jet) =
      programPT06ScalarGhostSpatialDC lower
        (truncateThroatSpatialMultiindexJet
          (Nat.add_le_add_right hOrder 1) jet) := by
  funext index
  apply programPT06GaugeCovector_ext_basis
  intro direction
  simp only [truncateThroatSpatialMultiindexJet,
    programPT06ScalarGhostSpatialDC_apply_basis,
    throatSpatialTotalDerivative]

/-- The scalar spatial differential commutes with formal total derivatives;
the source scalar jet carries the required two extra orders. -/
theorem programPT06ScalarGhostSpatialDC_commutes_totalDerivative
    {order : Nat} (direction : Fin 3)
    (jet : TruncatedThroatSpatialMultiindexJet Real ((order + 1) + 1)) :
    throatSpatialTotalDerivative direction
        (programPT06ScalarGhostSpatialDC (order + 1) jet) =
      programPT06ScalarGhostSpatialDC order
        (throatSpatialTotalDerivative direction jet) := by
  funext index
  apply programPT06GaugeCovector_ext_basis
  intro gradientDirection
  change
    programPT06ScalarGhostSpatialDC (order + 1) jet
        (show ThroatSpatialTruncatedIndex (order + 1) from
          { val := index.1 + throatSpatialCoordinateMultiIndex direction
            property := by
              rw [throatSpatialMultiIndexOrder_add_coordinateMultiIndex]
              omega })
        (programPT06ThroatSpatialBasis gradientDirection) =
      programPT06ScalarGhostSpatialDC order
        (throatSpatialTotalDerivative direction jet) index
        (programPT06ThroatSpatialBasis gradientDirection)
  rw [programPT06ScalarGhostSpatialDC_apply_basis,
    programPT06ScalarGhostSpatialDC_apply_basis]
  exact congrFun
    (throatSpatialTotalDerivative_comm
      (Fiber := Real) direction gradientDirection jet) index

private def programPT06ScalarGhostFirstFirstProjection (order : Nat) :
    LinearMap (RingHom.id Real)
      (ProgramPT06PairedAbelianScalarGhostSpatialJet4D order)
      (TruncatedThroatSpatialMultiindexJet Real order) where
  toFun jet index := (jet index).1.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def programPT06ScalarGhostFirstSecondProjection (order : Nat) :
    LinearMap (RingHom.id Real)
      (ProgramPT06PairedAbelianScalarGhostSpatialJet4D order)
      (TruncatedThroatSpatialMultiindexJet Real order) where
  toFun jet index := (jet index).1.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def programPT06ScalarGhostSecondFirstProjection (order : Nat) :
    LinearMap (RingHom.id Real)
      (ProgramPT06PairedAbelianScalarGhostSpatialJet4D order)
      (TruncatedThroatSpatialMultiindexJet Real order) where
  toFun jet index := (jet index).2.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def programPT06ScalarGhostSecondSecondProjection (order : Nat) :
    LinearMap (RingHom.id Real)
      (ProgramPT06PairedAbelianScalarGhostSpatialJet4D order)
      (TruncatedThroatSpatialMultiindexJet Real order) where
  toFun jet index := (jet index).2.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The four derived covectors `dc`, with the exact nesting of the four actual
T02 gauge-potential slots. -/
def programPT06PairedAbelianScalarGhostDC (order : Nat) :
    LinearMap (RingHom.id Real)
      (ProgramPT06PairedAbelianScalarGhostSpatialJet4D (order + 1))
      (TruncatedThroatSpatialMultiindexJet GaugeValueFiber order) where
  toFun jet index :=
    ((programPT06ScalarGhostSpatialDC order
        (programPT06ScalarGhostFirstFirstProjection (order + 1) jet) index,
      programPT06ScalarGhostSpatialDC order
        (programPT06ScalarGhostFirstSecondProjection (order + 1) jet) index),
     (programPT06ScalarGhostSpatialDC order
        (programPT06ScalarGhostSecondFirstProjection (order + 1) jet) index,
      programPT06ScalarGhostSpatialDC order
        (programPT06ScalarGhostSecondSecondProjection (order + 1) jet) index))
  map_add' first second := by
    funext index
    apply Prod.ext
    · apply Prod.ext
      · change programPT06ScalarGhostSpatialDC order
            (programPT06ScalarGhostFirstFirstProjection (order + 1)
              (first + second)) index =
          programPT06ScalarGhostSpatialDC order
              (programPT06ScalarGhostFirstFirstProjection (order + 1) first)
              index +
            programPT06ScalarGhostSpatialDC order
              (programPT06ScalarGhostFirstFirstProjection (order + 1) second)
              index
        rw [map_add, map_add]; rfl
      · change programPT06ScalarGhostSpatialDC order
            (programPT06ScalarGhostFirstSecondProjection (order + 1)
              (first + second)) index =
          programPT06ScalarGhostSpatialDC order
              (programPT06ScalarGhostFirstSecondProjection (order + 1) first)
              index +
            programPT06ScalarGhostSpatialDC order
              (programPT06ScalarGhostFirstSecondProjection (order + 1) second)
              index
        rw [map_add, map_add]; rfl
    · apply Prod.ext
      · change programPT06ScalarGhostSpatialDC order
            (programPT06ScalarGhostSecondFirstProjection (order + 1)
              (first + second)) index =
          programPT06ScalarGhostSpatialDC order
              (programPT06ScalarGhostSecondFirstProjection (order + 1) first)
              index +
            programPT06ScalarGhostSpatialDC order
              (programPT06ScalarGhostSecondFirstProjection (order + 1) second)
              index
        rw [map_add, map_add]; rfl
      · change programPT06ScalarGhostSpatialDC order
            (programPT06ScalarGhostSecondSecondProjection (order + 1)
              (first + second)) index =
          programPT06ScalarGhostSpatialDC order
              (programPT06ScalarGhostSecondSecondProjection (order + 1) first)
              index +
            programPT06ScalarGhostSpatialDC order
              (programPT06ScalarGhostSecondSecondProjection (order + 1) second)
              index
        rw [map_add, map_add]; rfl
  map_smul' scalar jet := by
    funext index
    apply Prod.ext
    · apply Prod.ext
      · change programPT06ScalarGhostSpatialDC order
            (programPT06ScalarGhostFirstFirstProjection (order + 1)
              (scalar • jet)) index =
          scalar •
            (programPT06ScalarGhostSpatialDC order
              (programPT06ScalarGhostFirstFirstProjection (order + 1) jet)
              index)
        change programPT06ScalarGhostSpatialDC order
            (scalar •
              programPT06ScalarGhostFirstFirstProjection (order + 1) jet) index = _
        exact congrFun (map_smul (programPT06ScalarGhostSpatialDC order)
          scalar (programPT06ScalarGhostFirstFirstProjection (order + 1) jet)) index
      · change programPT06ScalarGhostSpatialDC order
            (programPT06ScalarGhostFirstSecondProjection (order + 1)
              (scalar • jet)) index =
          scalar •
            (programPT06ScalarGhostSpatialDC order
              (programPT06ScalarGhostFirstSecondProjection (order + 1) jet)
              index)
        change programPT06ScalarGhostSpatialDC order
            (scalar •
              programPT06ScalarGhostFirstSecondProjection (order + 1) jet) index = _
        exact congrFun (map_smul (programPT06ScalarGhostSpatialDC order)
          scalar (programPT06ScalarGhostFirstSecondProjection (order + 1) jet)) index
    · apply Prod.ext
      · change programPT06ScalarGhostSpatialDC order
            (programPT06ScalarGhostSecondFirstProjection (order + 1)
              (scalar • jet)) index =
          scalar •
            (programPT06ScalarGhostSpatialDC order
              (programPT06ScalarGhostSecondFirstProjection (order + 1) jet)
              index)
        change programPT06ScalarGhostSpatialDC order
            (scalar •
              programPT06ScalarGhostSecondFirstProjection (order + 1) jet) index = _
        exact congrFun (map_smul (programPT06ScalarGhostSpatialDC order)
          scalar (programPT06ScalarGhostSecondFirstProjection (order + 1) jet)) index
      · change programPT06ScalarGhostSpatialDC order
            (programPT06ScalarGhostSecondSecondProjection (order + 1)
              (scalar • jet)) index =
          scalar •
            (programPT06ScalarGhostSpatialDC order
              (programPT06ScalarGhostSecondSecondProjection (order + 1) jet)
              index)
        change programPT06ScalarGhostSpatialDC order
            (scalar •
              programPT06ScalarGhostSecondSecondProjection (order + 1) jet) index = _
        exact congrFun (map_smul (programPT06ScalarGhostSpatialDC order)
          scalar (programPT06ScalarGhostSecondSecondProjection (order + 1) jet)) index

@[simp] theorem programPT06PairedAbelianScalarGhostDC_first_first_basis
    (order : Nat)
    (jet : ProgramPT06PairedAbelianScalarGhostSpatialJet4D (order + 1))
    (index : ThroatSpatialTruncatedIndex order)
    (direction : Fin 3) :
    (programPT06PairedAbelianScalarGhostDC order jet index).1.1
        (programPT06ThroatSpatialBasis direction) =
      (throatSpatialTotalDerivative direction jet index).1.1 := by
  exact programPT06ScalarGhostSpatialDC_apply_basis order
    (programPT06ScalarGhostFirstFirstProjection (order + 1) jet)
    index direction

@[simp] theorem programPT06PairedAbelianScalarGhostDC_first_second_basis
    (order : Nat)
    (jet : ProgramPT06PairedAbelianScalarGhostSpatialJet4D (order + 1))
    (index : ThroatSpatialTruncatedIndex order)
    (direction : Fin 3) :
    (programPT06PairedAbelianScalarGhostDC order jet index).1.2
        (programPT06ThroatSpatialBasis direction) =
      (throatSpatialTotalDerivative direction jet index).1.2 := by
  exact programPT06ScalarGhostSpatialDC_apply_basis order
    (programPT06ScalarGhostFirstSecondProjection (order + 1) jet)
    index direction

@[simp] theorem programPT06PairedAbelianScalarGhostDC_second_first_basis
    (order : Nat)
    (jet : ProgramPT06PairedAbelianScalarGhostSpatialJet4D (order + 1))
    (index : ThroatSpatialTruncatedIndex order)
    (direction : Fin 3) :
    (programPT06PairedAbelianScalarGhostDC order jet index).2.1
        (programPT06ThroatSpatialBasis direction) =
      (throatSpatialTotalDerivative direction jet index).2.1 := by
  exact programPT06ScalarGhostSpatialDC_apply_basis order
    (programPT06ScalarGhostSecondFirstProjection (order + 1) jet)
    index direction

@[simp] theorem programPT06PairedAbelianScalarGhostDC_second_second_basis
    (order : Nat)
    (jet : ProgramPT06PairedAbelianScalarGhostSpatialJet4D (order + 1))
    (index : ThroatSpatialTruncatedIndex order)
    (direction : Fin 3) :
    (programPT06PairedAbelianScalarGhostDC order jet index).2.2
        (programPT06ThroatSpatialBasis direction) =
      (throatSpatialTotalDerivative direction jet index).2.2 := by
  exact programPT06ScalarGhostSpatialDC_apply_basis order
    (programPT06ScalarGhostSecondSecondProjection (order + 1) jet)
    index direction

/-- The paired scalar-ghost differential commutes with the one-order-shifted
truncation maps. -/
theorem programPT06PairedAbelianScalarGhostDC_commutes_truncation
    {lower higher : Nat} (hOrder : lower <= higher)
    (jet : ProgramPT06PairedAbelianScalarGhostSpatialJet4D (higher + 1)) :
    truncateThroatSpatialMultiindexJet hOrder
        (programPT06PairedAbelianScalarGhostDC higher jet) =
      programPT06PairedAbelianScalarGhostDC lower
        (truncateThroatSpatialMultiindexJet
          (Nat.add_le_add_right hOrder 1) jet) := by
  funext index
  apply Prod.ext
  · apply Prod.ext
    · change truncateThroatSpatialMultiindexJet hOrder
          (programPT06ScalarGhostSpatialDC higher
            (programPT06ScalarGhostFirstFirstProjection (higher + 1) jet)) index =
        programPT06ScalarGhostSpatialDC lower
          (truncateThroatSpatialMultiindexJet
            (Nat.add_le_add_right hOrder 1)
            (programPT06ScalarGhostFirstFirstProjection (higher + 1) jet)) index
      exact congrFun
        (programPT06ScalarGhostSpatialDC_commutes_truncation hOrder
          (programPT06ScalarGhostFirstFirstProjection (higher + 1) jet)) index
    · change truncateThroatSpatialMultiindexJet hOrder
          (programPT06ScalarGhostSpatialDC higher
            (programPT06ScalarGhostFirstSecondProjection (higher + 1) jet)) index =
        programPT06ScalarGhostSpatialDC lower
          (truncateThroatSpatialMultiindexJet
            (Nat.add_le_add_right hOrder 1)
            (programPT06ScalarGhostFirstSecondProjection (higher + 1) jet)) index
      exact congrFun
        (programPT06ScalarGhostSpatialDC_commutes_truncation hOrder
          (programPT06ScalarGhostFirstSecondProjection (higher + 1) jet)) index
  · apply Prod.ext
    · change truncateThroatSpatialMultiindexJet hOrder
          (programPT06ScalarGhostSpatialDC higher
            (programPT06ScalarGhostSecondFirstProjection (higher + 1) jet)) index =
        programPT06ScalarGhostSpatialDC lower
          (truncateThroatSpatialMultiindexJet
            (Nat.add_le_add_right hOrder 1)
            (programPT06ScalarGhostSecondFirstProjection (higher + 1) jet)) index
      exact congrFun
        (programPT06ScalarGhostSpatialDC_commutes_truncation hOrder
          (programPT06ScalarGhostSecondFirstProjection (higher + 1) jet)) index
    · change truncateThroatSpatialMultiindexJet hOrder
          (programPT06ScalarGhostSpatialDC higher
            (programPT06ScalarGhostSecondSecondProjection (higher + 1) jet)) index =
        programPT06ScalarGhostSpatialDC lower
          (truncateThroatSpatialMultiindexJet
            (Nat.add_le_add_right hOrder 1)
            (programPT06ScalarGhostSecondSecondProjection (higher + 1) jet)) index
      exact congrFun
        (programPT06ScalarGhostSpatialDC_commutes_truncation hOrder
          (programPT06ScalarGhostSecondSecondProjection (higher + 1) jet)) index

/-- The paired scalar-ghost differential commutes with every formal spatial
total derivative at the shifted jet orders. -/
theorem programPT06PairedAbelianScalarGhostDC_commutes_totalDerivative
    {order : Nat} (direction : Fin 3)
    (jet : ProgramPT06PairedAbelianScalarGhostSpatialJet4D
      ((order + 1) + 1)) :
    throatSpatialTotalDerivative direction
        (programPT06PairedAbelianScalarGhostDC (order + 1) jet) =
      programPT06PairedAbelianScalarGhostDC order
        (throatSpatialTotalDerivative direction jet) := by
  funext index
  apply Prod.ext
  · apply Prod.ext
    · change throatSpatialTotalDerivative direction
          (programPT06ScalarGhostSpatialDC (order + 1)
            (programPT06ScalarGhostFirstFirstProjection
              ((order + 1) + 1) jet)) index =
        programPT06ScalarGhostSpatialDC order
          (throatSpatialTotalDerivative direction
            (programPT06ScalarGhostFirstFirstProjection
              ((order + 1) + 1) jet)) index
      exact congrFun
        (programPT06ScalarGhostSpatialDC_commutes_totalDerivative direction
          (programPT06ScalarGhostFirstFirstProjection
            ((order + 1) + 1) jet)) index
    · change throatSpatialTotalDerivative direction
          (programPT06ScalarGhostSpatialDC (order + 1)
            (programPT06ScalarGhostFirstSecondProjection
              ((order + 1) + 1) jet)) index =
        programPT06ScalarGhostSpatialDC order
          (throatSpatialTotalDerivative direction
            (programPT06ScalarGhostFirstSecondProjection
              ((order + 1) + 1) jet)) index
      exact congrFun
        (programPT06ScalarGhostSpatialDC_commutes_totalDerivative direction
          (programPT06ScalarGhostFirstSecondProjection
            ((order + 1) + 1) jet)) index
  · apply Prod.ext
    · change throatSpatialTotalDerivative direction
          (programPT06ScalarGhostSpatialDC (order + 1)
            (programPT06ScalarGhostSecondFirstProjection
              ((order + 1) + 1) jet)) index =
        programPT06ScalarGhostSpatialDC order
          (throatSpatialTotalDerivative direction
            (programPT06ScalarGhostSecondFirstProjection
              ((order + 1) + 1) jet)) index
      exact congrFun
        (programPT06ScalarGhostSpatialDC_commutes_totalDerivative direction
          (programPT06ScalarGhostSecondFirstProjection
            ((order + 1) + 1) jet)) index
    · change throatSpatialTotalDerivative direction
          (programPT06ScalarGhostSpatialDC (order + 1)
            (programPT06ScalarGhostSecondSecondProjection
              ((order + 1) + 1) jet)) index =
        programPT06ScalarGhostSpatialDC order
          (throatSpatialTotalDerivative direction
            (programPT06ScalarGhostSecondSecondProjection
              ((order + 1) + 1) jet)) index
      exact congrFun
        (programPT06ScalarGhostSpatialDC_commutes_totalDerivative direction
          (programPT06ScalarGhostSecondSecondProjection
            ((order + 1) + 1) jet)) index

/-- At level `order`, physical and metric-BV jets have order `order`, while
the scalar ghosts have the necessary order `order + 1`. -/
abbrev ProgramPT06FullPhysicalScalarGhostJetState4D (order : Nat) :=
  Prod
    (TruncatedThroatSpatialMultiindexJet PhysicalValueFiber order)
    (Prod
      (ProgramPT06PairedAbelianScalarGhostSpatialJet4D (order + 1))
      (ProgramPT06FiniteMetricBVSpatialJet order))

private def programPT06ScalarGhostStatePhysicalProjection (order : Nat) :
    LinearMap (RingHom.id Real)
      (ProgramPT06FullPhysicalScalarGhostJetState4D order)
      (TruncatedThroatSpatialMultiindexJet PhysicalValueFiber order) where
  toFun state := state.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def programPT06ScalarGhostStateGhostProjection (order : Nat) :
    LinearMap (RingHom.id Real)
      (ProgramPT06FullPhysicalScalarGhostJetState4D order)
      (ProgramPT06PairedAbelianScalarGhostSpatialJet4D (order + 1)) where
  toFun state := state.2.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def programPT06ScalarGhostStateBVProjection (order : Nat) :
    LinearMap (RingHom.id Real)
      (ProgramPT06FullPhysicalScalarGhostJetState4D order)
      (ProgramPT06FiniteMetricBVSpatialJet order) where
  toFun state := state.2.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Coefficientwise inclusion of the four derived covectors into the actual
four gauge slots of the eleven-component physical carrier. -/
def programPT06GaugeValueJetPhysicalInclusion (order : Nat) :
    LinearMap (RingHom.id Real)
      (TruncatedThroatSpatialMultiindexJet GaugeValueFiber order)
      (TruncatedThroatSpatialMultiindexJet PhysicalValueFiber order) :=
  LinearMap.pi fun index =>
    programPT06FullPhysicalGaugeValueInclusion.toLinearMap.comp
      (LinearMap.proj index)

/-- Physical gauge variation obtained from the scalar ghost jets by `dc`. -/
def programPT06ScalarGhostPhysicalGaugeVariation (order : Nat) :
    LinearMap (RingHom.id Real)
      (ProgramPT06PairedAbelianScalarGhostSpatialJet4D (order + 1))
      (TruncatedThroatSpatialMultiindexJet PhysicalValueFiber order) :=
  (programPT06GaugeValueJetPhysicalInclusion order).comp
    (programPT06PairedAbelianScalarGhostDC order)

@[simp] theorem programPT06ScalarGhostPhysicalGaugeVariation_apply
    (order : Nat)
    (ghost : ProgramPT06PairedAbelianScalarGhostSpatialJet4D (order + 1))
    (index : ThroatSpatialTruncatedIndex order) :
    programPT06ScalarGhostPhysicalGaugeVariation order ghost index =
      programPT06FullPhysicalGaugeValueInclusion
        (programPT06PairedAbelianScalarGhostDC order ghost index) :=
  rfl

/-- Linear BRST/BV differential on the shifted scalar-ghost jet state. -/
def programPT06FullPhysicalScalarGhostJetBRST (order : Nat) :
    LinearMap (RingHom.id Real)
      (ProgramPT06FullPhysicalScalarGhostJetState4D order)
      (ProgramPT06FullPhysicalScalarGhostJetState4D order) :=
  ((programPT06ScalarGhostPhysicalGaugeVariation order).comp
      (programPT06ScalarGhostStateGhostProjection order)).prod
    ((0 : LinearMap (RingHom.id Real)
        (ProgramPT06FullPhysicalScalarGhostJetState4D order)
        (ProgramPT06PairedAbelianScalarGhostSpatialJet4D (order + 1))).prod
      ((programPT06FiniteMetricBVJetBRST order).comp
        (programPT06ScalarGhostStateBVProjection order)))

@[simp] theorem programPT06FullPhysicalScalarGhostJetBRST_apply
    (order : Nat)
    (state : ProgramPT06FullPhysicalScalarGhostJetState4D order) :
    programPT06FullPhysicalScalarGhostJetBRST order state =
      (programPT06ScalarGhostPhysicalGaugeVariation order state.2.1,
        (0, programPT06FiniteMetricBVJetBRST order state.2.2)) :=
  rfl

/-- The scalar ghosts are killed, so the derived physical gauge variation
cannot contribute to a second BRST application. -/
theorem programPT06FullPhysicalScalarGhostJetBRST_square_zero
    (order : Nat)
    (state : ProgramPT06FullPhysicalScalarGhostJetState4D order) :
    programPT06FullPhysicalScalarGhostJetBRST order
        (programPT06FullPhysicalScalarGhostJetBRST order state) = 0 := by
  change
    (programPT06ScalarGhostPhysicalGaugeVariation order 0,
      (0, programPT06FiniteMetricBVJetBRST order
        (programPT06FiniteMetricBVJetBRST order state.2.2))) = 0
  apply Prod.ext
  · exact map_zero (programPT06ScalarGhostPhysicalGaugeVariation order)
  · apply Prod.ext
    · rfl
    · exact programPT06FiniteMetricBVJetBRST_square_zero order state.2.2

/-- A scalar ghost is detected whenever its derived four-covector jet is
nonzero. -/
theorem programPT06FullPhysicalScalarGhostJetBRST_nonzero_on_dc
    (order : Nat)
    (ghost : ProgramPT06PairedAbelianScalarGhostSpatialJet4D (order + 1))
    (hDC : Not (programPT06PairedAbelianScalarGhostDC order ghost = 0)) :
    Not (programPT06FullPhysicalScalarGhostJetBRST order
      (0, (ghost, 0)) = 0) := by
  intro hZero
  apply hDC
  funext index
  have hPhysical := congrArg
    (fun state : ProgramPT06FullPhysicalScalarGhostJetState4D order =>
      state.1 index) hZero
  have hGauge := congrArg programPT06FullPhysicalGaugeValueProjection hPhysical
  simpa using hGauge

/-- Truncation of shifted scalar-ghost states. -/
def truncateProgramPT06FullPhysicalScalarGhostJetState
    {lower higher : Nat} (hOrder : lower <= higher) :
    LinearMap (RingHom.id Real)
      (ProgramPT06FullPhysicalScalarGhostJetState4D higher)
      (ProgramPT06FullPhysicalScalarGhostJetState4D lower) :=
  ((truncateThroatSpatialMultiindexJetLinear hOrder).comp
      (programPT06ScalarGhostStatePhysicalProjection higher)).prod
    (((truncateThroatSpatialMultiindexJetLinear
        (Nat.add_le_add_right hOrder 1)).comp
      (programPT06ScalarGhostStateGhostProjection higher)).prod
    ((truncateThroatSpatialMultiindexJetLinear hOrder).comp
      (programPT06ScalarGhostStateBVProjection higher)))

/-- Formal total derivative of shifted scalar-ghost states. -/
def programPT06FullPhysicalScalarGhostStateTotalDerivative
    {order : Nat} (direction : Fin 3) :
    LinearMap (RingHom.id Real)
      (ProgramPT06FullPhysicalScalarGhostJetState4D (order + 1))
      (ProgramPT06FullPhysicalScalarGhostJetState4D order) :=
  ((throatSpatialTotalDerivativeLinear direction).comp
      (programPT06ScalarGhostStatePhysicalProjection (order + 1))).prod
    (((throatSpatialTotalDerivativeLinear direction).comp
      (programPT06ScalarGhostStateGhostProjection (order + 1))).prod
    ((throatSpatialTotalDerivativeLinear direction).comp
      (programPT06ScalarGhostStateBVProjection (order + 1))))

/-- The full scalar-ghost BRST differential commutes with shifted
truncation. -/
theorem programPT06FullPhysicalScalarGhostJetBRST_commutes_truncation
    {lower higher : Nat} (hOrder : lower <= higher)
    (state : ProgramPT06FullPhysicalScalarGhostJetState4D higher) :
    truncateProgramPT06FullPhysicalScalarGhostJetState hOrder
        (programPT06FullPhysicalScalarGhostJetBRST higher state) =
      programPT06FullPhysicalScalarGhostJetBRST lower
        (truncateProgramPT06FullPhysicalScalarGhostJetState hOrder state) := by
  apply Prod.ext
  · funext index
    exact congrArg programPT06FullPhysicalGaugeValueInclusion
      (congrFun
        (programPT06PairedAbelianScalarGhostDC_commutes_truncation
          hOrder state.2.1) index)
  · apply Prod.ext
    · rfl
    · exact programPT06FiniteMetricBVJetBRST_commutes_truncation
        hOrder state.2.2

/-- The full scalar-ghost BRST differential commutes with formal total
derivatives at the shifted physical/ghost jet orders. -/
theorem programPT06FullPhysicalScalarGhostJetBRST_commutes_totalDerivative
    {order : Nat} (direction : Fin 3)
    (state : ProgramPT06FullPhysicalScalarGhostJetState4D (order + 1)) :
    programPT06FullPhysicalScalarGhostStateTotalDerivative direction
        (programPT06FullPhysicalScalarGhostJetBRST (order + 1) state) =
      programPT06FullPhysicalScalarGhostJetBRST order
        (programPT06FullPhysicalScalarGhostStateTotalDerivative direction
          state) := by
  apply Prod.ext
  · funext index
    exact congrArg programPT06FullPhysicalGaugeValueInclusion
      (congrFun
        (programPT06PairedAbelianScalarGhostDC_commutes_totalDerivative
          direction state.2.1) index)
  · apply Prod.ext
    · rfl
    · exact programPT06FiniteMetricBVJetBRST_commutes_totalDerivative
        direction state.2.2

/-- Realize a shifted scalar-ghost state in Gate900 by filling its independent
gradient slot with the derived covector jet `dc`. -/
def programPT06FullPhysicalScalarGhostGate900Realization (order : Nat) :
    LinearMap (RingHom.id Real)
      (ProgramPT06FullPhysicalScalarGhostJetState4D order)
      (ProgramPT06FullPhysicalGaugeGradientSpatialJet4D order) :=
  LinearMap.pi fun index =>
    ((LinearMap.proj index).comp
      (programPT06ScalarGhostStatePhysicalProjection order)).prod
    (((LinearMap.proj index).comp
      ((programPT06PairedAbelianScalarGhostDC order).comp
        (programPT06ScalarGhostStateGhostProjection order))).prod
    ((LinearMap.proj index).comp
      (programPT06ScalarGhostStateBVProjection order)))

@[simp] theorem programPT06FullPhysicalScalarGhostGate900Realization_apply
    (order : Nat)
    (state : ProgramPT06FullPhysicalScalarGhostJetState4D order)
    (index : ThroatSpatialTruncatedIndex order) :
    programPT06FullPhysicalScalarGhostGate900Realization order state index =
      (state.1 index,
        (programPT06PairedAbelianScalarGhostDC order state.2.1 index,
          state.2.2 index)) :=
  rfl

/-- Realization in Gate900 intertwines the scalar-ghost-derived differential
with Gate900's gauge-gradient differential. -/
theorem programPT06FullPhysicalScalarGhostGate900Realization_chainMap
    (order : Nat)
    (state : ProgramPT06FullPhysicalScalarGhostJetState4D order) :
    programPT06FullPhysicalGaugeGradientJetBRST order
        (programPT06FullPhysicalScalarGhostGate900Realization order state) =
      programPT06FullPhysicalScalarGhostGate900Realization order
        (programPT06FullPhysicalScalarGhostJetBRST order state) := by
  funext index
  change
    (programPT06FullPhysicalGaugeValueInclusion
        (programPT06PairedAbelianScalarGhostDC order state.2.1 index),
      (0, finiteMetricBVBRST (state.2.2 index))) =
    (programPT06ScalarGhostPhysicalGaugeVariation order state.2.1 index,
      (programPT06PairedAbelianScalarGhostDC order 0 index,
        programPT06FiniteMetricBVJetBRST order state.2.2 index))
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · exact (congrFun
        (map_zero (programPT06PairedAbelianScalarGhostDC order)) index).symm
    · rfl

end
end P0EFTJanusProgramPT06FullPhysicalScalarGhostBRSTJetComplex4D
end JanusFormal
