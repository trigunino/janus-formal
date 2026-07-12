import Mathlib

namespace JanusFormal
namespace P0EFTJanusSectorQuantumNumbers

set_option autoImplicit false

/-- Local rotation/Spin type of a Janus field sector. -/
inductive RotationType where
  | scalar
  | vector
  | spinTwo
  | spinor
  | conjugateSpinor
  deriving DecidableEq, Repr

/-- Grassmann parity. -/
inductive GrassmannParity where
  | even
  | odd
  deriving DecidableEq, Repr

/-- Complete discrete label used by the fiberwise bilinear selection audit. -/
structure SectorLabel where
  rotationType : RotationType
  z4Phase : ZMod 4
  u1Charge : ℤ
  ghostNumber : ℤ
  grassmannParity : GrassmannParity
  deriving DecidableEq, Repr

/-- Rotation/Spin duality compatibility for a scalar-valued bilinear pairing. -/
def rotationDualCompatible
    (first second : RotationType) : Prop :=
  (first = RotationType.scalar /\ second = RotationType.scalar) \/
  (first = RotationType.vector /\ second = RotationType.vector) \/
  (first = RotationType.spinTwo /\ second = RotationType.spinTwo) \/
  (first = RotationType.spinor /\ second = RotationType.conjugateSpinor) \/
  (first = RotationType.conjugateSpinor /\ second = RotationType.spinor)

instance rotationDualCompatibleDecidable
    (first second : RotationType) :
    Decidable (rotationDualCompatible first second) := by
  unfold rotationDualCompatible
  infer_instance

/-- Necessary fiberwise selection rule for a ghost-number-zero scalar action. -/
def PairingAllowed
    (first second : SectorLabel) : Prop :=
  rotationDualCompatible first.rotationType second.rotationType /\
  first.z4Phase + second.z4Phase = 0 /\
  first.u1Charge + second.u1Charge = 0 /\
  first.ghostNumber + second.ghostNumber = 0 /\
  first.grassmannParity = second.grassmannParity

instance pairingAllowedDecidable
    (first second : SectorLabel) :
    Decidable (PairingAllowed first second) := by
  unfold PairingAllowed
  infer_instance

/-- Normal deformation: scalar under rotations, but sign/half-turn under the normal `Z4`. -/
def normalMode : SectorLabel :=
  { rotationType := RotationType.scalar
    z4Phase := 2
    u1Charge := 0
    ghostNumber := 0
    grassmannParity := GrassmannParity.even }

/-- Trace metric mode. -/
def traceMetricMode : SectorLabel :=
  { rotationType := RotationType.scalar
    z4Phase := 0
    u1Charge := 0
    ghostNumber := 0
    grassmannParity := GrassmannParity.even }

/-- Traceless symmetric metric mode. -/
def tracelessMetricMode : SectorLabel :=
  { rotationType := RotationType.spinTwo
    z4Phase := 0
    u1Charge := 0
    ghostNumber := 0
    grassmannParity := GrassmannParity.even }

/-- Abelian gauge one-form. -/
def gaugeOneFormMode : SectorLabel :=
  { rotationType := RotationType.vector
    z4Phase := 0
    u1Charge := 0
    ghostNumber := 0
    grassmannParity := GrassmannParity.even }

/-- Positive-quarter, positively charged spinor. -/
def positiveQuarterSpinor : SectorLabel :=
  { rotationType := RotationType.spinor
    z4Phase := 1
    u1Charge := 1
    ghostNumber := 0
    grassmannParity := GrassmannParity.odd }

/-- PT/conjugate negative-quarter spinor. -/
def negativeQuarterSpinor : SectorLabel :=
  { rotationType := RotationType.conjugateSpinor
    z4Phase := 3
    u1Charge := -1
    ghostNumber := 0
    grassmannParity := GrassmannParity.odd }

/-- Abelian Faddeev--Popov ghost. -/
def u1Ghost : SectorLabel :=
  { rotationType := RotationType.scalar
    z4Phase := 0
    u1Charge := 0
    ghostNumber := 1
    grassmannParity := GrassmannParity.odd }

/-- Abelian antighost. -/
def u1Antighost : SectorLabel :=
  { rotationType := RotationType.scalar
    z4Phase := 0
    u1Charge := 0
    ghostNumber := -1
    grassmannParity := GrassmannParity.odd }

/-- Diffeomorphism ghost. -/
def diffeomorphismGhost : SectorLabel :=
  { rotationType := RotationType.vector
    z4Phase := 0
    u1Charge := 0
    ghostNumber := 1
    grassmannParity := GrassmannParity.odd }

/-- Diffeomorphism antighost. -/
def diffeomorphismAntighost : SectorLabel :=
  { rotationType := RotationType.vector
    z4Phase := 0
    u1Charge := 0
    ghostNumber := -1
    grassmannParity := GrassmannParity.odd }

/-- The normal mode has a permitted self-pairing because `2+2=0 mod 4`. -/
@[simp] theorem normal_self_pairing_allowed :
    PairingAllowed normalMode normalMode := by
  native_decide

/-- The trace metric mode has its ordinary scalar pairing. -/
@[simp] theorem trace_self_pairing_allowed :
    PairingAllowed traceMetricMode traceMetricMode := by
  native_decide

/-- The spin-two sector has a permitted self-pairing. -/
@[simp] theorem traceless_self_pairing_allowed :
    PairingAllowed tracelessMetricMode tracelessMetricMode := by
  native_decide

/-- The vector gauge sector has a permitted self-pairing. -/
@[simp] theorem gauge_self_pairing_allowed :
    PairingAllowed gaugeOneFormMode gaugeOneFormMode := by
  native_decide

/-- The normal and trace scalars are distinguished by the normal `Z4` character. -/
@[simp] theorem normal_trace_pairing_forbidden :
    Not (PairingAllowed normalMode traceMetricMode) := by
  native_decide

/-- Trace and traceless tensor modes cannot mix by rotation type. -/
@[simp] theorem trace_traceless_pairing_forbidden :
    Not (PairingAllowed traceMetricMode tracelessMetricMode) := by
  native_decide

/-- Normal scalar and spin-two tensor cannot mix. -/
@[simp] theorem normal_traceless_pairing_forbidden :
    Not (PairingAllowed normalMode tracelessMetricMode) := by
  native_decide

/-- The two PT-conjugate quarter spinors admit the charged Hermitian pairing. -/
@[simp] theorem conjugate_spinor_pairing_allowed :
    PairingAllowed positiveQuarterSpinor negativeQuarterSpinor := by
  native_decide

/-- Two positive-quarter spinors do not give a neutral scalar bilinear. -/
@[simp] theorem positive_spinor_self_pairing_forbidden :
    Not (PairingAllowed positiveQuarterSpinor positiveQuarterSpinor) := by
  native_decide

/-- Two negative-quarter spinors do not give a neutral scalar bilinear. -/
@[simp] theorem negative_spinor_self_pairing_forbidden :
    Not (PairingAllowed negativeQuarterSpinor negativeQuarterSpinor) := by
  native_decide

/-- Ghost and antighost pair at total ghost number zero. -/
@[simp] theorem u1_ghost_antighost_pairing_allowed :
    PairingAllowed u1Ghost u1Antighost := by
  native_decide

/-- Two ghosts cannot appear in a ghost-number-zero quadratic action. -/
@[simp] theorem u1_ghost_self_pairing_forbidden :
    Not (PairingAllowed u1Ghost u1Ghost) := by
  native_decide

/-- Diffeomorphism ghost and antighost pair naturally. -/
@[simp] theorem diffeomorphism_ghost_antighost_pairing_allowed :
    PairingAllowed diffeomorphismGhost diffeomorphismAntighost := by
  native_decide

/-- Bosonic and Grassmann-odd sectors cannot mix in the scalar Hessian. -/
@[simp] theorem gauge_diffeomorphism_ghost_pairing_forbidden :
    Not (PairingAllowed gaugeOneFormMode diffeomorphismGhost) := by
  native_decide

/-- Complete core selection matrix. -/
theorem janus_core_pairing_matrix :
    PairingAllowed normalMode normalMode /\
    PairingAllowed traceMetricMode traceMetricMode /\
    PairingAllowed tracelessMetricMode tracelessMetricMode /\
    PairingAllowed gaugeOneFormMode gaugeOneFormMode /\
    Not (PairingAllowed normalMode traceMetricMode) /\
    PairingAllowed positiveQuarterSpinor negativeQuarterSpinor /\
    Not (PairingAllowed positiveQuarterSpinor positiveQuarterSpinor) /\
    PairingAllowed u1Ghost u1Antighost /\
    PairingAllowed diffeomorphismGhost diffeomorphismAntighost := by
  native_decide

/--
P.E interpretation: the full discrete grading is stronger than PT parity alone.
It removes the formerly free normal--trace mixing because the normal scalar is a
section of the sign-clutched normal line, while the trace metric scalar is
periodic.  The rule is necessary, not sufficient: existence and uniqueness of
an invariant bilinear form inside each allowed block remain representation-
theoretic questions.
-/
structure SectorSelectionPhysicalStatus where
  actualStructureGroupIdentified : Prop
  normalCharacterDerived : Prop
  spinCChargesDerived : Prop
  ghostNumbersDerived : Prop
  ptActionDerived : Prop
  fieldSectorLabelsDerived : Prop
  bilinearSelectionRulesProved : Prop
  noHiddenMultiplicityOrMixingProved : Prop


def sectorSelectionPhysicalClosure
    (s : SectorSelectionPhysicalStatus) : Prop :=
  s.actualStructureGroupIdentified /\
  s.normalCharacterDerived /\
  s.spinCChargesDerived /\
  s.ghostNumbersDerived /\
  s.ptActionDerived /\
  s.fieldSectorLabelsDerived /\
  s.bilinearSelectionRulesProved /\
  s.noHiddenMultiplicityOrMixingProved

end P0EFTJanusSectorQuantumNumbers
end JanusFormal
