/-!
Minimal Lean 4 skeleton for Janus formalization.
Only a tiny logical vocabulary, enough for proof automation on the Janus sector model.
-/

inductive Sector where
  | positive
  | negative
  deriving DecidableEq, Repr

def sameSector (a b : Sector) : Prop := a = b

def oppositeSector (a b : Sector) : Prop := a != b

inductive MetricSheet where
  | gPlus
  | gMinus
  deriving DecidableEq, Repr

def metricSheetFor (s : Sector) : MetricSheet :=
  match s with
  | Sector.positive => MetricSheet.gPlus
  | Sector.negative => MetricSheet.gMinus

def densitySign (s : Sector) : Int :=
  match s with
  | Sector.positive => 1
  | Sector.negative => -1

def metricEquationSign (s : Sector) : Int :=
  match s with
  | Sector.positive => 1
  | Sector.negative => -1

def newtonianCouplingSign (source test : Sector) : Int :=
  densitySign source * metricEquationSign test

def effectivePoissonDensity (rhoPlusAbs rhoMinusAbs : Int) (test : Sector) : Int :=
  newtonianCouplingSign Sector.positive test * rhoPlusAbs +
    newtonianCouplingSign Sector.negative test * rhoMinusAbs

inductive NewtonianInteraction where
  | attract
  | repel
  deriving DecidableEq, Repr

def janusNewtonianInteraction (a b : Sector) : NewtonianInteraction :=
  if newtonianCouplingSign a b = 1 then NewtonianInteraction.attract else NewtonianInteraction.repel

theorem same_sector_attracts (s : Sector) :
    janusNewtonianInteraction s s = NewtonianInteraction.attract := by
  cases s <;> simp [janusNewtonianInteraction, newtonianCouplingSign, densitySign, metricEquationSign]

theorem positive_uses_g_plus :
    metricSheetFor Sector.positive = MetricSheet.gPlus := by
  simp [metricSheetFor]

theorem negative_uses_g_minus :
    metricSheetFor Sector.negative = MetricSheet.gMinus := by
  simp [metricSheetFor]

theorem positive_positive_coupling :
    newtonianCouplingSign Sector.positive Sector.positive = 1 := by
  decide

theorem negative_negative_coupling :
    newtonianCouplingSign Sector.negative Sector.negative = 1 := by
  decide

theorem positive_negative_coupling :
    newtonianCouplingSign Sector.positive Sector.negative = -1 := by
  simp [newtonianCouplingSign, densitySign, metricEquationSign]

theorem negative_positive_coupling :
    newtonianCouplingSign Sector.negative Sector.positive = -1 := by
  simp [newtonianCouplingSign, densitySign, metricEquationSign]

theorem positive_metric_poisson_density (rhoPlusAbs rhoMinusAbs : Int) :
    effectivePoissonDensity rhoPlusAbs rhoMinusAbs Sector.positive =
      rhoPlusAbs + -rhoMinusAbs := by
  simp [effectivePoissonDensity, newtonianCouplingSign, densitySign, metricEquationSign]

theorem negative_metric_poisson_density (rhoPlusAbs rhoMinusAbs : Int) :
    effectivePoissonDensity rhoPlusAbs rhoMinusAbs Sector.negative =
      -rhoPlusAbs + rhoMinusAbs := by
  simp [effectivePoissonDensity, newtonianCouplingSign, densitySign, metricEquationSign]

theorem opposite_sector_repels :
    janusNewtonianInteraction Sector.positive Sector.negative = NewtonianInteraction.repel := by
  simp [janusNewtonianInteraction, newtonianCouplingSign, densitySign, metricEquationSign]

theorem opposite_sector_repels_commuted :
    janusNewtonianInteraction Sector.negative Sector.positive = NewtonianInteraction.repel := by
  simp [janusNewtonianInteraction, newtonianCouplingSign, densitySign, metricEquationSign]

theorem coupling_sign_table (a b : Sector) :
    newtonianCouplingSign a b = (if a = b then 1 else -1) := by
  cases a <;> cases b <;> simp [newtonianCouplingSign, densitySign, metricEquationSign]

theorem coupling_sign_comm (a b : Sector) :
    newtonianCouplingSign a b = newtonianCouplingSign b a := by
  cases a <;> cases b <;> simp [newtonianCouplingSign, densitySign, metricEquationSign]

theorem newtonianInteraction_comm (a b : Sector) :
    janusNewtonianInteraction a b = janusNewtonianInteraction b a := by
  cases a <;> cases b <;>
    simp [janusNewtonianInteraction, newtonianCouplingSign, densitySign, metricEquationSign]

theorem coupling_sign_of_sameSector {a b : Sector} (h : sameSector a b) :
    newtonianCouplingSign a b = 1 := by
  rcases h with rfl
  cases a <;> simp [newtonianCouplingSign, densitySign, metricEquationSign]

theorem coupling_sign_of_oppositeSector {a b : Sector} (h : oppositeSector a b) :
    newtonianCouplingSign a b = -1 := by
  have htab := coupling_sign_table a b
  by_cases hab : a = b
  · have hne : a ≠ b := by
      simpa [oppositeSector] using h
    exact False.elim (hne hab)
  · simpa [hab] using htab

theorem interaction_of_sameSector {a b : Sector} (h : sameSector a b) :
    janusNewtonianInteraction a b = NewtonianInteraction.attract := by
  have hs : newtonianCouplingSign a b = 1 := coupling_sign_of_sameSector h
  simp [janusNewtonianInteraction, hs]

theorem interaction_of_oppositeSector {a b : Sector} (h : oppositeSector a b) :
    janusNewtonianInteraction a b = NewtonianInteraction.repel := by
  have hs : newtonianCouplingSign a b = -1 := coupling_sign_of_oppositeSector h
  simp [janusNewtonianInteraction, hs]

theorem interaction_eq_iff_same_sector (a b : Sector) :
    Iff (janusNewtonianInteraction a b = NewtonianInteraction.attract) (a = b) := by
  constructor
  · intro h
    by_cases hab : a = b
    · exact hab
    · have hs : newtonianCouplingSign a b = -1 := by
        simpa [hab] using (coupling_sign_table a b)
      have hRep : janusNewtonianInteraction a b = NewtonianInteraction.repel := by
        simp [janusNewtonianInteraction, hs]
      exact False.elim (by simpa [hRep] using h)
  · intro h
    cases h
    exact same_sector_attracts a

theorem interaction_eq_iff_opposite_sector (a b : Sector) :
    Iff (janusNewtonianInteraction a b = NewtonianInteraction.repel) (Not (a = b)) := by
  constructor
  · intro h
    by_cases hab : a = b
    · have hs : newtonianCouplingSign a b = 1 := by
        simpa [hab] using (coupling_sign_table a b)
      have hAt : janusNewtonianInteraction a b = NewtonianInteraction.attract := by
        simp [janusNewtonianInteraction, hs]
      exact False.elim (by simpa [hAt] using h)
    · exact by
        simpa [oppositeSector] using hab
  · intro h
    exact interaction_of_oppositeSector (by simpa [oppositeSector] using h)

theorem effectivePoissonDensity_cases (rhoPlusAbs rhoMinusAbs : Int) (test : Sector) :
    effectivePoissonDensity rhoPlusAbs rhoMinusAbs test =
      (if test = Sector.positive then rhoPlusAbs + -rhoMinusAbs else -rhoPlusAbs + rhoMinusAbs) := by
  cases test <;> simp [effectivePoissonDensity, newtonianCouplingSign, densitySign, metricEquationSign]

theorem sameSector_refl (s : Sector) : sameSector s s := by
  rfl

theorem sameSector_of_eq {a b : Sector} (h : a = b) : sameSector a b := by
  simpa [sameSector] using h

theorem metricSheetFor_same {a b : Sector} (h : sameSector a b) : metricSheetFor a = metricSheetFor b := by
  simpa [sameSector] using congrArg metricSheetFor h

theorem metricSheetFor_iff_sameSector (a b : Sector) :
    Iff (metricSheetFor a = metricSheetFor b) (sameSector a b) := by
  constructor
  · intro h
    cases a <;> cases b <;>
      (first | rfl | simp [metricSheetFor] at h <;> contradiction)
  · intro h
    simpa [sameSector] using congrArg metricSheetFor h

theorem metricSheetFor_ne_opposite {a b : Sector} (h : oppositeSector a b) :
    Not (metricSheetFor a = metricSheetFor b) := by
  intro hms
  have hne : ¬ a = b := by
    simpa [oppositeSector] using h
  have hEq : sameSector a b := (metricSheetFor_iff_sameSector a b).1 hms
  exact hne (by simpa [sameSector] using hEq)

theorem metricSheetFor_iff_oppositeSector (a b : Sector) :
    Iff (Not (metricSheetFor a = metricSheetFor b)) (oppositeSector a b) := by
  constructor
  · intro h
    have hNotEq : ¬ sameSector a b := (not_congr (metricSheetFor_iff_sameSector a b)).1 h
    have hNotEq' : ¬ a = b := by
      simpa [sameSector] using hNotEq
    exact by
      simpa [oppositeSector] using hNotEq'
  · intro h
    have hNotEq' : ¬ a = b := by
      simpa [oppositeSector] using h
    have hNotEq : ¬ sameSector a b := by
      simpa [sameSector] using hNotEq'
    exact (not_congr (metricSheetFor_iff_sameSector a b)).2 hNotEq

theorem sameSector_irrefl (s : Sector) : Not (oppositeSector s s) := by
  simp [oppositeSector]

theorem sameSector_and_opposite (a b : Sector) : Not (And (sameSector a b) (oppositeSector a b)) := by
  intro h
  have hne : a ≠ b := by
    simpa [oppositeSector] using h.2
  exact hne (by simpa [sameSector] using h.1)

theorem coupling_sign_cases (a b : Sector) :
    Or (newtonianCouplingSign a b = 1) (newtonianCouplingSign a b = -1) := by
  cases a <;> cases b <;> simp [newtonianCouplingSign, densitySign, metricEquationSign]

theorem interaction_dichotomy (a b : Sector) :
    Or (janusNewtonianInteraction a b = NewtonianInteraction.attract)
      (janusNewtonianInteraction a b = NewtonianInteraction.repel) := by
  exact match decEq a b with
  | isTrue hEq => Or.inl (by cases hEq; exact same_sector_attracts a)
  | isFalse hNe => Or.inr (interaction_of_oppositeSector (by simpa [oppositeSector] using hNe))

theorem interaction_not_attract_implies_opposite (a b : Sector) :
    Not (janusNewtonianInteraction a b = NewtonianInteraction.attract) -> oppositeSector a b := by
  intro h
  exact (interaction_dichotomy a b).elim
    (fun hAt => False.elim (h hAt))
    (fun hRep => by
      exact by
        simpa [oppositeSector] using (interaction_eq_iff_opposite_sector a b).1 hRep)

theorem interaction_not_repel_implies_sameSector (a b : Sector) :
    Not (janusNewtonianInteraction a b = NewtonianInteraction.repel) -> sameSector a b := by
  intro h
  exact (interaction_dichotomy a b).elim
    (fun hAt => (interaction_eq_iff_same_sector a b).1 hAt)
    (fun hRep => False.elim (h hRep))
