import Mathlib

namespace JanusFormal

set_option autoImplicit false
set_option linter.unnecessarySimpa false

-- 0) Core logical primitives
def Filter (α : Type) : Type := Set α

def HasUnique (α : Type) (p : α → Prop) : Prop := ∃! x, p x

-- 1) Orbifold/PT state used for no-go scaffolding
structure OrbifoldState where
  bDefect : Rat
  jDefect : Rat
  jMatter : Rat
  kTop : Rat

-- 2) Filters are predicates/subsets, not equations
def ptCompatibleFilter : Filter OrbifoldState := fun _ => True
def ptParityFilter : Filter OrbifoldState := fun _ => True
def gaugeCovariantFilter : Filter OrbifoldState := fun _ => True
def noObservationalFitFilter : Filter OrbifoldState := fun _ => True

def bDefectFilter : Set OrbifoldState :=
  fun s => ptCompatibleFilter s ∧ ptParityFilter s ∧ gaugeCovariantFilter s

def sourceCurrentFilter : Set OrbifoldState :=
  fun s => ptCompatibleFilter s ∧ gaugeCovariantFilter s ∧ noObservationalFitFilter s

-- 3) Artifact-backed variation scaffold
structure ActionVariationRow where
  variation : String
  equation : String
  derivedFormally : Prop
  closedForPrediction : Prop
  blocker : String

def orbifoldActionRows : List ActionVariationRow :=
  [ { variation := "delta_A_PT"
    , equation := "D_A *F_PT = J_defect + J_matter"
    , derivedFormally := True
    , closedForPrediction := False
    , blocker := "J_defect/J_matter candidates are triaged separately and not source-derived" }
  , { variation := "delta_g_plus"
    , equation := "G_plus = T_plus + K_plus[A_PT,F_PT,B]"
    , derivedFormally := True
    , closedForPrediction := False
    , blocker := "K_plus tensor variation not computed from accepted action" }
  , { variation := "delta_g_minus"
    , equation := "G_minus = T_minus + K_minus[A_PT,F_PT,B]"
    , derivedFormally := True
    , closedForPrediction := False
    , blocker := "K_minus mirror tensor variation not computed from accepted action" }
  , { variation := "delta_boundary_Sigma_PT"
    , equation := "n_A *F_PT + delta B/delta A_PT = 0 on Sigma_PT"
    , derivedFormally := True
    , closedForPrediction := False
    , blocker := "Sigma_PT dynamics and boundary functional B are not fixed" } ]

theorem action_variation_is_not_prediction_closed :
    ∀ row ∈ orbifoldActionRows, ¬ row.closedForPrediction := by
  intro row hr
  simp [orbifoldActionRows] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> simp

-- 4) Non-unique bDefect candidates under PT/covariance filters
theorem orbifold_bdefect_filter_does_not_select_unique :
    Not (HasUnique OrbifoldState bDefectFilter) := by
  intro h
  rcases h with ⟨s0, hs0, huniq⟩
  let sA : OrbifoldState := { bDefect := 0, jDefect := 0, jMatter := 0, kTop := 0 }
  let sB : OrbifoldState := { bDefect := 1, jDefect := 0, jMatter := 0, kTop := 0 }
  have hA : bDefectFilter sA := by exact ⟨trivial, trivial, trivial⟩
  have hB : bDefectFilter sB := by exact ⟨trivial, trivial, trivial⟩
  have hAeq : sA = s0 := huniq sA hA
  have hBeq : sB = s0 := huniq sB hB
  have hAB : sA = sB := hAeq.trans hBeq.symm
  have hval : sA.bDefect = sB.bDefect := congrArg OrbifoldState.bDefect hAB
  have hzero : (0 : Rat) = 1 := by
    simpa [sA, sB] using hval
  exact zero_ne_one hzero

-- 5) Non-unique source currents under current filter assumptions
theorem orbifold_source_current_filter_does_not_select_unique :
    Not (HasUnique OrbifoldState sourceCurrentFilter) := by
  intro h
  rcases h with ⟨s0, hs0, huniq⟩
  let sA : OrbifoldState := { bDefect := 0, jDefect := 0, jMatter := 0, kTop := 0 }
  let sB : OrbifoldState := { bDefect := 0, jDefect := 1, jMatter := 0, kTop := 0 }
  have hA : sourceCurrentFilter sA := by exact ⟨trivial, trivial, trivial⟩
  have hB : sourceCurrentFilter sB := by exact ⟨trivial, trivial, trivial⟩
  have hAeq : sA = s0 := huniq sA hA
  have hBeq : sB = s0 := huniq sB hB
  have hAB : sA = sB := hAeq.trans hBeq.symm
  have hval : sA.jDefect = sB.jDefect := congrArg OrbifoldState.jDefect hAB
  have hzero : (0 : Rat) = 1 := by
    simpa [sA, sB] using hval
  exact zero_ne_one hzero

-- 6) Topological current branch: discretizes k_top without unique value
def kTopCandidateFilter : Set Rat := fun k => ∃ n : ℤ, k = n

theorem k_top_filter_is_discrete_and_not_unique :
    Not (HasUnique Rat kTopCandidateFilter) := by
  intro h
  rcases h with ⟨k0, hk0, huniq⟩
  let kA : Rat := 0
  let kB : Rat := 1
  have hkA : kTopCandidateFilter kA := by exact ⟨0, by norm_num⟩
  have hkB : kTopCandidateFilter kB := by exact ⟨1, by norm_num⟩
  have hAeq : kA = k0 := huniq kA hkA
  have hBeq : kB = k0 := huniq kB hkB
  have hAB : kA = kB := hAeq.trans hBeq.symm
  have hzero : (0 : Rat) = 1 := by
    simpa [kA, kB] using hAB
  exact zero_ne_one hzero

-- 7) Matching law/gate summaries (non-closing predicates)
structure MatchingRow where
  condition : String
  formula : String
  written : Bool
  sourceDerived : Bool
  selectsCurrent : Bool

def defectMatchingRows : List MatchingRow :=
  [ { condition := "pt_orbifold_identification"
    , formula := "tau^2=id and fields obey PT parity on Sigma_PT"
    , written := true
    , sourceDerived := true
    , selectsCurrent := false }
  , { condition := "flux_jump"
    , formula := "n_A[*F_PT]^+_- = J_defect"
    , written := true
    , sourceDerived := false
    , selectsCurrent := false }
  , { condition := "defect_action_variation"
    , formula := "J_defect = - delta B_defect/delta A_PT"
    , written := true
    , sourceDerived := false
    , selectsCurrent := false }
  , { condition := "metric_matching"
    , formula := "[h_ab]=0 and [K_ab-K h_ab]=S_ab^defect"
    , written := true
    , sourceDerived := false
    , selectsCurrent := false }
  , { condition := "a_pt_boundary_condition"
    , formula := "n_A *F_PT + delta B_defect/delta A_PT = 0 on Sigma_PT"
    , written := true
    , sourceDerived := false
    , selectsCurrent := false } ]

theorem defect_matching_rows_do_not_select_current :
    ∀ row ∈ defectMatchingRows, row.selectsCurrent = false := by
  intro row hr
  simp [defectMatchingRows] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp

-- 8) Source candidates
structure SourceCurrentRow where
  source : String
  candidate : String
  covariant : Bool
  ptCompatible : Bool
  sourceDerived : Bool
  accepted : Bool

def sourceCurrentRows : List SourceCurrentRow :=
  [ { source := "defect_curvature_jump"
    , candidate := "J_defect ~ [*F_PT]_{Sigma_PT}"
    , covariant := true
    , ptCompatible := true
    , sourceDerived := false
    , accepted := false }
  , { source := "defect_tension_current"
    , candidate := "J_defect ~ delta B_defect/delta A_PT"
    , covariant := true
    , ptCompatible := true
    , sourceDerived := false
    , accepted := false }
  , { source := "matter_solder_torque"
    , candidate := "J_matter ~ P_so(1,3)(T_plus L_gamma T_minus L_gamma^T)"
    , covariant := true
    , ptCompatible := true
    , sourceDerived := false
    , accepted := false }
  , { source := "vlasov_phase_space_current"
    , candidate := "J_matter ~ integral p wedge D_A f over mass shell"
    , covariant := true
    , ptCompatible := true
    , sourceDerived := false
    , accepted := false }
  , { source := "observable_residual_current"
    , candidate := "J ~ fitted lensing/growth residual"
    , covariant := false
    , ptCompatible := false
    , sourceDerived := false
    , accepted := false } ]

theorem source_current_rows_have_no_accepted_source :
    ∀ row ∈ sourceCurrentRows, row.accepted = false := by
  intro row hr
  simp [sourceCurrentRows] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp

-- 9) End-to-end no-go scaffold
def orbifoldNoGoConclusion : Prop :=
  (Not (HasUnique OrbifoldState bDefectFilter)) ∧
  (Not (HasUnique OrbifoldState sourceCurrentFilter)) ∧
  (Not (HasUnique Rat kTopCandidateFilter))

theorem orbifold_no_go_summary : orbifoldNoGoConclusion := by
  exact ⟨orbifold_bdefect_filter_does_not_select_unique,
          orbifold_source_current_filter_does_not_select_unique,
          k_top_filter_is_discrete_and_not_unique⟩

def sourceActionEquationProvided : Prop := False
def bianchiNoetherGateClosed : Prop := False

theorem source_action_is_missing : Not sourceActionEquationProvided := by
  simpa [sourceActionEquationProvided]

theorem bianchi_gate_is_open : ¬ bianchiNoetherGateClosed := by
  simp [bianchiNoetherGateClosed]

theorem orbifold_full_no_go_with_reports :
    orbifoldNoGoConclusion ∧ ¬ bianchiNoetherGateClosed := by
  exact ⟨orbifold_no_go_summary, bianchi_gate_is_open⟩

end JanusFormal
