# P0 S_path formalization summary (Lean)

## Scope and discipline
- Formalize only logical no-go structure from P0 artifacts.
- Do **not** prove physics of Janus.

## Core setup
- `Coeff : Type := Fin coeffDim → Rat`, with `coeffDim : Nat := 11`.
- `Filter (α : Type) : Type := Set α`.
- `HasUnique α p := ∃! x, p x`.

## Linear coefficient family
- Extracted indices: `c0Index .. c5Index, v1Index .. v5Index`.
- Selectors:
  - `C_J (c : Coeff) := c c0Index`
  - `V_J (c : Coeff) := c v1Index`
- Linear selector: `linearSelector : Coeff → Rat × Rat := fun c => (C_J c, V_J c)`.

### Linear filters (all predicates/subsets)
- `noFitFilter`, `PTFilter`, `sameLFilter`, `stabilityFilter`, `weakFieldSignFilter`.
- `linearFilterOnly := noFitFilter c ∧ PTFilter c ∧ sameLFilter c ∧ stabilityFilter c ∧ weakFieldSignFilter c`.

### Artifact-backed linear payload
- `linearNoGoReport` fields include:
  - `compatibilityMatrixRank := 0`
  - `compatibilityNullity := 11`
  - `filtersSelectUniqueCoefficients := False`
  - `sourceEquationsRequiredForUniqueSelection := 11`

### Linear no-go lemmas
- `linear_zero_equations_rank_nullity : compatibilityRank = 0 ∧ compatibilityNullity = coeffDim`.
- `filter_only_linear_not_unique : ¬ HasUnique Coeff linearFilterOnly`.
- `filter_only_linear_distinct_selectors`:
  - ∃ two solutions satisfying `linearFilterOnly` with different `linearSelector`.

## Nonlinear local family
- `LocalFamily` with fields
  - `cF : IIndex → Rat`
  - `vF : IIndex → Rat`, where `IIndex := Fin 5`.
- `localFilterOnly` from predicates on `LocalFamily` (`PTFilterLocal`, `sameLFilterLocal`, `stabilityFilterLocal`, `weakFieldSignFilterLocal`).

### Nonlinear no-go lemmas
- `local_filter_only_not_unique : ¬ HasUnique LocalFamily localFilterOnly`.
- `local_filter_only_allows_two_distinct_functions`:
  - ∃ `f1 f2`, both in `localFilterOnly`, with `localSelector f1 ≠ localSelector f2`.

## Constraints as classifier objects
- `ConstraintClass := filter | missingEquation`.
- `ConstraintSpec` records (`name`, `constraintClass`, `selectsUnique`).
- Set as filters:
  - `PTClassifier`, `sameLClassifier`, `stabilityClassifier`, `weakFieldSignClassifier`.
- Missing equation:
  - `sourceActionClassifier : ConstraintClass := missingEquation`.

## Bianchi/Noether acceptance gate (status scaffold)
- `bianchiNoetherGate : BianchiNoetherPayload` with `bianchiNoetherGateClosed := False`.
- `bianchi_gate_is_open : ¬ bianchiNoetherGate.bianchiNoetherGateClosed`.

## Final no-go conclusions
- `boundedNoGoConclusion := ¬ HasUnique Coeff linearFilterOnly ∧ ¬ HasUnique LocalFamily localFilterOnly`.
- `filter_only_not_predictive_without_source : ¬ sourceActionEquationProvided → boundedNoGoConclusion`.
- `sourceActionEquationProvided : Prop := False` and `source_action_missing : ¬ sourceActionEquationProvided`.
- `full_no_go_with_reports : boundedNoGoConclusion ∧ ¬ bianchiNoetherGate.bianchiNoetherGateClosed`.

## Validation
- `lake env lean formal/lean/P0SPathNoGo.lean`
- `lake build`

## Interpretation
- In Lean, current scaffolding proves: **filter-only constraints do not determine a unique selector/function**.
- A source/action-like equation is explicitly required to recover uniqueness/prediction power.
- Physical closure is still not reached at this stage of the pipeline (`Bianchi/Noether` gate remains open).