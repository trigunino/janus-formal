# Active Objective: Hard Global Math Closure

Goal: continue the project on the hard-math line only, with zero new phenomenological patching, until:

- APS/Pin theorem is proved without axioms in Lean,
- Orbifold 2:1 theorem is proved without axioms in Lean,
- the unique Janus/Z4/Holst action-to-equations interface is mathematically closed.

## Acceptance conditions

1. **APS/Pin lock**
   - Prove `aps_index_package_closed` in Lean from concrete lemmas (no `by sorry` / axiom placeholders).
   - Report atomic obligations as closed:
     - `pin_minus_lift_squared_minus_one`
     - `aps_boundary_projector_fredholm`
     - `eta_zero_mode_cancellation_global`
     - `no_parity_anomaly_global`
     - `trace_regularization_standard_global`
   - Final script status: `aps_index_package_closed == true` (or explicit unresolved theorem blocker with provenance).

2. **Orbifold 2:1 lock**
   - Prove `janus_cover_ratio_derived` in Lean from concrete lemmas (no placeholder).
   - Close atomic obligations:
     - `global_euler_holonomy_class_computed`
     - `volume_cover_ratio_two_to_one`
     - `global_volume_ratio_unique_two_to_one`
   - Final script status: `janus_cover_ratio_derived == true` (or explicit unresolved theorem blocker with provenance).

3. **Action-to-equations interface**
   - Keep `P0EFTJanusZ4FullActionAtomicClosureGate` in non-axiomatic mode.
   - Ensure a single master operator source and source-to-observable map are explicit:
     - `U_Z4` source
     - projection / slip / TCA consistency
     - plus/minus junction compatibility
   - No new phenomenological parameters introduced in this phase.

## Execution sequence (strict)

1. `P0EFTJanusZ4APSIndexPackageObligationGate`
   - populate `aps_index_package_closed` with concrete proof chain;
   - output `hard_math_aps_pack_lock = true` in the gate payload.
2. `P0EFTJanusZ4OrbifoldCoverRatioObligationGate`
   - populate `janus_cover_ratio_derived` with concrete proof chain;
   - output `hard_math_orbifold_lock = true` in the gate payload.
3. `P0EFTJanusZ4HardGlobalTheoremReductionGate`
   - connect the two locks to the hard-action interface status.
4. Update audit scripts to reflect closure status and remove any stale `false` hardcoded gates.
5. Update tests only by changing assertions from open→closed after Lean gate updates.

## Target sequence (one change at a time)

1. **Lean source proof stage**
   - Add direct theorem exports (not axioms) for:
     - `pin_minus_lift_squared_minus_one`
     - `aps_boundary_projector_fredholm`
     - `eta_zero_mode_cancellation_global`
     - `no_parity_anomaly_global`
     - `trace_regularization_standard_global`
   - Add direct theorem exports for:
     - `global_euler_holonomy_class_computed`
     - `volume_cover_ratio_two_to_one`
     - `global_volume_ratio_unique_two_to_one`
   - Each theorem must be imported by its obligation gate, not re-axiomatised.

2. **Reduction stage**
   - Update both gate theorems and script payloads to consume the above proofs.
   - Keep assertions explicit when an external theorem is required.

3. **Lock status stage**
   - Keep `hard_global_lock_ready = true` only when both locks and the action-to-equation
     consistency checks are true.
   - Keep `full_cosmology_prediction_ready_no_fit = false` while either lock remains unresolved.

## Rules

- **No** new CMB/solver edits in this objective.
- **No** Planck/observational promotion while any of the three locks remains unresolved.
- **No** lambda retuning or ad-hoc transport tweaks.
- If a theorem is irreducible and external, keep explicit `external` blocker and do not hide it as `true`.
