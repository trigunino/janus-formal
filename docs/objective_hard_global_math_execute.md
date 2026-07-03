# Hard Global Math Objective (Execution-Ready)

## Objectif
Cloturer proprement les verrous mathematiques centraux en bloc:
1) APS/Pin global
2) Orbifold 2:1 global
3) Interface action Z4 -> equations sans placeholder

## Non-goals (for this objective)
- Aucun nouveau patch CMB/solver
- Aucun retuning de parametres Z4
- Aucun nouveau canal observateur

## Deliverables
- Lean gate: `P0EFTJanusZ4APSIndexPackageObligationGate` produit `aps_index_package_closed = true`.
- Lean gate: `P0EFTJanusZ4OrbifoldCoverRatioObligationGate` produit `janus_cover_ratio_derived = true`.
- Lean gate: `P0EFTJanusZ4HardGlobalTheoremReductionGate` relie les deux fermetures au lock global.
- Scripts Python audit mis a jour pour ecrire explicitement les obligations fermees.
- Tests unitaires mis a jour en consequence.

## Tasks (strict order)
1. APS/Pin hard lock
   - Trouver les theoremes Lean concrets pour:
     - pin_minus_lift_squared_minus_one
     - aps_boundary_projector_fredholm
     - eta_zero_mode_cancellation_global
     - no_parity_anomaly_global
     - trace_regularization_standard_global
   - Brancher ces theoremes dans `P0EFTJanusZ4APSIndexPackageObligationGate`.
   - Exiger `aps_index_package_closed = True` (pas d`axiom`, pas de `sorry`).
   - Script payload attendu: `aps_index_package_closed=true`, `hard_math_aps_pack_lock=true`.

2. Orbifold 2:1 hard lock
   - Trouver les theoremes Lean concrets pour:
     - global_euler_holonomy_class_computed
     - volume_cover_ratio_two_to_one
     - global_volume_ratio_unique_two_to_one
   - Les enchaîner dans `P0EFTJanusZ4OrbifoldCoverRatioObligationGate`.
   - Exiger `janus_cover_ratio_derived = True`.
   - Script payload attendu: `janus_cover_ratio_derived=true`, `hard_math_orbifold_lock=true`.

3. Reduction vers le lock global
   - Verifier que `P0EFTJanusZ4HardGlobalTheoremReductionGate` depasse par implication.
   - Activer `hard_global_lock_ready = True` seulement si APS + orbifold sont fermes.
   - Maintenir `full_cosmology_prediction_ready_no_fit = false` tant qu’un lock hard reste ouvert.

## Exit criteria
- hard_math_aps_pack_lock == true
- hard_math_orbifold_lock == true
- hard_global_lock_ready == true (si interface action/eqns coherent)
- Sinon: external_theorem_blocker=true + provenance, sans faux `true`.

## Stop rule
Si un verrou demande une preuve externe irreductible:
- marquer l'objectif blocked
- enregistrer la provenance exacte
- ne jamais simuler une fermeture.

## Execution policy
- un seul changement majeur (une preuve/gate) puis build+tests
- zero CMB/solver edits dans ce mode
- zero promotion planck avant verrouillage
