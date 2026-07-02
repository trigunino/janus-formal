# Janus Formal Scaffold

Depot de travail pour formaliser et tester un pipeline Janus autour de :

- modules Lean (`JanusFormal/`) ;
- scripts Python d'audit et de generation de rapports (`scripts/`) ;
- tests unitaires (`tests/`) ;
- donnees traitees minimales (`data/processed/`) ;
- documentation scientifique et cartes de sources (`docs/`, `formal/`).

## Etat actuel

Statut separe par niveau de preuve :

- `formal_topology_scaffold_complete = True`
- `aps_global_theorem_proved = True`
- `orbifold_global_theorem_proved = True`
- `holst_geometric_lock_closed = True`
- `late_time_growth_branch_observationally_viable = True`
- `cmb_bao_monommetric_camb_hooks_sufficient = False`
- `bi_sector_boltzmann_backend_required = Open`
- `janus_z4_cmb_solver_status = InProgress`
- `acoustic_polarization_joint_gate_passed = False`
- `closed_theta2_acoustic_polarization_candidate = True`
- `photon_polarization_boltzmann_hierarchy_closed_effective = True`
- `boltzmann_closed_effective_z4_cmb_candidate = True`
- `planck_likelihood_completeness_candidate_trial_allowed = True`
- `full_planck_validation_allowed = False`
- `closed_boltzmann_candidate_robust = True`
- `standalone_highl_TE_EE_acquired = False`
- `standalone_highl_TE_EE_handshake_passed = False`
- `full_observational_cosmology_no_fit_ready = False`

Les verrous mathematiques internes formalises sous Lean restent fermes. Ce qui reste
ouvert n'est pas la topologie APS/orbifold, mais la validation observationnelle
complete avec un backend cosmologique capable de representer correctement le
caractere bi-secteur Janus-orbifold.

Les derniers gates CMB/BAO montrent que les hooks mono-metriques CAMB sont utiles
comme diagnostics EFT, mais insuffisants comme preuve finale du modele complet.

Le solveur CMB/Z4 suit maintenant une politique stricte :

- les spectres Planck officiels ne doivent pas consommer le solveur natif tant
  que la limite GR n'est pas validee contre une reference standard ;
- les deltas Z4 non nuls sont testes uniquement comme deviations controlees
  autour d'une baseline CAMB-GR sure ;
- le dernier gate acoustique/polarisation trouve un meilleur point
  `lambda_T=-0.008`, `lambda_E=-0.02` avec `delta_chi2 ~= -9.49`, mais il ne
  passe pas : les gardes de lissage TE/EE echouent ;
- la fermeture tight-coupling effective `Theta2` leve ce blocage : le gate
  ferme donne `delta_chi2 ~= -9.20`, interaction `~=-0.155`, et les gardes
  TE/EE passent ;
- statut exact : candidat acoustique/polarisation effectif, pas verdict Planck ;
- la hierarchie Boltzmann photon/polarisation est maintenant fermee au niveau
  effectif scalaire (`Theta_l`, `E_l`, source `Pi`, TCA -> free-streaming,
  convergence `lmax`) ;
- le trial Planck ferme-Boltzmann local preserve le gain
  (`delta_chi2 ~= -9.20`, ratio de preservation `~=1.000`) ;
- statut exact : `boltzmann_closed_effective_z4_cmb_candidate`, pas validation
  Planck globale.
- la complétude likelihood autorise le trial candidat, mais bloque la validation
  Planck complète car les standalone high-l TE/EE restent absents localement ;
- la robustesse locale du candidat passe : meilleur point non-edge, courbure
  locale détectée, gain conserve sous `lmax`/TCA.
- le candidat est gelé pour la prochaine validation : pas de retuning, pas de
  nouveau canal, pas d'ouverture slip/recombinaison/visibilité/miroir/primordial ;
- prochain verrou externe : acquérir ou raccorder standalone high-l TE/EE, puis
  tester exactement le même candidat.
- le handshake standalone TE/EE doit vérifier `C_l/D_l`, unités, signe TE,
  indexation `ell`, nuisance vector, foregrounds et sanity GR avant tout trial
  de décomposition high-l.

Freeze rule after checkpoint `8ce53806`: no new Z4 physics or parameter
retuning is allowed until standalone high-l TE/EE likelihood coverage is
acquired and the frozen candidate is rerun unchanged.

Point d'entree principal :

- `JanusFormal/P0EFTGlobalTopologyMasterLock.lean`
- `scripts/build_p0_eft_run9_master_lock.py`

## Validation rapide

```bash
python -m unittest discover -s tests -p "test_p0_eft_run*.py"
lake build JanusFormal.P0EFTGlobalTopologyMasterLock
```

Validation plus large :

```bash
lake build
```

Validation Lean active :

```bash
lake build JanusFormal
```

`JanusFormal.lean` est volontairement une facade active minimale. Le graphe
complet historique reste disponible dans :

```bash
lake build JanusFormal.AllImportsArchive
```

Validation CMB/Z4 active :

```bash
lake build JanusFormal
python -m unittest tests.test_p0_eft_janus_z4_cmb_diagnostic_master_report_script
python -m unittest tests.test_p0_eft_janus_z4_acoustic_polarization_joint_consistency_gate_script
python -m unittest tests.test_p0_eft_janus_z4_acoustic_polarization_closed_theta2_joint_gate_script
python -m unittest tests.test_p0_eft_janus_z4_photon_polarization_boltzmann_hierarchy_closure_gate_script
python -m unittest tests.test_p0_eft_janus_z4_official_planck_closed_boltzmann_acoustic_polarization_trial_script
python -m unittest tests.test_p0_eft_janus_z4_planck_likelihood_completeness_gate_script
python -m unittest tests.test_p0_eft_janus_z4_closed_boltzmann_candidate_robustness_gate_script
python -m unittest tests.test_p0_eft_janus_z4_standalone_teee_acquisition_gate_script
python -m unittest tests.test_p0_eft_janus_z4_standalone_teee_handshake_gate_script
```

`JanusFormal.LegacyCMB` est une archive compile-only des anciens essais
mono-metriques CAMB/Planck. Ne pas l'utiliser comme validation standard du
solveur Z4 natif ni comme preuve physique.

## Organisation utile

- `JanusFormal.lean` importe l'ensemble des modules Lean actifs.
- `JanusFormal/LegacyCMB.lean` regroupe les anciens diagnostics mono-metriques
  CAMB/Planck. Ils restent hors validation CMB/Z4 standard.
- `JanusFormal/P0EFT*.lean` contient les verrous formels EFT/topologie.
- `scripts/build_p0_eft_run*.py` genere les payloads et rapports d'audit.
- `tests/test_p0_eft_run*.py` verifie les statuts exposes par ces scripts.
- `data/processed/p0_eft_fsigma8/sdss_dr16_fsigma8_points.csv` contient le jeu traite minimal suivi.

## Non suivi par Git

Le depot exclut volontairement :

- `.venv/`
- `.lake/`
- `outputs/`
- `data/raw/`
- `*.egg-info/`
- caches Python

Ces elements sont regenerables localement et ne doivent pas etre pousses.

## Current CMB/Z4 checkpoint

- Standalone high-l TE/EE Cobaya wrappers and `.clik` data are available locally.
- GR/CAMB standalone TE/EE handshake passes.
- Frozen candidate high-l decomposition was rerun unchanged:
  - `lambda_T = -0.008`
  - `lambda_E = -0.02`
  - legacy overlapping diagnostic total: `delta_chi2 = -9.4326`
  - non-overlapping combined high-l total: `delta_chi2 = -5.6962`
  - non-overlapping decomposed high-l total: `delta_chi2 = -5.3212`
  - `delta_chi2_highl_TE = +0.0412`
  - `delta_chi2_highl_EE = -0.2733`
- `planck_highl_decomposed_effective_candidate = True`
- nuisance/foreground policy: `fixed_nuisance_effective_candidate`;
  no global nuisance profiling has been performed.
- nuisance sensitivity: local symmetric nuisance perturbations preserve the
  non-overlap gains; status `nuisance_sensitivity_checked_candidate`.
- local nuisance profiling: profiled gains remain favorable
  (`-5.1768`, `-5.9829`), but nuisance boundary hits are present
  (`calib_217T`, `gal545_A_217`), so
  `local_profiled_nuisance_effective_candidate = False`.
- boundary-safe nuisance profiling: guarded/fixed policies remove the boundary
  issue while preserving gains:
  - `boundary_guarded`: `(-5.7058`, `-6.5223`) for combined/decomposed bases;
  - `problem_nuisances_fixed`: `(-13.1561`, `-12.0977`);
  - `boundary_safe_local_profiled_candidate = True`.
- `profiled_planck_candidate = False` and `full_planck_validation = False`.
- residual diagnostics: TT peak shifts, TE zero shifts and EE peak shifts are
  zero in the tested high-l bands.
- This is still not a full Planck validation.
