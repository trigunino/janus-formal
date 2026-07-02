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
- prochain verrou CMB : fermeture complete de la hierarchie Boltzmann photon /
  polarisation.

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

Validation CMB/Z4 active :

```bash
lake build JanusFormal
python -m unittest tests.test_p0_eft_janus_z4_cmb_diagnostic_master_report_script
python -m unittest tests.test_p0_eft_janus_z4_acoustic_polarization_joint_consistency_gate_script
python -m unittest tests.test_p0_eft_janus_z4_acoustic_polarization_closed_theta2_joint_gate_script
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
