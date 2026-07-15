# Six nouveaux programmes de recherche Janus

## Statut commun

Ces programmes sont **exploratoires (O)**. Ils ne complètent ni le programme P,
ni l'action Janus, ni la détermination sans ajustement de `alpha`.

Chaîne obligatoire :

```text
objet Janus explicite -> équations bien posées -> limite GR/standard
-> observable -> données -> falsification -> verdict T/X/C/N/O
```

## J-GW — Ondes gravitationnelles et sirènes standard

**Question.** La dynamique bimétrique produit-elle une propagation, des
polarisations ou une distance de sirène distinctes de GR ?

**Dépendances.** Action/Hessien P-A/P-C, fond actif, deux métriques physiques et
couplage à la matière visible.

**Gates.**

1. `GW01` — dériver l'action tensorielle quadratique sur Minkowski puis FLRW.
2. `GW02` — diagonaliser modes sans masse/massif; tester fantômes, gradients,
   causalité et limite GR.
3. `GW03` — calculer vitesse, dispersion, oscillation inter-secteurs,
   amortissement et polarisations.
4. `GW04` — construire formes d'onde simples et distance de sirène.
5. `GW05` — likelihood publique GW avec/sans contrepartie électromagnétique.

**No-go.** Rejet si fantôme, instabilité observable, vitesse incompatible sans
mécanisme dérivé, ou absence de limite GR.

**Cibles.** Lean : diagonalisation et positivité conditionnelle. Python :
dispersion, propagation cosmologique, formes d'onde et likelihood.

**Avancement.** `GW01-Minkowski-TT` est fermé à niveau T/C; la dérivation FLRW
reste ouverte. Voir `docs/program_j_gw_status.md`.

## J-CO — Pulsars, binaires et plugstars

**Question.** Une solution compacte Janus régulière existe-t-elle et possède-t-elle
une signature extérieure mesurable ?

**Dépendances.** Équations non linéaires, matière des deux secteurs, jonctions et
métrique mesurée. `X2025-plugstars-jmp` reste une source de navigation, pas une
dérivation validée.

**Gates.**

1. `CO01` — vérifier manuellement les équations et conventions plugstar.
2. `CO02` — poser et résoudre l'ansatz statique sphérique à deux métriques.
3. `CO03` — régularité, masse ADM/quasi-locale et stabilité radiale.
4. `CO04` — orbites, Shapiro, précession, lentille et échos éventuels.
5. `CO05` — binaire post-newtonienne et perte d'énergie.
6. `CO06` — comparaison pulsars, binaires compactes et imagerie forte.

**No-go.** Rejet si coquille non conservée, violation de Bianchi, instabilité
radiale ou profil choisi sans équation d'état dérivée.

**Cibles.** Lean : jonctions/conservation. Python : solveur TOV bimétrique,
perturbations, timing et lentilles.

**Avancement.** `CO01` vérifie le noyau algébrique de la source et conclut que
`CO02` reste bloqué par l'absence d'équations statiques bimétriques, de loi de
conversion, de jonctions et d'équation d'état. Voir `docs/program_j_co_status.md`.

## J-TH — Thermodynamique hors équilibre de `Sigma`

**Question.** Les lois de passage à travers `Sigma` admettent-elles une
thermodynamique cohérente et une production d'entropie non négative ?

**Dépendances.** Courants à `Sigma`, orientation PT, temps physique/relationnel,
température et entropie définies par un état.

**Gates.**

1. `TH01` — bilans locaux d'énergie, charge et entropie des deux côtés.
2. `TH02` — classifier forces et flux sous PT.
3. `TH03` — Onsager-Casimir et positivité de la production d'entropie.
4. `TH04` — interface mobile et réponse non linéaire.
5. `TH05` — pont avec l'horloge entropique, sans confondre entropie thermique
   et intrication.
6. `TH06` — tester une éventuelle sélection d'état ou de secteur.

**No-go.** Rejet d'une loi de passage si elle permet une production totale
négative, ou si l'équilibre PT supprime la gorge faute de charge dérivée.

**Cibles.** Lean : bilans et formes positives. Python : transport couplé et
stabilité hors équilibre.

**Avancement.** `TH01-TH03` ferment le noyau conditionnel : bilans, parités
Onsager-Casimir et cône de production d'entropie positive. Les courants et
coefficients physiques attendent P (`TH-P01` à `TH-P06`).

## J-BBN — Nucléosynthèse, neutrinos et plasma primordial

**Question.** Une histoire thermique Janus respecte-t-elle les abondances
légères et le rayonnement relativiste ?

**Dépendances.** Fond pré-découplage réel, relation température-temps,
microphysique et conditions initiales. Le prototype Boltzmann ne suffit pas.

**Gates.**

1. `BBN01` — fermer le fond radiatif et sa conservation.
2. `BBN02` — distributions/collisions photons, leptons et neutrinos.
3. `BBN03` — transfert inter-secteurs et `Delta N_eff`.
4. `BBN04` — coupler un réseau BBN validé.
5. `BBN05` — reproduire la référence GR.
6. `BBN06` — D/H, He-3, He-4, Li-7 et confrontation BBN+CMB.

**No-go.** Rejet si aucune région dérivée ne reproduit expansion, `N_eff` et
abondances, ou si une température libre du secteur négatif est ajoutée à la
main.

**Cibles.** Lean : conservation/positivité. Python : backend BBN-neutrinos et
tests de référence.

## J-PT — Transition de phase et sélection d'état PT/CPT

**Question.** Une transition peut-elle sélectionner branche, flux ou état de
gorge sans importer la valeur observée de `alpha` ?

**Dépendances.** Espace de champs de P, action effective renormalisée,
prescription d'état et température éventuelle.

**Gates.**

1. `PT01` — classifier les paramètres d'ordre compatibles avec PT/CPT.
2. `PT02` — dériver le potentiel effectif minimal depuis une action déclarée.
3. `PT03` — phases, minima, ordre de transition et stabilité.
4. `PT04` — nucléation, percolation, défauts et domaines.
5. `PT05` — vérifier une sélection non circulaire du flux/de l'échelle.
6. `PT06` — fond stochastique GW, reliques et isocourbure.

**No-go.** La transition ne fixe pas `alpha` si les minima restent reliés par
une dilatation commune ou si une constante dimensionnelle libre est insérée.

**Cibles.** Lean : symétries, extrema et no-go d'échelle. Python : potentiel
thermique, bounce et spectre GW.

**Avancement.** `PT01-PT03` ferment la classification paire, les minima du
modèle quartique et le no-go de sélection d'échelle. Le potentiel physique
attend P (`PT-P01` à `PT-P06`).

## J-SF — Superfluide/condensat comme analogue

**Question.** Deux condensats peuvent-ils simuler certains mécanismes Janus et
révéler leurs instabilités ?

**Portée.** Analogie contrôlée uniquement; elle ne prouve pas que l'Univers est
un superfluide.

**Gates.**

1. `SF01` — modèle à deux champs de Gross-Pitaevskii et dictionnaire Janus.
2. `SF02` — fond, interface et métriques acoustiques.
3. `SF03` — spectre de Bogoliubov, modes localisés et stabilité.
4. `SF04` — transmission, réflexion, conversion et quench PT.
5. `SF05` — séparer invariants universels et artefacts du milieu.
6. `SF06` — protocole numérique puis, seulement si pertinent, expérimental.

**No-go.** Abandon si le signe recherché exige une énergie non bornée, si seule
la cinématique est reproduite, ou si le dictionnaire repose sur un réglage sans
homologue Janus.

**Cibles.** Lean : stabilité conditionnelle du modèle réduit. Python : solveur
Gross-Pitaevskii/Bogoliubov 1D puis 2D.

**Avancement.** `SF01-SF03` ferment le fond analogue stable et son spectre;
`SF04` ferme la diffusion acoustique à marche d'impédance. L'équivalence
fondamentale avec Janus reste explicitement non démontrée.

## Ordre d'exécution

Lots initiaux parallélisables : `GW01`, `CO01`, `TH01`, `BBN01`, `PT01`,
`SF01`. Priorité scientifique : J-GW, J-CO, J-TH, J-BBN, J-PT, puis J-SF.
Aucun test observationnel ne commence avant fermeture de la gate théorique et
reproduction de la référence GR ou du modèle analogue standard.
