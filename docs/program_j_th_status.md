# J-TH — thermodynamique de Sigma

## Statut

## Raccordement technique a P

- `TH-BP01` ferme : base effective D8 mesuree et interaction Candidate A integree.
- `TH-BP02` ferme : invariance PT de la premiere variation integree.
- `TH-BP03` ferme (passe 2) : chaine de variation des champs induits et reponse croisee nulle des secteurs non metrique/matiere.
- `TH-BP04` ferme (passe 3) : equivalence entre stationnarite LL canonique et equation forte PT-symetrique sous contrat d'integration par parties.
- `TH-BP05` ferme (passe 4) : trace thermique nucleaire du throat produit lisse et completement monotone aux temps positifs.
- `TH-BP06` ferme (passe 5) : les equations d'Euler scalaires locales impliquent conditionnellement la conservation globale du stress.
- `TH-BP07` ferme (mise a jour P 23/07) : certificat Green global de l'onde intrinseque avec transport pondere et facteur bulk/bord exact.
- Reprise P : identifier cette variation a des courants physiques, puis deriver energie, entropie et loi d'etat. `TH-P01` et les entrees microscopiques restent ouverts.

`TH01-TH03` sont fermés comme noyau **conditionnel T/X**. Ils classifient les
lois admissibles; ils ne dérivent pas encore les courants ni les coefficients
microscopiques de Janus.

## TH01 — bilans

Le bilan commun est

```text
dE_plus + dE_minus + dE_Sigma = P_external.
```

Un échange fermé `(-J,+J)` conserve exactement l'énergie totale. Une énergie
stockée sur `Sigma` compense également un déséquilibre des deux courants.
Le signe gravitationnel du secteur négatif reste séparé du signe de sa densité
thermodynamique : aucune « entropie négative » n'est postulée.

## TH02 — PT et Onsager-Casimir

Pour des parités `epsilon_i`, la relation conditionnelle est

```text
L_ij = epsilon_i epsilon_j L_ji.
```

Des canaux de même parité ont des coefficients croisés réciproques. Des canaux
de parité opposée ont une partie croisée antisymétrique, qui s'annule dans la
production quadratique d'entropie. L'application physique exige encore un état
d'équilibre et les parités microscopiques réelles.

## TH03 — second principe

La production à deux canaux

```text
sigma = L11 X1^2 + 2 L12_sym X1 X2 + L22 X2^2
```

est non négative lorsque la partie symétrique est positive semi-définie. Lean
prouve le critère avec `L11>0` et `L12_sym^2 <= L11 L22`. Le code Python teste
directement les valeurs propres pour une matrice de taille quelconque. Un
coefficient diagonal négatif fournit un contre-exemple explicite au second
principe.

## Registre de reprise P

| ID | Entrée manquante | Utilisation |
| --- | --- | --- |
| `TH-P01` | courants d'énergie issus de l'action | bilan physique TH01 |
| `TH-P02` | énergie/charge réellement stockée sur Sigma | terme de bord |
| `TH-P03` | forces thermodynamiques et températures d'état | définition de `X_i` |
| `TH-P04` | parités PT microscopiques | Onsager-Casimir physique |
| `TH-P05` | coefficients de transport dérivés | test du cône positif |
| `TH-P06` | état d'équilibre ou stationnaire sélectionné | domaine linéaire |

Point de reprise : instancier les structures `TH01Inputs`, `TH02Inputs` et
`TH03Status`; ne pas ajuster une matrice positive arbitraire puis l'appeler loi
Janus.

## TH04 — interface mobile et relaxation

Le bilan de saut conditionnel est

```text
J_plus - J_minus - v_Sigma (rho_plus-rho_minus) - source_Sigma = 0.
```

La limite stationnaire retrouve la continuité du flux. Un système linéaire
`Xdot=-L X` avec partie symétrique positive possède le Lyapunov
`V=|X|²/2`, non croissant. Le solveur Python utilise l'exponentielle spectrale
exacte pour les matrices symétriques.

Reprises : `TH-P07` vitesse physique de Sigma, `TH-P08` densités surfaciques,
`TH-P09` conditions de saut dérivées, `TH-P10` matrice de relaxation.

## TH05 — pont quantique

Un état de Bell pur vérifie dans l'audit :

```text
S_total=0,  S_plus=S_minus=log(2),  I(+:-)=2 log(2).
```

Cette entropie réduite est de l'intrication, pas une production thermique. Une
interprétation thermodynamique exige encore bain/coarse-graining, séparation
chaleur-travail et fonctionnelle de production.

Reprises : `TH-P11` état quantique global, `TH-P12` algèbres plus/minus,
`TH-P13` coarse-graining ou bain, `TH-P14` séparation chaleur-travail et
`TH-P15` production entropique dérivée.

## Cibles

```text
JanusFormal.Branches.JanusSigmaThermodynamics
src/janus_lab/sigma_thermodynamics.py
tests/test_sigma_thermodynamics.py
```
