# J-PT — transition de phase et sélection d'état

## Statut

## Raccordement technique a P

- `PT-BP01` ferme : interaction Candidate A locale/integree et invariance PT sur la base D8 mesuree.
- `PT-BP02` ferme (passe 2) : derivee effective de l'action globale Candidate A sous contrat explicite de domination.
- `PT-BP03` ferme (passe 3) : action scalaire holonome reguliere sur metrique lorentzienne generale et premiere variation effective.
- `PT-BP04` ferme (passe 4) : developpement exact le long d'une droite avec reste quadratique controle pour la fonctionnelle scalaire generale.
- `PT-BP05` ferme (passe 5) : seconde derivee non negative de la trace thermique nucleaire du cercle aux temps positifs.
- `PT-BP06` ferme (mise a jour P 23/07) : identite d'energie exacte et estimation coercive pour le reste scalaire.
- Reprise P : extraire un parametre d'ordre scalaire et son potentiel effectif renormalise. Ce pont ne ferme pas `PT-P01/PT-P03` et ne fournit pas encore de temperature critique.

`PT01-PT03` ferment un noyau de Landau **conditionnel T/X**. Ils établissent ce
que la symétrie PT permet et, surtout, ce qu'elle ne sélectionne pas.

## PT01 — paramètre d'ordre

Pour un paramètre d'ordre réel PT-impair `phi`, le potentiel minimal pair est

```text
V(phi)=a phi^2+b phi^4.
```

Lean vérifie `V(-phi)=V(phi)` pour toutes les valeurs de `a,b`. PT élimine les
termes impairs mais ne fixe aucun coefficient pair.

## PT02 — minima

Pour `b>0` :

- `a>=0` donne la phase symétrique `phi=0`;
- `a<0` donne deux minima PT-conjugués
  `phi²=-a/(2b)`;
- leur courbure vaut `-4a>0`;
- `phi=0` devient alors un maximum.

Le solveur Python classe les extrema et construit le diagramme thermique jouet
`a(T)=A(T²-Tc²)`.

## PT03 — no-go d'échelle

La valeur non nulle est entièrement déterminée par le rapport `-a/(2b)`. Une
rescaling de `a` rescale directement le minimum. Ainsi :

```text
symétrie PT + forme paire != sélection d'une échelle physique.
```

Introduire `Tc`, `a` ou un minimum voulu à la main déplacerait simplement le
problème de `alpha`.

## Registre de reprise P

| ID | Entrée manquante | Utilisation |
| --- | --- | --- |
| `PT-P01` | véritable paramètre d'ordre Janus | remplacer `phi` jouet |
| `PT-P02` | représentation/parité PT dérivée | base d'invariants |
| `PT-P03` | action effective renormalisée | coefficients `a,b,...` |
| `PT-P04` | prescription d'état et de température | diagramme physique |
| `PT-P05` | normalisation dimensionnelle non circulaire | test de `alpha` |
| `PT-P06` | termes de gradient et cinétique | nucléation/domaines |

Point de reprise : extraire les coefficients depuis la seconde variation et
l'action effective P; ne pas ajuster `a,b,Tc` à la valeur recherchée de
`alpha`.

## Cibles

```text
JanusFormal.Branches.JanusPTPhaseTransition
src/janus_lab/pt_phase_transition.py
tests/test_pt_phase_transition.py
```
