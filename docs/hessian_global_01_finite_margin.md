# HESSIAN-GLOBAL-01 — marge coercive finie du Hessien total

Date : **9 août 2026**.

La façade publique :

```lean
global_candidateA_hessian_preferred_finite_margin_frontier_gate
```

conserve toute la fermeture H10–H14 issue des symétries exactes de l’action. Son
prérequis de coercivité est désormais un calcul fini explicite.

## 1. Marge principale

Les cinq secteurs Candidate-A possèdent des constantes diagonales positives.
Les dix blocs croisés symétriques possèdent des bornes `C_st`.

La marge principale est :

\[
c_{\mathrm{principal}}
=
c_{\mathrm{floor}}-
\sum_{s<t}C_{st}.
\]

La dominance stricte des blocs diagonaux donne :

\[
c_{\mathrm{principal}}>0,
\qquad
c_{\mathrm{principal}}\|x\|^2
\leq Q_{\mathrm{principal}}(x).
\]

## 2. Perturbation physique H11

La véritable forme physique H11 possède une constante calculée sur le cœur
dense :

\[
|Q_{\mathrm{phys}}(x)|
\leq C_{\mathrm{phys}}\|x\|^2.
\]

Elle contient le Robin/GHY H10 canonique et les six Hessiennes non-Robin du
chart Candidate-A.

Sous :

\[
C_{\mathrm{phys}}<c_{\mathrm{principal}},
\]

la marge totale devient :

\[
c_{\mathrm{total}}
=
c_{\mathrm{floor}}
-
\sum_{s<t}C_{st}
-
C_{\mathrm{phys}}>0.
\]

## 3. Conclusion

Le module

```text
P0EFTJanusProgramPCandidateAFiveSectorPhysicalSmallnessGarding4D
```

prouve directement :

\[
c_{\mathrm{total}}\|x\|^2
\leq Q_{\mathrm{total}}(x).
\]

Le gate public est :

```lean
global_candidateA_hessian_preferred_finite_margin_garding_gate
```

## 4. Données analytiques restantes

La preuve finale est ramenée à :

```text
5 bornes diagonales
10 bornes de couplage symétriques
1 borne physique H11 sur le cœur dense
2 comparaisons strictes de constantes
```

Les projecteurs de défaut, paramétrix, bases choisies du noyau total, image
fermée et indice sont reconstruits par les couches aval.

## 5. Statut

Cette façade, son audit et son workflow sont présents dans la PR #60. La PR
reste en brouillon jusqu’à certification Lean complète.
