# HESSIAN-GLOBAL-01 — marge par formes croisées continues

Date : **9 août 2026**.

La façade :

```lean
global_candidateA_hessian_preferred_crossForm_margin_frontier_gate
```

est la réduction analytique la plus concrète de la route H10–H14 actuelle.

## 1. Bloc principal

Les cinq composantes diagonales du bloc BRST–SpinC–LL possèdent des constantes
positives `c_s`. Leur minimum certifié est `c_floor`.

Les couplages entre secteurs sont représentés par dix véritables formes
bilinéaires continues :

\[
B_{st}:\mathcal H\times\mathcal H\to\mathbb R,
\qquad s<t.
\]

Chaque constante de couplage est construite :

\[
C_{st}=\|B_{st}\|.
\]

La borne quadratique

\[
|B_{st}(x,x)|\leq\|B_{st}\|\|x\|^2
\]

est automatique.

La marge principale est :

\[
c_{\mathrm{principal}}
=
c_{\mathrm{floor}}-
\sum_{s<t}\|B_{st}\|.
\]

## 2. Bloc physique

La forme H11 physique réelle est contrôlée par la constante canonique issue du
cœur dense :

\[
|Q_{\mathrm{phys}}(x)|
\leq C_{\mathrm{phys}}\|x\|^2.
\]

Elle rassemble le second Fréchet Robin/GHY H10 et les six Hessiennes physiques
non-Robin du chart.

## 3. Hessien total

Sous :

\[
C_{\mathrm{phys}}<c_{\mathrm{principal}},
\]

le module

```text
P0EFTJanusProgramPCandidateAFiveSectorCrossFormPhysicalSmallness4D
```

construit :

\[
c_{\mathrm{total}}
=
c_{\mathrm{floor}}
-
\sum_{s<t}\|B_{st}\|
-
C_{\mathrm{phys}}>0
\]

et prouve :

\[
c_{\mathrm{total}}\|x\|^2
\leq Q_{\mathrm{total}}(x).
\]

Le gate est :

```lean
global_candidateA_hessian_preferred_crossForm_margin_garding_gate
```

## 4. Frontière restante

Il reste à construire, dans les vrais espaces Candidate-A :

```text
5 énergies diagonales et leurs constantes
10 formes bilinéaires croisées continues
1 borne cœur-dense du bloc physique H11
```

puis à vérifier les deux strictes dominances.

Toutes les conclusions Fredholm et H14 restent produites par la chaîne aval.
La PR #60 demeure en brouillon jusqu’à validation Lean complète.
