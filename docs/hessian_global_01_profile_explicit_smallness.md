# HESSIAN-GLOBAL-01 — profil numérique et petite norme explicite

Date : **9 août 2026**.

Cette note décrit l’entrée publique actuellement privilégiée pour la fermeture
H10–H14 du Hessien Candidate-A :

```lean
global_candidateA_hessian_preferred_action_symmetry_frontier_gate
```

Elle combine la géométrie H10 déjà fermée, les six Hessiennes physiques
canoniques, les symétries exactes de l’action et une estimation de Gårding dont
la petite perturbation H11 est mesurée sur le cœur lisse dense.

## 1. Les cinq secteurs D10-free

Le profil numérique contient cinq multiplicités :

```text
metric / diffeomorphism
Abelian gauge
primitive SpinC matter
longitudinal / LL
boundary / finite-BV
```

Aucune direction physique D10 n’est introduite. Pour chaque secteur de
multiplicité `n`, le type de coordonnées est `Fin n`.

Le profil ne choisit pas une base arbitraire du noyau complet. Il fixe seulement
le nombre et l’étiquetage des transformations candidates dans chaque secteur.

## 2. Les zéro-modes proviennent de l’action

Pour chaque mode sectoriel `v`, l’entrée analytique demande une invariance
locale exacte :

\[
S(x+t v)=S(x)
\]

sur un voisinage de l’origine. Le calcul de Noether déjà formalisé en déduit :

\[
D^2S(0)(v,w)=0
\]

pour tout `w`, puis :

\[
Hv=0
\]

pour le véritable représentant de Riesz du Hessien augmenté.

Les équations de zéro-mode ne sont donc pas des champs indépendants du paquet
terminal.

## 3. Indépendance et exhaustivité

Les familles sectorielles sont assemblées dans une famille orthogonale globale.
L’orthogonalité et la non-nullité donnent l’indépendance linéaire. L’estimation
de Gårding sur l’orthogonal de leur span interdit tout zéro-mode caché.

On obtient alors l’égalité exacte :

\[
\dim\ker H
=
\sum_{s\in\mathrm{Sector}}
\operatorname{multiplicité}(s).
\]

La façade numérique expose cette égalité via :

```lean
global_candidateA_hessian_canonicalSix_profileActionSymmetryExplicitSmallness_exact_count
```

## 4. Petite norme H11 calculée sur le cœur dense

L’ancienne route demandait directement :

```text
‖physical.form‖ < cPrincipal
```

sur la complétion. La route actuelle utilise les véritables formes physiques
sur le cœur diagonal dense.

Le morphisme cœur-vers-chart possède une constante `Cchart`. Les six Hessiennes
non-Robin du chart donnent une somme de normes, tandis que le bloc Robin est le
second Fréchet canonique de l’action GHY H10. La constante publique est donc de
la forme :

\[
C_{\mathrm{phys}}
=
C_{\mathrm{Robin}}
+
C_{\mathrm{chart}}^2
\sum_{j=1}^{6}\|B_j\|.
\]

La seule comparaison terminale est :

\[
C_{\mathrm{phys}}<c_{\mathrm{principal}}.
\]

La densité transfère ensuite cette estimation à la forme continue H11 complète.
Aucune forme physique arbitraire n’est choisie sur la complétion.

## 5. Sortie terminale

L’entrée préférée assemble automatiquement :

```text
H10  Robin/GHY same-action et Hessien symétrique
H13  vrai Hessien local Candidate-A
H11  prolongement physique continu sur l’unique domaine commun
H12  image fermée, noyau fini, Fredholm, indice zéro
H14  certificat global terminal
```

Elle fournit aussi :

```text
le modèle fini exact du noyau
le comptage par secteur
le gap coercif sur l’orthogonal du noyau
le Green réduit
la résolvante dans le gap
la stabilité sous petites perturbations auto-adjointes
```

## 6. Travail physique restant

La frontière est désormais ramenée aux preuves suivantes :

1. construire les cinq familles de transformations physiques dans le véritable
   espace de Hilbert commun ;
2. démontrer l’invariance locale de l’action Candidate-A sous chacune ;
3. démontrer leur non-nullité et leur orthogonalité croisée ;
4. prouver l’estimation de Gårding du bloc principal BRST–SpinC–LL sur leur
   orthogonal ;
5. établir la borne du morphisme cœur lisse vers le chart physique ;
6. vérifier numériquement ou analytiquement
   `canonicalSevenPhysicalConstant < principalGardingConstant`.

Les projecteurs auxiliaires, paramétrix abstraits, bases choisies du noyau total,
sept extensions physiques indépendantes et secondes complétions ne font plus
partie de l’interface privilégiée.

## 7. Statut Lean

Les modules, façades, audits statiques et workflows ciblés sont présents sur la
branche de la PR #60. La PR reste volontairement en brouillon : un build Lean
complet et vert demeure nécessaire avant de parler de certification par le
noyau.
