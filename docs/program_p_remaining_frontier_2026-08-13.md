# Programme P — bilan et frontière restante au 13 août 2026

## Portée de ce bilan

Ce document distingue trois niveaux qui ne doivent pas être confondus :

1. **fermé dans la façade canonique antérieure** : résultat déjà annoncé comme
   `DONE` à sa portée déclarée dans les feuilles de route du dépôt ;
2. **implémenté architecturalement dans la PR #60** : structures, réductions et
   certificats écrits, mais branche volontairement non validée par un build
   Lean complet ;
3. **preuve mathématique ou physique encore ouverte** : contenu qui ne peut pas
   être obtenu par simple assemblage des interfaces existantes.

La PR #60 reste une branche de travail. Aucun statut `DONE` canonique nouveau
ne doit être déduit de ce document avant élaboration Lean, audit des axiomes et
raccord aux façades publiques.

## 1. Socle global déjà fermé à sa portée déclarée

Les feuilles de route canoniques marquent comme fermés :

```text
GEO-GLOBAL-01
FIELD-GLOBAL-01
ANALYSIS-GLOBAL-01
BOUNDARY-GLOBAL-01
KJ-GLOBAL-01
KJ-GLOBAL-02
NATURAL-GLOBAL-01
ACTION-GLOBAL-01
EULER-GLOBAL-01          (chartwise)
NOETHER-GLOBAL-01        (secteur physique U(1)²)
HELMHOLTZ-GLOBAL-01      (chartwise)
VARCOH-GLOBAL-01
DIRAC-GLOBAL-01
REGULATOR-GLOBAL-01      (portée régulateur déclarée)
```

Cela fournit déjà :

* la géométrie Candidate-A intrinsèque et ses champs communs ;
* les domaines Sobolev/trace/bord ;
* le complexe covariant et la classification naturelle finie ;
* l'action régulière assemblée, son Euler et sa reconstruction de Helmholtz sur
  les cartes admissibles ;
* le Dirac global géométrique et le régulateur de référence dans leurs portées
  respectives.

Ces résultats ne sélectionnent pas encore une valeur physique unique de tous
les coefficients EFT et ne ferment pas automatiquement ADM, BRST complet,
Hessien elliptique, stabilité ou Quillen familial.

## 2. Ce que la PR #60 ajoute architecturalement

### 2.1 Hessien pointwise et vrai complément du noyau

La route préférée introduite dans la PR utilise une seule décomposition
orthogonale physique

```text
E ≃ M × A × S × L × B
```

et la restreint canoniquement à `(ker H)ᗮ`. Elle assemble :

```text
action Candidate-A véritable
→ Hessien augmenté auto-adjoint
→ générateurs exacts issus des symétries d'action
→ cinq projecteurs physiques
→ opérateur principal réduit A_red
→ cinq bornes diagonales + un reste A_off
→ petitesse H11
→ gap sur (ker H)ᗮ
→ Fredholm, indice zéro, Green, résolvante, stabilité.
```

Elle ajoute aussi une couche de domaine maximal bosonique/SpinC et une route de
fermeture micro-globale. Ces couches sont des architectures de preuve jusqu'à
leur instanciation concrète et leur élaboration.

### 2.2 Trace relative, Mellin et Quillen

La même branche poursuit le vrai opérateur réduit vers :

```text
exp(-t H_red)
→ différence relative avec un opérateur de référence
→ trace nucléaire intrinsèque
→ partie finie
→ Mellin/zêta
→ famille de déterminants
→ connexion de Bismut--Freed
→ atlas de références/coupures spectrales
→ clutching et holonomie.
```

La compacité absolue de l'exponentielle bornée n'est pas postulée : la branche
formalise au contraire qu'elle forcerait la dimension finie. Le chemin
spectral utilise donc une différence relative.

### 2.3 Vraie ligne de déterminant Fredholm

Les derniers fichiers construisent maintenant, pour une famille auto-adjointe,
la fibre réelle

```text
Det_Fred(H_a) = Hom(det coker H_a, det ker H_a).
```

L'égalité `range H_a = (ker H_a)ᗮ` donne canoniquement
`coker H_a ≃ ker H_a`. Une base physique fixe de chaque noyau fournit :

* les transports de noyau et de cokernel ;
* les transports des puissances extérieures maximales ;
* une ligne Fredholm de dimension un ;
* un frame non nul ;
* une normalisation exacte par les volumes nommés du noyau et du cokernel.

Le déterminant zêta complexe du complément inversible est encore conservé
comme seconde composante d'un paquet scindé. L'identification finale avec la
complexification/tensorisation de la ligne réelle reste explicitement ouverte.

## 3. Frontières mathématiques principales restantes

## A. Rendre la PR #60 réellement certifiée par Lean

C'est le premier verrou opérationnel, même s'il est volontairement différé :

1. élaborer les nouveaux fichiers dans l'ordre de dépendance ;
2. corriger imports, namespaces, paramètres implicites et conflits
   d'instances ;
3. supprimer les doublons de façades et anciennes routes devenues obsolètes ;
4. vérifier l'absence de `sorry`, `admit`, axiomes non documentés et
   déclarations `unsafe` ;
5. raccorder les gates préférées aux imports publics ;
6. faire passer le build complet puis les audits du dépôt ;
7. seulement ensuite mettre à jour les statuts canoniques `DONE/FRONTIER`.

Tant que cette étape n'est pas faite, la PR #60 représente une architecture
mathématique avancée, pas un certificat machine accepté.

## B. Fermer le Hessien Candidate-A pointwise

Les interfaces de la PR réduisent le contenu irréductible aux preuves suivantes.

### B1. Décomposition physique unique

Construire réellement l'isométrie de complétion cinq-secteurs et prouver son
accord sur le cœur lisse avec :

```text
métrique/difféomorphisme
U(1)²
matière SpinC primitive
longitudinal/LL
bord/finite-BV.
```

### B2. Générateurs exacts de symétrie

Écrire les vrais générateurs finis et prouver, pour la même action :

```text
S(x + t v) = S(x)
```

ou la version par flot non linéaire. Il faut couvrir les neuf blocs, pas
seulement le secteur Maxwell déjà fermé.

### B3. Commutation des projecteurs

Démontrer les identités projetées hors diagonale donnant

```text
H P_s = P_s H.
```

C'est ce qui permet aux cinq projecteurs de préserver le noyau réel et son
orthogonal.

### B4. Estimations elliptiques

Prouver sur les cinq secteurs du vrai complément :

```text
c_s ‖P_s x‖² ≤ ⟪A_red P_s x, P_s x⟫,
```

puis la borne unique

```text
‖A_red - Σ_s P_s A_red P_s‖ < c_floor.
```

### B5. Petitesse physique H11

Fermer l'inégalité explicite provenant du pont cœur-dense/chart :

```text
C_H11 < c_floor - ‖A_off‖.
```

### B6. Complétude du noyau nommé

Prouver que les générateurs physiques forment une base de `ker H`, donc qu'il
n'existe aucun mode caché.

### B7. Domaine maximal concret

Instancier les gates micro-globales avec les vrais opérateurs Candidate-A :

* densité du cœur commun ;
* fermeture graphique simultanée ;
* conservation de la trace SpinC ;
* annulation des défauts de Green/bord ;
* unicité du domaine fermé maximal.

## C. Fermer BRST-GLOBAL-01 dans toute sa portée géométrique

Le BRST actuel est une frontier réduite. Restent notamment :

1. la différentiabilité en paramètre des pullbacks tensoriels de gorge ;
2. la chain rule du pairing tensoriel intégré ;
3. les identités de skew-adjonction intégrée ;
4. les duals géométriques/intégrés Maxwell, métriques et bord ;
5. l'entrelacement coadjoint fidèle ;
6. le flot Candidate-A concret à mesure fixe pour tous les neuf blocs ;
7. l'identification entre la différentielle BRST géométrique, les symétries de
   l'action et les zéro-modes du même Hessien ;
8. le traitement global des secteurs SpinC, LL, null/finite-BV et antifields.

La fermeture BRST doit ensuite être reliée à la réduction du noyau et non
juxtaposée comme un certificat indépendant.

## D. Fermer ADM-GLOBAL-01 et exclure le mode de Boulware--Deser

La route ADM est encore réduite à FLRW. Il manque :

1. une décomposition 3+1 covariante des deux métriques ;
2. lapses **et shifts**, avec dérivées spatiales ;
3. les moments canoniques complets ;
4. toutes les contraintes primaires et secondaires ;
5. leur algèbre fonctionnelle de Poisson ;
6. la stabilité du rang sur l'espace de phase physique ;
7. la classification première/seconde classe ;
8. le comptage global des degrés de liberté ;
9. l'exclusion explicite du mode BD ;
10. le raccord des conditions de gorge, matière, LL et bord.

Sans cette étape, le bon comportement du témoin FLRW ne constitue pas une
preuve de consistance hamiltonienne générale.

## E. Fermer STABILITY-GLOBAL-01

La stabilité réduite doit être étendue à :

1. l'espace contraint après quotient ADM/BRST ;
2. tous les modes tensoriels, vectoriels et scalaires ;
3. les deux secteurs métriques et la matière SpinC ;
4. Maxwell, LL, gorge et termes de bord ;
5. les branches non proportionnelles ;
6. les limites faible champ et quasi-statique ;
7. les paramètres PPN et la limite newtonienne ;
8. les bornes d'énergie/non-croissance appropriées ;
9. la stabilité sous perturbations des données et des couplages ;
10. l'absence d'instabilités spectrales et de gradients dans le domaine
    physique.

Le gap du Hessien sur `(ker H)ᗮ` est une brique importante, mais il ne remplace
pas le quotient complet par les contraintes hamiltoniennes.

## F. Fermer la famille d'indices et Quillen

La PR a écrit les interfaces, mais il reste à construire les objets analytiques
réels :

1. une vraie famille de configurations Candidate-A et de Hessiennes `H_a` ;
2. l'auto-adjonction pour tout `a` ;
3. les trivialisations unitaires
   `T_a : (ker H_0)ᗮ ≃L (ker H_a)ᗮ` ;
4. un gap réduit uniforme ;
5. la différentiabilité de la famille transportée ;
6. la preuve de `G' = -G H' G` dans cette famille ;
7. la nucléarité/trace intrinsèque de chaque `G_a H'_a` relatif ;
8. les asymptotiques petit temps et l'intégrabilité grand temps ;
9. la continuation Mellin uniforme ;
10. les opérateurs de référence correspondant aux vraies coupures spectrales ;
11. l'indépendance de référence et le cocycle analytique ;
12. l'identification avec la connexion géométrique de Bismut--Freed ;
13. la formule locale de courbure de l'indice familial ;
14. la régularité de la base finie des noyaux ;
15. la complexification/tensorisation finale de
    `Hom(det coker, det ker)` avec la coordonnée zêta réduite.

## G. Fermer l'anomalie continue

Les résultats d'anomalie actuels donnent des modèles finis et des filtres de
consistance, mais il reste :

1. l'anomalie de la famille d'opérateurs Janus continue ;
2. les densités locales de l'indice et leur descente globale ;
3. les contributions de bord/eta/joints ;
4. la compatibilité Pin⁻/SpinC et PT ;
5. le calcul de la phase globale et des transformations de grande jauge ;
6. la comparaison avec la ligne Quillen construite par la famille réelle ;
7. la démonstration qu'aucune anomalie résiduelle n'invalide les symétries
   nécessaires à la réduction BRST/Hessien.

L'annulation d'anomalie reste un filtre de cohérence ; elle ne sélectionne pas
à elle seule les coefficients parity-even de Candidate-A.

## H. Construire un atlas variationnel réellement global

`EULER` et `HELMHOLTZ` sont fermés sur les cartes régulières communes. Il reste
à :

1. couvrir toute la strate physique régulière par des cartes normées
   compatibles ;
2. prouver les lois de transition et l'indépendance de carte des dérivées ;
3. traiter ou exclure proprement les strates où la racine/Sylvester devient
   singulière ;
4. relier le tangent géométrique brut au cœur analytique et aux complétions ;
5. prouver la régularité `C²` jointe des neuf blocs sur cet atlas ;
6. raccorder le domaine maximal fermé aux cartes locales.

## I. Sélection physique des coefficients et de la branche

Un résultat fondamental du programme est négatif : géométrie des modules,
naturalité, Helmholtz et annulation d'anomalie ne déterminent pas seuls une
action unique. Il reste donc à spécifier une source de sélection physique :

* réduction d'une théorie parente ;
* conditions de normalisation/renormalisation ;
* principe de positivité ou d'unitarité ;
* symétries discrètes supplémentaires ;
* conditions de vide et de limite GR ;
* critères expérimentaux explicitement séparés de la reconstruction
  mathématique.

Il faut ensuite :

1. déterminer la région non dégénérée des couplages ;
2. prouver que les hypothèses de coercivité et de petitesse y sont satisfaites ;
3. sélectionner les branches de racine et de vide admissibles ;
4. montrer que les contre-termes finis ne réintroduisent pas une ambiguïté
   physique non contrôlée ;
5. établir si la théorie obtenue est unique relativement à ces données, ou
   classifier honnêtement la famille résiduelle.

## J. Validation phénoménologique

Après la fermeture structurelle, il restera à relier Candidate-A à des
observables :

1. solutions de fond et cosmologie ;
2. perturbations linéaires complètes ;
3. limite newtonienne et PPN ;
4. propagation des ondes et causalité ;
5. spectre de masse et couplages matière ;
6. conditions aux gorges et effets de bord ;
7. contraintes observationnelles ;
8. comparaison contrôlée à GR et aux théories bimétriques usuelles.

Ces calculs ne doivent pas être utilisés rétroactivement comme axiomes pour
forcer la fermeture mathématique.

## 4. Ordre de travail recommandé

### Priorité 0 — confiance machine

```text
élaborer la PR #60
→ build complet
→ audit axiomes/sorry
→ raccord des façades publiques.
```

### Priorité 1 — pointwise physique

```text
B1 décomposition cinq-secteurs
→ B2 symétries exactes
→ B3 commutation
→ B4 estimations principales
→ B5 petitesse H11
→ B6 noyau complet
→ B7 domaine maximal.
```

Cette séquence ferme réellement `HESSIAN-GLOBAL-01` et `MICRO-GLOBAL-01` à la
portée Candidate-A.

### Priorité 2 — cohérence de jauge et hamiltonienne

```text
BRST complet
+ ADM covariant
+ exclusion BD.
```

### Priorité 3 — stabilité physique

```text
quotient contraint
→ tous les modes
→ faible champ/PPN
→ stabilité spectrale et énergétique.
```

### Priorité 4 — famille d'indices et anomalie

```text
famille H_a réelle
→ traces relatives
→ Mellin uniforme
→ Bismut--Freed
→ ligne complexe
→ anomalie continue.
```

### Priorité 5 — sélection et phénoménologie

```text
sélection des couplages/branches
→ solutions physiques
→ prédictions et comparaison expérimentale.
```

## 5. Critère de « fin du programme P »

Un terminal honnête ne doit pas seulement dire qu'une grande structure Lean
est habitée. Il doit fournir, pour une Candidate-A explicitement choisie :

```text
1. une action globale bien définie ;
2. son Euler et son Helmholtz global ;
3. ses symétries BRST/difféomorphes réelles ;
4. son système ADM sans mode BD ;
5. un Hessien fermé/Fredholm sur le quotient physique ;
6. son noyau exact et son Green réduit ;
7. une région de couplages stable ;
8. une famille d'indices/ligne Quillen/anomalie cohérente ;
9. une limite GR et des observables calculables ;
10. une déclaration claire de ce qui sélectionne — ou ne sélectionne pas — les
    coefficients physiques.
```

La PR #60 rapproche fortement les points 5, 6 et 8 au niveau architectural.
Les verrous dominants du programme complet restent les preuves elliptiques
concrètes, BRST/ADM, stabilité tous modes, famille d'indices analytique réelle,
et sélection physique des couplages.
