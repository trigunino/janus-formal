# Programme P — bilan du reste à faire après la PR #60

Date de référence : 2026-08-13.

## 1. Règle de lecture

Ce document distingue trois niveaux qui ne doivent pas être confondus :

1. les infrastructures globales ou sectorielles déjà construites ;
2. les frontiers qui réduisent une conclusion à des entrées mathématiques
   explicites ;
3. les quatorze portes terminales du registre canonique.

La PR #60 poursuit volontairement l'architecture avant le nettoyage final de
l'élaboration Lean. Elle ne revendique donc ni build vert ni fermeture d'une
porte terminale.

Le compteur officiel demeure :

```text
0 / 14 portes terminales.
```

Une porte ne peut être cochée qu'après construction de ses objets concrets,
compilation de son gate, intégration à la façade, audit et contrôle des axiomes.
Une structure `Prop` habitée par des hypothèses reproduisant la conclusion ne
constitue pas une fermeture.

## 2. Socle global déjà construit

Le registre opérationnel marque comme `DONE`, à leurs portées exactes :

```text
GEO-GLOBAL-01
FIELD-GLOBAL-01
ANALYSIS-GLOBAL-01
BOUNDARY-GLOBAL-01
KJ-GLOBAL-01
KJ-GLOBAL-02
NATURAL-GLOBAL-01
ACTION-GLOBAL-01
EULER-GLOBAL-01             chartwise
NOETHER-GLOBAL-01           physique U(1)^2
HELMHOLTZ-GLOBAL-01         chartwise
VARCOH-GLOBAL-01            cohomologie fonctionnelle globale
DIRAC-GLOBAL-01
```

Cela fournit notamment :

- la géométrie effective et les deux métriques Candidate A sur un tangent
  commun ;
- l'espace de champs physique D10-free et l'espace étendu séparé du
  régulateur ;
- les domaines Sobolev/trace/bord disponibles ;
- l'action Candidate A assemblée sur son domaine régulier ;
- ses neuf blocs locaux `C²` dans toute carte régulière fournie ;
- le véritable Euler chartwise, le Helmholtz chartwise et la reconstruction
  radiale normalisée ;
- la classification naturelle finie actuelle ;
- le Dirac SpinC global, son domaine maximal, sa tour spectrale géométrique et
  son Fredholm d'indice zéro.

Ces résultats sont substantiels, mais plusieurs ont une portée plus faible que
la porte terminale correspondante. En particulier :

- `EULER-GLOBAL-01` ne construit pas encore un atlas normé couvrant toutes les
  valeurs brutes du tangent global ;
- `HELMHOLTZ-GLOBAL-01` est une reconstruction sur les cartes régulières, pas
  le théorème local complet du bicomplexe variationnel ;
- `VARCOH-GLOBAL-01` concerne les fonctionnelles globales chartwise, pas la
  cohomologie horizontale locale des densités de jets ;
- `DIRAC-GLOBAL-01` ferme le Dirac physique, pas son identification automatique
  avec le Hessien complet Candidate A.

## 3. Ce que la PR #60 ajoute réellement

La route préférée de la PR #60 part du vrai Hessien de la même action et garde
le vrai noyau tout au long de la construction.

### 3.1 H10--H14 pointwise

Elle construit les interfaces et conséquences suivantes :

```text
une seule décomposition Hilbert cinq secteurs
→ projecteurs orthogonaux sur l'espace complet
→ restriction canonique à (ker H)ᗮ
→ générateurs issus de l'invariance de la même action
→ opérateur principal réduit A_red
→ cinq blocs diagonaux + un unique A_off
→ petitesse H11 explicite
→ gap positif sur le vrai complément du noyau
→ portée fermée, Fredholm, indice zéro
→ Green réduit, résolvante et stabilité
→ noyau nommé une fois une base identifiée.
```

### 3.2 Trace et déterminant relatifs

La PR évite d'appeler « chaleur nucléaire » l'exponentielle inversible d'un
opérateur borné en dimension infinie. Elle utilise à la place :

```text
exp(-t H_red) - exp(-t H_ref).
```

Elle sépare :

- l'expansion sommable de rang un ;
- l'indépendance de présentation de sa trace ;
- la partie finie petit temps/grand temps ;
- la représentation de Mellin normalisée par Gamma ;
- la continuation zêta ;
- la phase et la métrique de Quillen.

### 3.3 Famille d'indices

La branche contient maintenant la route :

```text
H_a sur l'espace Candidate A complet
→ vrais compléments (ker H_a)ᗮ
→ trivialisation unitaire vers (ker H_0)ᗮ
→ famille réduite uniformément gappée
→ G'_a = -G_a H'_a G_a
→ trace intrinsèque Tr(G_a H'_a)
→ connexion relative de Bismut--Freed
→ références locales et atlas de coupures spectrales
→ clutching et holonomie.
```

### 3.4 Noyaux finis et vraie ligne de Fredholm

Un même type fini `ZeroMode` indexe une base de chaque noyau. Le transport à
coordonnées constantes donne :

```text
ker H_a ≃ ker H_b
finrank ker H_a = card ZeroMode
multiplicités des cinq secteurs constantes.
```

La puissance extérieure maximale construit la ligne du noyau et son volume
nommé non nul. La self-adjonction et le gap donnent en plus :

```text
range H_a = (ker H_a)ᗮ
coker H_a = E / range H_a ≃ ker H_a.
```

La branche construit donc désormais la véritable fibre réelle de Fredholm :

```text
Det_Fred(H_a) = Hom(det coker H_a, det ker H_a).
```

Elle prouve :

- que les puissances extérieures du noyau et du conoyau sont de dimension un ;
- que chaque fibre de Fredholm est de dimension un ;
- que le transport des bases nommées induit de vraies équivalences entre les
  fibres ;
- que la frame Fredholm canonique est non nulle ;
- que le volume nommé du conoyau, tiré en arrière par `coker ≃ ker`, est non
  nul ;
- que la frame canonique envoie exactement ce volume du conoyau vers le volume
  nommé du noyau.

Le déterminant zêta du complément est ensuite joint à cette normalisation dans
un atlas de coordonnées complexes :

```text
D_i(a) = k_i(a) det_zeta,red(a)
g_ij(a) = k_j(a) / k_i(a)
A_i = A_red - k_i'/k_i.
```

Les lois de cocycle, de recollement, de parallélisme et de changement de jauge
sont dérivées. Dans le repère canonique nommé `k = 1`, la coordonnée complète
est exactement le déterminant zêta réduit et la connexion complète est la même
connexion zêta.

Ce qui reste séparé est plus précis qu'avant : il ne s'agit plus de construire
la ligne réelle de Fredholm, qui existe désormais, mais d'identifier sa
complexification/tensorisation avec la ligne analytique de Quillen et d'y
transporter la métrique, la connexion et la section zêta.

## 4. État des grands frontiers non terminaux

### ADM

Le secteur FLRW réduit possède Legendre, contraintes primaires, contrainte
secondaire, préservation et rang local ouvert. Il manque :

- les shifts et dérivées spatiales ;
- l'algèbre fonctionnelle complète des contraintes ;
- le rang global ;
- l'exclusion du mode de Boulware--Deser ;
- le raccord aux champs, à la matière et au bord complets.

### Stabilité et vide

La distinction entre Hessienne ambiante et variations contraintes est établie
sur les réductions actuelles. Il manque :

- la réduction sur le quotient ADM/BRST véritable ;
- tous les modes et toutes les espèces ;
- les conditions de bord ;
- la limite faible/PPN ;
- l'unicité d'un vide global stable.

### BRST

Le carré nul et une grande partie des actions Cartan, pairings et dualités sont
construits. Il manque notamment :

- l'habitant géométrique complet du flot neuf blocs ;
- la différentiation des pullbacks tensoriels nécessaire aux identités
  intégrées de skew-adjonction ;
- le choix physique de l'unique combinaison difféomorphe des deux conditions
  de de Donder Candidate A ;
- la réalisation elliptique auxiliaire cohérente des opérateurs FP lorentziens ;
- l'identification de son domaine avec celui du Hessien total.

### Hessien/Fredholm

La PR #60 rend la dépendance logique beaucoup plus précise, mais il manque les
habitants analytiques concrets :

1. l'isométrie physique cinq secteurs et son accord sur le cœur dense ;
2. les générateurs exacts des cinq secteurs et l'invariance locale de l'action ;
3. la commutation des projecteurs avec le Hessien complet ;
4. les cinq estimations diagonales de coercivité ;
5. la borne stricte sur l'unique reste hors diagonale ;
6. la petitesse H11 issue de la vraie estimation cœur-vers-carte ;
7. la preuve que les générateurs forment toute la base du noyau ;
8. l'identification au véritable opérateur elliptique non borné et à sa
   réalisation maximale ;
9. les constructions nucléaires relatives et leurs estimations uniformes ;
10. la famille Candidate A concrète et son calcul de Bismut--Freed ;
11. la complexification de la vraie ligne de Fredholm et son identification à
    la ligne analytique de Quillen.

### Quillen et anomalie

Les modèles de ligne, métrique, connexion, atlas et holonomie sont présents.
La vraie ligne algébrique de Fredholm et sa frame normalisée sont également
présentes. Il manque :

- la construction des références correspondant aux vraies coupures spectrales ;
- les asymptotiques uniformes de chaleur ;
- la comparaison zêta/trace logarithmique ;
- la formule locale d'indice des familles ;
- l'application des contraintes d'anomalie au contenu de champs Candidate A
  complet ;
- la complexification de `Hom(det coker, det ker)` et l'accord de cette ligne
  avec la ligne de Quillen, sa métrique, sa connexion et sa section.

### Régulateur

Un régulateur nucléaire global de référence existe. Il n'est pas encore prouvé
qu'il est la fonction spectrale du Hessien physique ou une référence relative
compatible avec lui.

### Micro, schéma et échelle

Les résultats actuels comprennent des no-go importants :

- deux parents différents peuvent produire les mêmes données réduites utiles ;
- les hypothèses actuelles ne sélectionnent pas l'action ni ses normalisations ;
- deux libertés de schéma de contre-termes restent effectives ;
- toutes les lois actuellement disponibles sont covariantes sous une même
  dilatation.

Par conséquent, `MICRO-GLOBAL-01`, la fixation de schéma et
`SCALE-GLOBAL-01` requièrent une donnée physique nouvelle. Ils ne peuvent pas
être fermés honnêtement par un choix arbitraire de constantes.

## 5. Les quatorze portes terminales

### T01 — fondations communes compilées

**Déjà disponible :** la majorité des objets globaux et pairings.

**Reste :** produire un certificat unique, typé et compilé sur les mêmes objets
communs après intégration de la branche actuelle, avec façade, audit et axiomes
contrôlés.

### T02 — `invariantLocalFunctionalBasisClassified`

**Déjà disponible :** classificateur naturel fini fidèle et troncature EFT à
six invariants.

**Reste :** classification complète de la base fonctionnelle locale admissible,
sur les jets structurés physiques, avec dépendances de dérivées, stratification
d'isotropie et preuve d'exhaustion.

### T03 — `fullEulerLagrangeOperatorDerived`

**Déjà disponible :** véritable Euler des neuf blocs sur toute carte régulière
commune fournie.

**Reste :** atlas physique couvrant le tangent brut, système local par
composantes, opérateur global recollé, domaines et termes de bord cohérents.

### T04 — `nonlinearHelmholtzConditionsProved`

**Déjà disponible :** Helmholtz chartwise par symétrie du vrai Jacobien et
reconstruction radiale.

**Reste :** conditions locales non linéaires complètes sur le jet PDE global,
y compris les directions de jauge, de métrique, de bord et les dépendances de
haut ordre.

### T05 — `variationalBicomplexObstructionVanishing`

**Déjà disponible :** obstruction fonctionnelle globale nulle sur les cartes.

**Reste :** construire le bicomplexe variationnel horizontal/contact des
densités locales de jets et démontrer la nullité de la classe d'obstruction
physique.

### T06 — `nullLagrangiansAndBoundaryTermsClassified`

**Déjà disponible :** plusieurs transgressions, GHY, faces nulles, joints et
résidus de bord explicites.

**Reste :** théorème d'exhaustion des lagrangiens nuls et des termes de bord
admissibles, compatible avec la gorge non orientable, les joints, le BRST et le
bicomplexe local.

### T07 — `anomalyConstraintsApplied`

**Déjà disponible :** modèles d'annulation PT, déterminants, vraie ligne de
Fredholm, ligne/atlas Quillen et frontiers d'anomalie.

**Reste :** appliquer le calcul d'anomalie continu au contenu de champs complet,
aux vraies classes caractéristiques et à la famille physique, puis déduire les
contraintes discrètes autorisées.

### T08 — `parentBulkOrMicroscopicSelectionPrincipleDerived`

**Déjà disponible :** réduction de Schur/Calderón abstraite et plusieurs no-go
de non-unicité.

**Reste :** dériver un parent bulk/jonction ou une loi microscopique concrète
qui sélectionne l'action Candidate A. Les hypothèses actuelles sont
insuffisantes par théorème, pas seulement par manque de Lean.

### T09 — `actionNormalizationDerived`

**Déjà disponible :** reconstruction d'une action normalisée une fois les
normalisations et une valeur de référence fournies.

**Reste :** dériver les constantes de normalisation depuis le parent ou la loi
microscopique, sans ajustement à la cible phénoménologique.

### T10 — `finiteCountertermsFixedMicroscopically`

**Déjà disponible :** classification de plusieurs ambiguïtés et no-go de
liberté de schéma.

**Reste :** donnée microscopique ou principe de renormalisation indépendant
fixant les parties finies. Cette porte ne suit pas des hypothèses actuelles.

### T11 — `globalActionClassReconstructed`

**Déjà disponible :** une action Candidate A explicite sur le domaine régulier
et une reconstruction chartwise depuis son Euler.

**Reste :** montrer qu'elle est la classe globale sélectionnée par T02--T10,
avec tous les overlaps, lagrangiens nuls, normalisations et contre-termes fixés.

### T12 — `hessianMatchesNaturalFredholmFamily`

**Déjà disponible :** la plus grande partie de l'architecture dans la PR #60,
le Dirac/Fredholm/régulateur global existant, la vraie ligne de Fredholm de la
famille et sa frame normalisée.

**Reste :** habiter les onze entrées analytiques listées plus haut, prouver
l'accord avec l'opérateur elliptique naturel non borné, identifier la ligne
complexifiée à la ligne de Quillen, puis compiler et auditer le gate terminal.
C'est la porte aujourd'hui la plus avancée architecturalement, mais elle n'est
pas fermée.

### T13 — `uniqueStableVacuumDerived`

**Déjà disponible :** stabilité de sous-secteurs, no-go de minimum strict dans
le témoin poussière et diagnostics FLRW.

**Reste :** réduction complète des contraintes, absence BD, spectre physique de
tous les modes, contrôle matière/bord et preuve d'existence puis d'unicité du
vide.

### T14 — `absoluteScaleDerivedNoFit`

**Déjà disponible :** no-go de covariance d'échelle et plusieurs relations
sans dimension.

**Reste :** une donnée dimensionnée indépendante issue du microscopique, puis
un vide stable qui la convertit en échelle physique absolue. Sans cette entrée,
la porte est bloquée par le no-go actuel.

## 6. Lecture par sous-programme P0, P-A à P-F

### P0

Le rôle no-go est largement rempli : géométrie de moduli, Hessien réduit,
anomalie ou données de branche ne sélectionnent pas seuls une action.

**Reste :** utiliser ces no-go comme contraintes de conception, non chercher à
les « fermer » par un choix conventionnel.

### P-A

Les propriétés universelles relatives et réductions parentales sont solides
aux niveaux finis et abstraits.

**Reste :** construire le véritable parent bulk/jonction et son problème de
bord ; c'est le cœur de T08--T10.

### P-B

L'anomalie est séparée correctement de la sélection parity-even.

**Reste :** calcul continu sur la famille physique complète, classes globales,
indice des familles et application effective des contraintes — T07.

### P-C

La reconstruction Helmholtz sur espaces de configurations et cartes régulières
est avancée.

**Reste :** le problème inverse local PDE complet : T03--T06.

### P-D

Les modules de coefficients invariants et plusieurs classifications finies sont
construits.

**Reste :** exhaustion de la base locale physique et sélection/normalisation
des coefficients survivants — T02, T09 et T11.

### P-E

Jets, frames adaptées, cocycles, lifts SpinC/Pin et beaucoup de géométrie
locale/globale sont construits.

**Reste :** groupoïde structuré physique complet, preuve Peetre--Slovák de
localité/régularité, réalisation holonome/surjectivité, classification des
évaluateurs lisses et test elliptique séparé.

### P-F

Le pullback d'un Hessien cible par une application de compatibilité est traité
abstraitement, avec Helmholtz et Noether.

**Reste :** le complexe non linéaire Janus concret, son opérateur PDE, sa
réalisation sur les vrais bundles et son raccord à l'action sélectionnée.

## 7. Chemin critique recommandé

### Phase 0 — intégration formelle de la PR #60

Ce n'est pas une porte scientifique, mais c'est une condition de confiance :

1. corriger l'élaboration fichier par fichier ;
2. retirer les doublons de frontiers historiques ;
3. importer uniquement la route préférée dans la façade ;
4. vérifier `#print axioms` ;
5. remettre l'audit terminal à jour.

### Phase 1 — fermeture concrète de T12

Ordre conseillé :

```text
isométrie cinq secteurs
→ générateurs exacts
→ commutation
→ coercivités diagonales
→ borne A_off
→ petitesse H11
→ base exacte du noyau
→ réalisation non bornée/Fredholm
→ trace relative et famille d'indice
→ complexification et accord Quillen de la ligne de Fredholm.
```

### Phase 2 — T03 à T06

Construire l'atlas brut du tangent, le système Euler local complet, le
bicomplexe variationnel et la classification exhaustive des bords.

### Phase 3 — T02, T07 et T11

Fermer la classification fonctionnelle, appliquer les anomalies, puis
reconstruire la classe globale admissible.

### Phase 4 — T08 à T10

Introduire et dériver la donnée parentale/microscopique réellement nouvelle.
Sans cette phase, normalisation et parties finies restent indéterminées.

### Phase 5 — T13 puis T14

Fermer ADM/BD et la stabilité de tous les modes, sélectionner le vide, puis
seulement dériver une échelle absolue à partir de l'entrée microscopique
dimensionnée.

## 8. Conclusion

Programme P n'est pas « presque fini » au sens des quatorze portes : le
compteur officiel reste `0/14`.

Il est en revanche très avancé au niveau de l'infrastructure : géométrie,
champs, action régulière, Dirac, Euler/Helmholtz chartwise et une architecture
Hessien--Fredholm--Quillen particulièrement développée, incluant désormais la
vraie ligne réelle de Fredholm de la famille.

La difficulté résiduelle n'est plus principalement l'absence de wrappers. Elle
se concentre sur trois noyaux scientifiques :

```text
1. globaliser le calcul variationnel local et son bicomplexe ;
2. habiter les estimations analytiques du Hessien/Fredholm physique et
   identifier sa ligne complexifiée à la ligne de Quillen ;
3. fournir la loi microscopique qui sélectionne normalisations, schéma, vide et
   échelle absolue.
```

La PR #60 attaque fortement le deuxième noyau. Elle ne remplace pas les premier
et troisième noyaux, et ne ferme aucune porte tant que les habitants concrets,
la compilation et l'audit ne sont pas obtenus.
