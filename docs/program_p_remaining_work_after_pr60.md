# Programme P — bilan du reste à faire après la PR #60

Date de référence : 2026-09-10.

## 1. Règle de lecture

Ce document distingue trois niveaux qui ne doivent pas être confondus :

1. les infrastructures globales ou sectorielles déjà construites ;
2. les frontiers qui réduisent une conclusion à des entrées mathématiques
   explicites ;
3. les quatorze portes terminales du registre canonique.

La PR #60 poursuivait volontairement l'architecture avant le nettoyage final
de l'élaboration Lean et ne fermait alors aucune porte terminale. `T01`–`T05`
ont depuis été fermées séparément ; `T06`–`T14` restent ouvertes.

Le compteur officiel demeure :

```text
5 / 14 portes terminales.
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
- `HELMHOLTZ-GLOBAL-01` ferme désormais le critère terminal fonctionnel global
  et chartwise de `T04` ; la représentation PDE locale métrique/GHY reste un
  suivi plus fort hors de ce critère ;
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

**Fermé le 2026-08-26 :**
`program_p_t01_global_foundations_pairings_terminal_gate` assemble sur un même
cœur global la métrique partagée, l'injectivité tangente, le pairing L2 positif
non dégénéré et l'inclusion dense injective dans sa complétion intrinsèque. Le
gate, son `.olean`, son import de façade et l'audit `1/14` sont verts ; les seuls
axiomes rapportés sont `propext`, `Classical.choice` et `Quot.sound`.

### T02 — `invariantLocalFunctionalBasisClassified`

**Déjà disponible :** classificateur naturel fini fidèle, troncature EFT à
six invariants, carrier local d'ordre deux séparant honnêtement les strates
physiques bulk et gorge, constructeur générique `C²` en carte fixe, extraction
réelle des jets SpinC primitifs et des trois champs LL depuis une configuration
gauge-fixée et paquet combiné de gorge, jets réels des deux métriques bulk et
induites de gorge, cœur bulk réel Christoffel/`U(1)²`, tous les slots
nonminimaux typés du carrier (neuf jets après expansion sectorielle), puis
assemblage du vrai carrier bulk sous une réalisation régulière compatible,
une carte et une donnée normale externe explicites. Les potentiels `U(1)²`
sectorisés réels de gorge fournissent le slot gauge exact en `EuclideanR3`.
Leur expansion finie reconstruit exactement le covecteur intrinsèque sur le
`baseSet` de la trivialisation tangente centrée et, pour Candidate-A, coïncide
avec l'expression en coordonnées du repère centré du pullback bulk ambiant en
tout point de ce domaine, après composition par l'inverse de la trivialisation
tangente. Deux repères tangents
centrés vérifient la loi contragrédiente exacte d'ordre zéro sur leur
intersection. Les transitions tangentes sont l'identité à ancre répétée,
s'inversent par échange des ancres et vérifient le cocycle exact sur les triples
intersections ; leurs transports covectoriels vérifient le cocycle dual
correspondant. La transition et son inverse varient `C∞` sur chaque overlap
comme applications linéaires continues. Les coefficients et covecteurs
reconstruits sont `C∞` sur chaque `baseSet` centré entier, et l'action duale est
`C∞` sur le double overlap. Après transport du premier représentant, celui-ci
et le second admettent exactement les mêmes certificats
`HasMFDerivWithinAt` pour toute dérivée première candidate. Cela reste une
congruence dans l'overlap. Dans la carte étendue centrée au point commun, la
formule de Leibniz explicite
`dC₂ = D₁₂ ∘ dC₁ + (dD₁₂) · C₁` est désormais prouvée. Elle reste
une loi de premier ordre dans une carte de base fixée, sans descente intrinsèque
des jets entre cartes. Un carrier local à deux paramètres sépare désormais
l'ancre du repère du centre de carte, coïncide exactement avec l'extracteur
Candidate-A historique sur la diagonale et porte cette loi dans son vrai champ
`firstDerivative`. Un lemme générique de Leibniz pour l'application d'une
famille d'opérateurs linéaires est ensuite différentié deux fois. Le vrai champ
`secondDerivative` satisfait donc la loi à quatre termes : transport de
`D²C₁`, deux termes mixtes et `D²D₁₂·C₁`. Cette loi est aussi transportée dans
le carrier physique exact `EuclideanR3`. À repère tangent fixé, la transition
réelle entre deux cartes étendues est `C²`, identifie les représentants comme
germes et donne les règles de chaîne exactes d'ordres un et deux dans un jet à
trois paramètres, y compris le Hessien de la transition de carte.
Les jets des transitions de cartes satisfont désormais le cocycle exact des
Jacobiennes et Hessiennes sur les triples overlaps. Une synthèse à carte source
centrée combine ensuite changement de repère et changement de carte aux ordres
un et deux ; la loi à trois paramètres est aussi transportée dans le carrier
physique `EuclideanR3`.
Sous `HasNoTangentialRadical` sectoriel, le jet métrique induit réel fournit un
candidat de Koszul ponctuel. La symétrie de sa dérivée transportée brute dans
les slots métriques, l'égalité de sa symétrisation explicite avec cette dérivée
brute et l'identité de Koszul brute sont prouvées. Le cœur gorge combine ces
slots tangentiel et gauge réels ; l'assemblage raffiné du vrai carrier gorge
n'externalise plus que `normalQuadratic`, sa symétrie et `physicalNormal`.
L'ancien assemblage à background entièrement externe reste compilé comme gate
historique. Le quotient projeté `(II, F)` possède aussi son orbite résiduelle
repère--SpinC et la réduction unique des évaluateurs invariants. Ces cent dix
gates de support restent non terminales et ne changent pas le compteur `1/14`.

Les présentations locales repère--carte d'un jet gauge arbitraire possèdent
maintenant la relation directe exacte valeur/Jacobienne/Hessienne et le `Setoid`
explicitement engendré par cette relation. Tous les jets gauge réels extraits
sont directement compatibles et définissent donc une classe canonique
indépendante de la présentation dans le quotient ponctuel. La relation engendrée
est maintenant prouvée égale à la relation directe, elle-même réflexive,
symétrique et transitive aux ordres zéro, un et deux. Le carrier brut est
désormais normé et de dimension finie ; ses transports semi-directs forment un
`VectorBundleCore` lisse sur l'atlas ouvert repère--carte. Le quotient ponctuel
s'identifie aux fibres de ce bundle, et les jets gauge `U(1)²` réels descendent
en une section globale `C∞`.

Les huit gates 68--75 ajoutent le core de bundle de seconds jets à
fibre fixe, deux critères génériques de recollement de sections et l'overlap
exact de tout `SmoothThroatField` de dimension finie. Les trois champs LL
descendent ainsi en sections globales `C∞` de bundles de seconds jets séparés,
avec valeurs d'ordre zéro exactes. Les dix-sept gates 76--92 complètent ensuite
les jets métriques covariants : extraction repère--carte arbitraire, overlaps et
cocycles aux ordres un/deux, transport semi-direct en groupoïde, bundle
vectoriel lisse et sections globales `C∞` des deux métriques induites. Les
dix-huit gates 93--110 (un critère générique et dix-sept gates SpinC) ferment à
leur tour l'extraction en trivialisation/carte arbitraire, les overlaps et
cocycles aux ordres zéro, un et deux, le transport semi-direct en groupoïde, le
`SmoothVectorBundleCore` et les sections globales `C∞` SpinC génériques et
physiques. Reste le bundle physique commun avec background et géométrie normale.

**Reste :** classification complète de la base fonctionnelle locale admissible,
avec extraction géométrique des formes normales/coordonnées normales au lieu du
contrat externe, décharge intrinsèque de la transversalité, construction d'une
connexion de Levi--Civita globale, assemblage des bundles lisses déjà séparés
avec les slots background et normal du carrier physique commun, action
deck/SpinC/jauge,
dépendances de dérivées, stratification
d'isotropie et preuve d'exhaustion.

### T03 — `fullEulerLagrangeOperatorDerived`

**Fermé le 2026-09-09 :** Gate 812 assemble le certificat Euler global typé
sur le carrier couplé full-BRST et son atlas couvert exact.

### T04 — `nonlinearHelmholtzConditionsProved`

**Déjà disponible :** Helmholtz chartwise par symétrie du vrai Jacobien et
reconstruction radiale. Les Gates 813, 816 et 817 ajoutent le tour de jets
multi-indices fini, le Helmholtz fonctionnel `C²` sur le domaine et l'atlas
exacts de T03, ainsi que les quatre restrictions physiques exactes ; le bloc LL
possède son système fort sur les relèvements lisses et la normalisation nulle
est exactement indépendante de l'action. Gate 818 construit les résidus Riesz
primaux des blocs position nulle et intrinsèque nulle, leur séparation pointwise
et leurs identités de Helmholtz propres et croisées. Gate 820 décompose
exactement l'Euler métrique–bord de `T03`, sur le graphe de raccord métrique et
le domaine admissible, en contributions old physique/Maxwell/SpinC et GHY
mobile. Gate 822 représente leur somme contrainte par un résidu Riesz primal
sur un graphe scalaire Hilbert fermé. Gate 825 factorise les trois résidus nuls
de T03 dans un 0-jet fini explicite, avec normalisation null/joint nulle. Gate
831 assemble ces blocs avec LL en un système exactement équivalent à l'Euler
T03 admissible, et remplace LL par ses trois équations fortes sur les
relèvements lisses. Gate 832 donne simultanément les dix réciprocités propres
et croisées en restreignant le Jacobien de Helmholtz exact aux quatre
injections physiques. Gate 837 extrait les vrais 2-jets joints de l'embedding
fidèle et de chaque coefficient des métriques ambiante et d'écran au composant
nul T03, puis identifie l'Euler fidèle et les pairings Riesz nuls au `fderiv`
de l'action géométrique. Gate 838 factorise les densités de faces et de joints
par les valeurs de ces jets. Gate 843 prouve la différentiation dominée de chaque
intégrale de face, leur somme finie et les formules Euler/Riesz, sous des contrats
analytiques explicites. Gates 844, 848 et 851 construisent ensuite le jet joint
de la densité, les jets des deux actions de joint et le contrat dominé complet
par compacité locale ; les hypothèses analytiques de Gate 843 sont ainsi
déchargées depuis la géométrie `C²`. Gate 855 prouve enfin les règles exactes
de chaîne et du produit aire–expansion–inaffinité, les transporte sous les
intégrales et les identifie aux deux pairings Riesz nuls de T03.

Gate 858 ajoute les vrais jets locaux de l'intégrande GHY et identifie deux fois
leur intégration à l'Euler GHY mobile à deux feuilles. Gate 863 ferme `T04` par le
certificat Helmholtz global/chartwise de l'action et de l'Euler exacts de T03,
avec les dix réciprocités propres et croisées des quatre blocs physiques.

**Fermé le 2026-09-10.** La représentation PDE locale métrique/GHY et son
raccord au système jet-PDE full-BRST restent un suivi plus fort hors du critère
terminal.

### T05 — `variationalBicomplexObstructionVanishing`

**Déjà disponible :** obstruction fonctionnelle globale nulle sur les cartes.
Les Gates 814–815 construisent le cœur algébrique relatif stratifié, le quotient
cycles/frontières et l'exactitude de l'obstruction pour une donnée de première
variation fournie. Gate 819 donne une réalisation cellulaire relative intégrée
avec `dH` et `dV` non nuls : l'obstruction y est non nulle comme cochaîne mais sa
classe est exacte, et les cochaînes distinguées s'évaluent sur l'action et
l'Euler exacts de T03. Gate 821 ajoute une cochaîne locale réellement typée du
courant scalaire cut-bulk et de sa densité de première feuille, leurs
intégrations et la loi de Stokes identifiée à la composante
`bulk → nonNullBoundary` du `dH` de Gate 819.

Gates 823–824 et 826–829 ajoutent la transgression nulle vers les joints, la
densité GHY, la densité LL, l'agrégat des vraies faces nulles et de leurs joints,
sa spécialisation au modèle fidèle T03, puis la somme locale EH/BRST/
interaction/Maxwell/LL du bulk. Toutes les intégrations annoncées sont reliées
exactement aux actions existantes ; SpinC demeure une frontière intégrée typée.
Gate 830 les rassemble dans un carrier de densités réellement stratifié avec
intégration sectorielle. Gate 833 intègre ce carrier vers les quatre strates de
la cochaîne relative de Gate 819 et récupère exactement la somme canonique des
actions bulk/SpinC/LL, GHY et nulles fidèles. Gate 834 prouve la commutation
d'intégration avec l'arête `dH` finie source nulle vers joints. Gate 835 établit
la naturalité de reparamétrisation correspondante aux degrés cellulaires de
Gate 819, sans transformation globale d'atlas. Gate 836 construit la vraie
densité locale SpinC lisse et l'identifie à l'action de graphe sur la seule
image lisse de son domaine.

Gate 839 réunit les deux arêtes horizontales disponibles, prouve `dH² = 0` et
leur commutation avec l'intégration. Gate 841 établit l'identité verticale et la
première variation sur la cochaîne canonique intégrée. Gate 840 donne une densité
spectrale exacte sur tout le graphe maximal SpinC ; Gate 842 la relève en une
densité spacetime `L¹` sous un contrat d'extension `L²` compatible avec le cœur
fini. Gates 845, 847 et 853 construisent cette extension depuis un cœur mesurable
et réduisent l'entrée encore absente à la mesurabilité des modes signés unitaires.
Gates 846 et 849--850 donnent le bicomplexe local de la sous-fibre nulle fixe.
Gates 852 et 854 typent les deux incidences horizontales manquantes et étendent
le différentiel vertical à toutes les strates fixes, avec les lois d'intégration
et d'anticommutation correspondantes. Gate 856 donne un inverse affine explicite
du `dH` nul→joint sur chaque intervalle non dégénéré et l'exactitude locale au
terme joint. Gate 857 contourne l'opacité du sélecteur de jauge par le pairing
scalaire intrinsèque : sa complétion `L¹` existe sur tout le graphe SpinC maximal
et son intégrale est exactement l'action.

Gate 859 isole les supports linéaires minimaux que doivent réaliser les vraies
incidences bulk→nul et GHY→joint. Gates 860–861 construisent la vraie variation
SpinC `L¹` sur le graphe maximal, l'installent dans le carrier stratifié et
retrouvent exactement son covecteur Euler après intégration. Gate 862 installe
de même le dV local GHY à deux feuilles et l'intègre exactement au jet et à
l'Euler GHY mobiles.

Gate 864 installe le vrai dV fidèle nul/joint et identifie son intégration au
`fderiv` de l'action géométrique nulle. Gate 865 assemble le bicomplexe relatif
concret de Gate 819 : `dH` et `dV` sont non nuls, les carrés, la loi mixte et
l'incidence sont prouvés, et la vraie première variation a une obstruction
cochaîne explicitement non nulle mais égale à une frontière horizontale, donc
de classe nulle. Ses cochaînes s'évaluent sur l'action et l'Euler exacts de T03,
avec Euler égal au gradient sur le domaine.

**Fermé le 2026-09-10.** Gate 865 ferme `T05` ; audit terminal `5/14`.

**Suivi plus fort hors critère terminal :** réaliser géométriquement les
supports de Gate 859, compléter le dV des autres secteurs et leurs
différentiations sous les intégrales, construire le bicomplexe local physique
complet, puis établir la naturalité/recollement d'atlas et l'exactitude locale
recollée. Ces objectifs ne sont pas déclarés fermés.

### T06 — `nullLagrangiansAndBoundaryTermsClassified`

**Déjà disponible :** plusieurs transgressions, GHY, faces nulles, joints et
résidus de bord explicites. Gates 866–900 classifient exactement les
lagrangiens nuls et primitives dans le carrier relatif intégré de T05,
classifient par constantes la classe indépendante de jets invariants de T02,
et appliquent l'équivalence relative aux vrais paquets GHY/nul/joint et au
paquet physique intégré complet. Gate 869 fournit en outre un calcul local
avant intégration sur la tour de jets multi-indices 4D : pour les densités
autonomes affines d'ordre un, le noyau d'Euler est exactement la somme des
constantes et des divergences horizontales, avec un différentiel linéaire de
type BRST. Gate 870 relie exactement, après choix d'une base, les coefficients
multi-indices spatiaux symétriques aux vrais jets encadrés T02. Gates 871–873
forment le produit hybride indépendant T02/T05, le classifient pour son
prédicat nul conjonctif, y plongent les familles physiques de bord avec
composante T02 nulle, et établissent la naturalité à base fixe du complexe
affine sous les applications linéaires qui commutent au différentiel. Gate 874
assemble le produit exact des onze fibres de valeurs physiques et l'identifie,
au niveau des fibres modèles, au produit des seconds jets encadrés T02. Gate
875 fournit la tour multi-indices spatiale véritable de `J⁰` à `J⁴`, ses
troncatures finies et ses dérivées totales commutatives. Gate 876 calcule les
dérivées de Fréchet explicites des polynômes diagonaux multilinéaires de degré
au plus quatre. Gates 877–881 identifient exactement le vrai `J²` Finsupp aux
présentations symétrique et physique T02, renforcent ce pont en équivalence
linéaire continue, définissent les dérivées verticales et totales des fonctions
locales, puis construisent l'opérateur d'Euler d'ordre deux sur `J⁴`. Gate 878
calcule le véritable dérivé de Fréchet de la famille T02 de degré quatre et
Gate 882 le transporte, avec le lagrangien local, sur le vrai `J²` Finsupp.
Gate 883 établit seulement le sens sûr « divergence horizontale d'un courant
affine implique Euler nul ». Gate 884 établit la réciproque exacte uniquement
pour les densités autonomes affines d'ordre deux. Gate 885 prolonge l'action de
deck physique uniquement sur le carrier réduit `(II, F)`, pas sur les onze
composantes physiques. Gate 886 intègre les densités locales continues sur
`J²`, dont la famille T02, le long d'une section à frame fixe dans le carrier
relatif T05 ; aucun théorème de Stokes reliant `dH` local aux bords relatifs
n'est prouvé. Gates 887–889 prolongent le différentiel métrique-BV fini non
nul sur la vraie tour de jets, prouvent la naturalité BRST affine générique,
puis réalisent le complexe affine exact sur ce sous-modèle physique fini.
Gate 890 donne la première famille vraiment non linéaire : la divergence des
courants-valeurs quadratiques dirigés de rang un est quadratique et annulée
par l'Euler de Gate 880. Gate 891 spécialise l'exactitude affine au vrai fibre
de valeurs physique T02 lorsque les coefficients quadratique, cubique et
quartique sont nuls. Gate 892 renforce l'involution de deck réduite `(II, F)`
en équivalences linéaires coefficientielles sur la tour algébrique puis, après
projection finie dans une frame fixe, en équivalences linéaires continues sur
`J²` et `J⁴`. Toute densité linéaire bornée `J²` invariante a alors un
covecteur d'Euler Gate880 équivariant et un lieu Euler-nul stable par deck.
Cette action ne porte toujours pas sur les onze composantes physiques. Gate
893 fournit un pont de Stokes local-vers-intégré exact pour le courant
scalaire cut-bulk canonique dans la seule direction normale du collier ; il ne
couvre ni les courants tangentiels ni les strates nulles et de joints. Gate
894 prolonge une action de deck aux onze composantes physiques et à leurs jets,
conditionnellement à la donnée d'actions fixes sur les fibres gauge et
métrique. Gate 895 place les onze valeurs physiques et la phase métrique-BV
finie dans un même complexe affine exact, mais son différentiel BV non nul
n'agit que sur le sommant métrique fini et s'annule sur les champs physiques
plongés. Gate 896 construit canoniquement les actions gauge et métrique à
partir de la partie linéaire identité de la translation deck dans la frame
produit fixe, ce qui rend l'action sur les onze valeurs et leurs jets
inconditionnelle dans cette frame; la covariance en trivialisation mobile
reste ouverte. Gate 897 prouve que le `dH` véritable de tout potentiel de
valeur `C²`, notamment des polynômes diagonaux de degré au plus quatre, est
annulé par l'Euler Gate880. Gate 898 étend ce résultat aux sommes bilinéaires
de rang fini dans les trois directions. Gate 899 réalise aussi la
transgression canonique face nulle-vers-joints dans le calcul local de jets et
la relie au `dH` intégré Gate819. Gate 900 ajoute quatre gradients de ghosts
abéliens formels au carrier physique/BV complet; le différentiel carré-zéro
non nul agit sur les quatre vrais slots gauge et sur le BV métrique fini, puis
se prolonge aux jets en commutant aux troncatures et dérivées totales. Ces
gradients ne proviennent pas encore de jets de ghosts scalaires. Gate 901
donne la première réciproque non linéaire : sur la famille quadratique
scalaire dirigée à six paramètres, elle calcule Euler exactement, caractérise
son noyau comme constantes plus divergences horizontales affines et
quadratiques, et construit la décomposition explicite. Les directions mixtes
et le carrier T02 complet restent hors de cette sous-classe. Gate 902 conjugue
l'action deck physique complète de la frame fixe par des trivialisations
linéaires ponctuelles fournies, avec lois de groupe et naturalité des jets
coefficientiels. Cette prolongation est spatialement gelée et n'est pas encore
identifiée aux transitions à termes dérivés de l'atlas géométrique. Gate 903
dérive ensuite les quatre covecteurs gauge depuis des jets de ghosts
scalaires d'un ordre supérieur, prouve les lois décalées de troncature et de
dérivée totale, puis construit un morphisme de complexes exact vers Gate900.
Le modèle reste en frame fixe, réel ordinaire, sans ghosts grassmanniens ni
BRST difféomorphisme non linéaire. Gate 904 autorise un composant de courant
dirigé à dépendre de tout le premier jet, prouve son vrai `dH` Gate879 et
l'annulation par Euler Gate880 sous des certificats explicites de Cartan et de
commutation aux ordres supérieurs. `C²` seul ne fournit pas ces dérivées; la
gate ne construit donc pas ces certificats et ne classifie pas le noyau. Gate
905 montre que la réalisation unidimensionnelle du générateur nul de Gate899
ne dépend pas du choix de la coordonnée formelle `Fin 3`, tout en conservant
Stokes T05 et l'incidence Gate819. Cela reste la même géométrie scalaire
nulle-vers-joints, sans théorème de Stokes tangentiel tridimensionnel. Gate
906 classifie ensuite le noyau quadratique scalaire autonome dans les trois
directions, coefficients gradient-gradient mixtes symétriques compris, avec
une décomposition explicite constante plus `dH`. Gate 907 relève la
réciproque dirigée sur un canal rang-un de la fibre modèle physique T02 fixe,
sans construire de fonctionnelle admissible T02 invariante ni prouver la
compatibilité deck. Gate
908 obtient une réciproque multifield de dimension finie pour un terme valeur
linéaire arbitraire, un carré valeur normalisé et tous les courants bilinéaires
de rang fini Gate898. Gate 909 remplace ce carré unique par une forme
bilinéaire valeur-valeur continue symétrique arbitraire et montre qu'Euler
détecte toute la forme. Gate 910 réalise la famille rang-un comme vraie
fonctionnelle admissible T02 et transporte sa classification Gate880, sous
deux témoins explicites d'invariance de transition T02; elle ne construit pas
de canal invariant non nul. Gate 911 prouve que chaque mineur hessien scalaire
à deux directions `u_ii u_jj - u_ij²` est annulé par Gate880 et construit un
courant d'ordre deux dont le vrai différentiel Gate879 est exactement cette
densité, après annulation formelle des termes d'ordre trois. Les réciproques
précédentes restent quadratiques de premier ordre et Gate911 ne couvre que les
mineurs hessiens scalaires individuels; elles n'incluent ni toutes les formes
gradient-gradient croisées entre canaux, ni la dépendance générale au second
jet au-delà de ces mineurs, ni le carrier polynomial T02 complet de degré
quatre. Gate 912 réalise un vrai mineur jacobien multifield
`α(u_i)β(u_j) - α(u_j)β(u_i)` comme différentiel Gate879 d'un courant explicite
de premier ordre et prouve directement son annulation par Gate880. Gate 913
sélectionne un canal LL réel explicite et non nul dans le produit physique des
onze champs, le prouve fixé coefficient par coefficient par l'action deck
canonique sur J⁰–J⁴, puis établit la naturalité en frame fixe de la densité
rang-un, d'Euler et de son représentant divergence. Elle n'identifie pas cette
action figée au `coordChange` T02. Gate 914 transporte ce canal LL non nul par
toute trivialisation mobile ponctuelle fournie et prouve la naturalité du
canal, de tous les coefficients de jet finis, de la densité rang-un, d'Euler
et du représentant divergence sous l'action conjuguée Gate902. La
prolongation reste spatialement figée et n'est pas le `coordChange` T02 avec
corrections de dérivées. Gate 915 ferme le span réel fini des mineurs
jacobiens multifield de Gate912 : le courant pondéré a pour vrai différentiel
Gate879 la densité pondérée, la densité et sa divergence sont annulées par
Gate880, et la représentation est stable par addition et multiplication
scalaire. Elle ne classifie pas tous les lagrangiens nuls de premier ordre.
Gate 916 regroupe des relèvements de cartes, leurs windings de transition et
une équation brute d'entrelacement Gate881/902. À partir de ces données de
compatibilité d'atlas, elle déduit les deux témoins Gate910, construit une
fonctionnelle rang-un T02 admissible, puis transporte le critère exact
d'obstruction Euler et le représentant constante plus `dH`. La construction
de ces données depuis l'atlas physique avec corrections de dérivées reste
ouverte.
Gate 917 traite le déterminant cubique du Hessien scalaire dans les trois
directions. Trois identités de Piola explicites annulent son Euler Gate880 et
un courant de cofacteurs de première ligne sur J² a pour vrai différentiel
Gate879 ce déterminant, après annulation de tous les termes J³. Il s'agit du
seul déterminant Hessien scalaire 3×3, pas d'une classification des polynômes
multifield généraux de second jet.
Gate 918 ferme le span réel fini des trois mineurs hessiens scalaires 2×2 de
Gate911. Elle somme leurs courants J² explicites, prouve que le vrai
différentiel Gate879 est la densité sommée, annule Gate880 et expose addition,
multiplication scalaire et plongement d'un générateur. Elle ajoute la clôture
par combinaisons linéaires finies, pas de nouveaux générateurs multifield.
Gate 919 étend le calcul polynomial diagonal de degré au plus quatre de Gate876
de la dérivée première à tout ordre de Frechet fibrewise fini. Pour chaque
forme homogène, elle identifie la dérivée supérieure à une somme explicite sur
les injections des variations étiquetées dans des slots distincts, spécialise
les ordres deux, trois et quatre, puis assemble le polynôme complet. Ces
formules restent fibrewise : Gate919 ne donne pas encore la formule Euler T02
ni la classification de son noyau.
Gate 920 ajoute les mineurs gradient-jacobiens multifield dépendant des
dérivées secondes. Leurs courants J² explicites ont pour vrai différentiel
Gate879 les densités mineures, et un calcul direct des slots pondérés annule
leur expression d'Euler Gate880, y compris dans la spécialisation scalaire de
Gate911. Elle traite un mineur décomposable à la fois et ne classifie pas le
noyau d'Euler complet du second ordre.
Ces résultats
ne classifient ni le noyau polynomial T02 non linéaire
général ni une action BV physique covariante complète.

**Reste :** classifier le noyau d'Euler de la classe polynomiale non triviale
sur `J⁴` et prouver son homotopie algébrique
`ker Euler = constantes + image dH`, construire le carrier local covariant
commun contenant les densités physiques complètes, puis étendre le pont
intégré compatible à Stokes au-delà du secteur scalaire normal et y relever
la classification. Il faut enfin transporter l'action de deck canonique dans
les vrais jets des trivialisations mobiles et construire le BV/BRST physique non
trivial sur tous les champs physiques.
`T06` reste ouverte.

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

**Suivi plus fort hors portes terminales T03--T05 :** construire le problème
inverse local PDE complet. La seule porte de ce bloc encore ouverte est T06.

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

### Phase 2 — T06 et renforcements locaux hors critères T03–T05

Poursuivre l'atlas brut du tangent et le bicomplexe physique local, puis fermer
la classification exhaustive des bords.

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
compteur officiel est désormais `5/14`. `T01`–`T05` sont fermées ;
`T06`–`T14` restent ouvertes.

Il est en revanche très avancé au niveau de l'infrastructure : géométrie,
champs, action régulière, Dirac, Euler/Helmholtz chartwise et une architecture
Hessien--Fredholm--Quillen particulièrement développée, incluant désormais la
vraie ligne réelle de Fredholm de la famille.

La difficulté résiduelle n'est plus principalement l'absence de wrappers. Elle
se concentre sur trois noyaux scientifiques :

```text
1. compléter le bicomplexe physique local et son recollement ;
2. habiter les estimations analytiques du Hessien/Fredholm physique et
   identifier sa ligne complexifiée à la ligne de Quillen ;
3. fournir la loi microscopique qui sélectionne normalisations, schéma, vide et
   échelle absolue.
```

La PR #60 attaque fortement le deuxième noyau. Elle ne remplace pas les premier
et troisième noyaux, et ne ferme aucune porte tant que les habitants concrets,
la compilation et l'audit ne sont pas obtenus.
