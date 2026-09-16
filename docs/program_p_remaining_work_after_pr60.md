# Programme P — bilan du reste à faire après la PR #60

Date de référence : 2026-09-15.

## 1. Règle de lecture

Ce document distingue trois niveaux qui ne doivent pas être confondus :

1. les infrastructures globales ou sectorielles déjà construites ;
2. les frontiers qui réduisent une conclusion à des entrées mathématiques
   explicites ;
3. les quatorze portes terminales du registre canonique.

La PR #60 poursuivait volontairement l'architecture avant le nettoyage final
de l'élaboration Lean et ne fermait alors aucune porte terminale. `T01`–`T06`
ont depuis été fermées séparément ; `T07`–`T14` restent ouvertes.

Le compteur officiel demeure :

```text
6 / 14 portes terminales.
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

Le premier sous-jalon de l'entrée 1 est maintenant construit : les projecteurs
continus canoniques bulk (difféomorphisme + abélien), matière et LL résolvent
le vrai Hilbert diagonal Candidate A ; le projecteur bulk coïncide avec celui
du cœur lisse. Le raffinement orthogonal physique du bloc bulk en métrique,
abélien et frontière/BV, nécessaire pour obtenir cinq secteurs au total, reste
à construire.

La décomposition du bulk en ses deux facteurs Hilbert existants,
difféomorphisme et abélien, donne maintenant des projecteurs continus
orthogonaux dont la somme est le projecteur bulk. Cela fournit quatre facteurs
achevés, sans créer de facteur frontière/BV indépendant. La route finale doit
utiliser le produit cinq secteurs `WithLp 2` déjà défini : l'ancien produit
ordinaire porte une norme maximum incompatible avec une isométrie hilbertienne
sur plusieurs secteurs non nuls.

Le graph Hilbert courant a désormais un no-go typé : ses quatre projecteurs
canoniques difféomorphisme/abélien/matière/LL reconstruisent déjà l'identité.
Tout cinquième projecteur frontière qui reconstruirait ce même espace avec eux
est donc nul. Un secteur frontière/BV indépendant et non nul exige un Hilbert
augmenté ; il ne peut pas être obtenu en renommant une coordonnée du graph
actuel. `T12` reste ouverte.

Sur ce graphe à quatre facteurs, une résolution auto-adjointe finie des
projecteurs canoniques D/A/matière/LL est maintenant compilée. Elle établit
aussi la décomposition pythagoricienne de la norme `WithLp 2`. Elle n'ajoute
aucun secteur frontière/BV et ne prouve pas la commutation avec le Hessien.
Le compteur terminal reste `6/14`.

Le Riesz L² exact du Hessien diagonal Candidate A commute désormais, par un
théorème compilé, avec chacun de ces quatre projecteurs. L'opérateur augmenté
par la forme physique à sept blocs n'est pas couvert : la commutation avec le
Hessien complet reste à prouver. `T12` demeure à `6/14`.

L'embedding lisse Candidate A est maintenant identifié exactement à un
embedding linéaire facteur par facteur D/A/matière/LL. Un lemme compilé montre
que les quatre projecteurs respectent tout embedding de cette forme. Leur
spécialisation individuelle sur le cœur physique est désormais prouvée pour
D/A/matière/LL. Le commutateur avec le Riesz physique augmenté reste ouvert ;
ce support ne change pas le compteur `6/14`.

Pour l'extension physique construite à partir de la borne du cœur H11, le
Riesz physique à sept blocs a maintenant une borne compilée `‖R_phys‖ ≤ C`
et tous ses pairings vérifient `‖⟪R_phys x,y⟫‖ ≤ C‖x‖‖y‖`. Il reste à
contrôler quantitativement la somme des blocs hors diagonale relativement à
la marge sectorielle ; `T12` reste ouverte à `6/14`.

La compression diagonale des quatre projecteurs est désormais prouvée
contractante ; ainsi le reste physique hors diagonale vérifie `‖R_phys,off‖ ≤
2C` sur le Hilbert Candidate A réel. Cette borne ne fournit pas l'inégalité
stricte `2C < sectorFloor` requise pour H12 et ne crée pas le cinquième
secteur frontière/BV. Le compteur reste `6/14`.

La référence Riesz diagonale commute avec ces projecteurs : sa somme avec le
Riesz physique a exactement le même reste hors diagonal, donc la même borne
`≤ 2C`. L'énoncé compilé vise cette somme explicite ; le seuil H12 reste ouvert.

Pour une face nulle non vide, le Riesz concret des reparamétrisations de faces
est nul sur une direction non nulle : il ne peut fournir le plancher diagonal
positif du cinquième secteur. Une autre Hessienne frontière/BV, avec sa borne
coercive et son raccord au graphe augmenté, reste à construire.

Une extension Hilbert explicite garde les quatre facteurs Candidate A et ajoute
des coordonnées finies de faces. Ses cinq projecteurs forment une résolution
orthogonale, avec axe frontière non nul dès qu'une face non nulle existe. Cette
construction est cinématique : elle ne fournit pas le Hessien frontière/BV ni
son plancher positif.

La forme physique à sept blocs s'annule sur tout premier argument du cœur
diffeomorphisme non minimal pur. Un éventuel plancher positif sur ces directions
doit donc venir de la Hessienne BRST diagonale ; son auto-pairing antifantôme
pur reste à formaliser.

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
Gate 921 transporte tout le calcul des dérivées supérieures de Gate919 par les
ponts physiques et Finsupp-J² réels de T02. Chaque ordre fini est identifié au
vrai `iteratedFDeriv`, avec formule explicite par injections et spécialisations
aux ordres deux, trois et quatre. La formule d'Euler complète et la
classification de son noyau restent à établir.
Gate 922 développe l'opérateur d'Euler général de Gate880 sur J⁴ en
contractions exactes D¹, D² et D³. La seconde dérivée totale contient le terme
de chaîne d'ordre trois et la dérivée de la translation formelle du jet. Gate
923 spécialise cette identité à toute fonctionnelle T02 admissible de degré au
plus quatre avec les dérivées réelles des Gates882 et 921. La formule complète
est calculée, mais son noyau polynomial et son courant d'homotopie restent à
classifier.
Gate 924 établit l'identité de Cartan radiale pour toute fonction locale C³
d'ordre deux sur la vraie tour Finsupp. La décomposition radiale symétrique de
J² utilise les demi-poids hors diagonale, un courant explicite sur J³ absorbe
les contractions non-Euler, et toute densité homogène non constante dans le
noyau d'Euler est un vrai différentiel horizontal après normalisation par son
degré. L'assemblage du polynôme T02 inhomogène et le sens réciproque sûr restent
à fermer.
Gate 925 combine trois dilatations du courant de Gate924 par une quadrature
radiale exacte en degrés un à quatre. Pour toute fonctionnelle T02 admissible,
l'annulation globale du covecteur d'Euler sur J⁴ fournit maintenant un courant
J³ explicite dont le différentiel horizontal est la densité locale moins son
terme constant. Le sens réciproque exige encore une soundness d'Euler pour ces
courants J³.
Gate 926 prouve que chaque composante de ce courant canonique est C∞. Elle
isole aussi les données non circulaires du sens réciproque : factorisation
exacte du `dH` sur J⁴ par une densité J², rétraction par extension nulle,
régularité C³ de la divergence et transfert des trois premières dérivées de
Fréchet itérées. Le télescopage d'Euler d'ordre supérieur reste à établir et
n'est pas supposé dans cette gate. Gate 927 construit le carrier à plafond
fixe requis pour ce calcul : restrictions, shifts tronqués commutatifs sur J⁸,
dérivées totales itérées et multi-indices, partielles verticales et somme
d'Euler d'ordre fini. Gate 928 dérive exactement une dérivée totale et prouve
la commutation des opérateurs totaux dans cet ambient sous régularité C². Gate
929 calcule aussi, par une route directe indépendante, les trois premières
dérivées de Fréchet de la divergence d'un courant J³ sur J⁴, avec tous les
termes provenant du shift linéaire. Gates 930--933 prouvent l'identité verticale
de Cartan, reconnaissent exactement son prédécesseur multi-indice, donnent le
commutateur prêt à télescoper et rendent `D^α` invariant par permutation et
ajout d'une coordonnée. Gate 934 établit enfin la naturalité générique des
lifts de fonctions locales pour les dérivées de Fréchet, verticales et totales.
Gate 935 construit les équivalences exactes de successeur et de partie d'ordre
bas qui réindexent les deux sommes finies de l'annulation d'Euler. Ces gates
alimentent Gates 936--938, qui ferment le télescopage signé, la linéarité de
l'Euler multi-indice et l'identité directionnelle complète
`Euler₄(D_i C) = 0` pour toute composante lisse d'un courant J³. Gate 939
effectue ensuite la somme des trois directions et prouve
`Euler₄(dH C) = 0` pour tout courant J³ lisse. Gate 940 identifie ensuite
exactement l'Euler multi-indice d'ordre deux à la formule pondérée Gate880.
Gate 941 prouve sa naturality sous le lift de densité J² vers J⁴ et le sens
réciproque de soundness. Gate 942 ferme alors le
noyau T02 de degré quatre dans les deux sens : Gate880 s'annule exactement
pour une constante plus le `dH` d'un courant J³ lisse, avec le courant radial
canonique comme témoin explicite. Gate 943 prouve aussi l'invariance de la
divergence représentée sous le vrai changement de carte T02 avec corrections
de dérivées ; le recollement du courant J³ lui-même reste ouvert.
Gate 944 construit une trace linéaire GHY-vers-joints sur tout carrier fini
non vide et prouve sa loi intégrée. Elle répartit la valeur GHY déjà intégrée
et ne remplace donc pas une restriction locale géométrique de codimension
deux. L'incidence bulk-vers-faces nulles reste sans habitant géométrique.
Gate 945 prolonge à J³ l'action mobile compatible fournie à Gate916, prouve son
cocycle, sa troncature exacte vers le vrai changement de carte T02 sur J² et le
recollement des représentants du courant radial canonique sous ce transport.
Ce prolongement reste choisi dans les données de coefficients Gates916/902 :
il n'est pas encore dérivé d'un atlas géométrique de troisièmes jets.
Gate 946 construit le vrai troisième dérivé de Frechet de la transition des
cartes de base de la gorge et prouve ses deux symétries trilinéaires adjacentes
depuis l'atlas lisse existant. C'est le coefficient géométrique de base requis,
mais un atlas J³ géométriquement prolongé du carrier physique complet, les
dérivées et cocycles restants des transitions de fibre et la descente du
courant restent à construire.
Gate 947 identifie la restriction centrée à la gorge du vrai `d c` abélien
global avec la dérivée du représentant réel du fantôme scalaire. La valeur et
la première dérivée du jet de jauge coïncident avec les slots de dérivées une
et deux du J² scalaire. Ce prépont analytique reste centré, limité à une
composante réelle ordinaire et à l'ordre physique un ; il n'est pas encore
raccordé au carrier pairé/gradué ni au slot BRST formel de Gate903. La
covariance sous cartes mobiles, l'action BV non linéaire/complète et une
extraction J³ du fantôme compatible T02 requise à l'ordre deux restent ouverts.
Gate 948 définit un carrier J³ encadré symétrique et la formule exacte à cinq
termes de son changement de base à fibre constante, avec troncature J²,
identité et composition conditionnelle. Il s'agit encore d'une construction
générique à fibre fixe. Gate 949 l'instancie avec les vrais coefficients de la
transition inverse des cartes de gorge jusqu'à D³, puis prouve la troncature
J² exacte et l'identité complète des auto-transitions.
Gate 950 munit ce carrier J³ de sa structure vectorielle réelle composante par
composante, sans revendiquer de structure normée ou complète. Gate 951 expose
le vrai coefficient D³ de la transition directe des repères covectoriels de
gorge et prouve ses deux symétries adjacentes depuis la régularité lisse.
Gate 952 dérive du germe de transition le vrai cocycle D³ des cartes de base,
avec la loi de composition exacte à cinq termes. Gate 953 construit le
transport semidirect générique d'ordre trois par la formule chaîne/Leibniz à
quinze termes et sa troncature J² exacte. Gate 954 l'instancie avec les vrais
coefficients D³ de base inverse et de fibre covectorielle directe. Sa
troncature est définitionnellement le transport de jauge J² existant. Gate 955
prouve le critère générique d'identité et de composition de ce transport J³ et
le conditionne en application linéaire réelle. Gate 956 dérive du germe de
recouvrement le cocycle D³ complet à quinze termes de la transition
covectorielle mobile réelle. Gate 957 assemble les cocycles réels de base et
de fibre et prouve les lois exactes d'identité, de composition et d'inverse du
transport de jauge J³. Gate 958 construit une équivalence réelle linéaire
exacte entre le carrier spatial multi-indice de degré au plus trois et le
carrier J³ encadré symétrique, puis prouve que la troncature Gate875 suivie de
la reconstruction J² encadrée explicite définie dans cette gate coïncide avec
la troncature encadrée. Gate 959 applique cette
équivalence au produit complet des onze composantes : elle conjugue le
changement J³ sélectionné de Gate 945 sur un carrier encadré, prouve identité,
composition et troncature exacte vers le vrai changement T02 sur J², puis
transporte les représentants sélectionnés du courant radial et leur loi de
changement de carte. Cela résout l'écart de format des carriers pour le
prolongement sélectionné/figé, sans construire un atlas D³ géométrique réel
des onze champs. Un secteur covectoriel de jauge séparé possède actuellement
un groupoïde de recouvrement D³ réel. Les autres coefficients et cocycles D³
des transitions de fibre physiques, la descente quotient/bundle et la descente
du courant multichamp sous l'atlas géométrique réel restent ouverts.
Gate 960 installe le transport linéaire J³ réel de jauge sur chaque recouvrement
de l'atlas de jauge existant, le totalise hors recouvrement, prouve identité,
composition et les deux lois d'inverse, puis prouve sa troncature point par
point exacte vers le changement de coordonnées du bundle J² de jauge. Cet
atlas reste algébrique en `LinearMap`. Gate 961 munit tout carrier J³ encadré
de la norme induite par ses composantes
et de sa structure d'espace normé réel, puis prouve sa dimension finie et sa
complétude quand la base et la fibre sont de dimension finie. Gate 962
conditionne chaque changement de coordonnées J³ réel de jauge en application
linéaire continue et y relève identité, composition, inverse et troncature J²
exacte. Cela prouve la continuité dans la variable jet à point de base fixé ; la
continuité jointe lorsque le point de base varie est fournie ensuite. Gate 963
prouve que les champs de coefficients D³ des vraies transitions de base et de
repère covectoriel sont localement `C∞` sur chaque recouvrement valide. Gate 964
prouve qu'une famille générique de transports semidirects J³ dépend continûment
de ses sept champs de coefficients continus de base et de fibre. Gate 965
applique ces résultats à l'atlas de jauge réel : la famille restreinte au
recouvrement est continue et le changement de coordonnées J³ totalisé est
`ContinuousOn` sur chaque recouvrement double. Gate 966 utilise cette
continuité et les lois exactes du groupoïde pour construire le
`VectorBundleCore` topologique J³ de jauge sur l'atlas existant. Ce core sert de
support à la mise à niveau lisse de Gate 971. Gate 967 sépare de la construction
LL la couche J³ réutilisable à fibre constante : elle exprime la règle de chaîne
générique en applications réelles linéaires, la spécialise
aux changements de coordonnées totalisés des vraies cartes inverses de gorge,
prouve identité et composition sur les recouvrements, puis la troncature exacte
vers le changement J² à fibre constante existant. Gate 968 emploie cette couche
pour construire les changements de coordonnées algébriques du produit J³ LL
réel pour les composantes métrique, mesure et champ LL, prouve leurs lois
d'identité et de composition, puis leur troncature exacte composante par
composante vers le changement de coordonnées du core produit LL J² existant.
Elle ne prouve ni continuité, ni core de bundle LL J³, ni extraction des jets
troisièmes des sections LL. Gate 969 prouve que, pour des modèles de base et de
fibre de dimension finie, une famille `C^n` des sept coefficients génériques
semidirects induit une famille `C^n` de transports J³ encadrés linéaires
continus. Gate 970 applique ce résultat et la régularité D³ des coefficients
réels : le transport J³ de jauge totalisé et son changement de coordonnées
linéaire continu sont `C∞` sur chaque recouvrement double. Gate 971 relève le
core topologique de Gate 966 en core `IsContMDiff` et prouve que sa famille de
fibres associée forme un `ContMDiffVectorBundle ∞`. Gate 972 construit la vraie
dérivée troisième de la transition de repère métrique covariante de rang deux,
prouve ses deux symétries adjacentes et son annulation sur les transitions
identiques. Gate 973 prouve la régularité locale `C∞` des champs de coefficients
D³ de la carte de base inverse et de la transition de fibre SpinC directe sur
chaque recouvrement double SpinC. Gate 974 prolonge le changement semidirect
métrique J² réel par les vrais coefficients D³ de la transition de carte de
base inverse et de la transition de repère covariante de rang deux. Le transport
J³ encadré algébrique ponctuel obtenu se tronque exactement vers le transport
métrique J² existant. Gate 975 isole une règle de Leibniz générique au troisième
ordre pour les applications linéaires continues et l'applique pour dériver le
cocycle D³ complet à quinze termes de la vraie transition de repère métrique
covariante de rang deux sur les recouvrements triples valides. Gate 976 combine
les lois des coefficients de carte de base inverse et de repère métrique direct
pour prouver l'identité, la composition et les deux lois d'inverse exactes du
transport métrique J³ encadré ponctuel, y compris son conditionnement en
application réelle linéaire. Gate 977 installe ce transport sur chaque
recouvrement double de la couverture métrique repère/carte existante et le
totalise par l'identité hors recouvrement. Elle prouve l'identité, la
composition et les deux lois d'inverse exactes, ainsi que la troncature
ponctuelle exacte vers le changement de coordonnées métrique J². Gate 978
conditionne chaque changement de coordonnées métrique J³ en application
linéaire continue et relève dans ce conditionnement l'identité, la composition,
les deux lois d'inverse et la troncature J² exacte. Elle établit seulement la
continuité dans la variable jet à point de base fixé. Gate 979 prouve que les
champs réels de coefficients D³ de la carte de base inverse et de la transition
de repère métrique covariante de rang deux directe sont localement `C∞` sur
chaque recouvrement double de l'atlas métrique. Elle fournit seulement la
régularité des deux nouveaux coefficients d'ordre trois. Gate 980 combine la
continuité des cinq coefficients d'ordre inférieur avec les deux champs D³ de
Gate 979 et le théorème générique de continuité du transport semidirect. La
famille restreinte de changements de coordonnées métriques J³ linéaires
continus est continue, et sa forme totalisée est `ContinuousOn` sur chaque
recouvrement double. Gate 981 combine la couverture métrique ouverte
repère/carte existante, les lois exactes du groupoïde et la continuité de Gate
980 pour construire le `VectorBundleCore` topologique métrique J³. Ses
ensembles de base sont ceux du core métrique J² existant et ses changements de
coordonnées sont les applications linéaires continues de Gate 978. Gate 982
combine les cinq champs de coefficients `C∞` d'ordre inférieur de l'atlas
métrique J² avec les champs `baseThird` et `fiberThird` de Gate 979 au moyen du
théorème générique de lissité du transport semidirect J³. Elle prouve que le
transport métrique J³ totalisé et les changements de coordonnées linéaires
continus concrets sont `ContMDiffOn` d'ordre `∞` sur chaque recouvrement double.
Gate 983 enregistre le core topologique métrique J³ comme `IsContMDiff` d'ordre
`∞` et prouve que sa famille de fibres associée forme un
`ContMDiffVectorBundle ∞`. La structure de bundle métrique J³ lisse est ainsi
complète ; l'extraction de sections et la descente du courant restent ouvertes.
Gate 984 expose comme coefficient trilinéaire continu nommé la vraie dérivée
troisième de la transition directe de trivialisation SpinC, exprimée dans la
carte de base cible. Elle prouve les deux symétries de directions adjacentes et
l’annulation de ce coefficient lorsque la trivialisation est répétée. Il s’agit
encore uniquement du coefficient algébrique de fibre d’ordre trois ; le
transport SpinC J³ ponctuel, ses lois de groupoïde, les changements de
coordonnées sur les recouvrements, un core de bundle, l’extraction de sections
et la descente du courant restent ouverts.
Gate 985 prolonge le changement semidirect SpinC J² réel par les vrais
coefficients D³ de la transition de carte de base inverse et de la transition
directe de trivialisation SpinC. Le transport SpinC J³ encadré algébrique
ponctuel obtenu se tronque exactement vers le transport SpinC J² existant. Ses
lois de groupoïde, les changements de coordonnées sur les recouvrements, un
core de bundle, l’extraction de sections et la descente du courant restent
ouverts.
Gate 986 applique la règle de Leibniz réutilisable au troisième ordre pour les
applications linéaires continues au germe réel de transition SpinC et dérive le
cocycle D³ complet à quinze termes de la transition directe de trivialisation
sur les recouvrements triples valides. Elle fournit uniquement la loi manquante
du coefficient de fibre d’ordre trois ; les lois de groupoïde ponctuelles SpinC
J³, les changements de coordonnées sur les recouvrements, un core de bundle,
l’extraction de sections et la descente du courant restent ouverts.
Gate 987 combine les lois des coefficients de carte de base inverse et de fibre
SpinC directe pour prouver l’identité et la composition exactes du transport
SpinC J³ encadré ponctuel. Son conditionnement en application réelle linéaire
satisfait l’identité, la composition et les deux lois d’inverse. Les changements
de coordonnées sur les recouvrements, un core de bundle, l’extraction de
sections et la descente du courant restent ouverts.
Gate 988 installe ce transport sur chaque recouvrement double de la couverture
SpinC trivialisation/carte de base existante et le totalise par l’identité hors
du recouvrement. Elle prouve l’identité, la composition et les deux lois
d’inverse exactes, ainsi que la troncature ponctuelle exacte vers le changement
de coordonnées SpinC J². Les applications restent réelles linéaires
algébriques ; leur conditionnement linéaire continu, la continuité en point de
base, un core de bundle, la lissité, l’extraction de sections et la descente du
courant restent ouverts.
Gate 989 conditionne chaque changement de coordonnées SpinC J³ en application
linéaire continue et relève dans ce conditionnement l’identité, la composition,
les deux lois d’inverse et la troncature J² exacte. Elle établit seulement la
continuité dans la variable jet à point de base fixé ; la continuité en point de
base, un core de bundle, la lissité, l’extraction de sections et la descente du
courant restent ouverts.
Gate 990 combine les cinq résultats de régularité d’ordre inférieur de l’atlas
SpinC J² avec les régularités d’ordre trois de la base et de la fibre fournies
par Gate 973 au moyen du théorème générique de continuité du transport semidirect
J³. La famille de changements de coordonnées SpinC J³ linéaires continus est
donc continue sur chaque recouvrement double. Un core de bundle, la lissité,
l’extraction de sections et la descente du courant restent ouverts.
Gate 991 combine la couverture ouverte SpinC trivialisation/carte de base déjà
existante, les lois de groupoïde SpinC J³ exactes et la continuité de Gate 990
en un `VectorBundleCore` topologique. Ses ouverts de base sont ceux de l’atlas
SpinC J² et ses changements de coordonnées sont les applications linéaires
continues de Gate 989. La lissité, l’extraction de sections et la descente du
courant restent ouvertes.
Gate 992 combine les cinq champs de coefficients `C∞` d’ordre inférieur de
l’atlas SpinC J² avec les champs d’ordre trois de la base et de la fibre de Gate
973 au moyen du théorème générique de lissité du transport semidirect J³. Le
transport SpinC J³ totalisé et les changements de coordonnées linéaires
continus concrets sont `ContMDiffOn` d’ordre `∞` sur chaque recouvrement double.
L’enregistrement du core lisse, l’extraction de sections et la descente du
courant restent ouverts.
Gate 993 enregistre le core topologique SpinC J³ comme `IsContMDiff` d’ordre
`∞` et prouve que sa famille de fibres associée forme un
`ContMDiffVectorBundle ∞`. La structure de bundle SpinC J³ lisse est ainsi
complète ; l’extraction de sections et la descente du courant restent ouvertes.
Gate 994 ajoute un extracteur J³ réutilisable en carte pour tout représentant
de coordonnées `C³`. Il conditionne les trois vraies dérivées de Fréchet,
prouve une seule fois les deux symétries adjacentes d’ordre trois et se tronque
exactement vers l’extracteur J² générique existant. La compatibilité sur les
recouvrements et la section globale ne sont pas encore établies.
Gate 995 applique cet extracteur générique à toute paire valide de
trivialisation SpinC et de carte de base. Elle expose le vrai jet SpinC J³
local, ses quatre projections et sa troncature J² exacte, ainsi que le wrapper
du secteur physique. La compatibilité sur les recouvrements, la lissité des
représentants locaux et la section globale restent ouvertes.
Gate 996 expose un assembleur générique de lissité à partir d’une troncature J²
lisse et d’un champ de dérivée troisième lisse, puis l’applique aux
représentants locaux SpinC réels. Chaque représentant SpinC J³ primitif et
physique est désormais `ContMDiffOn` d’ordre `∞` sur son ouvert d’atlas et se
tronque exactement vers le représentant J² existant. La compatibilité sur les
recouvrements et l’assemblage global restent ouverts.
Gate 997 prouve que le transport semidirect SpinC J³ réel envoie exactement
chaque jet primitif extrait vers son extraction dans la trivialisation et la
carte de base cibles. Le jet inférieur est traité par troncature exacte et la
compatibilité J² existante ; seule la composante d’ordre trois utilise les
règles de chaîne et de Leibniz déjà établies. Le wrapper physique vérifie la
même loi. Seul l’assemblage en section globale reste ouvert.
Gate 998 assemble les représentants locaux SpinC J³ lisses et compatibles au
moyen du constructeur de section locale du `VectorBundleCore` existant. Elle
définit les sections globales `C∞` primitives et physiques, identifie chaque
coordonnée locale valide à la vraie extraction dans une trivialisation et une
carte de base arbitraires, prouve les formules centrées et se tronque exactement
vers les sections J² existantes. L’extraction de la section SpinC J³ est ainsi
complète ; la descente du courant reste ouverte.
Gate 999 applique l’extracteur J³ générique à chaque paire valide de frame
métrique et de carte de base. Elle expose la valeur métrique réelle et ses trois
premières dérivées de Fréchet, se tronque définitionnellement vers l’extraction
métrique J² existante et fournit le wrapper de métrique induite physique avec sa
troncature J² centrée. La lissité des représentants locaux, la compatibilité sur
les recouvrements et la section métrique J³ globale restent ouvertes.
Gate 1000 totalise le jet métrique J³ extrait sur chaque ouvert de frame/carte.
Son champ de troisième dérivée est `C∞` ; avec la troncature exacte vers le
représentant J² lisse existant, l’assembleur J³ réutilisable prouve que le
représentant local complet est `ContMDiffOn` d’ordre `∞`. Le wrapper de métrique
induite physique a la même régularité. La compatibilité sur les recouvrements et
l’assemblage global restent ouverts.
Gate 1001 prouve que le transport semidirect métrique J³ réel envoie chaque jet
tensoriel lisse extrait vers son extraction dans la frame et la carte de base
cibles. Le jet inférieur découle de la troncature exacte et de la compatibilité
J² existante ; seule la composante d’ordre trois utilise les règles de chaîne et
de Leibniz déjà établies. Le wrapper de métrique induite physique vérifie la même
loi.
Gate 1002 assemble ces représentants locaux lisses et compatibles au moyen du
`VectorBundleCore` métrique J³ existant. Elle définit les sections globales
`C∞` primitives et physiques, identifie chaque coordonnée locale valide à la
vraie extraction frame/carte, prouve les formules centrées et se tronque
exactement vers les sections métriques J² existantes. L’extraction de la section
métrique J³ est ainsi complète.
Gate 1003 transforme le transport réel J³ à fibre constante en un
`VectorBundleCore` lisse, sur les domaines de cartes J² existants et avec les
lois de groupoïde exactes.
Gate 1004 forme le core LL J³ lisse comme produit des composantes métrique
auxiliaire, mesure et champ, avec troncature exacte vers le core LL J².
Gate 1005 assemble les onze composantes gauge, LL, métrique et SpinC dans le
core produit physique J³ commun et lisse. L’atlas physique J³ est complet ; les
sections gauge/LL et la descente du courant multichamp restent ouvertes.
Gate 1006 extrait le vrai jet gauge J³ dans toute paire frame/carte de base
valide et le tronque exactement vers l’extraction gauge J² existante. Gate 1007
totalise ces jets sur chaque ouvert et prouve leur représentant local `C∞`.
Gate 1008 établit leur compatibilité exacte avec le transport semidirect gauge
J³, y compris l’expansion complète des règles de chaîne et de Leibniz d’ordre
trois. Gate 1009 assemble les représentants compatibles en sections gauge J³
globales `C∞`, primitives et Candidate-A, avec coordonnées locales, formules
centrées et troncature J² exactes. Les sections gauge J³ sont complètes ; les
sections LL et la descente du courant multichamp restent ouvertes.
Gate 1010 fournit un extracteur J³ centré unique pour tout champ lisse à fibre
fixe et le spécialise aux trois composantes LL. Gate 1011 étend l’extraction à
toute carte de base valide, prouve la loi de transition d’ordre trois, totalise
les représentants et établit leur régularité locale `C∞`. Gate 1012 assemble
les sections J³ globales lisses de la métrique auxiliaire, de la mesure et du
champ LL, avec lois exactes de valeur, jet centré et troncature J², puis forme
leurs coordonnées de section produit. Les sections LL J³ sont complètes ;
l’assemblage de la section physique commune et la descente du courant
multichamp restent ouverts.
Gate 1013 combine les quatre composantes gauge, les trois LL, les deux
métriques et les deux SpinC dans un habitant unique de
`SmoothCoreSectionCoordinates` pour le core physique J³ commun. Elle construit
aussi la section globale de l’espace total, prouve sa formule exacte en
trivialisation locale et sa régularité globale `C∞`. Le bundle physique J³ et
sa section Candidate-A canonique sont assemblés.
Gate 1014 identifie exactement le vrai jet spatial J³ du produit des onze
champs avec la fibre physique de jets encadrés par une équivalence réelle
linéaire continue et fournit la troncature composante par composante vers J².
Gate 1015 transporte le courant radial de Gate 925 par ce bridge, établit ses
lois ponctuelles exactes de pullback d’atlas et prouve l’indépendance de son
évaluation sur la section physique J³ dans chaque étoile de référence. Gate
1016 construit le cocycle strictement positif des poids jacobiens absolus des
vraies transitions de cartes de base. Gate 1017 vectorise le courant radial
dans la base spatiale du complexe de jets et prouve sa loi combinée de cartes
base/fibre de poids un, jusque sur la section physique J³. Gate 1018 prouve la
régularité `C∞` du courant transporté, de sa densité vectorielle et des
représentants à base fixée. Gate 1019 lit cette densité comme un courant sur le
`J⁴` physique formel, puis identifie exactement son `dH` chartwise à la
divergence de Gate 925 et à la factorisation du noyau d'Euler. Gate 1020 définit
la contribution de la coordonnée de base au `dH` local chartwise et retrouve
exactement Gate 1019 dans le cas autonome. Indépendamment, Gate 1021 prouve la
naturelité du courant autonome à base gelée sous un lift J³/J⁴ coefficientiel
de Gate 945 fourni, avec troncature et entrelacement des dérivées totales. Ce
lift n'agit pas sur le `dH` base-dépendant de Gate 1020 et n'est pas la
transition de l'atlas physique. Gate 1022 différentie la formule locale réelle
de coordonnées de l'espace total J³ et prouve exactement
`dΦ(v,w)=(Jv,Cw+(dC·v)j)`, avec le terme de variation en base absent des lifts
gelés. Elle ne prolonge pas encore un frame de Cartan non holonome et ne
construit pas d'atlas J⁴ physique. Gate 1023 forme ces frames verticaux non
holonomes, les transporte avec le Jacobien de base inverse et prouve exactement
l'entrelacement des lifts. Un J⁴ formel fournit désormais son point J³ physique
tronqué et son frame Cartan, sans descente holonome revendiquée. Restent la
Gate 1024 définit le `dH` joint porté par ces frames, retrouve Gate 1020 sous sa
condition exacte de différentiabilité jointe et prouve la naturalité scalaire
par chaîne. Gate 1025 construit le représentant radial local à base variable
sans arguments de preuve, établit sa régularité jointe `C∞` et l'identifie à
Gate 1017 au point représenté. Gate 1026 lit ce représentant sur le J³ physique
formel, décharge par Gate 1025 la condition de différentiabilité jointe de Gate
1024 et retrouve sans hypothèse externe le `dH` base-dépendant de Gate 1020.
Gate 1027 construit les formes volume et flux signées normalisées, identifie la
dérivée extérieure du flux à la divergence coordonnée et prouve la loi de
pullback au déterminant signé. Gate 1028 identifie ce pullback à
`det(J)·J⁻¹` comme germe des vraies transitions de gorge et prouve sa loi de
divergence signée sur chaque overlap. Gate 1029 utilise la constance locale du
signe du déterminant non nul pour passer à la vraie densité vectorielle
`|det(J)|·J⁻¹` et à sa loi de divergence absolue. Gate 1030 identifie le `dH`
joint à la divergence sur une tranche affine de Cartan et prouve sa loi de
Piola absolue sous le vrai transport de frame non holonome, y compris pour le
courant radial sans hypothèse externe de régularité. Gate 1031 relève le
carrier de formes différentielles dans les coordonnées ambiantes 4D existantes
des faces nulles finies : volume coordonné signé, 3-forme de flux du courant,
`d flux = div·volume`, pullback par l'embedding mobile et formule sur le
générateur et les deux tangentes d'écran ; la fonctorialité donne les lois de
composition différentiable de source et d'application ambiante, et le
transformé de Piola signé sous Jacobiennes ambiantes inverses coïncide exactement
avec le pullback du flux ambiant sur la face nulle. Gate 1032 choisit un split
linéaire local arbitraire de l'espace ambiant en coordonnées de gorge et une
coordonnée transverse, ainsi que l'équivalence de coordonnées avec le carrier
holonome 4D du bulk. Elle construit les projections et embeddings associés,
montre qu'un courant tangent à la gorge a un flux hypersurface ambiant nul,
puis ajoute une composante scalaire transverse fournie. La densité radiale
physique J³ de Gate 1030, évaluée le long d'une section J³ locale fournie, est
retrouvée exactement par projection tangentielle sur la tranche transverse
nulle. Sur une vraie face nulle mobile, une interface séparée demande un
courant ambiant, une rigging transverse normalisée et leur identité de bord ;
sous ces données, le pullback de Gate 1031 vaut exactement la densité scalaire
prescrite, y compris avec la densité radiale de Gate 1030 comme terme tangent.
Une rigging brute de flux non nul fournit un habitant ensembliste concret par
normalisation et inverse de l'embedding injectif. Ses valeurs hors de la face
sont arbitraires et aucune régularité n'est prouvée. En particulier, la valeur
au bord ne relie pas encore le premier jet transverse ou la divergence 4D à la
divergence de gorge et au `dH` de Gate 1030. Aucune incidence commune bulk
coupé/face nulle, covariance d'atlas ambiant, orientation ou mesure d'écran,
intégration, Stokes ou trace GHY locale de codimension deux n'est construite.
Gate 1033 effectue le calcul régulier manquant dans le split produit choisi.
Lorsque les composantes de gorge et normale fournies sont `C¹`, elle construit
des courants produit et ambiant `C¹`, identifie les divergences coordonnées aux
traces intrinsèques, puis prouve qu'une extension constante dans la normale a
un premier jet transverse nul et vérifie `div₄ = div₃`. Sur la tranche affine
de Cartan correcte de Gate 1030, Gate 1030 décharge la régularité radiale/jointe
et donne `div₄ = dH`; la différentiabilité de la densité normale fournie reste
requise. Un profil normal affine réalise un premier jet transverse constant
arbitraire, ajoute cette pente à `div₄`, et le choix `-dH` donne une divergence
ambiante nulle au point de base en préservant
la valeur sur la tranche zéro. Ce split régulier n'est pas encore identifié au
vrai collier du bulk coupé ni à l'embedding d'une face nulle mobile finie.
Gate 1034 formalise cette identification comme une donnée d'incidence `C³`
conditionnelle. Elle envoie un ouvert non vide de la source nulle fois `[0,1]`
dans le vrai collier fini puis dans le bulk effectif, avec tout l'intervalle
normal fini contenu dans une carte holonome unique. La coordonnée
obtenue est `C³` sur cet ouvert ; sa tranche zéro est l'inclusion réelle du
bord coupé et coïncide exactement avec l'embedding mobile. Toute fonction de
composantes d'un courant ambiant `C¹` se compose donc régulièrement avec ce
représentant de collier. Le courant produit régulier
de Gate 1033 fournit un tel cas, et une extension de Gate 1032 dont le courant
est fourni `C¹` conserve sur la même tranche sa décomposition de bord et son
flux scalaire prescrit. Lorsque ces deux courants ambiants sont fournis égaux,
le courant régulier de Gate 1033 vérifie cette même loi exacte de flux. Aucun
habitant de la donnée d'incidence n'est encore construit. La donnée n'impose
aucune compatibilité de métrique, volume ou conormale et ne construit pas de
pullback tensoriel d'un champ vectoriel. Gate 1035 définit la vitesse unitaire
dans le vrai facteur normal `[0,1]`, montre que le tangent correspondant du
collier fini est non nul et que l'isomorphisme différentiel déjà construit
l'envoie sur un tangent non nul du bulk. Deux règles de chaîne explicites
identifient son image par le collier source de Gate 1034 à cette vraie normale
du bulk dans la carte holonome choisie. Une seconde donnée conditionnelle aligne
cette normale de carte sur la direction transverse pure de Gate 1033. Sous
cette donnée, le courant constant dans la normale a une dérivée normale nulle
et le courant affine réalise exactement sa pente prescrite. Sans utiliser cet
alignement, les formules de divergence coordonnée de Gate 1033 sont aussi
évaluées sur la vraie tranche zéro de Gate 1034. Ces résultats restent des
énoncés de composantes en coordonnées : aucun habitant de la donnée
d'alignement, aucune normale métrique, Jacobienne tangentielle complète,
compatibilité de volume ou conormale, covariance de champ vectoriel ni loi de
divergence intrinsèque n'est construit. La vraie tranche zéro n'est pas encore
prouvée de coordonnée transverse nulle dans le split arbitraire de Gate 1033.
Gate 1036 isole le défaut de support au niveau de la cochaîne relative. La cible
affine canonique actuellement construite réalise `bulk → nonNullBoundary`,
tandis que le `dH` abstrait complet de Gate 819 recopie la même composante bulk
dans les deux slots de bord. La cochaîne complète égale cette cible supportée
seulement sur le bord non nul exactement quand l'intégrale bulk s'annule ; une
hypothèse d'intégrale non nulle témoigne de l'échec de l'égalité. Cette
construction ne fournit donc pas à elle seule la composante manquante
`bulk → nullBoundary`. Elle ne décide pas si cette composante provient d'une
restriction supplémentaire sur le même collier ou d'une géométrie nulle
séparée.
Gate 1037 sépare ensuite les deux valeurs bulk à la source du complexe
horizontal intégré. Le différentiel suivant s'annule exactement quand ces
valeurs s'accordent ; leur sous-module compatible porte donc un opérateur
gradué de carré nul qui réutilise sans changement la composante
`nullBoundary → joint` des Gates 899/905. Le champ bulk-vers-nul de Gate 852
fournit cette compatibilité et retrouve sa cible complétée. La source nulle reste
toutefois contractuelle, sans construction géométrique.
Gate 1038 prouve sans hypothèse que la structure de géométrie nulle mobile est
habitée. Son hyperplan explicite `z = u` porte la métrique diagonale de signature
lorentzienne
`diag(-1, exp u, exp u, 1)`, une conormale définissante nulle non nulle, un
générateur nul, une métrique d'écran positive et une expansion unitaire ; le
relèvement métrique de la conormale redonne ce générateur. Le modèle est
indépendant de l'input, et ses données de joint et de normalisation sont des
constantes conventionnelles. Il ne construit ni réalisation d'action fidèle ni
carrier de joint et n'est pas encore identifié à une hypersurface du bulk
mapping-torus.
Gate 1039 ajoute la restriction linéaire locale des courants ambiants vers leur
flux scalaire tiré en arrière sur cet hyperplan. Le rigging concret `e₀` a un
flux non nul ; un inverse à droite ensembliste montre donc que toute densité de
carte est atteinte pour la famille de faces singleton. Aucune régularité n'est
affirmée pour cette extension, qui ne fournit ni intégration d'écran,
ni incidence mapping-torus, ni restriction PT05, ni loi de Stokes.
Gate 1040 prolonge cet hyperplan en un collier linéaire continu global
`((u,x,y),r) ↦ (u,x,y,u+r)`. Son inverse est explicite, sa tranche zéro redonne
l'embedding de Gate 1038, la fonction définissante vaut `r` et la dérivée
radiale positive est `e₃`. La convention `-e₃` pour le futur bord inférieur du
demi-collier `r ≥ 0` ne diffère du rigging de Gate 1039 que par le générateur
tangent ; elle a donc le même flux coordonné non nul. Gate 1041 fixe exactement
ce signe : deux échanges du repère tangent et l'alternance donnent le flux
coordonné `+1`, identique pour le rigging `e₀` de Gate 1039. Gate 1042 remplace
le choix ensembliste de Gate 1039 par le courant linéaire explicite
`(0,(r-1)ρ(q))` dans le collier. Son flux inférieur vaut `ρ`, sa valeur en
`r=1` est nulle, sa divergence coordonnée ambiante vaut `ρ(q)` aux points de
différentiabilité, et l'intégration sur `0 ≤ r ≤ 1` donne l'identité de Stokes
sur une fibre. Gate 1043 calcule la densité métrique
`√|det g| = exp u`, l'identifie à l'aire d'écran sur la face et prouve les
versions courant densitisé et volume métrique de cette identité fibre par
fibre. Gate 1044 munit toute la source `(u,x,y)` du volume coordonné et de la
mesure d'écran `exp(u) du dx dy`, prouve les formules d'intégrale pondérée et
d'intégrabilité, puis intègre Gate 1043 sur la source sous un contrat explicite
de différentiabilité et d'intégrabilité. Gate 1045 réutilise ensuite le collier
source fini de Gate 1034 pour donner à
`source × [0,1]` sa structure analytique à coins, identifier exactement ses
faces `r=0` et `r=1`, l'embarquer comme la dalle ambiante `0 ≤ z-u ≤ 1`, puis
y restreindre le courant affine avec flux inférieur `ρ` et valeur extérieure
nulle dans la convention coordonnée fixée. Gate 1046 prouve que toute densité
source différentiable à support compact satisfait automatiquement le contrat
d'intégrabilité pondérée de Gate 1044 et que son courant restreint au
demi-collier fermé est à support compact. Elle construit un bump lisse non nul,
de support égal à la boule fermée de rayon deux, et instancie pour lui la loi de
Stokes intégrée. Gate 1047 spécialise enfin l'incidence conditionnelle de Gate
1034 à cet hyperplan : sur le patch source, la face réelle du bulk mapping-torus
a exactement l'embedding warped comme coordonnée de carte. Elle y transporte
les formules coordonnées de courant, flux et densité métrique warped, et prouve
l'injectivité des points de bord sélectionnés. Ce raccord reste conditionnel et
limité à la face ; il n'identifie ni les colliers complets, ni leur normale, ni
la métrique ou la mesure physique du mapping-torus. Gate 1048 encode le raccord
suivant par un germe de transition ambiante en un point de cette face. Son
Jacobien est inversible, son déterminant absolu est strictement positif, et il
envoie exactement le radial warped `e₃` sur la normale de carte du vrai collier.
Le datum reste conditionnel et ponctuel ; aucune compatibilité globale de
collier, métrique, mesure ou Piola-divergence 4D n'en découle.
Gate 1049 extrait l'inverse local choisi et son Jacobien inverse, qui ramène la
normale du vrai collier sur `e₃`. Le pullback signé du courant densitisé préserve
alors, au point sélectionné, la trois-forme de flux de face et son coefficient
sur le repère source, aussi bien contre la vraie coordonnée de face que contre
l'embedding warped. Cette loi reste ponctuelle et fondée sur le volume
coordonné ; elle ne fournit ni covariance du volume métrique ni loi de
divergence de Piola en dimension quatre.
Gate 1050 ajoute cette loi de divergence en volume coordonné. Elle prouve la
formule de Piola signée ambiante en dimension quatre par dérivation extérieure
de la trois-forme de flux, obtient les Jacobiennes inverses sur tout le germe de
transition et déduit automatiquement la régularité du courant transformé d'un
courant cible `C¹`. Au point de face, la divergence est multipliée par le
déterminant signé tandis que le flux est préservé. Pour le courant affine, les
deux valeurs sont le déterminant signé fois `ρ` et le flux `ρ`. La mesure reste
le volume coordonné fixe, pas le volume métrique physique.
Gate 1051 prouve que ce déterminant non nul garde un signe strict dans un
voisinage et en déduit la loi de Piola absolue : la divergence est multipliée
par la densité positive `|det J|` sans choix d'orientation. Pour le courant
affine, elle vaut `|det J|ρ`. Le flux signé du pullback absolu reste exactement
`ρ` sous l'hypothèse explicite `det J > 0`, laquelle ne découle pas du datum de
transition actuel. Il s'agit toujours d'un Jacobien coordonné, pas encore du
volume métrique physique.
Gate 1052 écrit ce Jacobien dans la base ambiante fixe et prouve la loi de
congruence du volume métrique
`sqrt|det(Jᵀ g J)| = |det J| sqrt|det g|`. Sous l'hypothèse ponctuelle explicite
qu'une métrique cible fournie se tire en arrière sur la métrique warped, sa
densité multipliée par le Jacobien positif vaut à la fois la densité warped et
l'aire d'écran homogène. Cette hypothèse ne découle pas encore de l'incidence
ou de la transition, et la matrice cible n'est pas identifiée à une métrique
physique du bulk.
Gate 1053 renforce cette congruence sur le germe de transition. Le courant
ordinaire tiré en arrière puis densitisé par le volume warped y coïncide avec
le pullback de Piola absolu du courant cible densitisé. La formule coordonnée
`div_g X = (sqrt|g|)⁻¹ ∂(sqrt|g|X)` est donc naturelle au point de face, sous
la régularité du courant cible déjà densitisé. Le champ métrique cible reste
fourni et n'est relié ni à la métrique physique du mapping-torus ni à un
recollement d'atlas.
Gate 1054 rend ce champ cible physique. Elle inverse exactement la carte de
l'incidence, ramène la coordonnée warped de face sur le vrai point de bord du
mapping-torus et évalue une `SmoothGeneralLorentzMetric` sur le repère dérivé
de cette carte inverse. La transition reste dans la cible valide de la carte
sur un germe. Sous la congruence warped/physique toujours explicite, la
naturelleté de Gate 1053 concerne donc ces vrais coefficients métriques. Il
reste à construire un habitant de ce datum de compatibilité physique.
Gate 1055 élimine l'hypothèse supplémentaire de Gate 1053 sur la régularité du
courant déjà densitisé. Le cocycle de volume métrique, la densité warped lisse,
le Jacobien non nul et l'inverse local imposent la différentiabilité de la
densité métrique cible au point de face. Tout courant cible ordinaire `C¹`
fournit donc automatiquement le courant de volume requis, y compris pour la
métrique physique de Gate 1054. Le datum de compatibilité reste conditionnel.
Gate 1056 ouvre la voie physique fidèle : la métrique du collier est définie
comme le vrai pullback d'un champ métrique cible. Sa loi de densité à Jacobien
absolu, l'égalité du courant densitisé avec le pullback de Piola et la
naturelleté de la divergence au point de face sont alors automatiques. La
spécialisation aux vrais coefficients métriques de Gate 1054 ne demande aucune
compatibilité avec la métrique warped fixe. Une condition ponctuelle plus
faible suffit pour identifier la densité de face à l'aire d'écran ; réutiliser
la divergence warped exige encore une égalité sur un germe, exactement celle
fournie par le datum conditionnel plus fort de Gate 1054.
Gate 1057 ferme directement la régularité de cette voie physique fidèle. Sur
le domaine valide de la carte inverse, le point de carte et son repère dérivé
sont lisses, le repère coordonné transporté est une base et la
non-dégénérescence lorentzienne rend le déterminant métrique non nul. La
matrice physique, `sqrt|det g|` et le courant de volume associé à tout courant
ordinaire `C¹` sont donc différentiables à la face. La naturalité de divergence
de Gate 1056 ne demande plus aucune hypothèse de régularité densitisée ni de
compatibilité avec la métrique warped.
Gate 1058 identifie la géométrie nulle ponctuelle dans le pullback physique
fidèle : le générateur et le rigging normalisé forment une paire nulle avec
`g(N,k) = -1`, sont orthogonaux à l'écran warped de déterminant positif, et la densité de face
orientée par le rigging est son aire homogène. Le Jacobien signé de transition
est aussi le flux coordonné de l'opposé de la direction du facteur collier à
vitesse unité. Sa positivité reste une condition explicite de coorientation ;
la densité de face positive n'en fixe pas le signe.
Gate 1059 transporte le générateur, l'écran et le rigging dans les vrais
coefficients métriques physiques du mapping-torus. Les mêmes identités de paire
nulle y valent et l'aire d'écran cible est `exp u`. Ces résultats restent
conditionnels et ponctuels.
Gate 1060 prouve la régularité lisse du relèvement canonique de première feuille
et construit une `boundaryMap` inverse-stéréographique lisse, avec ses formules
exactes dans le cover et le quotient. Elle ferme la partie `boundaryMap` du
futur datum d'incidence, pas sa carte bulk adaptée.
Gate 1061 construit le germe de coordonnée adaptée manquant. Elle inverse
localement la vraie carte de bande tubulaire, lit les coordonnées équatoriales,
temporelle et de latitude, puis applique le cisaillement warped. Ses domaines
bulk et source sont ouverts, toute ancre choisie appartient au patch, et la
première feuille canonique réelle a exactement la coordonnée `(u,x,y,u)` sur
ce patch. Gate 1062 l'empaquette en difféomorphisme local et expose son inverse
partiel explicite. Le déterminant `1` obtenu est celui du seul aller-retour
carte/inverse et ne fixe pas l'orientation par rapport à une autre carte. Gate
1063 étend le représentant tubulaire à toute normale de `[0,1]`, l'identifie au
vrai collier cut-bulk et calcule sa coordonnée `(u,x,y,u+r)` ; elle ne place pas
encore tout ce collier dans l'unique germe bulk de Gate 1062. Gate 1064 remplace
la carte produit incompatible de Gate 1034 par une `PartialDiffeomorph`
physique libre, conserve un adaptateur depuis les anciens data et construit
l'incidence canonique adaptée. Sa validité de carte est affirmée sur la face.
Gate 1065 ferme la lacune de couverture normale sur la bande temporelle
fondamentale ouverte : pour un pôle stéréographique fixé, une même carte
physique contient toutes les normales `0 ≤ r ≤ 1`, a pour cible la bande warped
ouverte correspondante et donne exactement `(u,x,y,u+r)`. La couture temporelle
et le pôle choisi restent exclus. Gate 1066 généralise le datum de transition de
Gate 1048 à la nouvelle incidence. Son inhabitant canonique a pour vraie
transition l'identité comme germe du collier ; son Jacobien signé vaut donc
`+1` et la direction positive du collier devient `e₃`, indépendamment du
déterminant d'aller-retour de Gate 1062. Gate 1067 empaquette tout le collier
fini au-dessus de cette bande et restreint la loi de Stokes intégrée de Gate
1044 aux densités dont le support topologique reste dans la bande ; les deux
intégrales restreintes sont intégrables et égales à leurs versions globales.
Gate 1068 tire toute métrique lorentzienne lisse dans une carte physique
partielle, prouve que son déterminant coordonné est non nul et sa densité-volume
positive, puis corrige tout courant par le rapport exact des densités warped et
physique. Le courant densitisé et sa divergence coordonnée coïncident alors sur
la cible de carte, en particulier sur la face révisée et tout le collier fini
canonique.
Gate 1069 applique cette correction au courant affine du collier. Sur tout le
collier canonique au-dessus de la bande temporelle ouverte, les divergences
densitisées physique et warped coïncident point par point ; leurs intégrales de
fibre et bulk régionales sont donc égales, puis Gate 1067 donne la loi de Stokes
régionale pour la métrique physique. Les mesures restent celles des coordonnées
canoniques, sans pushforward sur l'image physique.
Gate 1070 isole le datum géométrique commun manquant pour le même `faithful`
fini arbitraire employé par T03/T05 et la même métrique Candidate-A
`plusBase.metric`. Sous ce datum, l'embedding fidèle est une coordonnée de carte
physique, son germe métrique ambiant est le pullback physique, son générateur est
nul et orthogonal à l'écran, et la métrique d'écran stockée est bien induite.
Aucun habitant canonique de ce datum n'est affirmé.
Gate 1071 pousse la mesure d'écran régionale par la vraie paramétrisation de la
première feuille dans le mapping-torus. Cette paramétrisation est injective sur
la bande fondamentale ouverte, le flux affine possède un représentant physique
mesurable, et son intégrale pushforward égale l'intégrale de bord coordonnée.
La loi Gate 1069 devient donc une égalité avec une intégrale sur l'image
physique du bord. La mesure-image bulk 4D et sa formule de Fubini restent à
construire.
Gate 1072 fournit la couche analytique locale de la trace GHY vers joint sur un
carrier mesuré : l'identité de dérivée d'une primitive donne les deux densités
d'extrémité orientées par le théorème fondamental, puis Fubini identifie
l'intégrale produit au coefficient de joint fini de T05. L'incidence physique
des coins et l'identification aux actions d'extrémité fidèles restent à fournir.
Gate 1073 empaquette la covariance base/fibre J³ déjà prouvée en une section
physique globale de densités vectorielles : chaque carte simultanément valide a
un représentant, les représentants satisfont la loi exacte de recouvrement, et
le courant radial de Gate 942 donne une section canonique dont la valeur dans la
carte préférée est la densité physique initiale.
Gate 1074 assemble les incidences locales de Gate 1070 en un atlas fourni qui
couvre chaque point source de chaque face du même `faithful`. Il en déduit
l'identification métrique, la nullité du générateur, son orthogonalité à l'écran
et la métrique d'écran induite. Aucun habitant ni transition orientée cohérente
entre patches n'est construit.
Gate 1075 construit la mesure produit 4D du collier canonique, la pousse sur
l'image bulk physique réelle, prouve l'intégrabilité jointe et Fubini, puis
transporte Stokes jusqu'aux mesures-images bulk et bord. Ces mesures restent des
pushforwards paramétrés, sans identification Hausdorff ou volume métrique
intrinsèque.
Gate 1076 prouve la régularité en base de l'évaluation radiale J³ sur toute
trivialisation commune fixée, sa mesurabilité forte sur la mesure canonique
restreinte et son intégrabilité sur tout sous-domaine compact de carte. Il
l'identifie au représentant global de Gate 1073 et spécialise la naturalité
Cartan--Piola à la vraie section J³ Candidate-A. Le sélecteur global de carte
préférée n'est pas prouvé mesurable et aucune intégrale globale d'atlas n'est
affirmée.
Gate 1077 instancie la couche de Gate 1072 sur un collier physique mesuré fourni
pour le même `faithful` et `plusBase`. Une formule structurelle de coaire et une
famille linéaire de primitives locales donnent le coefficient orienté, un vrai
opérateur linéaire T05 `GHY → joint` et son support d'intégration pour la densité
GHY canonique. Aucun collier ou famille de primitives canonique n'est habité.
Gate 1078 insère chaque résidu Euler T02 véritable dans le slot bulk du carrier
relatif T05. La nullité relative équivaut exactement à l'annulation d'Euler,
donc à la forme normale constante plus courant radial physique J³, avec les
primitives relatives T05 normalisées uniques. Ce carrier commun est logique et
ne revendique pas un chain map de Stokes physique global.
Gate 1079 réalise conditionnellement le passage du quatrième jet T02 formel au
collier physique de Gate 1075 : une section J⁴ compatible fournie identifie le
`dH` radial de Gate 942 à l'intégrande bulk physique, l'intègre au flux de bord
de la première feuille et sépare l'augmentation constante du bord relatif.
Gate 1080 produit le certificat terminal exhaustif sur la cohomologie
fonctionnelle globale dans les cartes normées, le secteur T02 invariant de
degré au plus quatre et le carrier relatif intégré T05. Il enregistre aussi les
corollaires concrets GHY, nul/joint fidèle et paquet physique intégré complet.

**Fermé le 2026-09-15.** Gate 1080 ferme `T06` ; audit terminal `6/14`.

**Suivi plus fort hors critère terminal :** la contrainte `face_coordinate` de
Gate 1034 est incompatible avec la carte produit fixe : sa projection spatiale
a rang deux sur la gorge réelle,
contre rang trois pour la face warped `(u,x,y,u)`. Gates 1064--1069 contournent
maintenant cette obstruction, couvrent le collier régional, fixent son signe de
transition et transportent la divergence densitisée sans supposer d'isométrie.
Construire un habitant de l'atlas Gate 1074 pour la famille fidèle
arbitraire, puis identifier le rigging normalisé, l'orientation, les transitions
de courant/flux et les mesures compatibles. Gate 1075 ferme la mesure-image et
Stokes seulement sur la première feuille canonique régionale. Gate 1076 ferme
la régularité dans une trivialisation fixée, mais il reste à recoller une
intégration J³ mesurable au niveau de l'atlas. Habiter aussi le collier/coaire et
la famille linéaire de primitives de Gate 1077 pour les vrais coins et actions
fidèles. Assembler ensuite ces flèches avec les flèches déjà réalisées
`bulk → nonNullBoundary`
et `nullBoundary → joint` en étendant le squelette intégré de Gate 1037 à un
chain map local/intégré commun, avec naturalité et compatibilité à
l'intégration et augmentation constante explicite. Ces réalisations globales
physiques d'atlas, Stokes, coaire et BV restent hors du critère terminal T06.

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
famille et sa frame normalisée, ainsi que la résolution auto-adjointe des
quatre secteurs du graphe diagonal actuel et leur commutation avec le Riesz
du Hessien diagonal.

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

**Suivi plus fort hors portes terminales T03--T06 :** construire le problème
inverse local PDE complet et les réalisations physiques globales d'atlas,
Stokes, coaire et BV.

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

### Phase 2 — Renforcements locaux hors critères T03–T06

Poursuivre l'atlas brut du tangent, le bicomplexe physique local et les
réalisations globales atlas/Stokes/coaire/BV.

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
compteur officiel est désormais `6/14`. `T01`–`T06` sont fermées ;
`T07`–`T14` restent ouvertes.

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
