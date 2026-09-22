# T12 : pairing matière–LL et obstruction BRST → D9

## Résultat positif

`strong_actualMatterLL_pairing_eq_physicalZero` établit le pairing exact entre
le Riesz augmenté réel et la fibre physique de Friedrichs à paramètre zéro,
sur le cœur réduit matière–LL de la carte forte centrée. Il utilise les données
géométriques, la réalisation matière et l'extension physique existantes, sans
hypothèse supplémentaire d'égalité des formes transportées et sans
`ProgramPT12CanonicalActualFriedrichsSmoothCoreIntertwiner4D`.

Source : `P0EFTJanusProgramPT12StrongMatterLLUnconditionalPairing4D.lean`.

## Obstruction démontrée

- `d9Real_pairing_nonneg` : le D9 installé, de poids `normSquared (covector i)`,
  a un pairing réel non négatif pour tous les modes, covecteurs et éléments
  de son domaine maximal.
- `exists_abelianBRST_negative_direction` : un champ Nakanishi–Lautrup abélien
  pairé constant non nul donne un pairing BRST strictement négatif.
- `no_abelianBRST_actual_to_D9_pairing` : aucune application du cœur BRST
  abélien vers ce domaine D9 ne préserve tous les auto-pairings. Le théorème
  n'exige même pas que l'application soit linéaire ou injective.
- `pureAbelianNakanishiLautrupCore_physicalHessian_left_zero` et
  `pureAbelianNakanishiLautrupCore_augmented_pairing_self` : sur ce témoin,
  la colonne physique H11 est nulle et le pairing réel augmenté vaut
  exactement `-‖globalPairedGaugeLieL2LinearMap ... field‖²`.

Sources : `P0EFTJanusProgramPT12D9NonnegativePairing4D.lean`,
`P0EFTJanusProgramPT12AbelianBRSTNegativeDirection4D.lean`,
`P0EFTJanusProgramPT12AbelianBRSTActualD9NoGo4D.lean` et
`P0EFTJanusProgramPT12AbelianBRSTNegativePhysicalColumn4D.lean`, dans
`JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple/Gates/`.

## Conséquence pour la fermeture

La réalisation sectorielle actual→D9 demandée est impossible avec le D9
positif actuel. L'obstruction abélienne suffit à bloquer cette identification
globale. Les constructions signées ci-dessous préparent une autre cible ;
elles n'établissent pas encore son accord modal avec le cœur réel.

Le quotient LL auxiliaire/mesure existe déjà dans
`P0EFTJanusProgramPT12LLFullSmoothReducedQuotient4D.lean` et demeure la voie LL.
Les gates Quillen existantes sont conservées. Aucun certificat terminal
global n'est ajouté et T12 n'est pas coché.

## Avancée signée du 22 septembre 2026

- `P0EFTJanusProgramPT12SignedBRSTGram4D.lean` construit les opérateurs de
  Gram et les termes croisés signés par adjoints, avec leurs pairings exacts.
- `P0EFTJanusProgramPT12AbelianSignedBRSTRealization4D.lean` identifie
  `pairedAbelianSignedRiesz` au Riesz abélien pairé réel sur le graphe
  complété et retrouve la polarisation BRST sur le cœur lisse. La complétion
  du carré conserve le terme négatif Nakanishi–Lautrup et les deux ghosts.
- `P0EFTJanusProgramPT12DiffeomorphismSignedBRSTRealization4D.lean`
  identifie `diagonalDiffeomorphismSignedRiesz` au Riesz difféomorphisme
  diagonal réel, avec les poids sectoriels et l'unique triplet nonminimal
  partagé. Son pairing lisse retrouve également l'action BRST réelle.
- `P0EFTJanusProgramPT12SignedBRSTAugmentedPairing4D.lean` assemble ces deux
  opérateurs avec les formes matière–LL et la forme physique complète.
  `signedBRST_retains_all_physical_columns` expose l'accord H11 déjà fourni
  par l'extension physique existante ; il ne construit pas une nouvelle
  extension ni une estimation spectrale des colonnes.
- `P0EFTJanusProgramPT12SignedD9Reference4D.lean` double le multiplicateur
  D9 avec les poids opposés. La référence est densément définie,
  autoadjointe et fermée ; elle est Fredholm sous les données existantes
  d'ellipticité à modes caractéristiques finis. Le module prouve aussi la
  décomposition signée exacte du symbole abélien nonminimal.

Ces égalités de Gram concernent les Riesz bornés des graphes réels. Une
complétion de carrés est une congruence, pas une identification isométrique
avec la référence modale. Elle ne fournit donc pas à elle seule un domaine
L² non borné, la propriété Fredholm ou la compacité des perturbations H11
pour l'opérateur géométrique réel. Le double D9 est une référence analytique,
pas une preuve d'identification de ses composantes avec les champs réels.

Restent à construire le transport géométrique actual→modes signé, son
accord de domaine et de cœur, les estimations nécessaires pour H11, puis
l'intertwining global avec le secteur LL quotienté et le certificat terminal.
Aucune hypothèse `ProgramPT12CanonicalActualFriedrichsSmoothCoreIntertwiner4D`
n'est ajoutée. L'obstruction vers le D9 positif reste valable.

## Symbole abélien complet et norme de graphe

`P0EFTJanusProgramPT12AbelianNonminimalSignedSymbol4D.lean` construit un
changement de coordonnées inversible pour le symbole Maxwell + BRST
nonminimal :

```text
(A, c, cbar, B) → (A.x, A.y, A.z, B − ξ·A, cbar + c, cbar − c).
```

L'inverse restitue explicitement tous les champs. Le changement respecte
l'addition et la multiplication scalaire. Le pairing complet est exactement
diagonal, de poids `(q, q, q, −1, q/2, −q/2)`, où `q = ‖ξ‖²`.
Le terme physique utilisé est le symbole Maxwell `−ξ×(ξ×A)` ; l'identification
avec le Hessien H11 géométrique global n'est pas démontrée par ce calcul.

`P0EFTJanusProgramPT12AbelianMixedOrderReference4D.lean` réalise ces poids sur
le domaine diagonal maximal, puis les duplique pour les deux secteurs
abéliens. Les douze coordonnées complexes par mode sont conservées. La
référence est dense, autoadjointe et fermée ; les données d'ellipticité D9
existantes donnent un gap `min(1, gap/2)` et la propriété Fredholm. Le poids
auxiliaire `−1` n'a jamais de zéro ; les cinq autres coordonnées s'annulent
exactement aux modes caractéristiques. Ce résultat précise la cible
abélienne : le double uniforme `±q` précédent ne décrit pas ce carré
auxiliaire d'ordre zéro.

`P0EFTJanusProgramPT12AbelianSignedCoordinateGraphBounds4D.lean` compare les
tailles quadratiques avant et après ce changement, en ajoutant `|ξ·A|²` de
chaque côté. Chacune est majorée par trois fois l'autre, uniformément en ξ.
En revanche, aucune constante uniforme ne contrôle le changement sur la
norme brute des coefficients : l'état `A=(1,0,0), c=cbar=B=0`, de taille
quadratique 1, a une image de taille `1+n²` pour `ξ=(n,0,0)`.

La congruence est donc contrôlée au niveau du graphe longitudinal, sans
être une isométrie L². Le transfert de domaine géométrique, les coefficients
variables et les autres colonnes H11 restent à traiter avant d'appliquer
ces références à l'opérateur réel. Le bloc difféomorphisme reste lui aussi
à identifier modalement. Aucun certificat global ni fermeture T12 n'est
déduit de ces trois gates.

## Annulation des ghosts diagonaux sur le cœur réel

`P0EFTJanusProgramPT12DiagonalGhostCancellation4D.lean` traite directement
le graphe difféomorphisme réel avec son unique triplet partagé. Sous les
deux conditions explicites

```text
metric.plus = metric.minus
candidateAPlusEinsteinKineticWeight + candidateAMinusEinsteinKineticWeight = 0,
```

les deux pairings sectoriels coïncident sur toute colonne ghost pur. Leur
somme pondérée s'annule. La densité du cœur lisse étend cette annulation
à tous les tests du graphe complété : `diagonalPureGhost_riesz_zero` est
une égalité du Riesz réel, sans référence modale.

`P0EFTJanusProgramPT12DiagonalGhostPhysicalKernel4D.lean` montre que la
projection physique du même ghost est nulle, donc que H11 laisse la colonne
nulle. Il étend le résultat au Riesz augmenté sur l'espace de Hilbert complet.
`diagonalGhost_injects_into_augmented_kernel` construit une injection linéaire
de tout l'espace des ghosts lisses dans ce noyau. En conséquence, prouver
que ce noyau est de dimension finie dans ce régime imposerait aussi la
dimension finie de l'espace des ghosts. La preuve de dimension infinie,
ajoutée ensuite, est décrite ci-dessous.

Ce résultat est conditionnel : il n'affirme pas que le fond retenu satisfait
ces deux égalités. Les couplages Einstein actuels imposent séparément leur
non-nullité, pas leur positivité ; cette seule non-nullité ne suffit donc
pas à exclure des poids opposés. Une réalisation globale doit traiter le
couplage du triplet partagé et vérifier ses hypothèses sur le fond choisi.
Dupliquer deux réalisations mono-métriques indépendantes ne traite pas ce
couplage. T12 reste ouvert ; Quillen et le quotient LL sont inchangés.

## Dimension infinie et obstruction au transport du noyau

`P0EFTJanusProgramPT12ScalarFrameGhostInjection4D.lean` construit l'application
linéaire injective `f ↦ (f X_i)_i`, où les `X_i` sont la famille finie de
champs tangents engendrant chaque fibre déjà construite sur le quotient.
Il n'est pas nécessaire de supposer une base globale du fibré tangent.
Une dimension finie des ghosts impliquerait celle des champs scalaires lisses.

Pour une période strictement positive,
`P0EFTJanusProgramPT12SmoothGhostInfiniteDimension4D.lean` réfute cette
dernière propriété. Les parties réelle et imaginaire plongent les champs
complexes dans deux copies des champs réels ; l'injection de Fourier
temporelle existante y réalise `Int →₀ Complex`, qui est de dimension réelle
infinie. Les ghosts difféomorphismes lisses sont donc eux-mêmes de dimension
réelle infinie.

`P0EFTJanusProgramPT12DiagonalGhostInfiniteKernel4D.lean` compose ce résultat
avec l'injection dans le noyau augmenté. Sous période positive, métriques
égales et somme nulle des poids cinétiques :

- `diagonalGhost_augmented_kernel_not_finiteDimensional` établit la dimension
  infinie du noyau du Riesz réel complet, avec H11 ;
- `diagonalGhost_no_finite_kernel_transport` exclut tout transport linéaire
  injectif de ce noyau vers un espace de dimension finie, donc vers un noyau
  de référence fini.

Il s'agit d'une obstruction sur l'opérateur réel, indépendante du choix de
signes de la référence D9. Une fermeture couvrant ce régime ne peut donc
conserver simultanément le noyau réel complet, un transport injectif de
ce noyau et un noyau cible fini. Les hypothèses d'égalité des métriques et
d'annulation des poids restent explicites ; elles ne sont pas affirmées
pour le fond choisi. Aucun quotient de ghosts ni certificat terminal n'est
introduit par ces modules.

## Quotient de Hilbert des ghosts et antighosts nuls

`P0EFTJanusProgramPT12ClosedNullQuotient4D.lean` établit la descente d'un
opérateur borné autoadjoint `A` par un sous-espace fermé `N ⊆ ker A`.
L'opérateur quotient satisfait `Aq(q x) = q(A x)` et préserve exactement
le pairing `⟨Aq(q x), q y⟩ = ⟨A x, y⟩`. Son autoadjonction est prouvée,
et son noyau vaut l'image de `ker A` par la projection quotient.

`P0EFTJanusProgramPT12DiagonalGhostHilbertQuotient4D.lean` applique cette
construction à l'espace de Hilbert réel augmenté. Le sous-espace quotienté
est l'adhérence de l'image des couples lisses `(ghost, antighost)`, avec
métriques perturbées et champ B nuls. L'annulation des deux colonnes dans
le Riesz augmenté est démontrée sous les mêmes conditions de métriques
égales et de somme nulle des poids. La période doit seulement être non nulle
pour cette construction, contrairement à la preuve de dimension infinie
qui utilise sa positivité.

Le cœur réel projeté est dense dans le quotient. Les deux colonnes nulles
y deviennent zéro ; le pairing du Riesz quotient sur ce cœur est exactement
le Hessien local gauge-fixé existant, avec toutes les contributions H11.
L'intertwining utilise la projection quotient concrète, qui n'est pas
injective sur l'espace initial. Il ne suppose pas le paquet terminal
`ProgramPT12CanonicalActualFriedrichsSmoothCoreIntertwiner4D`.

Cette réduction concerne le Hessien linéaire dans le régime d'annulation.
Elle ne démontre ni une équivalence BRST non linéaire, ni la réalisation
géométrique L² actual→D9. Le noyau résiduel est conservé explicitement :
sa dimension finie et un gap sur son complément restent à établir. Le
raccord au quotient LL et au certificat global reste ouvert ; T12 n'est
pas coché.

## Quotient du Jacobi LL non borné et raccord Friedrichs

`P0EFTJanusProgramPT12ClosedNullPMapQuotient4D.lean` construit la descente
d'un opérateur symétrique non borné par un sous-espace fermé de son noyau.
Le graphe quotient est défini par les représentants orthogonaux. Il reste
fermé ; son domaine est exactement l'image du domaine initial et reste
dense. La symétrie et le pairing sont préservés, sans perdre de sortie
non nulle de l'opérateur.

`P0EFTJanusProgramPT12LLFullJacobiHilbertQuotient4D.lean` applique cette
construction au Jacobi LL littéral à trois composantes, à flux de fond nul.
Le sous-espace quotienté est le noyau de la projection sur le champ LL :
il contient exactement les composantes L² auxiliaire et mesure. La preuve
utilise leur annulation déjà établie pour le Jacobi fermé.

`P0EFTJanusProgramPT12LLFullReducedQuotientCore4D.lean` identifie ce quotient
isométriquement au L² LL canonique. Le quotient lisse auxiliaire–mesure
existant s'y plonge injectivement avec image dense, et les deux projections
commutent sur toute direction lisse complète. Cette identification des
espaces ne nécessite pas l'hypothèse de flux nul.

`P0EFTJanusProgramPT12LLFullReducedFriedrichsBridge4D.lean` compose ensuite
la décomposition du graphe LL déjà prouvée avec cette isométrie. À flux nul,
le graphe quotient est exactement conjugué au Jacobi fermé du champ LL,
et se transporte dans le graphe du Friedrichs canonique existant. Son noyau
est nul. Le noyau du Jacobi LL complet est donc exactement constitué des
directions auxiliaire–mesure.

Le transport vers Friedrichs est une inclusion de graphes : l'égalité des
domaines avec cette extension n'est pas démontrée ici. Aucun certificat
Fredholm global, ni raccord des quotients LL et ghosts avec les colonnes H11
globales, n'en est déduit. L'obstruction BRST vers le D9 positif reste
présente ; T12 reste ouvert.

## Réalisation de Friedrichs sur le quotient LL

`P0EFTJanusProgramPT12IsometricPMapTransport4D.lean` transporte un opérateur
non borné par une isométrie linéaire surjective, avec son domaine explicite
et son graphe. Il préserve fermeture, densité, symétrie et bijectivité ;
l'autoadjonction est établie pour une réalisation symétrique surjective à
domaine dense.

`P0EFTJanusProgramPT12LLQuotientFriedrichsRealization4D.lean` applique ce
transport au Friedrichs LL déjà construit, via l'isométrie concrète du
quotient auxiliaire–mesure. Le domaine est la préimage exacte du domaine
canonique. Cette réalisation est autoadjointe, fermée, à domaine dense,
bijective et Fredholm. Son inverse borné compact est le transport de
`canonicalLLWeakL2Inverse`, avec identités d'inversion des deux côtés et
borne en norme. Aucun solveur ni intertwiner terminal n'est postulé.

À flux de fond nul, le Jacobi LL quotient fermé est une restriction de
cette réalisation. `P0EFTJanusProgramPT12LLQuotientFriedrichsSmoothPairing4D.lean`
place chaque direction lisse complète dans son domaine et prouve le pairing
exact avec le Hessien LL de la même action, y compris lorsque les représentants
contiennent des composantes auxiliaire et mesure arbitraires.

Ce certificat concerne le secteur LL quotient. Il ne prouve pas l'égalité
du Jacobi minimal fermé avec son extension de Friedrichs : la densité du
cœur pour la norme de graphe reste à établir. Les raccords BRST et H11 du
certificat global restent ouverts ; T12 n'est pas coché.

## Colonne LL augmentée et quotient commun ghosts–LL

`P0EFTJanusProgramPT12StrongFullLLQuotientColumn4D.lean` identifie la
colonne LL complète du Riesz augmenté au Hessien LL de même action, contre
tout test du cœur global. Sur la carte forte centrée, l'annulation des
sept blocs physiques déjà prouvée couvre aussi les directions auxiliaire
et mesure. À flux nul, ce pairing est exactement celui de la réalisation
de Friedrichs du quotient LL, avec la composante LL du test global.

`P0EFTJanusProgramPT12StrongGhostLLNullSpace4D.lean` en déduit que l'adhérence
des directions LL auxiliaire–mesure appartient au noyau du Riesz augmenté,
à flux nul. Elle est réunie au sous-espace fermé des ghosts–antighosts par
l'adhérence de leur somme. L'inclusion de cette somme fermée dans le noyau
est prouvée avec les conditions explicites d'égalité des métriques et de
somme nulle des poids d'Einstein, ainsi que les données de la carte forte.

`P0EFTJanusProgramPT12StrongGhostLLHilbertQuotient4D.lean` construit le
quotient commun dans l'espace de Hilbert réel augmenté. Le cœur projeté
est dense ; les deux familles de directions nulles y disparaissent.
Le Riesz descend concrètement, reste autoadjoint et conserve exactement
le pairing augmenté, donc toutes les contributions H11. Sa colonne LL
reste identifiée au pairing de Friedrichs LL après cette réduction commune.
Le noyau quotient est exactement l'image du noyau initial.

Il s'agit d'une descente du Riesz borné augmenté ; aucun opérateur global
non borné actual→D9 ni certificat Fredholm global n'est déduit. Les
hypothèses de cancellation ne sont pas affirmées pour le fond choisi.
Le noyau résiduel des autres secteurs, leur réalisation BRST et la fermeture
terminale restent ouverts ; T12 n'est pas coché.

## Facteur abélien et colonne H11 sur le quotient commun

`P0EFTJanusProgramPT12JointQuotientAbelianFactor4D.lean` construit la
projection abélienne continue sur le quotient ghosts–LL et son inclusion
linéaire isométrique. La projection est surjective et rétracte l'inclusion.
Ces constructions ne requièrent pas les hypothèses d'annulation : elles
utilisent seulement les coordonnées nulles des deux sous-espaces éliminés,
puis leur fermeture. Le secteur abélien complété reste donc intact.

`P0EFTJanusProgramPT12JointQuotientAbelianColumn4D.lean` établit une égalité
de vecteurs : l'opérateur augmenté réduit appliqué à l'inclusion abélienne
est la somme de l'inclusion du Riesz BRST signé et de la colonne physique
H11 projetée sur le quotient. Cette colonne conserve ses composantes dans
tous les secteurs. Son pairing contre tout représentant complété reste
exactement `physical.form` sur les représentants initiaux.

`P0EFTJanusProgramPT12JointQuotientAbelianSmoothPairing4D.lean` raccorde
l'inclusion au cœur lisse réel. Le pairing réduit est exactement l'action
BRST abélienne polarisée plus la Hessienne physique H11, contre tout test
lisse global. Le champ B non nul conserve l'auto-pairing strictement négatif
`-‖globalPairedGaugeLieL2LinearMap ... field‖²` après quotient.

La descente de l'opérateur et ces pairings réduits gardent explicitement
les hypothèses du quotient commun : flux LL nul, métriques sectorielles
égales et somme des poids cinétiques Einstein nulle, ainsi que la carte
forte centrée et l'extension physique déjà utilisée. L'isométrie du facteur
abélien ne signifie pas qu'il est invariant sous H11. Aucun accord modal
avec une cible D9 signée ni certificat Fredholm global n'est établi ici ;
l'obstruction vers le D9 positif persiste et T12 reste ouvert.

## Facteur difféomorphisme réduit et opérateur H11 commun

`P0EFTJanusProgramPT12JointQuotientDiffeomorphismFactor4D.lean` définit le
quotient du graphe diagonal par la fermeture de l'image des ghosts et
antighosts partagés. Son inclusion dans le quotient ghosts–LL est
isométrique ; une projection continue la rétracte. Leur relation
d'adjonction est prouvée.
Cette construction géométrique ne requiert aucune annulation des poids.

`P0EFTJanusProgramPT12ReducedDiffeomorphismSignedRiesz4D.lean` descend le
Riesz signé réel sur ce quotient sectoriel, sous égalité des métriques et
annulation de la somme des poids Einstein. L'opérateur est auto-adjoint,
son pairing est inchangé et son noyau est l'image du noyau initial. Aucune
dimension finie du noyau résiduel n'est déduite.

`P0EFTJanusProgramPT12JointQuotientPhysicalRiesz4D.lean` descend séparément
l'opérateur physique H11 complet sur le quotient commun. Sur la carte
forte centrée, cette descente ne demande ni flux LL nul, ni égalité des
métriques, ni annulation des poids Einstein. Elle conserve l'auto-adjonction
et retrouve exactement la Hessienne physique sur le cœur lisse.

`P0EFTJanusProgramPT12JointQuotientDiffeomorphismColumn4D.lean` établit
l'égalité de vecteurs entre la colonne augmentée réduite et la somme du
Riesz signé sectoriel inclus et de H11 appliqué à la même inclusion. H11
reste un opérateur global, avec ses composantes hors du secteur source.
La colonne abélienne précédemment construite utilise ce même H11 réduit.

`P0EFTJanusProgramPT12JointQuotientDiffeomorphismSmoothPairing4D.lean`
construit le cœur lisse sectoriel dense, annule ses ghosts et raccorde son
inclusion au cœur réel global. Contre tout test lisse global, le pairing
augmenté réduit est exactement l'action BRST difféomorphisme polarisée
plus H11. Il garde les hypothèses d'annulation du quotient augmenté.

Ces résultats réalisent les colonnes BRST sur les quotients réels ; ils ne
construisent pas leur identification modale avec D9 signé. L'obstruction
abélienne vers D9 positif demeure. L'identification modale signée et la
fermeture Fredholm globale restent à établir. T12 n'est pas coché.

## Décomposition globale du quotient de graphe et de son Riesz

`P0EFTJanusProgramPT12ClosedNullFactorIsometry4D.lean` isole le transport
isométrique d'un facteur entre quotients fermés compatibles. Ce petit
lemme évite un timeout de dépliage des types géométriques, sans augmenter
les limites de heartbeats.

`P0EFTJanusProgramPT12JointQuotientMatterLLFactor4D.lean` construit le
facteur matière–LL complété, quotienté par la fermeture des directions
LL auxiliaires/mesure, avec inclusion isométrique et projection adjointe.
`P0EFTJanusProgramPT12JointQuotientSectorDecomposition4D.lean` prouve la
reconstruction unique de tout vecteur du quotient global par les facteurs
difféomorphisme, abélien et matière–LL. Le produit scalaire et le carré de
la norme sont exactement les sommes sectorielles.

`P0EFTJanusProgramPT12ReducedMatterLLGraphRiesz4D.lean` extrait le bloc
matière–LL du Riesz de graphe existant, indépendamment de l'extension
physique. Son pairing est explicitement la somme des formes matière et
LL réelles. Sous les données fortes centrées et le flux LL nul, il descend
en un opérateur auto-adjoint sur le quotient sectoriel et sa colonne
coïncide avec celle du Riesz augmenté. H11 annule ce facteur entier.

`P0EFTJanusProgramPT12ThreeBlockHilbertAssembly4D.lean` isole l'assemblage
abstrait des trois colonnes et de l'opérateur physique commun, avec le
pairing et l'auto-adjonction de la différence de deux opérateurs.
`P0EFTJanusProgramPT12JointQuotientGlobalRiesz4D.lean` établit l'égalité
d'opérateurs sur tout le quotient global : Riesz augmenté = somme des trois
blocs sectoriels inclus et projetés + H11 réduit. La somme diagonale est
auto-adjointe ; son pairing global est explicite. H11 dépend seulement des
deux coordonnées BRST, en conservant leurs éventuels termes croisés.
L'assemblage garde les hypothèses d'annulation du Riesz augmenté.

Le quotient matière–LL construit ici porte la norme du graphe global.
Il n'est pas identifié au quotient LL en norme L² portant l'opérateur
non borné de Friedrichs. Cette égalité globale bornée ne fournit ni
l'identification modale signée ni le certificat Fredholm géométrique
terminal. T12 reste ouvert.

## Validation

### Pairing et obstruction vers le D9 positif

Les cinq nouveaux modules sont compilés séquentiellement avec
`scripts/run_lean_guarded.ps1`, priorité haute, un seul processus Lean,
`MemoryMB=4096` et `ReserveMB=4096`. Pics échantillonnés : pairing 4170 Mo,
D9 3630 Mo, témoin BRST 3733 Mo, impossibilité 3718 Mo, colonne H11 4010 Mo.
Le hub T12 importe les cinq modules via trois imports directs ; sa compilation
gardée est verte (4090 Mo). L'audit `#print axioms` des six théorèmes listés
ci-dessus ne retourne que `propext`, `Classical.choice` et `Quot.sound`
(3917 Mo). Aucun `sorry`, `admit` ou nouvel axiome ; `git diff --check` vert.

### Réalisations signées

Les cinq modules signés ont été compilés séparément avec le même protocole
gardé, séquentiel, priorité haute et réserve de 4096 Mo. Pics échantillonnés :
Gram 1929 Mo, abélien 3746 Mo, difféomorphisme 3995 Mo, assemblage H11
3872 Mo et référence D9 3612 Mo. Le hub T12 les importe par deux imports
directs supplémentaires ; sa compilation est verte (3957 Mo).
L'audit `#print axioms` porte sur treize résultats : les deux pairings de
Gram, les deux identifications au Riesz réel et leurs deux accords lisses,
les deux théorèmes d'assemblage/H11, les quatre propriétés du D9 signé et
son identité de symbole. Il ne retourne que `propext`, `Classical.choice`
et `Quot.sound` (3906 Mo). Aucun `sorry`, `admit` ou nouvel axiome dans les
cinq modules ; `git diff --check` vert.

### Symbole complet et référence abélienne d'ordre mixte

Les trois modules supplémentaires sont verts sous `run_lean_guarded`, un
seul Lean à priorité haute et réserve de 4096 Mo. Pics échantillonnés :
symbole 3706 Mo, référence pairée 3637 Mo, bornes de graphe 3691 Mo.
Le hub les importe via deux imports directs ; il compile à 3988 Mo.
L'audit `#print axioms` de quatorze déclarations (équivalence, linéarité,
pairing, zéros, gap pairé, quatre propriétés de l'opérateur, deux bornes de
graphe, croissance du témoin et absence de borne brute) ne retourne que
`propext`, `Classical.choice` et `Quot.sound` (3907 Mo). Aucun `sorry`,
`admit` ou nouvel axiome ; `git diff --check` vert.

### Noyau diagonal réel et augmentation H11

Les deux modules de cancellation sont compilés séquentiellement avec
`run_lean_guarded`, priorité haute et réserve de 4096 Mo. Pics échantillonnés :
graphe diagonal 3765 Mo, noyau augmenté et injection 4160 Mo. Le hub importe
les deux modules par un import direct supplémentaire et compile à 3993 Mo.
L'audit `#print axioms` des neuf théorèmes publics ne retourne que `propext`,
`Classical.choice` et `Quot.sound` (3889 Mo). Aucun `sorry`, `admit` ou nouvel
axiome ; `git diff --check` vert.

### Dimension infinie des ghosts et du noyau réel

Les trois nouveaux modules sont verts sous `run_lean_guarded`, priorité haute,
un seul Lean et réserve de 4096 Mo. Pics échantillonnés : injection par les
générateurs 3695 Mo, dimension infinie des ghosts 3814 Mo, noyau augmenté et
impossibilité de transport 3844 Mo. Le hub importe ces résultats par un
import direct supplémentaire et compile à 4082 Mo.
L'audit `#print axioms` des sept théorèmes publics ne retourne que `propext`,
`Classical.choice` et `Quot.sound` (3889 Mo). Aucun `sorry`, `admit` ou nouvel
axiome ; `git diff --check` vert.

### Quotient fermé des ghosts et antighosts

Les deux nouveaux modules sont verts sous `run_lean_guarded`, priorité haute,
un seul Lean et réserve de 4096 Mo. Pics échantillonnés : quotient abstrait
1929 Mo, quotient réel augmenté 4185 Mo. Le hub importe ces résultats par
un import direct supplémentaire et compile à 4226 Mo.
L'audit `#print axioms` des dix-sept théorèmes publics ne retourne que
`propext`, `Classical.choice` et `Quot.sound` (3897 Mo). Aucun `sorry`,
`admit` ou nouvel axiome ; `git diff --check` vert.

### Quotient du Jacobi LL non borné

Les quatre nouveaux modules sont verts sous `run_lean_guarded`, priorité
haute, un seul Lean et réserve de 4096 Mo. Pics échantillonnés : descente
abstraite 1923 Mo, quotient du Jacobi LL 3892 Mo, isométrie et cœur lisse
3899 Mo, raccord Friedrichs et noyau 3896 Mo. Le hub compile à 3970 Mo.
L'audit `#print axioms` des trente-deux théorèmes publics ne retourne que
`propext`, `Classical.choice` et `Quot.sound` (3920 Mo). Aucun `sorry`,
`admit` ou nouvel axiome ; `git diff --check` vert.

### Réalisation de Friedrichs sur le quotient LL

Les trois nouveaux modules sont verts sous `run_lean_guarded`, priorité
haute, un seul Lean et réserve de 4096 Mo. Pics échantillonnés : transport
isométrique 1928 Mo, réalisation quotient 3978 Mo, pairing de même action
3895 Mo. Le hub compile à 3971 Mo. L'audit `#print axioms` des vingt-huit
théorèmes publics ne retourne que `propext`, `Classical.choice` et
`Quot.sound` (3893 Mo). Aucun `sorry`, `admit` ou nouvel axiome ;
`git diff --check` vert.

### Colonne LL augmentée et quotient commun ghosts–LL

Les trois nouveaux modules sont verts sous `run_lean_guarded`, priorité
haute, un seul Lean et réserve de 4096 Mo. Pics échantillonnés : colonne LL
4184 Mo, sous-espace nul commun 4432 Mo, quotient augmenté 4476 Mo.
Le hub compile à 4107 Mo. L'audit `#print axioms` des quinze théorèmes
publics ne retourne que `propext`, `Classical.choice` et `Quot.sound`
(3893 Mo). Aucun `sorry`, `admit` ou nouvel axiome ; `git diff --check` vert.

### Facteur abélien et H11 sur le quotient commun

Les trois nouveaux modules sont verts sous `run_lean_guarded`, priorité
haute, un seul Lean et réserve de 4096 Mo. Pics échantillonnés : facteur
isométrique 4075 Mo, colonne opérateur 4239 Mo, raccord lisse 4480 Mo.
Le hub compile à 3962 Mo. L'audit `#print axioms` des dix-neuf théorèmes
publics et des deux inclusions isométriques ne retourne que `propext`,
`Classical.choice` et `Quot.sound` (3801 Mo). Aucun `sorry`, `admit` ou
nouvel axiome ; `git diff --check` vert.

### Facteur difféomorphisme réduit et H11 commun

Les cinq nouveaux modules sont verts sous `run_lean_guarded`, priorité
haute, un seul Lean et réserve de 4096 Mo. Pics échantillonnés : facteur
isométrique 4306 Mo, Riesz signé réduit 4232 Mo, H11 réduit 3951 Mo,
colonne opérateur 4277 Mo, raccord lisse 3995 Mo. Le hub compile à 3969 Mo.
L'audit `#print axioms` des trente-trois théorèmes publics et des deux
inclusions isométriques ne retourne que `propext`, `Classical.choice` et
`Quot.sound` (3923 Mo). Aucun `sorry`, `admit` ou nouvel axiome ;
`git diff --check` vert.

### Décomposition et Riesz globaux sur le quotient de graphe

Les six nouveaux modules sont verts sous `run_lean_guarded`, priorité
haute, un seul Lean et réserve de 4096 Mo. Pics échantillonnés : isométrie
abstraite 1921 Mo, facteur matière–LL 4334 Mo, décomposition 4328 Mo,
Riesz matière–LL 4311 Mo, assemblage abstrait 1987 Mo, Riesz global
4519 Mo. Le hub compile à 3981 Mo. Les timeouts de dépliage ont été
résolus par des lemmes abstraits et des compositions explicites, sans
augmenter les heartbeats.
L'audit `#print axioms` des trente-six théorèmes publics et des trois
inclusions isométriques ne retourne que `propext`, `Classical.choice` et
`Quot.sound` (3902 Mo). Aucun `sorry`, `admit` ou nouvel axiome ;
`git diff --check` vert.
